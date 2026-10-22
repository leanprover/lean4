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
size_t v_x_1976__boxed_1677_; size_t v_x_1977__boxed_1678_; lean_object* v_res_1679_; 
v_x_1976__boxed_1677_ = lean_unbox_usize(v_x_1673_);
lean_dec(v_x_1673_);
v_x_1977__boxed_1678_ = lean_unbox_usize(v_x_1674_);
lean_dec(v_x_1674_);
v_res_1679_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1672_, v_x_1976__boxed_1677_, v_x_1977__boxed_1678_, v_x_1675_, v_x_1676_);
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
lean_object* v_depth_1700_; lean_object* v_levelAssignDepth_1701_; lean_object* v_lmvarCounter_1702_; lean_object* v_mvarCounter_1703_; lean_object* v_lDecls_1704_; lean_object* v_decls_1705_; lean_object* v_userNames_1706_; lean_object* v_lAssignment_1707_; lean_object* v_eAssignment_1708_; lean_object* v_dAssignment_1709_; lean_object* v_synthNormMemo_1710_; lean_object* v___x_1712_; uint8_t v_isShared_1713_; uint8_t v_isSharedCheck_1724_; 
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
v_synthNormMemo_1710_ = lean_ctor_get(v_mctx_1692_, 10);
v_isSharedCheck_1724_ = !lean_is_exclusive(v_mctx_1692_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1712_ = v_mctx_1692_;
v_isShared_1713_ = v_isSharedCheck_1724_;
goto v_resetjp_1711_;
}
else
{
lean_inc(v_synthNormMemo_1710_);
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
lean_ctor_set(v_reuseFailAlloc_1723_, 10, v_synthNormMemo_1710_);
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
lean_object* v___x_1830_; lean_object* v___x_1831_; uint8_t v___x_1832_; 
v___x_1830_ = lean_unsigned_to_nat(0u);
v___x_1831_ = lean_array_get_size(v_instMVars_1790_);
v___x_1832_ = lean_nat_dec_lt(v___x_1830_, v___x_1831_);
if (v___x_1832_ == 0)
{
goto v___jp_1796_;
}
else
{
lean_object* v___x_1833_; size_t v___x_1834_; size_t v___x_1835_; lean_object* v___x_1836_; 
v___x_1833_ = lean_box(0);
v___x_1834_ = ((size_t)0ULL);
v___x_1835_ = lean_usize_of_nat(v___x_1831_);
v___x_1836_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1790_, v___x_1834_, v___x_1835_, v___x_1833_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_dec_ref_known(v___x_1836_, 1);
goto v___jp_1796_;
}
else
{
lean_object* v_a_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_1844_; 
lean_dec_ref(v_f_1788_);
lean_dec(v_methodName_1787_);
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1839_ = v___x_1836_;
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_a_1837_);
lean_dec(v___x_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_1844_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1842_; 
if (v_isShared_1840_ == 0)
{
v___x_1842_ = v___x_1839_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* v_methodName_1845_, lean_object* v_f_1846_, lean_object* v_args_1847_, lean_object* v_instMVars_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_){
_start:
{
lean_object* v_res_1854_; 
v_res_1854_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v_methodName_1845_, v_f_1846_, v_args_1847_, v_instMVars_1848_, v_a_1849_, v_a_1850_, v_a_1851_, v_a_1852_);
lean_dec(v_a_1852_);
lean_dec_ref(v_a_1851_);
lean_dec(v_a_1850_);
lean_dec_ref(v_a_1849_);
lean_dec_ref(v_instMVars_1848_);
lean_dec_ref(v_args_1847_);
return v_res_1854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* v_mvarId_1855_, lean_object* v_val_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_){
_start:
{
lean_object* v___x_1862_; 
v___x_1862_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1855_, v_val_1856_, v___y_1858_);
return v___x_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* v_mvarId_1863_, lean_object* v_val_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(v_mvarId_1863_, v_val_1864_, v___y_1865_, v___y_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* v_00_u03b2_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_x_1872_, v_x_1873_, v_x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1876_, lean_object* v_x_1877_, size_t v_x_1878_, size_t v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
lean_object* v___x_1882_; 
v___x_1882_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1877_, v_x_1878_, v_x_1879_, v_x_1880_, v_x_1881_);
return v___x_1882_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_, lean_object* v_x_1887_, lean_object* v_x_1888_){
_start:
{
size_t v_x_2404__boxed_1889_; size_t v_x_2405__boxed_1890_; lean_object* v_res_1891_; 
v_x_2404__boxed_1889_ = lean_unbox_usize(v_x_1885_);
lean_dec(v_x_1885_);
v_x_2405__boxed_1890_ = lean_unbox_usize(v_x_1886_);
lean_dec(v_x_1886_);
v_res_1891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1883_, v_x_1884_, v_x_2404__boxed_1889_, v_x_2405__boxed_1890_, v_x_1887_, v_x_1888_);
return v_res_1891_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1892_, lean_object* v_n_1893_, lean_object* v_k_1894_, lean_object* v_v_1895_){
_start:
{
lean_object* v___x_1896_; 
v___x_1896_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1893_, v_k_1894_, v_v_1895_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1897_, size_t v_depth_1898_, lean_object* v_keys_1899_, lean_object* v_vals_1900_, lean_object* v_heq_1901_, lean_object* v_i_1902_, lean_object* v_entries_1903_){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1898_, v_keys_1899_, v_vals_1900_, v_i_1902_, v_entries_1903_);
return v___x_1904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1905_, lean_object* v_depth_1906_, lean_object* v_keys_1907_, lean_object* v_vals_1908_, lean_object* v_heq_1909_, lean_object* v_i_1910_, lean_object* v_entries_1911_){
_start:
{
size_t v_depth_boxed_1912_; lean_object* v_res_1913_; 
v_depth_boxed_1912_ = lean_unbox_usize(v_depth_1906_);
lean_dec(v_depth_1906_);
v_res_1913_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1905_, v_depth_boxed_1912_, v_keys_1907_, v_vals_1908_, v_heq_1909_, v_i_1910_, v_entries_1911_);
lean_dec_ref(v_vals_1908_);
lean_dec_ref(v_keys_1907_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_, lean_object* v_x_1917_, lean_object* v_x_1918_){
_start:
{
lean_object* v___x_1919_; 
v___x_1919_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1915_, v_x_1916_, v_x_1917_, v_x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1924_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2));
v___x_1925_ = l_Lean_stringToMessageData(v___x_1924_);
return v___x_1925_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1927_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4));
v___x_1928_ = l_Lean_stringToMessageData(v___x_1927_);
return v___x_1928_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1932_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7));
v___x_1933_ = l_Lean_MessageData_ofFormat(v___x_1932_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* v_f_1934_, lean_object* v_xs_1935_, lean_object* v_type_1936_, lean_object* v_i_1937_, lean_object* v_j_1938_, lean_object* v_args_1939_, lean_object* v_instMVars_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = lean_array_get_size(v_xs_1935_);
v___x_1947_ = lean_nat_dec_le(v___x_1946_, v_i_1937_);
if (v___x_1947_ == 0)
{
if (lean_obj_tag(v_type_1936_) == 7)
{
lean_object* v_binderName_1948_; lean_object* v_binderType_1949_; lean_object* v_body_1950_; uint8_t v_binderInfo_1951_; lean_object* v___x_1952_; lean_object* v_d_1953_; lean_object* v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; 
v_binderName_1948_ = lean_ctor_get(v_type_1936_, 0);
lean_inc(v_binderName_1948_);
v_binderType_1949_ = lean_ctor_get(v_type_1936_, 1);
lean_inc_ref(v_binderType_1949_);
v_body_1950_ = lean_ctor_get(v_type_1936_, 2);
lean_inc_ref(v_body_1950_);
v_binderInfo_1951_ = lean_ctor_get_uint8(v_type_1936_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1936_, 3);
v___x_1952_ = lean_array_get_size(v_args_1939_);
v_d_1953_ = lean_expr_instantiate_rev_range(v_binderType_1949_, v_j_1938_, v___x_1952_, v_args_1939_);
lean_dec_ref(v_binderType_1949_);
switch(v_binderInfo_1951_)
{
case 1:
{
v___y_1955_ = v_a_1941_;
v___y_1956_ = v_a_1942_;
v___y_1957_ = v_a_1943_;
v___y_1958_ = v_a_1944_;
goto v___jp_1954_;
}
case 2:
{
v___y_1955_ = v_a_1941_;
v___y_1956_ = v_a_1942_;
v___y_1957_ = v_a_1943_;
v___y_1958_ = v_a_1944_;
goto v___jp_1954_;
}
case 3:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1965_, 0, v_d_1953_);
v___x_1966_ = 1;
v___x_1967_ = l_Lean_Meta_mkFreshExprMVar(v___x_1965_, v___x_1966_, v_binderName_1948_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1967_) == 0)
{
lean_object* v_a_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_a_1968_ = lean_ctor_get(v___x_1967_, 0);
lean_inc_n(v_a_1968_, 2);
lean_dec_ref_known(v___x_1967_, 1);
v___x_1969_ = lean_array_push(v_args_1939_, v_a_1968_);
v___x_1970_ = l_Lean_Expr_mvarId_x21(v_a_1968_);
lean_dec(v_a_1968_);
v___x_1971_ = lean_array_push(v_instMVars_1940_, v___x_1970_);
v_type_1936_ = v_body_1950_;
v_args_1939_ = v___x_1969_;
v_instMVars_1940_ = v___x_1971_;
goto _start;
}
else
{
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_instMVars_1940_);
lean_dec_ref(v_args_1939_);
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
lean_dec_ref(v_f_1934_);
return v___x_1967_;
}
}
default: 
{
lean_object* v_x_1973_; lean_object* v___y_1975_; lean_object* v___x_1992_; 
lean_dec(v_binderName_1948_);
v_x_1973_ = lean_array_fget_borrowed(v_xs_1935_, v_i_1937_);
lean_inc(v_a_1944_);
lean_inc_ref(v_a_1943_);
lean_inc(v_a_1942_);
lean_inc_ref(v_a_1941_);
lean_inc(v_x_1973_);
v___x_1992_ = lean_infer_type(v_x_1973_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1994_; uint8_t v_transparency_1995_; uint8_t v___x_1996_; uint8_t v___x_1997_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
v___x_1994_ = l_Lean_Meta_Context_config(v_a_1941_);
v_transparency_1995_ = lean_ctor_get_uint8(v___x_1994_, 9);
lean_dec_ref(v___x_1994_);
v___x_1996_ = 1;
v___x_1997_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
v___x_1998_ = l_Lean_Meta_isExprDefEq(v_d_1953_, v_a_1993_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
v___y_1975_ = v___x_1998_;
goto v___jp_1974_;
}
else
{
lean_object* v_keyedConfig_1999_; uint8_t v_trackZetaDelta_2000_; lean_object* v_zetaDeltaSet_2001_; lean_object* v_lctx_2002_; lean_object* v_localInstances_2003_; lean_object* v_defEqCtx_x3f_2004_; lean_object* v_synthPendingDepth_2005_; lean_object* v_customCanUnfoldPredicate_x3f_2006_; uint8_t v_univApprox_2007_; uint8_t v_inTypeClassResolution_2008_; uint8_t v_cacheInferType_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v_keyedConfig_1999_ = lean_ctor_get(v_a_1941_, 0);
v_trackZetaDelta_2000_ = lean_ctor_get_uint8(v_a_1941_, sizeof(void*)*7);
v_zetaDeltaSet_2001_ = lean_ctor_get(v_a_1941_, 1);
v_lctx_2002_ = lean_ctor_get(v_a_1941_, 2);
v_localInstances_2003_ = lean_ctor_get(v_a_1941_, 3);
v_defEqCtx_x3f_2004_ = lean_ctor_get(v_a_1941_, 4);
v_synthPendingDepth_2005_ = lean_ctor_get(v_a_1941_, 5);
v_customCanUnfoldPredicate_x3f_2006_ = lean_ctor_get(v_a_1941_, 6);
v_univApprox_2007_ = lean_ctor_get_uint8(v_a_1941_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2008_ = lean_ctor_get_uint8(v_a_1941_, sizeof(void*)*7 + 2);
v_cacheInferType_2009_ = lean_ctor_get_uint8(v_a_1941_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1999_);
v___x_2010_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1996_, v_keyedConfig_1999_);
lean_inc(v_customCanUnfoldPredicate_x3f_2006_);
lean_inc(v_synthPendingDepth_2005_);
lean_inc(v_defEqCtx_x3f_2004_);
lean_inc_ref(v_localInstances_2003_);
lean_inc_ref(v_lctx_2002_);
lean_inc(v_zetaDeltaSet_2001_);
v___x_2011_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2011_, 0, v___x_2010_);
lean_ctor_set(v___x_2011_, 1, v_zetaDeltaSet_2001_);
lean_ctor_set(v___x_2011_, 2, v_lctx_2002_);
lean_ctor_set(v___x_2011_, 3, v_localInstances_2003_);
lean_ctor_set(v___x_2011_, 4, v_defEqCtx_x3f_2004_);
lean_ctor_set(v___x_2011_, 5, v_synthPendingDepth_2005_);
lean_ctor_set(v___x_2011_, 6, v_customCanUnfoldPredicate_x3f_2006_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7, v_trackZetaDelta_2000_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 1, v_univApprox_2007_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2008_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*7 + 3, v_cacheInferType_2009_);
v___x_2012_ = l_Lean_Meta_isExprDefEq(v_d_1953_, v_a_1993_, v___x_2011_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec_ref_known(v___x_2011_, 7);
v___y_1975_ = v___x_2012_;
goto v___jp_1974_;
}
}
else
{
lean_dec_ref(v_d_1953_);
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_instMVars_1940_);
lean_dec_ref(v_args_1939_);
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
lean_dec_ref(v_f_1934_);
return v___x_1992_;
}
v___jp_1974_:
{
if (lean_obj_tag(v___y_1975_) == 0)
{
lean_object* v_a_1976_; uint8_t v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___y_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref_known(v___y_1975_, 1);
v___x_1977_ = lean_unbox(v_a_1976_);
lean_dec(v_a_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_instMVars_1940_);
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
v___x_1978_ = l_Lean_mkAppN(v_f_1934_, v_args_1939_);
lean_dec_ref(v_args_1939_);
lean_inc(v_x_1973_);
v___x_1979_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1978_, v_x_1973_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_1979_;
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = lean_unsigned_to_nat(1u);
v___x_1981_ = lean_nat_add(v_i_1937_, v___x_1980_);
lean_dec(v_i_1937_);
lean_inc(v_x_1973_);
v___x_1982_ = lean_array_push(v_args_1939_, v_x_1973_);
v_type_1936_ = v_body_1950_;
v_i_1937_ = v___x_1981_;
v_args_1939_ = v___x_1982_;
goto _start;
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_instMVars_1940_);
lean_dec_ref(v_args_1939_);
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
lean_dec_ref(v_f_1934_);
v_a_1984_ = lean_ctor_get(v___y_1975_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___y_1975_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___y_1975_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___y_1975_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
}
}
v___jp_1954_:
{
lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1959_, 0, v_d_1953_);
v___x_1960_ = 0;
v___x_1961_ = l_Lean_Meta_mkFreshExprMVar(v___x_1959_, v___x_1960_, v_binderName_1948_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
lean_object* v_a_1962_; lean_object* v___x_1963_; 
v_a_1962_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_a_1962_);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1963_ = lean_array_push(v_args_1939_, v_a_1962_);
v_type_1936_ = v_body_1950_;
v_args_1939_ = v___x_1963_;
v_a_1941_ = v___y_1955_;
v_a_1942_ = v___y_1956_;
v_a_1943_ = v___y_1957_;
v_a_1944_ = v___y_1958_;
goto _start;
}
else
{
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_instMVars_1940_);
lean_dec_ref(v_args_1939_);
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
lean_dec_ref(v_f_1934_);
return v___x_1961_;
}
}
}
else
{
lean_object* v___x_2013_; lean_object* v_type_2014_; lean_object* v___x_2015_; 
v___x_2013_ = lean_array_get_size(v_args_1939_);
v_type_2014_ = lean_expr_instantiate_rev_range(v_type_1936_, v_j_1938_, v___x_2013_, v_args_1939_);
lean_dec(v_j_1938_);
lean_dec_ref(v_type_1936_);
v___x_2015_ = l_Lean_Meta_whnfD(v_type_2014_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; uint8_t v___x_2017_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref_known(v___x_2015_, 1);
v___x_2017_ = l_Lean_Expr_isForall(v_a_2016_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec(v_a_2016_);
lean_dec_ref(v_instMVars_1940_);
lean_dec_ref(v_args_1939_);
lean_dec(v_i_1937_);
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2019_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2020_ = l_Lean_indentExpr(v_f_1934_);
v___x_2021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2019_);
lean_ctor_set(v___x_2021_, 1, v___x_2020_);
v___x_2022_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_unsigned_to_nat(0u);
v___x_2025_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2026_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1935_, v___x_2024_, v___x_2025_);
v___x_2027_ = l_Lean_indentD(v___x_2026_);
v___x_2028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2028_, 0, v___x_2023_);
lean_ctor_set(v___x_2028_, 1, v___x_2027_);
v___x_2029_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_2018_, v___x_2028_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
return v___x_2029_;
}
else
{
v_type_1936_ = v_a_2016_;
v_j_1938_ = v___x_2013_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1940_);
lean_dec_ref(v_args_1939_);
lean_dec(v_i_1937_);
lean_dec_ref(v_f_1934_);
return v___x_2015_;
}
}
}
else
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
lean_dec(v_j_1938_);
lean_dec(v_i_1937_);
lean_dec_ref(v_type_1936_);
v___x_2031_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2032_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2031_, v_f_1934_, v_args_1939_, v_instMVars_1940_, v_a_1941_, v_a_1942_, v_a_1943_, v_a_1944_);
lean_dec_ref(v_instMVars_1940_);
lean_dec_ref(v_args_1939_);
return v___x_2032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2033_, lean_object* v_xs_2034_, lean_object* v_type_2035_, lean_object* v_i_2036_, lean_object* v_j_2037_, lean_object* v_args_2038_, lean_object* v_instMVars_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2033_, v_xs_2034_, v_type_2035_, v_i_2036_, v_j_2037_, v_args_2038_, v_instMVars_2039_, v_a_2040_, v_a_2041_, v_a_2042_, v_a_2043_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec(v_a_2041_);
lean_dec_ref(v_a_2040_);
lean_dec_ref(v_xs_2034_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2048_, lean_object* v_fType_2049_, lean_object* v_xs_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_unsigned_to_nat(0u);
v___x_2057_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2058_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2048_, v_xs_2050_, v_fType_2049_, v___x_2056_, v___x_2056_, v___x_2057_, v___x_2057_, v_a_2051_, v_a_2052_, v_a_2053_, v_a_2054_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2059_, lean_object* v_fType_2060_, lean_object* v_xs_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2059_, v_fType_2060_, v_xs_2061_, v_a_2062_, v_a_2063_, v_a_2064_, v_a_2065_);
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2064_);
lean_dec(v_a_2063_);
lean_dec_ref(v_a_2062_);
lean_dec_ref(v_xs_2061_);
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2068_, lean_object* v_x_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
if (lean_obj_tag(v_x_2068_) == 0)
{
lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2075_ = l_List_reverse___redArg(v_x_2069_);
v___x_2076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2076_, 0, v___x_2075_);
return v___x_2076_;
}
else
{
lean_object* v_tail_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2095_; 
v_tail_2077_ = lean_ctor_get(v_x_2068_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_x_2068_);
if (v_isSharedCheck_2095_ == 0)
{
lean_object* v_unused_2096_; 
v_unused_2096_ = lean_ctor_get(v_x_2068_, 0);
lean_dec(v_unused_2096_);
v___x_2079_ = v_x_2068_;
v_isShared_2080_ = v_isSharedCheck_2095_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_tail_2077_);
lean_dec(v_x_2068_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2095_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; 
v___x_2081_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_);
if (lean_obj_tag(v___x_2081_) == 0)
{
lean_object* v_a_2082_; lean_object* v___x_2084_; 
v_a_2082_ = lean_ctor_get(v___x_2081_, 0);
lean_inc(v_a_2082_);
lean_dec_ref_known(v___x_2081_, 1);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v_x_2069_);
lean_ctor_set(v___x_2079_, 0, v_a_2082_);
v___x_2084_ = v___x_2079_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_a_2082_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_x_2069_);
v___x_2084_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
v_x_2068_ = v_tail_2077_;
v_x_2069_ = v___x_2084_;
goto _start;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_del_object(v___x_2079_);
lean_dec(v_tail_2077_);
lean_dec(v_x_2069_);
v_a_2087_ = lean_ctor_get(v___x_2081_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2081_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2081_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2081_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2097_, lean_object* v_x_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2097_, v_x_2098_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2107_, 0, v___x_2106_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2108_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_2109_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2110_ = lean_unsigned_to_nat(0u);
v___x_2111_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
lean_ctor_set(v___x_2111_, 1, v___x_2110_);
lean_ctor_set(v___x_2111_, 2, v___x_2110_);
lean_ctor_set(v___x_2111_, 3, v___x_2110_);
lean_ctor_set(v___x_2111_, 4, v___x_2109_);
lean_ctor_set(v___x_2111_, 5, v___x_2109_);
lean_ctor_set(v___x_2111_, 6, v___x_2109_);
lean_ctor_set(v___x_2111_, 7, v___x_2109_);
lean_ctor_set(v___x_2111_, 8, v___x_2109_);
lean_ctor_set(v___x_2111_, 9, v___x_2109_);
lean_ctor_set(v___x_2111_, 10, v___x_2108_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_unsigned_to_nat(32u);
v___x_2113_ = lean_mk_empty_array_with_capacity(v___x_2112_);
v___x_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2115_ = ((size_t)5ULL);
v___x_2116_ = lean_unsigned_to_nat(0u);
v___x_2117_ = lean_unsigned_to_nat(32u);
v___x_2118_ = lean_mk_empty_array_with_capacity(v___x_2117_);
v___x_2119_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2120_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2120_, 0, v___x_2119_);
lean_ctor_set(v___x_2120_, 1, v___x_2118_);
lean_ctor_set(v___x_2120_, 2, v___x_2116_);
lean_ctor_set(v___x_2120_, 3, v___x_2116_);
lean_ctor_set_usize(v___x_2120_, 4, v___x_2115_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2121_ = lean_box(1);
v___x_2122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2124_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2123_);
lean_ctor_set(v___x_2124_, 1, v___x_2122_);
lean_ctor_set(v___x_2124_, 2, v___x_2121_);
return v___x_2124_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2127_ = l_Lean_stringToMessageData(v___x_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2130_ = l_Lean_stringToMessageData(v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2146_, lean_object* v_declHint_2147_, lean_object* v___y_2148_){
_start:
{
lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v_env_2152_; uint8_t v___x_2153_; 
v___x_2150_ = lean_box(0);
v___x_2151_ = lean_st_ref_get(v___y_2148_);
v_env_2152_ = lean_ctor_get(v___x_2151_, 0);
lean_inc_ref(v_env_2152_);
lean_dec(v___x_2151_);
v___x_2153_ = l_Lean_Name_isAnonymous(v_declHint_2147_);
if (v___x_2153_ == 0)
{
uint8_t v_isExporting_2154_; 
v_isExporting_2154_ = lean_ctor_get_uint8(v_env_2152_, sizeof(void*)*13);
if (v_isExporting_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_msg_2146_);
return v___x_2155_;
}
else
{
lean_object* v___x_2156_; uint8_t v___x_2157_; 
lean_inc_ref(v_env_2152_);
v___x_2156_ = l_Lean_Environment_setExporting(v_env_2152_, v___x_2153_);
lean_inc(v_declHint_2147_);
lean_inc_ref(v___x_2156_);
v___x_2157_ = l_Lean_Environment_contains(v___x_2156_, v_declHint_2147_, v_isExporting_2154_);
if (v___x_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref(v___x_2156_);
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_msg_2146_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v_c_2164_; lean_object* v___x_2165_; 
v___x_2159_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2161_ = l_Lean_Options_empty;
v___x_2162_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2156_);
lean_ctor_set(v___x_2162_, 1, v___x_2159_);
lean_ctor_set(v___x_2162_, 2, v___x_2160_);
lean_ctor_set(v___x_2162_, 3, v___x_2161_);
lean_inc(v_declHint_2147_);
v___x_2163_ = l_Lean_MessageData_ofConstName(v_declHint_2147_, v___x_2153_);
v_c_2164_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2164_, 0, v___x_2162_);
lean_ctor_set(v_c_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2152_, v_declHint_2147_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2166_);
lean_ctor_set(v___x_2167_, 1, v_c_2164_);
v___x_2168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Lean_MessageData_note(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_msg_2146_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2171_);
return v___x_2172_;
}
else
{
lean_object* v_val_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2207_; 
v_val_2173_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2175_ = v___x_2165_;
v_isShared_2176_ = v_isSharedCheck_2207_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_val_2173_);
lean_dec(v___x_2165_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2207_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2177_; lean_object* v_moduleNames_2178_; lean_object* v_mod_2179_; uint8_t v___x_2180_; 
v___x_2177_ = l_Lean_Environment_header(v_env_2152_);
lean_dec_ref(v_env_2152_);
v_moduleNames_2178_ = lean_ctor_get(v___x_2177_, 4);
lean_inc_ref(v_moduleNames_2178_);
lean_dec_ref(v___x_2177_);
v_mod_2179_ = lean_array_get(v___x_2150_, v_moduleNames_2178_, v_val_2173_);
lean_dec(v_val_2173_);
lean_dec_ref(v_moduleNames_2178_);
v___x_2180_ = l_Lean_isPrivateName(v_declHint_2147_);
lean_dec(v_declHint_2147_);
if (v___x_2180_ == 0)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v_c_2164_);
v___x_2183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2182_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
v___x_2185_ = l_Lean_MessageData_ofName(v_mod_2179_);
v___x_2186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2184_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = l_Lean_MessageData_note(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v_msg_2146_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2190_);
v___x_2192_ = v___x_2175_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2190_);
v___x_2192_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
return v___x_2192_;
}
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2205_; 
v___x_2194_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
lean_ctor_set(v___x_2195_, 1, v_c_2164_);
v___x_2196_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = l_Lean_MessageData_ofName(v_mod_2179_);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
v___x_2200_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_MessageData_note(v___x_2201_);
v___x_2203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2203_, 0, v_msg_2146_);
lean_ctor_set(v___x_2203_, 1, v___x_2202_);
if (v_isShared_2176_ == 0)
{
lean_ctor_set_tag(v___x_2175_, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2203_);
v___x_2205_ = v___x_2175_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v___x_2203_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2208_; 
lean_dec_ref(v_env_2152_);
lean_dec(v_declHint_2147_);
v___x_2208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2208_, 0, v_msg_2146_);
return v___x_2208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2209_, lean_object* v_declHint_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_){
_start:
{
lean_object* v_res_2213_; 
v_res_2213_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2209_, v_declHint_2210_, v___y_2211_);
lean_dec(v___y_2211_);
return v_res_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2214_, lean_object* v_declHint_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v___x_2221_; lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2231_; 
v___x_2221_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2214_, v_declHint_2215_, v___y_2219_);
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2224_ = v___x_2221_;
v_isShared_2225_ = v_isSharedCheck_2231_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2221_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2231_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2229_; 
v___x_2226_ = l_Lean_unknownIdentifierMessageTag;
v___x_2227_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2226_);
lean_ctor_set(v___x_2227_, 1, v_a_2222_);
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2227_);
v___x_2229_ = v___x_2224_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2232_, lean_object* v_declHint_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2232_, v_declHint_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2240_, lean_object* v_msg_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_toCold_2247_; lean_object* v_currRecDepth_2248_; lean_object* v_ref_2249_; uint16_t v_optionFlags_2250_; uint8_t v_suppressElabErrors_2251_; uint8_t v_isRecordingDeps_2252_; lean_object* v_ref_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; 
v_toCold_2247_ = lean_ctor_get(v___y_2244_, 0);
v_currRecDepth_2248_ = lean_ctor_get(v___y_2244_, 1);
v_ref_2249_ = lean_ctor_get(v___y_2244_, 2);
v_optionFlags_2250_ = lean_ctor_get_uint16(v___y_2244_, sizeof(void*)*3);
v_suppressElabErrors_2251_ = lean_ctor_get_uint8(v___y_2244_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2252_ = lean_ctor_get_uint8(v___y_2244_, sizeof(void*)*3 + 3);
v_ref_2253_ = l_Lean_replaceRef(v_ref_2240_, v_ref_2249_);
lean_inc(v_currRecDepth_2248_);
lean_inc_ref(v_toCold_2247_);
v___x_2254_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2254_, 0, v_toCold_2247_);
lean_ctor_set(v___x_2254_, 1, v_currRecDepth_2248_);
lean_ctor_set(v___x_2254_, 2, v_ref_2253_);
lean_ctor_set_uint16(v___x_2254_, sizeof(void*)*3, v_optionFlags_2250_);
lean_ctor_set_uint8(v___x_2254_, sizeof(void*)*3 + 2, v_suppressElabErrors_2251_);
lean_ctor_set_uint8(v___x_2254_, sizeof(void*)*3 + 3, v_isRecordingDeps_2252_);
v___x_2255_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2241_, v___y_2242_, v___y_2243_, v___x_2254_, v___y_2245_);
lean_dec_ref_known(v___x_2254_, 3);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2256_, lean_object* v_msg_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2256_, v_msg_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_ref_2256_);
return v_res_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2264_, lean_object* v_msg_2265_, lean_object* v_declHint_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___x_2272_; lean_object* v_a_2273_; lean_object* v___x_2274_; 
v___x_2272_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2265_, v_declHint_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
v_a_2273_ = lean_ctor_get(v___x_2272_, 0);
lean_inc(v_a_2273_);
lean_dec_ref(v___x_2272_);
v___x_2274_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2264_, v_a_2273_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2275_, lean_object* v_msg_2276_, lean_object* v_declHint_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2275_, v_msg_2276_, v_declHint_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec(v_ref_2275_);
return v_res_2283_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2286_ = l_Lean_stringToMessageData(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2290_, lean_object* v_constName_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_){
_start:
{
lean_object* v___x_2297_; uint8_t v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2297_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2298_ = 0;
lean_inc(v_constName_2291_);
v___x_2299_ = l_Lean_MessageData_ofConstName(v_constName_2291_, v___x_2298_);
v___x_2300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2300_, 0, v___x_2297_);
lean_ctor_set(v___x_2300_, 1, v___x_2299_);
v___x_2301_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2300_);
lean_ctor_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2290_, v___x_2302_, v_constName_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2304_, lean_object* v_constName_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2304_, v_constName_2305_, v___y_2306_, v___y_2307_, v___y_2308_, v___y_2309_);
lean_dec(v___y_2309_);
lean_dec_ref(v___y_2308_);
lean_dec(v___y_2307_);
lean_dec_ref(v___y_2306_);
lean_dec(v_ref_2304_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
lean_object* v_ref_2318_; lean_object* v___x_2319_; 
v_ref_2318_ = lean_ctor_get(v___y_2315_, 2);
v___x_2319_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2318_, v_constName_2312_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v___x_2333_; lean_object* v_env_2334_; uint8_t v___x_2335_; lean_object* v___x_2336_; 
v___x_2333_ = lean_st_ref_get(v___y_2331_);
v_env_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc_ref(v_env_2334_);
lean_dec(v___x_2333_);
v___x_2335_ = 0;
lean_inc(v_constName_2327_);
v___x_2336_ = l_Lean_Environment_findConstVal_x3f(v_env_2334_, v_constName_2327_, v___x_2335_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
return v___x_2337_;
}
else
{
lean_object* v_val_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2345_; 
lean_dec(v_constName_2327_);
v_val_2338_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2340_ = v___x_2336_;
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
else
{
lean_inc(v_val_2338_);
lean_dec(v___x_2336_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2345_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2343_; 
if (v_isShared_2341_ == 0)
{
lean_ctor_set_tag(v___x_2340_, 0);
v___x_2343_ = v___x_2340_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v_val_2338_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; 
lean_inc(v_constName_2353_);
v___x_2359_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2353_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2359_) == 0)
{
lean_object* v_a_2360_; lean_object* v_levelParams_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v_a_2360_ = lean_ctor_get(v___x_2359_, 0);
lean_inc(v_a_2360_);
lean_dec_ref_known(v___x_2359_, 1);
v_levelParams_2361_ = lean_ctor_get(v_a_2360_, 1);
v___x_2362_ = lean_box(0);
lean_inc(v_levelParams_2361_);
v___x_2363_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2361_, v___x_2362_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc_n(v_a_2364_, 2);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = l_Lean_mkConst(v_constName_2353_, v_a_2364_);
v___x_2366_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2360_, v_a_2364_, v_a_2357_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2375_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2369_ = v___x_2366_;
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_a_2367_);
lean_dec(v___x_2366_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2375_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2365_);
lean_ctor_set(v___x_2371_, 1, v_a_2367_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 0, v___x_2371_);
v___x_2373_ = v___x_2369_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v___x_2365_);
v_a_2376_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2366_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2366_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_dec(v_a_2360_);
lean_dec(v_constName_2353_);
v_a_2384_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2363_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2363_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
else
{
lean_object* v_a_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2399_; 
lean_dec(v_constName_2353_);
v_a_2392_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2394_ = v___x_2359_;
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_a_2392_);
lean_dec(v___x_2359_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2399_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2395_ == 0)
{
v___x_2397_ = v___x_2394_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_a_2392_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2400_, v_a_2401_, v_a_2402_, v_a_2403_, v_a_2404_);
lean_dec(v_a_2404_);
lean_dec_ref(v_a_2403_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2407_, lean_object* v_constName_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_, lean_object* v___y_2412_){
_start:
{
lean_object* v___x_2414_; 
v___x_2414_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2415_, lean_object* v_constName_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2415_, v_constName_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2423_, lean_object* v_ref_2424_, lean_object* v_constName_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2424_, v_constName_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_ref_2433_, lean_object* v_constName_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2432_, v_ref_2433_, v_constName_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v_ref_2433_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2441_, lean_object* v_ref_2442_, lean_object* v_msg_2443_, lean_object* v_declHint_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; 
v___x_2450_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2442_, v_msg_2443_, v_declHint_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2451_, lean_object* v_ref_2452_, lean_object* v_msg_2453_, lean_object* v_declHint_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2451_, v_ref_2452_, v_msg_2453_, v_declHint_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec_ref(v___y_2455_);
lean_dec(v_ref_2452_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2461_, lean_object* v_declHint_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v___x_2468_; 
v___x_2468_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2461_, v_declHint_2462_, v___y_2466_);
return v___x_2468_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2469_, lean_object* v_declHint_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2469_, v_declHint_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2477_, lean_object* v_ref_2478_, lean_object* v_msg_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2478_, v_msg_2479_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2486_, lean_object* v_ref_2487_, lean_object* v_msg_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2486_, v_ref_2487_, v_msg_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_);
lean_dec(v___y_2492_);
lean_dec_ref(v___y_2491_);
lean_dec(v___y_2490_);
lean_dec_ref(v___y_2489_);
lean_dec(v_ref_2487_);
return v_res_2494_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; 
v___x_2496_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2497_ = l_Lean_stringToMessageData(v___x_2496_);
return v___x_2497_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2501_, lean_object* v_f_2502_, lean_object* v_inst_2503_, lean_object* v_xs_2504_, lean_object* v_x_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2511_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2512_ = lean_apply_1(v_inst_2501_, v_f_2502_);
v___x_2513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2511_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2515_, 0, v___x_2513_);
lean_ctor_set(v___x_2515_, 1, v___x_2514_);
v___x_2516_ = lean_apply_1(v_inst_2503_, v_xs_2504_);
v___x_2517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2515_);
lean_ctor_set(v___x_2517_, 1, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
return v___x_2518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2519_, lean_object* v_f_2520_, lean_object* v_inst_2521_, lean_object* v_xs_2522_, lean_object* v_x_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2519_, v_f_2520_, v_inst_2521_, v_xs_2522_, v_x_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
lean_dec(v___y_2527_);
lean_dec_ref(v___y_2526_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec_ref(v_x_2523_);
return v_res_2529_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2530_; 
v___x_2530_ = l_instMonadEIO___redArg();
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2532_ = l_StateRefT_x27_instMonad___redArg(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2539_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2540_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2541_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2540_, v___x_2539_);
return v___x_2541_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; 
v___x_2542_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2543_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2544_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2543_, v___x_2542_);
return v___x_2544_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2547_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2548_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2549_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2550_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2549_, v___x_2548_, v___x_2547_);
return v___x_2550_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___f_2552_; lean_object* v___f_2553_; lean_object* v___x_2554_; 
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2552_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2553_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2554_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2553_, v___f_2552_, v___x_2551_);
return v___x_2554_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_instMonadExceptOfEIO___redArg();
return v___x_2555_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2557_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2556_);
return v___x_2557_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2559_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
v___x_2560_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2561_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2560_);
return v___x_2561_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; 
v___x_2562_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2563_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2562_);
return v___x_2563_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2575_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2576_ = l_Lean_Name_append(v___x_2575_, v___x_2574_);
return v___x_2576_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2583_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2584_ = l_Lean_Name_append(v___x_2583_, v___x_2582_);
return v___x_2584_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2585_; double v___x_2586_; 
v___x_2585_ = lean_unsigned_to_nat(1000000000u);
v___x_2586_ = lean_float_of_nat(v___x_2585_);
return v___x_2586_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2593_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2594_ = l_Lean_Name_append(v___x_2593_, v___x_2592_);
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2595_, lean_object* v_inst_2596_, lean_object* v_f_2597_, lean_object* v_xs_2598_, lean_object* v_k_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v___x_2605_; lean_object* v_toApplicative_2606_; lean_object* v_toFunctor_2607_; lean_object* v_toSeq_2608_; lean_object* v_toSeqLeft_2609_; lean_object* v_toSeqRight_2610_; lean_object* v___f_2611_; lean_object* v___f_2612_; lean_object* v___f_2613_; lean_object* v___f_2614_; lean_object* v___x_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___f_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v_toApplicative_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2845_; 
v___x_2605_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2606_ = lean_ctor_get(v___x_2605_, 0);
v_toFunctor_2607_ = lean_ctor_get(v_toApplicative_2606_, 0);
v_toSeq_2608_ = lean_ctor_get(v_toApplicative_2606_, 2);
v_toSeqLeft_2609_ = lean_ctor_get(v_toApplicative_2606_, 3);
v_toSeqRight_2610_ = lean_ctor_get(v_toApplicative_2606_, 4);
v___f_2611_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2612_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2607_, 2);
v___f_2613_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2613_, 0, v_toFunctor_2607_);
v___f_2614_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2614_, 0, v_toFunctor_2607_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v___f_2613_);
lean_ctor_set(v___x_2615_, 1, v___f_2614_);
lean_inc(v_toSeqRight_2610_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toSeqRight_2610_);
lean_inc(v_toSeqLeft_2609_);
v___f_2617_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2617_, 0, v_toSeqLeft_2609_);
lean_inc(v_toSeq_2608_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toSeq_2608_);
v___x_2619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2619_, 0, v___x_2615_);
lean_ctor_set(v___x_2619_, 1, v___f_2611_);
lean_ctor_set(v___x_2619_, 2, v___f_2618_);
lean_ctor_set(v___x_2619_, 3, v___f_2617_);
lean_ctor_set(v___x_2619_, 4, v___f_2616_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2619_);
lean_ctor_set(v___x_2620_, 1, v___f_2612_);
v___x_2621_ = l_StateRefT_x27_instMonad___redArg(v___x_2620_);
v_toApplicative_2622_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v___x_2621_, 1);
lean_dec(v_unused_2846_);
v___x_2624_ = v___x_2621_;
v_isShared_2625_ = v_isSharedCheck_2845_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_toApplicative_2622_);
lean_dec(v___x_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2845_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v_toFunctor_2626_; lean_object* v_toSeq_2627_; lean_object* v_toSeqLeft_2628_; lean_object* v_toSeqRight_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2843_; 
v_toFunctor_2626_ = lean_ctor_get(v_toApplicative_2622_, 0);
v_toSeq_2627_ = lean_ctor_get(v_toApplicative_2622_, 2);
v_toSeqLeft_2628_ = lean_ctor_get(v_toApplicative_2622_, 3);
v_toSeqRight_2629_ = lean_ctor_get(v_toApplicative_2622_, 4);
v_isSharedCheck_2843_ = !lean_is_exclusive(v_toApplicative_2622_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v_toApplicative_2622_, 1);
lean_dec(v_unused_2844_);
v___x_2631_ = v_toApplicative_2622_;
v_isShared_2632_ = v_isSharedCheck_2843_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_toSeqRight_2629_);
lean_inc(v_toSeqLeft_2628_);
lean_inc(v_toSeq_2627_);
lean_inc(v_toFunctor_2626_);
lean_dec(v_toApplicative_2622_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2843_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___f_2633_; lean_object* v___f_2634_; lean_object* v___f_2635_; lean_object* v___f_2636_; lean_object* v___x_2637_; lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___f_2640_; lean_object* v___x_2642_; 
v___f_2633_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2634_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2626_);
v___f_2635_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2635_, 0, v_toFunctor_2626_);
v___f_2636_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2636_, 0, v_toFunctor_2626_);
v___x_2637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2637_, 0, v___f_2635_);
lean_ctor_set(v___x_2637_, 1, v___f_2636_);
v___f_2638_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2638_, 0, v_toSeqRight_2629_);
v___f_2639_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2639_, 0, v_toSeqLeft_2628_);
v___f_2640_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2640_, 0, v_toSeq_2627_);
if (v_isShared_2632_ == 0)
{
lean_ctor_set(v___x_2631_, 4, v___f_2638_);
lean_ctor_set(v___x_2631_, 3, v___f_2639_);
lean_ctor_set(v___x_2631_, 2, v___f_2640_);
lean_ctor_set(v___x_2631_, 1, v___f_2633_);
lean_ctor_set(v___x_2631_, 0, v___x_2637_);
v___x_2642_ = v___x_2631_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2842_, 1, v___f_2633_);
lean_ctor_set(v_reuseFailAlloc_2842_, 2, v___f_2640_);
lean_ctor_set(v_reuseFailAlloc_2842_, 3, v___f_2639_);
lean_ctor_set(v_reuseFailAlloc_2842_, 4, v___f_2638_);
v___x_2642_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
lean_object* v___x_2644_; 
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 1, v___f_2634_);
lean_ctor_set(v___x_2624_, 0, v___x_2642_);
v___x_2644_ = v___x_2624_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2841_, 1, v___f_2634_);
v___x_2644_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v_toMonadRef_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_toCold_2650_; lean_object* v_options_2651_; uint8_t v_hasTrace_2652_; 
v___x_2645_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2646_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2647_ = lean_ctor_get(v___x_2646_, 0);
v___x_2648_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2649_ = l_Lean_KVMap_instValueBool;
v_toCold_2650_ = lean_ctor_get(v_a_2602_, 0);
v_options_2651_ = lean_ctor_get(v_toCold_2650_, 2);
v_hasTrace_2652_ = lean_ctor_get_uint8(v_options_2651_, sizeof(void*)*1);
if (v_hasTrace_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec_ref(v___x_2644_);
lean_dec(v_xs_2598_);
lean_dec(v_f_2597_);
lean_dec_ref(v_inst_2596_);
lean_dec_ref(v_inst_2595_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2653_ = lean_apply_5(v_k_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2653_) == 0)
{
return v___x_2653_;
}
else
{
lean_object* v_a_2654_; uint8_t v___x_2655_; 
v_a_2654_ = lean_ctor_get(v___x_2653_, 0);
lean_inc(v_a_2654_);
v___x_2655_ = l_Lean_Exception_isInterrupt(v_a_2654_);
if (v___x_2655_ == 0)
{
uint8_t v___x_2656_; 
lean_inc(v_a_2654_);
v___x_2656_ = l_Lean_Exception_isRuntime(v_a_2654_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2658_; uint8_t v_isShared_2659_; uint8_t v_isSharedCheck_2663_; 
v_isSharedCheck_2663_ = !lean_is_exclusive(v___x_2653_);
if (v_isSharedCheck_2663_ == 0)
{
lean_object* v_unused_2664_; 
v_unused_2664_ = lean_ctor_get(v___x_2653_, 0);
lean_dec(v_unused_2664_);
v___x_2658_ = v___x_2653_;
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
else
{
lean_dec(v___x_2653_);
v___x_2658_ = lean_box(0);
v_isShared_2659_ = v_isSharedCheck_2663_;
goto v_resetjp_2657_;
}
v_resetjp_2657_:
{
lean_object* v___x_2661_; 
if (v_isShared_2659_ == 0)
{
v___x_2661_ = v___x_2658_;
goto v_reusejp_2660_;
}
else
{
lean_object* v_reuseFailAlloc_2662_; 
v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2654_);
v___x_2661_ = v_reuseFailAlloc_2662_;
goto v_reusejp_2660_;
}
v_reusejp_2660_:
{
return v___x_2661_;
}
}
}
else
{
lean_dec(v_a_2654_);
return v___x_2653_;
}
}
else
{
lean_dec(v_a_2654_);
return v___x_2653_;
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2665_; lean_object* v___x_2666_; lean_object* v___y_2668_; lean_object* v_a_2669_; lean_object* v___f_2695_; lean_object* v___f_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v_a_2704_; lean_object* v___y_2718_; lean_object* v___y_2719_; lean_object* v_a_2720_; lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v_a_2725_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v_a_2730_; lean_object* v___y_2741_; lean_object* v___y_2742_; lean_object* v_a_2743_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v_a_2756_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v_a_2761_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v_a_2766_; 
v_inheritedTraceOptions_2665_ = lean_ctor_get(v_toCold_2650_, 11);
v___x_2666_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2695_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2695_, 0, v_inst_2595_);
lean_closure_set(v___f_2695_, 1, v_f_2597_);
lean_closure_set(v___f_2695_, 2, v_inst_2596_);
lean_closure_set(v___f_2695_, 3, v_xs_2598_);
v___f_2696_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2698_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2699_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2700_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2665_, v_options_2651_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2813_; lean_object* v___x_2814_; uint8_t v___x_2815_; 
v___x_2813_ = l_Lean_trace_profiler;
v___x_2814_ = l_Lean_Option_get___redArg(v___x_2649_, v_options_2651_, v___x_2813_);
v___x_2815_ = lean_unbox(v___x_2814_);
lean_dec(v___x_2814_);
if (v___x_2815_ == 0)
{
lean_object* v___x_2816_; 
lean_dec_ref(v___f_2695_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2816_ = lean_apply_5(v_k_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; uint8_t v___x_2820_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2819_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2820_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2665_, v_options_2651_, v___x_2819_);
if (v___x_2820_ == 0)
{
lean_dec(v_a_2817_);
lean_dec_ref(v___x_2644_);
return v___x_2816_;
}
else
{
lean_object* v___x_2821_; lean_object* v___x_8887__overap_2822_; lean_object* v___x_2823_; 
lean_dec_ref_known(v___x_2816_, 1);
lean_inc(v_a_2817_);
v___x_2821_ = l_Lean_MessageData_ofExpr(v_a_2817_);
lean_inc_ref(v_toMonadRef_2647_);
lean_inc_ref(v___x_2644_);
v___x_8887__overap_2822_ = l_Lean_addTrace___redArg(v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, v___x_2818_, v___x_2821_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2823_ = lean_apply_5(v___x_8887__overap_2822_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
lean_dec_ref(v___x_2644_);
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2823_, 0);
lean_dec(v_unused_2831_);
v___x_2825_ = v___x_2823_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v___x_2823_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_a_2817_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2817_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_dec(v_a_2817_);
v_a_2832_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2823_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2823_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
lean_inc(v_a_2832_);
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
v___y_2668_ = v___x_2837_;
v_a_2669_ = v_a_2832_;
goto v___jp_2667_;
}
}
}
}
}
else
{
lean_object* v_a_2840_; 
v_a_2840_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2840_);
v___y_2668_ = v___x_2816_;
v_a_2669_ = v_a_2840_;
goto v___jp_2667_;
}
}
else
{
goto v___jp_2776_;
}
}
else
{
goto v___jp_2776_;
}
v___jp_2667_:
{
uint8_t v___x_2670_; 
v___x_2670_ = l_Lean_Exception_isInterrupt(v_a_2669_);
if (v___x_2670_ == 0)
{
uint8_t v___x_2671_; 
lean_inc_ref(v_a_2669_);
v___x_2671_ = l_Lean_Exception_isRuntime(v_a_2669_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
lean_dec_ref(v___y_2668_);
v___x_2672_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2673_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2674_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2665_, v_options_2651_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec_ref(v___x_2644_);
v___x_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2675_, 0, v_a_2669_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_8704__overap_2677_; lean_object* v___x_2678_; 
lean_inc_ref(v_a_2669_);
v___x_2676_ = l_Lean_Exception_toMessageData(v_a_2669_);
lean_inc_ref(v_toMonadRef_2647_);
v___x_8704__overap_2677_ = l_Lean_addTrace___redArg(v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, v___x_2672_, v___x_2676_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2678_ = lean_apply_5(v___x_8704__overap_2677_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2686_);
v___x_2680_ = v___x_2678_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v___x_2678_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set_tag(v___x_2680_, 1);
lean_ctor_set(v___x_2680_, 0, v_a_2669_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2669_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec_ref(v_a_2669_);
v_a_2687_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2678_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2678_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_2669_);
lean_dec_ref(v___x_2644_);
return v___y_2668_;
}
}
else
{
lean_dec_ref(v_a_2669_);
lean_dec_ref(v___x_2644_);
return v___y_2668_;
}
}
v___jp_2701_:
{
lean_object* v___x_2705_; double v___x_2706_; double v___x_2707_; double v___x_2708_; double v___x_2709_; double v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_8763__overap_2715_; lean_object* v___x_2716_; 
v___x_2705_ = lean_io_mono_nanos_now();
v___x_2706_ = lean_float_of_nat(v___y_2702_);
v___x_2707_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2708_ = lean_float_div(v___x_2706_, v___x_2707_);
v___x_2709_ = lean_float_of_nat(v___x_2705_);
v___x_2710_ = lean_float_div(v___x_2709_, v___x_2707_);
v___x_2711_ = lean_box_float(v___x_2708_);
v___x_2712_ = lean_box_float(v___x_2710_);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___x_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2714_, 0, v_a_2704_);
lean_ctor_set(v___x_2714_, 1, v___x_2713_);
lean_inc_ref(v_toMonadRef_2647_);
v___x_8763__overap_2715_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, lean_box(0), v___x_2648_, v___f_2696_, v___x_2697_, v_hasTrace_2652_, v___x_2698_, v_options_2651_, v___x_2700_, v___y_2703_, v___f_2695_, v___x_2714_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2716_ = lean_apply_5(v___x_8763__overap_2715_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
return v___x_2716_;
}
v___jp_2717_:
{
lean_object* v___x_2721_; 
v___x_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2721_, 0, v_a_2720_);
v___y_2702_ = v___y_2718_;
v___y_2703_ = v___y_2719_;
v_a_2704_ = v___x_2721_;
goto v___jp_2701_;
}
v___jp_2722_:
{
lean_object* v___x_2726_; 
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v_a_2725_);
v___y_2702_ = v___y_2723_;
v___y_2703_ = v___y_2724_;
v_a_2704_ = v___x_2726_;
goto v___jp_2701_;
}
v___jp_2727_:
{
uint8_t v___x_2731_; 
v___x_2731_ = l_Lean_Exception_isInterrupt(v_a_2730_);
if (v___x_2731_ == 0)
{
uint8_t v___x_2732_; 
lean_inc_ref(v_a_2730_);
v___x_2732_ = l_Lean_Exception_isRuntime(v_a_2730_);
if (v___x_2732_ == 0)
{
lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v___x_2735_; 
v___x_2733_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2734_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2665_, v_options_2651_, v___x_2734_);
if (v___x_2735_ == 0)
{
v___y_2723_ = v___y_2728_;
v___y_2724_ = v___y_2729_;
v_a_2725_ = v_a_2730_;
goto v___jp_2722_;
}
else
{
lean_object* v___x_2736_; lean_object* v___x_8782__overap_2737_; lean_object* v___x_2738_; 
lean_inc_ref(v_a_2730_);
v___x_2736_ = l_Lean_Exception_toMessageData(v_a_2730_);
lean_inc_ref(v_toMonadRef_2647_);
lean_inc_ref(v___x_2644_);
v___x_8782__overap_2737_ = l_Lean_addTrace___redArg(v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, v___x_2733_, v___x_2736_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2738_ = lean_apply_5(v___x_8782__overap_2737_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_dec_ref_known(v___x_2738_, 1);
v___y_2723_ = v___y_2728_;
v___y_2724_ = v___y_2729_;
v_a_2725_ = v_a_2730_;
goto v___jp_2722_;
}
else
{
lean_object* v_a_2739_; 
lean_dec_ref(v_a_2730_);
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
v___y_2723_ = v___y_2728_;
v___y_2724_ = v___y_2729_;
v_a_2725_ = v_a_2739_;
goto v___jp_2722_;
}
}
}
else
{
v___y_2723_ = v___y_2728_;
v___y_2724_ = v___y_2729_;
v_a_2725_ = v_a_2730_;
goto v___jp_2722_;
}
}
else
{
v___y_2723_ = v___y_2728_;
v___y_2724_ = v___y_2729_;
v_a_2725_ = v_a_2730_;
goto v___jp_2722_;
}
}
v___jp_2740_:
{
lean_object* v___x_2744_; double v___x_2745_; double v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_8823__overap_2751_; lean_object* v___x_2752_; 
v___x_2744_ = lean_io_get_num_heartbeats();
v___x_2745_ = lean_float_of_nat(v___y_2742_);
v___x_2746_ = lean_float_of_nat(v___x_2744_);
v___x_2747_ = lean_box_float(v___x_2745_);
v___x_2748_ = lean_box_float(v___x_2746_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2747_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
v___x_2750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2750_, 0, v_a_2743_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
lean_inc_ref(v_toMonadRef_2647_);
v___x_8823__overap_2751_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, lean_box(0), v___x_2648_, v___f_2696_, v___x_2697_, v_hasTrace_2652_, v___x_2698_, v_options_2651_, v___x_2700_, v___y_2741_, v___f_2695_, v___x_2750_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2752_ = lean_apply_5(v___x_8823__overap_2751_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
return v___x_2752_;
}
v___jp_2753_:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2757_, 0, v_a_2756_);
v___y_2741_ = v___y_2754_;
v___y_2742_ = v___y_2755_;
v_a_2743_ = v___x_2757_;
goto v___jp_2740_;
}
v___jp_2758_:
{
lean_object* v___x_2762_; 
v___x_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2762_, 0, v_a_2761_);
v___y_2741_ = v___y_2759_;
v___y_2742_ = v___y_2760_;
v_a_2743_ = v___x_2762_;
goto v___jp_2740_;
}
v___jp_2763_:
{
uint8_t v___x_2767_; 
v___x_2767_ = l_Lean_Exception_isInterrupt(v_a_2766_);
if (v___x_2767_ == 0)
{
uint8_t v___x_2768_; 
lean_inc_ref(v_a_2766_);
v___x_2768_ = l_Lean_Exception_isRuntime(v_a_2766_);
if (v___x_2768_ == 0)
{
lean_object* v___x_2769_; lean_object* v___x_2770_; uint8_t v___x_2771_; 
v___x_2769_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2770_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2665_, v_options_2651_, v___x_2770_);
if (v___x_2771_ == 0)
{
v___y_2759_ = v___y_2764_;
v___y_2760_ = v___y_2765_;
v_a_2761_ = v_a_2766_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2772_; lean_object* v___x_8842__overap_2773_; lean_object* v___x_2774_; 
lean_inc_ref(v_a_2766_);
v___x_2772_ = l_Lean_Exception_toMessageData(v_a_2766_);
lean_inc_ref(v_toMonadRef_2647_);
lean_inc_ref(v___x_2644_);
v___x_8842__overap_2773_ = l_Lean_addTrace___redArg(v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, v___x_2769_, v___x_2772_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2774_ = lean_apply_5(v___x_8842__overap_2773_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_dec_ref_known(v___x_2774_, 1);
v___y_2759_ = v___y_2764_;
v___y_2760_ = v___y_2765_;
v_a_2761_ = v_a_2766_;
goto v___jp_2758_;
}
else
{
lean_object* v_a_2775_; 
lean_dec_ref(v_a_2766_);
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___y_2759_ = v___y_2764_;
v___y_2760_ = v___y_2765_;
v_a_2761_ = v_a_2775_;
goto v___jp_2758_;
}
}
}
else
{
v___y_2759_ = v___y_2764_;
v___y_2760_ = v___y_2765_;
v_a_2761_ = v_a_2766_;
goto v___jp_2758_;
}
}
else
{
v___y_2759_ = v___y_2764_;
v___y_2760_ = v___y_2765_;
v_a_2761_ = v_a_2766_;
goto v___jp_2758_;
}
}
v___jp_2776_:
{
lean_object* v___x_8741__overap_2777_; lean_object* v___x_2778_; 
lean_inc_ref(v___x_2644_);
v___x_8741__overap_2777_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2644_, v___x_2645_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2778_ = lean_apply_5(v___x_8741__overap_2777_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2781_ = l_Lean_Option_get___redArg(v___x_2649_, v_options_2651_, v___x_2780_);
v___x_2782_ = lean_unbox(v___x_2781_);
lean_dec(v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_io_mono_nanos_now();
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2784_ = lean_apply_5(v_k_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; uint8_t v___x_2788_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref_known(v___x_2784_, 1);
v___x_2786_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2787_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2665_, v_options_2651_, v___x_2787_);
if (v___x_2788_ == 0)
{
v___y_2718_ = v___x_2783_;
v___y_2719_ = v_a_2779_;
v_a_2720_ = v_a_2785_;
goto v___jp_2717_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_8803__overap_2790_; lean_object* v___x_2791_; 
lean_inc(v_a_2785_);
v___x_2789_ = l_Lean_MessageData_ofExpr(v_a_2785_);
lean_inc_ref(v_toMonadRef_2647_);
lean_inc_ref(v___x_2644_);
v___x_8803__overap_2790_ = l_Lean_addTrace___redArg(v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, v___x_2786_, v___x_2789_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2791_ = lean_apply_5(v___x_8803__overap_2790_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_dec_ref_known(v___x_2791_, 1);
v___y_2718_ = v___x_2783_;
v___y_2719_ = v_a_2779_;
v_a_2720_ = v_a_2785_;
goto v___jp_2717_;
}
else
{
lean_object* v_a_2792_; 
lean_dec(v_a_2785_);
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___y_2728_ = v___x_2783_;
v___y_2729_ = v_a_2779_;
v_a_2730_ = v_a_2792_;
goto v___jp_2727_;
}
}
}
else
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2784_, 1);
v___y_2728_ = v___x_2783_;
v___y_2729_ = v_a_2779_;
v_a_2730_ = v_a_2793_;
goto v___jp_2727_;
}
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2795_ = lean_apply_5(v_k_2599_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v_a_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; uint8_t v___x_2799_; 
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v___x_2797_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2798_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2665_, v_options_2651_, v___x_2798_);
if (v___x_2799_ == 0)
{
v___y_2754_ = v_a_2779_;
v___y_2755_ = v___x_2794_;
v_a_2756_ = v_a_2796_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2800_; lean_object* v___x_8863__overap_2801_; lean_object* v___x_2802_; 
lean_inc(v_a_2796_);
v___x_2800_ = l_Lean_MessageData_ofExpr(v_a_2796_);
lean_inc_ref(v_toMonadRef_2647_);
lean_inc_ref(v___x_2644_);
v___x_8863__overap_2801_ = l_Lean_addTrace___redArg(v___x_2644_, v___x_2645_, v_toMonadRef_2647_, v___x_2666_, v___x_2797_, v___x_2800_);
lean_inc(v_a_2603_);
lean_inc_ref(v_a_2602_);
lean_inc(v_a_2601_);
lean_inc_ref(v_a_2600_);
v___x_2802_ = lean_apply_5(v___x_8863__overap_2801_, v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_, lean_box(0));
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_dec_ref_known(v___x_2802_, 1);
v___y_2754_ = v_a_2779_;
v___y_2755_ = v___x_2794_;
v_a_2756_ = v_a_2796_;
goto v___jp_2753_;
}
else
{
lean_object* v_a_2803_; 
lean_dec(v_a_2796_);
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
v___y_2764_ = v_a_2779_;
v___y_2765_ = v___x_2794_;
v_a_2766_ = v_a_2803_;
goto v___jp_2763_;
}
}
}
else
{
lean_object* v_a_2804_; 
v_a_2804_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2795_, 1);
v___y_2764_ = v_a_2779_;
v___y_2765_ = v___x_2794_;
v_a_2766_ = v_a_2804_;
goto v___jp_2763_;
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec_ref(v___f_2695_);
lean_dec_ref(v___x_2644_);
lean_dec_ref(v_k_2599_);
v_a_2805_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2778_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2778_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2847_, lean_object* v_inst_2848_, lean_object* v_f_2849_, lean_object* v_xs_2850_, lean_object* v_k_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_, lean_object* v_a_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2847_, v_inst_2848_, v_f_2849_, v_xs_2850_, v_k_2851_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
lean_dec(v_a_2855_);
lean_dec_ref(v_a_2854_);
lean_dec(v_a_2853_);
lean_dec_ref(v_a_2852_);
return v_res_2857_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2858_, lean_object* v_00_u03b2_2859_, lean_object* v_inst_2860_, lean_object* v_inst_2861_, lean_object* v_f_2862_, lean_object* v_xs_2863_, lean_object* v_k_2864_, lean_object* v_a_2865_, lean_object* v_a_2866_, lean_object* v_a_2867_, lean_object* v_a_2868_){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2860_, v_inst_2861_, v_f_2862_, v_xs_2863_, v_k_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_);
return v___x_2870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2871_, lean_object* v_00_u03b2_2872_, lean_object* v_inst_2873_, lean_object* v_inst_2874_, lean_object* v_f_2875_, lean_object* v_xs_2876_, lean_object* v_k_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_, lean_object* v_a_2880_, lean_object* v_a_2881_, lean_object* v_a_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2871_, v_00_u03b2_2872_, v_inst_2873_, v_inst_2874_, v_f_2875_, v_xs_2876_, v_k_2877_, v_a_2878_, v_a_2879_, v_a_2880_, v_a_2881_);
lean_dec(v_a_2881_);
lean_dec_ref(v_a_2880_);
lean_dec(v_a_2879_);
lean_dec_ref(v_a_2878_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2884_, uint8_t v_allowLevelAssignments_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v___x_2891_; 
v___x_2891_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2885_, v_k_2884_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
v_a_2900_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2891_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2891_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2908_, lean_object* v_allowLevelAssignments_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2915_; lean_object* v_res_2916_; 
v_allowLevelAssignments_boxed_2915_ = lean_unbox(v_allowLevelAssignments_2909_);
v_res_2916_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2908_, v_allowLevelAssignments_boxed_2915_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2917_, lean_object* v_k_2918_, uint8_t v_allowLevelAssignments_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v___x_2925_; 
v___x_2925_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2918_, v_allowLevelAssignments_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2926_, lean_object* v_k_2927_, lean_object* v_allowLevelAssignments_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2934_; lean_object* v_res_2935_; 
v_allowLevelAssignments_boxed_2934_ = lean_unbox(v_allowLevelAssignments_2928_);
v_res_2935_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2926_, v_k_2927_, v_allowLevelAssignments_boxed_2934_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2936_, lean_object* v_xs_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v___x_2943_; 
v___x_2943_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2936_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v_a_2944_; lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___x_2947_; 
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref_known(v___x_2943_, 1);
v_fst_2945_ = lean_ctor_get(v_a_2944_, 0);
lean_inc(v_fst_2945_);
v_snd_2946_ = lean_ctor_get(v_a_2944_, 1);
lean_inc(v_snd_2946_);
lean_dec(v_a_2944_);
v___x_2947_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2945_, v_snd_2946_, v_xs_2937_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
return v___x_2947_;
}
else
{
lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v_a_2948_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2943_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2943_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2956_, lean_object* v_xs_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_, lean_object* v___y_2962_){
_start:
{
lean_object* v_res_2963_; 
v_res_2963_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2956_, v_xs_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
lean_dec(v___y_2961_);
lean_dec_ref(v___y_2960_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v_xs_2957_);
return v_res_2963_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2964_ = lean_unsigned_to_nat(32u);
v___x_2965_ = lean_mk_empty_array_with_capacity(v___x_2964_);
v___x_2966_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2966_, 0, v___x_2965_);
return v___x_2966_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2967_ = ((size_t)5ULL);
v___x_2968_ = lean_unsigned_to_nat(0u);
v___x_2969_ = lean_unsigned_to_nat(32u);
v___x_2970_ = lean_mk_empty_array_with_capacity(v___x_2969_);
v___x_2971_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2972_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
lean_ctor_set(v___x_2972_, 1, v___x_2970_);
lean_ctor_set(v___x_2972_, 2, v___x_2968_);
lean_ctor_set(v___x_2972_, 3, v___x_2968_);
lean_ctor_set_usize(v___x_2972_, 4, v___x_2967_);
return v___x_2972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; lean_object* v_traceState_2976_; lean_object* v_traces_2977_; lean_object* v___x_2978_; lean_object* v_traceState_2979_; lean_object* v_env_2980_; lean_object* v_nextMacroScope_2981_; lean_object* v_ngen_2982_; lean_object* v_auxDeclNGen_2983_; lean_object* v_cache_2984_; lean_object* v_recordedDeps_2985_; lean_object* v_messages_2986_; lean_object* v_infoState_2987_; lean_object* v_snapshotTasks_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_3007_; 
v___x_2975_ = lean_st_ref_get(v___y_2973_);
v_traceState_2976_ = lean_ctor_get(v___x_2975_, 4);
lean_inc_ref(v_traceState_2976_);
lean_dec(v___x_2975_);
v_traces_2977_ = lean_ctor_get(v_traceState_2976_, 0);
lean_inc_ref(v_traces_2977_);
lean_dec_ref(v_traceState_2976_);
v___x_2978_ = lean_st_ref_take(v___y_2973_);
v_traceState_2979_ = lean_ctor_get(v___x_2978_, 4);
v_env_2980_ = lean_ctor_get(v___x_2978_, 0);
v_nextMacroScope_2981_ = lean_ctor_get(v___x_2978_, 1);
v_ngen_2982_ = lean_ctor_get(v___x_2978_, 2);
v_auxDeclNGen_2983_ = lean_ctor_get(v___x_2978_, 3);
v_cache_2984_ = lean_ctor_get(v___x_2978_, 5);
v_recordedDeps_2985_ = lean_ctor_get(v___x_2978_, 6);
v_messages_2986_ = lean_ctor_get(v___x_2978_, 7);
v_infoState_2987_ = lean_ctor_get(v___x_2978_, 8);
v_snapshotTasks_2988_ = lean_ctor_get(v___x_2978_, 9);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2990_ = v___x_2978_;
v_isShared_2991_ = v_isSharedCheck_3007_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_snapshotTasks_2988_);
lean_inc(v_infoState_2987_);
lean_inc(v_messages_2986_);
lean_inc(v_recordedDeps_2985_);
lean_inc(v_cache_2984_);
lean_inc(v_traceState_2979_);
lean_inc(v_auxDeclNGen_2983_);
lean_inc(v_ngen_2982_);
lean_inc(v_nextMacroScope_2981_);
lean_inc(v_env_2980_);
lean_dec(v___x_2978_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_3007_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
uint64_t v_tid_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_3005_; 
v_tid_2992_ = lean_ctor_get_uint64(v_traceState_2979_, sizeof(void*)*1);
v_isSharedCheck_3005_ = !lean_is_exclusive(v_traceState_2979_);
if (v_isSharedCheck_3005_ == 0)
{
lean_object* v_unused_3006_; 
v_unused_3006_ = lean_ctor_get(v_traceState_2979_, 0);
lean_dec(v_unused_3006_);
v___x_2994_ = v_traceState_2979_;
v_isShared_2995_ = v_isSharedCheck_3005_;
goto v_resetjp_2993_;
}
else
{
lean_dec(v_traceState_2979_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_3005_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2996_; lean_object* v___x_2998_; 
v___x_2996_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_2995_ == 0)
{
lean_ctor_set(v___x_2994_, 0, v___x_2996_);
v___x_2998_ = v___x_2994_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v___x_2996_);
lean_ctor_set_uint64(v_reuseFailAlloc_3004_, sizeof(void*)*1, v_tid_2992_);
v___x_2998_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
lean_object* v___x_3000_; 
if (v_isShared_2991_ == 0)
{
lean_ctor_set(v___x_2990_, 4, v___x_2998_);
v___x_3000_ = v___x_2990_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_env_2980_);
lean_ctor_set(v_reuseFailAlloc_3003_, 1, v_nextMacroScope_2981_);
lean_ctor_set(v_reuseFailAlloc_3003_, 2, v_ngen_2982_);
lean_ctor_set(v_reuseFailAlloc_3003_, 3, v_auxDeclNGen_2983_);
lean_ctor_set(v_reuseFailAlloc_3003_, 4, v___x_2998_);
lean_ctor_set(v_reuseFailAlloc_3003_, 5, v_cache_2984_);
lean_ctor_set(v_reuseFailAlloc_3003_, 6, v_recordedDeps_2985_);
lean_ctor_set(v_reuseFailAlloc_3003_, 7, v_messages_2986_);
lean_ctor_set(v_reuseFailAlloc_3003_, 8, v_infoState_2987_);
lean_ctor_set(v_reuseFailAlloc_3003_, 9, v_snapshotTasks_2988_);
v___x_3000_ = v_reuseFailAlloc_3003_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3001_; lean_object* v___x_3002_; 
v___x_3001_ = lean_st_ref_put(v___y_2973_, v___x_3000_);
v___x_3002_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3002_, 0, v_traces_2977_);
return v___x_3002_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3008_, lean_object* v___y_3009_){
_start:
{
lean_object* v_res_3010_; 
v_res_3010_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3008_);
lean_dec(v___y_3008_);
return v_res_3010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3011_, lean_object* v_opt_3012_){
_start:
{
lean_object* v_name_3013_; lean_object* v_defValue_3014_; lean_object* v_map_3015_; lean_object* v___x_3016_; 
v_name_3013_ = lean_ctor_get(v_opt_3012_, 0);
v_defValue_3014_ = lean_ctor_get(v_opt_3012_, 1);
v_map_3015_ = lean_ctor_get(v_opts_3011_, 0);
v___x_3016_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3015_, v_name_3013_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_inc(v_defValue_3014_);
return v_defValue_3014_;
}
else
{
lean_object* v_val_3017_; 
v_val_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_val_3017_);
lean_dec_ref_known(v___x_3016_, 1);
if (lean_obj_tag(v_val_3017_) == 3)
{
lean_object* v_v_3018_; 
v_v_3018_ = lean_ctor_get(v_val_3017_, 0);
lean_inc(v_v_3018_);
lean_dec_ref_known(v_val_3017_, 1);
return v_v_3018_;
}
else
{
lean_dec(v_val_3017_);
lean_inc(v_defValue_3014_);
return v_defValue_3014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3019_, lean_object* v_opt_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3019_, v_opt_3020_);
lean_dec_ref(v_opt_3020_);
lean_dec_ref(v_opts_3019_);
return v_res_3021_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3022_, lean_object* v_opt_3023_){
_start:
{
lean_object* v_name_3024_; lean_object* v_defValue_3025_; lean_object* v_map_3026_; lean_object* v___x_3027_; 
v_name_3024_ = lean_ctor_get(v_opt_3023_, 0);
v_defValue_3025_ = lean_ctor_get(v_opt_3023_, 1);
v_map_3026_ = lean_ctor_get(v_opts_3022_, 0);
v___x_3027_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3026_, v_name_3024_);
if (lean_obj_tag(v___x_3027_) == 0)
{
uint8_t v___x_3028_; 
v___x_3028_ = lean_unbox(v_defValue_3025_);
return v___x_3028_;
}
else
{
lean_object* v_val_3029_; 
v_val_3029_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_val_3029_);
lean_dec_ref_known(v___x_3027_, 1);
if (lean_obj_tag(v_val_3029_) == 1)
{
uint8_t v_v_3030_; 
v_v_3030_ = lean_ctor_get_uint8(v_val_3029_, 0);
lean_dec_ref_known(v_val_3029_, 0);
return v_v_3030_;
}
else
{
uint8_t v___x_3031_; 
lean_dec(v_val_3029_);
v___x_3031_ = lean_unbox(v_defValue_3025_);
return v___x_3031_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3032_, lean_object* v_opt_3033_){
_start:
{
uint8_t v_res_3034_; lean_object* v_r_3035_; 
v_res_3034_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3032_, v_opt_3033_);
lean_dec_ref(v_opt_3033_);
lean_dec_ref(v_opts_3032_);
v_r_3035_ = lean_box(v_res_3034_);
return v_r_3035_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3036_){
_start:
{
if (lean_obj_tag(v_e_3036_) == 0)
{
uint8_t v___x_3037_; 
v___x_3037_ = 2;
return v___x_3037_;
}
else
{
lean_object* v_a_3038_; uint8_t v___x_3039_; 
v_a_3038_ = lean_ctor_get(v_e_3036_, 0);
v___x_3039_ = l_Lean_Expr_hasSyntheticSorry(v_a_3038_);
if (v___x_3039_ == 0)
{
uint8_t v___x_3040_; 
v___x_3040_ = 0;
return v___x_3040_;
}
else
{
uint8_t v___x_3041_; 
v___x_3041_ = 1;
return v___x_3041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3042_);
lean_dec_ref(v_e_3042_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3045_, size_t v_i_3046_, lean_object* v_bs_3047_){
_start:
{
uint8_t v___x_3048_; 
v___x_3048_ = lean_usize_dec_lt(v_i_3046_, v_sz_3045_);
if (v___x_3048_ == 0)
{
return v_bs_3047_;
}
else
{
lean_object* v_v_3049_; lean_object* v_msg_3050_; lean_object* v___x_3051_; lean_object* v_bs_x27_3052_; size_t v___x_3053_; size_t v___x_3054_; lean_object* v___x_3055_; 
v_v_3049_ = lean_array_uget_borrowed(v_bs_3047_, v_i_3046_);
v_msg_3050_ = lean_ctor_get(v_v_3049_, 1);
lean_inc_ref(v_msg_3050_);
v___x_3051_ = lean_unsigned_to_nat(0u);
v_bs_x27_3052_ = lean_array_uset(v_bs_3047_, v_i_3046_, v___x_3051_);
v___x_3053_ = ((size_t)1ULL);
v___x_3054_ = lean_usize_add(v_i_3046_, v___x_3053_);
v___x_3055_ = lean_array_uset(v_bs_x27_3052_, v_i_3046_, v_msg_3050_);
v_i_3046_ = v___x_3054_;
v_bs_3047_ = v___x_3055_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3057_, lean_object* v_i_3058_, lean_object* v_bs_3059_){
_start:
{
size_t v_sz_boxed_3060_; size_t v_i_boxed_3061_; lean_object* v_res_3062_; 
v_sz_boxed_3060_ = lean_unbox_usize(v_sz_3057_);
lean_dec(v_sz_3057_);
v_i_boxed_3061_ = lean_unbox_usize(v_i_3058_);
lean_dec(v_i_3058_);
v_res_3062_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3060_, v_i_boxed_3061_, v_bs_3059_);
return v_res_3062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3063_, lean_object* v_data_3064_, lean_object* v_ref_3065_, lean_object* v_msg_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v_toCold_3072_; lean_object* v_currRecDepth_3073_; lean_object* v_ref_3074_; uint16_t v_optionFlags_3075_; uint8_t v_suppressElabErrors_3076_; uint8_t v_isRecordingDeps_3077_; lean_object* v_ref_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v_traceState_3081_; lean_object* v_traces_3082_; lean_object* v___x_3083_; size_t v_sz_3084_; size_t v___x_3085_; lean_object* v___x_3086_; lean_object* v_msg_3087_; lean_object* v___x_3088_; lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3127_; 
v_toCold_3072_ = lean_ctor_get(v___y_3069_, 0);
v_currRecDepth_3073_ = lean_ctor_get(v___y_3069_, 1);
v_ref_3074_ = lean_ctor_get(v___y_3069_, 2);
v_optionFlags_3075_ = lean_ctor_get_uint16(v___y_3069_, sizeof(void*)*3);
v_suppressElabErrors_3076_ = lean_ctor_get_uint8(v___y_3069_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3077_ = lean_ctor_get_uint8(v___y_3069_, sizeof(void*)*3 + 3);
v_ref_3078_ = l_Lean_replaceRef(v_ref_3065_, v_ref_3074_);
lean_inc(v_currRecDepth_3073_);
lean_inc_ref(v_toCold_3072_);
v___x_3079_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3079_, 0, v_toCold_3072_);
lean_ctor_set(v___x_3079_, 1, v_currRecDepth_3073_);
lean_ctor_set(v___x_3079_, 2, v_ref_3078_);
lean_ctor_set_uint16(v___x_3079_, sizeof(void*)*3, v_optionFlags_3075_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3 + 2, v_suppressElabErrors_3076_);
lean_ctor_set_uint8(v___x_3079_, sizeof(void*)*3 + 3, v_isRecordingDeps_3077_);
v___x_3080_ = lean_st_ref_get(v___y_3070_);
v_traceState_3081_ = lean_ctor_get(v___x_3080_, 4);
lean_inc_ref(v_traceState_3081_);
lean_dec(v___x_3080_);
v_traces_3082_ = lean_ctor_get(v_traceState_3081_, 0);
lean_inc_ref(v_traces_3082_);
lean_dec_ref(v_traceState_3081_);
v___x_3083_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3082_);
lean_dec_ref(v_traces_3082_);
v_sz_3084_ = lean_array_size(v___x_3083_);
v___x_3085_ = ((size_t)0ULL);
v___x_3086_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3084_, v___x_3085_, v___x_3083_);
v_msg_3087_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3087_, 0, v_data_3064_);
lean_ctor_set(v_msg_3087_, 1, v_msg_3066_);
lean_ctor_set(v_msg_3087_, 2, v___x_3086_);
v___x_3088_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3087_, v___y_3067_, v___y_3068_, v___x_3079_, v___y_3070_);
lean_dec_ref_known(v___x_3079_, 3);
v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3088_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3091_ = v___x_3088_;
v_isShared_3092_ = v_isSharedCheck_3127_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3088_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3127_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3093_; lean_object* v_traceState_3094_; lean_object* v_env_3095_; lean_object* v_nextMacroScope_3096_; lean_object* v_ngen_3097_; lean_object* v_auxDeclNGen_3098_; lean_object* v_cache_3099_; lean_object* v_recordedDeps_3100_; lean_object* v_messages_3101_; lean_object* v_infoState_3102_; lean_object* v_snapshotTasks_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3126_; 
v___x_3093_ = lean_st_ref_take(v___y_3070_);
v_traceState_3094_ = lean_ctor_get(v___x_3093_, 4);
v_env_3095_ = lean_ctor_get(v___x_3093_, 0);
v_nextMacroScope_3096_ = lean_ctor_get(v___x_3093_, 1);
v_ngen_3097_ = lean_ctor_get(v___x_3093_, 2);
v_auxDeclNGen_3098_ = lean_ctor_get(v___x_3093_, 3);
v_cache_3099_ = lean_ctor_get(v___x_3093_, 5);
v_recordedDeps_3100_ = lean_ctor_get(v___x_3093_, 6);
v_messages_3101_ = lean_ctor_get(v___x_3093_, 7);
v_infoState_3102_ = lean_ctor_get(v___x_3093_, 8);
v_snapshotTasks_3103_ = lean_ctor_get(v___x_3093_, 9);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3105_ = v___x_3093_;
v_isShared_3106_ = v_isSharedCheck_3126_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_snapshotTasks_3103_);
lean_inc(v_infoState_3102_);
lean_inc(v_messages_3101_);
lean_inc(v_recordedDeps_3100_);
lean_inc(v_cache_3099_);
lean_inc(v_traceState_3094_);
lean_inc(v_auxDeclNGen_3098_);
lean_inc(v_ngen_3097_);
lean_inc(v_nextMacroScope_3096_);
lean_inc(v_env_3095_);
lean_dec(v___x_3093_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3126_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
uint64_t v_tid_3107_; lean_object* v___x_3109_; uint8_t v_isShared_3110_; uint8_t v_isSharedCheck_3124_; 
v_tid_3107_ = lean_ctor_get_uint64(v_traceState_3094_, sizeof(void*)*1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_traceState_3094_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_traceState_3094_, 0);
lean_dec(v_unused_3125_);
v___x_3109_ = v_traceState_3094_;
v_isShared_3110_ = v_isSharedCheck_3124_;
goto v_resetjp_3108_;
}
else
{
lean_dec(v_traceState_3094_);
v___x_3109_ = lean_box(0);
v_isShared_3110_ = v_isSharedCheck_3124_;
goto v_resetjp_3108_;
}
v_resetjp_3108_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v___x_3111_ = lean_box(0);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v_ref_3065_);
lean_ctor_set(v___x_3112_, 1, v_a_3089_);
v___x_3113_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3063_, v___x_3112_);
if (v_isShared_3110_ == 0)
{
lean_ctor_set(v___x_3109_, 0, v___x_3113_);
v___x_3115_ = v___x_3109_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3113_);
lean_ctor_set_uint64(v_reuseFailAlloc_3123_, sizeof(void*)*1, v_tid_3107_);
v___x_3115_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3117_; 
if (v_isShared_3106_ == 0)
{
lean_ctor_set(v___x_3105_, 4, v___x_3115_);
v___x_3117_ = v___x_3105_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_env_3095_);
lean_ctor_set(v_reuseFailAlloc_3122_, 1, v_nextMacroScope_3096_);
lean_ctor_set(v_reuseFailAlloc_3122_, 2, v_ngen_3097_);
lean_ctor_set(v_reuseFailAlloc_3122_, 3, v_auxDeclNGen_3098_);
lean_ctor_set(v_reuseFailAlloc_3122_, 4, v___x_3115_);
lean_ctor_set(v_reuseFailAlloc_3122_, 5, v_cache_3099_);
lean_ctor_set(v_reuseFailAlloc_3122_, 6, v_recordedDeps_3100_);
lean_ctor_set(v_reuseFailAlloc_3122_, 7, v_messages_3101_);
lean_ctor_set(v_reuseFailAlloc_3122_, 8, v_infoState_3102_);
lean_ctor_set(v_reuseFailAlloc_3122_, 9, v_snapshotTasks_3103_);
v___x_3117_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3118_ = lean_st_ref_put(v___y_3070_, v___x_3117_);
if (v_isShared_3092_ == 0)
{
lean_ctor_set(v___x_3091_, 0, v___x_3111_);
v___x_3120_ = v___x_3091_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v___x_3111_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3128_, lean_object* v_data_3129_, lean_object* v_ref_3130_, lean_object* v_msg_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3128_, v_data_3129_, v_ref_3130_, v_msg_3131_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
lean_dec(v___y_3133_);
lean_dec_ref(v___y_3132_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3138_){
_start:
{
if (lean_obj_tag(v_x_3138_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v_x_3138_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v_x_3138_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v_x_3138_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v_x_3138_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
lean_ctor_set_tag(v___x_3142_, 1);
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v_x_3138_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v_x_3138_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v_x_3138_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v_x_3138_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 0);
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_res_3158_; 
v_res_3158_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3156_);
return v_res_3158_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3159_; double v___x_3160_; 
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = lean_float_of_nat(v___x_3159_);
return v___x_3160_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3163_ = l_Lean_stringToMessageData(v___x_3162_);
return v___x_3163_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3164_; double v___x_3165_; 
v___x_3164_ = lean_unsigned_to_nat(1000u);
v___x_3165_ = lean_float_of_nat(v___x_3164_);
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3166_, uint8_t v_collapsed_3167_, lean_object* v_tag_3168_, lean_object* v_opts_3169_, uint8_t v_clsEnabled_3170_, lean_object* v_oldTraces_3171_, lean_object* v_msg_3172_, lean_object* v_resStartStop_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
lean_object* v_fst_3179_; lean_object* v_snd_3180_; lean_object* v___y_3182_; lean_object* v___y_3183_; lean_object* v_data_3184_; lean_object* v_fst_3195_; lean_object* v_snd_3196_; lean_object* v___x_3197_; uint8_t v___x_3198_; lean_object* v___y_3200_; lean_object* v_a_3201_; uint8_t v___y_3216_; double v___y_3248_; 
v_fst_3179_ = lean_ctor_get(v_resStartStop_3173_, 0);
lean_inc(v_fst_3179_);
v_snd_3180_ = lean_ctor_get(v_resStartStop_3173_, 1);
lean_inc(v_snd_3180_);
lean_dec_ref(v_resStartStop_3173_);
v_fst_3195_ = lean_ctor_get(v_snd_3180_, 0);
lean_inc(v_fst_3195_);
v_snd_3196_ = lean_ctor_get(v_snd_3180_, 1);
lean_inc(v_snd_3196_);
lean_dec(v_snd_3180_);
v___x_3197_ = l_Lean_trace_profiler;
v___x_3198_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3169_, v___x_3197_);
if (v___x_3198_ == 0)
{
v___y_3216_ = v___x_3198_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3254_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3169_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; double v___x_3257_; double v___x_3258_; double v___x_3259_; 
v___x_3255_ = l_Lean_trace_profiler_threshold;
v___x_3256_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3169_, v___x_3255_);
v___x_3257_ = lean_float_of_nat(v___x_3256_);
v___x_3258_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3259_ = lean_float_div(v___x_3257_, v___x_3258_);
v___y_3248_ = v___x_3259_;
goto v___jp_3247_;
}
else
{
lean_object* v___x_3260_; lean_object* v___x_3261_; double v___x_3262_; 
v___x_3260_ = l_Lean_trace_profiler_threshold;
v___x_3261_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3169_, v___x_3260_);
v___x_3262_ = lean_float_of_nat(v___x_3261_);
v___y_3248_ = v___x_3262_;
goto v___jp_3247_;
}
}
v___jp_3181_:
{
lean_object* v___x_3185_; 
lean_inc(v___y_3183_);
v___x_3185_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3171_, v_data_3184_, v___y_3183_, v___y_3182_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v___x_3186_; 
lean_dec_ref_known(v___x_3185_, 1);
v___x_3186_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3179_);
return v___x_3186_;
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3194_; 
lean_dec(v_fst_3179_);
v_a_3187_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3194_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3194_ == 0)
{
v___x_3189_ = v___x_3185_;
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3185_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3194_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3192_; 
if (v_isShared_3190_ == 0)
{
v___x_3192_ = v___x_3189_;
goto v_reusejp_3191_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v_a_3187_);
v___x_3192_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3191_;
}
v_reusejp_3191_:
{
return v___x_3192_;
}
}
}
}
v___jp_3199_:
{
uint8_t v_result_3202_; lean_object* v___x_3203_; lean_object* v___x_3204_; double v___x_3205_; lean_object* v_data_3206_; 
v_result_3202_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3179_);
v___x_3203_ = lean_box(v_result_3202_);
v___x_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3204_, 0, v___x_3203_);
v___x_3205_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3168_);
lean_inc_ref(v___x_3204_);
lean_inc(v_cls_3166_);
v_data_3206_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3206_, 0, v_cls_3166_);
lean_ctor_set(v_data_3206_, 1, v___x_3204_);
lean_ctor_set(v_data_3206_, 2, v_tag_3168_);
lean_ctor_set_float(v_data_3206_, sizeof(void*)*3, v___x_3205_);
lean_ctor_set_float(v_data_3206_, sizeof(void*)*3 + 8, v___x_3205_);
lean_ctor_set_uint8(v_data_3206_, sizeof(void*)*3 + 16, v_collapsed_3167_);
if (v___x_3198_ == 0)
{
lean_dec_ref_known(v___x_3204_, 1);
lean_dec(v_snd_3196_);
lean_dec(v_fst_3195_);
lean_dec_ref(v_tag_3168_);
lean_dec(v_cls_3166_);
v___y_3182_ = v_a_3201_;
v___y_3183_ = v___y_3200_;
v_data_3184_ = v_data_3206_;
goto v___jp_3181_;
}
else
{
lean_object* v_data_3207_; double v___x_3208_; double v___x_3209_; 
lean_dec_ref_known(v_data_3206_, 3);
v_data_3207_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3207_, 0, v_cls_3166_);
lean_ctor_set(v_data_3207_, 1, v___x_3204_);
lean_ctor_set(v_data_3207_, 2, v_tag_3168_);
v___x_3208_ = lean_unbox_float(v_fst_3195_);
lean_dec(v_fst_3195_);
lean_ctor_set_float(v_data_3207_, sizeof(void*)*3, v___x_3208_);
v___x_3209_ = lean_unbox_float(v_snd_3196_);
lean_dec(v_snd_3196_);
lean_ctor_set_float(v_data_3207_, sizeof(void*)*3 + 8, v___x_3209_);
lean_ctor_set_uint8(v_data_3207_, sizeof(void*)*3 + 16, v_collapsed_3167_);
v___y_3182_ = v_a_3201_;
v___y_3183_ = v___y_3200_;
v_data_3184_ = v_data_3207_;
goto v___jp_3181_;
}
}
v___jp_3210_:
{
lean_object* v_ref_3211_; lean_object* v___x_3212_; 
v_ref_3211_ = lean_ctor_get(v___y_3176_, 2);
lean_inc(v___y_3177_);
lean_inc_ref(v___y_3176_);
lean_inc(v___y_3175_);
lean_inc_ref(v___y_3174_);
lean_inc(v_fst_3179_);
v___x_3212_ = lean_apply_6(v_msg_3172_, v_fst_3179_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, lean_box(0));
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v_a_3213_; 
v_a_3213_ = lean_ctor_get(v___x_3212_, 0);
lean_inc(v_a_3213_);
lean_dec_ref_known(v___x_3212_, 1);
v___y_3200_ = v_ref_3211_;
v_a_3201_ = v_a_3213_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3214_; 
lean_dec_ref_known(v___x_3212_, 1);
v___x_3214_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3200_ = v_ref_3211_;
v_a_3201_ = v___x_3214_;
goto v___jp_3199_;
}
}
v___jp_3215_:
{
if (v_clsEnabled_3170_ == 0)
{
if (v___y_3216_ == 0)
{
lean_object* v___x_3217_; lean_object* v_traceState_3218_; lean_object* v_env_3219_; lean_object* v_nextMacroScope_3220_; lean_object* v_ngen_3221_; lean_object* v_auxDeclNGen_3222_; lean_object* v_cache_3223_; lean_object* v_recordedDeps_3224_; lean_object* v_messages_3225_; lean_object* v_infoState_3226_; lean_object* v_snapshotTasks_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3246_; 
lean_dec(v_snd_3196_);
lean_dec(v_fst_3195_);
lean_dec_ref(v_msg_3172_);
lean_dec_ref(v_tag_3168_);
lean_dec(v_cls_3166_);
v___x_3217_ = lean_st_ref_take(v___y_3177_);
v_traceState_3218_ = lean_ctor_get(v___x_3217_, 4);
v_env_3219_ = lean_ctor_get(v___x_3217_, 0);
v_nextMacroScope_3220_ = lean_ctor_get(v___x_3217_, 1);
v_ngen_3221_ = lean_ctor_get(v___x_3217_, 2);
v_auxDeclNGen_3222_ = lean_ctor_get(v___x_3217_, 3);
v_cache_3223_ = lean_ctor_get(v___x_3217_, 5);
v_recordedDeps_3224_ = lean_ctor_get(v___x_3217_, 6);
v_messages_3225_ = lean_ctor_get(v___x_3217_, 7);
v_infoState_3226_ = lean_ctor_get(v___x_3217_, 8);
v_snapshotTasks_3227_ = lean_ctor_get(v___x_3217_, 9);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3229_ = v___x_3217_;
v_isShared_3230_ = v_isSharedCheck_3246_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_snapshotTasks_3227_);
lean_inc(v_infoState_3226_);
lean_inc(v_messages_3225_);
lean_inc(v_recordedDeps_3224_);
lean_inc(v_cache_3223_);
lean_inc(v_traceState_3218_);
lean_inc(v_auxDeclNGen_3222_);
lean_inc(v_ngen_3221_);
lean_inc(v_nextMacroScope_3220_);
lean_inc(v_env_3219_);
lean_dec(v___x_3217_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3246_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
uint64_t v_tid_3231_; lean_object* v_traces_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3245_; 
v_tid_3231_ = lean_ctor_get_uint64(v_traceState_3218_, sizeof(void*)*1);
v_traces_3232_ = lean_ctor_get(v_traceState_3218_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v_traceState_3218_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3234_ = v_traceState_3218_;
v_isShared_3235_ = v_isSharedCheck_3245_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_traces_3232_);
lean_dec(v_traceState_3218_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3245_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3236_; lean_object* v___x_3238_; 
v___x_3236_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3171_, v_traces_3232_);
lean_dec_ref(v_traces_3232_);
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 0, v___x_3236_);
v___x_3238_ = v___x_3234_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v___x_3236_);
lean_ctor_set_uint64(v_reuseFailAlloc_3244_, sizeof(void*)*1, v_tid_3231_);
v___x_3238_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3240_; 
if (v_isShared_3230_ == 0)
{
lean_ctor_set(v___x_3229_, 4, v___x_3238_);
v___x_3240_ = v___x_3229_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3243_; 
v_reuseFailAlloc_3243_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3243_, 0, v_env_3219_);
lean_ctor_set(v_reuseFailAlloc_3243_, 1, v_nextMacroScope_3220_);
lean_ctor_set(v_reuseFailAlloc_3243_, 2, v_ngen_3221_);
lean_ctor_set(v_reuseFailAlloc_3243_, 3, v_auxDeclNGen_3222_);
lean_ctor_set(v_reuseFailAlloc_3243_, 4, v___x_3238_);
lean_ctor_set(v_reuseFailAlloc_3243_, 5, v_cache_3223_);
lean_ctor_set(v_reuseFailAlloc_3243_, 6, v_recordedDeps_3224_);
lean_ctor_set(v_reuseFailAlloc_3243_, 7, v_messages_3225_);
lean_ctor_set(v_reuseFailAlloc_3243_, 8, v_infoState_3226_);
lean_ctor_set(v_reuseFailAlloc_3243_, 9, v_snapshotTasks_3227_);
v___x_3240_ = v_reuseFailAlloc_3243_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_st_ref_put(v___y_3177_, v___x_3240_);
v___x_3242_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3179_);
return v___x_3242_;
}
}
}
}
}
else
{
goto v___jp_3210_;
}
}
else
{
goto v___jp_3210_;
}
}
v___jp_3247_:
{
double v___x_3249_; double v___x_3250_; double v___x_3251_; uint8_t v___x_3252_; 
v___x_3249_ = lean_unbox_float(v_snd_3196_);
v___x_3250_ = lean_unbox_float(v_fst_3195_);
v___x_3251_ = lean_float_sub(v___x_3249_, v___x_3250_);
v___x_3252_ = lean_float_decLt(v___y_3248_, v___x_3251_);
v___y_3216_ = v___x_3252_;
goto v___jp_3215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3263_, lean_object* v_collapsed_3264_, lean_object* v_tag_3265_, lean_object* v_opts_3266_, lean_object* v_clsEnabled_3267_, lean_object* v_oldTraces_3268_, lean_object* v_msg_3269_, lean_object* v_resStartStop_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
uint8_t v_collapsed_boxed_3276_; uint8_t v_clsEnabled_boxed_3277_; lean_object* v_res_3278_; 
v_collapsed_boxed_3276_ = lean_unbox(v_collapsed_3264_);
v_clsEnabled_boxed_3277_ = lean_unbox(v_clsEnabled_3267_);
v_res_3278_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3263_, v_collapsed_boxed_3276_, v_tag_3265_, v_opts_3266_, v_clsEnabled_boxed_3277_, v_oldTraces_3268_, v_msg_3269_, v_resStartStop_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec_ref(v_opts_3266_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3279_, lean_object* v_a_3280_){
_start:
{
if (lean_obj_tag(v_a_3279_) == 0)
{
lean_object* v___x_3281_; 
v___x_3281_ = l_List_reverse___redArg(v_a_3280_);
return v___x_3281_;
}
else
{
lean_object* v_head_3282_; lean_object* v_tail_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3292_; 
v_head_3282_ = lean_ctor_get(v_a_3279_, 0);
v_tail_3283_ = lean_ctor_get(v_a_3279_, 1);
v_isSharedCheck_3292_ = !lean_is_exclusive(v_a_3279_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3285_ = v_a_3279_;
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_tail_3283_);
lean_inc(v_head_3282_);
lean_dec(v_a_3279_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3292_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3287_; lean_object* v___x_3289_; 
v___x_3287_ = l_Lean_MessageData_ofExpr(v_head_3282_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v_a_3280_);
lean_ctor_set(v___x_3285_, 0, v___x_3287_);
v___x_3289_ = v___x_3285_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v___x_3287_);
lean_ctor_set(v_reuseFailAlloc_3291_, 1, v_a_3280_);
v___x_3289_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
v_a_3279_ = v_tail_3283_;
v_a_3280_ = v___x_3289_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3293_, lean_object* v_xs_3294_, lean_object* v_x_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; 
v___x_3301_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3302_ = l_Lean_MessageData_ofName(v_f_3293_);
v___x_3303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3301_);
lean_ctor_set(v___x_3303_, 1, v___x_3302_);
v___x_3304_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3303_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_array_to_list(v_xs_3294_);
v___x_3307_ = lean_box(0);
v___x_3308_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3306_, v___x_3307_);
v___x_3309_ = l_Lean_MessageData_ofList(v___x_3308_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3305_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3312_, lean_object* v_xs_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3312_, v_xs_3313_, v_x_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec_ref(v_x_3314_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3323_, lean_object* v_msg_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
lean_object* v_ref_3330_; lean_object* v___x_3331_; lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3377_; 
v_ref_3330_ = lean_ctor_get(v___y_3327_, 2);
v___x_3331_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3377_ == 0)
{
v___x_3334_ = v___x_3331_;
v_isShared_3335_ = v_isSharedCheck_3377_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___x_3331_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3377_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
lean_object* v___x_3336_; lean_object* v_traceState_3337_; lean_object* v_env_3338_; lean_object* v_nextMacroScope_3339_; lean_object* v_ngen_3340_; lean_object* v_auxDeclNGen_3341_; lean_object* v_cache_3342_; lean_object* v_recordedDeps_3343_; lean_object* v_messages_3344_; lean_object* v_infoState_3345_; lean_object* v_snapshotTasks_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3376_; 
v___x_3336_ = lean_st_ref_take(v___y_3328_);
v_traceState_3337_ = lean_ctor_get(v___x_3336_, 4);
v_env_3338_ = lean_ctor_get(v___x_3336_, 0);
v_nextMacroScope_3339_ = lean_ctor_get(v___x_3336_, 1);
v_ngen_3340_ = lean_ctor_get(v___x_3336_, 2);
v_auxDeclNGen_3341_ = lean_ctor_get(v___x_3336_, 3);
v_cache_3342_ = lean_ctor_get(v___x_3336_, 5);
v_recordedDeps_3343_ = lean_ctor_get(v___x_3336_, 6);
v_messages_3344_ = lean_ctor_get(v___x_3336_, 7);
v_infoState_3345_ = lean_ctor_get(v___x_3336_, 8);
v_snapshotTasks_3346_ = lean_ctor_get(v___x_3336_, 9);
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3376_ == 0)
{
v___x_3348_ = v___x_3336_;
v_isShared_3349_ = v_isSharedCheck_3376_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_snapshotTasks_3346_);
lean_inc(v_infoState_3345_);
lean_inc(v_messages_3344_);
lean_inc(v_recordedDeps_3343_);
lean_inc(v_cache_3342_);
lean_inc(v_traceState_3337_);
lean_inc(v_auxDeclNGen_3341_);
lean_inc(v_ngen_3340_);
lean_inc(v_nextMacroScope_3339_);
lean_inc(v_env_3338_);
lean_dec(v___x_3336_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3376_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
uint64_t v_tid_3350_; lean_object* v_traces_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3375_; 
v_tid_3350_ = lean_ctor_get_uint64(v_traceState_3337_, sizeof(void*)*1);
v_traces_3351_ = lean_ctor_get(v_traceState_3337_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v_traceState_3337_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3353_ = v_traceState_3337_;
v_isShared_3354_ = v_isSharedCheck_3375_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_traces_3351_);
lean_dec(v_traceState_3337_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3375_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v___x_3356_; double v___x_3357_; uint8_t v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3366_; 
v___x_3355_ = lean_box(0);
v___x_3356_ = lean_box(0);
v___x_3357_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3358_ = 0;
v___x_3359_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3360_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3360_, 0, v_cls_3323_);
lean_ctor_set(v___x_3360_, 1, v___x_3356_);
lean_ctor_set(v___x_3360_, 2, v___x_3359_);
lean_ctor_set_float(v___x_3360_, sizeof(void*)*3, v___x_3357_);
lean_ctor_set_float(v___x_3360_, sizeof(void*)*3 + 8, v___x_3357_);
lean_ctor_set_uint8(v___x_3360_, sizeof(void*)*3 + 16, v___x_3358_);
v___x_3361_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3362_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3360_);
lean_ctor_set(v___x_3362_, 1, v_a_3332_);
lean_ctor_set(v___x_3362_, 2, v___x_3361_);
lean_inc(v_ref_3330_);
v___x_3363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3363_, 0, v_ref_3330_);
lean_ctor_set(v___x_3363_, 1, v___x_3362_);
v___x_3364_ = l_Lean_PersistentArray_push___redArg(v_traces_3351_, v___x_3363_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3364_);
v___x_3366_ = v___x_3353_;
goto v_reusejp_3365_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3364_);
lean_ctor_set_uint64(v_reuseFailAlloc_3374_, sizeof(void*)*1, v_tid_3350_);
v___x_3366_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3365_;
}
v_reusejp_3365_:
{
lean_object* v___x_3368_; 
if (v_isShared_3349_ == 0)
{
lean_ctor_set(v___x_3348_, 4, v___x_3366_);
v___x_3368_ = v___x_3348_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3373_; 
v_reuseFailAlloc_3373_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_env_3338_);
lean_ctor_set(v_reuseFailAlloc_3373_, 1, v_nextMacroScope_3339_);
lean_ctor_set(v_reuseFailAlloc_3373_, 2, v_ngen_3340_);
lean_ctor_set(v_reuseFailAlloc_3373_, 3, v_auxDeclNGen_3341_);
lean_ctor_set(v_reuseFailAlloc_3373_, 4, v___x_3366_);
lean_ctor_set(v_reuseFailAlloc_3373_, 5, v_cache_3342_);
lean_ctor_set(v_reuseFailAlloc_3373_, 6, v_recordedDeps_3343_);
lean_ctor_set(v_reuseFailAlloc_3373_, 7, v_messages_3344_);
lean_ctor_set(v_reuseFailAlloc_3373_, 8, v_infoState_3345_);
lean_ctor_set(v_reuseFailAlloc_3373_, 9, v_snapshotTasks_3346_);
v___x_3368_ = v_reuseFailAlloc_3373_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3369_ = lean_st_ref_put(v___y_3328_, v___x_3368_);
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 0, v___x_3355_);
v___x_3371_ = v___x_3334_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3355_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3378_, lean_object* v_msg_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3378_, v_msg_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3386_, lean_object* v_xs_3387_, lean_object* v_k_3388_, lean_object* v_a_3389_, lean_object* v_a_3390_, lean_object* v_a_3391_, lean_object* v_a_3392_){
_start:
{
lean_object* v_toCold_3394_; lean_object* v_options_3395_; uint8_t v_hasTrace_3396_; 
v_toCold_3394_ = lean_ctor_get(v_a_3391_, 0);
v_options_3395_ = lean_ctor_get(v_toCold_3394_, 2);
v_hasTrace_3396_ = lean_ctor_get_uint8(v_options_3395_, sizeof(void*)*1);
if (v_hasTrace_3396_ == 0)
{
lean_object* v___x_3397_; 
lean_dec_ref(v_xs_3387_);
lean_dec(v_f_3386_);
lean_inc(v_a_3392_);
lean_inc_ref(v_a_3391_);
lean_inc(v_a_3390_);
lean_inc_ref(v_a_3389_);
v___x_3397_ = lean_apply_5(v_k_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, lean_box(0));
return v___x_3397_;
}
else
{
lean_object* v_inheritedTraceOptions_3398_; lean_object* v___f_3399_; lean_object* v___y_3401_; lean_object* v_a_3402_; lean_object* v___x_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; lean_object* v___y_3432_; lean_object* v___y_3433_; lean_object* v_a_3434_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v_a_3449_; lean_object* v___y_3452_; lean_object* v___y_3453_; lean_object* v_a_3454_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v_a_3459_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v_a_3471_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v_a_3483_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v_a_3488_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v_a_3493_; 
v_inheritedTraceOptions_3398_ = lean_ctor_get(v_toCold_3394_, 11);
v___f_3399_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3399_, 0, v_f_3386_);
lean_closure_set(v___f_3399_, 1, v_xs_3387_);
v___x_3427_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3429_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3430_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3395_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3527_; uint8_t v___x_3528_; 
v___x_3527_ = l_Lean_trace_profiler;
v___x_3528_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3395_, v___x_3527_);
if (v___x_3528_ == 0)
{
lean_object* v___x_3529_; 
lean_dec_ref(v___f_3399_);
lean_inc(v_a_3392_);
lean_inc_ref(v_a_3391_);
lean_inc(v_a_3390_);
lean_inc_ref(v_a_3389_);
v___x_3529_ = lean_apply_5(v_k_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, lean_box(0));
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3532_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3533_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3395_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_dec(v_a_3530_);
return v___x_3529_;
}
else
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_dec_ref_known(v___x_3529_, 1);
lean_inc(v_a_3530_);
v___x_3534_ = l_Lean_MessageData_ofExpr(v_a_3530_);
v___x_3535_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3531_, v___x_3534_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3542_ == 0)
{
lean_object* v_unused_3543_; 
v_unused_3543_ = lean_ctor_get(v___x_3535_, 0);
lean_dec(v_unused_3543_);
v___x_3537_ = v___x_3535_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_dec(v___x_3535_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_a_3530_);
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3530_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec(v_a_3530_);
v_a_3544_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3535_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3535_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
lean_inc(v_a_3544_);
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
v___y_3401_ = v___x_3549_;
v_a_3402_ = v_a_3544_;
goto v___jp_3400_;
}
}
}
}
}
else
{
lean_object* v_a_3552_; 
v_a_3552_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3552_);
v___y_3401_ = v___x_3529_;
v_a_3402_ = v_a_3552_;
goto v___jp_3400_;
}
}
else
{
goto v___jp_3502_;
}
}
else
{
goto v___jp_3502_;
}
v___jp_3400_:
{
uint8_t v___x_3403_; 
v___x_3403_ = l_Lean_Exception_isInterrupt(v_a_3402_);
if (v___x_3403_ == 0)
{
uint8_t v___x_3404_; 
lean_inc_ref(v_a_3402_);
v___x_3404_ = l_Lean_Exception_isRuntime(v_a_3402_);
if (v___x_3404_ == 0)
{
lean_object* v___x_3405_; lean_object* v___x_3406_; uint8_t v___x_3407_; 
lean_dec_ref(v___y_3401_);
v___x_3405_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3406_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3407_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3395_, v___x_3406_);
if (v___x_3407_ == 0)
{
lean_object* v___x_3408_; 
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v_a_3402_);
return v___x_3408_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; 
lean_inc_ref(v_a_3402_);
v___x_3409_ = l_Lean_Exception_toMessageData(v_a_3402_);
v___x_3410_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3405_, v___x_3409_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3410_) == 0)
{
lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3410_, 0);
lean_dec(v_unused_3418_);
v___x_3412_ = v___x_3410_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_dec(v___x_3410_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set_tag(v___x_3412_, 1);
lean_ctor_set(v___x_3412_, 0, v_a_3402_);
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3402_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_dec_ref(v_a_3402_);
v_a_3419_ = lean_ctor_get(v___x_3410_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3410_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3410_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3402_);
return v___y_3401_;
}
}
else
{
lean_dec_ref(v_a_3402_);
return v___y_3401_;
}
}
v___jp_3431_:
{
lean_object* v___x_3435_; double v___x_3436_; double v___x_3437_; double v___x_3438_; double v___x_3439_; double v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3435_ = lean_io_mono_nanos_now();
v___x_3436_ = lean_float_of_nat(v___y_3432_);
v___x_3437_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3438_ = lean_float_div(v___x_3436_, v___x_3437_);
v___x_3439_ = lean_float_of_nat(v___x_3435_);
v___x_3440_ = lean_float_div(v___x_3439_, v___x_3437_);
v___x_3441_ = lean_box_float(v___x_3438_);
v___x_3442_ = lean_box_float(v___x_3440_);
v___x_3443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
v___x_3444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3444_, 0, v_a_3434_);
lean_ctor_set(v___x_3444_, 1, v___x_3443_);
v___x_3445_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3427_, v_hasTrace_3396_, v___x_3428_, v_options_3395_, v___x_3430_, v___y_3433_, v___f_3399_, v___x_3444_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
return v___x_3445_;
}
v___jp_3446_:
{
lean_object* v___x_3450_; 
v___x_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3450_, 0, v_a_3449_);
v___y_3432_ = v___y_3447_;
v___y_3433_ = v___y_3448_;
v_a_3434_ = v___x_3450_;
goto v___jp_3431_;
}
v___jp_3451_:
{
lean_object* v___x_3455_; 
v___x_3455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3455_, 0, v_a_3454_);
v___y_3432_ = v___y_3452_;
v___y_3433_ = v___y_3453_;
v_a_3434_ = v___x_3455_;
goto v___jp_3431_;
}
v___jp_3456_:
{
uint8_t v___x_3460_; 
v___x_3460_ = l_Lean_Exception_isInterrupt(v_a_3459_);
if (v___x_3460_ == 0)
{
uint8_t v___x_3461_; 
lean_inc_ref(v_a_3459_);
v___x_3461_ = l_Lean_Exception_isRuntime(v_a_3459_);
if (v___x_3461_ == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; uint8_t v___x_3464_; 
v___x_3462_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3463_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3464_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3395_, v___x_3463_);
if (v___x_3464_ == 0)
{
v___y_3452_ = v___y_3457_;
v___y_3453_ = v___y_3458_;
v_a_3454_ = v_a_3459_;
goto v___jp_3451_;
}
else
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
lean_inc_ref(v_a_3459_);
v___x_3465_ = l_Lean_Exception_toMessageData(v_a_3459_);
v___x_3466_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3462_, v___x_3465_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3466_) == 0)
{
lean_dec_ref_known(v___x_3466_, 1);
v___y_3452_ = v___y_3457_;
v___y_3453_ = v___y_3458_;
v_a_3454_ = v_a_3459_;
goto v___jp_3451_;
}
else
{
lean_object* v_a_3467_; 
lean_dec_ref(v_a_3459_);
v_a_3467_ = lean_ctor_get(v___x_3466_, 0);
lean_inc(v_a_3467_);
lean_dec_ref_known(v___x_3466_, 1);
v___y_3452_ = v___y_3457_;
v___y_3453_ = v___y_3458_;
v_a_3454_ = v_a_3467_;
goto v___jp_3451_;
}
}
}
else
{
v___y_3452_ = v___y_3457_;
v___y_3453_ = v___y_3458_;
v_a_3454_ = v_a_3459_;
goto v___jp_3451_;
}
}
else
{
v___y_3452_ = v___y_3457_;
v___y_3453_ = v___y_3458_;
v_a_3454_ = v_a_3459_;
goto v___jp_3451_;
}
}
v___jp_3468_:
{
lean_object* v___x_3472_; double v___x_3473_; double v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3472_ = lean_io_get_num_heartbeats();
v___x_3473_ = lean_float_of_nat(v___y_3470_);
v___x_3474_ = lean_float_of_nat(v___x_3472_);
v___x_3475_ = lean_box_float(v___x_3473_);
v___x_3476_ = lean_box_float(v___x_3474_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_a_3471_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3427_, v_hasTrace_3396_, v___x_3428_, v_options_3395_, v___x_3430_, v___y_3469_, v___f_3399_, v___x_3478_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
return v___x_3479_;
}
v___jp_3480_:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_a_3483_);
v___y_3469_ = v___y_3481_;
v___y_3470_ = v___y_3482_;
v_a_3471_ = v___x_3484_;
goto v___jp_3468_;
}
v___jp_3485_:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v_a_3488_);
v___y_3469_ = v___y_3486_;
v___y_3470_ = v___y_3487_;
v_a_3471_ = v___x_3489_;
goto v___jp_3468_;
}
v___jp_3490_:
{
uint8_t v___x_3494_; 
v___x_3494_ = l_Lean_Exception_isInterrupt(v_a_3493_);
if (v___x_3494_ == 0)
{
uint8_t v___x_3495_; 
lean_inc_ref(v_a_3493_);
v___x_3495_ = l_Lean_Exception_isRuntime(v_a_3493_);
if (v___x_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3496_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3497_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3395_, v___x_3497_);
if (v___x_3498_ == 0)
{
v___y_3486_ = v___y_3491_;
v___y_3487_ = v___y_3492_;
v_a_3488_ = v_a_3493_;
goto v___jp_3485_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_inc_ref(v_a_3493_);
v___x_3499_ = l_Lean_Exception_toMessageData(v_a_3493_);
v___x_3500_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3496_, v___x_3499_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec_ref_known(v___x_3500_, 1);
v___y_3486_ = v___y_3491_;
v___y_3487_ = v___y_3492_;
v_a_3488_ = v_a_3493_;
goto v___jp_3485_;
}
else
{
lean_object* v_a_3501_; 
lean_dec_ref(v_a_3493_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___y_3486_ = v___y_3491_;
v___y_3487_ = v___y_3492_;
v_a_3488_ = v_a_3501_;
goto v___jp_3485_;
}
}
}
else
{
v___y_3486_ = v___y_3491_;
v___y_3487_ = v___y_3492_;
v_a_3488_ = v_a_3493_;
goto v___jp_3485_;
}
}
else
{
v___y_3486_ = v___y_3491_;
v___y_3487_ = v___y_3492_;
v_a_3488_ = v_a_3493_;
goto v___jp_3485_;
}
}
v___jp_3502_:
{
lean_object* v___x_3503_; lean_object* v_a_3504_; lean_object* v___x_3505_; uint8_t v___x_3506_; 
v___x_3503_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3392_);
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref(v___x_3503_);
v___x_3505_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3506_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3395_, v___x_3505_);
if (v___x_3506_ == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; 
v___x_3507_ = lean_io_mono_nanos_now();
lean_inc(v_a_3392_);
lean_inc_ref(v_a_3391_);
lean_inc(v_a_3390_);
lean_inc_ref(v_a_3389_);
v___x_3508_ = lean_apply_5(v_k_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, lean_box(0));
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v___x_3510_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3511_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3395_, v___x_3511_);
if (v___x_3512_ == 0)
{
v___y_3447_ = v___x_3507_;
v___y_3448_ = v_a_3504_;
v_a_3449_ = v_a_3509_;
goto v___jp_3446_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_inc(v_a_3509_);
v___x_3513_ = l_Lean_MessageData_ofExpr(v_a_3509_);
v___x_3514_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3510_, v___x_3513_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_dec_ref_known(v___x_3514_, 1);
v___y_3447_ = v___x_3507_;
v___y_3448_ = v_a_3504_;
v_a_3449_ = v_a_3509_;
goto v___jp_3446_;
}
else
{
lean_object* v_a_3515_; 
lean_dec(v_a_3509_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___y_3457_ = v___x_3507_;
v___y_3458_ = v_a_3504_;
v_a_3459_ = v_a_3515_;
goto v___jp_3456_;
}
}
}
else
{
lean_object* v_a_3516_; 
v_a_3516_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3516_);
lean_dec_ref_known(v___x_3508_, 1);
v___y_3457_ = v___x_3507_;
v___y_3458_ = v_a_3504_;
v_a_3459_ = v_a_3516_;
goto v___jp_3456_;
}
}
else
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3392_);
lean_inc_ref(v_a_3391_);
lean_inc(v_a_3390_);
lean_inc_ref(v_a_3389_);
v___x_3518_ = lean_apply_5(v_k_3388_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_, lean_box(0));
if (lean_obj_tag(v___x_3518_) == 0)
{
lean_object* v_a_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3519_);
lean_dec_ref_known(v___x_3518_, 1);
v___x_3520_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3521_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3522_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3398_, v_options_3395_, v___x_3521_);
if (v___x_3522_ == 0)
{
v___y_3481_ = v_a_3504_;
v___y_3482_ = v___x_3517_;
v_a_3483_ = v_a_3519_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3523_; lean_object* v___x_3524_; 
lean_inc(v_a_3519_);
v___x_3523_ = l_Lean_MessageData_ofExpr(v_a_3519_);
v___x_3524_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3520_, v___x_3523_, v_a_3389_, v_a_3390_, v_a_3391_, v_a_3392_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_dec_ref_known(v___x_3524_, 1);
v___y_3481_ = v_a_3504_;
v___y_3482_ = v___x_3517_;
v_a_3483_ = v_a_3519_;
goto v___jp_3480_;
}
else
{
lean_object* v_a_3525_; 
lean_dec(v_a_3519_);
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
v___y_3491_ = v_a_3504_;
v___y_3492_ = v___x_3517_;
v_a_3493_ = v_a_3525_;
goto v___jp_3490_;
}
}
}
else
{
lean_object* v_a_3526_; 
v_a_3526_ = lean_ctor_get(v___x_3518_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v___x_3518_, 1);
v___y_3491_ = v_a_3504_;
v___y_3492_ = v___x_3517_;
v_a_3493_ = v_a_3526_;
goto v___jp_3490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3553_, lean_object* v_xs_3554_, lean_object* v_k_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3553_, v_xs_3554_, v_k_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3562_, lean_object* v_xs_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v___f_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_inc_ref(v_xs_3563_);
lean_inc(v_constName_3562_);
v___f_3569_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3569_, 0, v_constName_3562_);
lean_closure_set(v___f_3569_, 1, v_xs_3563_);
v___x_3570_ = 0;
v___x_3571_ = lean_box(v___x_3570_);
v___x_3572_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3572_, 0, lean_box(0));
lean_closure_set(v___x_3572_, 1, v___f_3569_);
lean_closure_set(v___x_3572_, 2, v___x_3571_);
v___x_3573_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3562_, v_xs_3563_, v___x_3572_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3574_, lean_object* v_xs_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_){
_start:
{
lean_object* v_res_3581_; 
v_res_3581_ = l_Lean_Meta_mkAppM(v_constName_3574_, v_xs_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_);
lean_dec(v_a_3579_);
lean_dec_ref(v_a_3578_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
return v_res_3581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_){
_start:
{
lean_object* v___x_3587_; 
v___x_3587_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3585_);
return v___x_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_){
_start:
{
lean_object* v_res_3593_; 
v_res_3593_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec_ref(v___y_3588_);
return v_res_3593_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3594_, lean_object* v_x_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___x_3601_; 
v___x_3601_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3595_);
return v___x_3601_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3602_, lean_object* v_x_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_res_3609_; 
v_res_3609_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3602_, v_x_3603_, v___y_3604_, v___y_3605_, v___y_3606_, v___y_3607_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v___y_3604_);
return v_res_3609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3610_, lean_object* v_xs_3611_, lean_object* v_x_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_){
_start:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; 
v___x_3618_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3619_ = l_Lean_MessageData_ofExpr(v_f_3610_);
v___x_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3618_);
lean_ctor_set(v___x_3620_, 1, v___x_3619_);
v___x_3621_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3620_);
lean_ctor_set(v___x_3622_, 1, v___x_3621_);
v___x_3623_ = lean_array_to_list(v_xs_3611_);
v___x_3624_ = lean_box(0);
v___x_3625_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3623_, v___x_3624_);
v___x_3626_ = l_Lean_MessageData_ofList(v___x_3625_);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3622_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3628_, 0, v___x_3627_);
return v___x_3628_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3629_, lean_object* v_xs_3630_, lean_object* v_x_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
lean_object* v_res_3637_; 
v_res_3637_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3629_, v_xs_3630_, v_x_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_x_3631_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3638_, lean_object* v_xs_3639_, lean_object* v_k_3640_, lean_object* v_a_3641_, lean_object* v_a_3642_, lean_object* v_a_3643_, lean_object* v_a_3644_){
_start:
{
lean_object* v_toCold_3646_; lean_object* v_options_3647_; uint8_t v_hasTrace_3648_; 
v_toCold_3646_ = lean_ctor_get(v_a_3643_, 0);
v_options_3647_ = lean_ctor_get(v_toCold_3646_, 2);
v_hasTrace_3648_ = lean_ctor_get_uint8(v_options_3647_, sizeof(void*)*1);
if (v_hasTrace_3648_ == 0)
{
lean_object* v___x_3649_; 
lean_dec_ref(v_xs_3639_);
lean_dec_ref(v_f_3638_);
lean_inc(v_a_3644_);
lean_inc_ref(v_a_3643_);
lean_inc(v_a_3642_);
lean_inc_ref(v_a_3641_);
v___x_3649_ = lean_apply_5(v_k_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, lean_box(0));
return v___x_3649_;
}
else
{
lean_object* v_inheritedTraceOptions_3650_; lean_object* v___f_3651_; lean_object* v___y_3653_; lean_object* v_a_3654_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; lean_object* v___y_3684_; lean_object* v___y_3685_; lean_object* v_a_3686_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_a_3701_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v_a_3706_; lean_object* v___y_3709_; lean_object* v___y_3710_; lean_object* v_a_3711_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v_a_3723_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v_a_3735_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v_a_3740_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v_a_3745_; 
v_inheritedTraceOptions_3650_ = lean_ctor_get(v_toCold_3646_, 11);
v___f_3651_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3651_, 0, v_f_3638_);
lean_closure_set(v___f_3651_, 1, v_xs_3639_);
v___x_3679_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3680_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3681_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3650_, v_options_3647_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3779_; uint8_t v___x_3780_; 
v___x_3779_ = l_Lean_trace_profiler;
v___x_3780_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3647_, v___x_3779_);
if (v___x_3780_ == 0)
{
lean_object* v___x_3781_; 
lean_dec_ref(v___f_3651_);
lean_inc(v_a_3644_);
lean_inc_ref(v_a_3643_);
lean_inc(v_a_3642_);
lean_inc_ref(v_a_3641_);
v___x_3781_ = lean_apply_5(v_k_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, lean_box(0));
if (lean_obj_tag(v___x_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; uint8_t v___x_3785_; 
v_a_3782_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3782_);
v___x_3783_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3784_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3785_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3650_, v_options_3647_, v___x_3784_);
if (v___x_3785_ == 0)
{
lean_dec(v_a_3782_);
return v___x_3781_;
}
else
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
lean_dec_ref_known(v___x_3781_, 1);
lean_inc(v_a_3782_);
v___x_3786_ = l_Lean_MessageData_ofExpr(v_a_3782_);
v___x_3787_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3783_, v___x_3786_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; 
v_unused_3795_ = lean_ctor_get(v___x_3787_, 0);
lean_dec(v_unused_3795_);
v___x_3789_ = v___x_3787_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_dec(v___x_3787_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v_a_3782_);
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3782_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_dec(v_a_3782_);
v_a_3796_ = lean_ctor_get(v___x_3787_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3787_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3787_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3787_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
lean_inc(v_a_3796_);
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
v___y_3653_ = v___x_3801_;
v_a_3654_ = v_a_3796_;
goto v___jp_3652_;
}
}
}
}
}
else
{
lean_object* v_a_3804_; 
v_a_3804_ = lean_ctor_get(v___x_3781_, 0);
lean_inc(v_a_3804_);
v___y_3653_ = v___x_3781_;
v_a_3654_ = v_a_3804_;
goto v___jp_3652_;
}
}
else
{
goto v___jp_3754_;
}
}
else
{
goto v___jp_3754_;
}
v___jp_3652_:
{
uint8_t v___x_3655_; 
v___x_3655_ = l_Lean_Exception_isInterrupt(v_a_3654_);
if (v___x_3655_ == 0)
{
uint8_t v___x_3656_; 
lean_inc_ref(v_a_3654_);
v___x_3656_ = l_Lean_Exception_isRuntime(v_a_3654_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; lean_object* v___x_3658_; uint8_t v___x_3659_; 
lean_dec_ref(v___y_3653_);
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3658_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3659_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3650_, v_options_3647_, v___x_3658_);
if (v___x_3659_ == 0)
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3660_, 0, v_a_3654_);
return v___x_3660_;
}
else
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
lean_inc_ref(v_a_3654_);
v___x_3661_ = l_Lean_Exception_toMessageData(v_a_3654_);
v___x_3662_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3657_, v___x_3661_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3669_ == 0)
{
lean_object* v_unused_3670_; 
v_unused_3670_ = lean_ctor_get(v___x_3662_, 0);
lean_dec(v_unused_3670_);
v___x_3664_ = v___x_3662_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v___x_3662_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
lean_ctor_set_tag(v___x_3664_, 1);
lean_ctor_set(v___x_3664_, 0, v_a_3654_);
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3654_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_dec_ref(v_a_3654_);
v_a_3671_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3662_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3662_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_3654_);
return v___y_3653_;
}
}
else
{
lean_dec_ref(v_a_3654_);
return v___y_3653_;
}
}
v___jp_3683_:
{
lean_object* v___x_3687_; double v___x_3688_; double v___x_3689_; double v___x_3690_; double v___x_3691_; double v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; lean_object* v___x_3697_; 
v___x_3687_ = lean_io_mono_nanos_now();
v___x_3688_ = lean_float_of_nat(v___y_3685_);
v___x_3689_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3690_ = lean_float_div(v___x_3688_, v___x_3689_);
v___x_3691_ = lean_float_of_nat(v___x_3687_);
v___x_3692_ = lean_float_div(v___x_3691_, v___x_3689_);
v___x_3693_ = lean_box_float(v___x_3690_);
v___x_3694_ = lean_box_float(v___x_3692_);
v___x_3695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3695_, 0, v___x_3693_);
lean_ctor_set(v___x_3695_, 1, v___x_3694_);
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v_a_3686_);
lean_ctor_set(v___x_3696_, 1, v___x_3695_);
v___x_3697_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3679_, v_hasTrace_3648_, v___x_3680_, v_options_3647_, v___x_3682_, v___y_3684_, v___f_3651_, v___x_3696_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
return v___x_3697_;
}
v___jp_3698_:
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v_a_3701_);
v___y_3684_ = v___y_3699_;
v___y_3685_ = v___y_3700_;
v_a_3686_ = v___x_3702_;
goto v___jp_3683_;
}
v___jp_3703_:
{
lean_object* v___x_3707_; 
v___x_3707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3707_, 0, v_a_3706_);
v___y_3684_ = v___y_3704_;
v___y_3685_ = v___y_3705_;
v_a_3686_ = v___x_3707_;
goto v___jp_3683_;
}
v___jp_3708_:
{
uint8_t v___x_3712_; 
v___x_3712_ = l_Lean_Exception_isInterrupt(v_a_3711_);
if (v___x_3712_ == 0)
{
uint8_t v___x_3713_; 
lean_inc_ref(v_a_3711_);
v___x_3713_ = l_Lean_Exception_isRuntime(v_a_3711_);
if (v___x_3713_ == 0)
{
lean_object* v___x_3714_; lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3714_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3715_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3650_, v_options_3647_, v___x_3715_);
if (v___x_3716_ == 0)
{
v___y_3704_ = v___y_3709_;
v___y_3705_ = v___y_3710_;
v_a_3706_ = v_a_3711_;
goto v___jp_3703_;
}
else
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
lean_inc_ref(v_a_3711_);
v___x_3717_ = l_Lean_Exception_toMessageData(v_a_3711_);
v___x_3718_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3714_, v___x_3717_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_dec_ref_known(v___x_3718_, 1);
v___y_3704_ = v___y_3709_;
v___y_3705_ = v___y_3710_;
v_a_3706_ = v_a_3711_;
goto v___jp_3703_;
}
else
{
lean_object* v_a_3719_; 
lean_dec_ref(v_a_3711_);
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v___y_3704_ = v___y_3709_;
v___y_3705_ = v___y_3710_;
v_a_3706_ = v_a_3719_;
goto v___jp_3703_;
}
}
}
else
{
v___y_3704_ = v___y_3709_;
v___y_3705_ = v___y_3710_;
v_a_3706_ = v_a_3711_;
goto v___jp_3703_;
}
}
else
{
v___y_3704_ = v___y_3709_;
v___y_3705_ = v___y_3710_;
v_a_3706_ = v_a_3711_;
goto v___jp_3703_;
}
}
v___jp_3720_:
{
lean_object* v___x_3724_; double v___x_3725_; double v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3724_ = lean_io_get_num_heartbeats();
v___x_3725_ = lean_float_of_nat(v___y_3722_);
v___x_3726_ = lean_float_of_nat(v___x_3724_);
v___x_3727_ = lean_box_float(v___x_3725_);
v___x_3728_ = lean_box_float(v___x_3726_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3727_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_a_3723_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3679_, v_hasTrace_3648_, v___x_3680_, v_options_3647_, v___x_3682_, v___y_3721_, v___f_3651_, v___x_3730_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
return v___x_3731_;
}
v___jp_3732_:
{
lean_object* v___x_3736_; 
v___x_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3736_, 0, v_a_3735_);
v___y_3721_ = v___y_3733_;
v___y_3722_ = v___y_3734_;
v_a_3723_ = v___x_3736_;
goto v___jp_3720_;
}
v___jp_3737_:
{
lean_object* v___x_3741_; 
v___x_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_a_3740_);
v___y_3721_ = v___y_3738_;
v___y_3722_ = v___y_3739_;
v_a_3723_ = v___x_3741_;
goto v___jp_3720_;
}
v___jp_3742_:
{
uint8_t v___x_3746_; 
v___x_3746_ = l_Lean_Exception_isInterrupt(v_a_3745_);
if (v___x_3746_ == 0)
{
uint8_t v___x_3747_; 
lean_inc_ref(v_a_3745_);
v___x_3747_ = l_Lean_Exception_isRuntime(v_a_3745_);
if (v___x_3747_ == 0)
{
lean_object* v___x_3748_; lean_object* v___x_3749_; uint8_t v___x_3750_; 
v___x_3748_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3749_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3750_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3650_, v_options_3647_, v___x_3749_);
if (v___x_3750_ == 0)
{
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3744_;
v_a_3740_ = v_a_3745_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_inc_ref(v_a_3745_);
v___x_3751_ = l_Lean_Exception_toMessageData(v_a_3745_);
v___x_3752_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3748_, v___x_3751_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3752_) == 0)
{
lean_dec_ref_known(v___x_3752_, 1);
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3744_;
v_a_3740_ = v_a_3745_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_3753_; 
lean_dec_ref(v_a_3745_);
v_a_3753_ = lean_ctor_get(v___x_3752_, 0);
lean_inc(v_a_3753_);
lean_dec_ref_known(v___x_3752_, 1);
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3744_;
v_a_3740_ = v_a_3753_;
goto v___jp_3737_;
}
}
}
else
{
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3744_;
v_a_3740_ = v_a_3745_;
goto v___jp_3737_;
}
}
else
{
v___y_3738_ = v___y_3743_;
v___y_3739_ = v___y_3744_;
v_a_3740_ = v_a_3745_;
goto v___jp_3737_;
}
}
v___jp_3754_:
{
lean_object* v___x_3755_; lean_object* v_a_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3755_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3644_);
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref(v___x_3755_);
v___x_3757_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3758_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3647_, v___x_3757_);
if (v___x_3758_ == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = lean_io_mono_nanos_now();
lean_inc(v_a_3644_);
lean_inc_ref(v_a_3643_);
lean_inc(v_a_3642_);
lean_inc_ref(v_a_3641_);
v___x_3760_ = lean_apply_5(v_k_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, lean_box(0));
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_object* v_a_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___x_3762_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3763_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3650_, v_options_3647_, v___x_3763_);
if (v___x_3764_ == 0)
{
v___y_3699_ = v_a_3756_;
v___y_3700_ = v___x_3759_;
v_a_3701_ = v_a_3761_;
goto v___jp_3698_;
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_inc(v_a_3761_);
v___x_3765_ = l_Lean_MessageData_ofExpr(v_a_3761_);
v___x_3766_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3762_, v___x_3765_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_dec_ref_known(v___x_3766_, 1);
v___y_3699_ = v_a_3756_;
v___y_3700_ = v___x_3759_;
v_a_3701_ = v_a_3761_;
goto v___jp_3698_;
}
else
{
lean_object* v_a_3767_; 
lean_dec(v_a_3761_);
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___y_3709_ = v_a_3756_;
v___y_3710_ = v___x_3759_;
v_a_3711_ = v_a_3767_;
goto v___jp_3708_;
}
}
}
else
{
lean_object* v_a_3768_; 
v_a_3768_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3768_);
lean_dec_ref_known(v___x_3760_, 1);
v___y_3709_ = v_a_3756_;
v___y_3710_ = v___x_3759_;
v_a_3711_ = v_a_3768_;
goto v___jp_3708_;
}
}
else
{
lean_object* v___x_3769_; lean_object* v___x_3770_; 
v___x_3769_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3644_);
lean_inc_ref(v_a_3643_);
lean_inc(v_a_3642_);
lean_inc_ref(v_a_3641_);
v___x_3770_ = lean_apply_5(v_k_3640_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_, lean_box(0));
if (lean_obj_tag(v___x_3770_) == 0)
{
lean_object* v_a_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
v_a_3771_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3771_);
lean_dec_ref_known(v___x_3770_, 1);
v___x_3772_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3773_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3650_, v_options_3647_, v___x_3773_);
if (v___x_3774_ == 0)
{
v___y_3733_ = v_a_3756_;
v___y_3734_ = v___x_3769_;
v_a_3735_ = v_a_3771_;
goto v___jp_3732_;
}
else
{
lean_object* v___x_3775_; lean_object* v___x_3776_; 
lean_inc(v_a_3771_);
v___x_3775_ = l_Lean_MessageData_ofExpr(v_a_3771_);
v___x_3776_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3772_, v___x_3775_, v_a_3641_, v_a_3642_, v_a_3643_, v_a_3644_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_dec_ref_known(v___x_3776_, 1);
v___y_3733_ = v_a_3756_;
v___y_3734_ = v___x_3769_;
v_a_3735_ = v_a_3771_;
goto v___jp_3732_;
}
else
{
lean_object* v_a_3777_; 
lean_dec(v_a_3771_);
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
lean_inc(v_a_3777_);
lean_dec_ref_known(v___x_3776_, 1);
v___y_3743_ = v_a_3756_;
v___y_3744_ = v___x_3769_;
v_a_3745_ = v_a_3777_;
goto v___jp_3742_;
}
}
}
else
{
lean_object* v_a_3778_; 
v_a_3778_ = lean_ctor_get(v___x_3770_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3770_, 1);
v___y_3743_ = v_a_3756_;
v___y_3744_ = v___x_3769_;
v_a_3745_ = v_a_3778_;
goto v___jp_3742_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3805_, lean_object* v_xs_3806_, lean_object* v_k_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_){
_start:
{
lean_object* v_res_3813_; 
v_res_3813_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3805_, v_xs_3806_, v_k_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
lean_dec(v_a_3811_);
lean_dec_ref(v_a_3810_);
lean_dec(v_a_3809_);
lean_dec_ref(v_a_3808_);
return v_res_3813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3814_, lean_object* v_xs_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___x_3821_; 
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
lean_inc(v_a_3817_);
lean_inc_ref(v_a_3816_);
lean_inc_ref(v_f_3814_);
v___x_3821_ = lean_infer_type(v_f_3814_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3823_; uint8_t v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
lean_inc_ref(v_xs_3815_);
lean_inc_ref(v_f_3814_);
v___x_3823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3823_, 0, v_f_3814_);
lean_closure_set(v___x_3823_, 1, v_a_3822_);
lean_closure_set(v___x_3823_, 2, v_xs_3815_);
v___x_3824_ = 0;
v___x_3825_ = lean_box(v___x_3824_);
v___x_3826_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3826_, 0, lean_box(0));
lean_closure_set(v___x_3826_, 1, v___x_3823_);
lean_closure_set(v___x_3826_, 2, v___x_3825_);
v___x_3827_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3814_, v_xs_3815_, v___x_3826_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
return v___x_3827_;
}
else
{
lean_dec_ref(v_xs_3815_);
lean_dec_ref(v_f_3814_);
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3828_, lean_object* v_xs_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_){
_start:
{
lean_object* v_res_3835_; 
v_res_3835_ = l_Lean_Meta_mkAppM_x27(v_f_3828_, v_xs_3829_, v_a_3830_, v_a_3831_, v_a_3832_, v_a_3833_);
lean_dec(v_a_3833_);
lean_dec_ref(v_a_3832_);
lean_dec(v_a_3831_);
lean_dec_ref(v_a_3830_);
return v_res_3835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3836_, size_t v_i_3837_, size_t v_stop_3838_, lean_object* v_b_3839_){
_start:
{
lean_object* v___y_3841_; uint8_t v___x_3845_; 
v___x_3845_ = lean_usize_dec_eq(v_i_3837_, v_stop_3838_);
if (v___x_3845_ == 0)
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_array_uget_borrowed(v_as_3836_, v_i_3837_);
if (lean_obj_tag(v___x_3846_) == 0)
{
v___y_3841_ = v_b_3839_;
goto v___jp_3840_;
}
else
{
lean_object* v_val_3847_; lean_object* v___x_3848_; 
v_val_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_val_3847_);
v___x_3848_ = lean_array_push(v_b_3839_, v_val_3847_);
v___y_3841_ = v___x_3848_;
goto v___jp_3840_;
}
}
else
{
return v_b_3839_;
}
v___jp_3840_:
{
size_t v___x_3842_; size_t v___x_3843_; 
v___x_3842_ = ((size_t)1ULL);
v___x_3843_ = lean_usize_add(v_i_3837_, v___x_3842_);
v_i_3837_ = v___x_3843_;
v_b_3839_ = v___y_3841_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3849_, lean_object* v_i_3850_, lean_object* v_stop_3851_, lean_object* v_b_3852_){
_start:
{
size_t v_i_boxed_3853_; size_t v_stop_boxed_3854_; lean_object* v_res_3855_; 
v_i_boxed_3853_ = lean_unbox_usize(v_i_3850_);
lean_dec(v_i_3850_);
v_stop_boxed_3854_ = lean_unbox_usize(v_stop_3851_);
lean_dec(v_stop_3851_);
v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3849_, v_i_boxed_3853_, v_stop_boxed_3854_, v_b_3852_);
lean_dec_ref(v_as_3849_);
return v_res_3855_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3862_; lean_object* v___x_3863_; 
v___x_3862_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3863_ = l_Lean_MessageData_ofFormat(v___x_3862_);
return v___x_3863_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_box(1);
v___x_3865_ = l_Lean_MessageData_ofFormat(v___x_3864_);
return v___x_3865_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3869_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3870_ = l_Lean_MessageData_ofFormat(v___x_3869_);
return v___x_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3871_, lean_object* v_xs_3872_, lean_object* v_x_3873_, lean_object* v_x_3874_, lean_object* v_x_3875_, lean_object* v_x_3876_, lean_object* v_x_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
if (lean_obj_tag(v_x_3877_) == 7)
{
lean_object* v_binderName_3883_; lean_object* v_binderType_3884_; lean_object* v_body_3885_; uint8_t v_binderInfo_3886_; lean_object* v___x_3887_; uint8_t v___x_3888_; 
v_binderName_3883_ = lean_ctor_get(v_x_3877_, 0);
lean_inc(v_binderName_3883_);
v_binderType_3884_ = lean_ctor_get(v_x_3877_, 1);
lean_inc_ref(v_binderType_3884_);
v_body_3885_ = lean_ctor_get(v_x_3877_, 2);
lean_inc_ref(v_body_3885_);
v_binderInfo_3886_ = lean_ctor_get_uint8(v_x_3877_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3877_, 3);
v___x_3887_ = lean_array_get_size(v_xs_3872_);
v___x_3888_ = lean_nat_dec_lt(v_x_3873_, v___x_3887_);
if (v___x_3888_ == 0)
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
lean_dec_ref(v_body_3885_);
lean_dec_ref(v_binderType_3884_);
lean_dec(v_binderName_3883_);
lean_dec(v_x_3875_);
lean_dec(v_x_3873_);
v___x_3889_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3890_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3889_, v_f_3871_, v_x_3874_, v_x_3876_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
lean_dec_ref(v_x_3876_);
lean_dec_ref(v_x_3874_);
return v___x_3890_;
}
else
{
lean_object* v___x_3891_; lean_object* v_d_3892_; lean_object* v___x_3893_; 
v___x_3891_ = lean_array_get_size(v_x_3874_);
v_d_3892_ = lean_expr_instantiate_rev_range(v_binderType_3884_, v_x_3875_, v___x_3891_, v_x_3874_);
lean_dec_ref(v_binderType_3884_);
v___x_3893_ = lean_array_fget_borrowed(v_xs_3872_, v_x_3873_);
if (lean_obj_tag(v___x_3893_) == 0)
{
if (v_binderInfo_3886_ == 3)
{
lean_object* v___x_3894_; uint8_t v___x_3895_; lean_object* v___x_3896_; 
v___x_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3894_, 0, v_d_3892_);
v___x_3895_ = 1;
v___x_3896_ = l_Lean_Meta_mkFreshExprMVar(v___x_3894_, v___x_3895_, v_binderName_3883_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc_n(v_a_3897_, 2);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = lean_unsigned_to_nat(1u);
v___x_3899_ = lean_nat_add(v_x_3873_, v___x_3898_);
lean_dec(v_x_3873_);
v___x_3900_ = lean_array_push(v_x_3874_, v_a_3897_);
v___x_3901_ = l_Lean_Expr_mvarId_x21(v_a_3897_);
lean_dec(v_a_3897_);
v___x_3902_ = lean_array_push(v_x_3876_, v___x_3901_);
v_x_3873_ = v___x_3899_;
v_x_3874_ = v___x_3900_;
v_x_3876_ = v___x_3902_;
v_x_3877_ = v_body_3885_;
goto _start;
}
else
{
lean_dec_ref(v_body_3885_);
lean_dec_ref(v_x_3876_);
lean_dec(v_x_3875_);
lean_dec_ref(v_x_3874_);
lean_dec(v_x_3873_);
lean_dec_ref(v_f_3871_);
return v___x_3896_;
}
}
else
{
lean_object* v___x_3904_; uint8_t v___x_3905_; lean_object* v___x_3906_; 
v___x_3904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3904_, 0, v_d_3892_);
v___x_3905_ = 0;
v___x_3906_ = l_Lean_Meta_mkFreshExprMVar(v___x_3904_, v___x_3905_, v_binderName_3883_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
v___x_3908_ = lean_unsigned_to_nat(1u);
v___x_3909_ = lean_nat_add(v_x_3873_, v___x_3908_);
lean_dec(v_x_3873_);
v___x_3910_ = lean_array_push(v_x_3874_, v_a_3907_);
v_x_3873_ = v___x_3909_;
v_x_3874_ = v___x_3910_;
v_x_3877_ = v_body_3885_;
goto _start;
}
else
{
lean_dec_ref(v_body_3885_);
lean_dec_ref(v_x_3876_);
lean_dec(v_x_3875_);
lean_dec_ref(v_x_3874_);
lean_dec(v_x_3873_);
lean_dec_ref(v_f_3871_);
return v___x_3906_;
}
}
}
else
{
lean_object* v_val_3912_; lean_object* v___x_3913_; 
lean_dec(v_binderName_3883_);
v_val_3912_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3881_);
lean_inc_ref(v_a_3880_);
lean_inc(v_a_3879_);
lean_inc_ref(v_a_3878_);
lean_inc(v_val_3912_);
v___x_3913_ = lean_infer_type(v_val_3912_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = l_Lean_Meta_isExprDefEq(v_d_3892_, v_a_3914_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; uint8_t v___x_3917_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc(v_a_3916_);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = lean_unbox(v_a_3916_);
lean_dec(v_a_3916_);
if (v___x_3917_ == 0)
{
lean_object* v___x_3918_; lean_object* v___x_3919_; 
lean_dec_ref(v_body_3885_);
lean_dec_ref(v_x_3876_);
lean_dec(v_x_3875_);
lean_dec(v_x_3873_);
v___x_3918_ = l_Lean_mkAppN(v_f_3871_, v_x_3874_);
lean_dec_ref(v_x_3874_);
lean_inc(v_val_3912_);
v___x_3919_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3918_, v_val_3912_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
return v___x_3919_;
}
else
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; 
v___x_3920_ = lean_unsigned_to_nat(1u);
v___x_3921_ = lean_nat_add(v_x_3873_, v___x_3920_);
lean_dec(v_x_3873_);
lean_inc(v_val_3912_);
v___x_3922_ = lean_array_push(v_x_3874_, v_val_3912_);
v_x_3873_ = v___x_3921_;
v_x_3874_ = v___x_3922_;
v_x_3877_ = v_body_3885_;
goto _start;
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_dec_ref(v_body_3885_);
lean_dec_ref(v_x_3876_);
lean_dec(v_x_3875_);
lean_dec_ref(v_x_3874_);
lean_dec(v_x_3873_);
lean_dec_ref(v_f_3871_);
v_a_3924_ = lean_ctor_get(v___x_3915_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3915_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3915_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
else
{
lean_dec_ref(v_d_3892_);
lean_dec_ref(v_body_3885_);
lean_dec_ref(v_x_3876_);
lean_dec(v_x_3875_);
lean_dec_ref(v_x_3874_);
lean_dec(v_x_3873_);
lean_dec_ref(v_f_3871_);
return v___x_3913_;
}
}
}
}
else
{
lean_object* v___x_3932_; lean_object* v_type_3933_; lean_object* v___x_3934_; 
v___x_3932_ = lean_array_get_size(v_x_3874_);
v_type_3933_ = lean_expr_instantiate_rev_range(v_x_3877_, v_x_3875_, v___x_3932_, v_x_3874_);
lean_dec(v_x_3875_);
lean_dec_ref(v_x_3877_);
v___x_3934_ = l_Lean_Meta_whnfD(v_type_3933_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; uint8_t v___x_3936_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v___x_3936_ = l_Lean_Expr_isForall(v_a_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; uint8_t v___x_3938_; 
lean_dec(v_a_3935_);
v___x_3937_ = lean_array_get_size(v_xs_3872_);
v___x_3938_ = lean_nat_dec_eq(v_x_3873_, v___x_3937_);
lean_dec(v_x_3873_);
if (v___x_3938_ == 0)
{
lean_object* v___x_3939_; lean_object* v___y_3941_; lean_object* v___x_3954_; uint8_t v___x_3955_; 
lean_dec_ref(v_x_3876_);
lean_dec_ref(v_x_3874_);
v___x_3939_ = lean_unsigned_to_nat(0u);
v___x_3954_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3955_ = lean_nat_dec_lt(v___x_3939_, v___x_3937_);
if (v___x_3955_ == 0)
{
v___y_3941_ = v___x_3954_;
goto v___jp_3940_;
}
else
{
size_t v___x_3956_; size_t v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = ((size_t)0ULL);
v___x_3957_ = lean_usize_of_nat(v___x_3937_);
v___x_3958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3872_, v___x_3956_, v___x_3957_, v___x_3954_);
v___y_3941_ = v___x_3958_;
goto v___jp_3940_;
}
v___jp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3942_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3943_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3944_ = l_Lean_indentExpr(v_f_3871_);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3951_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3941_, v___x_3939_, v___x_3950_);
lean_dec_ref(v___y_3941_);
v___x_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3952_, 0, v___x_3949_);
lean_ctor_set(v___x_3952_, 1, v___x_3951_);
v___x_3953_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3942_, v___x_3952_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
return v___x_3953_;
}
}
else
{
lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3959_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3960_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3959_, v_f_3871_, v_x_3874_, v_x_3876_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_);
lean_dec_ref(v_x_3876_);
lean_dec_ref(v_x_3874_);
return v___x_3960_;
}
}
else
{
v_x_3875_ = v___x_3932_;
v_x_3877_ = v_a_3935_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3876_);
lean_dec_ref(v_x_3874_);
lean_dec(v_x_3873_);
lean_dec_ref(v_f_3871_);
return v___x_3934_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_3962_, lean_object* v_xs_3963_, lean_object* v_x_3964_, lean_object* v_x_3965_, lean_object* v_x_3966_, lean_object* v_x_3967_, lean_object* v_x_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_3962_, v_xs_3963_, v_x_3964_, v_x_3965_, v_x_3966_, v_x_3967_, v_x_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec_ref(v_xs_3963_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_3975_, lean_object* v_xs_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3982_; 
v___x_3982_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_3975_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; lean_object* v_fst_3984_; lean_object* v_snd_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v_fst_3984_ = lean_ctor_get(v_a_3983_, 0);
lean_inc(v_fst_3984_);
v_snd_3985_ = lean_ctor_get(v_a_3983_, 1);
lean_inc(v_snd_3985_);
lean_dec(v_a_3983_);
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_3987_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3988_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_3984_, v_xs_3976_, v___x_3986_, v___x_3987_, v___x_3986_, v___x_3987_, v_snd_3985_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
return v___x_3988_;
}
else
{
lean_object* v_a_3989_; lean_object* v___x_3991_; uint8_t v_isShared_3992_; uint8_t v_isSharedCheck_3996_; 
v_a_3989_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3991_ = v___x_3982_;
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
else
{
lean_inc(v_a_3989_);
lean_dec(v___x_3982_);
v___x_3991_ = lean_box(0);
v_isShared_3992_ = v_isSharedCheck_3996_;
goto v_resetjp_3990_;
}
v_resetjp_3990_:
{
lean_object* v___x_3994_; 
if (v_isShared_3992_ == 0)
{
v___x_3994_ = v___x_3991_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v_a_3989_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_3997_, lean_object* v_xs_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_3997_, v_xs_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_);
lean_dec(v___y_4002_);
lean_dec_ref(v___y_4001_);
lean_dec(v___y_4000_);
lean_dec_ref(v___y_3999_);
lean_dec_ref(v_xs_3998_);
return v_res_4004_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4009_ = l_Lean_MessageData_ofFormat(v___x_4008_);
return v___x_4009_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4010_, lean_object* v_a_4011_){
_start:
{
if (lean_obj_tag(v_a_4010_) == 0)
{
lean_object* v___x_4012_; 
v___x_4012_ = l_List_reverse___redArg(v_a_4011_);
return v___x_4012_;
}
else
{
lean_object* v_head_4013_; lean_object* v_tail_4014_; lean_object* v___x_4016_; uint8_t v_isShared_4017_; uint8_t v_isSharedCheck_4027_; 
v_head_4013_ = lean_ctor_get(v_a_4010_, 0);
v_tail_4014_ = lean_ctor_get(v_a_4010_, 1);
v_isSharedCheck_4027_ = !lean_is_exclusive(v_a_4010_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4016_ = v_a_4010_;
v_isShared_4017_ = v_isSharedCheck_4027_;
goto v_resetjp_4015_;
}
else
{
lean_inc(v_tail_4014_);
lean_inc(v_head_4013_);
lean_dec(v_a_4010_);
v___x_4016_ = lean_box(0);
v_isShared_4017_ = v_isSharedCheck_4027_;
goto v_resetjp_4015_;
}
v_resetjp_4015_:
{
lean_object* v___y_4019_; 
if (lean_obj_tag(v_head_4013_) == 0)
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4019_ = v___x_4024_;
goto v___jp_4018_;
}
else
{
lean_object* v_val_4025_; lean_object* v___x_4026_; 
v_val_4025_ = lean_ctor_get(v_head_4013_, 0);
lean_inc(v_val_4025_);
lean_dec_ref_known(v_head_4013_, 1);
v___x_4026_ = l_Lean_MessageData_ofExpr(v_val_4025_);
v___y_4019_ = v___x_4026_;
goto v___jp_4018_;
}
v___jp_4018_:
{
lean_object* v___x_4021_; 
if (v_isShared_4017_ == 0)
{
lean_ctor_set(v___x_4016_, 1, v_a_4011_);
lean_ctor_set(v___x_4016_, 0, v___y_4019_);
v___x_4021_ = v___x_4016_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4023_; 
v_reuseFailAlloc_4023_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4023_, 0, v___y_4019_);
lean_ctor_set(v_reuseFailAlloc_4023_, 1, v_a_4011_);
v___x_4021_ = v_reuseFailAlloc_4023_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
v_a_4010_ = v_tail_4014_;
v_a_4011_ = v___x_4021_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4028_, lean_object* v_xs_4029_, lean_object* v_x_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4036_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4037_ = l_Lean_MessageData_ofName(v_f_4028_);
v___x_4038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4036_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
v___x_4039_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4038_);
lean_ctor_set(v___x_4040_, 1, v___x_4039_);
v___x_4041_ = lean_array_to_list(v_xs_4029_);
v___x_4042_ = lean_box(0);
v___x_4043_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4041_, v___x_4042_);
v___x_4044_ = l_Lean_MessageData_ofList(v___x_4043_);
v___x_4045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4040_);
lean_ctor_set(v___x_4045_, 1, v___x_4044_);
v___x_4046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
return v___x_4046_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4047_, lean_object* v_xs_4048_, lean_object* v_x_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4047_, v_xs_4048_, v_x_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v_x_4049_);
return v_res_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4056_, lean_object* v_xs_4057_, lean_object* v_k_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_toCold_4064_; lean_object* v_options_4065_; uint8_t v_hasTrace_4066_; 
v_toCold_4064_ = lean_ctor_get(v_a_4061_, 0);
v_options_4065_ = lean_ctor_get(v_toCold_4064_, 2);
v_hasTrace_4066_ = lean_ctor_get_uint8(v_options_4065_, sizeof(void*)*1);
if (v_hasTrace_4066_ == 0)
{
lean_object* v___x_4067_; 
lean_dec_ref(v_xs_4057_);
lean_dec(v_f_4056_);
lean_inc(v_a_4062_);
lean_inc_ref(v_a_4061_);
lean_inc(v_a_4060_);
lean_inc_ref(v_a_4059_);
v___x_4067_ = lean_apply_5(v_k_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, lean_box(0));
return v___x_4067_;
}
else
{
lean_object* v_inheritedTraceOptions_4068_; lean_object* v___f_4069_; lean_object* v___y_4071_; lean_object* v_a_4072_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; uint8_t v___x_4100_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v_a_4104_; lean_object* v___y_4117_; lean_object* v___y_4118_; lean_object* v_a_4119_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v_a_4124_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v_a_4129_; lean_object* v___y_4139_; lean_object* v___y_4140_; lean_object* v_a_4141_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v_a_4153_; lean_object* v___y_4156_; lean_object* v___y_4157_; lean_object* v_a_4158_; lean_object* v___y_4161_; lean_object* v___y_4162_; lean_object* v_a_4163_; 
v_inheritedTraceOptions_4068_ = lean_ctor_get(v_toCold_4064_, 11);
v___f_4069_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4069_, 0, v_f_4056_);
lean_closure_set(v___f_4069_, 1, v_xs_4057_);
v___x_4097_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4098_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4099_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4100_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4099_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4197_; uint8_t v___x_4198_; 
v___x_4197_ = l_Lean_trace_profiler;
v___x_4198_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4065_, v___x_4197_);
if (v___x_4198_ == 0)
{
lean_object* v___x_4199_; 
lean_dec_ref(v___f_4069_);
lean_inc(v_a_4062_);
lean_inc_ref(v_a_4061_);
lean_inc(v_a_4060_);
lean_inc_ref(v_a_4059_);
v___x_4199_ = lean_apply_5(v_k_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, lean_box(0));
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; uint8_t v___x_4203_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
v___x_4201_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4202_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4203_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4202_);
if (v___x_4203_ == 0)
{
lean_dec(v_a_4200_);
return v___x_4199_;
}
else
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_dec_ref_known(v___x_4199_, 1);
lean_inc(v_a_4200_);
v___x_4204_ = l_Lean_MessageData_ofExpr(v_a_4200_);
v___x_4205_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4201_, v___x_4204_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v___x_4207_; uint8_t v_isShared_4208_; uint8_t v_isSharedCheck_4212_; 
v_isSharedCheck_4212_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4212_ == 0)
{
lean_object* v_unused_4213_; 
v_unused_4213_ = lean_ctor_get(v___x_4205_, 0);
lean_dec(v_unused_4213_);
v___x_4207_ = v___x_4205_;
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
else
{
lean_dec(v___x_4205_);
v___x_4207_ = lean_box(0);
v_isShared_4208_ = v_isSharedCheck_4212_;
goto v_resetjp_4206_;
}
v_resetjp_4206_:
{
lean_object* v___x_4210_; 
if (v_isShared_4208_ == 0)
{
lean_ctor_set(v___x_4207_, 0, v_a_4200_);
v___x_4210_ = v___x_4207_;
goto v_reusejp_4209_;
}
else
{
lean_object* v_reuseFailAlloc_4211_; 
v_reuseFailAlloc_4211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4200_);
v___x_4210_ = v_reuseFailAlloc_4211_;
goto v_reusejp_4209_;
}
v_reusejp_4209_:
{
return v___x_4210_;
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v_a_4200_);
v_a_4214_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4205_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4205_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
lean_inc(v_a_4214_);
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
v___y_4071_ = v___x_4219_;
v_a_4072_ = v_a_4214_;
goto v___jp_4070_;
}
}
}
}
}
else
{
lean_object* v_a_4222_; 
v_a_4222_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4222_);
v___y_4071_ = v___x_4199_;
v_a_4072_ = v_a_4222_;
goto v___jp_4070_;
}
}
else
{
goto v___jp_4172_;
}
}
else
{
goto v___jp_4172_;
}
v___jp_4070_:
{
uint8_t v___x_4073_; 
v___x_4073_ = l_Lean_Exception_isInterrupt(v_a_4072_);
if (v___x_4073_ == 0)
{
uint8_t v___x_4074_; 
lean_inc_ref(v_a_4072_);
v___x_4074_ = l_Lean_Exception_isRuntime(v_a_4072_);
if (v___x_4074_ == 0)
{
lean_object* v___x_4075_; lean_object* v___x_4076_; uint8_t v___x_4077_; 
lean_dec_ref(v___y_4071_);
v___x_4075_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4076_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4077_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4076_);
if (v___x_4077_ == 0)
{
lean_object* v___x_4078_; 
v___x_4078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4078_, 0, v_a_4072_);
return v___x_4078_;
}
else
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
lean_inc_ref(v_a_4072_);
v___x_4079_ = l_Lean_Exception_toMessageData(v_a_4072_);
v___x_4080_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4075_, v___x_4079_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v___x_4080_, 0);
lean_dec(v_unused_4088_);
v___x_4082_ = v___x_4080_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_dec(v___x_4080_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
lean_ctor_set_tag(v___x_4082_, 1);
lean_ctor_set(v___x_4082_, 0, v_a_4072_);
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4072_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v_a_4072_);
v_a_4089_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4080_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4080_);
v___x_4091_ = lean_box(0);
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
v_resetjp_4090_:
{
lean_object* v___x_4094_; 
if (v_isShared_4092_ == 0)
{
v___x_4094_ = v___x_4091_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_a_4089_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_4072_);
return v___y_4071_;
}
}
else
{
lean_dec_ref(v_a_4072_);
return v___y_4071_;
}
}
v___jp_4101_:
{
lean_object* v___x_4105_; double v___x_4106_; double v___x_4107_; double v___x_4108_; double v___x_4109_; double v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4105_ = lean_io_mono_nanos_now();
v___x_4106_ = lean_float_of_nat(v___y_4103_);
v___x_4107_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4108_ = lean_float_div(v___x_4106_, v___x_4107_);
v___x_4109_ = lean_float_of_nat(v___x_4105_);
v___x_4110_ = lean_float_div(v___x_4109_, v___x_4107_);
v___x_4111_ = lean_box_float(v___x_4108_);
v___x_4112_ = lean_box_float(v___x_4110_);
v___x_4113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4111_);
lean_ctor_set(v___x_4113_, 1, v___x_4112_);
v___x_4114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4114_, 0, v_a_4104_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4097_, v_hasTrace_4066_, v___x_4098_, v_options_4065_, v___x_4100_, v___y_4102_, v___f_4069_, v___x_4114_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
return v___x_4115_;
}
v___jp_4116_:
{
lean_object* v___x_4120_; 
v___x_4120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4120_, 0, v_a_4119_);
v___y_4102_ = v___y_4117_;
v___y_4103_ = v___y_4118_;
v_a_4104_ = v___x_4120_;
goto v___jp_4101_;
}
v___jp_4121_:
{
lean_object* v___x_4125_; 
v___x_4125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4125_, 0, v_a_4124_);
v___y_4102_ = v___y_4122_;
v___y_4103_ = v___y_4123_;
v_a_4104_ = v___x_4125_;
goto v___jp_4101_;
}
v___jp_4126_:
{
uint8_t v___x_4130_; 
v___x_4130_ = l_Lean_Exception_isInterrupt(v_a_4129_);
if (v___x_4130_ == 0)
{
uint8_t v___x_4131_; 
lean_inc_ref(v_a_4129_);
v___x_4131_ = l_Lean_Exception_isRuntime(v_a_4129_);
if (v___x_4131_ == 0)
{
lean_object* v___x_4132_; lean_object* v___x_4133_; uint8_t v___x_4134_; 
v___x_4132_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4133_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4134_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4133_);
if (v___x_4134_ == 0)
{
v___y_4122_ = v___y_4127_;
v___y_4123_ = v___y_4128_;
v_a_4124_ = v_a_4129_;
goto v___jp_4121_;
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; 
lean_inc_ref(v_a_4129_);
v___x_4135_ = l_Lean_Exception_toMessageData(v_a_4129_);
v___x_4136_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4132_, v___x_4135_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_dec_ref_known(v___x_4136_, 1);
v___y_4122_ = v___y_4127_;
v___y_4123_ = v___y_4128_;
v_a_4124_ = v_a_4129_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4137_; 
lean_dec_ref(v_a_4129_);
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
v___y_4122_ = v___y_4127_;
v___y_4123_ = v___y_4128_;
v_a_4124_ = v_a_4137_;
goto v___jp_4121_;
}
}
}
else
{
v___y_4122_ = v___y_4127_;
v___y_4123_ = v___y_4128_;
v_a_4124_ = v_a_4129_;
goto v___jp_4121_;
}
}
else
{
v___y_4122_ = v___y_4127_;
v___y_4123_ = v___y_4128_;
v_a_4124_ = v_a_4129_;
goto v___jp_4121_;
}
}
v___jp_4138_:
{
lean_object* v___x_4142_; double v___x_4143_; double v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4142_ = lean_io_get_num_heartbeats();
v___x_4143_ = lean_float_of_nat(v___y_4140_);
v___x_4144_ = lean_float_of_nat(v___x_4142_);
v___x_4145_ = lean_box_float(v___x_4143_);
v___x_4146_ = lean_box_float(v___x_4144_);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4145_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v_a_4141_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4097_, v_hasTrace_4066_, v___x_4098_, v_options_4065_, v___x_4100_, v___y_4139_, v___f_4069_, v___x_4148_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
return v___x_4149_;
}
v___jp_4150_:
{
lean_object* v___x_4154_; 
v___x_4154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4154_, 0, v_a_4153_);
v___y_4139_ = v___y_4151_;
v___y_4140_ = v___y_4152_;
v_a_4141_ = v___x_4154_;
goto v___jp_4138_;
}
v___jp_4155_:
{
lean_object* v___x_4159_; 
v___x_4159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4159_, 0, v_a_4158_);
v___y_4139_ = v___y_4156_;
v___y_4140_ = v___y_4157_;
v_a_4141_ = v___x_4159_;
goto v___jp_4138_;
}
v___jp_4160_:
{
uint8_t v___x_4164_; 
v___x_4164_ = l_Lean_Exception_isInterrupt(v_a_4163_);
if (v___x_4164_ == 0)
{
uint8_t v___x_4165_; 
lean_inc_ref(v_a_4163_);
v___x_4165_ = l_Lean_Exception_isRuntime(v_a_4163_);
if (v___x_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; 
v___x_4166_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4167_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4167_);
if (v___x_4168_ == 0)
{
v___y_4156_ = v___y_4161_;
v___y_4157_ = v___y_4162_;
v_a_4158_ = v_a_4163_;
goto v___jp_4155_;
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
lean_inc_ref(v_a_4163_);
v___x_4169_ = l_Lean_Exception_toMessageData(v_a_4163_);
v___x_4170_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4166_, v___x_4169_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_dec_ref_known(v___x_4170_, 1);
v___y_4156_ = v___y_4161_;
v___y_4157_ = v___y_4162_;
v_a_4158_ = v_a_4163_;
goto v___jp_4155_;
}
else
{
lean_object* v_a_4171_; 
lean_dec_ref(v_a_4163_);
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___y_4156_ = v___y_4161_;
v___y_4157_ = v___y_4162_;
v_a_4158_ = v_a_4171_;
goto v___jp_4155_;
}
}
}
else
{
v___y_4156_ = v___y_4161_;
v___y_4157_ = v___y_4162_;
v_a_4158_ = v_a_4163_;
goto v___jp_4155_;
}
}
else
{
v___y_4156_ = v___y_4161_;
v___y_4157_ = v___y_4162_;
v_a_4158_ = v_a_4163_;
goto v___jp_4155_;
}
}
v___jp_4172_:
{
lean_object* v___x_4173_; lean_object* v_a_4174_; lean_object* v___x_4175_; uint8_t v___x_4176_; 
v___x_4173_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4062_);
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref(v___x_4173_);
v___x_4175_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4176_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4065_, v___x_4175_);
if (v___x_4176_ == 0)
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_io_mono_nanos_now();
lean_inc(v_a_4062_);
lean_inc_ref(v_a_4061_);
lean_inc(v_a_4060_);
lean_inc_ref(v_a_4059_);
v___x_4178_ = lean_apply_5(v_k_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, lean_box(0));
if (lean_obj_tag(v___x_4178_) == 0)
{
lean_object* v_a_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; uint8_t v___x_4182_; 
v_a_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4179_);
lean_dec_ref_known(v___x_4178_, 1);
v___x_4180_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4181_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4182_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4181_);
if (v___x_4182_ == 0)
{
v___y_4117_ = v_a_4174_;
v___y_4118_ = v___x_4177_;
v_a_4119_ = v_a_4179_;
goto v___jp_4116_;
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; 
lean_inc(v_a_4179_);
v___x_4183_ = l_Lean_MessageData_ofExpr(v_a_4179_);
v___x_4184_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4180_, v___x_4183_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4184_) == 0)
{
lean_dec_ref_known(v___x_4184_, 1);
v___y_4117_ = v_a_4174_;
v___y_4118_ = v___x_4177_;
v_a_4119_ = v_a_4179_;
goto v___jp_4116_;
}
else
{
lean_object* v_a_4185_; 
lean_dec(v_a_4179_);
v_a_4185_ = lean_ctor_get(v___x_4184_, 0);
lean_inc(v_a_4185_);
lean_dec_ref_known(v___x_4184_, 1);
v___y_4127_ = v_a_4174_;
v___y_4128_ = v___x_4177_;
v_a_4129_ = v_a_4185_;
goto v___jp_4126_;
}
}
}
else
{
lean_object* v_a_4186_; 
v_a_4186_ = lean_ctor_get(v___x_4178_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4178_, 1);
v___y_4127_ = v_a_4174_;
v___y_4128_ = v___x_4177_;
v_a_4129_ = v_a_4186_;
goto v___jp_4126_;
}
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4062_);
lean_inc_ref(v_a_4061_);
lean_inc(v_a_4060_);
lean_inc_ref(v_a_4059_);
v___x_4188_ = lean_apply_5(v_k_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, lean_box(0));
if (lean_obj_tag(v___x_4188_) == 0)
{
lean_object* v_a_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; uint8_t v___x_4192_; 
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref_known(v___x_4188_, 1);
v___x_4190_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4191_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4192_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4068_, v_options_4065_, v___x_4191_);
if (v___x_4192_ == 0)
{
v___y_4151_ = v_a_4174_;
v___y_4152_ = v___x_4187_;
v_a_4153_ = v_a_4189_;
goto v___jp_4150_;
}
else
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_inc(v_a_4189_);
v___x_4193_ = l_Lean_MessageData_ofExpr(v_a_4189_);
v___x_4194_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4190_, v___x_4193_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4194_) == 0)
{
lean_dec_ref_known(v___x_4194_, 1);
v___y_4151_ = v_a_4174_;
v___y_4152_ = v___x_4187_;
v_a_4153_ = v_a_4189_;
goto v___jp_4150_;
}
else
{
lean_object* v_a_4195_; 
lean_dec(v_a_4189_);
v_a_4195_ = lean_ctor_get(v___x_4194_, 0);
lean_inc(v_a_4195_);
lean_dec_ref_known(v___x_4194_, 1);
v___y_4161_ = v_a_4174_;
v___y_4162_ = v___x_4187_;
v_a_4163_ = v_a_4195_;
goto v___jp_4160_;
}
}
}
else
{
lean_object* v_a_4196_; 
v_a_4196_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4188_, 1);
v___y_4161_ = v_a_4174_;
v___y_4162_ = v___x_4187_;
v_a_4163_ = v_a_4196_;
goto v___jp_4160_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4223_, lean_object* v_xs_4224_, lean_object* v_k_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_, lean_object* v_a_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4223_, v_xs_4224_, v_k_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
lean_dec(v_a_4229_);
lean_dec_ref(v_a_4228_);
lean_dec(v_a_4227_);
lean_dec_ref(v_a_4226_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4232_, lean_object* v_xs_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_){
_start:
{
lean_object* v___f_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; 
lean_inc_ref(v_xs_4233_);
lean_inc(v_constName_4232_);
v___f_4239_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4239_, 0, v_constName_4232_);
lean_closure_set(v___f_4239_, 1, v_xs_4233_);
v___x_4240_ = 0;
v___x_4241_ = lean_box(v___x_4240_);
v___x_4242_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4242_, 0, lean_box(0));
lean_closure_set(v___x_4242_, 1, v___f_4239_);
lean_closure_set(v___x_4242_, 2, v___x_4241_);
v___x_4243_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4232_, v_xs_4233_, v___x_4242_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_);
return v___x_4243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4244_, lean_object* v_xs_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_, lean_object* v_a_4250_){
_start:
{
lean_object* v_res_4251_; 
v_res_4251_ = l_Lean_Meta_mkAppOptM(v_constName_4244_, v_xs_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
lean_dec(v_a_4249_);
lean_dec_ref(v_a_4248_);
lean_dec(v_a_4247_);
lean_dec_ref(v_a_4246_);
return v_res_4251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4252_, lean_object* v_xs_4253_, lean_object* v_x_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4260_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4261_ = l_Lean_MessageData_ofExpr(v_f_4252_);
v___x_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = lean_array_to_list(v_xs_4253_);
v___x_4266_ = lean_box(0);
v___x_4267_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4265_, v___x_4266_);
v___x_4268_ = l_Lean_MessageData_ofList(v___x_4267_);
v___x_4269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4269_, 0, v___x_4264_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4269_);
return v___x_4270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4271_, lean_object* v_xs_4272_, lean_object* v_x_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4271_, v_xs_4272_, v_x_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec_ref(v_x_4273_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4280_, lean_object* v_xs_4281_, lean_object* v_k_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_){
_start:
{
lean_object* v_toCold_4288_; lean_object* v_options_4289_; uint8_t v_hasTrace_4290_; 
v_toCold_4288_ = lean_ctor_get(v_a_4285_, 0);
v_options_4289_ = lean_ctor_get(v_toCold_4288_, 2);
v_hasTrace_4290_ = lean_ctor_get_uint8(v_options_4289_, sizeof(void*)*1);
if (v_hasTrace_4290_ == 0)
{
lean_object* v___x_4291_; 
lean_dec_ref(v_xs_4281_);
lean_dec_ref(v_f_4280_);
lean_inc(v_a_4286_);
lean_inc_ref(v_a_4285_);
lean_inc(v_a_4284_);
lean_inc_ref(v_a_4283_);
v___x_4291_ = lean_apply_5(v_k_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, lean_box(0));
return v___x_4291_;
}
else
{
lean_object* v_inheritedTraceOptions_4292_; lean_object* v___f_4293_; lean_object* v___y_4295_; lean_object* v_a_4296_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; uint8_t v___x_4324_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v_a_4328_; lean_object* v___y_4341_; lean_object* v___y_4342_; lean_object* v_a_4343_; lean_object* v___y_4346_; lean_object* v___y_4347_; lean_object* v_a_4348_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v_a_4353_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v_a_4365_; lean_object* v___y_4375_; lean_object* v___y_4376_; lean_object* v_a_4377_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v_a_4382_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v_a_4387_; 
v_inheritedTraceOptions_4292_ = lean_ctor_get(v_toCold_4288_, 11);
v___f_4293_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4293_, 0, v_f_4280_);
lean_closure_set(v___f_4293_, 1, v_xs_4281_);
v___x_4321_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4322_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4323_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4324_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4289_, v___x_4323_);
if (v___x_4324_ == 0)
{
lean_object* v___x_4421_; uint8_t v___x_4422_; 
v___x_4421_ = l_Lean_trace_profiler;
v___x_4422_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4289_, v___x_4421_);
if (v___x_4422_ == 0)
{
lean_object* v___x_4423_; 
lean_dec_ref(v___f_4293_);
lean_inc(v_a_4286_);
lean_inc_ref(v_a_4285_);
lean_inc(v_a_4284_);
lean_inc_ref(v_a_4283_);
v___x_4423_ = lean_apply_5(v_k_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, lean_box(0));
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; uint8_t v___x_4427_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
v___x_4425_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4426_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4427_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4289_, v___x_4426_);
if (v___x_4427_ == 0)
{
lean_dec(v_a_4424_);
return v___x_4423_;
}
else
{
lean_object* v___x_4428_; lean_object* v___x_4429_; 
lean_dec_ref_known(v___x_4423_, 1);
lean_inc(v_a_4424_);
v___x_4428_ = l_Lean_MessageData_ofExpr(v_a_4424_);
v___x_4429_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4425_, v___x_4428_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v___x_4431_; uint8_t v_isShared_4432_; uint8_t v_isSharedCheck_4436_; 
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4436_ == 0)
{
lean_object* v_unused_4437_; 
v_unused_4437_ = lean_ctor_get(v___x_4429_, 0);
lean_dec(v_unused_4437_);
v___x_4431_ = v___x_4429_;
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
else
{
lean_dec(v___x_4429_);
v___x_4431_ = lean_box(0);
v_isShared_4432_ = v_isSharedCheck_4436_;
goto v_resetjp_4430_;
}
v_resetjp_4430_:
{
lean_object* v___x_4434_; 
if (v_isShared_4432_ == 0)
{
lean_ctor_set(v___x_4431_, 0, v_a_4424_);
v___x_4434_ = v___x_4431_;
goto v_reusejp_4433_;
}
else
{
lean_object* v_reuseFailAlloc_4435_; 
v_reuseFailAlloc_4435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4435_, 0, v_a_4424_);
v___x_4434_ = v_reuseFailAlloc_4435_;
goto v_reusejp_4433_;
}
v_reusejp_4433_:
{
return v___x_4434_;
}
}
}
else
{
lean_object* v_a_4438_; lean_object* v___x_4440_; uint8_t v_isShared_4441_; uint8_t v_isSharedCheck_4445_; 
lean_dec(v_a_4424_);
v_a_4438_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4440_ = v___x_4429_;
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
else
{
lean_inc(v_a_4438_);
lean_dec(v___x_4429_);
v___x_4440_ = lean_box(0);
v_isShared_4441_ = v_isSharedCheck_4445_;
goto v_resetjp_4439_;
}
v_resetjp_4439_:
{
lean_object* v___x_4443_; 
lean_inc(v_a_4438_);
if (v_isShared_4441_ == 0)
{
v___x_4443_ = v___x_4440_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_a_4438_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
v___y_4295_ = v___x_4443_;
v_a_4296_ = v_a_4438_;
goto v___jp_4294_;
}
}
}
}
}
else
{
lean_object* v_a_4446_; 
v_a_4446_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4446_);
v___y_4295_ = v___x_4423_;
v_a_4296_ = v_a_4446_;
goto v___jp_4294_;
}
}
else
{
goto v___jp_4396_;
}
}
else
{
goto v___jp_4396_;
}
v___jp_4294_:
{
uint8_t v___x_4297_; 
v___x_4297_ = l_Lean_Exception_isInterrupt(v_a_4296_);
if (v___x_4297_ == 0)
{
uint8_t v___x_4298_; 
lean_inc_ref(v_a_4296_);
v___x_4298_ = l_Lean_Exception_isRuntime(v_a_4296_);
if (v___x_4298_ == 0)
{
lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
lean_dec_ref(v___y_4295_);
v___x_4299_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4300_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4301_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4289_, v___x_4300_);
if (v___x_4301_ == 0)
{
lean_object* v___x_4302_; 
v___x_4302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4302_, 0, v_a_4296_);
return v___x_4302_;
}
else
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
lean_inc_ref(v_a_4296_);
v___x_4303_ = l_Lean_Exception_toMessageData(v_a_4296_);
v___x_4304_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4299_, v___x_4303_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4311_ == 0)
{
lean_object* v_unused_4312_; 
v_unused_4312_ = lean_ctor_get(v___x_4304_, 0);
lean_dec(v_unused_4312_);
v___x_4306_ = v___x_4304_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_dec(v___x_4304_);
v___x_4306_ = lean_box(0);
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
v_resetjp_4305_:
{
lean_object* v___x_4309_; 
if (v_isShared_4307_ == 0)
{
lean_ctor_set_tag(v___x_4306_, 1);
lean_ctor_set(v___x_4306_, 0, v_a_4296_);
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4296_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
return v___x_4309_;
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
lean_dec_ref(v_a_4296_);
v_a_4313_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4320_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4320_ == 0)
{
v___x_4315_ = v___x_4304_;
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4304_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4320_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v___x_4318_; 
if (v_isShared_4316_ == 0)
{
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
return v___x_4318_;
}
}
}
}
}
else
{
lean_dec_ref(v_a_4296_);
return v___y_4295_;
}
}
else
{
lean_dec_ref(v_a_4296_);
return v___y_4295_;
}
}
v___jp_4325_:
{
lean_object* v___x_4329_; double v___x_4330_; double v___x_4331_; double v___x_4332_; double v___x_4333_; double v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; 
v___x_4329_ = lean_io_mono_nanos_now();
v___x_4330_ = lean_float_of_nat(v___y_4326_);
v___x_4331_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4332_ = lean_float_div(v___x_4330_, v___x_4331_);
v___x_4333_ = lean_float_of_nat(v___x_4329_);
v___x_4334_ = lean_float_div(v___x_4333_, v___x_4331_);
v___x_4335_ = lean_box_float(v___x_4332_);
v___x_4336_ = lean_box_float(v___x_4334_);
v___x_4337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4337_, 0, v___x_4335_);
lean_ctor_set(v___x_4337_, 1, v___x_4336_);
v___x_4338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4338_, 0, v_a_4328_);
lean_ctor_set(v___x_4338_, 1, v___x_4337_);
v___x_4339_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4321_, v_hasTrace_4290_, v___x_4322_, v_options_4289_, v___x_4324_, v___y_4327_, v___f_4293_, v___x_4338_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
return v___x_4339_;
}
v___jp_4340_:
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4344_, 0, v_a_4343_);
v___y_4326_ = v___y_4341_;
v___y_4327_ = v___y_4342_;
v_a_4328_ = v___x_4344_;
goto v___jp_4325_;
}
v___jp_4345_:
{
lean_object* v___x_4349_; 
v___x_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4349_, 0, v_a_4348_);
v___y_4326_ = v___y_4346_;
v___y_4327_ = v___y_4347_;
v_a_4328_ = v___x_4349_;
goto v___jp_4325_;
}
v___jp_4350_:
{
uint8_t v___x_4354_; 
v___x_4354_ = l_Lean_Exception_isInterrupt(v_a_4353_);
if (v___x_4354_ == 0)
{
uint8_t v___x_4355_; 
lean_inc_ref(v_a_4353_);
v___x_4355_ = l_Lean_Exception_isRuntime(v_a_4353_);
if (v___x_4355_ == 0)
{
lean_object* v___x_4356_; lean_object* v___x_4357_; uint8_t v___x_4358_; 
v___x_4356_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4357_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4358_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4289_, v___x_4357_);
if (v___x_4358_ == 0)
{
v___y_4346_ = v___y_4351_;
v___y_4347_ = v___y_4352_;
v_a_4348_ = v_a_4353_;
goto v___jp_4345_;
}
else
{
lean_object* v___x_4359_; lean_object* v___x_4360_; 
lean_inc_ref(v_a_4353_);
v___x_4359_ = l_Lean_Exception_toMessageData(v_a_4353_);
v___x_4360_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4356_, v___x_4359_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_dec_ref_known(v___x_4360_, 1);
v___y_4346_ = v___y_4351_;
v___y_4347_ = v___y_4352_;
v_a_4348_ = v_a_4353_;
goto v___jp_4345_;
}
else
{
lean_object* v_a_4361_; 
lean_dec_ref(v_a_4353_);
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
v___y_4346_ = v___y_4351_;
v___y_4347_ = v___y_4352_;
v_a_4348_ = v_a_4361_;
goto v___jp_4345_;
}
}
}
else
{
v___y_4346_ = v___y_4351_;
v___y_4347_ = v___y_4352_;
v_a_4348_ = v_a_4353_;
goto v___jp_4345_;
}
}
else
{
v___y_4346_ = v___y_4351_;
v___y_4347_ = v___y_4352_;
v_a_4348_ = v_a_4353_;
goto v___jp_4345_;
}
}
v___jp_4362_:
{
lean_object* v___x_4366_; double v___x_4367_; double v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; 
v___x_4366_ = lean_io_get_num_heartbeats();
v___x_4367_ = lean_float_of_nat(v___y_4363_);
v___x_4368_ = lean_float_of_nat(v___x_4366_);
v___x_4369_ = lean_box_float(v___x_4367_);
v___x_4370_ = lean_box_float(v___x_4368_);
v___x_4371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4371_, 0, v___x_4369_);
lean_ctor_set(v___x_4371_, 1, v___x_4370_);
v___x_4372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4372_, 0, v_a_4365_);
lean_ctor_set(v___x_4372_, 1, v___x_4371_);
v___x_4373_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4321_, v_hasTrace_4290_, v___x_4322_, v_options_4289_, v___x_4324_, v___y_4364_, v___f_4293_, v___x_4372_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
return v___x_4373_;
}
v___jp_4374_:
{
lean_object* v___x_4378_; 
v___x_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4378_, 0, v_a_4377_);
v___y_4363_ = v___y_4375_;
v___y_4364_ = v___y_4376_;
v_a_4365_ = v___x_4378_;
goto v___jp_4362_;
}
v___jp_4379_:
{
lean_object* v___x_4383_; 
v___x_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4383_, 0, v_a_4382_);
v___y_4363_ = v___y_4380_;
v___y_4364_ = v___y_4381_;
v_a_4365_ = v___x_4383_;
goto v___jp_4362_;
}
v___jp_4384_:
{
uint8_t v___x_4388_; 
v___x_4388_ = l_Lean_Exception_isInterrupt(v_a_4387_);
if (v___x_4388_ == 0)
{
uint8_t v___x_4389_; 
lean_inc_ref(v_a_4387_);
v___x_4389_ = l_Lean_Exception_isRuntime(v_a_4387_);
if (v___x_4389_ == 0)
{
lean_object* v___x_4390_; lean_object* v___x_4391_; uint8_t v___x_4392_; 
v___x_4390_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4391_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4392_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4289_, v___x_4391_);
if (v___x_4392_ == 0)
{
v___y_4380_ = v___y_4385_;
v___y_4381_ = v___y_4386_;
v_a_4382_ = v_a_4387_;
goto v___jp_4379_;
}
else
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
lean_inc_ref(v_a_4387_);
v___x_4393_ = l_Lean_Exception_toMessageData(v_a_4387_);
v___x_4394_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4390_, v___x_4393_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_dec_ref_known(v___x_4394_, 1);
v___y_4380_ = v___y_4385_;
v___y_4381_ = v___y_4386_;
v_a_4382_ = v_a_4387_;
goto v___jp_4379_;
}
else
{
lean_object* v_a_4395_; 
lean_dec_ref(v_a_4387_);
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
v___y_4380_ = v___y_4385_;
v___y_4381_ = v___y_4386_;
v_a_4382_ = v_a_4395_;
goto v___jp_4379_;
}
}
}
else
{
v___y_4380_ = v___y_4385_;
v___y_4381_ = v___y_4386_;
v_a_4382_ = v_a_4387_;
goto v___jp_4379_;
}
}
else
{
v___y_4380_ = v___y_4385_;
v___y_4381_ = v___y_4386_;
v_a_4382_ = v_a_4387_;
goto v___jp_4379_;
}
}
v___jp_4396_:
{
lean_object* v___x_4397_; lean_object* v_a_4398_; lean_object* v___x_4399_; uint8_t v___x_4400_; 
v___x_4397_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4286_);
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref(v___x_4397_);
v___x_4399_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4400_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4289_, v___x_4399_);
if (v___x_4400_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_io_mono_nanos_now();
lean_inc(v_a_4286_);
lean_inc_ref(v_a_4285_);
lean_inc(v_a_4284_);
lean_inc_ref(v_a_4283_);
v___x_4402_ = lean_apply_5(v_k_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, lean_box(0));
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v___x_4404_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4405_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4406_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4289_, v___x_4405_);
if (v___x_4406_ == 0)
{
v___y_4341_ = v___x_4401_;
v___y_4342_ = v_a_4398_;
v_a_4343_ = v_a_4403_;
goto v___jp_4340_;
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
lean_inc(v_a_4403_);
v___x_4407_ = l_Lean_MessageData_ofExpr(v_a_4403_);
v___x_4408_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4404_, v___x_4407_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_dec_ref_known(v___x_4408_, 1);
v___y_4341_ = v___x_4401_;
v___y_4342_ = v_a_4398_;
v_a_4343_ = v_a_4403_;
goto v___jp_4340_;
}
else
{
lean_object* v_a_4409_; 
lean_dec(v_a_4403_);
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v___y_4351_ = v___x_4401_;
v___y_4352_ = v_a_4398_;
v_a_4353_ = v_a_4409_;
goto v___jp_4350_;
}
}
}
else
{
lean_object* v_a_4410_; 
v_a_4410_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4402_, 1);
v___y_4351_ = v___x_4401_;
v___y_4352_ = v_a_4398_;
v_a_4353_ = v_a_4410_;
goto v___jp_4350_;
}
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4411_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4286_);
lean_inc_ref(v_a_4285_);
lean_inc(v_a_4284_);
lean_inc_ref(v_a_4283_);
v___x_4412_ = lean_apply_5(v_k_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_, lean_box(0));
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4415_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4416_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4292_, v_options_4289_, v___x_4415_);
if (v___x_4416_ == 0)
{
v___y_4375_ = v___x_4411_;
v___y_4376_ = v_a_4398_;
v_a_4377_ = v_a_4413_;
goto v___jp_4374_;
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_inc(v_a_4413_);
v___x_4417_ = l_Lean_MessageData_ofExpr(v_a_4413_);
v___x_4418_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4414_, v___x_4417_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
if (lean_obj_tag(v___x_4418_) == 0)
{
lean_dec_ref_known(v___x_4418_, 1);
v___y_4375_ = v___x_4411_;
v___y_4376_ = v_a_4398_;
v_a_4377_ = v_a_4413_;
goto v___jp_4374_;
}
else
{
lean_object* v_a_4419_; 
lean_dec(v_a_4413_);
v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
lean_inc(v_a_4419_);
lean_dec_ref_known(v___x_4418_, 1);
v___y_4385_ = v___x_4411_;
v___y_4386_ = v_a_4398_;
v_a_4387_ = v_a_4419_;
goto v___jp_4384_;
}
}
}
else
{
lean_object* v_a_4420_; 
v_a_4420_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4420_);
lean_dec_ref_known(v___x_4412_, 1);
v___y_4385_ = v___x_4411_;
v___y_4386_ = v_a_4398_;
v_a_4387_ = v_a_4420_;
goto v___jp_4384_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4447_, lean_object* v_xs_4448_, lean_object* v_k_4449_, lean_object* v_a_4450_, lean_object* v_a_4451_, lean_object* v_a_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4447_, v_xs_4448_, v_k_4449_, v_a_4450_, v_a_4451_, v_a_4452_, v_a_4453_);
lean_dec(v_a_4453_);
lean_dec_ref(v_a_4452_);
lean_dec(v_a_4451_);
lean_dec_ref(v_a_4450_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4456_, lean_object* v_xs_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_, lean_object* v_a_4460_, lean_object* v_a_4461_){
_start:
{
lean_object* v___x_4463_; 
lean_inc(v_a_4461_);
lean_inc_ref(v_a_4460_);
lean_inc(v_a_4459_);
lean_inc_ref(v_a_4458_);
lean_inc_ref(v_f_4456_);
v___x_4463_ = lean_infer_type(v_f_4456_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___x_4463_, 1);
v___x_4465_ = lean_unsigned_to_nat(0u);
v___x_4466_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4457_);
lean_inc_ref(v_f_4456_);
v___x_4467_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4467_, 0, v_f_4456_);
lean_closure_set(v___x_4467_, 1, v_xs_4457_);
lean_closure_set(v___x_4467_, 2, v___x_4465_);
lean_closure_set(v___x_4467_, 3, v___x_4466_);
lean_closure_set(v___x_4467_, 4, v___x_4465_);
lean_closure_set(v___x_4467_, 5, v___x_4466_);
lean_closure_set(v___x_4467_, 6, v_a_4464_);
v___x_4468_ = 0;
v___x_4469_ = lean_box(v___x_4468_);
v___x_4470_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4470_, 0, lean_box(0));
lean_closure_set(v___x_4470_, 1, v___x_4467_);
lean_closure_set(v___x_4470_, 2, v___x_4469_);
v___x_4471_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4456_, v_xs_4457_, v___x_4470_, v_a_4458_, v_a_4459_, v_a_4460_, v_a_4461_);
return v___x_4471_;
}
else
{
lean_dec_ref(v_xs_4457_);
lean_dec_ref(v_f_4456_);
return v___x_4463_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4472_, lean_object* v_xs_4473_, lean_object* v_a_4474_, lean_object* v_a_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_){
_start:
{
lean_object* v_res_4479_; 
v_res_4479_ = l_Lean_Meta_mkAppOptM_x27(v_f_4472_, v_xs_4473_, v_a_4474_, v_a_4475_, v_a_4476_, v_a_4477_);
lean_dec(v_a_4477_);
lean_dec_ref(v_a_4476_);
lean_dec(v_a_4475_);
lean_dec_ref(v_a_4474_);
return v_res_4479_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4487_; lean_object* v___x_4488_; 
v___x_4487_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4488_ = l_Lean_MessageData_ofFormat(v___x_4487_);
return v___x_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4489_, lean_object* v_h1_4490_, lean_object* v_h2_4491_, lean_object* v_a_4492_, lean_object* v_a_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_){
_start:
{
lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___x_4507_; uint8_t v___x_4508_; 
v___x_4507_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4508_ = l_Lean_Expr_isAppOf(v_h2_4491_, v___x_4507_);
if (v___x_4508_ == 0)
{
lean_object* v___x_4509_; 
lean_inc_ref(v_h2_4491_);
v___x_4509_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4491_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_);
if (lean_obj_tag(v___x_4509_) == 0)
{
lean_object* v_a_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; uint8_t v___x_4513_; 
v_a_4510_ = lean_ctor_get(v___x_4509_, 0);
lean_inc(v_a_4510_);
lean_dec_ref_known(v___x_4509_, 1);
v___x_4511_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4512_ = lean_unsigned_to_nat(3u);
v___x_4513_ = l_Lean_Expr_isAppOfArity(v_a_4510_, v___x_4511_, v___x_4512_);
if (v___x_4513_ == 0)
{
lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
lean_dec_ref(v_h1_4490_);
lean_dec_ref(v_motive_4489_);
v___x_4514_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4515_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4516_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4491_, v_a_4510_);
v___x_4517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4515_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
v___x_4518_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4514_, v___x_4517_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_);
return v___x_4518_;
}
else
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; 
v___x_4519_ = l_Lean_Expr_appFn_x21(v_a_4510_);
v___x_4520_ = l_Lean_Expr_appFn_x21(v___x_4519_);
v___x_4521_ = l_Lean_Expr_appArg_x21(v___x_4520_);
lean_dec_ref(v___x_4520_);
v___x_4522_ = l_Lean_Expr_appArg_x21(v___x_4519_);
lean_dec_ref(v___x_4519_);
v___x_4523_ = l_Lean_Expr_appArg_x21(v_a_4510_);
lean_dec(v_a_4510_);
lean_inc_ref(v___x_4521_);
v___x_4524_ = l_Lean_Meta_getLevel(v___x_4521_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_);
if (lean_obj_tag(v___x_4524_) == 0)
{
lean_object* v_a_4525_; lean_object* v___x_4526_; 
v_a_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc(v_a_4525_);
lean_dec_ref_known(v___x_4524_, 1);
lean_inc_ref(v_motive_4489_);
v___x_4526_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4489_, v_a_4492_, v_a_4493_, v_a_4494_, v_a_4495_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4550_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4529_ = v___x_4526_;
v_isShared_4530_ = v_isSharedCheck_4550_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4526_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4550_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
if (lean_obj_tag(v_a_4527_) == 7)
{
lean_object* v_body_4531_; 
v_body_4531_ = lean_ctor_get(v_a_4527_, 2);
lean_inc_ref(v_body_4531_);
lean_dec_ref_known(v_a_4527_, 3);
if (lean_obj_tag(v_body_4531_) == 3)
{
lean_object* v_u_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4548_; 
v_u_4532_ = lean_ctor_get(v_body_4531_, 0);
lean_inc(v_u_4532_);
lean_dec_ref_known(v_body_4531_, 1);
v___x_4533_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4534_ = lean_box(0);
v___x_4535_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4535_, 0, v_a_4525_);
lean_ctor_set(v___x_4535_, 1, v___x_4534_);
v___x_4536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4536_, 0, v_u_4532_);
lean_ctor_set(v___x_4536_, 1, v___x_4535_);
v___x_4537_ = l_Lean_mkConst(v___x_4533_, v___x_4536_);
v___x_4538_ = lean_unsigned_to_nat(6u);
v___x_4539_ = lean_mk_empty_array_with_capacity(v___x_4538_);
v___x_4540_ = lean_array_push(v___x_4539_, v___x_4521_);
v___x_4541_ = lean_array_push(v___x_4540_, v___x_4522_);
v___x_4542_ = lean_array_push(v___x_4541_, v_motive_4489_);
v___x_4543_ = lean_array_push(v___x_4542_, v_h1_4490_);
v___x_4544_ = lean_array_push(v___x_4543_, v___x_4523_);
v___x_4545_ = lean_array_push(v___x_4544_, v_h2_4491_);
v___x_4546_ = l_Lean_mkAppN(v___x_4537_, v___x_4545_);
lean_dec_ref(v___x_4545_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4546_);
v___x_4548_ = v___x_4529_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4546_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
else
{
lean_dec_ref(v_body_4531_);
lean_del_object(v___x_4529_);
lean_dec(v_a_4525_);
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v___x_4521_);
lean_dec_ref(v_h2_4491_);
lean_dec_ref(v_h1_4490_);
v___y_4498_ = v_a_4492_;
v___y_4499_ = v_a_4493_;
v___y_4500_ = v_a_4494_;
v___y_4501_ = v_a_4495_;
goto v___jp_4497_;
}
}
else
{
lean_del_object(v___x_4529_);
lean_dec(v_a_4527_);
lean_dec(v_a_4525_);
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v___x_4521_);
lean_dec_ref(v_h2_4491_);
lean_dec_ref(v_h1_4490_);
v___y_4498_ = v_a_4492_;
v___y_4499_ = v_a_4493_;
v___y_4500_ = v_a_4494_;
v___y_4501_ = v_a_4495_;
goto v___jp_4497_;
}
}
}
else
{
lean_dec(v_a_4525_);
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v___x_4521_);
lean_dec_ref(v_h2_4491_);
lean_dec_ref(v_h1_4490_);
lean_dec_ref(v_motive_4489_);
return v___x_4526_;
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec_ref(v___x_4523_);
lean_dec_ref(v___x_4522_);
lean_dec_ref(v___x_4521_);
lean_dec_ref(v_h2_4491_);
lean_dec_ref(v_h1_4490_);
lean_dec_ref(v_motive_4489_);
v_a_4551_ = lean_ctor_get(v___x_4524_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4524_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4524_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4524_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4491_);
lean_dec_ref(v_h1_4490_);
lean_dec_ref(v_motive_4489_);
return v___x_4509_;
}
}
else
{
lean_object* v___x_4559_; 
lean_dec_ref(v_h2_4491_);
lean_dec_ref(v_motive_4489_);
v___x_4559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4559_, 0, v_h1_4490_);
return v___x_4559_;
}
v___jp_4497_:
{
lean_object* v___x_4502_; lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4502_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4503_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4504_ = l_Lean_indentExpr(v_motive_4489_);
v___x_4505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4505_, 0, v___x_4503_);
lean_ctor_set(v___x_4505_, 1, v___x_4504_);
v___x_4506_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4502_, v___x_4505_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
return v___x_4506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4560_, lean_object* v_h1_4561_, lean_object* v_h2_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_){
_start:
{
lean_object* v_res_4568_; 
v_res_4568_ = l_Lean_Meta_mkEqNDRec(v_motive_4560_, v_h1_4561_, v_h2_4562_, v_a_4563_, v_a_4564_, v_a_4565_, v_a_4566_);
lean_dec(v_a_4566_);
lean_dec_ref(v_a_4565_);
lean_dec(v_a_4564_);
lean_dec_ref(v_a_4563_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4573_, lean_object* v_h1_4574_, lean_object* v_h2_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_){
_start:
{
lean_object* v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___x_4591_; uint8_t v___x_4592_; 
v___x_4591_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4592_ = l_Lean_Expr_isAppOf(v_h2_4575_, v___x_4591_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; 
lean_inc_ref(v_h2_4575_);
v___x_4593_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; uint8_t v___x_4597_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref_known(v___x_4593_, 1);
v___x_4595_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4596_ = lean_unsigned_to_nat(3u);
v___x_4597_ = l_Lean_Expr_isAppOfArity(v_a_4594_, v___x_4595_, v___x_4596_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; 
lean_dec(v_a_4594_);
lean_dec_ref(v_h1_4574_);
lean_dec_ref(v_motive_4573_);
v___x_4598_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4599_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4600_ = l_Lean_indentExpr(v_h2_4575_);
v___x_4601_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4599_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
v___x_4602_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4598_, v___x_4601_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
return v___x_4602_;
}
else
{
lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; 
v___x_4603_ = l_Lean_Expr_appFn_x21(v_a_4594_);
v___x_4604_ = l_Lean_Expr_appFn_x21(v___x_4603_);
v___x_4605_ = l_Lean_Expr_appArg_x21(v___x_4604_);
lean_dec_ref(v___x_4604_);
v___x_4606_ = l_Lean_Expr_appArg_x21(v___x_4603_);
lean_dec_ref(v___x_4603_);
v___x_4607_ = l_Lean_Expr_appArg_x21(v_a_4594_);
lean_dec(v_a_4594_);
lean_inc_ref(v___x_4605_);
v___x_4608_ = l_Lean_Meta_getLevel(v___x_4605_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; lean_object* v___x_4610_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v___x_4608_, 1);
lean_inc_ref(v_motive_4573_);
v___x_4610_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4573_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4635_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4635_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4635_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
if (lean_obj_tag(v_a_4611_) == 7)
{
lean_object* v_body_4615_; 
v_body_4615_ = lean_ctor_get(v_a_4611_, 2);
lean_inc_ref(v_body_4615_);
lean_dec_ref_known(v_a_4611_, 3);
if (lean_obj_tag(v_body_4615_) == 7)
{
lean_object* v_body_4616_; 
v_body_4616_ = lean_ctor_get(v_body_4615_, 2);
lean_inc_ref(v_body_4616_);
lean_dec_ref_known(v_body_4615_, 3);
if (lean_obj_tag(v_body_4616_) == 3)
{
lean_object* v_u_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4633_; 
v_u_4617_ = lean_ctor_get(v_body_4616_, 0);
lean_inc(v_u_4617_);
lean_dec_ref_known(v_body_4616_, 1);
v___x_4618_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4619_ = lean_box(0);
v___x_4620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4620_, 0, v_a_4609_);
lean_ctor_set(v___x_4620_, 1, v___x_4619_);
v___x_4621_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4621_, 0, v_u_4617_);
lean_ctor_set(v___x_4621_, 1, v___x_4620_);
v___x_4622_ = l_Lean_mkConst(v___x_4618_, v___x_4621_);
v___x_4623_ = lean_unsigned_to_nat(6u);
v___x_4624_ = lean_mk_empty_array_with_capacity(v___x_4623_);
v___x_4625_ = lean_array_push(v___x_4624_, v___x_4605_);
v___x_4626_ = lean_array_push(v___x_4625_, v___x_4606_);
v___x_4627_ = lean_array_push(v___x_4626_, v_motive_4573_);
v___x_4628_ = lean_array_push(v___x_4627_, v_h1_4574_);
v___x_4629_ = lean_array_push(v___x_4628_, v___x_4607_);
v___x_4630_ = lean_array_push(v___x_4629_, v_h2_4575_);
v___x_4631_ = l_Lean_mkAppN(v___x_4622_, v___x_4630_);
lean_dec_ref(v___x_4630_);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4631_);
v___x_4633_ = v___x_4613_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
else
{
lean_dec_ref(v_body_4616_);
lean_del_object(v___x_4613_);
lean_dec(v_a_4609_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v_h2_4575_);
lean_dec_ref(v_h1_4574_);
v___y_4582_ = v_a_4576_;
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
v___y_4585_ = v_a_4579_;
goto v___jp_4581_;
}
}
else
{
lean_dec_ref(v_body_4615_);
lean_del_object(v___x_4613_);
lean_dec(v_a_4609_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v_h2_4575_);
lean_dec_ref(v_h1_4574_);
v___y_4582_ = v_a_4576_;
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
v___y_4585_ = v_a_4579_;
goto v___jp_4581_;
}
}
else
{
lean_del_object(v___x_4613_);
lean_dec(v_a_4611_);
lean_dec(v_a_4609_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v_h2_4575_);
lean_dec_ref(v_h1_4574_);
v___y_4582_ = v_a_4576_;
v___y_4583_ = v_a_4577_;
v___y_4584_ = v_a_4578_;
v___y_4585_ = v_a_4579_;
goto v___jp_4581_;
}
}
}
else
{
lean_dec(v_a_4609_);
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v_h2_4575_);
lean_dec_ref(v_h1_4574_);
lean_dec_ref(v_motive_4573_);
return v___x_4610_;
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec_ref(v___x_4607_);
lean_dec_ref(v___x_4606_);
lean_dec_ref(v___x_4605_);
lean_dec_ref(v_h2_4575_);
lean_dec_ref(v_h1_4574_);
lean_dec_ref(v_motive_4573_);
v_a_4636_ = lean_ctor_get(v___x_4608_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4608_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4608_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4608_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4575_);
lean_dec_ref(v_h1_4574_);
lean_dec_ref(v_motive_4573_);
return v___x_4593_;
}
}
else
{
lean_object* v___x_4644_; 
lean_dec_ref(v_h2_4575_);
lean_dec_ref(v_motive_4573_);
v___x_4644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4644_, 0, v_h1_4574_);
return v___x_4644_;
}
v___jp_4581_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; 
v___x_4586_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4587_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4588_ = l_Lean_indentExpr(v_motive_4573_);
v___x_4589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4587_);
lean_ctor_set(v___x_4589_, 1, v___x_4588_);
v___x_4590_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4586_, v___x_4589_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
return v___x_4590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4645_, lean_object* v_h1_4646_, lean_object* v_h2_4647_, lean_object* v_a_4648_, lean_object* v_a_4649_, lean_object* v_a_4650_, lean_object* v_a_4651_, lean_object* v_a_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_Meta_mkEqRec(v_motive_4645_, v_h1_4646_, v_h2_4647_, v_a_4648_, v_a_4649_, v_a_4650_, v_a_4651_);
lean_dec(v_a_4651_);
lean_dec_ref(v_a_4650_);
lean_dec(v_a_4649_);
lean_dec_ref(v_a_4648_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore(lean_object* v_00_u03b1_4658_, lean_object* v_00_u03b2_4659_, lean_object* v_h_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_, lean_object* v_a_4664_, lean_object* v_a_4665_){
_start:
{
lean_object* v___x_4667_; 
lean_inc_ref(v_00_u03b1_4658_);
v___x_4667_ = l_Lean_Meta_getLevel(v_00_u03b1_4658_, v_a_4662_, v_a_4663_, v_a_4664_, v_a_4665_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4680_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4680_ == 0)
{
v___x_4670_ = v___x_4667_;
v_isShared_4671_ = v_isSharedCheck_4680_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4667_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4680_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4672_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4673_ = lean_box(0);
v___x_4674_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4674_, 0, v_a_4668_);
lean_ctor_set(v___x_4674_, 1, v___x_4673_);
v___x_4675_ = l_Lean_mkConst(v___x_4672_, v___x_4674_);
v___x_4676_ = l_Lean_mkApp4(v___x_4675_, v_00_u03b1_4658_, v_00_u03b2_4659_, v_h_4660_, v_a_4661_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v___x_4676_);
v___x_4678_ = v___x_4670_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
else
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4688_; 
lean_dec_ref(v_a_4661_);
lean_dec_ref(v_h_4660_);
lean_dec_ref(v_00_u03b2_4659_);
lean_dec_ref(v_00_u03b1_4658_);
v_a_4681_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4683_ = v___x_4667_;
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4667_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4688_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v___x_4686_; 
if (v_isShared_4684_ == 0)
{
v___x_4686_ = v___x_4683_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v_a_4681_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore___boxed(lean_object* v_00_u03b1_4689_, lean_object* v_00_u03b2_4690_, lean_object* v_h_4691_, lean_object* v_a_4692_, lean_object* v_a_4693_, lean_object* v_a_4694_, lean_object* v_a_4695_, lean_object* v_a_4696_, lean_object* v_a_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l_Lean_Meta_mkEqMPCore(v_00_u03b1_4689_, v_00_u03b2_4690_, v_h_4691_, v_a_4692_, v_a_4693_, v_a_4694_, v_a_4695_, v_a_4696_);
lean_dec(v_a_4696_);
lean_dec_ref(v_a_4695_);
lean_dec(v_a_4694_);
lean_dec_ref(v_a_4693_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4699_, lean_object* v_pr_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_, lean_object* v_a_4704_){
_start:
{
lean_object* v___x_4706_; 
lean_inc_ref(v_eqProof_4699_);
v___x_4706_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_eqProof_4699_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
if (lean_obj_tag(v___x_4706_) == 0)
{
lean_object* v_a_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; uint8_t v___x_4710_; 
v_a_4707_ = lean_ctor_get(v___x_4706_, 0);
lean_inc(v_a_4707_);
lean_dec_ref_known(v___x_4706_, 1);
v___x_4708_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4709_ = lean_unsigned_to_nat(3u);
v___x_4710_ = l_Lean_Expr_isAppOfArity(v_a_4707_, v___x_4708_, v___x_4709_);
if (v___x_4710_ == 0)
{
lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; 
lean_dec_ref(v_pr_4700_);
v___x_4711_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4712_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4713_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_eqProof_4699_, v_a_4707_);
v___x_4714_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4714_, 0, v___x_4712_);
lean_ctor_set(v___x_4714_, 1, v___x_4713_);
v___x_4715_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4711_, v___x_4714_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
return v___x_4715_;
}
else
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4716_ = l_Lean_Expr_appFn_x21(v_a_4707_);
v___x_4717_ = l_Lean_Expr_appArg_x21(v___x_4716_);
lean_dec_ref(v___x_4716_);
v___x_4718_ = l_Lean_Expr_appArg_x21(v_a_4707_);
lean_dec(v_a_4707_);
v___x_4719_ = l_Lean_Meta_mkEqMPCore(v___x_4717_, v___x_4718_, v_eqProof_4699_, v_pr_4700_, v_a_4701_, v_a_4702_, v_a_4703_, v_a_4704_);
return v___x_4719_;
}
}
else
{
lean_dec_ref(v_pr_4700_);
lean_dec_ref(v_eqProof_4699_);
return v___x_4706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4720_, lean_object* v_pr_4721_, lean_object* v_a_4722_, lean_object* v_a_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_){
_start:
{
lean_object* v_res_4727_; 
v_res_4727_ = l_Lean_Meta_mkEqMP(v_eqProof_4720_, v_pr_4721_, v_a_4722_, v_a_4723_, v_a_4724_, v_a_4725_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
lean_dec(v_a_4723_);
lean_dec_ref(v_a_4722_);
return v_res_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4732_, lean_object* v_pr_4733_, lean_object* v_a_4734_, lean_object* v_a_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_){
_start:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; 
v___x_4739_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4740_ = lean_unsigned_to_nat(2u);
v___x_4741_ = lean_mk_empty_array_with_capacity(v___x_4740_);
v___x_4742_ = lean_array_push(v___x_4741_, v_eqProof_4732_);
v___x_4743_ = lean_array_push(v___x_4742_, v_pr_4733_);
v___x_4744_ = l_Lean_Meta_mkAppM(v___x_4739_, v___x_4743_, v_a_4734_, v_a_4735_, v_a_4736_, v_a_4737_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4745_, lean_object* v_pr_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_){
_start:
{
lean_object* v_res_4752_; 
v_res_4752_ = l_Lean_Meta_mkEqMPR(v_eqProof_4745_, v_pr_4746_, v_a_4747_, v_a_4748_, v_a_4749_, v_a_4750_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
lean_dec(v_a_4748_);
lean_dec_ref(v_a_4747_);
return v_res_4752_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v___f_4759_; lean_object* v___x_12329__overap_4760_; lean_object* v___x_4761_; 
v___f_4759_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12329__overap_4760_ = lean_panic_fn_borrowed(v___f_4759_, v_msg_4753_);
lean_inc(v___y_4757_);
lean_inc_ref(v___y_4756_);
lean_inc(v___y_4755_);
lean_inc_ref(v___y_4754_);
v___x_4761_ = lean_apply_5(v___x_12329__overap_4760_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, lean_box(0));
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_){
_start:
{
lean_object* v_res_4768_; 
v_res_4768_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4762_, v___y_4763_, v___y_4764_, v___y_4765_, v___y_4766_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
lean_dec(v___y_4764_);
lean_dec_ref(v___y_4763_);
return v_res_4768_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4769_, uint8_t v_skipRealize_4770_, lean_object* v___y_4771_){
_start:
{
lean_object* v___x_4773_; lean_object* v_env_4774_; uint8_t v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4773_ = lean_st_ref_get(v___y_4771_);
v_env_4774_ = lean_ctor_get(v___x_4773_, 0);
lean_inc_ref(v_env_4774_);
lean_dec(v___x_4773_);
v___x_4775_ = l_Lean_Environment_contains(v_env_4774_, v_constName_4769_, v_skipRealize_4770_);
v___x_4776_ = lean_box(v___x_4775_);
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
return v___x_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4778_, lean_object* v_skipRealize_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
uint8_t v_skipRealize_boxed_4782_; lean_object* v_res_4783_; 
v_skipRealize_boxed_4782_ = lean_unbox(v_skipRealize_4779_);
v_res_4783_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4778_, v_skipRealize_boxed_4782_, v___y_4780_);
lean_dec(v___y_4780_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4784_, uint8_t v_skipRealize_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
lean_object* v___x_4791_; 
v___x_4791_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4784_, v_skipRealize_4785_, v___y_4789_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4792_, lean_object* v_skipRealize_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
uint8_t v_skipRealize_boxed_4799_; lean_object* v_res_4800_; 
v_skipRealize_boxed_4799_ = lean_unbox(v_skipRealize_4793_);
v_res_4800_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4792_, v_skipRealize_boxed_4799_, v___y_4794_, v___y_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___x_4801_, uint8_t v___x_4802_, lean_object* v_P_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; lean_object* v___x_4813_; 
v___x_4809_ = lean_unsigned_to_nat(1u);
v___x_4810_ = lean_mk_empty_array_with_capacity(v___x_4809_);
lean_inc_ref(v_P_4803_);
v___x_4811_ = lean_array_push(v___x_4810_, v_P_4803_);
v___x_4812_ = 1;
v___x_4813_ = l_Lean_Meta_mkLambdaFVars(v___x_4811_, v_P_4803_, v___x_4801_, v___x_4802_, v___x_4801_, v___x_4802_, v___x_4812_, v___y_4804_, v___y_4805_, v___y_4806_, v___y_4807_);
lean_dec_ref(v___x_4811_);
return v___x_4813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___x_4814_, lean_object* v___x_4815_, lean_object* v_P_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
uint8_t v___x_13769__boxed_4822_; uint8_t v___x_13770__boxed_4823_; lean_object* v_res_4824_; 
v___x_13769__boxed_4822_ = lean_unbox(v___x_4814_);
v___x_13770__boxed_4823_ = lean_unbox(v___x_4815_);
v_res_4824_ = l_Lean_Meta_mkNoConfusion___lam__0(v___x_13769__boxed_4822_, v___x_13770__boxed_4823_, v_P_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
return v_res_4824_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; 
v___x_4826_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4827_ = l_Lean_stringToMessageData(v___x_4826_);
return v___x_4827_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; 
v___x_4829_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4830_ = l_Lean_stringToMessageData(v___x_4829_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4831_, lean_object* v_b_4832_, lean_object* v_i_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_){
_start:
{
lean_object* v_stop_4839_; lean_object* v_step_4840_; lean_object* v_a_4842_; uint8_t v___x_4845_; 
v_stop_4839_ = lean_ctor_get(v_range_4831_, 1);
v_step_4840_ = lean_ctor_get(v_range_4831_, 2);
v___x_4845_ = lean_nat_dec_lt(v_i_4833_, v_stop_4839_);
if (v___x_4845_ == 0)
{
lean_object* v___x_4846_; 
lean_dec(v_i_4833_);
v___x_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4846_, 0, v_b_4832_);
return v___x_4846_;
}
else
{
lean_object* v___x_4847_; 
lean_inc(v___y_4837_);
lean_inc_ref(v___y_4836_);
lean_inc(v___y_4835_);
lean_inc_ref(v___y_4834_);
lean_inc_ref(v_b_4832_);
v___x_4847_ = lean_infer_type(v_b_4832_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v_a_4848_; lean_object* v___x_4849_; 
v_a_4848_ = lean_ctor_get(v___x_4847_, 0);
lean_inc(v_a_4848_);
lean_dec_ref_known(v___x_4847_, 1);
v___x_4849_ = l_Lean_Meta_whnfForall(v_a_4848_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref_known(v___x_4849_, 1);
v___x_4851_ = l_Lean_Expr_bindingDomain_x21(v_a_4850_);
lean_dec(v_a_4850_);
lean_inc(v___y_4837_);
lean_inc_ref(v___y_4836_);
lean_inc(v___y_4835_);
lean_inc_ref(v___y_4834_);
v___x_4852_ = lean_whnf(v___x_4851_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
if (lean_obj_tag(v___x_4852_) == 0)
{
lean_object* v_a_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; uint8_t v___x_4856_; 
v_a_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc(v_a_4853_);
lean_dec_ref_known(v___x_4852_, 1);
v___x_4854_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4855_ = lean_unsigned_to_nat(4u);
v___x_4856_ = l_Lean_Expr_isAppOfArity(v_a_4853_, v___x_4854_, v___x_4855_);
if (v___x_4856_ == 0)
{
lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v___x_4859_; 
v___x_4857_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4858_ = lean_unsigned_to_nat(3u);
v___x_4859_ = l_Lean_Expr_isAppOfArity(v_a_4853_, v___x_4857_, v___x_4858_);
if (v___x_4859_ == 0)
{
lean_object* v___x_4860_; 
lean_dec(v_i_4833_);
lean_inc(v___y_4837_);
lean_inc_ref(v___y_4836_);
lean_inc(v___y_4835_);
lean_inc_ref(v___y_4834_);
v___x_4860_ = lean_infer_type(v_b_4832_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4878_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v___x_4862_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4863_ = l_Lean_MessageData_ofExpr(v_a_4853_);
v___x_4864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set(v___x_4864_, 1, v___x_4863_);
v___x_4865_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4864_);
lean_ctor_set(v___x_4866_, 1, v___x_4865_);
v___x_4867_ = lean_unsigned_to_nat(30u);
v___x_4868_ = l_Lean_inlineExpr(v_a_4861_, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4866_);
lean_ctor_set(v___x_4869_, 1, v___x_4868_);
v___x_4870_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4869_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4878_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4876_; 
if (v_isShared_4874_ == 0)
{
v___x_4876_ = v___x_4873_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4877_; 
v_reuseFailAlloc_4877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4877_, 0, v_a_4871_);
v___x_4876_ = v_reuseFailAlloc_4877_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
return v___x_4876_;
}
}
}
else
{
lean_dec(v_a_4853_);
return v___x_4860_;
}
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v___x_4879_ = l_Lean_Expr_appFn_x21(v_a_4853_);
lean_dec(v_a_4853_);
v___x_4880_ = l_Lean_Expr_appArg_x21(v___x_4879_);
lean_dec_ref(v___x_4879_);
v___x_4881_ = l_Lean_Meta_mkEqRefl(v___x_4880_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v_a_4882_; lean_object* v___x_4883_; 
v_a_4882_ = lean_ctor_get(v___x_4881_, 0);
lean_inc(v_a_4882_);
lean_dec_ref_known(v___x_4881_, 1);
v___x_4883_ = l_Lean_Expr_app___override(v_b_4832_, v_a_4882_);
v_a_4842_ = v___x_4883_;
goto v___jp_4841_;
}
else
{
lean_dec(v_i_4833_);
lean_dec_ref(v_b_4832_);
return v___x_4881_;
}
}
}
else
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; 
v___x_4884_ = l_Lean_Expr_appFn_x21(v_a_4853_);
lean_dec(v_a_4853_);
v___x_4885_ = l_Lean_Expr_appFn_x21(v___x_4884_);
lean_dec_ref(v___x_4884_);
v___x_4886_ = l_Lean_Expr_appArg_x21(v___x_4885_);
lean_dec_ref(v___x_4885_);
v___x_4887_ = l_Lean_Meta_mkHEqRefl(v___x_4886_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
if (lean_obj_tag(v___x_4887_) == 0)
{
lean_object* v_a_4888_; lean_object* v___x_4889_; 
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
lean_inc(v_a_4888_);
lean_dec_ref_known(v___x_4887_, 1);
v___x_4889_ = l_Lean_Expr_app___override(v_b_4832_, v_a_4888_);
v_a_4842_ = v___x_4889_;
goto v___jp_4841_;
}
else
{
lean_dec(v_i_4833_);
lean_dec_ref(v_b_4832_);
return v___x_4887_;
}
}
}
else
{
lean_dec(v_i_4833_);
lean_dec_ref(v_b_4832_);
return v___x_4852_;
}
}
else
{
lean_dec(v_i_4833_);
lean_dec_ref(v_b_4832_);
return v___x_4849_;
}
}
else
{
lean_dec(v_i_4833_);
lean_dec_ref(v_b_4832_);
return v___x_4847_;
}
}
v___jp_4841_:
{
lean_object* v___x_4843_; 
v___x_4843_ = lean_nat_add(v_i_4833_, v_step_4840_);
lean_dec(v_i_4833_);
v_b_4832_ = v_a_4842_;
v_i_4833_ = v___x_4843_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4890_, lean_object* v_b_4891_, lean_object* v_i_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4890_, v_b_4891_, v_i_4892_, v___y_4893_, v___y_4894_, v___y_4895_, v___y_4896_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
lean_dec_ref(v_range_4890_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4899_, lean_object* v_b_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_){
_start:
{
lean_object* v___x_4906_; 
lean_inc(v___y_4904_);
lean_inc_ref(v___y_4903_);
lean_inc(v___y_4902_);
lean_inc_ref(v___y_4901_);
v___x_4906_ = lean_apply_6(v_k_4899_, v_b_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_, lean_box(0));
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4907_, lean_object* v_b_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4907_, v_b_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
lean_dec(v___y_4910_);
lean_dec_ref(v___y_4909_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4915_, uint8_t v_bi_4916_, lean_object* v_type_4917_, lean_object* v_k_4918_, uint8_t v_kind_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_){
_start:
{
lean_object* v___f_4925_; lean_object* v___x_4926_; 
v___f_4925_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4925_, 0, v_k_4918_);
v___x_4926_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4915_, v_bi_4916_, v_type_4917_, v___f_4925_, v_kind_4919_, v___y_4920_, v___y_4921_, v___y_4922_, v___y_4923_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4934_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4934_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4934_ == 0)
{
v___x_4929_ = v___x_4926_;
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_a_4927_);
lean_dec(v___x_4926_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4934_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4932_; 
if (v_isShared_4930_ == 0)
{
v___x_4932_ = v___x_4929_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4933_; 
v_reuseFailAlloc_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4933_, 0, v_a_4927_);
v___x_4932_ = v_reuseFailAlloc_4933_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
return v___x_4932_;
}
}
}
else
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
v_a_4935_ = lean_ctor_get(v___x_4926_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4926_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4926_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4926_);
v___x_4937_ = lean_box(0);
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
v_resetjp_4936_:
{
lean_object* v___x_4940_; 
if (v_isShared_4938_ == 0)
{
v___x_4940_ = v___x_4937_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v_a_4935_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_4943_, lean_object* v_bi_4944_, lean_object* v_type_4945_, lean_object* v_k_4946_, lean_object* v_kind_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
uint8_t v_bi_boxed_4953_; uint8_t v_kind_boxed_4954_; lean_object* v_res_4955_; 
v_bi_boxed_4953_ = lean_unbox(v_bi_4944_);
v_kind_boxed_4954_ = lean_unbox(v_kind_4947_);
v_res_4955_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4943_, v_bi_boxed_4953_, v_type_4945_, v_k_4946_, v_kind_boxed_4954_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
return v_res_4955_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_4956_, lean_object* v_type_4957_, lean_object* v_k_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
uint8_t v___x_4964_; uint8_t v___x_4965_; lean_object* v___x_4966_; 
v___x_4964_ = 0;
v___x_4965_ = 0;
v___x_4966_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4956_, v___x_4964_, v_type_4957_, v_k_4958_, v___x_4965_, v___y_4959_, v___y_4960_, v___y_4961_, v___y_4962_);
return v___x_4966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_4967_, lean_object* v_type_4968_, lean_object* v_k_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
lean_object* v_res_4975_; 
v_res_4975_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_4967_, v_type_4968_, v_k_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
return v_res_4975_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4982_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_4983_ = l_Lean_MessageData_ofFormat(v___x_4982_);
return v___x_4983_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6(void){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; 
v___x_4985_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__5));
v___x_4986_ = l_Lean_stringToMessageData(v___x_4985_);
return v___x_4986_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8(void){
_start:
{
lean_object* v___x_4988_; lean_object* v___x_4989_; 
v___x_4988_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__7));
v___x_4989_ = l_Lean_stringToMessageData(v___x_4988_);
return v___x_4989_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4993_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_4994_ = l_Lean_MessageData_ofFormat(v___x_4993_);
return v___x_4994_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5000_; lean_object* v___x_5001_; 
v___x_5000_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5001_ = l_Lean_stringToMessageData(v___x_5000_);
return v___x_5001_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__18(void){
_start:
{
lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_5003_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__17));
v___x_5004_ = l_Lean_stringToMessageData(v___x_5003_);
return v___x_5004_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__19(void){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5005_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__14));
v___x_5006_ = l_Lean_MessageData_ofName(v___x_5005_);
return v___x_5006_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__22(void){
_start:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; 
v___x_5009_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5010_ = lean_unsigned_to_nat(10u);
v___x_5011_ = lean_unsigned_to_nat(511u);
v___x_5012_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__20));
v___x_5013_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5014_ = l_mkPanicMessageWithDecl(v___x_5013_, v___x_5012_, v___x_5011_, v___x_5010_, v___x_5009_);
return v___x_5014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5018_, lean_object* v_h_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_){
_start:
{
lean_object* v___x_5025_; 
lean_inc(v_a_5023_);
lean_inc_ref(v_a_5022_);
lean_inc(v_a_5021_);
lean_inc_ref(v_a_5020_);
lean_inc_ref(v_h_5019_);
v___x_5025_ = lean_infer_type(v_h_5019_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5025_) == 0)
{
lean_object* v_a_5026_; lean_object* v___x_5027_; 
v_a_5026_ = lean_ctor_get(v___x_5025_, 0);
lean_inc(v_a_5026_);
lean_dec_ref_known(v___x_5025_, 1);
lean_inc(v_a_5023_);
lean_inc_ref(v_a_5022_);
lean_inc(v_a_5021_);
lean_inc_ref(v_a_5020_);
v___x_5027_ = lean_whnf(v_a_5026_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; uint8_t v___x_5031_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref_known(v___x_5027_, 1);
v___x_5029_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5030_ = lean_unsigned_to_nat(3u);
v___x_5031_ = l_Lean_Expr_isAppOfArity(v_a_5028_, v___x_5029_, v___x_5030_);
if (v___x_5031_ == 0)
{
lean_object* v___x_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; 
lean_dec_ref(v_target_5018_);
v___x_5032_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5033_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5034_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5019_, v_a_5028_);
v___x_5035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5035_, 0, v___x_5033_);
lean_ctor_set(v___x_5035_, 1, v___x_5034_);
v___x_5036_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5032_, v___x_5035_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
return v___x_5036_;
}
else
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___y_5043_; lean_object* v___y_5044_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___x_5055_; 
v___x_5037_ = l_Lean_Expr_appFn_x21(v_a_5028_);
v___x_5038_ = l_Lean_Expr_appFn_x21(v___x_5037_);
v___x_5039_ = l_Lean_Expr_appArg_x21(v___x_5038_);
lean_dec_ref(v___x_5038_);
v___x_5040_ = l_Lean_Expr_appArg_x21(v___x_5037_);
lean_dec_ref(v___x_5037_);
v___x_5041_ = l_Lean_Expr_appArg_x21(v_a_5028_);
lean_dec(v_a_5028_);
v___x_5055_ = l_Lean_Meta_whnfD(v___x_5039_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5055_) == 0)
{
lean_object* v_a_5056_; lean_object* v___y_5058_; lean_object* v___y_5059_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___x_5067_; 
v_a_5056_ = lean_ctor_get(v___x_5055_, 0);
lean_inc(v_a_5056_);
lean_dec_ref_known(v___x_5055_, 1);
v___x_5067_ = l_Lean_Expr_getAppFn(v_a_5056_);
if (lean_obj_tag(v___x_5067_) == 4)
{
lean_object* v_declName_5068_; lean_object* v_us_5069_; lean_object* v___x_5070_; lean_object* v_env_5071_; uint8_t v___x_5072_; lean_object* v___x_5073_; 
v_declName_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc(v_declName_5068_);
v_us_5069_ = lean_ctor_get(v___x_5067_, 1);
lean_inc(v_us_5069_);
lean_dec_ref_known(v___x_5067_, 2);
v___x_5070_ = lean_st_ref_get(v_a_5023_);
v_env_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc_ref(v_env_5071_);
lean_dec(v___x_5070_);
v___x_5072_ = 0;
v___x_5073_ = l_Lean_Environment_find_x3f(v_env_5071_, v_declName_5068_, v___x_5072_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_dec(v_us_5069_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v___y_5058_ = v_a_5020_;
v___y_5059_ = v_a_5021_;
v___y_5060_ = v_a_5022_;
v___y_5061_ = v_a_5023_;
goto v___jp_5057_;
}
else
{
lean_object* v_val_5074_; 
v_val_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc(v_val_5074_);
lean_dec_ref_known(v___x_5073_, 1);
if (lean_obj_tag(v_val_5074_) == 5)
{
lean_object* v_val_5075_; lean_object* v___x_5076_; 
v_val_5075_ = lean_ctor_get(v_val_5074_, 0);
lean_inc_ref(v_val_5075_);
lean_dec_ref_known(v_val_5074_, 1);
lean_inc_ref(v_target_5018_);
v___x_5076_ = l_Lean_Meta_getLevel(v_target_5018_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5078_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___x_5076_, 1);
lean_inc_ref(v___x_5040_);
v___x_5078_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5040_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_a_5079_; 
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
lean_inc(v_a_5079_);
lean_dec_ref_known(v___x_5078_, 1);
if (lean_obj_tag(v_a_5079_) == 1)
{
lean_object* v_val_5080_; lean_object* v_fst_5081_; lean_object* v_snd_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5296_; 
v_val_5080_ = lean_ctor_get(v_a_5079_, 0);
lean_inc(v_val_5080_);
lean_dec_ref_known(v_a_5079_, 1);
v_fst_5081_ = lean_ctor_get(v_val_5080_, 0);
v_snd_5082_ = lean_ctor_get(v_val_5080_, 1);
v_isSharedCheck_5296_ = !lean_is_exclusive(v_val_5080_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5084_ = v_val_5080_;
v_isShared_5085_ = v_isSharedCheck_5296_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_snd_5082_);
lean_inc(v_fst_5081_);
lean_dec(v_val_5080_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5296_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5086_; 
lean_inc_ref(v___x_5041_);
v___x_5086_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5041_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5086_, 1);
if (lean_obj_tag(v_a_5087_) == 1)
{
lean_object* v_val_5088_; lean_object* v_fst_5089_; lean_object* v_snd_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5287_; 
v_val_5088_ = lean_ctor_get(v_a_5087_, 0);
lean_inc(v_val_5088_);
lean_dec_ref_known(v_a_5087_, 1);
v_fst_5089_ = lean_ctor_get(v_val_5088_, 0);
v_snd_5090_ = lean_ctor_get(v_val_5088_, 1);
v_isSharedCheck_5287_ = !lean_is_exclusive(v_val_5088_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5092_ = v_val_5088_;
v_isShared_5093_ = v_isSharedCheck_5287_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_snd_5090_);
lean_inc(v_fst_5089_);
lean_dec(v_val_5088_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5287_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v_toConstantVal_5094_; lean_object* v_cidx_5095_; lean_object* v_numParams_5096_; lean_object* v_numFields_5097_; lean_object* v_cidx_5098_; uint8_t v___x_5099_; 
v_toConstantVal_5094_ = lean_ctor_get(v_fst_5081_, 0);
lean_inc_ref(v_toConstantVal_5094_);
v_cidx_5095_ = lean_ctor_get(v_fst_5081_, 2);
lean_inc(v_cidx_5095_);
v_numParams_5096_ = lean_ctor_get(v_fst_5081_, 3);
lean_inc(v_numParams_5096_);
v_numFields_5097_ = lean_ctor_get(v_fst_5081_, 4);
lean_inc(v_numFields_5097_);
lean_dec(v_fst_5081_);
v_cidx_5098_ = lean_ctor_get(v_fst_5089_, 2);
lean_inc(v_cidx_5098_);
lean_dec(v_fst_5089_);
v___x_5099_ = lean_nat_dec_eq(v_cidx_5095_, v_cidx_5098_);
lean_dec(v_cidx_5098_);
lean_dec(v_cidx_5095_);
if (v___x_5099_ == 0)
{
lean_object* v_toConstantVal_5100_; lean_object* v_name_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v___x_5104_; lean_object* v_a_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v_a_5108_; uint8_t v___x_5130_; 
lean_dec(v_numFields_5097_);
lean_dec(v_numParams_5096_);
lean_dec_ref(v_toConstantVal_5094_);
lean_dec(v_snd_5090_);
lean_dec(v_snd_5082_);
v_toConstantVal_5100_ = lean_ctor_get(v_val_5075_, 0);
lean_inc_ref(v_toConstantVal_5100_);
lean_dec_ref(v_val_5075_);
v_name_5101_ = lean_ctor_get(v_toConstantVal_5100_, 0);
lean_inc(v_name_5101_);
lean_dec_ref(v_toConstantVal_5100_);
v___x_5102_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5103_ = l_Lean_Name_str___override(v_name_5101_, v___x_5102_);
lean_inc(v___x_5103_);
v___x_5104_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5103_, v___x_5031_, v_a_5023_);
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5105_);
lean_dec_ref(v___x_5104_);
v___x_5106_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__14));
v___x_5107_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5106_, v___x_5031_, v_a_5023_);
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5108_);
lean_dec_ref(v___x_5107_);
v___x_5130_ = lean_unbox(v_a_5105_);
lean_dec(v_a_5105_);
if (v___x_5130_ == 0)
{
lean_dec(v_a_5108_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
goto v___jp_5109_;
}
else
{
uint8_t v___x_5131_; 
v___x_5131_ = lean_unbox(v_a_5108_);
lean_dec(v_a_5108_);
if (v___x_5131_ == 0)
{
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
goto v___jp_5109_;
}
else
{
lean_object* v___x_5132_; lean_object* v_dummy_5133_; lean_object* v_nargs_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
lean_del_object(v___x_5092_);
lean_del_object(v___x_5084_);
v___x_5132_ = l_Lean_mkConst(v___x_5103_, v_us_5069_);
v_dummy_5133_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5134_ = l_Lean_Expr_getAppNumArgs(v_a_5056_);
lean_inc(v_nargs_5134_);
v___x_5135_ = lean_mk_array(v_nargs_5134_, v_dummy_5133_);
v___x_5136_ = lean_unsigned_to_nat(1u);
v___x_5137_ = lean_nat_sub(v_nargs_5134_, v___x_5136_);
lean_dec(v_nargs_5134_);
lean_inc_n(v_a_5056_, 2);
v___x_5138_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5056_, v___x_5135_, v___x_5137_);
v___x_5139_ = l_Lean_mkAppN(v___x_5132_, v___x_5138_);
lean_dec_ref(v___x_5138_);
v___x_5140_ = l_Lean_Meta_getLevel(v_a_5056_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
if (lean_obj_tag(v___x_5140_) == 0)
{
lean_object* v_a_5141_; lean_object* v___x_5143_; uint8_t v_isShared_5144_; uint8_t v_isSharedCheck_5163_; 
v_a_5141_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5143_ = v___x_5140_;
v_isShared_5144_ = v_isSharedCheck_5163_;
goto v_resetjp_5142_;
}
else
{
lean_inc(v_a_5141_);
lean_dec(v___x_5140_);
v___x_5143_ = lean_box(0);
v_isShared_5144_ = v_isSharedCheck_5163_;
goto v_resetjp_5142_;
}
v_resetjp_5142_:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5161_; 
v___x_5145_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5146_ = lean_box(0);
v___x_5147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5147_, 0, v_a_5077_);
lean_ctor_set(v___x_5147_, 1, v___x_5146_);
v___x_5148_ = l_Lean_mkConst(v___x_5145_, v___x_5147_);
v___x_5149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5149_, 0, v_a_5141_);
lean_ctor_set(v___x_5149_, 1, v___x_5146_);
v___x_5150_ = l_Lean_mkConst(v___x_5106_, v___x_5149_);
v___x_5151_ = lean_unsigned_to_nat(5u);
v___x_5152_ = lean_mk_empty_array_with_capacity(v___x_5151_);
v___x_5153_ = lean_array_push(v___x_5152_, v_a_5056_);
v___x_5154_ = lean_array_push(v___x_5153_, v___x_5139_);
v___x_5155_ = lean_array_push(v___x_5154_, v___x_5040_);
v___x_5156_ = lean_array_push(v___x_5155_, v___x_5041_);
v___x_5157_ = lean_array_push(v___x_5156_, v_h_5019_);
v___x_5158_ = l_Lean_mkAppN(v___x_5150_, v___x_5157_);
lean_dec_ref(v___x_5157_);
v___x_5159_ = l_Lean_mkAppB(v___x_5148_, v_target_5018_, v___x_5158_);
if (v_isShared_5144_ == 0)
{
lean_ctor_set(v___x_5143_, 0, v___x_5159_);
v___x_5161_ = v___x_5143_;
goto v_reusejp_5160_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v___x_5159_);
v___x_5161_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5160_;
}
v_reusejp_5160_:
{
return v___x_5161_;
}
}
}
else
{
lean_object* v_a_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5171_; 
lean_dec_ref(v___x_5139_);
lean_dec(v_a_5077_);
lean_dec(v_a_5056_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v_a_5164_ = lean_ctor_get(v___x_5140_, 0);
v_isSharedCheck_5171_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5171_ == 0)
{
v___x_5166_ = v___x_5140_;
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_a_5164_);
lean_dec(v___x_5140_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5171_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v___x_5169_; 
if (v_isShared_5167_ == 0)
{
v___x_5169_ = v___x_5166_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5170_; 
v_reuseFailAlloc_5170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5170_, 0, v_a_5164_);
v___x_5169_ = v_reuseFailAlloc_5170_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
return v___x_5169_;
}
}
}
}
}
v___jp_5109_:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; lean_object* v___x_5113_; 
v___x_5110_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5111_ = l_Lean_MessageData_ofName(v___x_5103_);
if (v_isShared_5093_ == 0)
{
lean_ctor_set_tag(v___x_5092_, 7);
lean_ctor_set(v___x_5092_, 1, v___x_5111_);
lean_ctor_set(v___x_5092_, 0, v___x_5110_);
v___x_5113_ = v___x_5092_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5129_; 
v_reuseFailAlloc_5129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5129_, 0, v___x_5110_);
lean_ctor_set(v_reuseFailAlloc_5129_, 1, v___x_5111_);
v___x_5113_ = v_reuseFailAlloc_5129_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
lean_object* v___x_5114_; lean_object* v___x_5116_; 
v___x_5114_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__18, &l_Lean_Meta_mkNoConfusion___closed__18_once, _init_l_Lean_Meta_mkNoConfusion___closed__18);
if (v_isShared_5085_ == 0)
{
lean_ctor_set_tag(v___x_5084_, 7);
lean_ctor_set(v___x_5084_, 1, v___x_5114_);
lean_ctor_set(v___x_5084_, 0, v___x_5113_);
v___x_5116_ = v___x_5084_;
goto v_reusejp_5115_;
}
else
{
lean_object* v_reuseFailAlloc_5128_; 
v_reuseFailAlloc_5128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5128_, 0, v___x_5113_);
lean_ctor_set(v_reuseFailAlloc_5128_, 1, v___x_5114_);
v___x_5116_ = v_reuseFailAlloc_5128_;
goto v_reusejp_5115_;
}
v_reusejp_5115_:
{
lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v_a_5120_; lean_object* v___x_5122_; uint8_t v_isShared_5123_; uint8_t v_isSharedCheck_5127_; 
v___x_5117_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__19, &l_Lean_Meta_mkNoConfusion___closed__19_once, _init_l_Lean_Meta_mkNoConfusion___closed__19);
v___x_5118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5118_, 0, v___x_5116_);
lean_ctor_set(v___x_5118_, 1, v___x_5117_);
v___x_5119_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5118_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
v_a_5120_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5127_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5127_ == 0)
{
v___x_5122_ = v___x_5119_;
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
else
{
lean_inc(v_a_5120_);
lean_dec(v___x_5119_);
v___x_5122_ = lean_box(0);
v_isShared_5123_ = v_isSharedCheck_5127_;
goto v_resetjp_5121_;
}
v_resetjp_5121_:
{
lean_object* v___x_5125_; 
if (v_isShared_5123_ == 0)
{
v___x_5125_ = v___x_5122_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_a_5120_);
v___x_5125_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
return v___x_5125_;
}
}
}
}
}
}
else
{
lean_object* v___x_5172_; uint8_t v___x_5173_; 
lean_dec_ref(v_val_5075_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
v___x_5172_ = lean_unsigned_to_nat(0u);
v___x_5173_ = lean_nat_dec_eq(v_numFields_5097_, v___x_5172_);
lean_dec(v_numFields_5097_);
if (v___x_5173_ == 0)
{
lean_object* v_name_5174_; lean_object* v___x_5175_; lean_object* v___x_5176_; lean_object* v___y_5178_; lean_object* v___y_5179_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___x_5265_; lean_object* v_a_5266_; uint8_t v___x_5267_; 
v_name_5174_ = lean_ctor_get(v_toConstantVal_5094_, 0);
lean_inc(v_name_5174_);
lean_dec_ref(v_toConstantVal_5094_);
v___x_5175_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5176_ = l_Lean_Name_str___override(v_name_5174_, v___x_5175_);
lean_inc(v___x_5176_);
v___x_5265_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5176_, v___x_5031_, v_a_5023_);
v_a_5266_ = lean_ctor_get(v___x_5265_, 0);
lean_inc(v_a_5266_);
lean_dec_ref(v___x_5265_);
v___x_5267_ = lean_unbox(v_a_5266_);
lean_dec(v_a_5266_);
if (v___x_5267_ == 0)
{
lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5271_; 
lean_dec(v_numParams_5096_);
lean_del_object(v___x_5092_);
lean_dec(v_snd_5090_);
lean_dec(v_snd_5082_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v___x_5268_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5269_ = l_Lean_MessageData_ofName(v___x_5176_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set_tag(v___x_5084_, 7);
lean_ctor_set(v___x_5084_, 1, v___x_5269_);
lean_ctor_set(v___x_5084_, 0, v___x_5268_);
v___x_5271_ = v___x_5084_;
goto v_reusejp_5270_;
}
else
{
lean_object* v_reuseFailAlloc_5281_; 
v_reuseFailAlloc_5281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5281_, 0, v___x_5268_);
lean_ctor_set(v_reuseFailAlloc_5281_, 1, v___x_5269_);
v___x_5271_ = v_reuseFailAlloc_5281_;
goto v_reusejp_5270_;
}
v_reusejp_5270_:
{
lean_object* v___x_5272_; lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5280_; 
v___x_5272_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5271_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
v_a_5273_ = lean_ctor_get(v___x_5272_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5272_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5275_ = v___x_5272_;
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5272_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5280_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5278_; 
if (v_isShared_5276_ == 0)
{
v___x_5278_ = v___x_5275_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v_a_5273_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
}
else
{
lean_del_object(v___x_5084_);
v___y_5178_ = v_a_5020_;
v___y_5179_ = v_a_5021_;
v___y_5180_ = v_a_5022_;
v___y_5181_ = v_a_5023_;
goto v___jp_5177_;
}
v___jp_5177_:
{
lean_object* v___x_5182_; 
lean_inc(v___x_5176_);
v___x_5182_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___x_5176_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; lean_object* v_dummy_5184_; lean_object* v_nargs_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; lean_object* v___x_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v_type_5192_; lean_object* v___x_5194_; uint8_t v_isShared_5195_; uint8_t v_isSharedCheck_5254_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
lean_inc(v_a_5183_);
lean_dec_ref_known(v___x_5182_, 1);
v_dummy_5184_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5185_ = l_Lean_Expr_getAppNumArgs(v_a_5056_);
lean_inc(v_nargs_5185_);
v___x_5186_ = lean_mk_array(v_nargs_5185_, v_dummy_5184_);
v___x_5187_ = lean_unsigned_to_nat(1u);
v___x_5188_ = lean_nat_sub(v_nargs_5185_, v___x_5187_);
lean_dec(v_nargs_5185_);
v___x_5189_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5056_, v___x_5186_, v___x_5188_);
lean_inc(v_numParams_5096_);
v___x_5190_ = l_Array_toSubarray___redArg(v___x_5189_, v___x_5172_, v_numParams_5096_);
v___x_5191_ = lean_array_get_size(v_snd_5082_);
v_type_5192_ = lean_ctor_get(v_a_5183_, 2);
v_isSharedCheck_5254_ = !lean_is_exclusive(v_a_5183_);
if (v_isSharedCheck_5254_ == 0)
{
lean_object* v_unused_5255_; lean_object* v_unused_5256_; 
v_unused_5255_ = lean_ctor_get(v_a_5183_, 1);
lean_dec(v_unused_5255_);
v_unused_5256_ = lean_ctor_get(v_a_5183_, 0);
lean_dec(v_unused_5256_);
v___x_5194_ = v_a_5183_;
v_isShared_5195_ = v_isSharedCheck_5254_;
goto v_resetjp_5193_;
}
else
{
lean_inc(v_type_5192_);
lean_dec(v_a_5183_);
v___x_5194_ = lean_box(0);
v_isShared_5195_ = v_isSharedCheck_5254_;
goto v_resetjp_5193_;
}
v_resetjp_5193_:
{
lean_object* v_start_5196_; lean_object* v_stop_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; uint8_t v___x_5210_; 
v_start_5196_ = lean_ctor_get(v___x_5190_, 1);
v_stop_5197_ = lean_ctor_get(v___x_5190_, 2);
lean_inc(v_numParams_5096_);
v___x_5198_ = l_Array_toSubarray___redArg(v_snd_5082_, v_numParams_5096_, v___x_5191_);
v___x_5199_ = lean_array_get_size(v_snd_5090_);
v___x_5200_ = l_Subarray_copy___redArg(v___x_5198_);
v___x_5201_ = l_Array_toSubarray___redArg(v_snd_5090_, v_numParams_5096_, v___x_5199_);
v___x_5202_ = l_Subarray_copy___redArg(v___x_5201_);
v___x_5203_ = l_Lean_Expr_getNumHeadForalls(v_type_5192_);
lean_dec_ref(v_type_5192_);
v___x_5204_ = lean_nat_sub(v_stop_5197_, v_start_5196_);
v___x_5205_ = lean_array_get_size(v___x_5200_);
v___x_5206_ = lean_nat_add(v___x_5204_, v___x_5205_);
lean_dec(v___x_5204_);
v___x_5207_ = lean_array_get_size(v___x_5202_);
v___x_5208_ = lean_nat_add(v___x_5206_, v___x_5207_);
lean_dec(v___x_5206_);
v___x_5209_ = lean_nat_add(v___x_5208_, v___x_5030_);
lean_dec(v___x_5208_);
v___x_5210_ = lean_nat_dec_le(v___x_5209_, v___x_5203_);
if (v___x_5210_ == 0)
{
lean_object* v___x_5211_; lean_object* v___x_5212_; 
lean_dec(v___x_5209_);
lean_dec(v___x_5203_);
lean_dec_ref(v___x_5202_);
lean_dec_ref(v___x_5200_);
lean_del_object(v___x_5194_);
lean_dec_ref(v___x_5190_);
lean_dec(v___x_5176_);
lean_del_object(v___x_5092_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v___x_5211_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__22, &l_Lean_Meta_mkNoConfusion___closed__22_once, _init_l_Lean_Meta_mkNoConfusion___closed__22);
v___x_5212_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5211_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
return v___x_5212_;
}
else
{
lean_object* v___x_5214_; 
if (v_isShared_5093_ == 0)
{
lean_ctor_set_tag(v___x_5092_, 1);
lean_ctor_set(v___x_5092_, 1, v_us_5069_);
lean_ctor_set(v___x_5092_, 0, v_a_5077_);
v___x_5214_ = v___x_5092_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5077_);
lean_ctor_set(v_reuseFailAlloc_5253_, 1, v_us_5069_);
v___x_5214_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5225_; 
v___x_5215_ = l_Lean_mkConst(v___x_5176_, v___x_5214_);
v___x_5216_ = l_Subarray_copy___redArg(v___x_5190_);
v___x_5217_ = l_Lean_mkAppN(v___x_5215_, v___x_5216_);
lean_dec_ref(v___x_5216_);
v___x_5218_ = lean_mk_empty_array_with_capacity(v___x_5187_);
v___x_5219_ = lean_array_push(v___x_5218_, v_target_5018_);
v___x_5220_ = l_Array_append___redArg(v___x_5219_, v___x_5200_);
lean_dec_ref(v___x_5200_);
v___x_5221_ = l_Array_append___redArg(v___x_5220_, v___x_5202_);
lean_dec_ref(v___x_5202_);
v___x_5222_ = l_Lean_mkAppN(v___x_5217_, v___x_5221_);
lean_dec_ref(v___x_5221_);
v___x_5223_ = lean_nat_sub(v___x_5203_, v___x_5209_);
lean_dec(v___x_5209_);
lean_dec(v___x_5203_);
if (v_isShared_5195_ == 0)
{
lean_ctor_set(v___x_5194_, 2, v___x_5187_);
lean_ctor_set(v___x_5194_, 1, v___x_5223_);
lean_ctor_set(v___x_5194_, 0, v___x_5172_);
v___x_5225_ = v___x_5194_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5252_; 
v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5172_);
lean_ctor_set(v_reuseFailAlloc_5252_, 1, v___x_5223_);
lean_ctor_set(v_reuseFailAlloc_5252_, 2, v___x_5187_);
v___x_5225_ = v_reuseFailAlloc_5252_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
lean_object* v___x_5226_; 
v___x_5226_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5225_, v___x_5222_, v___x_5172_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
lean_dec_ref(v___x_5225_);
if (lean_obj_tag(v___x_5226_) == 0)
{
lean_object* v_a_5227_; lean_object* v___x_5228_; 
v_a_5227_ = lean_ctor_get(v___x_5226_, 0);
lean_inc_n(v_a_5227_, 2);
lean_dec_ref_known(v___x_5226_, 1);
lean_inc(v___y_5181_);
lean_inc_ref(v___y_5180_);
lean_inc(v___y_5179_);
lean_inc_ref(v___y_5178_);
v___x_5228_ = lean_infer_type(v_a_5227_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v___x_5230_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref_known(v___x_5228_, 1);
v___x_5230_ = l_Lean_Meta_whnfForall(v_a_5229_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5251_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
v_isSharedCheck_5251_ = !lean_is_exclusive(v___x_5230_);
if (v_isSharedCheck_5251_ == 0)
{
v___x_5233_ = v___x_5230_;
v_isShared_5234_ = v_isSharedCheck_5251_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_a_5231_);
lean_dec(v___x_5230_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5251_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5235_; uint8_t v___x_5236_; 
v___x_5235_ = l_Lean_Expr_bindingDomain_x21(v_a_5231_);
lean_dec(v_a_5231_);
v___x_5236_ = l_Lean_Expr_isHEq(v___x_5235_);
lean_dec_ref(v___x_5235_);
if (v___x_5236_ == 0)
{
lean_object* v___x_5237_; lean_object* v___x_5239_; 
v___x_5237_ = l_Lean_Expr_app___override(v_a_5227_, v_h_5019_);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v___x_5237_);
v___x_5239_ = v___x_5233_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5240_; 
v_reuseFailAlloc_5240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5240_, 0, v___x_5237_);
v___x_5239_ = v_reuseFailAlloc_5240_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
return v___x_5239_;
}
}
else
{
lean_object* v___x_5241_; 
lean_del_object(v___x_5233_);
v___x_5241_ = l_Lean_Meta_mkHEqOfEq(v_h_5019_, v___y_5178_, v___y_5179_, v___y_5180_, v___y_5181_);
if (lean_obj_tag(v___x_5241_) == 0)
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5250_; 
v_a_5242_ = lean_ctor_get(v___x_5241_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5241_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5244_ = v___x_5241_;
v_isShared_5245_ = v_isSharedCheck_5250_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5241_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5250_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5246_; lean_object* v___x_5248_; 
v___x_5246_ = l_Lean_Expr_app___override(v_a_5227_, v_a_5242_);
if (v_isShared_5245_ == 0)
{
lean_ctor_set(v___x_5244_, 0, v___x_5246_);
v___x_5248_ = v___x_5244_;
goto v_reusejp_5247_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v___x_5246_);
v___x_5248_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5247_;
}
v_reusejp_5247_:
{
return v___x_5248_;
}
}
}
else
{
lean_dec(v_a_5227_);
return v___x_5241_;
}
}
}
}
else
{
lean_dec(v_a_5227_);
lean_dec_ref(v_h_5019_);
return v___x_5230_;
}
}
else
{
lean_dec(v_a_5227_);
lean_dec_ref(v_h_5019_);
return v___x_5228_;
}
}
else
{
lean_dec_ref(v_h_5019_);
return v___x_5226_;
}
}
}
}
}
}
else
{
lean_object* v_a_5257_; lean_object* v___x_5259_; uint8_t v_isShared_5260_; uint8_t v_isSharedCheck_5264_; 
lean_dec(v___x_5176_);
lean_dec(v_numParams_5096_);
lean_del_object(v___x_5092_);
lean_dec(v_snd_5090_);
lean_dec(v_snd_5082_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v_a_5257_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5264_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5264_ == 0)
{
v___x_5259_ = v___x_5182_;
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
else
{
lean_inc(v_a_5257_);
lean_dec(v___x_5182_);
v___x_5259_ = lean_box(0);
v_isShared_5260_ = v_isSharedCheck_5264_;
goto v_resetjp_5258_;
}
v_resetjp_5258_:
{
lean_object* v___x_5262_; 
if (v_isShared_5260_ == 0)
{
v___x_5262_ = v___x_5259_;
goto v_reusejp_5261_;
}
else
{
lean_object* v_reuseFailAlloc_5263_; 
v_reuseFailAlloc_5263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5263_, 0, v_a_5257_);
v___x_5262_ = v_reuseFailAlloc_5263_;
goto v_reusejp_5261_;
}
v_reusejp_5261_:
{
return v___x_5262_;
}
}
}
}
}
else
{
lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___f_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; 
lean_dec(v_numParams_5096_);
lean_dec_ref(v_toConstantVal_5094_);
lean_del_object(v___x_5092_);
lean_dec(v_snd_5090_);
lean_del_object(v___x_5084_);
lean_dec(v_snd_5082_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5019_);
v___x_5282_ = lean_box(v___x_5072_);
v___x_5283_ = lean_box(v___x_5173_);
v___f_5284_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5284_, 0, v___x_5282_);
lean_closure_set(v___f_5284_, 1, v___x_5283_);
v___x_5285_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__24));
v___x_5286_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5285_, v_target_5018_, v___f_5284_, v_a_5020_, v_a_5021_, v_a_5022_, v_a_5023_);
return v___x_5286_;
}
}
}
}
else
{
lean_dec(v_a_5087_);
lean_del_object(v___x_5084_);
lean_dec(v_snd_5082_);
lean_dec(v_fst_5081_);
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v___y_5043_ = v_a_5020_;
v___y_5044_ = v_a_5021_;
v___y_5045_ = v_a_5022_;
v___y_5046_ = v_a_5023_;
goto v___jp_5042_;
}
}
else
{
lean_object* v_a_5288_; lean_object* v___x_5290_; uint8_t v_isShared_5291_; uint8_t v_isSharedCheck_5295_; 
lean_del_object(v___x_5084_);
lean_dec(v_snd_5082_);
lean_dec(v_fst_5081_);
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v_a_5288_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5290_ = v___x_5086_;
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
else
{
lean_inc(v_a_5288_);
lean_dec(v___x_5086_);
v___x_5290_ = lean_box(0);
v_isShared_5291_ = v_isSharedCheck_5295_;
goto v_resetjp_5289_;
}
v_resetjp_5289_:
{
lean_object* v___x_5293_; 
if (v_isShared_5291_ == 0)
{
v___x_5293_ = v___x_5290_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v_a_5288_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
}
}
else
{
lean_dec(v_a_5079_);
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v___y_5043_ = v_a_5020_;
v___y_5044_ = v_a_5021_;
v___y_5045_ = v_a_5022_;
v___y_5046_ = v_a_5023_;
goto v___jp_5042_;
}
}
else
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5304_; 
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v_a_5297_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5299_ = v___x_5078_;
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___x_5078_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5302_; 
if (v_isShared_5300_ == 0)
{
v___x_5302_ = v___x_5299_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
return v___x_5302_;
}
}
}
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v_a_5305_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5076_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5076_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
lean_object* v___x_5310_; 
if (v_isShared_5308_ == 0)
{
v___x_5310_ = v___x_5307_;
goto v_reusejp_5309_;
}
else
{
lean_object* v_reuseFailAlloc_5311_; 
v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
v___x_5310_ = v_reuseFailAlloc_5311_;
goto v_reusejp_5309_;
}
v_reusejp_5309_:
{
return v___x_5310_;
}
}
}
}
else
{
lean_dec(v_val_5074_);
lean_dec(v_us_5069_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v___y_5058_ = v_a_5020_;
v___y_5059_ = v_a_5021_;
v___y_5060_ = v_a_5022_;
v___y_5061_ = v_a_5023_;
goto v___jp_5057_;
}
}
}
else
{
lean_dec_ref(v___x_5067_);
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
v___y_5058_ = v_a_5020_;
v___y_5059_ = v_a_5021_;
v___y_5060_ = v_a_5022_;
v___y_5061_ = v_a_5023_;
goto v___jp_5057_;
}
v___jp_5057_:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5062_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5063_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5064_ = l_Lean_indentExpr(v_a_5056_);
v___x_5065_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5065_, 0, v___x_5063_);
lean_ctor_set(v___x_5065_, 1, v___x_5064_);
v___x_5066_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5062_, v___x_5065_, v___y_5058_, v___y_5059_, v___y_5060_, v___y_5061_);
return v___x_5066_;
}
}
else
{
lean_dec_ref(v___x_5041_);
lean_dec_ref(v___x_5040_);
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
return v___x_5055_;
}
v___jp_5042_:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; 
v___x_5047_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__6, &l_Lean_Meta_mkNoConfusion___closed__6_once, _init_l_Lean_Meta_mkNoConfusion___closed__6);
v___x_5048_ = l_Lean_MessageData_ofExpr(v___x_5040_);
v___x_5049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5049_, 0, v___x_5047_);
lean_ctor_set(v___x_5049_, 1, v___x_5048_);
v___x_5050_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__8, &l_Lean_Meta_mkNoConfusion___closed__8_once, _init_l_Lean_Meta_mkNoConfusion___closed__8);
v___x_5051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5051_, 0, v___x_5049_);
lean_ctor_set(v___x_5051_, 1, v___x_5050_);
v___x_5052_ = l_Lean_MessageData_ofExpr(v___x_5041_);
v___x_5053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5053_, 0, v___x_5051_);
lean_ctor_set(v___x_5053_, 1, v___x_5052_);
v___x_5054_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5053_, v___y_5043_, v___y_5044_, v___y_5045_, v___y_5046_);
return v___x_5054_;
}
}
}
else
{
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
return v___x_5027_;
}
}
else
{
lean_dec_ref(v_h_5019_);
lean_dec_ref(v_target_5018_);
return v___x_5025_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5313_, lean_object* v_h_5314_, lean_object* v_a_5315_, lean_object* v_a_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l_Lean_Meta_mkNoConfusion(v_target_5313_, v_h_5314_, v_a_5315_, v_a_5316_, v_a_5317_, v_a_5318_);
lean_dec(v_a_5318_);
lean_dec_ref(v_a_5317_);
lean_dec(v_a_5316_);
lean_dec_ref(v_a_5315_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5321_, lean_object* v_b_5322_, lean_object* v_i_5323_, lean_object* v_hs_5324_, lean_object* v_hl_5325_, lean_object* v___y_5326_, lean_object* v___y_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_){
_start:
{
lean_object* v___x_5331_; 
v___x_5331_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5321_, v_b_5322_, v_i_5323_, v___y_5326_, v___y_5327_, v___y_5328_, v___y_5329_);
return v___x_5331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5332_, lean_object* v_b_5333_, lean_object* v_i_5334_, lean_object* v_hs_5335_, lean_object* v_hl_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_){
_start:
{
lean_object* v_res_5342_; 
v_res_5342_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5332_, v_b_5333_, v_i_5334_, v_hs_5335_, v_hl_5336_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec(v___y_5338_);
lean_dec_ref(v___y_5337_);
lean_dec_ref(v_range_5332_);
return v_res_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5343_, lean_object* v_name_5344_, uint8_t v_bi_5345_, lean_object* v_type_5346_, lean_object* v_k_5347_, uint8_t v_kind_5348_, lean_object* v___y_5349_, lean_object* v___y_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_){
_start:
{
lean_object* v___x_5354_; 
v___x_5354_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5344_, v_bi_5345_, v_type_5346_, v_k_5347_, v_kind_5348_, v___y_5349_, v___y_5350_, v___y_5351_, v___y_5352_);
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5355_, lean_object* v_name_5356_, lean_object* v_bi_5357_, lean_object* v_type_5358_, lean_object* v_k_5359_, lean_object* v_kind_5360_, lean_object* v___y_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_){
_start:
{
uint8_t v_bi_boxed_5366_; uint8_t v_kind_boxed_5367_; lean_object* v_res_5368_; 
v_bi_boxed_5366_ = lean_unbox(v_bi_5357_);
v_kind_boxed_5367_ = lean_unbox(v_kind_5360_);
v_res_5368_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5355_, v_name_5356_, v_bi_boxed_5366_, v_type_5358_, v_k_5359_, v_kind_boxed_5367_, v___y_5361_, v___y_5362_, v___y_5363_, v___y_5364_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
lean_dec(v___y_5362_);
lean_dec_ref(v___y_5361_);
return v_res_5368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5369_, lean_object* v_name_5370_, lean_object* v_type_5371_, lean_object* v_k_5372_, lean_object* v___y_5373_, lean_object* v___y_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v___x_5378_; 
v___x_5378_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5370_, v_type_5371_, v_k_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_);
return v___x_5378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5379_, lean_object* v_name_5380_, lean_object* v_type_5381_, lean_object* v_k_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v_res_5388_; 
v_res_5388_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5379_, v_name_5380_, v_type_5381_, v_k_5382_, v___y_5383_, v___y_5384_, v___y_5385_, v___y_5386_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
lean_dec(v___y_5384_);
lean_dec_ref(v___y_5383_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5394_, lean_object* v_e_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_){
_start:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; 
v___x_5401_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5402_, 0, v_monad_5394_);
v___x_5403_ = lean_box(0);
v___x_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5404_, 0, v_e_5395_);
v___x_5405_ = lean_unsigned_to_nat(4u);
v___x_5406_ = lean_mk_empty_array_with_capacity(v___x_5405_);
v___x_5407_ = lean_array_push(v___x_5406_, v___x_5402_);
v___x_5408_ = lean_array_push(v___x_5407_, v___x_5403_);
v___x_5409_ = lean_array_push(v___x_5408_, v___x_5403_);
v___x_5410_ = lean_array_push(v___x_5409_, v___x_5404_);
v___x_5411_ = l_Lean_Meta_mkAppOptM(v___x_5401_, v___x_5410_, v_a_5396_, v_a_5397_, v_a_5398_, v_a_5399_);
return v___x_5411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5412_, lean_object* v_e_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_){
_start:
{
lean_object* v_res_5419_; 
v_res_5419_ = l_Lean_Meta_mkPure(v_monad_5412_, v_e_5413_, v_a_5414_, v_a_5415_, v_a_5416_, v_a_5417_);
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
lean_dec(v_a_5415_);
lean_dec_ref(v_a_5414_);
return v_res_5419_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5429_; lean_object* v___x_5430_; 
v___x_5429_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5430_ = l_Lean_MessageData_ofFormat(v___x_5429_);
return v___x_5430_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5434_; lean_object* v___x_5435_; 
v___x_5434_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5435_ = l_Lean_MessageData_ofFormat(v___x_5434_);
return v___x_5435_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5439_; lean_object* v___x_5440_; 
v___x_5439_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5440_ = l_Lean_MessageData_ofFormat(v___x_5439_);
return v___x_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5441_, lean_object* v_fieldName_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_){
_start:
{
lean_object* v___x_5448_; 
lean_inc(v_a_5446_);
lean_inc_ref(v_a_5445_);
lean_inc(v_a_5444_);
lean_inc_ref(v_a_5443_);
lean_inc_ref(v_s_5441_);
v___x_5448_ = lean_infer_type(v_s_5441_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5448_) == 0)
{
lean_object* v_a_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5545_; 
v_a_5449_ = lean_ctor_get(v___x_5448_, 0);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5448_);
if (v_isSharedCheck_5545_ == 0)
{
v___x_5451_ = v___x_5448_;
v_isShared_5452_ = v_isSharedCheck_5545_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_a_5449_);
lean_dec(v___x_5448_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5545_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5453_; 
lean_inc(v_a_5446_);
lean_inc_ref(v_a_5445_);
lean_inc(v_a_5444_);
lean_inc_ref(v_a_5443_);
v___x_5453_ = lean_whnf(v_a_5449_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5453_) == 0)
{
lean_object* v_a_5454_; lean_object* v___x_5456_; uint8_t v_isShared_5457_; uint8_t v_isSharedCheck_5544_; 
v_a_5454_ = lean_ctor_get(v___x_5453_, 0);
v_isSharedCheck_5544_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5544_ == 0)
{
v___x_5456_ = v___x_5453_;
v_isShared_5457_ = v_isSharedCheck_5544_;
goto v_resetjp_5455_;
}
else
{
lean_inc(v_a_5454_);
lean_dec(v___x_5453_);
v___x_5456_ = lean_box(0);
v_isShared_5457_ = v_isSharedCheck_5544_;
goto v_resetjp_5455_;
}
v_resetjp_5455_:
{
lean_object* v___y_5459_; lean_object* v___y_5460_; lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___x_5477_; 
v___x_5477_ = l_Lean_Expr_getAppFn(v_a_5454_);
if (lean_obj_tag(v___x_5477_) == 4)
{
lean_object* v_declName_5478_; lean_object* v_us_5479_; lean_object* v___x_5480_; lean_object* v_env_5481_; lean_object* v___y_5483_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; uint8_t v___x_5525_; 
v_declName_5478_ = lean_ctor_get(v___x_5477_, 0);
lean_inc_n(v_declName_5478_, 2);
v_us_5479_ = lean_ctor_get(v___x_5477_, 1);
lean_inc(v_us_5479_);
lean_dec_ref_known(v___x_5477_, 2);
v___x_5480_ = lean_st_ref_get(v_a_5446_);
v_env_5481_ = lean_ctor_get(v___x_5480_, 0);
lean_inc_ref_n(v_env_5481_, 2);
lean_dec(v___x_5480_);
v___x_5525_ = l_Lean_isStructure(v_env_5481_, v_declName_5478_);
if (v___x_5525_ == 0)
{
lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; 
v___x_5526_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5527_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5454_);
lean_inc_ref(v_s_5441_);
v___x_5528_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5441_, v_a_5454_);
v___x_5529_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5529_, 0, v___x_5527_);
lean_ctor_set(v___x_5529_, 1, v___x_5528_);
v___x_5530_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5526_, v___x_5529_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
if (lean_obj_tag(v___x_5530_) == 0)
{
lean_dec_ref_known(v___x_5530_, 1);
v___y_5483_ = v_a_5443_;
v___y_5484_ = v_a_5444_;
v___y_5485_ = v_a_5445_;
v___y_5486_ = v_a_5446_;
goto v___jp_5482_;
}
else
{
lean_object* v_a_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5538_; 
lean_dec_ref(v_env_5481_);
lean_dec(v_us_5479_);
lean_dec(v_declName_5478_);
lean_del_object(v___x_5456_);
lean_dec(v_a_5454_);
lean_del_object(v___x_5451_);
lean_dec(v_fieldName_5442_);
lean_dec_ref(v_s_5441_);
v_a_5531_ = lean_ctor_get(v___x_5530_, 0);
v_isSharedCheck_5538_ = !lean_is_exclusive(v___x_5530_);
if (v_isSharedCheck_5538_ == 0)
{
v___x_5533_ = v___x_5530_;
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_a_5531_);
lean_dec(v___x_5530_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5538_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5536_; 
if (v_isShared_5534_ == 0)
{
v___x_5536_ = v___x_5533_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v_a_5531_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
}
else
{
v___y_5483_ = v_a_5443_;
v___y_5484_ = v_a_5444_;
v___y_5485_ = v_a_5445_;
v___y_5486_ = v_a_5446_;
goto v___jp_5482_;
}
v___jp_5482_:
{
lean_object* v___x_5487_; 
lean_inc(v_fieldName_5442_);
lean_inc(v_declName_5478_);
lean_inc_ref(v_env_5481_);
v___x_5487_ = l_Lean_getProjFnForField_x3f(v_env_5481_, v_declName_5478_, v_fieldName_5442_);
if (lean_obj_tag(v___x_5487_) == 0)
{
lean_object* v___x_5488_; lean_object* v___x_5489_; size_t v_sz_5490_; size_t v___x_5491_; lean_object* v___x_5492_; 
lean_dec(v_us_5479_);
lean_del_object(v___x_5456_);
lean_inc(v_declName_5478_);
lean_inc_ref(v_env_5481_);
v___x_5488_ = l_Lean_getStructureFields(v_env_5481_, v_declName_5478_);
v___x_5489_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5490_ = lean_array_size(v___x_5488_);
v___x_5491_ = ((size_t)0ULL);
lean_inc(v_fieldName_5442_);
lean_inc_ref(v_s_5441_);
v___x_5492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5481_, v_declName_5478_, v_s_5441_, v_fieldName_5442_, v___x_5488_, v_sz_5490_, v___x_5491_, v___x_5489_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_);
lean_dec_ref(v___x_5488_);
if (lean_obj_tag(v___x_5492_) == 0)
{
lean_object* v_a_5493_; lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5503_; 
v_a_5493_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5503_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5503_ == 0)
{
v___x_5495_ = v___x_5492_;
v_isShared_5496_ = v_isSharedCheck_5503_;
goto v_resetjp_5494_;
}
else
{
lean_inc(v_a_5493_);
lean_dec(v___x_5492_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5503_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v_fst_5497_; 
v_fst_5497_ = lean_ctor_get(v_a_5493_, 0);
lean_inc(v_fst_5497_);
lean_dec(v_a_5493_);
if (lean_obj_tag(v_fst_5497_) == 0)
{
lean_del_object(v___x_5495_);
v___y_5459_ = v___y_5483_;
v___y_5460_ = v___y_5485_;
v___y_5461_ = v___y_5486_;
v___y_5462_ = v___y_5484_;
goto v___jp_5458_;
}
else
{
lean_object* v_val_5498_; 
v_val_5498_ = lean_ctor_get(v_fst_5497_, 0);
lean_inc(v_val_5498_);
lean_dec_ref_known(v_fst_5497_, 1);
if (lean_obj_tag(v_val_5498_) == 0)
{
lean_del_object(v___x_5495_);
v___y_5459_ = v___y_5483_;
v___y_5460_ = v___y_5485_;
v___y_5461_ = v___y_5486_;
v___y_5462_ = v___y_5484_;
goto v___jp_5458_;
}
else
{
lean_object* v_val_5499_; lean_object* v___x_5501_; 
lean_dec(v_a_5454_);
lean_del_object(v___x_5451_);
lean_dec(v_fieldName_5442_);
lean_dec_ref(v_s_5441_);
v_val_5499_ = lean_ctor_get(v_val_5498_, 0);
lean_inc(v_val_5499_);
lean_dec_ref_known(v_val_5498_, 1);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 0, v_val_5499_);
v___x_5501_ = v___x_5495_;
goto v_reusejp_5500_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v_val_5499_);
v___x_5501_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5500_;
}
v_reusejp_5500_:
{
return v___x_5501_;
}
}
}
}
}
else
{
lean_object* v_a_5504_; lean_object* v___x_5506_; uint8_t v_isShared_5507_; uint8_t v_isSharedCheck_5511_; 
lean_dec(v_a_5454_);
lean_del_object(v___x_5451_);
lean_dec(v_fieldName_5442_);
lean_dec_ref(v_s_5441_);
v_a_5504_ = lean_ctor_get(v___x_5492_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5492_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5506_ = v___x_5492_;
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
else
{
lean_inc(v_a_5504_);
lean_dec(v___x_5492_);
v___x_5506_ = lean_box(0);
v_isShared_5507_ = v_isSharedCheck_5511_;
goto v_resetjp_5505_;
}
v_resetjp_5505_:
{
lean_object* v___x_5509_; 
if (v_isShared_5507_ == 0)
{
v___x_5509_ = v___x_5506_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_a_5504_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
}
}
else
{
lean_object* v_val_5512_; lean_object* v_dummy_5513_; lean_object* v_nargs_5514_; lean_object* v___x_5515_; lean_object* v___x_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5523_; 
lean_dec_ref(v_env_5481_);
lean_dec(v_declName_5478_);
lean_del_object(v___x_5451_);
lean_dec(v_fieldName_5442_);
v_val_5512_ = lean_ctor_get(v___x_5487_, 0);
lean_inc(v_val_5512_);
lean_dec_ref_known(v___x_5487_, 1);
v_dummy_5513_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5514_ = l_Lean_Expr_getAppNumArgs(v_a_5454_);
lean_inc(v_nargs_5514_);
v___x_5515_ = lean_mk_array(v_nargs_5514_, v_dummy_5513_);
v___x_5516_ = lean_unsigned_to_nat(1u);
v___x_5517_ = lean_nat_sub(v_nargs_5514_, v___x_5516_);
lean_dec(v_nargs_5514_);
v___x_5518_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5454_, v___x_5515_, v___x_5517_);
v___x_5519_ = l_Lean_mkConst(v_val_5512_, v_us_5479_);
v___x_5520_ = l_Lean_mkAppN(v___x_5519_, v___x_5518_);
lean_dec_ref(v___x_5518_);
v___x_5521_ = l_Lean_Expr_app___override(v___x_5520_, v_s_5441_);
if (v_isShared_5457_ == 0)
{
lean_ctor_set(v___x_5456_, 0, v___x_5521_);
v___x_5523_ = v___x_5456_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v___x_5521_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
return v___x_5523_;
}
}
}
}
else
{
lean_object* v___x_5539_; lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; 
lean_dec_ref(v___x_5477_);
lean_del_object(v___x_5456_);
lean_del_object(v___x_5451_);
lean_dec(v_fieldName_5442_);
v___x_5539_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5540_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5541_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5441_, v_a_5454_);
v___x_5542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5542_, 0, v___x_5540_);
lean_ctor_set(v___x_5542_, 1, v___x_5541_);
v___x_5543_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5539_, v___x_5542_, v_a_5443_, v_a_5444_, v_a_5445_, v_a_5446_);
return v___x_5543_;
}
v___jp_5458_:
{
lean_object* v___x_5463_; lean_object* v___x_5464_; uint8_t v___x_5465_; lean_object* v___x_5466_; lean_object* v___x_5468_; 
v___x_5463_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5464_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5465_ = 1;
v___x_5466_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5442_, v___x_5465_);
if (v_isShared_5452_ == 0)
{
lean_ctor_set_tag(v___x_5451_, 3);
lean_ctor_set(v___x_5451_, 0, v___x_5466_);
v___x_5468_ = v___x_5451_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v___x_5466_);
v___x_5468_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; 
v___x_5469_ = l_Lean_MessageData_ofFormat(v___x_5468_);
v___x_5470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5464_);
lean_ctor_set(v___x_5470_, 1, v___x_5469_);
v___x_5471_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5472_, 0, v___x_5470_);
lean_ctor_set(v___x_5472_, 1, v___x_5471_);
v___x_5473_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5441_, v_a_5454_);
v___x_5474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5472_);
lean_ctor_set(v___x_5474_, 1, v___x_5473_);
v___x_5475_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5463_, v___x_5474_, v___y_5459_, v___y_5462_, v___y_5460_, v___y_5461_);
return v___x_5475_;
}
}
}
}
else
{
lean_del_object(v___x_5451_);
lean_dec(v_fieldName_5442_);
lean_dec_ref(v_s_5441_);
return v___x_5453_;
}
}
}
else
{
lean_dec(v_fieldName_5442_);
lean_dec_ref(v_s_5441_);
return v___x_5448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5546_, lean_object* v_declName_5547_, lean_object* v_s_5548_, lean_object* v_fieldName_5549_, lean_object* v_as_5550_, size_t v_sz_5551_, size_t v_i_5552_, lean_object* v_b_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_){
_start:
{
lean_object* v_a_5560_; uint8_t v___x_5564_; 
v___x_5564_ = lean_usize_dec_lt(v_i_5552_, v_sz_5551_);
if (v___x_5564_ == 0)
{
lean_object* v___x_5565_; 
lean_dec(v_fieldName_5549_);
lean_dec_ref(v_s_5548_);
lean_dec(v_declName_5547_);
lean_dec_ref(v___x_5546_);
v___x_5565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5565_, 0, v_b_5553_);
return v___x_5565_;
}
else
{
lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v_a_5568_; lean_object* v___x_5569_; 
lean_dec_ref(v_b_5553_);
v___x_5566_ = lean_box(0);
v___x_5567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5568_ = lean_array_uget_borrowed(v_as_5550_, v_i_5552_);
lean_inc(v_a_5568_);
lean_inc(v_declName_5547_);
lean_inc_ref(v___x_5546_);
v___x_5569_ = l_Lean_isSubobjectField_x3f(v___x_5546_, v_declName_5547_, v_a_5568_);
if (lean_obj_tag(v___x_5569_) == 0)
{
v_a_5560_ = v___x_5567_;
goto v___jp_5559_;
}
else
{
lean_object* v___x_5571_; uint8_t v_isShared_5572_; uint8_t v_isSharedCheck_5629_; 
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5569_);
if (v_isSharedCheck_5629_ == 0)
{
lean_object* v_unused_5630_; 
v_unused_5630_ = lean_ctor_get(v___x_5569_, 0);
lean_dec(v_unused_5630_);
v___x_5571_ = v___x_5569_;
v_isShared_5572_ = v_isSharedCheck_5629_;
goto v_resetjp_5570_;
}
else
{
lean_dec(v___x_5569_);
v___x_5571_ = lean_box(0);
v_isShared_5572_ = v_isSharedCheck_5629_;
goto v_resetjp_5570_;
}
v_resetjp_5570_:
{
lean_object* v___x_5573_; 
lean_inc(v_a_5568_);
lean_inc_ref(v_s_5548_);
v___x_5573_ = l_Lean_Meta_mkProjection(v_s_5548_, v_a_5568_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
if (lean_obj_tag(v___x_5573_) == 0)
{
lean_object* v_a_5574_; lean_object* v___x_5575_; 
v_a_5574_ = lean_ctor_get(v___x_5573_, 0);
lean_inc(v_a_5574_);
lean_dec_ref_known(v___x_5573_, 1);
v___x_5575_ = l_Lean_Meta_saveState___redArg(v___y_5555_, v___y_5557_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v_a_5576_; lean_object* v___x_5577_; 
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
lean_inc(v_a_5576_);
lean_dec_ref_known(v___x_5575_, 1);
lean_inc(v_fieldName_5549_);
v___x_5577_ = l_Lean_Meta_mkProjection(v_a_5574_, v_fieldName_5549_, v___y_5554_, v___y_5555_, v___y_5556_, v___y_5557_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5580_; uint8_t v_isShared_5581_; uint8_t v_isSharedCheck_5590_; 
lean_dec(v_a_5576_);
lean_dec(v_fieldName_5549_);
lean_dec_ref(v_s_5548_);
lean_dec(v_declName_5547_);
lean_dec_ref(v___x_5546_);
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5580_ = v___x_5577_;
v_isShared_5581_ = v_isSharedCheck_5590_;
goto v_resetjp_5579_;
}
else
{
lean_inc(v_a_5578_);
lean_dec(v___x_5577_);
v___x_5580_ = lean_box(0);
v_isShared_5581_ = v_isSharedCheck_5590_;
goto v_resetjp_5579_;
}
v_resetjp_5579_:
{
lean_object* v___x_5583_; 
if (v_isShared_5572_ == 0)
{
lean_ctor_set(v___x_5571_, 0, v_a_5578_);
v___x_5583_ = v___x_5571_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5578_);
v___x_5583_ = v_reuseFailAlloc_5589_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
lean_object* v___x_5584_; lean_object* v___x_5585_; lean_object* v___x_5587_; 
v___x_5584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5584_, 0, v___x_5583_);
v___x_5585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5585_, 0, v___x_5584_);
lean_ctor_set(v___x_5585_, 1, v___x_5566_);
if (v_isShared_5581_ == 0)
{
lean_ctor_set(v___x_5580_, 0, v___x_5585_);
v___x_5587_ = v___x_5580_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5588_; 
v_reuseFailAlloc_5588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5588_, 0, v___x_5585_);
v___x_5587_ = v_reuseFailAlloc_5588_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
return v___x_5587_;
}
}
}
}
else
{
lean_object* v_a_5591_; lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5612_; 
lean_del_object(v___x_5571_);
v_a_5591_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5612_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5612_ == 0)
{
v___x_5593_ = v___x_5577_;
v_isShared_5594_ = v_isSharedCheck_5612_;
goto v_resetjp_5592_;
}
else
{
lean_inc(v_a_5591_);
lean_dec(v___x_5577_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5612_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
uint8_t v___x_5595_; 
v___x_5595_ = l_Lean_Exception_isInterrupt(v_a_5591_);
if (v___x_5595_ == 0)
{
uint8_t v___x_5596_; 
lean_inc(v_a_5591_);
v___x_5596_ = l_Lean_Exception_isRuntime(v_a_5591_);
if (v___x_5596_ == 0)
{
lean_object* v___x_5597_; 
lean_del_object(v___x_5593_);
lean_dec(v_a_5591_);
v___x_5597_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5576_, v___y_5555_, v___y_5557_);
if (lean_obj_tag(v___x_5597_) == 0)
{
lean_dec_ref_known(v___x_5597_, 1);
v_a_5560_ = v___x_5567_;
goto v___jp_5559_;
}
else
{
lean_object* v_a_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5605_; 
lean_dec(v_fieldName_5549_);
lean_dec_ref(v_s_5548_);
lean_dec(v_declName_5547_);
lean_dec_ref(v___x_5546_);
v_a_5598_ = lean_ctor_get(v___x_5597_, 0);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5597_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5600_ = v___x_5597_;
v_isShared_5601_ = v_isSharedCheck_5605_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_a_5598_);
lean_dec(v___x_5597_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5605_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5603_; 
if (v_isShared_5601_ == 0)
{
v___x_5603_ = v___x_5600_;
goto v_reusejp_5602_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_a_5598_);
v___x_5603_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5602_;
}
v_reusejp_5602_:
{
return v___x_5603_;
}
}
}
}
else
{
lean_object* v___x_5607_; 
lean_dec(v_a_5576_);
lean_dec(v_fieldName_5549_);
lean_dec_ref(v_s_5548_);
lean_dec(v_declName_5547_);
lean_dec_ref(v___x_5546_);
if (v_isShared_5594_ == 0)
{
v___x_5607_ = v___x_5593_;
goto v_reusejp_5606_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v_a_5591_);
v___x_5607_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5606_;
}
v_reusejp_5606_:
{
return v___x_5607_;
}
}
}
else
{
lean_object* v___x_5610_; 
lean_dec(v_a_5576_);
lean_dec(v_fieldName_5549_);
lean_dec_ref(v_s_5548_);
lean_dec(v_declName_5547_);
lean_dec_ref(v___x_5546_);
if (v_isShared_5594_ == 0)
{
v___x_5610_ = v___x_5593_;
goto v_reusejp_5609_;
}
else
{
lean_object* v_reuseFailAlloc_5611_; 
v_reuseFailAlloc_5611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5611_, 0, v_a_5591_);
v___x_5610_ = v_reuseFailAlloc_5611_;
goto v_reusejp_5609_;
}
v_reusejp_5609_:
{
return v___x_5610_;
}
}
}
}
}
else
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
lean_dec(v_a_5574_);
lean_del_object(v___x_5571_);
lean_dec(v_fieldName_5549_);
lean_dec_ref(v_s_5548_);
lean_dec(v_declName_5547_);
lean_dec_ref(v___x_5546_);
v_a_5613_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5615_ = v___x_5575_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5575_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5616_ == 0)
{
v___x_5618_ = v___x_5615_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5613_);
v___x_5618_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5617_;
}
v_reusejp_5617_:
{
return v___x_5618_;
}
}
}
}
else
{
lean_object* v_a_5621_; lean_object* v___x_5623_; uint8_t v_isShared_5624_; uint8_t v_isSharedCheck_5628_; 
lean_del_object(v___x_5571_);
lean_dec(v_fieldName_5549_);
lean_dec_ref(v_s_5548_);
lean_dec(v_declName_5547_);
lean_dec_ref(v___x_5546_);
v_a_5621_ = lean_ctor_get(v___x_5573_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5573_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5623_ = v___x_5573_;
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
else
{
lean_inc(v_a_5621_);
lean_dec(v___x_5573_);
v___x_5623_ = lean_box(0);
v_isShared_5624_ = v_isSharedCheck_5628_;
goto v_resetjp_5622_;
}
v_resetjp_5622_:
{
lean_object* v___x_5626_; 
if (v_isShared_5624_ == 0)
{
v___x_5626_ = v___x_5623_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v_a_5621_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
}
}
v___jp_5559_:
{
size_t v___x_5561_; size_t v___x_5562_; 
v___x_5561_ = ((size_t)1ULL);
v___x_5562_ = lean_usize_add(v_i_5552_, v___x_5561_);
lean_inc_ref(v_a_5560_);
v_i_5552_ = v___x_5562_;
v_b_5553_ = v_a_5560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5631_, lean_object* v_declName_5632_, lean_object* v_s_5633_, lean_object* v_fieldName_5634_, lean_object* v_as_5635_, lean_object* v_sz_5636_, lean_object* v_i_5637_, lean_object* v_b_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_){
_start:
{
size_t v_sz_boxed_5644_; size_t v_i_boxed_5645_; lean_object* v_res_5646_; 
v_sz_boxed_5644_ = lean_unbox_usize(v_sz_5636_);
lean_dec(v_sz_5636_);
v_i_boxed_5645_ = lean_unbox_usize(v_i_5637_);
lean_dec(v_i_5637_);
v_res_5646_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5631_, v_declName_5632_, v_s_5633_, v_fieldName_5634_, v_as_5635_, v_sz_boxed_5644_, v_i_boxed_5645_, v_b_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec_ref(v_as_5635_);
return v_res_5646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5647_, lean_object* v_fieldName_5648_, lean_object* v_a_5649_, lean_object* v_a_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_){
_start:
{
lean_object* v_res_5654_; 
v_res_5654_ = l_Lean_Meta_mkProjection(v_s_5647_, v_fieldName_5648_, v_a_5649_, v_a_5650_, v_a_5651_, v_a_5652_);
lean_dec(v_a_5652_);
lean_dec_ref(v_a_5651_);
lean_dec(v_a_5650_);
lean_dec_ref(v_a_5649_);
return v_res_5654_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5655_, lean_object* v_cons_5656_, lean_object* v_x_5657_){
_start:
{
if (lean_obj_tag(v_x_5657_) == 0)
{
lean_dec_ref(v_cons_5656_);
lean_inc_ref(v_nil_5655_);
return v_nil_5655_;
}
else
{
lean_object* v_head_5658_; lean_object* v_tail_5659_; lean_object* v___x_5660_; lean_object* v___x_5661_; lean_object* v___x_5662_; 
v_head_5658_ = lean_ctor_get(v_x_5657_, 0);
lean_inc(v_head_5658_);
v_tail_5659_ = lean_ctor_get(v_x_5657_, 1);
lean_inc(v_tail_5659_);
lean_dec_ref_known(v_x_5657_, 2);
lean_inc_ref(v_cons_5656_);
v___x_5660_ = l_Lean_Expr_app___override(v_cons_5656_, v_head_5658_);
v___x_5661_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5655_, v_cons_5656_, v_tail_5659_);
v___x_5662_ = l_Lean_Expr_app___override(v___x_5660_, v___x_5661_);
return v___x_5662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5663_, lean_object* v_cons_5664_, lean_object* v_x_5665_){
_start:
{
lean_object* v_res_5666_; 
v_res_5666_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5663_, v_cons_5664_, v_x_5665_);
lean_dec_ref(v_nil_5663_);
return v_res_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5676_, lean_object* v_xs_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_, lean_object* v_a_5680_, lean_object* v_a_5681_){
_start:
{
lean_object* v___x_5683_; 
lean_inc_ref(v_type_5676_);
v___x_5683_ = l_Lean_Meta_getDecLevel(v_type_5676_, v_a_5678_, v_a_5679_, v_a_5680_, v_a_5681_);
if (lean_obj_tag(v___x_5683_) == 0)
{
lean_object* v_a_5684_; lean_object* v___x_5686_; uint8_t v_isShared_5687_; uint8_t v_isSharedCheck_5703_; 
v_a_5684_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5703_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5703_ == 0)
{
v___x_5686_ = v___x_5683_;
v_isShared_5687_ = v_isSharedCheck_5703_;
goto v_resetjp_5685_;
}
else
{
lean_inc(v_a_5684_);
lean_dec(v___x_5683_);
v___x_5686_ = lean_box(0);
v_isShared_5687_ = v_isSharedCheck_5703_;
goto v_resetjp_5685_;
}
v_resetjp_5685_:
{
lean_object* v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5688_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5689_ = lean_box(0);
v___x_5690_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5690_, 0, v_a_5684_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
lean_inc_ref(v___x_5690_);
v___x_5691_ = l_Lean_mkConst(v___x_5688_, v___x_5690_);
lean_inc_ref(v_type_5676_);
v___x_5692_ = l_Lean_Expr_app___override(v___x_5691_, v_type_5676_);
if (lean_obj_tag(v_xs_5677_) == 0)
{
lean_object* v___x_5694_; 
lean_dec_ref_known(v___x_5690_, 2);
lean_dec_ref(v_type_5676_);
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 0, v___x_5692_);
v___x_5694_ = v___x_5686_;
goto v_reusejp_5693_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5692_);
v___x_5694_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5693_;
}
v_reusejp_5693_:
{
return v___x_5694_;
}
}
else
{
lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; lean_object* v___x_5701_; 
v___x_5696_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5697_ = l_Lean_mkConst(v___x_5696_, v___x_5690_);
v___x_5698_ = l_Lean_Expr_app___override(v___x_5697_, v_type_5676_);
v___x_5699_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5692_, v___x_5698_, v_xs_5677_);
lean_dec_ref(v___x_5692_);
if (v_isShared_5687_ == 0)
{
lean_ctor_set(v___x_5686_, 0, v___x_5699_);
v___x_5701_ = v___x_5686_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5699_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
else
{
lean_object* v_a_5704_; lean_object* v___x_5706_; uint8_t v_isShared_5707_; uint8_t v_isSharedCheck_5711_; 
lean_dec(v_xs_5677_);
lean_dec_ref(v_type_5676_);
v_a_5704_ = lean_ctor_get(v___x_5683_, 0);
v_isSharedCheck_5711_ = !lean_is_exclusive(v___x_5683_);
if (v_isSharedCheck_5711_ == 0)
{
v___x_5706_ = v___x_5683_;
v_isShared_5707_ = v_isSharedCheck_5711_;
goto v_resetjp_5705_;
}
else
{
lean_inc(v_a_5704_);
lean_dec(v___x_5683_);
v___x_5706_ = lean_box(0);
v_isShared_5707_ = v_isSharedCheck_5711_;
goto v_resetjp_5705_;
}
v_resetjp_5705_:
{
lean_object* v___x_5709_; 
if (v_isShared_5707_ == 0)
{
v___x_5709_ = v___x_5706_;
goto v_reusejp_5708_;
}
else
{
lean_object* v_reuseFailAlloc_5710_; 
v_reuseFailAlloc_5710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5710_, 0, v_a_5704_);
v___x_5709_ = v_reuseFailAlloc_5710_;
goto v_reusejp_5708_;
}
v_reusejp_5708_:
{
return v___x_5709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5712_, lean_object* v_xs_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_, lean_object* v_a_5717_, lean_object* v_a_5718_){
_start:
{
lean_object* v_res_5719_; 
v_res_5719_ = l_Lean_Meta_mkListLit(v_type_5712_, v_xs_5713_, v_a_5714_, v_a_5715_, v_a_5716_, v_a_5717_);
lean_dec(v_a_5717_);
lean_dec_ref(v_a_5716_);
lean_dec(v_a_5715_);
lean_dec_ref(v_a_5714_);
return v_res_5719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5724_, lean_object* v_xs_5725_, lean_object* v_a_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_){
_start:
{
lean_object* v___x_5731_; 
lean_inc_ref(v_type_5724_);
v___x_5731_ = l_Lean_Meta_getDecLevel(v_type_5724_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_);
if (lean_obj_tag(v___x_5731_) == 0)
{
lean_object* v_a_5732_; lean_object* v___x_5733_; 
v_a_5732_ = lean_ctor_get(v___x_5731_, 0);
lean_inc(v_a_5732_);
lean_dec_ref_known(v___x_5731_, 1);
lean_inc_ref(v_type_5724_);
v___x_5733_ = l_Lean_Meta_mkListLit(v_type_5724_, v_xs_5725_, v_a_5726_, v_a_5727_, v_a_5728_, v_a_5729_);
if (lean_obj_tag(v___x_5733_) == 0)
{
lean_object* v_a_5734_; lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5747_; 
v_a_5734_ = lean_ctor_get(v___x_5733_, 0);
v_isSharedCheck_5747_ = !lean_is_exclusive(v___x_5733_);
if (v_isSharedCheck_5747_ == 0)
{
v___x_5736_ = v___x_5733_;
v_isShared_5737_ = v_isSharedCheck_5747_;
goto v_resetjp_5735_;
}
else
{
lean_inc(v_a_5734_);
lean_dec(v___x_5733_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5747_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v___x_5743_; lean_object* v___x_5745_; 
v___x_5738_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5739_ = lean_box(0);
v___x_5740_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5740_, 0, v_a_5732_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
v___x_5741_ = l_Lean_mkConst(v___x_5738_, v___x_5740_);
v___x_5742_ = l_Lean_Expr_app___override(v___x_5741_, v_type_5724_);
v___x_5743_ = l_Lean_Expr_app___override(v___x_5742_, v_a_5734_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 0, v___x_5743_);
v___x_5745_ = v___x_5736_;
goto v_reusejp_5744_;
}
else
{
lean_object* v_reuseFailAlloc_5746_; 
v_reuseFailAlloc_5746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5746_, 0, v___x_5743_);
v___x_5745_ = v_reuseFailAlloc_5746_;
goto v_reusejp_5744_;
}
v_reusejp_5744_:
{
return v___x_5745_;
}
}
}
else
{
lean_dec(v_a_5732_);
lean_dec_ref(v_type_5724_);
return v___x_5733_;
}
}
else
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5755_; 
lean_dec(v_xs_5725_);
lean_dec_ref(v_type_5724_);
v_a_5748_ = lean_ctor_get(v___x_5731_, 0);
v_isSharedCheck_5755_ = !lean_is_exclusive(v___x_5731_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5750_ = v___x_5731_;
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5731_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5755_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5753_; 
if (v_isShared_5751_ == 0)
{
v___x_5753_ = v___x_5750_;
goto v_reusejp_5752_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v_a_5748_);
v___x_5753_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5752_;
}
v_reusejp_5752_:
{
return v___x_5753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5756_, lean_object* v_xs_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_){
_start:
{
lean_object* v_res_5763_; 
v_res_5763_ = l_Lean_Meta_mkArrayLit(v_type_5756_, v_xs_5757_, v_a_5758_, v_a_5759_, v_a_5760_, v_a_5761_);
lean_dec(v_a_5761_);
lean_dec_ref(v_a_5760_);
lean_dec(v_a_5759_);
lean_dec_ref(v_a_5758_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5769_, lean_object* v_a_5770_, lean_object* v_a_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_){
_start:
{
lean_object* v___x_5775_; 
lean_inc_ref(v_type_5769_);
v___x_5775_ = l_Lean_Meta_getDecLevel(v_type_5769_, v_a_5770_, v_a_5771_, v_a_5772_, v_a_5773_);
if (lean_obj_tag(v___x_5775_) == 0)
{
lean_object* v_a_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5788_; 
v_a_5776_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5788_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5788_ == 0)
{
v___x_5778_ = v___x_5775_;
v_isShared_5779_ = v_isSharedCheck_5788_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_a_5776_);
lean_dec(v___x_5775_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5788_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v___x_5780_; lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5786_; 
v___x_5780_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5781_ = lean_box(0);
v___x_5782_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5782_, 0, v_a_5776_);
lean_ctor_set(v___x_5782_, 1, v___x_5781_);
v___x_5783_ = l_Lean_mkConst(v___x_5780_, v___x_5782_);
v___x_5784_ = l_Lean_Expr_app___override(v___x_5783_, v_type_5769_);
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 0, v___x_5784_);
v___x_5786_ = v___x_5778_;
goto v_reusejp_5785_;
}
else
{
lean_object* v_reuseFailAlloc_5787_; 
v_reuseFailAlloc_5787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5787_, 0, v___x_5784_);
v___x_5786_ = v_reuseFailAlloc_5787_;
goto v_reusejp_5785_;
}
v_reusejp_5785_:
{
return v___x_5786_;
}
}
}
else
{
lean_object* v_a_5789_; lean_object* v___x_5791_; uint8_t v_isShared_5792_; uint8_t v_isSharedCheck_5796_; 
lean_dec_ref(v_type_5769_);
v_a_5789_ = lean_ctor_get(v___x_5775_, 0);
v_isSharedCheck_5796_ = !lean_is_exclusive(v___x_5775_);
if (v_isSharedCheck_5796_ == 0)
{
v___x_5791_ = v___x_5775_;
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
else
{
lean_inc(v_a_5789_);
lean_dec(v___x_5775_);
v___x_5791_ = lean_box(0);
v_isShared_5792_ = v_isSharedCheck_5796_;
goto v_resetjp_5790_;
}
v_resetjp_5790_:
{
lean_object* v___x_5794_; 
if (v_isShared_5792_ == 0)
{
v___x_5794_ = v___x_5791_;
goto v_reusejp_5793_;
}
else
{
lean_object* v_reuseFailAlloc_5795_; 
v_reuseFailAlloc_5795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5795_, 0, v_a_5789_);
v___x_5794_ = v_reuseFailAlloc_5795_;
goto v_reusejp_5793_;
}
v_reusejp_5793_:
{
return v___x_5794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5797_, lean_object* v_a_5798_, lean_object* v_a_5799_, lean_object* v_a_5800_, lean_object* v_a_5801_, lean_object* v_a_5802_){
_start:
{
lean_object* v_res_5803_; 
v_res_5803_ = l_Lean_Meta_mkNone(v_type_5797_, v_a_5798_, v_a_5799_, v_a_5800_, v_a_5801_);
lean_dec(v_a_5801_);
lean_dec_ref(v_a_5800_);
lean_dec(v_a_5799_);
lean_dec_ref(v_a_5798_);
return v_res_5803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5808_, lean_object* v_value_5809_, lean_object* v_a_5810_, lean_object* v_a_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_){
_start:
{
lean_object* v___x_5815_; 
lean_inc_ref(v_type_5808_);
v___x_5815_ = l_Lean_Meta_getDecLevel(v_type_5808_, v_a_5810_, v_a_5811_, v_a_5812_, v_a_5813_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_object* v_a_5816_; lean_object* v___x_5818_; uint8_t v_isShared_5819_; uint8_t v_isSharedCheck_5828_; 
v_a_5816_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5828_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5828_ == 0)
{
v___x_5818_ = v___x_5815_;
v_isShared_5819_ = v_isSharedCheck_5828_;
goto v_resetjp_5817_;
}
else
{
lean_inc(v_a_5816_);
lean_dec(v___x_5815_);
v___x_5818_ = lean_box(0);
v_isShared_5819_ = v_isSharedCheck_5828_;
goto v_resetjp_5817_;
}
v_resetjp_5817_:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; lean_object* v___x_5824_; lean_object* v___x_5826_; 
v___x_5820_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5821_ = lean_box(0);
v___x_5822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5822_, 0, v_a_5816_);
lean_ctor_set(v___x_5822_, 1, v___x_5821_);
v___x_5823_ = l_Lean_mkConst(v___x_5820_, v___x_5822_);
v___x_5824_ = l_Lean_mkAppB(v___x_5823_, v_type_5808_, v_value_5809_);
if (v_isShared_5819_ == 0)
{
lean_ctor_set(v___x_5818_, 0, v___x_5824_);
v___x_5826_ = v___x_5818_;
goto v_reusejp_5825_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v___x_5824_);
v___x_5826_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5825_;
}
v_reusejp_5825_:
{
return v___x_5826_;
}
}
}
else
{
lean_object* v_a_5829_; lean_object* v___x_5831_; uint8_t v_isShared_5832_; uint8_t v_isSharedCheck_5836_; 
lean_dec_ref(v_value_5809_);
lean_dec_ref(v_type_5808_);
v_a_5829_ = lean_ctor_get(v___x_5815_, 0);
v_isSharedCheck_5836_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5836_ == 0)
{
v___x_5831_ = v___x_5815_;
v_isShared_5832_ = v_isSharedCheck_5836_;
goto v_resetjp_5830_;
}
else
{
lean_inc(v_a_5829_);
lean_dec(v___x_5815_);
v___x_5831_ = lean_box(0);
v_isShared_5832_ = v_isSharedCheck_5836_;
goto v_resetjp_5830_;
}
v_resetjp_5830_:
{
lean_object* v___x_5834_; 
if (v_isShared_5832_ == 0)
{
v___x_5834_ = v___x_5831_;
goto v_reusejp_5833_;
}
else
{
lean_object* v_reuseFailAlloc_5835_; 
v_reuseFailAlloc_5835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5835_, 0, v_a_5829_);
v___x_5834_ = v_reuseFailAlloc_5835_;
goto v_reusejp_5833_;
}
v_reusejp_5833_:
{
return v___x_5834_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5837_, lean_object* v_value_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_, lean_object* v_a_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_){
_start:
{
lean_object* v_res_5844_; 
v_res_5844_ = l_Lean_Meta_mkSome(v_type_5837_, v_value_5838_, v_a_5839_, v_a_5840_, v_a_5841_, v_a_5842_);
lean_dec(v_a_5842_);
lean_dec_ref(v_a_5841_);
lean_dec(v_a_5840_);
lean_dec_ref(v_a_5839_);
return v_res_5844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5850_, lean_object* v_a_5851_, lean_object* v_a_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_){
_start:
{
lean_object* v___x_5856_; lean_object* v___x_5857_; lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5856_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5857_, 0, v_p_5850_);
v___x_5858_ = lean_box(0);
v___x_5859_ = lean_unsigned_to_nat(2u);
v___x_5860_ = lean_mk_empty_array_with_capacity(v___x_5859_);
v___x_5861_ = lean_array_push(v___x_5860_, v___x_5857_);
v___x_5862_ = lean_array_push(v___x_5861_, v___x_5858_);
v___x_5863_ = l_Lean_Meta_mkAppOptM(v___x_5856_, v___x_5862_, v_a_5851_, v_a_5852_, v_a_5853_, v_a_5854_);
return v___x_5863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5864_, lean_object* v_a_5865_, lean_object* v_a_5866_, lean_object* v_a_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_){
_start:
{
lean_object* v_res_5870_; 
v_res_5870_ = l_Lean_Meta_mkDecide(v_p_5864_, v_a_5865_, v_a_5866_, v_a_5867_, v_a_5868_);
lean_dec(v_a_5868_);
lean_dec_ref(v_a_5867_);
lean_dec(v_a_5866_);
lean_dec_ref(v_a_5865_);
return v_res_5870_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5876_ = lean_box(0);
v___x_5877_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5878_ = l_Lean_mkConst(v___x_5877_, v___x_5876_);
return v___x_5878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_, lean_object* v_a_5886_){
_start:
{
lean_object* v___x_5888_; 
v___x_5888_ = l_Lean_Meta_mkDecide(v_p_5882_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
if (lean_obj_tag(v___x_5888_) == 0)
{
lean_object* v_a_5889_; lean_object* v___x_5890_; lean_object* v___x_5891_; 
v_a_5889_ = lean_ctor_get(v___x_5888_, 0);
lean_inc(v_a_5889_);
lean_dec_ref_known(v___x_5888_, 1);
v___x_5890_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5891_ = l_Lean_Meta_mkEq(v_a_5889_, v___x_5890_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
if (lean_obj_tag(v___x_5891_) == 0)
{
lean_object* v_a_5892_; lean_object* v___x_5893_; 
v_a_5892_ = lean_ctor_get(v___x_5891_, 0);
lean_inc(v_a_5892_);
lean_dec_ref_known(v___x_5891_, 1);
v___x_5893_ = l_Lean_Meta_mkEqRefl(v___x_5890_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
if (lean_obj_tag(v___x_5893_) == 0)
{
lean_object* v_a_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; 
v_a_5894_ = lean_ctor_get(v___x_5893_, 0);
lean_inc(v_a_5894_);
lean_dec_ref_known(v___x_5893_, 1);
v___x_5895_ = l_Lean_Meta_mkExpectedPropHint(v_a_5894_, v_a_5892_);
v___x_5896_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5897_ = lean_unsigned_to_nat(1u);
v___x_5898_ = lean_mk_empty_array_with_capacity(v___x_5897_);
v___x_5899_ = lean_array_push(v___x_5898_, v___x_5895_);
v___x_5900_ = l_Lean_Meta_mkAppM(v___x_5896_, v___x_5899_, v_a_5883_, v_a_5884_, v_a_5885_, v_a_5886_);
return v___x_5900_;
}
else
{
lean_dec(v_a_5892_);
return v___x_5893_;
}
}
else
{
return v___x_5891_;
}
}
else
{
return v___x_5888_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5901_, lean_object* v_a_5902_, lean_object* v_a_5903_, lean_object* v_a_5904_, lean_object* v_a_5905_, lean_object* v_a_5906_){
_start:
{
lean_object* v_res_5907_; 
v_res_5907_ = l_Lean_Meta_mkDecideProof(v_p_5901_, v_a_5902_, v_a_5903_, v_a_5904_, v_a_5905_);
lean_dec(v_a_5905_);
lean_dec_ref(v_a_5904_);
lean_dec(v_a_5903_);
lean_dec_ref(v_a_5902_);
return v_res_5907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5913_, lean_object* v_b_5914_, lean_object* v_a_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_){
_start:
{
lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; 
v___x_5920_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_5921_ = lean_unsigned_to_nat(2u);
v___x_5922_ = lean_mk_empty_array_with_capacity(v___x_5921_);
v___x_5923_ = lean_array_push(v___x_5922_, v_a_5913_);
v___x_5924_ = lean_array_push(v___x_5923_, v_b_5914_);
v___x_5925_ = l_Lean_Meta_mkAppM(v___x_5920_, v___x_5924_, v_a_5915_, v_a_5916_, v_a_5917_, v_a_5918_);
return v___x_5925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_5926_, lean_object* v_b_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_){
_start:
{
lean_object* v_res_5933_; 
v_res_5933_ = l_Lean_Meta_mkLt(v_a_5926_, v_b_5927_, v_a_5928_, v_a_5929_, v_a_5930_, v_a_5931_);
lean_dec(v_a_5931_);
lean_dec_ref(v_a_5930_);
lean_dec(v_a_5929_);
lean_dec_ref(v_a_5928_);
return v_res_5933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_5939_, lean_object* v_b_5940_, lean_object* v_a_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_){
_start:
{
lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; 
v___x_5946_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_5947_ = lean_unsigned_to_nat(2u);
v___x_5948_ = lean_mk_empty_array_with_capacity(v___x_5947_);
v___x_5949_ = lean_array_push(v___x_5948_, v_a_5939_);
v___x_5950_ = lean_array_push(v___x_5949_, v_b_5940_);
v___x_5951_ = l_Lean_Meta_mkAppM(v___x_5946_, v___x_5950_, v_a_5941_, v_a_5942_, v_a_5943_, v_a_5944_);
return v___x_5951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_5952_, lean_object* v_b_5953_, lean_object* v_a_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_){
_start:
{
lean_object* v_res_5959_; 
v_res_5959_ = l_Lean_Meta_mkLe(v_a_5952_, v_b_5953_, v_a_5954_, v_a_5955_, v_a_5956_, v_a_5957_);
lean_dec(v_a_5957_);
lean_dec_ref(v_a_5956_);
lean_dec(v_a_5955_);
lean_dec_ref(v_a_5954_);
return v_res_5959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_5965_, lean_object* v_a_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_){
_start:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5971_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_5972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5972_, 0, v_00_u03b1_5965_);
v___x_5973_ = lean_box(0);
v___x_5974_ = lean_unsigned_to_nat(2u);
v___x_5975_ = lean_mk_empty_array_with_capacity(v___x_5974_);
v___x_5976_ = lean_array_push(v___x_5975_, v___x_5972_);
v___x_5977_ = lean_array_push(v___x_5976_, v___x_5973_);
v___x_5978_ = l_Lean_Meta_mkAppOptM(v___x_5971_, v___x_5977_, v_a_5966_, v_a_5967_, v_a_5968_, v_a_5969_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lean_Meta_mkDefault(v_00_u03b1_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_);
lean_dec(v_a_5983_);
lean_dec_ref(v_a_5982_);
lean_dec(v_a_5981_);
lean_dec_ref(v_a_5980_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_){
_start:
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; 
v___x_5997_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_5998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5998_, 0, v_00_u03b1_5991_);
v___x_5999_ = lean_box(0);
v___x_6000_ = lean_unsigned_to_nat(2u);
v___x_6001_ = lean_mk_empty_array_with_capacity(v___x_6000_);
v___x_6002_ = lean_array_push(v___x_6001_, v___x_5998_);
v___x_6003_ = lean_array_push(v___x_6002_, v___x_5999_);
v___x_6004_ = l_Lean_Meta_mkAppOptM(v___x_5997_, v___x_6003_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_);
return v___x_6004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_){
_start:
{
lean_object* v_res_6011_; 
v_res_6011_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6005_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
lean_dec(v_a_6009_);
lean_dec_ref(v_a_6008_);
lean_dec(v_a_6007_);
lean_dec_ref(v_a_6006_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_, lean_object* v_a_6018_, lean_object* v_a_6019_){
_start:
{
lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6021_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6022_ = lean_unsigned_to_nat(1u);
v___x_6023_ = lean_mk_empty_array_with_capacity(v___x_6022_);
v___x_6024_ = lean_array_push(v___x_6023_, v_h_6015_);
v___x_6025_ = l_Lean_Meta_mkAppM(v___x_6021_, v___x_6024_, v_a_6016_, v_a_6017_, v_a_6018_, v_a_6019_);
return v___x_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6026_, lean_object* v_a_6027_, lean_object* v_a_6028_, lean_object* v_a_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_){
_start:
{
lean_object* v_res_6032_; 
v_res_6032_ = l_Lean_Meta_mkFunExt(v_h_6026_, v_a_6027_, v_a_6028_, v_a_6029_, v_a_6030_);
lean_dec(v_a_6030_);
lean_dec_ref(v_a_6029_);
lean_dec(v_a_6028_);
lean_dec_ref(v_a_6027_);
return v_res_6032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6036_, lean_object* v_a_6037_, lean_object* v_a_6038_, lean_object* v_a_6039_, lean_object* v_a_6040_){
_start:
{
lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___x_6042_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6043_ = lean_unsigned_to_nat(1u);
v___x_6044_ = lean_mk_empty_array_with_capacity(v___x_6043_);
v___x_6045_ = lean_array_push(v___x_6044_, v_h_6036_);
v___x_6046_ = l_Lean_Meta_mkAppM(v___x_6042_, v___x_6045_, v_a_6037_, v_a_6038_, v_a_6039_, v_a_6040_);
return v___x_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6047_, lean_object* v_a_6048_, lean_object* v_a_6049_, lean_object* v_a_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_){
_start:
{
lean_object* v_res_6053_; 
v_res_6053_ = l_Lean_Meta_mkPropExt(v_h_6047_, v_a_6048_, v_a_6049_, v_a_6050_, v_a_6051_);
lean_dec(v_a_6051_);
lean_dec_ref(v_a_6050_);
lean_dec(v_a_6049_);
lean_dec_ref(v_a_6048_);
return v_res_6053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6057_, lean_object* v_h_u2082_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_){
_start:
{
lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; 
v___x_6064_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6065_ = lean_unsigned_to_nat(2u);
v___x_6066_ = lean_mk_empty_array_with_capacity(v___x_6065_);
v___x_6067_ = lean_array_push(v___x_6066_, v_h_u2081_6057_);
v___x_6068_ = lean_array_push(v___x_6067_, v_h_u2082_6058_);
v___x_6069_ = l_Lean_Meta_mkAppM(v___x_6064_, v___x_6068_, v_a_6059_, v_a_6060_, v_a_6061_, v_a_6062_);
return v___x_6069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6070_, lean_object* v_h_u2082_6071_, lean_object* v_a_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_){
_start:
{
lean_object* v_res_6077_; 
v_res_6077_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6070_, v_h_u2082_6071_, v_a_6072_, v_a_6073_, v_a_6074_, v_a_6075_);
lean_dec(v_a_6075_);
lean_dec_ref(v_a_6074_);
lean_dec(v_a_6073_);
lean_dec_ref(v_a_6072_);
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6081_, lean_object* v_h_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_){
_start:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6088_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6089_ = lean_unsigned_to_nat(2u);
v___x_6090_ = lean_mk_empty_array_with_capacity(v___x_6089_);
v___x_6091_ = lean_array_push(v___x_6090_, v_b_6081_);
v___x_6092_ = lean_array_push(v___x_6091_, v_h_6082_);
v___x_6093_ = l_Lean_Meta_mkAppM(v___x_6088_, v___x_6092_, v_a_6083_, v_a_6084_, v_a_6085_, v_a_6086_);
return v___x_6093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6094_, lean_object* v_h_6095_, lean_object* v_a_6096_, lean_object* v_a_6097_, lean_object* v_a_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_){
_start:
{
lean_object* v_res_6101_; 
v_res_6101_ = l_Lean_Meta_mkLetValCongr(v_b_6094_, v_h_6095_, v_a_6096_, v_a_6097_, v_a_6098_, v_a_6099_);
lean_dec(v_a_6099_);
lean_dec_ref(v_a_6098_);
lean_dec(v_a_6097_);
lean_dec_ref(v_a_6096_);
return v_res_6101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6105_, lean_object* v_h_6106_, lean_object* v_a_6107_, lean_object* v_a_6108_, lean_object* v_a_6109_, lean_object* v_a_6110_){
_start:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6112_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6113_ = lean_unsigned_to_nat(2u);
v___x_6114_ = lean_mk_empty_array_with_capacity(v___x_6113_);
v___x_6115_ = lean_array_push(v___x_6114_, v_a_6105_);
v___x_6116_ = lean_array_push(v___x_6115_, v_h_6106_);
v___x_6117_ = l_Lean_Meta_mkAppM(v___x_6112_, v___x_6116_, v_a_6107_, v_a_6108_, v_a_6109_, v_a_6110_);
return v___x_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6118_, lean_object* v_h_6119_, lean_object* v_a_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_){
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l_Lean_Meta_mkLetBodyCongr(v_a_6118_, v_h_6119_, v_a_6120_, v_a_6121_, v_a_6122_, v_a_6123_);
lean_dec(v_a_6123_);
lean_dec_ref(v_a_6122_);
lean_dec(v_a_6121_);
lean_dec_ref(v_a_6120_);
return v_res_6125_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; 
v___x_6129_ = lean_box(0);
v___x_6130_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6131_ = l_Lean_mkConst(v___x_6130_, v___x_6129_);
return v___x_6131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6135_, lean_object* v_h_6136_){
_start:
{
lean_object* v___x_6140_; uint8_t v___x_6141_; 
lean_inc_ref(v_h_6136_);
v___x_6140_ = l_Lean_Expr_cleanupAnnotations(v_h_6136_);
v___x_6141_ = l_Lean_Expr_isApp(v___x_6140_);
if (v___x_6141_ == 0)
{
lean_dec_ref(v___x_6140_);
goto v___jp_6137_;
}
else
{
lean_object* v_arg_6142_; lean_object* v___x_6143_; uint8_t v___x_6144_; 
v_arg_6142_ = lean_ctor_get(v___x_6140_, 1);
lean_inc_ref(v_arg_6142_);
v___x_6143_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6140_);
v___x_6144_ = l_Lean_Expr_isApp(v___x_6143_);
if (v___x_6144_ == 0)
{
lean_dec_ref(v___x_6143_);
lean_dec_ref(v_arg_6142_);
goto v___jp_6137_;
}
else
{
lean_object* v___x_6145_; lean_object* v___x_6146_; uint8_t v___x_6147_; 
v___x_6145_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6143_);
v___x_6146_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6147_ = l_Lean_Expr_isConstOf(v___x_6145_, v___x_6146_);
lean_dec_ref(v___x_6145_);
if (v___x_6147_ == 0)
{
lean_dec_ref(v_arg_6142_);
goto v___jp_6137_;
}
else
{
lean_dec_ref(v_h_6136_);
lean_dec_ref(v_p_6135_);
return v_arg_6142_;
}
}
}
v___jp_6137_:
{
lean_object* v___x_6138_; lean_object* v___x_6139_; 
v___x_6138_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6139_ = l_Lean_mkAppB(v___x_6138_, v_p_6135_, v_h_6136_);
return v___x_6139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6148_, lean_object* v_a_6149_, lean_object* v_a_6150_, lean_object* v_a_6151_, lean_object* v_a_6152_){
_start:
{
lean_object* v___y_6155_; lean_object* v___y_6156_; lean_object* v___y_6157_; lean_object* v___y_6158_; lean_object* v___x_6164_; 
lean_inc_ref(v_h_6148_);
v___x_6164_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6148_, v_a_6150_);
if (lean_obj_tag(v___x_6164_) == 0)
{
lean_object* v_a_6165_; lean_object* v___x_6167_; uint8_t v_isShared_6168_; uint8_t v_isSharedCheck_6180_; 
v_a_6165_ = lean_ctor_get(v___x_6164_, 0);
v_isSharedCheck_6180_ = !lean_is_exclusive(v___x_6164_);
if (v_isSharedCheck_6180_ == 0)
{
v___x_6167_ = v___x_6164_;
v_isShared_6168_ = v_isSharedCheck_6180_;
goto v_resetjp_6166_;
}
else
{
lean_inc(v_a_6165_);
lean_dec(v___x_6164_);
v___x_6167_ = lean_box(0);
v_isShared_6168_ = v_isSharedCheck_6180_;
goto v_resetjp_6166_;
}
v_resetjp_6166_:
{
lean_object* v___x_6169_; uint8_t v___x_6170_; 
v___x_6169_ = l_Lean_Expr_cleanupAnnotations(v_a_6165_);
v___x_6170_ = l_Lean_Expr_isApp(v___x_6169_);
if (v___x_6170_ == 0)
{
lean_dec_ref(v___x_6169_);
lean_del_object(v___x_6167_);
v___y_6155_ = v_a_6149_;
v___y_6156_ = v_a_6150_;
v___y_6157_ = v_a_6151_;
v___y_6158_ = v_a_6152_;
goto v___jp_6154_;
}
else
{
lean_object* v_arg_6171_; lean_object* v___x_6172_; uint8_t v___x_6173_; 
v_arg_6171_ = lean_ctor_get(v___x_6169_, 1);
lean_inc_ref(v_arg_6171_);
v___x_6172_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6169_);
v___x_6173_ = l_Lean_Expr_isApp(v___x_6172_);
if (v___x_6173_ == 0)
{
lean_dec_ref(v___x_6172_);
lean_dec_ref(v_arg_6171_);
lean_del_object(v___x_6167_);
v___y_6155_ = v_a_6149_;
v___y_6156_ = v_a_6150_;
v___y_6157_ = v_a_6151_;
v___y_6158_ = v_a_6152_;
goto v___jp_6154_;
}
else
{
lean_object* v___x_6174_; lean_object* v___x_6175_; uint8_t v___x_6176_; 
v___x_6174_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6172_);
v___x_6175_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6176_ = l_Lean_Expr_isConstOf(v___x_6174_, v___x_6175_);
lean_dec_ref(v___x_6174_);
if (v___x_6176_ == 0)
{
lean_dec_ref(v_arg_6171_);
lean_del_object(v___x_6167_);
v___y_6155_ = v_a_6149_;
v___y_6156_ = v_a_6150_;
v___y_6157_ = v_a_6151_;
v___y_6158_ = v_a_6152_;
goto v___jp_6154_;
}
else
{
lean_object* v___x_6178_; 
lean_dec_ref(v_h_6148_);
if (v_isShared_6168_ == 0)
{
lean_ctor_set(v___x_6167_, 0, v_arg_6171_);
v___x_6178_ = v___x_6167_;
goto v_reusejp_6177_;
}
else
{
lean_object* v_reuseFailAlloc_6179_; 
v_reuseFailAlloc_6179_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6179_, 0, v_arg_6171_);
v___x_6178_ = v_reuseFailAlloc_6179_;
goto v_reusejp_6177_;
}
v_reusejp_6177_:
{
return v___x_6178_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6148_);
return v___x_6164_;
}
v___jp_6154_:
{
lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; 
v___x_6159_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6160_ = lean_unsigned_to_nat(1u);
v___x_6161_ = lean_mk_empty_array_with_capacity(v___x_6160_);
v___x_6162_ = lean_array_push(v___x_6161_, v_h_6148_);
v___x_6163_ = l_Lean_Meta_mkAppM(v___x_6159_, v___x_6162_, v___y_6155_, v___y_6156_, v___y_6157_, v___y_6158_);
return v___x_6163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6181_, lean_object* v_a_6182_, lean_object* v_a_6183_, lean_object* v_a_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_){
_start:
{
lean_object* v_res_6187_; 
v_res_6187_ = l_Lean_Meta_mkOfEqFalse(v_h_6181_, v_a_6182_, v_a_6183_, v_a_6184_, v_a_6185_);
lean_dec(v_a_6185_);
lean_dec_ref(v_a_6184_);
lean_dec(v_a_6183_);
lean_dec_ref(v_a_6182_);
return v_res_6187_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6191_ = lean_box(0);
v___x_6192_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6193_ = l_Lean_mkConst(v___x_6192_, v___x_6191_);
return v___x_6193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6197_, lean_object* v_h_6198_){
_start:
{
lean_object* v___x_6202_; uint8_t v___x_6203_; 
lean_inc_ref(v_h_6198_);
v___x_6202_ = l_Lean_Expr_cleanupAnnotations(v_h_6198_);
v___x_6203_ = l_Lean_Expr_isApp(v___x_6202_);
if (v___x_6203_ == 0)
{
lean_dec_ref(v___x_6202_);
goto v___jp_6199_;
}
else
{
lean_object* v_arg_6204_; lean_object* v___x_6205_; uint8_t v___x_6206_; 
v_arg_6204_ = lean_ctor_get(v___x_6202_, 1);
lean_inc_ref(v_arg_6204_);
v___x_6205_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6202_);
v___x_6206_ = l_Lean_Expr_isApp(v___x_6205_);
if (v___x_6206_ == 0)
{
lean_dec_ref(v___x_6205_);
lean_dec_ref(v_arg_6204_);
goto v___jp_6199_;
}
else
{
lean_object* v___x_6207_; lean_object* v___x_6208_; uint8_t v___x_6209_; 
v___x_6207_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6205_);
v___x_6208_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6209_ = l_Lean_Expr_isConstOf(v___x_6207_, v___x_6208_);
lean_dec_ref(v___x_6207_);
if (v___x_6209_ == 0)
{
lean_dec_ref(v_arg_6204_);
goto v___jp_6199_;
}
else
{
lean_dec_ref(v_h_6198_);
lean_dec_ref(v_p_6197_);
return v_arg_6204_;
}
}
}
v___jp_6199_:
{
lean_object* v___x_6200_; lean_object* v___x_6201_; 
v___x_6200_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6201_ = l_Lean_mkAppB(v___x_6200_, v_p_6197_, v_h_6198_);
return v___x_6201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6210_, lean_object* v_a_6211_, lean_object* v_a_6212_, lean_object* v_a_6213_, lean_object* v_a_6214_){
_start:
{
lean_object* v___y_6217_; lean_object* v___y_6218_; lean_object* v___y_6219_; lean_object* v___y_6220_; lean_object* v___x_6226_; 
lean_inc_ref(v_h_6210_);
v___x_6226_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6210_, v_a_6212_);
if (lean_obj_tag(v___x_6226_) == 0)
{
lean_object* v_a_6227_; lean_object* v___x_6229_; uint8_t v_isShared_6230_; uint8_t v_isSharedCheck_6242_; 
v_a_6227_ = lean_ctor_get(v___x_6226_, 0);
v_isSharedCheck_6242_ = !lean_is_exclusive(v___x_6226_);
if (v_isSharedCheck_6242_ == 0)
{
v___x_6229_ = v___x_6226_;
v_isShared_6230_ = v_isSharedCheck_6242_;
goto v_resetjp_6228_;
}
else
{
lean_inc(v_a_6227_);
lean_dec(v___x_6226_);
v___x_6229_ = lean_box(0);
v_isShared_6230_ = v_isSharedCheck_6242_;
goto v_resetjp_6228_;
}
v_resetjp_6228_:
{
lean_object* v___x_6231_; uint8_t v___x_6232_; 
v___x_6231_ = l_Lean_Expr_cleanupAnnotations(v_a_6227_);
v___x_6232_ = l_Lean_Expr_isApp(v___x_6231_);
if (v___x_6232_ == 0)
{
lean_dec_ref(v___x_6231_);
lean_del_object(v___x_6229_);
v___y_6217_ = v_a_6211_;
v___y_6218_ = v_a_6212_;
v___y_6219_ = v_a_6213_;
v___y_6220_ = v_a_6214_;
goto v___jp_6216_;
}
else
{
lean_object* v_arg_6233_; lean_object* v___x_6234_; uint8_t v___x_6235_; 
v_arg_6233_ = lean_ctor_get(v___x_6231_, 1);
lean_inc_ref(v_arg_6233_);
v___x_6234_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6231_);
v___x_6235_ = l_Lean_Expr_isApp(v___x_6234_);
if (v___x_6235_ == 0)
{
lean_dec_ref(v___x_6234_);
lean_dec_ref(v_arg_6233_);
lean_del_object(v___x_6229_);
v___y_6217_ = v_a_6211_;
v___y_6218_ = v_a_6212_;
v___y_6219_ = v_a_6213_;
v___y_6220_ = v_a_6214_;
goto v___jp_6216_;
}
else
{
lean_object* v___x_6236_; lean_object* v___x_6237_; uint8_t v___x_6238_; 
v___x_6236_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6234_);
v___x_6237_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6238_ = l_Lean_Expr_isConstOf(v___x_6236_, v___x_6237_);
lean_dec_ref(v___x_6236_);
if (v___x_6238_ == 0)
{
lean_dec_ref(v_arg_6233_);
lean_del_object(v___x_6229_);
v___y_6217_ = v_a_6211_;
v___y_6218_ = v_a_6212_;
v___y_6219_ = v_a_6213_;
v___y_6220_ = v_a_6214_;
goto v___jp_6216_;
}
else
{
lean_object* v___x_6240_; 
lean_dec_ref(v_h_6210_);
if (v_isShared_6230_ == 0)
{
lean_ctor_set(v___x_6229_, 0, v_arg_6233_);
v___x_6240_ = v___x_6229_;
goto v_reusejp_6239_;
}
else
{
lean_object* v_reuseFailAlloc_6241_; 
v_reuseFailAlloc_6241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6241_, 0, v_arg_6233_);
v___x_6240_ = v_reuseFailAlloc_6241_;
goto v_reusejp_6239_;
}
v_reusejp_6239_:
{
return v___x_6240_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6210_);
return v___x_6226_;
}
v___jp_6216_:
{
lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; lean_object* v___x_6225_; 
v___x_6221_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6222_ = lean_unsigned_to_nat(1u);
v___x_6223_ = lean_mk_empty_array_with_capacity(v___x_6222_);
v___x_6224_ = lean_array_push(v___x_6223_, v_h_6210_);
v___x_6225_ = l_Lean_Meta_mkAppM(v___x_6221_, v___x_6224_, v___y_6217_, v___y_6218_, v___y_6219_, v___y_6220_);
return v___x_6225_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6243_, lean_object* v_a_6244_, lean_object* v_a_6245_, lean_object* v_a_6246_, lean_object* v_a_6247_, lean_object* v_a_6248_){
_start:
{
lean_object* v_res_6249_; 
v_res_6249_ = l_Lean_Meta_mkOfEqTrue(v_h_6243_, v_a_6244_, v_a_6245_, v_a_6246_, v_a_6247_);
lean_dec(v_a_6247_);
lean_dec_ref(v_a_6246_);
lean_dec(v_a_6245_);
lean_dec_ref(v_a_6244_);
return v_res_6249_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6250_; lean_object* v___x_6251_; lean_object* v___x_6252_; 
v___x_6250_ = lean_box(0);
v___x_6251_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6252_ = l_Lean_mkConst(v___x_6251_, v___x_6250_);
return v___x_6252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6253_, lean_object* v_h_6254_){
_start:
{
lean_object* v___x_6258_; uint8_t v___x_6259_; 
lean_inc_ref(v_h_6254_);
v___x_6258_ = l_Lean_Expr_cleanupAnnotations(v_h_6254_);
v___x_6259_ = l_Lean_Expr_isApp(v___x_6258_);
if (v___x_6259_ == 0)
{
lean_dec_ref(v___x_6258_);
goto v___jp_6255_;
}
else
{
lean_object* v_arg_6260_; lean_object* v___x_6261_; uint8_t v___x_6262_; 
v_arg_6260_ = lean_ctor_get(v___x_6258_, 1);
lean_inc_ref(v_arg_6260_);
v___x_6261_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6258_);
v___x_6262_ = l_Lean_Expr_isApp(v___x_6261_);
if (v___x_6262_ == 0)
{
lean_dec_ref(v___x_6261_);
lean_dec_ref(v_arg_6260_);
goto v___jp_6255_;
}
else
{
lean_object* v___x_6263_; lean_object* v___x_6264_; uint8_t v___x_6265_; 
v___x_6263_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6261_);
v___x_6264_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6265_ = l_Lean_Expr_isConstOf(v___x_6263_, v___x_6264_);
lean_dec_ref(v___x_6263_);
if (v___x_6265_ == 0)
{
lean_dec_ref(v_arg_6260_);
goto v___jp_6255_;
}
else
{
lean_dec_ref(v_h_6254_);
lean_dec_ref(v_p_6253_);
return v_arg_6260_;
}
}
}
v___jp_6255_:
{
lean_object* v___x_6256_; lean_object* v___x_6257_; 
v___x_6256_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6257_ = l_Lean_mkAppB(v___x_6256_, v_p_6253_, v_h_6254_);
return v___x_6257_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6266_, lean_object* v_a_6267_, lean_object* v_a_6268_, lean_object* v_a_6269_, lean_object* v_a_6270_){
_start:
{
lean_object* v___y_6273_; lean_object* v___y_6274_; lean_object* v___y_6275_; lean_object* v___y_6276_; lean_object* v___x_6288_; 
lean_inc_ref(v_h_6266_);
v___x_6288_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6266_, v_a_6268_);
if (lean_obj_tag(v___x_6288_) == 0)
{
lean_object* v_a_6289_; lean_object* v___x_6291_; uint8_t v_isShared_6292_; uint8_t v_isSharedCheck_6304_; 
v_a_6289_ = lean_ctor_get(v___x_6288_, 0);
v_isSharedCheck_6304_ = !lean_is_exclusive(v___x_6288_);
if (v_isSharedCheck_6304_ == 0)
{
v___x_6291_ = v___x_6288_;
v_isShared_6292_ = v_isSharedCheck_6304_;
goto v_resetjp_6290_;
}
else
{
lean_inc(v_a_6289_);
lean_dec(v___x_6288_);
v___x_6291_ = lean_box(0);
v_isShared_6292_ = v_isSharedCheck_6304_;
goto v_resetjp_6290_;
}
v_resetjp_6290_:
{
lean_object* v___x_6293_; uint8_t v___x_6294_; 
v___x_6293_ = l_Lean_Expr_cleanupAnnotations(v_a_6289_);
v___x_6294_ = l_Lean_Expr_isApp(v___x_6293_);
if (v___x_6294_ == 0)
{
lean_dec_ref(v___x_6293_);
lean_del_object(v___x_6291_);
v___y_6273_ = v_a_6267_;
v___y_6274_ = v_a_6268_;
v___y_6275_ = v_a_6269_;
v___y_6276_ = v_a_6270_;
goto v___jp_6272_;
}
else
{
lean_object* v_arg_6295_; lean_object* v___x_6296_; uint8_t v___x_6297_; 
v_arg_6295_ = lean_ctor_get(v___x_6293_, 1);
lean_inc_ref(v_arg_6295_);
v___x_6296_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6293_);
v___x_6297_ = l_Lean_Expr_isApp(v___x_6296_);
if (v___x_6297_ == 0)
{
lean_dec_ref(v___x_6296_);
lean_dec_ref(v_arg_6295_);
lean_del_object(v___x_6291_);
v___y_6273_ = v_a_6267_;
v___y_6274_ = v_a_6268_;
v___y_6275_ = v_a_6269_;
v___y_6276_ = v_a_6270_;
goto v___jp_6272_;
}
else
{
lean_object* v___x_6298_; lean_object* v___x_6299_; uint8_t v___x_6300_; 
v___x_6298_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6296_);
v___x_6299_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6300_ = l_Lean_Expr_isConstOf(v___x_6298_, v___x_6299_);
lean_dec_ref(v___x_6298_);
if (v___x_6300_ == 0)
{
lean_dec_ref(v_arg_6295_);
lean_del_object(v___x_6291_);
v___y_6273_ = v_a_6267_;
v___y_6274_ = v_a_6268_;
v___y_6275_ = v_a_6269_;
v___y_6276_ = v_a_6270_;
goto v___jp_6272_;
}
else
{
lean_object* v___x_6302_; 
lean_dec_ref(v_h_6266_);
if (v_isShared_6292_ == 0)
{
lean_ctor_set(v___x_6291_, 0, v_arg_6295_);
v___x_6302_ = v___x_6291_;
goto v_reusejp_6301_;
}
else
{
lean_object* v_reuseFailAlloc_6303_; 
v_reuseFailAlloc_6303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6303_, 0, v_arg_6295_);
v___x_6302_ = v_reuseFailAlloc_6303_;
goto v_reusejp_6301_;
}
v_reusejp_6301_:
{
return v___x_6302_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6266_);
return v___x_6288_;
}
v___jp_6272_:
{
lean_object* v___x_6277_; 
lean_inc(v___y_6276_);
lean_inc_ref(v___y_6275_);
lean_inc(v___y_6274_);
lean_inc_ref(v___y_6273_);
lean_inc_ref(v_h_6266_);
v___x_6277_ = lean_infer_type(v_h_6266_, v___y_6273_, v___y_6274_, v___y_6275_, v___y_6276_);
if (lean_obj_tag(v___x_6277_) == 0)
{
lean_object* v_a_6278_; lean_object* v___x_6280_; uint8_t v_isShared_6281_; uint8_t v_isSharedCheck_6287_; 
v_a_6278_ = lean_ctor_get(v___x_6277_, 0);
v_isSharedCheck_6287_ = !lean_is_exclusive(v___x_6277_);
if (v_isSharedCheck_6287_ == 0)
{
v___x_6280_ = v___x_6277_;
v_isShared_6281_ = v_isSharedCheck_6287_;
goto v_resetjp_6279_;
}
else
{
lean_inc(v_a_6278_);
lean_dec(v___x_6277_);
v___x_6280_ = lean_box(0);
v_isShared_6281_ = v_isSharedCheck_6287_;
goto v_resetjp_6279_;
}
v_resetjp_6279_:
{
lean_object* v___x_6282_; lean_object* v___x_6283_; lean_object* v___x_6285_; 
v___x_6282_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6283_ = l_Lean_mkAppB(v___x_6282_, v_a_6278_, v_h_6266_);
if (v_isShared_6281_ == 0)
{
lean_ctor_set(v___x_6280_, 0, v___x_6283_);
v___x_6285_ = v___x_6280_;
goto v_reusejp_6284_;
}
else
{
lean_object* v_reuseFailAlloc_6286_; 
v_reuseFailAlloc_6286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6286_, 0, v___x_6283_);
v___x_6285_ = v_reuseFailAlloc_6286_;
goto v_reusejp_6284_;
}
v_reusejp_6284_:
{
return v___x_6285_;
}
}
}
else
{
lean_dec_ref(v_h_6266_);
return v___x_6277_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6305_, lean_object* v_a_6306_, lean_object* v_a_6307_, lean_object* v_a_6308_, lean_object* v_a_6309_, lean_object* v_a_6310_){
_start:
{
lean_object* v_res_6311_; 
v_res_6311_ = l_Lean_Meta_mkEqTrue(v_h_6305_, v_a_6306_, v_a_6307_, v_a_6308_, v_a_6309_);
lean_dec(v_a_6309_);
lean_dec_ref(v_a_6308_);
lean_dec(v_a_6307_);
lean_dec_ref(v_a_6306_);
return v_res_6311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_){
_start:
{
lean_object* v___y_6319_; lean_object* v___y_6320_; lean_object* v___y_6321_; lean_object* v___y_6322_; lean_object* v___x_6328_; uint8_t v___x_6329_; 
lean_inc_ref(v_h_6312_);
v___x_6328_ = l_Lean_Expr_cleanupAnnotations(v_h_6312_);
v___x_6329_ = l_Lean_Expr_isApp(v___x_6328_);
if (v___x_6329_ == 0)
{
lean_dec_ref(v___x_6328_);
v___y_6319_ = v_a_6313_;
v___y_6320_ = v_a_6314_;
v___y_6321_ = v_a_6315_;
v___y_6322_ = v_a_6316_;
goto v___jp_6318_;
}
else
{
lean_object* v_arg_6330_; lean_object* v___x_6331_; uint8_t v___x_6332_; 
v_arg_6330_ = lean_ctor_get(v___x_6328_, 1);
lean_inc_ref(v_arg_6330_);
v___x_6331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6328_);
v___x_6332_ = l_Lean_Expr_isApp(v___x_6331_);
if (v___x_6332_ == 0)
{
lean_dec_ref(v___x_6331_);
lean_dec_ref(v_arg_6330_);
v___y_6319_ = v_a_6313_;
v___y_6320_ = v_a_6314_;
v___y_6321_ = v_a_6315_;
v___y_6322_ = v_a_6316_;
goto v___jp_6318_;
}
else
{
lean_object* v___x_6333_; lean_object* v___x_6334_; uint8_t v___x_6335_; 
v___x_6333_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6331_);
v___x_6334_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6335_ = l_Lean_Expr_isConstOf(v___x_6333_, v___x_6334_);
lean_dec_ref(v___x_6333_);
if (v___x_6335_ == 0)
{
lean_dec_ref(v_arg_6330_);
v___y_6319_ = v_a_6313_;
v___y_6320_ = v_a_6314_;
v___y_6321_ = v_a_6315_;
v___y_6322_ = v_a_6316_;
goto v___jp_6318_;
}
else
{
lean_object* v___x_6336_; 
lean_dec_ref(v_h_6312_);
v___x_6336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6336_, 0, v_arg_6330_);
return v___x_6336_;
}
}
}
v___jp_6318_:
{
lean_object* v___x_6323_; lean_object* v___x_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v___x_6327_; 
v___x_6323_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6324_ = lean_unsigned_to_nat(1u);
v___x_6325_ = lean_mk_empty_array_with_capacity(v___x_6324_);
v___x_6326_ = lean_array_push(v___x_6325_, v_h_6312_);
v___x_6327_ = l_Lean_Meta_mkAppM(v___x_6323_, v___x_6326_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_);
return v___x_6327_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6337_, lean_object* v_a_6338_, lean_object* v_a_6339_, lean_object* v_a_6340_, lean_object* v_a_6341_, lean_object* v_a_6342_){
_start:
{
lean_object* v_res_6343_; 
v_res_6343_ = l_Lean_Meta_mkEqFalse(v_h_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_);
lean_dec(v_a_6341_);
lean_dec_ref(v_a_6340_);
lean_dec(v_a_6339_);
lean_dec_ref(v_a_6338_);
return v_res_6343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6347_, lean_object* v_a_6348_, lean_object* v_a_6349_, lean_object* v_a_6350_, lean_object* v_a_6351_){
_start:
{
lean_object* v___x_6353_; lean_object* v___x_6354_; lean_object* v___x_6355_; lean_object* v___x_6356_; lean_object* v___x_6357_; 
v___x_6353_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6354_ = lean_unsigned_to_nat(1u);
v___x_6355_ = lean_mk_empty_array_with_capacity(v___x_6354_);
v___x_6356_ = lean_array_push(v___x_6355_, v_h_6347_);
v___x_6357_ = l_Lean_Meta_mkAppM(v___x_6353_, v___x_6356_, v_a_6348_, v_a_6349_, v_a_6350_, v_a_6351_);
return v___x_6357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6358_, lean_object* v_a_6359_, lean_object* v_a_6360_, lean_object* v_a_6361_, lean_object* v_a_6362_, lean_object* v_a_6363_){
_start:
{
lean_object* v_res_6364_; 
v_res_6364_ = l_Lean_Meta_mkEqFalse_x27(v_h_6358_, v_a_6359_, v_a_6360_, v_a_6361_, v_a_6362_);
lean_dec(v_a_6362_);
lean_dec_ref(v_a_6361_);
lean_dec(v_a_6360_);
lean_dec_ref(v_a_6359_);
return v_res_6364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6368_, lean_object* v_h_u2082_6369_, lean_object* v_a_6370_, lean_object* v_a_6371_, lean_object* v_a_6372_, lean_object* v_a_6373_){
_start:
{
lean_object* v___x_6375_; lean_object* v___x_6376_; lean_object* v___x_6377_; lean_object* v___x_6378_; lean_object* v___x_6379_; lean_object* v___x_6380_; 
v___x_6375_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6376_ = lean_unsigned_to_nat(2u);
v___x_6377_ = lean_mk_empty_array_with_capacity(v___x_6376_);
v___x_6378_ = lean_array_push(v___x_6377_, v_h_u2081_6368_);
v___x_6379_ = lean_array_push(v___x_6378_, v_h_u2082_6369_);
v___x_6380_ = l_Lean_Meta_mkAppM(v___x_6375_, v___x_6379_, v_a_6370_, v_a_6371_, v_a_6372_, v_a_6373_);
return v___x_6380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6381_, lean_object* v_h_u2082_6382_, lean_object* v_a_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_){
_start:
{
lean_object* v_res_6388_; 
v_res_6388_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6381_, v_h_u2082_6382_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_);
lean_dec(v_a_6386_);
lean_dec_ref(v_a_6385_);
lean_dec(v_a_6384_);
lean_dec_ref(v_a_6383_);
return v_res_6388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6392_, lean_object* v_h_u2082_6393_, lean_object* v_a_6394_, lean_object* v_a_6395_, lean_object* v_a_6396_, lean_object* v_a_6397_){
_start:
{
lean_object* v___x_6399_; lean_object* v___x_6400_; lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; 
v___x_6399_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6400_ = lean_unsigned_to_nat(2u);
v___x_6401_ = lean_mk_empty_array_with_capacity(v___x_6400_);
v___x_6402_ = lean_array_push(v___x_6401_, v_h_u2081_6392_);
v___x_6403_ = lean_array_push(v___x_6402_, v_h_u2082_6393_);
v___x_6404_ = l_Lean_Meta_mkAppM(v___x_6399_, v___x_6403_, v_a_6394_, v_a_6395_, v_a_6396_, v_a_6397_);
return v___x_6404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6405_, lean_object* v_h_u2082_6406_, lean_object* v_a_6407_, lean_object* v_a_6408_, lean_object* v_a_6409_, lean_object* v_a_6410_, lean_object* v_a_6411_){
_start:
{
lean_object* v_res_6412_; 
v_res_6412_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6405_, v_h_u2082_6406_, v_a_6407_, v_a_6408_, v_a_6409_, v_a_6410_);
lean_dec(v_a_6410_);
lean_dec_ref(v_a_6409_);
lean_dec(v_a_6408_);
lean_dec_ref(v_a_6407_);
return v_res_6412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6416_, lean_object* v_h_u2082_6417_, lean_object* v_a_6418_, lean_object* v_a_6419_, lean_object* v_a_6420_, lean_object* v_a_6421_){
_start:
{
lean_object* v___x_6423_; lean_object* v___x_6424_; lean_object* v___x_6425_; lean_object* v___x_6426_; lean_object* v___x_6427_; lean_object* v___x_6428_; 
v___x_6423_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6424_ = lean_unsigned_to_nat(2u);
v___x_6425_ = lean_mk_empty_array_with_capacity(v___x_6424_);
v___x_6426_ = lean_array_push(v___x_6425_, v_h_u2081_6416_);
v___x_6427_ = lean_array_push(v___x_6426_, v_h_u2082_6417_);
v___x_6428_ = l_Lean_Meta_mkAppM(v___x_6423_, v___x_6427_, v_a_6418_, v_a_6419_, v_a_6420_, v_a_6421_);
return v___x_6428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6429_, lean_object* v_h_u2082_6430_, lean_object* v_a_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_, lean_object* v_a_6435_){
_start:
{
lean_object* v_res_6436_; 
v_res_6436_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6429_, v_h_u2082_6430_, v_a_6431_, v_a_6432_, v_a_6433_, v_a_6434_);
lean_dec(v_a_6434_);
lean_dec_ref(v_a_6433_);
lean_dec(v_a_6432_);
lean_dec_ref(v_a_6431_);
return v_res_6436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6440_, lean_object* v_a_6441_, lean_object* v_a_6442_, lean_object* v_a_6443_, lean_object* v_a_6444_){
_start:
{
lean_object* v___x_6446_; lean_object* v___x_6447_; lean_object* v___x_6448_; lean_object* v___x_6449_; lean_object* v___x_6450_; 
v___x_6446_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6447_ = lean_unsigned_to_nat(1u);
v___x_6448_ = lean_mk_empty_array_with_capacity(v___x_6447_);
v___x_6449_ = lean_array_push(v___x_6448_, v_h_6440_);
v___x_6450_ = l_Lean_Meta_mkAppM(v___x_6446_, v___x_6449_, v_a_6441_, v_a_6442_, v_a_6443_, v_a_6444_);
return v___x_6450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6451_, lean_object* v_a_6452_, lean_object* v_a_6453_, lean_object* v_a_6454_, lean_object* v_a_6455_, lean_object* v_a_6456_){
_start:
{
lean_object* v_res_6457_; 
v_res_6457_ = l_Lean_Meta_mkForallCongr(v_h_6451_, v_a_6452_, v_a_6453_, v_a_6454_, v_a_6455_);
lean_dec(v_a_6455_);
lean_dec_ref(v_a_6454_);
lean_dec(v_a_6453_);
lean_dec_ref(v_a_6452_);
return v_res_6457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_){
_start:
{
lean_object* v___y_6468_; lean_object* v_a_6469_; lean_object* v___x_6474_; lean_object* v___x_6475_; lean_object* v___x_6476_; lean_object* v___x_6477_; lean_object* v___x_6478_; 
v___x_6474_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6475_ = lean_unsigned_to_nat(1u);
v___x_6476_ = lean_mk_empty_array_with_capacity(v___x_6475_);
v___x_6477_ = lean_array_push(v___x_6476_, v_m_6461_);
v___x_6478_ = l_Lean_Meta_mkAppM(v___x_6474_, v___x_6477_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_);
if (lean_obj_tag(v___x_6478_) == 0)
{
lean_object* v_a_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; 
v_a_6479_ = lean_ctor_get(v___x_6478_, 0);
lean_inc(v_a_6479_);
lean_dec_ref_known(v___x_6478_, 1);
v___x_6480_ = lean_box(0);
v___x_6481_ = l_Lean_Meta_trySynthInstance(v_a_6479_, v___x_6480_, v_a_6462_, v_a_6463_, v_a_6464_, v_a_6465_);
if (lean_obj_tag(v___x_6481_) == 0)
{
lean_object* v_a_6482_; lean_object* v___x_6484_; uint8_t v_isShared_6485_; uint8_t v_isSharedCheck_6500_; 
v_a_6482_ = lean_ctor_get(v___x_6481_, 0);
v_isSharedCheck_6500_ = !lean_is_exclusive(v___x_6481_);
if (v_isSharedCheck_6500_ == 0)
{
v___x_6484_ = v___x_6481_;
v_isShared_6485_ = v_isSharedCheck_6500_;
goto v_resetjp_6483_;
}
else
{
lean_inc(v_a_6482_);
lean_dec(v___x_6481_);
v___x_6484_ = lean_box(0);
v_isShared_6485_ = v_isSharedCheck_6500_;
goto v_resetjp_6483_;
}
v_resetjp_6483_:
{
if (lean_obj_tag(v_a_6482_) == 1)
{
lean_object* v_a_6486_; lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6496_; 
v_a_6486_ = lean_ctor_get(v_a_6482_, 0);
v_isSharedCheck_6496_ = !lean_is_exclusive(v_a_6482_);
if (v_isSharedCheck_6496_ == 0)
{
v___x_6488_ = v_a_6482_;
v_isShared_6489_ = v_isSharedCheck_6496_;
goto v_resetjp_6487_;
}
else
{
lean_inc(v_a_6486_);
lean_dec(v_a_6482_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6496_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
lean_object* v___x_6491_; 
if (v_isShared_6489_ == 0)
{
v___x_6491_ = v___x_6488_;
goto v_reusejp_6490_;
}
else
{
lean_object* v_reuseFailAlloc_6495_; 
v_reuseFailAlloc_6495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6495_, 0, v_a_6486_);
v___x_6491_ = v_reuseFailAlloc_6495_;
goto v_reusejp_6490_;
}
v_reusejp_6490_:
{
lean_object* v___x_6493_; 
if (v_isShared_6485_ == 0)
{
lean_ctor_set(v___x_6484_, 0, v___x_6491_);
v___x_6493_ = v___x_6484_;
goto v_reusejp_6492_;
}
else
{
lean_object* v_reuseFailAlloc_6494_; 
v_reuseFailAlloc_6494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6494_, 0, v___x_6491_);
v___x_6493_ = v_reuseFailAlloc_6494_;
goto v_reusejp_6492_;
}
v_reusejp_6492_:
{
return v___x_6493_;
}
}
}
}
else
{
lean_object* v___x_6498_; 
lean_dec(v_a_6482_);
if (v_isShared_6485_ == 0)
{
lean_ctor_set(v___x_6484_, 0, v___x_6480_);
v___x_6498_ = v___x_6484_;
goto v_reusejp_6497_;
}
else
{
lean_object* v_reuseFailAlloc_6499_; 
v_reuseFailAlloc_6499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6499_, 0, v___x_6480_);
v___x_6498_ = v_reuseFailAlloc_6499_;
goto v_reusejp_6497_;
}
v_reusejp_6497_:
{
return v___x_6498_;
}
}
}
}
else
{
lean_object* v_a_6501_; lean_object* v___x_6503_; uint8_t v_isShared_6504_; uint8_t v_isSharedCheck_6508_; 
v_a_6501_ = lean_ctor_get(v___x_6481_, 0);
v_isSharedCheck_6508_ = !lean_is_exclusive(v___x_6481_);
if (v_isSharedCheck_6508_ == 0)
{
v___x_6503_ = v___x_6481_;
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
else
{
lean_inc(v_a_6501_);
lean_dec(v___x_6481_);
v___x_6503_ = lean_box(0);
v_isShared_6504_ = v_isSharedCheck_6508_;
goto v_resetjp_6502_;
}
v_resetjp_6502_:
{
lean_object* v___x_6506_; 
lean_inc(v_a_6501_);
if (v_isShared_6504_ == 0)
{
v___x_6506_ = v___x_6503_;
goto v_reusejp_6505_;
}
else
{
lean_object* v_reuseFailAlloc_6507_; 
v_reuseFailAlloc_6507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6507_, 0, v_a_6501_);
v___x_6506_ = v_reuseFailAlloc_6507_;
goto v_reusejp_6505_;
}
v_reusejp_6505_:
{
v___y_6468_ = v___x_6506_;
v_a_6469_ = v_a_6501_;
goto v___jp_6467_;
}
}
}
}
else
{
lean_object* v_a_6509_; lean_object* v___x_6511_; uint8_t v_isShared_6512_; uint8_t v_isSharedCheck_6516_; 
v_a_6509_ = lean_ctor_get(v___x_6478_, 0);
v_isSharedCheck_6516_ = !lean_is_exclusive(v___x_6478_);
if (v_isSharedCheck_6516_ == 0)
{
v___x_6511_ = v___x_6478_;
v_isShared_6512_ = v_isSharedCheck_6516_;
goto v_resetjp_6510_;
}
else
{
lean_inc(v_a_6509_);
lean_dec(v___x_6478_);
v___x_6511_ = lean_box(0);
v_isShared_6512_ = v_isSharedCheck_6516_;
goto v_resetjp_6510_;
}
v_resetjp_6510_:
{
lean_object* v___x_6514_; 
lean_inc(v_a_6509_);
if (v_isShared_6512_ == 0)
{
v___x_6514_ = v___x_6511_;
goto v_reusejp_6513_;
}
else
{
lean_object* v_reuseFailAlloc_6515_; 
v_reuseFailAlloc_6515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6515_, 0, v_a_6509_);
v___x_6514_ = v_reuseFailAlloc_6515_;
goto v_reusejp_6513_;
}
v_reusejp_6513_:
{
v___y_6468_ = v___x_6514_;
v_a_6469_ = v_a_6509_;
goto v___jp_6467_;
}
}
}
v___jp_6467_:
{
uint8_t v___x_6470_; 
v___x_6470_ = l_Lean_Exception_isInterrupt(v_a_6469_);
if (v___x_6470_ == 0)
{
uint8_t v___x_6471_; 
v___x_6471_ = l_Lean_Exception_isRuntime(v_a_6469_);
if (v___x_6471_ == 0)
{
lean_object* v___x_6472_; lean_object* v___x_6473_; 
lean_dec_ref(v___y_6468_);
v___x_6472_ = lean_box(0);
v___x_6473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6473_, 0, v___x_6472_);
return v___x_6473_;
}
else
{
return v___y_6468_;
}
}
else
{
lean_dec_ref(v_a_6469_);
return v___y_6468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6517_, lean_object* v_a_6518_, lean_object* v_a_6519_, lean_object* v_a_6520_, lean_object* v_a_6521_, lean_object* v_a_6522_){
_start:
{
lean_object* v_res_6523_; 
v_res_6523_ = l_Lean_Meta_isMonad_x3f(v_m_6517_, v_a_6518_, v_a_6519_, v_a_6520_, v_a_6521_);
lean_dec(v_a_6521_);
lean_dec_ref(v_a_6520_);
lean_dec(v_a_6519_);
lean_dec_ref(v_a_6518_);
return v_res_6523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6531_, lean_object* v_n_6532_, lean_object* v_a_6533_, lean_object* v_a_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_){
_start:
{
lean_object* v___x_6538_; 
lean_inc_ref(v_type_6531_);
v___x_6538_ = l_Lean_Meta_getDecLevel(v_type_6531_, v_a_6533_, v_a_6534_, v_a_6535_, v_a_6536_);
if (lean_obj_tag(v___x_6538_) == 0)
{
lean_object* v_a_6539_; lean_object* v___x_6540_; lean_object* v___x_6541_; lean_object* v___x_6542_; lean_object* v___x_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; 
v_a_6539_ = lean_ctor_get(v___x_6538_, 0);
lean_inc(v_a_6539_);
lean_dec_ref_known(v___x_6538_, 1);
v___x_6540_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6541_ = lean_box(0);
v___x_6542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6542_, 0, v_a_6539_);
lean_ctor_set(v___x_6542_, 1, v___x_6541_);
lean_inc_ref(v___x_6542_);
v___x_6543_ = l_Lean_mkConst(v___x_6540_, v___x_6542_);
v___x_6544_ = l_Lean_mkRawNatLit(v_n_6532_);
lean_inc_ref(v___x_6544_);
lean_inc_ref(v_type_6531_);
v___x_6545_ = l_Lean_mkAppB(v___x_6543_, v_type_6531_, v___x_6544_);
v___x_6546_ = lean_box(0);
v___x_6547_ = l_Lean_Meta_synthInstance(v___x_6545_, v___x_6546_, v_a_6533_, v_a_6534_, v_a_6535_, v_a_6536_);
if (lean_obj_tag(v___x_6547_) == 0)
{
lean_object* v_a_6548_; lean_object* v___x_6550_; uint8_t v_isShared_6551_; uint8_t v_isSharedCheck_6558_; 
v_a_6548_ = lean_ctor_get(v___x_6547_, 0);
v_isSharedCheck_6558_ = !lean_is_exclusive(v___x_6547_);
if (v_isSharedCheck_6558_ == 0)
{
v___x_6550_ = v___x_6547_;
v_isShared_6551_ = v_isSharedCheck_6558_;
goto v_resetjp_6549_;
}
else
{
lean_inc(v_a_6548_);
lean_dec(v___x_6547_);
v___x_6550_ = lean_box(0);
v_isShared_6551_ = v_isSharedCheck_6558_;
goto v_resetjp_6549_;
}
v_resetjp_6549_:
{
lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6556_; 
v___x_6552_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6553_ = l_Lean_mkConst(v___x_6552_, v___x_6542_);
v___x_6554_ = l_Lean_mkApp3(v___x_6553_, v_type_6531_, v___x_6544_, v_a_6548_);
if (v_isShared_6551_ == 0)
{
lean_ctor_set(v___x_6550_, 0, v___x_6554_);
v___x_6556_ = v___x_6550_;
goto v_reusejp_6555_;
}
else
{
lean_object* v_reuseFailAlloc_6557_; 
v_reuseFailAlloc_6557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6557_, 0, v___x_6554_);
v___x_6556_ = v_reuseFailAlloc_6557_;
goto v_reusejp_6555_;
}
v_reusejp_6555_:
{
return v___x_6556_;
}
}
}
else
{
lean_dec_ref(v___x_6544_);
lean_dec_ref_known(v___x_6542_, 2);
lean_dec_ref(v_type_6531_);
return v___x_6547_;
}
}
else
{
lean_object* v_a_6559_; lean_object* v___x_6561_; uint8_t v_isShared_6562_; uint8_t v_isSharedCheck_6566_; 
lean_dec(v_n_6532_);
lean_dec_ref(v_type_6531_);
v_a_6559_ = lean_ctor_get(v___x_6538_, 0);
v_isSharedCheck_6566_ = !lean_is_exclusive(v___x_6538_);
if (v_isSharedCheck_6566_ == 0)
{
v___x_6561_ = v___x_6538_;
v_isShared_6562_ = v_isSharedCheck_6566_;
goto v_resetjp_6560_;
}
else
{
lean_inc(v_a_6559_);
lean_dec(v___x_6538_);
v___x_6561_ = lean_box(0);
v_isShared_6562_ = v_isSharedCheck_6566_;
goto v_resetjp_6560_;
}
v_resetjp_6560_:
{
lean_object* v___x_6564_; 
if (v_isShared_6562_ == 0)
{
v___x_6564_ = v___x_6561_;
goto v_reusejp_6563_;
}
else
{
lean_object* v_reuseFailAlloc_6565_; 
v_reuseFailAlloc_6565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6565_, 0, v_a_6559_);
v___x_6564_ = v_reuseFailAlloc_6565_;
goto v_reusejp_6563_;
}
v_reusejp_6563_:
{
return v___x_6564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6567_, lean_object* v_n_6568_, lean_object* v_a_6569_, lean_object* v_a_6570_, lean_object* v_a_6571_, lean_object* v_a_6572_, lean_object* v_a_6573_){
_start:
{
lean_object* v_res_6574_; 
v_res_6574_ = l_Lean_Meta_mkNumeral(v_type_6567_, v_n_6568_, v_a_6569_, v_a_6570_, v_a_6571_, v_a_6572_);
lean_dec(v_a_6572_);
lean_dec_ref(v_a_6571_);
lean_dec(v_a_6570_);
lean_dec_ref(v_a_6569_);
return v_res_6574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6575_, lean_object* v_opName_6576_, lean_object* v_a_6577_, lean_object* v_b_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_){
_start:
{
lean_object* v___x_6584_; 
lean_inc(v_a_6582_);
lean_inc_ref(v_a_6581_);
lean_inc(v_a_6580_);
lean_inc_ref(v_a_6579_);
lean_inc_ref(v_a_6577_);
v___x_6584_ = lean_infer_type(v_a_6577_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_);
if (lean_obj_tag(v___x_6584_) == 0)
{
lean_object* v_a_6585_; lean_object* v___x_6586_; 
v_a_6585_ = lean_ctor_get(v___x_6584_, 0);
lean_inc_n(v_a_6585_, 2);
lean_dec_ref_known(v___x_6584_, 1);
v___x_6586_ = l_Lean_Meta_getDecLevel(v_a_6585_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_);
if (lean_obj_tag(v___x_6586_) == 0)
{
lean_object* v_a_6587_; lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v___x_6590_; lean_object* v___x_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; 
v_a_6587_ = lean_ctor_get(v___x_6586_, 0);
lean_inc_n(v_a_6587_, 3);
lean_dec_ref_known(v___x_6586_, 1);
v___x_6588_ = lean_box(0);
v___x_6589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6589_, 0, v_a_6587_);
lean_ctor_set(v___x_6589_, 1, v___x_6588_);
v___x_6590_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6590_, 0, v_a_6587_);
lean_ctor_set(v___x_6590_, 1, v___x_6589_);
v___x_6591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6591_, 0, v_a_6587_);
lean_ctor_set(v___x_6591_, 1, v___x_6590_);
lean_inc_ref(v___x_6591_);
v___x_6592_ = l_Lean_mkConst(v_className_6575_, v___x_6591_);
lean_inc_n(v_a_6585_, 3);
v___x_6593_ = l_Lean_mkApp3(v___x_6592_, v_a_6585_, v_a_6585_, v_a_6585_);
v___x_6594_ = lean_box(0);
v___x_6595_ = l_Lean_Meta_synthInstance(v___x_6593_, v___x_6594_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_);
if (lean_obj_tag(v___x_6595_) == 0)
{
lean_object* v_a_6596_; lean_object* v___x_6598_; uint8_t v_isShared_6599_; uint8_t v_isSharedCheck_6605_; 
v_a_6596_ = lean_ctor_get(v___x_6595_, 0);
v_isSharedCheck_6605_ = !lean_is_exclusive(v___x_6595_);
if (v_isSharedCheck_6605_ == 0)
{
v___x_6598_ = v___x_6595_;
v_isShared_6599_ = v_isSharedCheck_6605_;
goto v_resetjp_6597_;
}
else
{
lean_inc(v_a_6596_);
lean_dec(v___x_6595_);
v___x_6598_ = lean_box(0);
v_isShared_6599_ = v_isSharedCheck_6605_;
goto v_resetjp_6597_;
}
v_resetjp_6597_:
{
lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6603_; 
v___x_6600_ = l_Lean_mkConst(v_opName_6576_, v___x_6591_);
lean_inc_n(v_a_6585_, 2);
v___x_6601_ = l_Lean_mkApp6(v___x_6600_, v_a_6585_, v_a_6585_, v_a_6585_, v_a_6596_, v_a_6577_, v_b_6578_);
if (v_isShared_6599_ == 0)
{
lean_ctor_set(v___x_6598_, 0, v___x_6601_);
v___x_6603_ = v___x_6598_;
goto v_reusejp_6602_;
}
else
{
lean_object* v_reuseFailAlloc_6604_; 
v_reuseFailAlloc_6604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6604_, 0, v___x_6601_);
v___x_6603_ = v_reuseFailAlloc_6604_;
goto v_reusejp_6602_;
}
v_reusejp_6602_:
{
return v___x_6603_;
}
}
}
else
{
lean_dec_ref_known(v___x_6591_, 2);
lean_dec(v_a_6585_);
lean_dec_ref(v_b_6578_);
lean_dec_ref(v_a_6577_);
lean_dec(v_opName_6576_);
return v___x_6595_;
}
}
else
{
lean_object* v_a_6606_; lean_object* v___x_6608_; uint8_t v_isShared_6609_; uint8_t v_isSharedCheck_6613_; 
lean_dec(v_a_6585_);
lean_dec_ref(v_b_6578_);
lean_dec_ref(v_a_6577_);
lean_dec(v_opName_6576_);
lean_dec(v_className_6575_);
v_a_6606_ = lean_ctor_get(v___x_6586_, 0);
v_isSharedCheck_6613_ = !lean_is_exclusive(v___x_6586_);
if (v_isSharedCheck_6613_ == 0)
{
v___x_6608_ = v___x_6586_;
v_isShared_6609_ = v_isSharedCheck_6613_;
goto v_resetjp_6607_;
}
else
{
lean_inc(v_a_6606_);
lean_dec(v___x_6586_);
v___x_6608_ = lean_box(0);
v_isShared_6609_ = v_isSharedCheck_6613_;
goto v_resetjp_6607_;
}
v_resetjp_6607_:
{
lean_object* v___x_6611_; 
if (v_isShared_6609_ == 0)
{
v___x_6611_ = v___x_6608_;
goto v_reusejp_6610_;
}
else
{
lean_object* v_reuseFailAlloc_6612_; 
v_reuseFailAlloc_6612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6612_, 0, v_a_6606_);
v___x_6611_ = v_reuseFailAlloc_6612_;
goto v_reusejp_6610_;
}
v_reusejp_6610_:
{
return v___x_6611_;
}
}
}
}
else
{
lean_dec_ref(v_b_6578_);
lean_dec_ref(v_a_6577_);
lean_dec(v_opName_6576_);
lean_dec(v_className_6575_);
return v___x_6584_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6614_, lean_object* v_opName_6615_, lean_object* v_a_6616_, lean_object* v_b_6617_, lean_object* v_a_6618_, lean_object* v_a_6619_, lean_object* v_a_6620_, lean_object* v_a_6621_, lean_object* v_a_6622_){
_start:
{
lean_object* v_res_6623_; 
v_res_6623_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6614_, v_opName_6615_, v_a_6616_, v_b_6617_, v_a_6618_, v_a_6619_, v_a_6620_, v_a_6621_);
lean_dec(v_a_6621_);
lean_dec_ref(v_a_6620_);
lean_dec(v_a_6619_);
lean_dec_ref(v_a_6618_);
return v_res_6623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6631_, lean_object* v_b_6632_, lean_object* v_a_6633_, lean_object* v_a_6634_, lean_object* v_a_6635_, lean_object* v_a_6636_){
_start:
{
lean_object* v___x_6638_; lean_object* v___x_6639_; lean_object* v___x_6640_; 
v___x_6638_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6639_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6640_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6638_, v___x_6639_, v_a_6631_, v_b_6632_, v_a_6633_, v_a_6634_, v_a_6635_, v_a_6636_);
return v___x_6640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6641_, lean_object* v_b_6642_, lean_object* v_a_6643_, lean_object* v_a_6644_, lean_object* v_a_6645_, lean_object* v_a_6646_, lean_object* v_a_6647_){
_start:
{
lean_object* v_res_6648_; 
v_res_6648_ = l_Lean_Meta_mkAdd(v_a_6641_, v_b_6642_, v_a_6643_, v_a_6644_, v_a_6645_, v_a_6646_);
lean_dec(v_a_6646_);
lean_dec_ref(v_a_6645_);
lean_dec(v_a_6644_);
lean_dec_ref(v_a_6643_);
return v_res_6648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6656_, lean_object* v_b_6657_, lean_object* v_a_6658_, lean_object* v_a_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_){
_start:
{
lean_object* v___x_6663_; lean_object* v___x_6664_; lean_object* v___x_6665_; 
v___x_6663_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6664_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6665_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6663_, v___x_6664_, v_a_6656_, v_b_6657_, v_a_6658_, v_a_6659_, v_a_6660_, v_a_6661_);
return v___x_6665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6666_, lean_object* v_b_6667_, lean_object* v_a_6668_, lean_object* v_a_6669_, lean_object* v_a_6670_, lean_object* v_a_6671_, lean_object* v_a_6672_){
_start:
{
lean_object* v_res_6673_; 
v_res_6673_ = l_Lean_Meta_mkSub(v_a_6666_, v_b_6667_, v_a_6668_, v_a_6669_, v_a_6670_, v_a_6671_);
lean_dec(v_a_6671_);
lean_dec_ref(v_a_6670_);
lean_dec(v_a_6669_);
lean_dec_ref(v_a_6668_);
return v_res_6673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6681_, lean_object* v_b_6682_, lean_object* v_a_6683_, lean_object* v_a_6684_, lean_object* v_a_6685_, lean_object* v_a_6686_){
_start:
{
lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; 
v___x_6688_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6689_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6690_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6688_, v___x_6689_, v_a_6681_, v_b_6682_, v_a_6683_, v_a_6684_, v_a_6685_, v_a_6686_);
return v___x_6690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6691_, lean_object* v_b_6692_, lean_object* v_a_6693_, lean_object* v_a_6694_, lean_object* v_a_6695_, lean_object* v_a_6696_, lean_object* v_a_6697_){
_start:
{
lean_object* v_res_6698_; 
v_res_6698_ = l_Lean_Meta_mkMul(v_a_6691_, v_b_6692_, v_a_6693_, v_a_6694_, v_a_6695_, v_a_6696_);
lean_dec(v_a_6696_);
lean_dec_ref(v_a_6695_);
lean_dec(v_a_6694_);
lean_dec_ref(v_a_6693_);
return v_res_6698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6699_, lean_object* v_rName_6700_, lean_object* v_a_6701_, lean_object* v_b_6702_, lean_object* v_a_6703_, lean_object* v_a_6704_, lean_object* v_a_6705_, lean_object* v_a_6706_){
_start:
{
lean_object* v___x_6708_; 
lean_inc(v_a_6706_);
lean_inc_ref(v_a_6705_);
lean_inc(v_a_6704_);
lean_inc_ref(v_a_6703_);
lean_inc_ref(v_a_6701_);
v___x_6708_ = lean_infer_type(v_a_6701_, v_a_6703_, v_a_6704_, v_a_6705_, v_a_6706_);
if (lean_obj_tag(v___x_6708_) == 0)
{
lean_object* v_a_6709_; lean_object* v___x_6710_; 
v_a_6709_ = lean_ctor_get(v___x_6708_, 0);
lean_inc_n(v_a_6709_, 2);
lean_dec_ref_known(v___x_6708_, 1);
v___x_6710_ = l_Lean_Meta_getDecLevel(v_a_6709_, v_a_6703_, v_a_6704_, v_a_6705_, v_a_6706_);
if (lean_obj_tag(v___x_6710_) == 0)
{
lean_object* v_a_6711_; lean_object* v___x_6712_; lean_object* v___x_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; 
v_a_6711_ = lean_ctor_get(v___x_6710_, 0);
lean_inc(v_a_6711_);
lean_dec_ref_known(v___x_6710_, 1);
v___x_6712_ = lean_box(0);
v___x_6713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6713_, 0, v_a_6711_);
lean_ctor_set(v___x_6713_, 1, v___x_6712_);
lean_inc_ref(v___x_6713_);
v___x_6714_ = l_Lean_mkConst(v_className_6699_, v___x_6713_);
lean_inc(v_a_6709_);
v___x_6715_ = l_Lean_Expr_app___override(v___x_6714_, v_a_6709_);
v___x_6716_ = lean_box(0);
v___x_6717_ = l_Lean_Meta_synthInstance(v___x_6715_, v___x_6716_, v_a_6703_, v_a_6704_, v_a_6705_, v_a_6706_);
if (lean_obj_tag(v___x_6717_) == 0)
{
lean_object* v_a_6718_; lean_object* v___x_6720_; uint8_t v_isShared_6721_; uint8_t v_isSharedCheck_6727_; 
v_a_6718_ = lean_ctor_get(v___x_6717_, 0);
v_isSharedCheck_6727_ = !lean_is_exclusive(v___x_6717_);
if (v_isSharedCheck_6727_ == 0)
{
v___x_6720_ = v___x_6717_;
v_isShared_6721_ = v_isSharedCheck_6727_;
goto v_resetjp_6719_;
}
else
{
lean_inc(v_a_6718_);
lean_dec(v___x_6717_);
v___x_6720_ = lean_box(0);
v_isShared_6721_ = v_isSharedCheck_6727_;
goto v_resetjp_6719_;
}
v_resetjp_6719_:
{
lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6725_; 
v___x_6722_ = l_Lean_mkConst(v_rName_6700_, v___x_6713_);
v___x_6723_ = l_Lean_mkApp4(v___x_6722_, v_a_6709_, v_a_6718_, v_a_6701_, v_b_6702_);
if (v_isShared_6721_ == 0)
{
lean_ctor_set(v___x_6720_, 0, v___x_6723_);
v___x_6725_ = v___x_6720_;
goto v_reusejp_6724_;
}
else
{
lean_object* v_reuseFailAlloc_6726_; 
v_reuseFailAlloc_6726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6726_, 0, v___x_6723_);
v___x_6725_ = v_reuseFailAlloc_6726_;
goto v_reusejp_6724_;
}
v_reusejp_6724_:
{
return v___x_6725_;
}
}
}
else
{
lean_dec_ref_known(v___x_6713_, 2);
lean_dec(v_a_6709_);
lean_dec_ref(v_b_6702_);
lean_dec_ref(v_a_6701_);
lean_dec(v_rName_6700_);
return v___x_6717_;
}
}
else
{
lean_object* v_a_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6735_; 
lean_dec(v_a_6709_);
lean_dec_ref(v_b_6702_);
lean_dec_ref(v_a_6701_);
lean_dec(v_rName_6700_);
lean_dec(v_className_6699_);
v_a_6728_ = lean_ctor_get(v___x_6710_, 0);
v_isSharedCheck_6735_ = !lean_is_exclusive(v___x_6710_);
if (v_isSharedCheck_6735_ == 0)
{
v___x_6730_ = v___x_6710_;
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6710_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6735_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v___x_6733_; 
if (v_isShared_6731_ == 0)
{
v___x_6733_ = v___x_6730_;
goto v_reusejp_6732_;
}
else
{
lean_object* v_reuseFailAlloc_6734_; 
v_reuseFailAlloc_6734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6734_, 0, v_a_6728_);
v___x_6733_ = v_reuseFailAlloc_6734_;
goto v_reusejp_6732_;
}
v_reusejp_6732_:
{
return v___x_6733_;
}
}
}
}
else
{
lean_dec_ref(v_b_6702_);
lean_dec_ref(v_a_6701_);
lean_dec(v_rName_6700_);
lean_dec(v_className_6699_);
return v___x_6708_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6736_, lean_object* v_rName_6737_, lean_object* v_a_6738_, lean_object* v_b_6739_, lean_object* v_a_6740_, lean_object* v_a_6741_, lean_object* v_a_6742_, lean_object* v_a_6743_, lean_object* v_a_6744_){
_start:
{
lean_object* v_res_6745_; 
v_res_6745_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6736_, v_rName_6737_, v_a_6738_, v_b_6739_, v_a_6740_, v_a_6741_, v_a_6742_, v_a_6743_);
lean_dec(v_a_6743_);
lean_dec_ref(v_a_6742_);
lean_dec(v_a_6741_);
lean_dec_ref(v_a_6740_);
return v_res_6745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6748_, lean_object* v_b_6749_, lean_object* v_a_6750_, lean_object* v_a_6751_, lean_object* v_a_6752_, lean_object* v_a_6753_){
_start:
{
lean_object* v___x_6755_; lean_object* v___x_6756_; lean_object* v___x_6757_; 
v___x_6755_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6756_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6757_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6755_, v___x_6756_, v_a_6748_, v_b_6749_, v_a_6750_, v_a_6751_, v_a_6752_, v_a_6753_);
return v___x_6757_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6758_, lean_object* v_b_6759_, lean_object* v_a_6760_, lean_object* v_a_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_, lean_object* v_a_6764_){
_start:
{
lean_object* v_res_6765_; 
v_res_6765_ = l_Lean_Meta_mkLE(v_a_6758_, v_b_6759_, v_a_6760_, v_a_6761_, v_a_6762_, v_a_6763_);
lean_dec(v_a_6763_);
lean_dec_ref(v_a_6762_);
lean_dec(v_a_6761_);
lean_dec_ref(v_a_6760_);
return v_res_6765_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6768_, lean_object* v_b_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_, lean_object* v_a_6773_){
_start:
{
lean_object* v___x_6775_; lean_object* v___x_6776_; lean_object* v___x_6777_; 
v___x_6775_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6776_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6777_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6775_, v___x_6776_, v_a_6768_, v_b_6769_, v_a_6770_, v_a_6771_, v_a_6772_, v_a_6773_);
return v___x_6777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6778_, lean_object* v_b_6779_, lean_object* v_a_6780_, lean_object* v_a_6781_, lean_object* v_a_6782_, lean_object* v_a_6783_, lean_object* v_a_6784_){
_start:
{
lean_object* v_res_6785_; 
v_res_6785_ = l_Lean_Meta_mkLT(v_a_6778_, v_b_6779_, v_a_6780_, v_a_6781_, v_a_6782_, v_a_6783_);
lean_dec(v_a_6783_);
lean_dec_ref(v_a_6782_);
lean_dec(v_a_6781_);
lean_dec_ref(v_a_6780_);
return v_res_6785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6791_, lean_object* v_a_6792_, lean_object* v_a_6793_, lean_object* v_a_6794_, lean_object* v_a_6795_){
_start:
{
lean_object* v___x_6797_; lean_object* v___x_6798_; uint8_t v___x_6799_; 
v___x_6797_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6798_ = lean_unsigned_to_nat(3u);
v___x_6799_ = l_Lean_Expr_isAppOfArity(v_h_6791_, v___x_6797_, v___x_6798_);
if (v___x_6799_ == 0)
{
lean_object* v___x_6800_; lean_object* v___x_6801_; lean_object* v___x_6802_; lean_object* v___x_6803_; lean_object* v___x_6804_; 
v___x_6800_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6801_ = lean_unsigned_to_nat(1u);
v___x_6802_ = lean_mk_empty_array_with_capacity(v___x_6801_);
v___x_6803_ = lean_array_push(v___x_6802_, v_h_6791_);
v___x_6804_ = l_Lean_Meta_mkAppM(v___x_6800_, v___x_6803_, v_a_6792_, v_a_6793_, v_a_6794_, v_a_6795_);
return v___x_6804_;
}
else
{
lean_object* v___x_6805_; lean_object* v___x_6806_; 
v___x_6805_ = l_Lean_Expr_appArg_x21(v_h_6791_);
lean_dec_ref(v_h_6791_);
v___x_6806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6806_, 0, v___x_6805_);
return v___x_6806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6807_, lean_object* v_a_6808_, lean_object* v_a_6809_, lean_object* v_a_6810_, lean_object* v_a_6811_, lean_object* v_a_6812_){
_start:
{
lean_object* v_res_6813_; 
v_res_6813_ = l_Lean_Meta_mkIffOfEq(v_h_6807_, v_a_6808_, v_a_6809_, v_a_6810_, v_a_6811_);
lean_dec(v_a_6811_);
lean_dec_ref(v_a_6810_);
lean_dec(v_a_6809_);
lean_dec_ref(v_a_6808_);
return v_res_6813_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; 
v___x_6819_ = lean_box(0);
v___x_6820_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6821_ = l_Lean_mkConst(v___x_6820_, v___x_6819_);
return v___x_6821_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6824_; lean_object* v___x_6825_; lean_object* v___x_6826_; 
v___x_6824_ = lean_box(0);
v___x_6825_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6826_ = l_Lean_mkConst(v___x_6825_, v___x_6824_);
return v___x_6826_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6827_; lean_object* v___x_6828_; lean_object* v___x_6829_; 
v___x_6827_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6828_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6829_, 0, v___x_6828_);
lean_ctor_set(v___x_6829_, 1, v___x_6827_);
return v___x_6829_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6834_; lean_object* v___x_6835_; lean_object* v___x_6836_; 
v___x_6834_ = lean_box(0);
v___x_6835_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6836_ = l_Lean_mkConst(v___x_6835_, v___x_6834_);
return v___x_6836_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6839_; lean_object* v___x_6840_; lean_object* v___x_6841_; 
v___x_6839_ = lean_box(0);
v___x_6840_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6841_ = l_Lean_mkConst(v___x_6840_, v___x_6839_);
return v___x_6841_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6842_, lean_object* v_a_6843_, lean_object* v_a_6844_, lean_object* v_a_6845_, lean_object* v_a_6846_){
_start:
{
if (lean_obj_tag(v_a_6842_) == 0)
{
lean_object* v___x_6848_; lean_object* v___x_6849_; 
v___x_6848_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6849_, 0, v___x_6848_);
return v___x_6849_;
}
else
{
lean_object* v_tail_6850_; 
v_tail_6850_ = lean_ctor_get(v_a_6842_, 1);
if (lean_obj_tag(v_tail_6850_) == 0)
{
lean_object* v_head_6851_; lean_object* v___x_6853_; uint8_t v_isShared_6854_; uint8_t v_isSharedCheck_6875_; 
v_head_6851_ = lean_ctor_get(v_a_6842_, 0);
v_isSharedCheck_6875_ = !lean_is_exclusive(v_a_6842_);
if (v_isSharedCheck_6875_ == 0)
{
lean_object* v_unused_6876_; 
v_unused_6876_ = lean_ctor_get(v_a_6842_, 1);
lean_dec(v_unused_6876_);
v___x_6853_ = v_a_6842_;
v_isShared_6854_ = v_isSharedCheck_6875_;
goto v_resetjp_6852_;
}
else
{
lean_inc(v_head_6851_);
lean_dec(v_a_6842_);
v___x_6853_ = lean_box(0);
v_isShared_6854_ = v_isSharedCheck_6875_;
goto v_resetjp_6852_;
}
v_resetjp_6852_:
{
lean_object* v___x_6855_; 
lean_inc(v_a_6846_);
lean_inc_ref(v_a_6845_);
lean_inc(v_a_6844_);
lean_inc_ref(v_a_6843_);
lean_inc(v_head_6851_);
v___x_6855_ = lean_infer_type(v_head_6851_, v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_);
if (lean_obj_tag(v___x_6855_) == 0)
{
lean_object* v_a_6856_; lean_object* v___x_6858_; uint8_t v_isShared_6859_; uint8_t v_isSharedCheck_6866_; 
v_a_6856_ = lean_ctor_get(v___x_6855_, 0);
v_isSharedCheck_6866_ = !lean_is_exclusive(v___x_6855_);
if (v_isSharedCheck_6866_ == 0)
{
v___x_6858_ = v___x_6855_;
v_isShared_6859_ = v_isSharedCheck_6866_;
goto v_resetjp_6857_;
}
else
{
lean_inc(v_a_6856_);
lean_dec(v___x_6855_);
v___x_6858_ = lean_box(0);
v_isShared_6859_ = v_isSharedCheck_6866_;
goto v_resetjp_6857_;
}
v_resetjp_6857_:
{
lean_object* v___x_6861_; 
if (v_isShared_6854_ == 0)
{
lean_ctor_set_tag(v___x_6853_, 0);
lean_ctor_set(v___x_6853_, 1, v_a_6856_);
v___x_6861_ = v___x_6853_;
goto v_reusejp_6860_;
}
else
{
lean_object* v_reuseFailAlloc_6865_; 
v_reuseFailAlloc_6865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6865_, 0, v_head_6851_);
lean_ctor_set(v_reuseFailAlloc_6865_, 1, v_a_6856_);
v___x_6861_ = v_reuseFailAlloc_6865_;
goto v_reusejp_6860_;
}
v_reusejp_6860_:
{
lean_object* v___x_6863_; 
if (v_isShared_6859_ == 0)
{
lean_ctor_set(v___x_6858_, 0, v___x_6861_);
v___x_6863_ = v___x_6858_;
goto v_reusejp_6862_;
}
else
{
lean_object* v_reuseFailAlloc_6864_; 
v_reuseFailAlloc_6864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6864_, 0, v___x_6861_);
v___x_6863_ = v_reuseFailAlloc_6864_;
goto v_reusejp_6862_;
}
v_reusejp_6862_:
{
return v___x_6863_;
}
}
}
}
else
{
lean_object* v_a_6867_; lean_object* v___x_6869_; uint8_t v_isShared_6870_; uint8_t v_isSharedCheck_6874_; 
lean_del_object(v___x_6853_);
lean_dec(v_head_6851_);
v_a_6867_ = lean_ctor_get(v___x_6855_, 0);
v_isSharedCheck_6874_ = !lean_is_exclusive(v___x_6855_);
if (v_isSharedCheck_6874_ == 0)
{
v___x_6869_ = v___x_6855_;
v_isShared_6870_ = v_isSharedCheck_6874_;
goto v_resetjp_6868_;
}
else
{
lean_inc(v_a_6867_);
lean_dec(v___x_6855_);
v___x_6869_ = lean_box(0);
v_isShared_6870_ = v_isSharedCheck_6874_;
goto v_resetjp_6868_;
}
v_resetjp_6868_:
{
lean_object* v___x_6872_; 
if (v_isShared_6870_ == 0)
{
v___x_6872_ = v___x_6869_;
goto v_reusejp_6871_;
}
else
{
lean_object* v_reuseFailAlloc_6873_; 
v_reuseFailAlloc_6873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6873_, 0, v_a_6867_);
v___x_6872_ = v_reuseFailAlloc_6873_;
goto v_reusejp_6871_;
}
v_reusejp_6871_:
{
return v___x_6872_;
}
}
}
}
}
else
{
lean_object* v_head_6877_; lean_object* v___x_6878_; 
lean_inc(v_tail_6850_);
v_head_6877_ = lean_ctor_get(v_a_6842_, 0);
lean_inc(v_head_6877_);
lean_dec_ref_known(v_a_6842_, 2);
v___x_6878_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6850_, v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_);
if (lean_obj_tag(v___x_6878_) == 0)
{
lean_object* v_a_6879_; lean_object* v_fst_6880_; lean_object* v_snd_6881_; lean_object* v___x_6883_; uint8_t v_isShared_6884_; uint8_t v_isSharedCheck_6909_; 
v_a_6879_ = lean_ctor_get(v___x_6878_, 0);
lean_inc(v_a_6879_);
lean_dec_ref_known(v___x_6878_, 1);
v_fst_6880_ = lean_ctor_get(v_a_6879_, 0);
v_snd_6881_ = lean_ctor_get(v_a_6879_, 1);
v_isSharedCheck_6909_ = !lean_is_exclusive(v_a_6879_);
if (v_isSharedCheck_6909_ == 0)
{
v___x_6883_ = v_a_6879_;
v_isShared_6884_ = v_isSharedCheck_6909_;
goto v_resetjp_6882_;
}
else
{
lean_inc(v_snd_6881_);
lean_inc(v_fst_6880_);
lean_dec(v_a_6879_);
v___x_6883_ = lean_box(0);
v_isShared_6884_ = v_isSharedCheck_6909_;
goto v_resetjp_6882_;
}
v_resetjp_6882_:
{
lean_object* v___x_6885_; 
lean_inc(v_a_6846_);
lean_inc_ref(v_a_6845_);
lean_inc(v_a_6844_);
lean_inc_ref(v_a_6843_);
lean_inc(v_head_6877_);
v___x_6885_ = lean_infer_type(v_head_6877_, v_a_6843_, v_a_6844_, v_a_6845_, v_a_6846_);
if (lean_obj_tag(v___x_6885_) == 0)
{
lean_object* v_a_6886_; lean_object* v___x_6888_; uint8_t v_isShared_6889_; uint8_t v_isSharedCheck_6900_; 
v_a_6886_ = lean_ctor_get(v___x_6885_, 0);
v_isSharedCheck_6900_ = !lean_is_exclusive(v___x_6885_);
if (v_isSharedCheck_6900_ == 0)
{
v___x_6888_ = v___x_6885_;
v_isShared_6889_ = v_isSharedCheck_6900_;
goto v_resetjp_6887_;
}
else
{
lean_inc(v_a_6886_);
lean_dec(v___x_6885_);
v___x_6888_ = lean_box(0);
v_isShared_6889_ = v_isSharedCheck_6900_;
goto v_resetjp_6887_;
}
v_resetjp_6887_:
{
lean_object* v___x_6890_; lean_object* v___x_6891_; lean_object* v___x_6892_; lean_object* v___x_6893_; lean_object* v___x_6895_; 
v___x_6890_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6881_);
lean_inc(v_a_6886_);
v___x_6891_ = l_Lean_mkApp4(v___x_6890_, v_a_6886_, v_snd_6881_, v_head_6877_, v_fst_6880_);
v___x_6892_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6893_ = l_Lean_mkAppB(v___x_6892_, v_a_6886_, v_snd_6881_);
if (v_isShared_6884_ == 0)
{
lean_ctor_set(v___x_6883_, 1, v___x_6893_);
lean_ctor_set(v___x_6883_, 0, v___x_6891_);
v___x_6895_ = v___x_6883_;
goto v_reusejp_6894_;
}
else
{
lean_object* v_reuseFailAlloc_6899_; 
v_reuseFailAlloc_6899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6899_, 0, v___x_6891_);
lean_ctor_set(v_reuseFailAlloc_6899_, 1, v___x_6893_);
v___x_6895_ = v_reuseFailAlloc_6899_;
goto v_reusejp_6894_;
}
v_reusejp_6894_:
{
lean_object* v___x_6897_; 
if (v_isShared_6889_ == 0)
{
lean_ctor_set(v___x_6888_, 0, v___x_6895_);
v___x_6897_ = v___x_6888_;
goto v_reusejp_6896_;
}
else
{
lean_object* v_reuseFailAlloc_6898_; 
v_reuseFailAlloc_6898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6898_, 0, v___x_6895_);
v___x_6897_ = v_reuseFailAlloc_6898_;
goto v_reusejp_6896_;
}
v_reusejp_6896_:
{
return v___x_6897_;
}
}
}
}
else
{
lean_object* v_a_6901_; lean_object* v___x_6903_; uint8_t v_isShared_6904_; uint8_t v_isSharedCheck_6908_; 
lean_del_object(v___x_6883_);
lean_dec(v_snd_6881_);
lean_dec(v_fst_6880_);
lean_dec(v_head_6877_);
v_a_6901_ = lean_ctor_get(v___x_6885_, 0);
v_isSharedCheck_6908_ = !lean_is_exclusive(v___x_6885_);
if (v_isSharedCheck_6908_ == 0)
{
v___x_6903_ = v___x_6885_;
v_isShared_6904_ = v_isSharedCheck_6908_;
goto v_resetjp_6902_;
}
else
{
lean_inc(v_a_6901_);
lean_dec(v___x_6885_);
v___x_6903_ = lean_box(0);
v_isShared_6904_ = v_isSharedCheck_6908_;
goto v_resetjp_6902_;
}
v_resetjp_6902_:
{
lean_object* v___x_6906_; 
if (v_isShared_6904_ == 0)
{
v___x_6906_ = v___x_6903_;
goto v_reusejp_6905_;
}
else
{
lean_object* v_reuseFailAlloc_6907_; 
v_reuseFailAlloc_6907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6907_, 0, v_a_6901_);
v___x_6906_ = v_reuseFailAlloc_6907_;
goto v_reusejp_6905_;
}
v_reusejp_6905_:
{
return v___x_6906_;
}
}
}
}
}
else
{
lean_dec(v_head_6877_);
return v___x_6878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6910_, lean_object* v_a_6911_, lean_object* v_a_6912_, lean_object* v_a_6913_, lean_object* v_a_6914_, lean_object* v_a_6915_){
_start:
{
lean_object* v_res_6916_; 
v_res_6916_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6910_, v_a_6911_, v_a_6912_, v_a_6913_, v_a_6914_);
lean_dec(v_a_6914_);
lean_dec_ref(v_a_6913_);
lean_dec(v_a_6912_);
lean_dec_ref(v_a_6911_);
return v_res_6916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6917_, lean_object* v_a_6918_, lean_object* v_a_6919_, lean_object* v_a_6920_, lean_object* v_a_6921_){
_start:
{
lean_object* v___x_6923_; 
v___x_6923_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6917_, v_a_6918_, v_a_6919_, v_a_6920_, v_a_6921_);
if (lean_obj_tag(v___x_6923_) == 0)
{
lean_object* v_a_6924_; lean_object* v___x_6926_; uint8_t v_isShared_6927_; uint8_t v_isSharedCheck_6932_; 
v_a_6924_ = lean_ctor_get(v___x_6923_, 0);
v_isSharedCheck_6932_ = !lean_is_exclusive(v___x_6923_);
if (v_isSharedCheck_6932_ == 0)
{
v___x_6926_ = v___x_6923_;
v_isShared_6927_ = v_isSharedCheck_6932_;
goto v_resetjp_6925_;
}
else
{
lean_inc(v_a_6924_);
lean_dec(v___x_6923_);
v___x_6926_ = lean_box(0);
v_isShared_6927_ = v_isSharedCheck_6932_;
goto v_resetjp_6925_;
}
v_resetjp_6925_:
{
lean_object* v_fst_6928_; lean_object* v___x_6930_; 
v_fst_6928_ = lean_ctor_get(v_a_6924_, 0);
lean_inc(v_fst_6928_);
lean_dec(v_a_6924_);
if (v_isShared_6927_ == 0)
{
lean_ctor_set(v___x_6926_, 0, v_fst_6928_);
v___x_6930_ = v___x_6926_;
goto v_reusejp_6929_;
}
else
{
lean_object* v_reuseFailAlloc_6931_; 
v_reuseFailAlloc_6931_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6931_, 0, v_fst_6928_);
v___x_6930_ = v_reuseFailAlloc_6931_;
goto v_reusejp_6929_;
}
v_reusejp_6929_:
{
return v___x_6930_;
}
}
}
else
{
lean_object* v_a_6933_; lean_object* v___x_6935_; uint8_t v_isShared_6936_; uint8_t v_isSharedCheck_6940_; 
v_a_6933_ = lean_ctor_get(v___x_6923_, 0);
v_isSharedCheck_6940_ = !lean_is_exclusive(v___x_6923_);
if (v_isSharedCheck_6940_ == 0)
{
v___x_6935_ = v___x_6923_;
v_isShared_6936_ = v_isSharedCheck_6940_;
goto v_resetjp_6934_;
}
else
{
lean_inc(v_a_6933_);
lean_dec(v___x_6923_);
v___x_6935_ = lean_box(0);
v_isShared_6936_ = v_isSharedCheck_6940_;
goto v_resetjp_6934_;
}
v_resetjp_6934_:
{
lean_object* v___x_6938_; 
if (v_isShared_6936_ == 0)
{
v___x_6938_ = v___x_6935_;
goto v_reusejp_6937_;
}
else
{
lean_object* v_reuseFailAlloc_6939_; 
v_reuseFailAlloc_6939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6939_, 0, v_a_6933_);
v___x_6938_ = v_reuseFailAlloc_6939_;
goto v_reusejp_6937_;
}
v_reusejp_6937_:
{
return v___x_6938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_6941_, lean_object* v_a_6942_, lean_object* v_a_6943_, lean_object* v_a_6944_, lean_object* v_a_6945_, lean_object* v_a_6946_){
_start:
{
lean_object* v_res_6947_; 
v_res_6947_ = l_Lean_Meta_mkAndIntroN(v_hs_6941_, v_a_6942_, v_a_6943_, v_a_6944_, v_a_6945_);
lean_dec(v_a_6945_);
lean_dec_ref(v_a_6944_);
lean_dec(v_a_6943_);
lean_dec_ref(v_a_6942_);
return v_res_6947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7004_; uint8_t v___x_7005_; lean_object* v___x_7006_; lean_object* v___x_7007_; 
v___x_7004_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7005_ = 0;
v___x_7006_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7007_ = l_Lean_registerTraceClass(v___x_7004_, v___x_7005_, v___x_7006_);
if (lean_obj_tag(v___x_7007_) == 0)
{
lean_object* v___x_7008_; uint8_t v___x_7009_; lean_object* v___x_7010_; 
lean_dec_ref_known(v___x_7007_, 1);
v___x_7008_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7009_ = 1;
v___x_7010_ = l_Lean_registerTraceClass(v___x_7008_, v___x_7009_, v___x_7006_);
if (lean_obj_tag(v___x_7010_) == 0)
{
lean_object* v___x_7011_; lean_object* v___x_7012_; 
lean_dec_ref_known(v___x_7010_, 1);
v___x_7011_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7012_ = l_Lean_registerTraceClass(v___x_7011_, v___x_7009_, v___x_7006_);
return v___x_7012_;
}
else
{
return v___x_7010_;
}
}
else
{
return v___x_7007_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7013_){
_start:
{
lean_object* v_res_7014_; 
v_res_7014_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7014_;
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
