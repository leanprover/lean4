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
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_MessageData_arrayExpr_toMessageData(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_inlineExpr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_instExceptToTraceResultExpr___lam__0___boxed(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_ReaderT_instMonadFunctor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_instMonadEIO(lean_object*);
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
lean_object* l_ReaderT_instMonadLift___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadExceptOfEIO(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(lean_object*);
lean_object* l_Lean_instMonadAlwaysExceptReaderT___redArg(lean_object*);
extern lean_object* l_Lean_Meta_instAddMessageContextMetaM;
lean_object* l_Lean_addTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_KVMap_instValueBool;
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
static const lean_string_object l_Lean_Meta_mkEqTrans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trans"};
static const lean_object* l_Lean_Meta_mkEqTrans___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqTrans___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqTrans___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqTrans___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqTrans___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqTrans___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 40, 198, 234, 16, 168, 79, 243)}};
static const lean_object* l_Lean_Meta_mkEqTrans___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqTrans___closed__1_value;
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
static const lean_ctor_object l_Lean_Meta_mkHEqTrans___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkHEqTrans___closed__0_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqTrans___closed__0_value),LEAN_SCALAR_PTR_LITERAL(137, 23, 102, 245, 235, 101, 160, 50)}};
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
static const lean_closure_object l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadLift___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6_value;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7 = (const lean_object*)&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8;
static lean_once_cell_t l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9;
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_instMonadFunctor___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_closure_object l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instExceptToTraceResultExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
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
static const lean_string_object l_Lean_Meta_mkEqMP___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mp"};
static const lean_object* l_Lean_Meta_mkEqMP___closed__0 = (const lean_object*)&l_Lean_Meta_mkEqMP___closed__0_value;
static const lean_ctor_object l_Lean_Meta_mkEqMP___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_mkEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_mkEqMP___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_mkEqMP___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_mkEqMP___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 66, 254, 161, 210, 133, 94, 78)}};
static const lean_object* l_Lean_Meta_mkEqMP___closed__1 = (const lean_object*)&l_Lean_Meta_mkEqMP___closed__1_value;
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "inductive type expected"};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__5 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__5_value;
static const lean_ctor_object l_Lean_Meta_mkNoConfusion___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_mkNoConfusion___closed__5_value)}};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__6 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__6_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__7;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "mkNoConfusion: No manifest constructors in "};
static const lean_object* l_Lean_Meta_mkNoConfusion___closed__8 = (const lean_object*)&l_Lean_Meta_mkNoConfusion___closed__8_value;
static lean_once_cell_t l_Lean_Meta_mkNoConfusion___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_mkNoConfusion___closed__9;
static const lean_string_object l_Lean_Meta_mkNoConfusion___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " = "};
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
lean_object* v___x_431_; lean_object* v_env_432_; lean_object* v___x_433_; lean_object* v_mctx_434_; lean_object* v_lctx_435_; lean_object* v_options_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_431_ = lean_st_ref_get(v___y_429_);
v_env_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_env_432_);
lean_dec(v___x_431_);
v___x_433_ = lean_st_ref_get(v___y_427_);
v_mctx_434_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_mctx_434_);
lean_dec(v___x_433_);
v_lctx_435_ = lean_ctor_get(v___y_426_, 2);
v_options_436_ = lean_ctor_get(v___y_428_, 2);
lean_inc_ref(v_options_436_);
lean_inc_ref(v_lctx_435_);
v___x_437_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_437_, 0, v_env_432_);
lean_ctor_set(v___x_437_, 1, v_mctx_434_);
lean_ctor_set(v___x_437_, 2, v_lctx_435_);
lean_ctor_set(v___x_437_, 3, v_options_436_);
v___x_438_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_msgData_425_);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0___boxed(lean_object* v_msgData_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msgData_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(lean_object* v_msg_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_ref_453_; lean_object* v___x_454_; lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_463_; 
v_ref_453_ = lean_ctor_get(v___y_450_, 5);
v___x_454_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_463_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_463_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_459_; lean_object* v___x_461_; 
lean_inc(v_ref_453_);
v___x_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_459_, 0, v_ref_453_);
lean_ctor_set(v___x_459_, 1, v_a_455_);
if (v_isShared_458_ == 0)
{
lean_ctor_set_tag(v___x_457_, 1);
lean_ctor_set(v___x_457_, 0, v___x_459_);
v___x_461_ = v___x_457_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg___boxed(lean_object* v_msg_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_){
_start:
{
lean_object* v_res_470_; 
v_res_470_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
lean_dec_ref(v___y_465_);
return v_res_470_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1(void){
_start:
{
lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_472_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__0));
v___x_473_ = l_Lean_stringToMessageData(v___x_472_);
return v___x_473_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3(void){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__2));
v___x_476_ = l_Lean_stringToMessageData(v___x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(lean_object* v_op_477_, lean_object* v_msg_478_, lean_object* v_a_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_484_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1);
v___x_485_ = l_Lean_MessageData_ofName(v_op_477_);
v___x_486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_484_);
lean_ctor_set(v___x_486_, 1, v___x_485_);
v___x_487_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3);
v___x_488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_486_);
lean_ctor_set(v___x_488_, 1, v___x_487_);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_488_);
lean_ctor_set(v___x_489_, 1, v_msg_478_);
v___x_490_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_489_, v_a_479_, v_a_480_, v_a_481_, v_a_482_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___boxed(lean_object* v_op_491_, lean_object* v_msg_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_op_491_, v_msg_492_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec(v_a_496_);
lean_dec_ref(v_a_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_a_493_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object* v_00_u03b1_499_, lean_object* v_op_500_, lean_object* v_msg_501_, lean_object* v_a_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_op_500_, v_msg_501_, v_a_502_, v_a_503_, v_a_504_, v_a_505_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___boxed(lean_object* v_00_u03b1_508_, lean_object* v_op_509_, lean_object* v_msg_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_){
_start:
{
lean_object* v_res_516_; 
v_res_516_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(v_00_u03b1_508_, v_op_509_, v_msg_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
lean_dec(v_a_514_);
lean_dec_ref(v_a_513_);
lean_dec(v_a_512_);
lean_dec_ref(v_a_511_);
return v_res_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0(lean_object* v_00_u03b1_517_, lean_object* v_msg_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___boxed(lean_object* v_00_u03b1_525_, lean_object* v_msg_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0(v_00_u03b1_525_, v_msg_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
return v_res_532_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__4(void){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_540_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__3));
v___x_541_ = l_Lean_MessageData_ofFormat(v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object* v_h_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; uint8_t v___x_549_; 
v___x_548_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_549_ = l_Lean_Expr_isAppOf(v_h_542_, v___x_548_);
if (v___x_549_ == 0)
{
lean_object* v___x_550_; 
lean_inc_ref(v_h_542_);
v___x_550_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_542_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
if (lean_obj_tag(v___x_550_) == 0)
{
lean_object* v_a_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v_a_551_ = lean_ctor_get(v___x_550_, 0);
lean_inc(v_a_551_);
lean_dec_ref_known(v___x_550_, 1);
v___x_552_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_553_ = lean_unsigned_to_nat(3u);
v___x_554_ = l_Lean_Expr_isAppOfArity(v_a_551_, v___x_552_, v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; 
v___x_555_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__1));
v___x_556_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_557_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_542_, v_a_551_);
v___x_558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_556_);
lean_ctor_set(v___x_558_, 1, v___x_557_);
v___x_559_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_555_, v___x_558_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
return v___x_559_;
}
else
{
lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_560_ = l_Lean_Expr_appFn_x21(v_a_551_);
v___x_561_ = l_Lean_Expr_appFn_x21(v___x_560_);
v___x_562_ = l_Lean_Expr_appArg_x21(v___x_561_);
lean_dec_ref(v___x_561_);
lean_inc_ref(v___x_562_);
v___x_563_ = l_Lean_Meta_getLevel(v___x_562_, v_a_543_, v_a_544_, v_a_545_, v_a_546_);
if (lean_obj_tag(v___x_563_) == 0)
{
lean_object* v_a_564_; lean_object* v___x_566_; uint8_t v_isShared_567_; uint8_t v_isSharedCheck_578_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_578_ == 0)
{
v___x_566_ = v___x_563_;
v_isShared_567_ = v_isSharedCheck_578_;
goto v_resetjp_565_;
}
else
{
lean_inc(v_a_564_);
lean_dec(v___x_563_);
v___x_566_ = lean_box(0);
v_isShared_567_ = v_isSharedCheck_578_;
goto v_resetjp_565_;
}
v_resetjp_565_:
{
lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_576_; 
v___x_568_ = l_Lean_Expr_appArg_x21(v___x_560_);
lean_dec_ref(v___x_560_);
v___x_569_ = l_Lean_Expr_appArg_x21(v_a_551_);
lean_dec(v_a_551_);
v___x_570_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__1));
v___x_571_ = lean_box(0);
v___x_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_572_, 0, v_a_564_);
lean_ctor_set(v___x_572_, 1, v___x_571_);
v___x_573_ = l_Lean_mkConst(v___x_570_, v___x_572_);
v___x_574_ = l_Lean_mkApp4(v___x_573_, v___x_562_, v___x_568_, v___x_569_, v_h_542_);
if (v_isShared_567_ == 0)
{
lean_ctor_set(v___x_566_, 0, v___x_574_);
v___x_576_ = v___x_566_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
else
{
lean_object* v_a_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_586_; 
lean_dec_ref(v___x_562_);
lean_dec_ref(v___x_560_);
lean_dec(v_a_551_);
lean_dec_ref(v_h_542_);
v_a_579_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_586_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_586_ == 0)
{
v___x_581_ = v___x_563_;
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_a_579_);
lean_dec(v___x_563_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_586_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_584_; 
if (v_isShared_582_ == 0)
{
v___x_584_ = v___x_581_;
goto v_reusejp_583_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_a_579_);
v___x_584_ = v_reuseFailAlloc_585_;
goto v_reusejp_583_;
}
v_reusejp_583_:
{
return v___x_584_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_542_);
return v___x_550_;
}
}
else
{
lean_object* v___x_587_; 
v___x_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_587_, 0, v_h_542_);
return v___x_587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm___boxed(lean_object* v_h_588_, lean_object* v_a_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Meta_mkEqSymm(v_h_588_, v_a_589_, v_a_590_, v_a_591_, v_a_592_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
lean_dec(v_a_590_);
lean_dec_ref(v_a_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object* v_h_u2081_599_, lean_object* v_h_u2082_600_, lean_object* v_a_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_){
_start:
{
lean_object* v___x_606_; uint8_t v___x_607_; 
v___x_606_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_607_ = l_Lean_Expr_isAppOf(v_h_u2081_599_, v___x_606_);
if (v___x_607_ == 0)
{
uint8_t v___x_608_; 
v___x_608_ = l_Lean_Expr_isAppOf(v_h_u2082_600_, v___x_606_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; 
lean_inc_ref(v_h_u2081_599_);
v___x_609_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_599_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_609_) == 0)
{
lean_object* v_a_610_; lean_object* v___x_611_; 
v_a_610_ = lean_ctor_get(v___x_609_, 0);
lean_inc(v_a_610_);
lean_dec_ref_known(v___x_609_, 1);
lean_inc_ref(v_h_u2082_600_);
v___x_611_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_600_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_611_) == 0)
{
lean_object* v_a_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; 
v_a_612_ = lean_ctor_get(v___x_611_, 0);
lean_inc(v_a_612_);
lean_dec_ref_known(v___x_611_, 1);
v___x_613_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_614_ = lean_unsigned_to_nat(3u);
v___x_615_ = l_Lean_Expr_isAppOfArity(v_a_610_, v___x_613_, v___x_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_a_612_);
lean_dec_ref(v_h_u2082_600_);
v___x_616_ = ((lean_object*)(l_Lean_Meta_mkEqTrans___closed__1));
v___x_617_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_618_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_599_, v_a_610_);
v___x_619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_617_);
lean_ctor_set(v___x_619_, 1, v___x_618_);
v___x_620_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_616_, v___x_619_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_620_;
}
else
{
uint8_t v___x_621_; 
v___x_621_ = l_Lean_Expr_isAppOfArity(v_a_612_, v___x_613_, v___x_614_);
if (v___x_621_ == 0)
{
lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
lean_dec(v_a_610_);
lean_dec_ref(v_h_u2081_599_);
v___x_622_ = ((lean_object*)(l_Lean_Meta_mkEqTrans___closed__1));
v___x_623_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_624_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_600_, v_a_612_);
v___x_625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_625_, 0, v___x_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
v___x_626_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_622_, v___x_625_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
return v___x_626_;
}
else
{
lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_627_ = l_Lean_Expr_appFn_x21(v_a_610_);
v___x_628_ = l_Lean_Expr_appFn_x21(v___x_627_);
v___x_629_ = l_Lean_Expr_appArg_x21(v___x_628_);
lean_dec_ref(v___x_628_);
lean_inc_ref(v___x_629_);
v___x_630_ = l_Lean_Meta_getLevel(v___x_629_, v_a_601_, v_a_602_, v_a_603_, v_a_604_);
if (lean_obj_tag(v___x_630_) == 0)
{
lean_object* v_a_631_; lean_object* v___x_633_; uint8_t v_isShared_634_; uint8_t v_isSharedCheck_646_; 
v_a_631_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_646_ == 0)
{
v___x_633_ = v___x_630_;
v_isShared_634_ = v_isSharedCheck_646_;
goto v_resetjp_632_;
}
else
{
lean_inc(v_a_631_);
lean_dec(v___x_630_);
v___x_633_ = lean_box(0);
v_isShared_634_ = v_isSharedCheck_646_;
goto v_resetjp_632_;
}
v_resetjp_632_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_635_ = l_Lean_Expr_appArg_x21(v___x_627_);
lean_dec_ref(v___x_627_);
v___x_636_ = l_Lean_Expr_appArg_x21(v_a_610_);
lean_dec(v_a_610_);
v___x_637_ = l_Lean_Expr_appArg_x21(v_a_612_);
lean_dec(v_a_612_);
v___x_638_ = ((lean_object*)(l_Lean_Meta_mkEqTrans___closed__1));
v___x_639_ = lean_box(0);
v___x_640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_640_, 0, v_a_631_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
v___x_641_ = l_Lean_mkConst(v___x_638_, v___x_640_);
v___x_642_ = l_Lean_mkApp6(v___x_641_, v___x_629_, v___x_635_, v___x_636_, v___x_637_, v_h_u2081_599_, v_h_u2082_600_);
if (v_isShared_634_ == 0)
{
lean_ctor_set(v___x_633_, 0, v___x_642_);
v___x_644_ = v___x_633_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_642_);
v___x_644_ = v_reuseFailAlloc_645_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
return v___x_644_;
}
}
}
else
{
lean_object* v_a_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_654_; 
lean_dec_ref(v___x_629_);
lean_dec_ref(v___x_627_);
lean_dec(v_a_612_);
lean_dec(v_a_610_);
lean_dec_ref(v_h_u2082_600_);
lean_dec_ref(v_h_u2081_599_);
v_a_647_ = lean_ctor_get(v___x_630_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_630_);
if (v_isSharedCheck_654_ == 0)
{
v___x_649_ = v___x_630_;
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_a_647_);
lean_dec(v___x_630_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_654_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_652_; 
if (v_isShared_650_ == 0)
{
v___x_652_ = v___x_649_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_a_647_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
}
else
{
lean_dec(v_a_610_);
lean_dec_ref(v_h_u2082_600_);
lean_dec_ref(v_h_u2081_599_);
return v___x_611_;
}
}
else
{
lean_dec_ref(v_h_u2082_600_);
lean_dec_ref(v_h_u2081_599_);
return v___x_609_;
}
}
else
{
lean_object* v___x_655_; 
lean_dec_ref(v_h_u2082_600_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_h_u2081_599_);
return v___x_655_;
}
}
else
{
lean_object* v___x_656_; 
lean_dec_ref(v_h_u2081_599_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_h_u2082_600_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans___boxed(lean_object* v_h_u2081_657_, lean_object* v_h_u2082_658_, lean_object* v_a_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_Lean_Meta_mkEqTrans(v_h_u2081_657_, v_h_u2082_658_, v_a_659_, v_a_660_, v_a_661_, v_a_662_);
lean_dec(v_a_662_);
lean_dec_ref(v_a_661_);
lean_dec(v_a_660_);
lean_dec_ref(v_a_659_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object* v_h_u2081_x3f_665_, lean_object* v_h_u2082_x3f_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_){
_start:
{
lean_object* v_h_673_; 
if (lean_obj_tag(v_h_u2081_x3f_665_) == 0)
{
if (lean_obj_tag(v_h_u2082_x3f_666_) == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_h_u2082_x3f_666_);
return v___x_676_;
}
else
{
lean_object* v_val_677_; 
v_val_677_ = lean_ctor_get(v_h_u2082_x3f_666_, 0);
lean_inc(v_val_677_);
lean_dec_ref_known(v_h_u2082_x3f_666_, 1);
v_h_673_ = v_val_677_;
goto v___jp_672_;
}
}
else
{
if (lean_obj_tag(v_h_u2082_x3f_666_) == 0)
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v_h_u2081_x3f_665_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v_h_u2081_x3f_665_, 1);
v_h_673_ = v_val_678_;
goto v___jp_672_;
}
else
{
lean_object* v_val_679_; lean_object* v_val_680_; lean_object* v___x_682_; uint8_t v_isShared_683_; uint8_t v_isSharedCheck_704_; 
v_val_679_ = lean_ctor_get(v_h_u2081_x3f_665_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_h_u2081_x3f_665_, 1);
v_val_680_ = lean_ctor_get(v_h_u2082_x3f_666_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v_h_u2082_x3f_666_);
if (v_isSharedCheck_704_ == 0)
{
v___x_682_ = v_h_u2082_x3f_666_;
v_isShared_683_ = v_isSharedCheck_704_;
goto v_resetjp_681_;
}
else
{
lean_inc(v_val_680_);
lean_dec(v_h_u2082_x3f_666_);
v___x_682_ = lean_box(0);
v_isShared_683_ = v_isSharedCheck_704_;
goto v_resetjp_681_;
}
v_resetjp_681_:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_Meta_mkEqTrans(v_val_679_, v_val_680_, v_a_667_, v_a_668_, v_a_669_, v_a_670_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v___x_687_; uint8_t v_isShared_688_; uint8_t v_isSharedCheck_695_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_695_ == 0)
{
v___x_687_ = v___x_684_;
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
else
{
lean_inc(v_a_685_);
lean_dec(v___x_684_);
v___x_687_ = lean_box(0);
v_isShared_688_ = v_isSharedCheck_695_;
goto v_resetjp_686_;
}
v_resetjp_686_:
{
lean_object* v___x_690_; 
if (v_isShared_683_ == 0)
{
lean_ctor_set(v___x_682_, 0, v_a_685_);
v___x_690_ = v___x_682_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v_a_685_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_688_ == 0)
{
lean_ctor_set(v___x_687_, 0, v___x_690_);
v___x_692_ = v___x_687_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_del_object(v___x_682_);
v_a_696_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_684_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_684_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
}
}
v___jp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_674_, 0, v_h_673_);
v___x_675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_675_, 0, v___x_674_);
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f___boxed(lean_object* v_h_u2081_x3f_705_, lean_object* v_h_u2082_x3f_706_, lean_object* v_a_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_){
_start:
{
lean_object* v_res_712_; 
v_res_712_ = l_Lean_Meta_mkEqTrans_x3f(v_h_u2081_x3f_705_, v_h_u2082_x3f_706_, v_a_707_, v_a_708_, v_a_709_, v_a_710_);
lean_dec(v_a_710_);
lean_dec_ref(v_a_709_);
lean_dec(v_a_708_);
lean_dec_ref(v_a_707_);
return v_res_712_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__3(void){
_start:
{
lean_object* v___x_719_; lean_object* v___x_720_; 
v___x_719_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__2));
v___x_720_ = l_Lean_MessageData_ofFormat(v___x_719_);
return v___x_720_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object* v_h_721_, lean_object* v_a_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_){
_start:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_728_ = l_Lean_Expr_isAppOf(v_h_721_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_inc_ref(v_h_721_);
v___x_729_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_721_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_729_) == 0)
{
lean_object* v_a_730_; lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
lean_inc(v_a_730_);
lean_dec_ref_known(v___x_729_, 1);
v___x_731_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_732_ = lean_unsigned_to_nat(4u);
v___x_733_ = l_Lean_Expr_isAppOfArity(v_a_730_, v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_734_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_735_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_736_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_721_, v_a_730_);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_734_, v___x_737_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
return v___x_738_;
}
else
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_739_ = l_Lean_Expr_appFn_x21(v_a_730_);
v___x_740_ = l_Lean_Expr_appFn_x21(v___x_739_);
v___x_741_ = l_Lean_Expr_appFn_x21(v___x_740_);
v___x_742_ = l_Lean_Expr_appArg_x21(v___x_741_);
lean_dec_ref(v___x_741_);
lean_inc_ref(v___x_742_);
v___x_743_ = l_Lean_Meta_getLevel(v___x_742_, v_a_722_, v_a_723_, v_a_724_, v_a_725_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_759_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_759_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_759_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_759_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_748_ = l_Lean_Expr_appArg_x21(v___x_740_);
lean_dec_ref(v___x_740_);
v___x_749_ = l_Lean_Expr_appArg_x21(v___x_739_);
lean_dec_ref(v___x_739_);
v___x_750_ = l_Lean_Expr_appArg_x21(v_a_730_);
lean_dec(v_a_730_);
v___x_751_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v_a_744_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = l_Lean_mkConst(v___x_751_, v___x_753_);
v___x_755_ = l_Lean_mkApp5(v___x_754_, v___x_742_, v___x_749_, v___x_748_, v___x_750_, v_h_721_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_755_);
v___x_757_ = v___x_746_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
else
{
lean_object* v_a_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_767_; 
lean_dec_ref(v___x_742_);
lean_dec_ref(v___x_740_);
lean_dec_ref(v___x_739_);
lean_dec(v_a_730_);
lean_dec_ref(v_h_721_);
v_a_760_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_767_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_767_ == 0)
{
v___x_762_ = v___x_743_;
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_a_760_);
lean_dec(v___x_743_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_767_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_765_; 
if (v_isShared_763_ == 0)
{
v___x_765_ = v___x_762_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_a_760_);
v___x_765_ = v_reuseFailAlloc_766_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
return v___x_765_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_721_);
return v___x_729_;
}
}
else
{
lean_object* v___x_768_; 
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v_h_721_);
return v___x_768_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm___boxed(lean_object* v_h_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l_Lean_Meta_mkHEqSymm(v_h_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object* v_h_u2081_779_, lean_object* v_h_u2082_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_786_; uint8_t v___x_787_; 
v___x_786_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_787_ = l_Lean_Expr_isAppOf(v_h_u2081_779_, v___x_786_);
if (v___x_787_ == 0)
{
uint8_t v___x_788_; 
v___x_788_ = l_Lean_Expr_isAppOf(v_h_u2082_780_, v___x_786_);
if (v___x_788_ == 0)
{
lean_object* v___x_789_; 
lean_inc_ref(v_h_u2081_779_);
v___x_789_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_779_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_789_) == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc(v_a_790_);
lean_dec_ref_known(v___x_789_, 1);
lean_inc_ref(v_h_u2082_780_);
v___x_791_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_780_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_794_; uint8_t v___x_795_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_794_ = lean_unsigned_to_nat(4u);
v___x_795_ = l_Lean_Expr_isAppOfArity(v_a_790_, v___x_793_, v___x_794_);
if (v___x_795_ == 0)
{
lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; 
lean_dec(v_a_792_);
lean_dec_ref(v_h_u2082_780_);
v___x_796_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_797_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_798_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_779_, v_a_790_);
v___x_799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_799_, 0, v___x_797_);
lean_ctor_set(v___x_799_, 1, v___x_798_);
v___x_800_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_796_, v___x_799_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_800_;
}
else
{
uint8_t v___x_801_; 
v___x_801_ = l_Lean_Expr_isAppOfArity(v_a_792_, v___x_793_, v___x_794_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_a_790_);
lean_dec_ref(v_h_u2081_779_);
v___x_802_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_803_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_804_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_780_, v_a_792_);
v___x_805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_803_);
lean_ctor_set(v___x_805_, 1, v___x_804_);
v___x_806_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_802_, v___x_805_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_807_ = l_Lean_Expr_appFn_x21(v_a_790_);
v___x_808_ = l_Lean_Expr_appFn_x21(v___x_807_);
v___x_809_ = l_Lean_Expr_appFn_x21(v___x_808_);
v___x_810_ = l_Lean_Expr_appArg_x21(v___x_809_);
lean_dec_ref(v___x_809_);
lean_inc_ref(v___x_810_);
v___x_811_ = l_Lean_Meta_getLevel(v___x_810_, v_a_781_, v_a_782_, v_a_783_, v_a_784_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_830_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_830_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_830_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_830_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_828_; 
v___x_816_ = l_Lean_Expr_appArg_x21(v___x_808_);
lean_dec_ref(v___x_808_);
v___x_817_ = l_Lean_Expr_appArg_x21(v___x_807_);
lean_dec_ref(v___x_807_);
v___x_818_ = l_Lean_Expr_appArg_x21(v_a_790_);
lean_dec(v_a_790_);
v___x_819_ = l_Lean_Expr_appFn_x21(v_a_792_);
v___x_820_ = l_Lean_Expr_appArg_x21(v___x_819_);
lean_dec_ref(v___x_819_);
v___x_821_ = l_Lean_Expr_appArg_x21(v_a_792_);
lean_dec(v_a_792_);
v___x_822_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_823_ = lean_box(0);
v___x_824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_824_, 0, v_a_812_);
lean_ctor_set(v___x_824_, 1, v___x_823_);
v___x_825_ = l_Lean_mkConst(v___x_822_, v___x_824_);
v___x_826_ = l_Lean_mkApp8(v___x_825_, v___x_810_, v___x_817_, v___x_820_, v___x_816_, v___x_818_, v___x_821_, v_h_u2081_779_, v_h_u2082_780_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 0, v___x_826_);
v___x_828_ = v___x_814_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v___x_810_);
lean_dec_ref(v___x_808_);
lean_dec_ref(v___x_807_);
lean_dec(v_a_792_);
lean_dec(v_a_790_);
lean_dec_ref(v_h_u2082_780_);
lean_dec_ref(v_h_u2081_779_);
v_a_831_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_811_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_811_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
}
}
else
{
lean_dec(v_a_790_);
lean_dec_ref(v_h_u2082_780_);
lean_dec_ref(v_h_u2081_779_);
return v___x_791_;
}
}
else
{
lean_dec_ref(v_h_u2082_780_);
lean_dec_ref(v_h_u2081_779_);
return v___x_789_;
}
}
else
{
lean_object* v___x_839_; 
lean_dec_ref(v_h_u2082_780_);
v___x_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_839_, 0, v_h_u2081_779_);
return v___x_839_;
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v_h_u2081_779_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v_h_u2082_780_);
return v___x_840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans___boxed(lean_object* v_h_u2081_841_, lean_object* v_h_u2082_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_841_, v_h_u2082_842_, v_a_843_, v_a_844_, v_a_845_, v_a_846_);
lean_dec(v_a_846_);
lean_dec_ref(v_a_845_);
lean_dec(v_a_844_);
lean_dec_ref(v_a_843_);
return v_res_848_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__2(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; 
v___x_852_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__1));
v___x_853_ = l_Lean_stringToMessageData(v___x_852_);
return v___x_853_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__4(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; 
v___x_855_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__3));
v___x_856_ = l_Lean_stringToMessageData(v___x_855_);
return v___x_856_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__6(void){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__5));
v___x_859_ = l_Lean_stringToMessageData(v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* v_h_860_, uint8_t v_check_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v___x_867_; 
lean_inc_ref(v_h_860_);
v___x_867_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_860_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
lean_dec_ref_known(v___x_867_, 1);
v___x_869_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_870_ = lean_unsigned_to_nat(4u);
v___x_871_ = l_Lean_Expr_isAppOfArity(v_a_868_, v___x_869_, v___x_870_);
if (v___x_871_ == 0)
{
lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v_a_868_);
v___x_872_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_873_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__2, &l_Lean_Meta_mkEqOfHEq___closed__2_once, _init_l_Lean_Meta_mkEqOfHEq___closed__2);
v___x_874_ = l_Lean_indentExpr(v_h_860_);
v___x_875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_875_, 0, v___x_873_);
lean_ctor_set(v___x_875_, 1, v___x_874_);
v___x_876_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_872_, v___x_875_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
return v___x_876_;
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; 
v___x_877_ = l_Lean_Expr_appFn_x21(v_a_868_);
v___x_878_ = l_Lean_Expr_appFn_x21(v___x_877_);
v___x_879_ = l_Lean_Expr_appFn_x21(v___x_878_);
v___x_880_ = l_Lean_Expr_appArg_x21(v___x_879_);
lean_dec_ref(v___x_879_);
v___x_881_ = l_Lean_Expr_appArg_x21(v___x_878_);
lean_dec_ref(v___x_878_);
v___x_882_ = l_Lean_Expr_appArg_x21(v_a_868_);
lean_dec(v_a_868_);
if (v_check_861_ == 0)
{
lean_dec_ref(v___x_877_);
v___y_884_ = v_a_862_;
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
goto v___jp_883_;
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = l_Lean_Expr_appArg_x21(v___x_877_);
lean_dec_ref(v___x_877_);
lean_inc_ref(v___x_910_);
lean_inc_ref(v___x_880_);
v___x_911_ = l_Lean_Meta_isExprDefEq(v___x_880_, v___x_910_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; uint8_t v___x_913_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc(v_a_912_);
lean_dec_ref_known(v___x_911_, 1);
v___x_913_ = lean_unbox(v_a_912_);
lean_dec(v_a_912_);
if (v___x_913_ == 0)
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v_h_860_);
v___x_914_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_915_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__4, &l_Lean_Meta_mkEqOfHEq___closed__4_once, _init_l_Lean_Meta_mkEqOfHEq___closed__4);
v___x_916_ = l_Lean_indentExpr(v___x_880_);
v___x_917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_917_, 0, v___x_915_);
lean_ctor_set(v___x_917_, 1, v___x_916_);
v___x_918_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__6, &l_Lean_Meta_mkEqOfHEq___closed__6_once, _init_l_Lean_Meta_mkEqOfHEq___closed__6);
v___x_919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_919_, 0, v___x_917_);
lean_ctor_set(v___x_919_, 1, v___x_918_);
v___x_920_ = l_Lean_indentExpr(v___x_910_);
v___x_921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_921_, 0, v___x_919_);
lean_ctor_set(v___x_921_, 1, v___x_920_);
v___x_922_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_914_, v___x_921_, v_a_862_, v_a_863_, v_a_864_, v_a_865_);
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
else
{
lean_dec_ref(v___x_910_);
v___y_884_ = v_a_862_;
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
goto v___jp_883_;
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec_ref(v___x_910_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v_h_860_);
v_a_931_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_911_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_911_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
v___jp_883_:
{
lean_object* v___x_888_; 
lean_inc_ref(v___x_880_);
v___x_888_ = l_Lean_Meta_getLevel(v___x_880_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_901_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_901_ == 0)
{
v___x_891_ = v___x_888_;
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_888_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_901_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_893_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_894_ = lean_box(0);
v___x_895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_895_, 0, v_a_889_);
lean_ctor_set(v___x_895_, 1, v___x_894_);
v___x_896_ = l_Lean_mkConst(v___x_893_, v___x_895_);
v___x_897_ = l_Lean_mkApp4(v___x_896_, v___x_880_, v___x_881_, v___x_882_, v_h_860_);
if (v_isShared_892_ == 0)
{
lean_ctor_set(v___x_891_, 0, v___x_897_);
v___x_899_ = v___x_891_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v___x_880_);
lean_dec_ref(v_h_860_);
v_a_902_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_888_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_888_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_860_);
return v___x_867_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___boxed(lean_object* v_h_939_, lean_object* v_check_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_){
_start:
{
uint8_t v_check_boxed_946_; lean_object* v_res_947_; 
v_check_boxed_946_ = lean_unbox(v_check_940_);
v_res_947_ = l_Lean_Meta_mkEqOfHEq(v_h_939_, v_check_boxed_946_, v_a_941_, v_a_942_, v_a_943_, v_a_944_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec_ref(v_a_941_);
return v_res_947_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqOfEq___closed__2(void){
_start:
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__2));
v___x_952_ = l_Lean_stringToMessageData(v___x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq(lean_object* v_h_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_){
_start:
{
lean_object* v___x_959_; 
lean_inc_ref(v_h_953_);
v___x_959_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_959_) == 0)
{
lean_object* v_a_960_; lean_object* v___x_961_; lean_object* v___x_962_; uint8_t v___x_963_; 
v_a_960_ = lean_ctor_get(v___x_959_, 0);
lean_inc(v_a_960_);
lean_dec_ref_known(v___x_959_, 1);
v___x_961_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_962_ = lean_unsigned_to_nat(3u);
v___x_963_ = l_Lean_Expr_isAppOfArity(v_a_960_, v___x_961_, v___x_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_a_960_);
v___x_964_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_965_ = lean_obj_once(&l_Lean_Meta_mkHEqOfEq___closed__2, &l_Lean_Meta_mkHEqOfEq___closed__2_once, _init_l_Lean_Meta_mkHEqOfEq___closed__2);
v___x_966_ = l_Lean_indentExpr(v_h_953_);
v___x_967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_965_);
lean_ctor_set(v___x_967_, 1, v___x_966_);
v___x_968_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_964_, v___x_967_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
return v___x_968_;
}
else
{
lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_969_ = l_Lean_Expr_appFn_x21(v_a_960_);
v___x_970_ = l_Lean_Expr_appFn_x21(v___x_969_);
v___x_971_ = l_Lean_Expr_appArg_x21(v___x_970_);
lean_dec_ref(v___x_970_);
lean_inc_ref(v___x_971_);
v___x_972_ = l_Lean_Meta_getLevel(v___x_971_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
if (lean_obj_tag(v___x_972_) == 0)
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_987_; 
v_a_973_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_987_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_987_ == 0)
{
v___x_975_ = v___x_972_;
v_isShared_976_ = v_isSharedCheck_987_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_972_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_987_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_985_; 
v___x_977_ = l_Lean_Expr_appArg_x21(v___x_969_);
lean_dec_ref(v___x_969_);
v___x_978_ = l_Lean_Expr_appArg_x21(v_a_960_);
lean_dec(v_a_960_);
v___x_979_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_980_ = lean_box(0);
v___x_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_981_, 0, v_a_973_);
lean_ctor_set(v___x_981_, 1, v___x_980_);
v___x_982_ = l_Lean_mkConst(v___x_979_, v___x_981_);
v___x_983_ = l_Lean_mkApp4(v___x_982_, v___x_971_, v___x_977_, v___x_978_, v_h_953_);
if (v_isShared_976_ == 0)
{
lean_ctor_set(v___x_975_, 0, v___x_983_);
v___x_985_ = v___x_975_;
goto v_reusejp_984_;
}
else
{
lean_object* v_reuseFailAlloc_986_; 
v_reuseFailAlloc_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_986_, 0, v___x_983_);
v___x_985_ = v_reuseFailAlloc_986_;
goto v_reusejp_984_;
}
v_reusejp_984_:
{
return v___x_985_;
}
}
}
else
{
lean_object* v_a_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_995_; 
lean_dec_ref(v___x_971_);
lean_dec_ref(v___x_969_);
lean_dec(v_a_960_);
lean_dec_ref(v_h_953_);
v_a_988_ = lean_ctor_get(v___x_972_, 0);
v_isSharedCheck_995_ = !lean_is_exclusive(v___x_972_);
if (v_isSharedCheck_995_ == 0)
{
v___x_990_ = v___x_972_;
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_a_988_);
lean_dec(v___x_972_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_995_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_993_; 
if (v_isShared_991_ == 0)
{
v___x_993_ = v___x_990_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_994_; 
v_reuseFailAlloc_994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_994_, 0, v_a_988_);
v___x_993_ = v_reuseFailAlloc_994_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
return v___x_993_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_953_);
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq___boxed(lean_object* v_h_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_Meta_mkHEqOfEq(v_h_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_);
lean_dec(v_a_1000_);
lean_dec_ref(v_a_999_);
lean_dec(v_a_998_);
lean_dec_ref(v_a_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f(lean_object* v_e_1003_){
_start:
{
lean_object* v___x_1004_; lean_object* v___x_1005_; uint8_t v___x_1006_; 
v___x_1004_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1005_ = lean_unsigned_to_nat(2u);
v___x_1006_ = l_Lean_Expr_isAppOfArity(v_e_1003_, v___x_1004_, v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = lean_box(0);
return v___x_1007_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1008_ = l_Lean_Expr_appArg_x21(v_e_1003_);
v___x_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1009_, 0, v___x_1008_);
return v___x_1009_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f___boxed(lean_object* v_e_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l_Lean_Meta_isRefl_x3f(v_e_1010_);
lean_dec_ref(v_e_1010_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(lean_object* v_msg_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v___f_1019_; lean_object* v___x_1140__overap_1020_; lean_object* v___x_1021_; 
v___f_1019_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_1140__overap_1020_ = lean_panic_fn_borrowed(v___f_1019_, v_msg_1013_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
v___x_1021_ = lean_apply_5(v___x_1140__overap_1020_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, lean_box(0));
return v___x_1021_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___boxed(lean_object* v_msg_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
lean_object* v_res_1028_; 
v_res_1028_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v_msg_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
return v_res_1028_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__2(void){
_start:
{
lean_object* v___x_1032_; lean_object* v_dummy_1033_; 
v___x_1032_ = lean_box(0);
v_dummy_1033_ = l_Lean_Expr_sort___override(v___x_1032_);
return v_dummy_1033_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__6(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1037_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1038_ = lean_unsigned_to_nat(48u);
v___x_1039_ = lean_unsigned_to_nat(204u);
v___x_1040_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1041_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1042_ = l_mkPanicMessageWithDecl(v___x_1041_, v___x_1040_, v___x_1039_, v___x_1038_, v___x_1037_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__9(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = lean_unsigned_to_nat(0u);
v___x_1047_ = l_Lean_Expr_bvar___override(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__10(void){
_start:
{
lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1048_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1049_ = lean_unsigned_to_nat(1u);
v___x_1050_ = lean_mk_empty_array_with_capacity(v___x_1049_);
v___x_1051_ = lean_array_push(v___x_1050_, v___x_1048_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__15(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1058_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1059_ = lean_unsigned_to_nat(49u);
v___x_1060_ = lean_unsigned_to_nat(201u);
v___x_1061_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1062_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1063_ = l_mkPanicMessageWithDecl(v___x_1062_, v___x_1061_, v___x_1060_, v___x_1059_, v___x_1058_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f(lean_object* v_e_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_){
_start:
{
lean_object* v___y_1074_; lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___x_1119_; lean_object* v___x_1120_; uint8_t v___x_1121_; 
v___x_1119_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1120_ = lean_unsigned_to_nat(6u);
v___x_1121_ = l_Lean_Expr_isAppOfArity(v_e_1064_, v___x_1119_, v___x_1120_);
if (v___x_1121_ == 0)
{
v___y_1074_ = v_a_1065_;
v___y_1075_ = v_a_1066_;
v___y_1076_ = v_a_1067_;
v___y_1077_ = v_a_1068_;
goto v___jp_1073_;
}
else
{
lean_object* v_dummy_1122_; lean_object* v_nargs_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; uint8_t v___x_1129_; 
v_dummy_1122_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1123_ = l_Lean_Expr_getAppNumArgs(v_e_1064_);
lean_inc(v_nargs_1123_);
v___x_1124_ = lean_mk_array(v_nargs_1123_, v_dummy_1122_);
v___x_1125_ = lean_unsigned_to_nat(1u);
v___x_1126_ = lean_nat_sub(v_nargs_1123_, v___x_1125_);
lean_dec(v_nargs_1123_);
lean_inc_ref(v_e_1064_);
v___x_1127_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1064_, v___x_1124_, v___x_1126_);
v___x_1128_ = lean_array_get_size(v___x_1127_);
v___x_1129_ = lean_nat_dec_eq(v___x_1128_, v___x_1120_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; lean_object* v___x_1131_; 
lean_dec_ref(v___x_1127_);
v___x_1130_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__15, &l_Lean_Meta_congrArg_x3f___closed__15_once, _init_l_Lean_Meta_congrArg_x3f___closed__15);
v___x_1131_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1130_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_);
if (lean_obj_tag(v___x_1131_) == 0)
{
lean_dec_ref_known(v___x_1131_, 1);
v___y_1074_ = v_a_1065_;
v___y_1075_ = v_a_1066_;
v___y_1076_ = v_a_1067_;
v___y_1077_ = v_a_1068_;
goto v___jp_1073_;
}
else
{
lean_object* v_a_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1139_; 
lean_dec_ref(v_e_1064_);
v_a_1132_ = lean_ctor_get(v___x_1131_, 0);
v_isSharedCheck_1139_ = !lean_is_exclusive(v___x_1131_);
if (v_isSharedCheck_1139_ == 0)
{
v___x_1134_ = v___x_1131_;
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_a_1132_);
lean_dec(v___x_1131_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1139_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v___x_1137_; 
if (v_isShared_1135_ == 0)
{
v___x_1137_ = v___x_1134_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_a_1132_);
v___x_1137_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1136_;
}
v_reusejp_1136_:
{
return v___x_1137_;
}
}
}
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v_e_1064_);
v___x_1140_ = lean_unsigned_to_nat(0u);
v___x_1141_ = lean_array_fget(v___x_1127_, v___x_1140_);
v___x_1142_ = lean_unsigned_to_nat(4u);
v___x_1143_ = lean_array_fget(v___x_1127_, v___x_1142_);
v___x_1144_ = lean_unsigned_to_nat(5u);
v___x_1145_ = lean_array_fget(v___x_1127_, v___x_1144_);
lean_dec_ref(v___x_1127_);
v___x_1146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1143_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1141_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
return v___x_1149_;
}
}
v___jp_1070_:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_box(0);
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
v___jp_1073_:
{
lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1078_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1079_ = lean_unsigned_to_nat(6u);
v___x_1080_ = l_Lean_Expr_isAppOfArity(v_e_1064_, v___x_1078_, v___x_1079_);
if (v___x_1080_ == 0)
{
lean_dec_ref(v_e_1064_);
goto v___jp_1070_;
}
else
{
lean_object* v_dummy_1081_; lean_object* v_nargs_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; uint8_t v___x_1088_; 
v_dummy_1081_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1082_ = l_Lean_Expr_getAppNumArgs(v_e_1064_);
lean_inc(v_nargs_1082_);
v___x_1083_ = lean_mk_array(v_nargs_1082_, v_dummy_1081_);
v___x_1084_ = lean_unsigned_to_nat(1u);
v___x_1085_ = lean_nat_sub(v_nargs_1082_, v___x_1084_);
lean_dec(v_nargs_1082_);
v___x_1086_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1064_, v___x_1083_, v___x_1085_);
v___x_1087_ = lean_array_get_size(v___x_1086_);
v___x_1088_ = lean_nat_dec_eq(v___x_1087_, v___x_1079_);
if (v___x_1088_ == 0)
{
lean_object* v___x_1089_; lean_object* v___x_1090_; 
lean_dec_ref(v___x_1086_);
v___x_1089_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__6, &l_Lean_Meta_congrArg_x3f___closed__6_once, _init_l_Lean_Meta_congrArg_x3f___closed__6);
v___x_1090_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1089_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_dec_ref_known(v___x_1090_, 1);
goto v___jp_1070_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; uint8_t v___x_1110_; lean_object* v_00_u03b1_x27_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v_f_x27_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1099_ = lean_unsigned_to_nat(0u);
v___x_1100_ = lean_array_fget(v___x_1086_, v___x_1099_);
v___x_1101_ = lean_array_fget(v___x_1086_, v___x_1084_);
v___x_1102_ = lean_unsigned_to_nat(4u);
v___x_1103_ = lean_array_fget(v___x_1086_, v___x_1102_);
v___x_1104_ = lean_unsigned_to_nat(5u);
v___x_1105_ = lean_array_fget(v___x_1086_, v___x_1104_);
lean_dec_ref(v___x_1086_);
v___x_1106_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1107_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1108_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1109_ = l_Lean_Expr_beta(v___x_1101_, v___x_1108_);
v___x_1110_ = 0;
v_00_u03b1_x27_1111_ = l_Lean_Expr_forallE___override(v___x_1106_, v___x_1100_, v___x_1109_, v___x_1110_);
v___x_1112_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__12));
v___x_1113_ = l_Lean_Expr_app___override(v___x_1107_, v___x_1105_);
lean_inc_ref(v_00_u03b1_x27_1111_);
v_f_x27_1114_ = l_Lean_Expr_lam___override(v___x_1112_, v_00_u03b1_x27_1111_, v___x_1113_, v___x_1110_);
v___x_1115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1115_, 0, v_f_x27_1114_);
lean_ctor_set(v___x_1115_, 1, v___x_1103_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_00_u03b1_x27_1111_);
lean_ctor_set(v___x_1116_, 1, v___x_1115_);
v___x_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1117_, 0, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
return v___x_1118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___boxed(lean_object* v_e_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Meta_congrArg_x3f(v_e_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
return v_res_1156_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__2(void){
_start:
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
v___x_1160_ = ((lean_object*)(l_Lean_Meta_mkCongrArg___closed__1));
v___x_1161_ = l_Lean_MessageData_ofFormat(v___x_1160_);
return v___x_1161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object* v_f_1162_, lean_object* v_h_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_){
_start:
{
lean_object* v___x_1169_; 
v___x_1169_ = l_Lean_Meta_isRefl_x3f(v_h_1163_);
if (lean_obj_tag(v___x_1169_) == 1)
{
lean_object* v_val_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec_ref(v_h_1163_);
v_val_1170_ = lean_ctor_get(v___x_1169_, 0);
lean_inc(v_val_1170_);
lean_dec_ref_known(v___x_1169_, 1);
v___x_1171_ = l_Lean_Expr_app___override(v_f_1162_, v_val_1170_);
v___x_1172_ = l_Lean_Meta_mkEqRefl(v___x_1171_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1172_;
}
else
{
lean_object* v___x_1173_; 
lean_dec(v___x_1169_);
lean_inc_ref(v_h_1163_);
v___x_1173_ = l_Lean_Meta_congrArg_x3f(v_h_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1173_) == 0)
{
lean_object* v_a_1174_; 
v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
lean_inc(v_a_1174_);
lean_dec_ref_known(v___x_1173_, 1);
if (lean_obj_tag(v_a_1174_) == 1)
{
lean_object* v_val_1175_; lean_object* v_snd_1176_; lean_object* v_fst_1177_; lean_object* v_fst_1178_; lean_object* v_snd_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; 
lean_dec_ref(v_h_1163_);
v_val_1175_ = lean_ctor_get(v_a_1174_, 0);
lean_inc(v_val_1175_);
lean_dec_ref_known(v_a_1174_, 1);
v_snd_1176_ = lean_ctor_get(v_val_1175_, 1);
lean_inc(v_snd_1176_);
v_fst_1177_ = lean_ctor_get(v_val_1175_, 0);
lean_inc(v_fst_1177_);
lean_dec(v_val_1175_);
v_fst_1178_ = lean_ctor_get(v_snd_1176_, 0);
lean_inc(v_fst_1178_);
v_snd_1179_ = lean_ctor_get(v_snd_1176_, 1);
lean_inc(v_snd_1179_);
lean_dec(v_snd_1176_);
v___x_1180_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1181_ = lean_unsigned_to_nat(1u);
v___x_1182_ = lean_mk_empty_array_with_capacity(v___x_1181_);
v___x_1183_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1184_ = l_Lean_Expr_beta(v_fst_1178_, v___x_1183_);
v___x_1185_ = lean_array_push(v___x_1182_, v___x_1184_);
v___x_1186_ = l_Lean_Expr_beta(v_f_1162_, v___x_1185_);
v___x_1187_ = 0;
v___x_1188_ = l_Lean_Expr_lam___override(v___x_1180_, v_fst_1177_, v___x_1186_, v___x_1187_);
v_f_1162_ = v___x_1188_;
v_h_1163_ = v_snd_1179_;
goto _start;
}
else
{
lean_object* v___x_1190_; 
lean_dec(v_a_1174_);
lean_inc_ref(v_h_1163_);
v___x_1190_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1190_) == 0)
{
lean_object* v_a_1191_; lean_object* v___x_1192_; 
v_a_1191_ = lean_ctor_get(v___x_1190_, 0);
lean_inc(v_a_1191_);
lean_dec_ref_known(v___x_1190_, 1);
lean_inc_ref(v_f_1162_);
v___x_1192_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_f_1162_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1192_) == 0)
{
lean_object* v_a_1193_; 
v_a_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_a_1193_);
lean_dec_ref_known(v___x_1192_, 1);
if (lean_obj_tag(v_a_1193_) == 7)
{
lean_object* v_binderType_1200_; lean_object* v_body_1201_; uint8_t v___x_1202_; 
v_binderType_1200_ = lean_ctor_get(v_a_1193_, 1);
v_body_1201_ = lean_ctor_get(v_a_1193_, 2);
v___x_1202_ = l_Lean_Expr_hasLooseBVars(v_body_1201_);
if (v___x_1202_ == 0)
{
lean_object* v___x_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
lean_inc_ref(v_body_1201_);
lean_inc_ref(v_binderType_1200_);
lean_dec_ref_known(v_a_1193_, 3);
v___x_1203_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1204_ = lean_unsigned_to_nat(3u);
v___x_1205_ = l_Lean_Expr_isAppOfArity(v_a_1191_, v___x_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; 
lean_dec_ref(v_body_1201_);
lean_dec_ref(v_binderType_1200_);
lean_dec_ref(v_f_1162_);
v___x_1206_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1207_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1208_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1163_, v_a_1191_);
v___x_1209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1207_);
lean_ctor_set(v___x_1209_, 1, v___x_1208_);
v___x_1210_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1206_, v___x_1209_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1210_;
}
else
{
lean_object* v___x_1211_; 
lean_inc_ref(v_binderType_1200_);
v___x_1211_ = l_Lean_Meta_getLevel(v_binderType_1200_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1211_) == 0)
{
lean_object* v_a_1212_; lean_object* v___x_1213_; 
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref_known(v___x_1211_, 1);
lean_inc_ref(v_body_1201_);
v___x_1213_ = l_Lean_Meta_getLevel(v_body_1201_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1230_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1230_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1228_; 
v___x_1218_ = l_Lean_Expr_appFn_x21(v_a_1191_);
v___x_1219_ = l_Lean_Expr_appArg_x21(v___x_1218_);
lean_dec_ref(v___x_1218_);
v___x_1220_ = l_Lean_Expr_appArg_x21(v_a_1191_);
lean_dec(v_a_1191_);
v___x_1221_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1222_ = lean_box(0);
v___x_1223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1223_, 0, v_a_1214_);
lean_ctor_set(v___x_1223_, 1, v___x_1222_);
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1212_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = l_Lean_mkConst(v___x_1221_, v___x_1224_);
v___x_1226_ = l_Lean_mkApp6(v___x_1225_, v_binderType_1200_, v_body_1201_, v___x_1219_, v___x_1220_, v_f_1162_, v_h_1163_);
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 0, v___x_1226_);
v___x_1228_ = v___x_1216_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v___x_1226_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
else
{
lean_object* v_a_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1238_; 
lean_dec(v_a_1212_);
lean_dec_ref(v_body_1201_);
lean_dec_ref(v_binderType_1200_);
lean_dec(v_a_1191_);
lean_dec_ref(v_h_1163_);
lean_dec_ref(v_f_1162_);
v_a_1231_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1238_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1238_ == 0)
{
v___x_1233_ = v___x_1213_;
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_a_1231_);
lean_dec(v___x_1213_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1238_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1236_; 
if (v_isShared_1234_ == 0)
{
v___x_1236_ = v___x_1233_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_a_1231_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
}
}
else
{
lean_object* v_a_1239_; lean_object* v___x_1241_; uint8_t v_isShared_1242_; uint8_t v_isSharedCheck_1246_; 
lean_dec_ref(v_body_1201_);
lean_dec_ref(v_binderType_1200_);
lean_dec(v_a_1191_);
lean_dec_ref(v_h_1163_);
lean_dec_ref(v_f_1162_);
v_a_1239_ = lean_ctor_get(v___x_1211_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1211_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1241_ = v___x_1211_;
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
else
{
lean_inc(v_a_1239_);
lean_dec(v___x_1211_);
v___x_1241_ = lean_box(0);
v_isShared_1242_ = v_isSharedCheck_1246_;
goto v_resetjp_1240_;
}
v_resetjp_1240_:
{
lean_object* v___x_1244_; 
if (v_isShared_1242_ == 0)
{
v___x_1244_ = v___x_1241_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_a_1239_);
v___x_1244_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1243_;
}
v_reusejp_1243_:
{
return v___x_1244_;
}
}
}
}
}
else
{
lean_dec(v_a_1191_);
lean_dec_ref(v_h_1163_);
goto v___jp_1194_;
}
}
else
{
lean_dec(v_a_1191_);
lean_dec_ref(v_h_1163_);
goto v___jp_1194_;
}
v___jp_1194_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1195_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1196_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1197_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_f_1162_, v_a_1193_);
v___x_1198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1196_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1195_, v___x_1198_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
return v___x_1199_;
}
}
else
{
lean_dec(v_a_1191_);
lean_dec_ref(v_h_1163_);
lean_dec_ref(v_f_1162_);
return v___x_1192_;
}
}
else
{
lean_dec_ref(v_h_1163_);
lean_dec_ref(v_f_1162_);
return v___x_1190_;
}
}
}
else
{
lean_object* v_a_1247_; lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
lean_dec_ref(v_h_1163_);
lean_dec_ref(v_f_1162_);
v_a_1247_ = lean_ctor_get(v___x_1173_, 0);
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1173_);
if (v_isSharedCheck_1254_ == 0)
{
v___x_1249_ = v___x_1173_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_inc(v_a_1247_);
lean_dec(v___x_1173_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1247_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___boxed(lean_object* v_f_1255_, lean_object* v_h_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l_Lean_Meta_mkCongrArg(v_f_1255_, v_h_1256_, v_a_1257_, v_a_1258_, v_a_1259_, v_a_1260_);
lean_dec(v_a_1260_);
lean_dec_ref(v_a_1259_);
lean_dec(v_a_1258_);
lean_dec_ref(v_a_1257_);
return v_res_1262_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__0(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1263_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1264_ = lean_unsigned_to_nat(2u);
v___x_1265_ = lean_mk_empty_array_with_capacity(v___x_1264_);
v___x_1266_ = lean_array_push(v___x_1265_, v___x_1263_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__3(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = ((lean_object*)(l_Lean_Meta_mkCongrFun___closed__2));
v___x_1271_ = l_Lean_MessageData_ofFormat(v___x_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object* v_h_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = l_Lean_Meta_isRefl_x3f(v_h_1272_);
if (lean_obj_tag(v___x_1279_) == 1)
{
lean_object* v_val_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
lean_dec_ref(v_h_1272_);
v_val_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_val_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = l_Lean_Expr_app___override(v_val_1280_, v_a_1273_);
v___x_1282_ = l_Lean_Meta_mkEqRefl(v___x_1281_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1282_;
}
else
{
lean_object* v___x_1283_; 
lean_dec(v___x_1279_);
lean_inc_ref(v_h_1272_);
v___x_1283_ = l_Lean_Meta_congrArg_x3f(v_h_1272_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
if (lean_obj_tag(v_a_1284_) == 1)
{
lean_object* v_val_1285_; lean_object* v_snd_1286_; lean_object* v_fst_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; uint8_t v___x_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_dec_ref(v_h_1272_);
v_val_1285_ = lean_ctor_get(v_a_1284_, 0);
lean_inc(v_val_1285_);
lean_dec_ref_known(v_a_1284_, 1);
v_snd_1286_ = lean_ctor_get(v_val_1285_, 1);
lean_inc(v_snd_1286_);
v_fst_1287_ = lean_ctor_get(v_val_1285_, 0);
lean_inc(v_fst_1287_);
lean_dec(v_val_1285_);
v_fst_1288_ = lean_ctor_get(v_snd_1286_, 0);
lean_inc(v_fst_1288_);
v_snd_1289_ = lean_ctor_get(v_snd_1286_, 1);
lean_inc(v_snd_1289_);
lean_dec(v_snd_1286_);
v___x_1290_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1291_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__0, &l_Lean_Meta_mkCongrFun___closed__0_once, _init_l_Lean_Meta_mkCongrFun___closed__0);
v___x_1292_ = lean_array_push(v___x_1291_, v_a_1273_);
v___x_1293_ = l_Lean_Expr_beta(v_fst_1288_, v___x_1292_);
v___x_1294_ = 0;
v___x_1295_ = l_Lean_Expr_lam___override(v___x_1290_, v_fst_1287_, v___x_1293_, v___x_1294_);
v___x_1296_ = l_Lean_Meta_mkCongrArg(v___x_1295_, v_snd_1289_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1296_;
}
else
{
lean_object* v___x_1297_; 
lean_dec(v_a_1284_);
lean_inc_ref(v_h_1272_);
v___x_1297_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1272_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; uint8_t v___x_1301_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1300_ = lean_unsigned_to_nat(3u);
v___x_1301_ = l_Lean_Expr_isAppOfArity(v_a_1298_, v___x_1299_, v___x_1300_);
if (v___x_1301_ == 0)
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; 
lean_dec_ref(v_a_1273_);
v___x_1302_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1303_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1304_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1272_, v_a_1298_);
v___x_1305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1303_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1302_, v___x_1305_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1306_;
}
else
{
lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1307_ = l_Lean_Expr_appFn_x21(v_a_1298_);
v___x_1308_ = l_Lean_Expr_appFn_x21(v___x_1307_);
v___x_1309_ = l_Lean_Expr_appArg_x21(v___x_1308_);
lean_dec_ref(v___x_1308_);
v___x_1310_ = l_Lean_Meta_whnfD(v___x_1309_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1310_) == 0)
{
lean_object* v_a_1311_; 
v_a_1311_ = lean_ctor_get(v___x_1310_, 0);
lean_inc(v_a_1311_);
lean_dec_ref_known(v___x_1310_, 1);
if (lean_obj_tag(v_a_1311_) == 7)
{
lean_object* v_binderName_1312_; lean_object* v_binderType_1313_; lean_object* v_body_1314_; uint8_t v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v_binderName_1312_ = lean_ctor_get(v_a_1311_, 0);
lean_inc(v_binderName_1312_);
v_binderType_1313_ = lean_ctor_get(v_a_1311_, 1);
lean_inc_ref_n(v_binderType_1313_, 3);
v_body_1314_ = lean_ctor_get(v_a_1311_, 2);
lean_inc_ref(v_body_1314_);
lean_dec_ref_known(v_a_1311_, 3);
v___x_1315_ = 0;
v___x_1316_ = l_Lean_mkLambda(v_binderName_1312_, v___x_1315_, v_binderType_1313_, v_body_1314_);
v___x_1317_ = l_Lean_Meta_getLevel(v_binderType_1313_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v_a_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v_a_1318_ = lean_ctor_get(v___x_1317_, 0);
lean_inc(v_a_1318_);
lean_dec_ref_known(v___x_1317_, 1);
lean_inc_ref(v_a_1273_);
lean_inc_ref(v___x_1316_);
v___x_1319_ = l_Lean_Expr_app___override(v___x_1316_, v_a_1273_);
v___x_1320_ = l_Lean_Meta_getLevel(v___x_1319_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1336_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1336_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1336_ == 0)
{
v___x_1323_ = v___x_1320_;
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_a_1321_);
lean_dec(v___x_1320_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1336_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1334_; 
v___x_1325_ = l_Lean_Expr_appArg_x21(v___x_1307_);
lean_dec_ref(v___x_1307_);
v___x_1326_ = l_Lean_Expr_appArg_x21(v_a_1298_);
lean_dec(v_a_1298_);
v___x_1327_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1328_ = lean_box(0);
v___x_1329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_a_1321_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1318_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = l_Lean_mkConst(v___x_1327_, v___x_1330_);
v___x_1332_ = l_Lean_mkApp6(v___x_1331_, v_binderType_1313_, v___x_1316_, v___x_1325_, v___x_1326_, v_h_1272_, v_a_1273_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 0, v___x_1332_);
v___x_1334_ = v___x_1323_;
goto v_reusejp_1333_;
}
else
{
lean_object* v_reuseFailAlloc_1335_; 
v_reuseFailAlloc_1335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1335_, 0, v___x_1332_);
v___x_1334_ = v_reuseFailAlloc_1335_;
goto v_reusejp_1333_;
}
v_reusejp_1333_:
{
return v___x_1334_;
}
}
}
else
{
lean_object* v_a_1337_; lean_object* v___x_1339_; uint8_t v_isShared_1340_; uint8_t v_isSharedCheck_1344_; 
lean_dec(v_a_1318_);
lean_dec_ref(v___x_1316_);
lean_dec_ref(v_binderType_1313_);
lean_dec_ref(v___x_1307_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_h_1272_);
v_a_1337_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1344_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1344_ == 0)
{
v___x_1339_ = v___x_1320_;
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
else
{
lean_inc(v_a_1337_);
lean_dec(v___x_1320_);
v___x_1339_ = lean_box(0);
v_isShared_1340_ = v_isSharedCheck_1344_;
goto v_resetjp_1338_;
}
v_resetjp_1338_:
{
lean_object* v___x_1342_; 
if (v_isShared_1340_ == 0)
{
v___x_1342_ = v___x_1339_;
goto v_reusejp_1341_;
}
else
{
lean_object* v_reuseFailAlloc_1343_; 
v_reuseFailAlloc_1343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1343_, 0, v_a_1337_);
v___x_1342_ = v_reuseFailAlloc_1343_;
goto v_reusejp_1341_;
}
v_reusejp_1341_:
{
return v___x_1342_;
}
}
}
}
else
{
lean_object* v_a_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1352_; 
lean_dec_ref(v___x_1316_);
lean_dec_ref(v_binderType_1313_);
lean_dec_ref(v___x_1307_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_h_1272_);
v_a_1345_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1352_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1352_ == 0)
{
v___x_1347_ = v___x_1317_;
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_a_1345_);
lean_dec(v___x_1317_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1352_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1350_; 
if (v_isShared_1348_ == 0)
{
v___x_1350_ = v___x_1347_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1351_; 
v_reuseFailAlloc_1351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1351_, 0, v_a_1345_);
v___x_1350_ = v_reuseFailAlloc_1351_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
return v___x_1350_;
}
}
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec(v_a_1311_);
lean_dec_ref(v___x_1307_);
lean_dec_ref(v_a_1273_);
v___x_1353_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1354_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__3, &l_Lean_Meta_mkCongrFun___closed__3_once, _init_l_Lean_Meta_mkCongrFun___closed__3);
v___x_1355_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1272_, v_a_1298_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1353_, v___x_1356_, v_a_1274_, v_a_1275_, v_a_1276_, v_a_1277_);
return v___x_1357_;
}
}
else
{
lean_dec_ref(v___x_1307_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_h_1272_);
return v___x_1310_;
}
}
}
else
{
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_h_1272_);
return v___x_1297_;
}
}
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec_ref(v_a_1273_);
lean_dec_ref(v_h_1272_);
v_a_1358_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1283_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1283_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___boxed(lean_object* v_h_1366_, lean_object* v_a_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_Lean_Meta_mkCongrFun(v_h_1366_, v_a_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_);
lean_dec(v_a_1371_);
lean_dec_ref(v_a_1370_);
lean_dec(v_a_1369_);
lean_dec_ref(v_a_1368_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object* v_h_u2081_1377_, lean_object* v_h_u2082_1378_, lean_object* v_a_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_){
_start:
{
lean_object* v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1385_ = l_Lean_Expr_isAppOf(v_h_u2081_1377_, v___x_1384_);
if (v___x_1385_ == 0)
{
uint8_t v___x_1386_; 
v___x_1386_ = l_Lean_Expr_isAppOf(v_h_u2082_1378_, v___x_1384_);
if (v___x_1386_ == 0)
{
lean_object* v___x_1387_; 
lean_inc_ref(v_h_u2081_1377_);
v___x_1387_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_1377_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1387_) == 0)
{
lean_object* v_a_1388_; lean_object* v___x_1389_; 
v_a_1388_ = lean_ctor_get(v___x_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___x_1387_, 1);
lean_inc_ref(v_h_u2082_1378_);
v___x_1389_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; uint8_t v___x_1393_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1392_ = lean_unsigned_to_nat(3u);
v___x_1393_ = l_Lean_Expr_isAppOfArity(v_a_1388_, v___x_1391_, v___x_1392_);
if (v___x_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; 
lean_dec(v_a_1390_);
lean_dec_ref(v_h_u2082_1378_);
v___x_1394_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1395_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1396_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1377_, v_a_1388_);
v___x_1397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1397_, 0, v___x_1395_);
lean_ctor_set(v___x_1397_, 1, v___x_1396_);
v___x_1398_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1394_, v___x_1397_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1398_;
}
else
{
uint8_t v___x_1399_; 
v___x_1399_ = l_Lean_Expr_isAppOfArity(v_a_1390_, v___x_1391_, v___x_1392_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; 
lean_dec(v_a_1388_);
lean_dec_ref(v_h_u2081_1377_);
v___x_1400_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1401_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1402_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_1378_, v_a_1390_);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
v___x_1404_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1400_, v___x_1403_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1404_;
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; 
v___x_1405_ = l_Lean_Expr_appFn_x21(v_a_1388_);
v___x_1406_ = l_Lean_Expr_appFn_x21(v___x_1405_);
v___x_1407_ = l_Lean_Expr_appArg_x21(v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1408_ = l_Lean_Meta_whnfD(v___x_1407_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1408_) == 0)
{
lean_object* v_a_1409_; 
v_a_1409_ = lean_ctor_get(v___x_1408_, 0);
lean_inc(v_a_1409_);
lean_dec_ref_known(v___x_1408_, 1);
if (lean_obj_tag(v_a_1409_) == 7)
{
lean_object* v_body_1416_; uint8_t v___x_1417_; 
v_body_1416_ = lean_ctor_get(v_a_1409_, 2);
lean_inc_ref(v_body_1416_);
lean_dec_ref_known(v_a_1409_, 3);
v___x_1417_ = l_Lean_Expr_hasLooseBVars(v_body_1416_);
if (v___x_1417_ == 0)
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
v___x_1418_ = l_Lean_Expr_appFn_x21(v_a_1390_);
v___x_1419_ = l_Lean_Expr_appFn_x21(v___x_1418_);
v___x_1420_ = l_Lean_Expr_appArg_x21(v___x_1419_);
lean_dec_ref(v___x_1419_);
lean_inc_ref(v___x_1420_);
v___x_1421_ = l_Lean_Meta_getLevel(v___x_1420_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1421_) == 0)
{
lean_object* v_a_1422_; lean_object* v___x_1423_; 
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref_known(v___x_1421_, 1);
lean_inc_ref(v_body_1416_);
v___x_1423_ = l_Lean_Meta_getLevel(v_body_1416_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
if (lean_obj_tag(v___x_1423_) == 0)
{
lean_object* v_a_1424_; lean_object* v___x_1426_; uint8_t v_isShared_1427_; uint8_t v_isSharedCheck_1441_; 
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1441_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1441_ == 0)
{
v___x_1426_ = v___x_1423_;
v_isShared_1427_ = v_isSharedCheck_1441_;
goto v_resetjp_1425_;
}
else
{
lean_inc(v_a_1424_);
lean_dec(v___x_1423_);
v___x_1426_ = lean_box(0);
v_isShared_1427_ = v_isSharedCheck_1441_;
goto v_resetjp_1425_;
}
v_resetjp_1425_:
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1439_; 
v___x_1428_ = l_Lean_Expr_appArg_x21(v___x_1405_);
lean_dec_ref(v___x_1405_);
v___x_1429_ = l_Lean_Expr_appArg_x21(v_a_1388_);
lean_dec(v_a_1388_);
v___x_1430_ = l_Lean_Expr_appArg_x21(v___x_1418_);
lean_dec_ref(v___x_1418_);
v___x_1431_ = l_Lean_Expr_appArg_x21(v_a_1390_);
lean_dec(v_a_1390_);
v___x_1432_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1433_ = lean_box(0);
v___x_1434_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_a_1424_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1422_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_mkConst(v___x_1432_, v___x_1435_);
v___x_1437_ = l_Lean_mkApp8(v___x_1436_, v___x_1420_, v_body_1416_, v___x_1428_, v___x_1429_, v___x_1430_, v___x_1431_, v_h_u2081_1377_, v_h_u2082_1378_);
if (v_isShared_1427_ == 0)
{
lean_ctor_set(v___x_1426_, 0, v___x_1437_);
v___x_1439_ = v___x_1426_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1437_);
v___x_1439_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
return v___x_1439_;
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_dec(v_a_1422_);
lean_dec_ref(v___x_1420_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_body_1416_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1390_);
lean_dec(v_a_1388_);
lean_dec_ref(v_h_u2082_1378_);
lean_dec_ref(v_h_u2081_1377_);
v_a_1442_ = lean_ctor_get(v___x_1423_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1423_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1423_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1423_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
else
{
lean_object* v_a_1450_; lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1457_; 
lean_dec_ref(v___x_1420_);
lean_dec_ref(v___x_1418_);
lean_dec_ref(v_body_1416_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1390_);
lean_dec(v_a_1388_);
lean_dec_ref(v_h_u2082_1378_);
lean_dec_ref(v_h_u2081_1377_);
v_a_1450_ = lean_ctor_get(v___x_1421_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v___x_1421_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1452_ = v___x_1421_;
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
else
{
lean_inc(v_a_1450_);
lean_dec(v___x_1421_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1457_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1455_; 
if (v_isShared_1453_ == 0)
{
v___x_1455_ = v___x_1452_;
goto v_reusejp_1454_;
}
else
{
lean_object* v_reuseFailAlloc_1456_; 
v_reuseFailAlloc_1456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1456_, 0, v_a_1450_);
v___x_1455_ = v_reuseFailAlloc_1456_;
goto v_reusejp_1454_;
}
v_reusejp_1454_:
{
return v___x_1455_;
}
}
}
}
else
{
lean_dec_ref(v_body_1416_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1390_);
lean_dec_ref(v_h_u2082_1378_);
goto v___jp_1410_;
}
}
else
{
lean_dec(v_a_1409_);
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1390_);
lean_dec_ref(v_h_u2082_1378_);
goto v___jp_1410_;
}
v___jp_1410_:
{
lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
v___x_1411_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1412_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1413_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1377_, v_a_1388_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1411_, v___x_1414_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1415_;
}
}
else
{
lean_dec_ref(v___x_1405_);
lean_dec(v_a_1390_);
lean_dec(v_a_1388_);
lean_dec_ref(v_h_u2082_1378_);
lean_dec_ref(v_h_u2081_1377_);
return v___x_1408_;
}
}
}
}
else
{
lean_dec(v_a_1388_);
lean_dec_ref(v_h_u2082_1378_);
lean_dec_ref(v_h_u2081_1377_);
return v___x_1389_;
}
}
else
{
lean_dec_ref(v_h_u2082_1378_);
lean_dec_ref(v_h_u2081_1377_);
return v___x_1387_;
}
}
else
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = l_Lean_Expr_appArg_x21(v_h_u2082_1378_);
lean_dec_ref(v_h_u2082_1378_);
v___x_1459_ = l_Lean_Meta_mkCongrFun(v_h_u2081_1377_, v___x_1458_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1459_;
}
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1460_ = l_Lean_Expr_appArg_x21(v_h_u2081_1377_);
lean_dec_ref(v_h_u2081_1377_);
v___x_1461_ = l_Lean_Meta_mkCongrArg(v___x_1460_, v_h_u2082_1378_, v_a_1379_, v_a_1380_, v_a_1381_, v_a_1382_);
return v___x_1461_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr___boxed(lean_object* v_h_u2081_1462_, lean_object* v_h_u2082_1463_, lean_object* v_a_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Meta_mkCongr(v_h_u2081_1462_, v_h_u2082_1463_, v_a_1464_, v_a_1465_, v_a_1466_, v_a_1467_);
lean_dec(v_a_1467_);
lean_dec_ref(v_a_1466_);
lean_dec(v_a_1465_);
lean_dec_ref(v_a_1464_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(lean_object* v_e_1470_, lean_object* v___y_1471_){
_start:
{
uint8_t v___x_1473_; 
v___x_1473_ = l_Lean_Expr_hasMVar(v_e_1470_);
if (v___x_1473_ == 0)
{
lean_object* v___x_1474_; 
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_e_1470_);
return v___x_1474_;
}
else
{
lean_object* v___x_1475_; lean_object* v_mctx_1476_; lean_object* v___x_1477_; lean_object* v_fst_1478_; lean_object* v_snd_1479_; lean_object* v___x_1480_; lean_object* v_cache_1481_; lean_object* v_zetaDeltaFVarIds_1482_; lean_object* v_postponed_1483_; lean_object* v_diag_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1493_; 
v___x_1475_ = lean_st_ref_get(v___y_1471_);
v_mctx_1476_ = lean_ctor_get(v___x_1475_, 0);
lean_inc_ref(v_mctx_1476_);
lean_dec(v___x_1475_);
v___x_1477_ = l_Lean_instantiateMVarsCore(v_mctx_1476_, v_e_1470_);
v_fst_1478_ = lean_ctor_get(v___x_1477_, 0);
lean_inc(v_fst_1478_);
v_snd_1479_ = lean_ctor_get(v___x_1477_, 1);
lean_inc(v_snd_1479_);
lean_dec_ref(v___x_1477_);
v___x_1480_ = lean_st_ref_take(v___y_1471_);
v_cache_1481_ = lean_ctor_get(v___x_1480_, 1);
v_zetaDeltaFVarIds_1482_ = lean_ctor_get(v___x_1480_, 2);
v_postponed_1483_ = lean_ctor_get(v___x_1480_, 3);
v_diag_1484_ = lean_ctor_get(v___x_1480_, 4);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v___x_1480_, 0);
lean_dec(v_unused_1494_);
v___x_1486_ = v___x_1480_;
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_diag_1484_);
lean_inc(v_postponed_1483_);
lean_inc(v_zetaDeltaFVarIds_1482_);
lean_inc(v_cache_1481_);
lean_dec(v___x_1480_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1493_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v_snd_1479_);
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_snd_1479_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v_cache_1481_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_zetaDeltaFVarIds_1482_);
lean_ctor_set(v_reuseFailAlloc_1492_, 3, v_postponed_1483_);
lean_ctor_set(v_reuseFailAlloc_1492_, 4, v_diag_1484_);
v___x_1489_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_st_ref_set(v___y_1471_, v___x_1489_);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v_fst_1478_);
return v___x_1491_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg___boxed(lean_object* v_e_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1495_, v___y_1496_);
lean_dec(v___y_1496_);
return v_res_1498_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(lean_object* v_e_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v___x_1505_; 
v___x_1505_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1499_, v___y_1501_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___boxed(lean_object* v_e_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(v_e_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
return v_res_1512_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1513_, lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_){
_start:
{
lean_object* v_ks_1517_; lean_object* v_vs_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1542_; 
v_ks_1517_ = lean_ctor_get(v_x_1513_, 0);
v_vs_1518_ = lean_ctor_get(v_x_1513_, 1);
v_isSharedCheck_1542_ = !lean_is_exclusive(v_x_1513_);
if (v_isSharedCheck_1542_ == 0)
{
v___x_1520_ = v_x_1513_;
v_isShared_1521_ = v_isSharedCheck_1542_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_vs_1518_);
lean_inc(v_ks_1517_);
lean_dec(v_x_1513_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1542_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1522_; uint8_t v___x_1523_; 
v___x_1522_ = lean_array_get_size(v_ks_1517_);
v___x_1523_ = lean_nat_dec_lt(v_x_1514_, v___x_1522_);
if (v___x_1523_ == 0)
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1527_; 
lean_dec(v_x_1514_);
v___x_1524_ = lean_array_push(v_ks_1517_, v_x_1515_);
v___x_1525_ = lean_array_push(v_vs_1518_, v_x_1516_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v___x_1525_);
lean_ctor_set(v___x_1520_, 0, v___x_1524_);
v___x_1527_ = v___x_1520_;
goto v_reusejp_1526_;
}
else
{
lean_object* v_reuseFailAlloc_1528_; 
v_reuseFailAlloc_1528_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1528_, 0, v___x_1524_);
lean_ctor_set(v_reuseFailAlloc_1528_, 1, v___x_1525_);
v___x_1527_ = v_reuseFailAlloc_1528_;
goto v_reusejp_1526_;
}
v_reusejp_1526_:
{
return v___x_1527_;
}
}
else
{
lean_object* v_k_x27_1529_; uint8_t v___x_1530_; 
v_k_x27_1529_ = lean_array_fget_borrowed(v_ks_1517_, v_x_1514_);
v___x_1530_ = l_Lean_instBEqMVarId_beq(v_x_1515_, v_k_x27_1529_);
if (v___x_1530_ == 0)
{
lean_object* v___x_1532_; 
if (v_isShared_1521_ == 0)
{
v___x_1532_ = v___x_1520_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1536_; 
v_reuseFailAlloc_1536_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1536_, 0, v_ks_1517_);
lean_ctor_set(v_reuseFailAlloc_1536_, 1, v_vs_1518_);
v___x_1532_ = v_reuseFailAlloc_1536_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_nat_add(v_x_1514_, v___x_1533_);
lean_dec(v_x_1514_);
v_x_1513_ = v___x_1532_;
v_x_1514_ = v___x_1534_;
goto _start;
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1540_; 
v___x_1537_ = lean_array_fset(v_ks_1517_, v_x_1514_, v_x_1515_);
v___x_1538_ = lean_array_fset(v_vs_1518_, v_x_1514_, v_x_1516_);
lean_dec(v_x_1514_);
if (v_isShared_1521_ == 0)
{
lean_ctor_set(v___x_1520_, 1, v___x_1538_);
lean_ctor_set(v___x_1520_, 0, v___x_1537_);
v___x_1540_ = v___x_1520_;
goto v_reusejp_1539_;
}
else
{
lean_object* v_reuseFailAlloc_1541_; 
v_reuseFailAlloc_1541_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1541_, 0, v___x_1537_);
lean_ctor_set(v_reuseFailAlloc_1541_, 1, v___x_1538_);
v___x_1540_ = v_reuseFailAlloc_1541_;
goto v_reusejp_1539_;
}
v_reusejp_1539_:
{
return v___x_1540_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_1543_, lean_object* v_k_1544_, lean_object* v_v_1545_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_1543_, v___x_1546_, v_k_1544_, v_v_1545_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1549_, size_t v_x_1550_, size_t v_x_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
if (lean_obj_tag(v_x_1549_) == 0)
{
lean_object* v_es_1554_; size_t v___x_1555_; size_t v___x_1556_; lean_object* v_j_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_es_1554_ = lean_ctor_get(v_x_1549_, 0);
v___x_1555_ = ((size_t)31ULL);
v___x_1556_ = lean_usize_land(v_x_1550_, v___x_1555_);
v_j_1557_ = lean_usize_to_nat(v___x_1556_);
v___x_1558_ = lean_array_get_size(v_es_1554_);
v___x_1559_ = lean_nat_dec_lt(v_j_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_dec(v_j_1557_);
lean_dec(v_x_1553_);
lean_dec(v_x_1552_);
return v_x_1549_;
}
else
{
lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1598_; 
lean_inc_ref(v_es_1554_);
v_isSharedCheck_1598_ = !lean_is_exclusive(v_x_1549_);
if (v_isSharedCheck_1598_ == 0)
{
lean_object* v_unused_1599_; 
v_unused_1599_ = lean_ctor_get(v_x_1549_, 0);
lean_dec(v_unused_1599_);
v___x_1561_ = v_x_1549_;
v_isShared_1562_ = v_isSharedCheck_1598_;
goto v_resetjp_1560_;
}
else
{
lean_dec(v_x_1549_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1598_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v_v_1563_; lean_object* v___x_1564_; lean_object* v_xs_x27_1565_; lean_object* v___y_1567_; 
v_v_1563_ = lean_array_fget(v_es_1554_, v_j_1557_);
v___x_1564_ = lean_box(0);
v_xs_x27_1565_ = lean_array_fset(v_es_1554_, v_j_1557_, v___x_1564_);
switch(lean_obj_tag(v_v_1563_))
{
case 0:
{
lean_object* v_key_1572_; lean_object* v_val_1573_; lean_object* v___x_1575_; uint8_t v_isShared_1576_; uint8_t v_isSharedCheck_1583_; 
v_key_1572_ = lean_ctor_get(v_v_1563_, 0);
v_val_1573_ = lean_ctor_get(v_v_1563_, 1);
v_isSharedCheck_1583_ = !lean_is_exclusive(v_v_1563_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1575_ = v_v_1563_;
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
else
{
lean_inc(v_val_1573_);
lean_inc(v_key_1572_);
lean_dec(v_v_1563_);
v___x_1575_ = lean_box(0);
v_isShared_1576_ = v_isSharedCheck_1583_;
goto v_resetjp_1574_;
}
v_resetjp_1574_:
{
uint8_t v___x_1577_; 
v___x_1577_ = l_Lean_instBEqMVarId_beq(v_x_1552_, v_key_1572_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; 
lean_del_object(v___x_1575_);
v___x_1578_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1572_, v_val_1573_, v_x_1552_, v_x_1553_);
v___x_1579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1579_, 0, v___x_1578_);
v___y_1567_ = v___x_1579_;
goto v___jp_1566_;
}
else
{
lean_object* v___x_1581_; 
lean_dec(v_val_1573_);
lean_dec(v_key_1572_);
if (v_isShared_1576_ == 0)
{
lean_ctor_set(v___x_1575_, 1, v_x_1553_);
lean_ctor_set(v___x_1575_, 0, v_x_1552_);
v___x_1581_ = v___x_1575_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_x_1552_);
lean_ctor_set(v_reuseFailAlloc_1582_, 1, v_x_1553_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
v___y_1567_ = v___x_1581_;
goto v___jp_1566_;
}
}
}
}
case 1:
{
lean_object* v_node_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1596_; 
v_node_1584_ = lean_ctor_get(v_v_1563_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_v_1563_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1586_ = v_v_1563_;
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_node_1584_);
lean_dec(v_v_1563_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1596_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
size_t v___x_1588_; size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1594_; 
v___x_1588_ = ((size_t)5ULL);
v___x_1589_ = lean_usize_shift_right(v_x_1550_, v___x_1588_);
v___x_1590_ = ((size_t)1ULL);
v___x_1591_ = lean_usize_add(v_x_1551_, v___x_1590_);
v___x_1592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_node_1584_, v___x_1589_, v___x_1591_, v_x_1552_, v_x_1553_);
if (v_isShared_1587_ == 0)
{
lean_ctor_set(v___x_1586_, 0, v___x_1592_);
v___x_1594_ = v___x_1586_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v___x_1592_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
v___y_1567_ = v___x_1594_;
goto v___jp_1566_;
}
}
}
default: 
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_x_1552_);
lean_ctor_set(v___x_1597_, 1, v_x_1553_);
v___y_1567_ = v___x_1597_;
goto v___jp_1566_;
}
}
v___jp_1566_:
{
lean_object* v___x_1568_; lean_object* v___x_1570_; 
v___x_1568_ = lean_array_fset(v_xs_x27_1565_, v_j_1557_, v___y_1567_);
lean_dec(v_j_1557_);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 0, v___x_1568_);
v___x_1570_ = v___x_1561_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1568_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
else
{
lean_object* v_ks_1600_; lean_object* v_vs_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1621_; 
v_ks_1600_ = lean_ctor_get(v_x_1549_, 0);
v_vs_1601_ = lean_ctor_get(v_x_1549_, 1);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_x_1549_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1603_ = v_x_1549_;
v_isShared_1604_ = v_isSharedCheck_1621_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_vs_1601_);
lean_inc(v_ks_1600_);
lean_dec(v_x_1549_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1621_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1606_; 
if (v_isShared_1604_ == 0)
{
v___x_1606_ = v___x_1603_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_ks_1600_);
lean_ctor_set(v_reuseFailAlloc_1620_, 1, v_vs_1601_);
v___x_1606_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v_newNode_1607_; uint8_t v___y_1609_; size_t v___x_1615_; uint8_t v___x_1616_; 
v_newNode_1607_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v___x_1606_, v_x_1552_, v_x_1553_);
v___x_1615_ = ((size_t)7ULL);
v___x_1616_ = lean_usize_dec_le(v___x_1615_, v_x_1551_);
if (v___x_1616_ == 0)
{
lean_object* v___x_1617_; lean_object* v___x_1618_; uint8_t v___x_1619_; 
v___x_1617_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1607_);
v___x_1618_ = lean_unsigned_to_nat(4u);
v___x_1619_ = lean_nat_dec_lt(v___x_1617_, v___x_1618_);
lean_dec(v___x_1617_);
v___y_1609_ = v___x_1619_;
goto v___jp_1608_;
}
else
{
v___y_1609_ = v___x_1616_;
goto v___jp_1608_;
}
v___jp_1608_:
{
if (v___y_1609_ == 0)
{
lean_object* v_ks_1610_; lean_object* v_vs_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; 
v_ks_1610_ = lean_ctor_get(v_newNode_1607_, 0);
lean_inc_ref(v_ks_1610_);
v_vs_1611_ = lean_ctor_get(v_newNode_1607_, 1);
lean_inc_ref(v_vs_1611_);
lean_dec_ref(v_newNode_1607_);
v___x_1612_ = lean_unsigned_to_nat(0u);
v___x_1613_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1551_, v_ks_1610_, v_vs_1611_, v___x_1612_, v___x_1613_);
lean_dec_ref(v_vs_1611_);
lean_dec_ref(v_ks_1610_);
return v___x_1614_;
}
else
{
return v_newNode_1607_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_1622_, lean_object* v_keys_1623_, lean_object* v_vals_1624_, lean_object* v_i_1625_, lean_object* v_entries_1626_){
_start:
{
lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___x_1627_ = lean_array_get_size(v_keys_1623_);
v___x_1628_ = lean_nat_dec_lt(v_i_1625_, v___x_1627_);
if (v___x_1628_ == 0)
{
lean_dec(v_i_1625_);
return v_entries_1626_;
}
else
{
lean_object* v_k_1629_; lean_object* v_v_1630_; uint64_t v___x_1631_; size_t v_h_1632_; size_t v___x_1633_; lean_object* v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; size_t v___x_1637_; size_t v_h_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_k_1629_ = lean_array_fget_borrowed(v_keys_1623_, v_i_1625_);
v_v_1630_ = lean_array_fget_borrowed(v_vals_1624_, v_i_1625_);
v___x_1631_ = l_Lean_instHashableMVarId_hash(v_k_1629_);
v_h_1632_ = lean_uint64_to_usize(v___x_1631_);
v___x_1633_ = ((size_t)5ULL);
v___x_1634_ = lean_unsigned_to_nat(1u);
v___x_1635_ = ((size_t)1ULL);
v___x_1636_ = lean_usize_sub(v_depth_1622_, v___x_1635_);
v___x_1637_ = lean_usize_mul(v___x_1633_, v___x_1636_);
v_h_1638_ = lean_usize_shift_right(v_h_1632_, v___x_1637_);
v___x_1639_ = lean_nat_add(v_i_1625_, v___x_1634_);
lean_dec(v_i_1625_);
lean_inc(v_v_1630_);
lean_inc(v_k_1629_);
v___x_1640_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_entries_1626_, v_h_1638_, v_depth_1622_, v_k_1629_, v_v_1630_);
v_i_1625_ = v___x_1639_;
v_entries_1626_ = v___x_1640_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1642_, lean_object* v_keys_1643_, lean_object* v_vals_1644_, lean_object* v_i_1645_, lean_object* v_entries_1646_){
_start:
{
size_t v_depth_boxed_1647_; lean_object* v_res_1648_; 
v_depth_boxed_1647_ = lean_unbox_usize(v_depth_1642_);
lean_dec(v_depth_1642_);
v_res_1648_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_1647_, v_keys_1643_, v_vals_1644_, v_i_1645_, v_entries_1646_);
lean_dec_ref(v_vals_1644_);
lean_dec_ref(v_keys_1643_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_, lean_object* v_x_1653_){
_start:
{
size_t v_x_1977__boxed_1654_; size_t v_x_1978__boxed_1655_; lean_object* v_res_1656_; 
v_x_1977__boxed_1654_ = lean_unbox_usize(v_x_1650_);
lean_dec(v_x_1650_);
v_x_1978__boxed_1655_ = lean_unbox_usize(v_x_1651_);
lean_dec(v_x_1651_);
v_res_1656_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1649_, v_x_1977__boxed_1654_, v_x_1978__boxed_1655_, v_x_1652_, v_x_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object* v_x_1657_, lean_object* v_x_1658_, lean_object* v_x_1659_){
_start:
{
uint64_t v___x_1660_; size_t v___x_1661_; size_t v___x_1662_; lean_object* v___x_1663_; 
v___x_1660_ = l_Lean_instHashableMVarId_hash(v_x_1658_);
v___x_1661_ = lean_uint64_to_usize(v___x_1660_);
v___x_1662_ = ((size_t)1ULL);
v___x_1663_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1657_, v___x_1661_, v___x_1662_, v_x_1658_, v_x_1659_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(lean_object* v_mvarId_1664_, lean_object* v_val_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; lean_object* v_mctx_1669_; lean_object* v_cache_1670_; lean_object* v_zetaDeltaFVarIds_1671_; lean_object* v_postponed_1672_; lean_object* v_diag_1673_; lean_object* v___x_1675_; uint8_t v_isShared_1676_; uint8_t v_isSharedCheck_1701_; 
v___x_1668_ = lean_st_ref_take(v___y_1666_);
v_mctx_1669_ = lean_ctor_get(v___x_1668_, 0);
v_cache_1670_ = lean_ctor_get(v___x_1668_, 1);
v_zetaDeltaFVarIds_1671_ = lean_ctor_get(v___x_1668_, 2);
v_postponed_1672_ = lean_ctor_get(v___x_1668_, 3);
v_diag_1673_ = lean_ctor_get(v___x_1668_, 4);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1668_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1675_ = v___x_1668_;
v_isShared_1676_ = v_isSharedCheck_1701_;
goto v_resetjp_1674_;
}
else
{
lean_inc(v_diag_1673_);
lean_inc(v_postponed_1672_);
lean_inc(v_zetaDeltaFVarIds_1671_);
lean_inc(v_cache_1670_);
lean_inc(v_mctx_1669_);
lean_dec(v___x_1668_);
v___x_1675_ = lean_box(0);
v_isShared_1676_ = v_isSharedCheck_1701_;
goto v_resetjp_1674_;
}
v_resetjp_1674_:
{
lean_object* v_depth_1677_; lean_object* v_levelAssignDepth_1678_; lean_object* v_lmvarCounter_1679_; lean_object* v_mvarCounter_1680_; lean_object* v_lDecls_1681_; lean_object* v_decls_1682_; lean_object* v_userNames_1683_; lean_object* v_lAssignment_1684_; lean_object* v_eAssignment_1685_; lean_object* v_dAssignment_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1700_; 
v_depth_1677_ = lean_ctor_get(v_mctx_1669_, 0);
v_levelAssignDepth_1678_ = lean_ctor_get(v_mctx_1669_, 1);
v_lmvarCounter_1679_ = lean_ctor_get(v_mctx_1669_, 2);
v_mvarCounter_1680_ = lean_ctor_get(v_mctx_1669_, 3);
v_lDecls_1681_ = lean_ctor_get(v_mctx_1669_, 4);
v_decls_1682_ = lean_ctor_get(v_mctx_1669_, 5);
v_userNames_1683_ = lean_ctor_get(v_mctx_1669_, 6);
v_lAssignment_1684_ = lean_ctor_get(v_mctx_1669_, 7);
v_eAssignment_1685_ = lean_ctor_get(v_mctx_1669_, 8);
v_dAssignment_1686_ = lean_ctor_get(v_mctx_1669_, 9);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_mctx_1669_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1688_ = v_mctx_1669_;
v_isShared_1689_ = v_isSharedCheck_1700_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_dAssignment_1686_);
lean_inc(v_eAssignment_1685_);
lean_inc(v_lAssignment_1684_);
lean_inc(v_userNames_1683_);
lean_inc(v_decls_1682_);
lean_inc(v_lDecls_1681_);
lean_inc(v_mvarCounter_1680_);
lean_inc(v_lmvarCounter_1679_);
lean_inc(v_levelAssignDepth_1678_);
lean_inc(v_depth_1677_);
lean_dec(v_mctx_1669_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1700_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_eAssignment_1685_, v_mvarId_1664_, v_val_1665_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 8, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_depth_1677_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_levelAssignDepth_1678_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_lmvarCounter_1679_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_mvarCounter_1680_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_lDecls_1681_);
lean_ctor_set(v_reuseFailAlloc_1699_, 5, v_decls_1682_);
lean_ctor_set(v_reuseFailAlloc_1699_, 6, v_userNames_1683_);
lean_ctor_set(v_reuseFailAlloc_1699_, 7, v_lAssignment_1684_);
lean_ctor_set(v_reuseFailAlloc_1699_, 8, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1699_, 9, v_dAssignment_1686_);
v___x_1692_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1694_; 
if (v_isShared_1676_ == 0)
{
lean_ctor_set(v___x_1675_, 0, v___x_1692_);
v___x_1694_ = v___x_1675_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_cache_1670_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_zetaDeltaFVarIds_1671_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_postponed_1672_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_diag_1673_);
v___x_1694_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_st_ref_set(v___y_1666_, v___x_1694_);
v___x_1696_ = lean_box(0);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1696_);
return v___x_1697_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg___boxed(lean_object* v_mvarId_1702_, lean_object* v_val_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1702_, v_val_1703_, v___y_1704_);
lean_dec(v___y_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(lean_object* v_as_1707_, size_t v_i_1708_, size_t v_stop_1709_, lean_object* v_b_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
uint8_t v___x_1716_; 
v___x_1716_ = lean_usize_dec_eq(v_i_1708_, v_stop_1709_);
if (v___x_1716_ == 0)
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1717_ = lean_array_uget_borrowed(v_as_1707_, v_i_1708_);
lean_inc(v___x_1717_);
v___x_1718_ = l_Lean_MVarId_getDecl(v___x_1717_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v_type_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v_type_1720_ = lean_ctor_get(v_a_1719_, 2);
lean_inc_ref(v_type_1720_);
lean_dec(v_a_1719_);
v___x_1721_ = lean_box(0);
v___x_1722_ = l_Lean_Meta_synthInstance(v_type_1720_, v___x_1721_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
if (lean_obj_tag(v___x_1722_) == 0)
{
lean_object* v_a_1723_; lean_object* v___x_1724_; 
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
lean_inc(v___x_1717_);
v___x_1724_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v___x_1717_, v_a_1723_, v___y_1712_);
if (lean_obj_tag(v___x_1724_) == 0)
{
lean_object* v_a_1725_; size_t v___x_1726_; size_t v___x_1727_; 
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = ((size_t)1ULL);
v___x_1727_ = lean_usize_add(v_i_1708_, v___x_1726_);
v_i_1708_ = v___x_1727_;
v_b_1710_ = v_a_1725_;
goto _start;
}
else
{
return v___x_1724_;
}
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
v_a_1729_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1722_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1722_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
v_a_1737_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1718_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1718_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v_b_1710_);
return v___x_1745_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2___boxed(lean_object* v_as_1746_, lean_object* v_i_1747_, lean_object* v_stop_1748_, lean_object* v_b_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
size_t v_i_boxed_1755_; size_t v_stop_boxed_1756_; lean_object* v_res_1757_; 
v_i_boxed_1755_ = lean_unbox_usize(v_i_1747_);
lean_dec(v_i_1747_);
v_stop_boxed_1756_ = lean_unbox_usize(v_stop_1748_);
lean_dec(v_stop_1748_);
v_res_1757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_as_1746_, v_i_boxed_1755_, v_stop_boxed_1756_, v_b_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v___y_1751_);
lean_dec_ref(v___y_1750_);
lean_dec_ref(v_as_1746_);
return v_res_1757_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2(void){
_start:
{
lean_object* v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1));
v___x_1762_ = l_Lean_MessageData_ofFormat(v___x_1761_);
return v___x_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* v_methodName_1763_, lean_object* v_f_1764_, lean_object* v_args_1765_, lean_object* v_instMVars_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_, lean_object* v_a_1770_){
_start:
{
lean_object* v___y_1807_; lean_object* v___x_1816_; lean_object* v___x_1817_; uint8_t v___x_1818_; 
v___x_1816_ = lean_unsigned_to_nat(0u);
v___x_1817_ = lean_array_get_size(v_instMVars_1766_);
v___x_1818_ = lean_nat_dec_lt(v___x_1816_, v___x_1817_);
if (v___x_1818_ == 0)
{
goto v___jp_1772_;
}
else
{
lean_object* v___x_1819_; uint8_t v___x_1820_; 
v___x_1819_ = lean_box(0);
v___x_1820_ = lean_nat_dec_le(v___x_1817_, v___x_1817_);
if (v___x_1820_ == 0)
{
if (v___x_1818_ == 0)
{
goto v___jp_1772_;
}
else
{
size_t v___x_1821_; size_t v___x_1822_; lean_object* v___x_1823_; 
v___x_1821_ = ((size_t)0ULL);
v___x_1822_ = lean_usize_of_nat(v___x_1817_);
v___x_1823_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1766_, v___x_1821_, v___x_1822_, v___x_1819_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
v___y_1807_ = v___x_1823_;
goto v___jp_1806_;
}
}
else
{
size_t v___x_1824_; size_t v___x_1825_; lean_object* v___x_1826_; 
v___x_1824_ = ((size_t)0ULL);
v___x_1825_ = lean_usize_of_nat(v___x_1817_);
v___x_1826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1766_, v___x_1824_, v___x_1825_, v___x_1819_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
v___y_1807_ = v___x_1826_;
goto v___jp_1806_;
}
}
v___jp_1772_:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v_a_1775_; lean_object* v___x_1776_; 
v___x_1773_ = l_Lean_mkAppN(v_f_1764_, v_args_1765_);
v___x_1774_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v___x_1773_, v_a_1768_);
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc_n(v_a_1775_, 2);
lean_dec_ref(v___x_1774_);
v___x_1776_ = l_Lean_Meta_hasAssignableMVar(v_a_1775_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1797_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1779_ = v___x_1776_;
v_isShared_1780_ = v_isSharedCheck_1797_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1776_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1797_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
uint8_t v___x_1781_; 
v___x_1781_ = lean_unbox(v_a_1777_);
lean_dec(v_a_1777_);
if (v___x_1781_ == 0)
{
lean_object* v___x_1783_; 
lean_dec(v_methodName_1763_);
if (v_isShared_1780_ == 0)
{
lean_ctor_set(v___x_1779_, 0, v_a_1775_);
v___x_1783_ = v___x_1779_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1775_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
else
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_del_object(v___x_1779_);
v___x_1785_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2);
v___x_1786_ = l_Lean_indentExpr(v_a_1775_);
v___x_1787_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1787_, 0, v___x_1785_);
lean_ctor_set(v___x_1787_, 1, v___x_1786_);
v___x_1788_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_methodName_1763_, v___x_1787_, v_a_1767_, v_a_1768_, v_a_1769_, v_a_1770_);
v_a_1789_ = lean_ctor_get(v___x_1788_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1788_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1788_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1805_; 
lean_dec(v_a_1775_);
lean_dec(v_methodName_1763_);
v_a_1798_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1805_ == 0)
{
v___x_1800_ = v___x_1776_;
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1776_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1805_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1803_; 
if (v_isShared_1801_ == 0)
{
v___x_1803_ = v___x_1800_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_a_1798_);
v___x_1803_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
return v___x_1803_;
}
}
}
}
v___jp_1806_:
{
if (lean_obj_tag(v___y_1807_) == 0)
{
lean_dec_ref_known(v___y_1807_, 1);
goto v___jp_1772_;
}
else
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec_ref(v_f_1764_);
lean_dec(v_methodName_1763_);
v_a_1808_ = lean_ctor_get(v___y_1807_, 0);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___y_1807_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___y_1807_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___y_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* v_methodName_1827_, lean_object* v_f_1828_, lean_object* v_args_1829_, lean_object* v_instMVars_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_){
_start:
{
lean_object* v_res_1836_; 
v_res_1836_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v_methodName_1827_, v_f_1828_, v_args_1829_, v_instMVars_1830_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec_ref(v_instMVars_1830_);
lean_dec_ref(v_args_1829_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* v_mvarId_1837_, lean_object* v_val_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v___x_1844_; 
v___x_1844_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1837_, v_val_1838_, v___y_1840_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* v_mvarId_1845_, lean_object* v_val_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(v_mvarId_1845_, v_val_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* v_00_u03b2_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_, lean_object* v_x_1856_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_x_1854_, v_x_1855_, v_x_1856_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1858_, lean_object* v_x_1859_, size_t v_x_1860_, size_t v_x_1861_, lean_object* v_x_1862_, lean_object* v_x_1863_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1859_, v_x_1860_, v_x_1861_, v_x_1862_, v_x_1863_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_, lean_object* v_x_1870_){
_start:
{
size_t v_x_2421__boxed_1871_; size_t v_x_2422__boxed_1872_; lean_object* v_res_1873_; 
v_x_2421__boxed_1871_ = lean_unbox_usize(v_x_1867_);
lean_dec(v_x_1867_);
v_x_2422__boxed_1872_ = lean_unbox_usize(v_x_1868_);
lean_dec(v_x_1868_);
v_res_1873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1865_, v_x_1866_, v_x_2421__boxed_1871_, v_x_2422__boxed_1872_, v_x_1869_, v_x_1870_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1874_, lean_object* v_n_1875_, lean_object* v_k_1876_, lean_object* v_v_1877_){
_start:
{
lean_object* v___x_1878_; 
v___x_1878_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1875_, v_k_1876_, v_v_1877_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1879_, size_t v_depth_1880_, lean_object* v_keys_1881_, lean_object* v_vals_1882_, lean_object* v_heq_1883_, lean_object* v_i_1884_, lean_object* v_entries_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1880_, v_keys_1881_, v_vals_1882_, v_i_1884_, v_entries_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1887_, lean_object* v_depth_1888_, lean_object* v_keys_1889_, lean_object* v_vals_1890_, lean_object* v_heq_1891_, lean_object* v_i_1892_, lean_object* v_entries_1893_){
_start:
{
size_t v_depth_boxed_1894_; lean_object* v_res_1895_; 
v_depth_boxed_1894_ = lean_unbox_usize(v_depth_1888_);
lean_dec(v_depth_1888_);
v_res_1895_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1887_, v_depth_boxed_1894_, v_keys_1889_, v_vals_1890_, v_heq_1891_, v_i_1892_, v_entries_1893_);
lean_dec_ref(v_vals_1890_);
lean_dec_ref(v_keys_1889_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1897_, v_x_1898_, v_x_1899_, v_x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2));
v___x_1907_ = l_Lean_stringToMessageData(v___x_1906_);
return v___x_1907_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4));
v___x_1910_ = l_Lean_stringToMessageData(v___x_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7));
v___x_1915_ = l_Lean_MessageData_ofFormat(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* v_f_1916_, lean_object* v_xs_1917_, lean_object* v_type_1918_, lean_object* v_i_1919_, lean_object* v_j_1920_, lean_object* v_args_1921_, lean_object* v_instMVars_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_, lean_object* v_a_1926_){
_start:
{
lean_object* v___x_1928_; uint8_t v___x_1929_; 
v___x_1928_ = lean_array_get_size(v_xs_1917_);
v___x_1929_ = lean_nat_dec_le(v___x_1928_, v_i_1919_);
if (v___x_1929_ == 0)
{
if (lean_obj_tag(v_type_1918_) == 7)
{
lean_object* v_binderName_1930_; lean_object* v_binderType_1931_; lean_object* v_body_1932_; uint8_t v_binderInfo_1933_; lean_object* v___x_1934_; lean_object* v_d_1935_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; 
v_binderName_1930_ = lean_ctor_get(v_type_1918_, 0);
lean_inc(v_binderName_1930_);
v_binderType_1931_ = lean_ctor_get(v_type_1918_, 1);
lean_inc_ref(v_binderType_1931_);
v_body_1932_ = lean_ctor_get(v_type_1918_, 2);
lean_inc_ref(v_body_1932_);
v_binderInfo_1933_ = lean_ctor_get_uint8(v_type_1918_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1918_, 3);
v___x_1934_ = lean_array_get_size(v_args_1921_);
v_d_1935_ = lean_expr_instantiate_rev_range(v_binderType_1931_, v_j_1920_, v___x_1934_, v_args_1921_);
lean_dec_ref(v_binderType_1931_);
switch(v_binderInfo_1933_)
{
case 1:
{
v___y_1937_ = v_a_1923_;
v___y_1938_ = v_a_1924_;
v___y_1939_ = v_a_1925_;
v___y_1940_ = v_a_1926_;
goto v___jp_1936_;
}
case 2:
{
v___y_1937_ = v_a_1923_;
v___y_1938_ = v_a_1924_;
v___y_1939_ = v_a_1925_;
v___y_1940_ = v_a_1926_;
goto v___jp_1936_;
}
case 3:
{
lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1947_, 0, v_d_1935_);
v___x_1948_ = 1;
v___x_1949_ = l_Lean_Meta_mkFreshExprMVar(v___x_1947_, v___x_1948_, v_binderName_1930_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1949_) == 0)
{
lean_object* v_a_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v_a_1950_ = lean_ctor_get(v___x_1949_, 0);
lean_inc_n(v_a_1950_, 2);
lean_dec_ref_known(v___x_1949_, 1);
v___x_1951_ = lean_array_push(v_args_1921_, v_a_1950_);
v___x_1952_ = l_Lean_Expr_mvarId_x21(v_a_1950_);
lean_dec(v_a_1950_);
v___x_1953_ = lean_array_push(v_instMVars_1922_, v___x_1952_);
v_type_1918_ = v_body_1932_;
v_args_1921_ = v___x_1951_;
v_instMVars_1922_ = v___x_1953_;
goto _start;
}
else
{
lean_dec_ref(v_body_1932_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_f_1916_);
return v___x_1949_;
}
}
default: 
{
lean_object* v_x_1955_; lean_object* v___x_1956_; 
lean_dec(v_binderName_1930_);
v_x_1955_ = lean_array_fget_borrowed(v_xs_1917_, v_i_1919_);
lean_inc(v_a_1926_);
lean_inc_ref(v_a_1925_);
lean_inc(v_a_1924_);
lean_inc_ref(v_a_1923_);
lean_inc(v_x_1955_);
v___x_1956_ = lean_infer_type(v_x_1955_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1956_) == 0)
{
lean_object* v_a_1957_; uint8_t v___y_1959_; lean_object* v___x_1990_; uint8_t v_transparency_1991_; uint8_t v___x_1992_; uint8_t v___x_1993_; 
v_a_1957_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___x_1956_, 1);
v___x_1990_ = l_Lean_Meta_Context_config(v_a_1923_);
v_transparency_1991_ = lean_ctor_get_uint8(v___x_1990_, 9);
lean_dec_ref(v___x_1990_);
v___x_1992_ = 1;
v___x_1993_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
v___y_1959_ = v_transparency_1991_;
goto v___jp_1958_;
}
else
{
v___y_1959_ = v___x_1992_;
goto v___jp_1958_;
}
v___jp_1958_:
{
lean_object* v_keyedConfig_1960_; uint8_t v_trackZetaDelta_1961_; lean_object* v_zetaDeltaSet_1962_; lean_object* v_lctx_1963_; lean_object* v_localInstances_1964_; lean_object* v_defEqCtx_x3f_1965_; lean_object* v_synthPendingDepth_1966_; lean_object* v_customCanUnfoldPredicate_x3f_1967_; uint8_t v_univApprox_1968_; uint8_t v_inTypeClassResolution_1969_; uint8_t v_cacheInferType_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v_keyedConfig_1960_ = lean_ctor_get(v_a_1923_, 0);
v_trackZetaDelta_1961_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7);
v_zetaDeltaSet_1962_ = lean_ctor_get(v_a_1923_, 1);
v_lctx_1963_ = lean_ctor_get(v_a_1923_, 2);
v_localInstances_1964_ = lean_ctor_get(v_a_1923_, 3);
v_defEqCtx_x3f_1965_ = lean_ctor_get(v_a_1923_, 4);
v_synthPendingDepth_1966_ = lean_ctor_get(v_a_1923_, 5);
v_customCanUnfoldPredicate_x3f_1967_ = lean_ctor_get(v_a_1923_, 6);
v_univApprox_1968_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1969_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7 + 2);
v_cacheInferType_1970_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1960_);
v___x_1971_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_1959_, v_keyedConfig_1960_);
lean_inc(v_customCanUnfoldPredicate_x3f_1967_);
lean_inc(v_synthPendingDepth_1966_);
lean_inc(v_defEqCtx_x3f_1965_);
lean_inc_ref(v_localInstances_1964_);
lean_inc_ref(v_lctx_1963_);
lean_inc(v_zetaDeltaSet_1962_);
v___x_1972_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v_zetaDeltaSet_1962_);
lean_ctor_set(v___x_1972_, 2, v_lctx_1963_);
lean_ctor_set(v___x_1972_, 3, v_localInstances_1964_);
lean_ctor_set(v___x_1972_, 4, v_defEqCtx_x3f_1965_);
lean_ctor_set(v___x_1972_, 5, v_synthPendingDepth_1966_);
lean_ctor_set(v___x_1972_, 6, v_customCanUnfoldPredicate_x3f_1967_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*7, v_trackZetaDelta_1961_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*7 + 1, v_univApprox_1968_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1969_);
lean_ctor_set_uint8(v___x_1972_, sizeof(void*)*7 + 3, v_cacheInferType_1970_);
v___x_1973_ = l_Lean_Meta_isExprDefEq(v_d_1935_, v_a_1957_, v___x_1972_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec_ref_known(v___x_1972_, 7);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; uint8_t v___x_1975_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = lean_unbox(v_a_1974_);
lean_dec(v_a_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
lean_dec_ref(v_body_1932_);
lean_dec_ref(v_instMVars_1922_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
v___x_1976_ = l_Lean_mkAppN(v_f_1916_, v_args_1921_);
lean_dec_ref(v_args_1921_);
lean_inc(v_x_1955_);
v___x_1977_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1976_, v_x_1955_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1978_ = lean_unsigned_to_nat(1u);
v___x_1979_ = lean_nat_add(v_i_1919_, v___x_1978_);
lean_dec(v_i_1919_);
lean_inc(v_x_1955_);
v___x_1980_ = lean_array_push(v_args_1921_, v_x_1955_);
v_type_1918_ = v_body_1932_;
v_i_1919_ = v___x_1979_;
v_args_1921_ = v___x_1980_;
goto _start;
}
}
else
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1989_; 
lean_dec_ref(v_body_1932_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_f_1916_);
v_a_1982_ = lean_ctor_get(v___x_1973_, 0);
v_isSharedCheck_1989_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1989_ == 0)
{
v___x_1984_ = v___x_1973_;
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1973_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1989_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v___x_1987_; 
if (v_isShared_1985_ == 0)
{
v___x_1987_ = v___x_1984_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v_a_1982_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
}
}
}
else
{
lean_dec_ref(v_d_1935_);
lean_dec_ref(v_body_1932_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_f_1916_);
return v___x_1956_;
}
}
}
v___jp_1936_:
{
lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; 
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v_d_1935_);
v___x_1942_ = 0;
v___x_1943_ = l_Lean_Meta_mkFreshExprMVar(v___x_1941_, v___x_1942_, v_binderName_1930_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = lean_array_push(v_args_1921_, v_a_1944_);
v_type_1918_ = v_body_1932_;
v_args_1921_ = v___x_1945_;
v_a_1923_ = v___y_1937_;
v_a_1924_ = v___y_1938_;
v_a_1925_ = v___y_1939_;
v_a_1926_ = v___y_1940_;
goto _start;
}
else
{
lean_dec_ref(v_body_1932_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_f_1916_);
return v___x_1943_;
}
}
}
else
{
lean_object* v___x_1994_; lean_object* v_type_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_array_get_size(v_args_1921_);
v_type_1995_ = lean_expr_instantiate_rev_range(v_type_1918_, v_j_1920_, v___x_1994_, v_args_1921_);
lean_dec(v_j_1920_);
lean_dec_ref(v_type_1918_);
v___x_1996_ = l_Lean_Meta_whnfD(v_type_1995_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; uint8_t v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l_Lean_Expr_isForall(v_a_1997_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
lean_dec(v_a_1997_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_i_1919_);
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2000_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2001_ = l_Lean_indentExpr(v_f_1916_);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2007_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1917_, v___x_2005_, v___x_2006_);
v___x_2008_ = l_Lean_indentD(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2004_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1999_, v___x_2009_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
return v___x_2010_;
}
else
{
v_type_1918_ = v_a_1997_;
v_j_1920_ = v___x_1994_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_i_1919_);
lean_dec_ref(v_f_1916_);
return v___x_1996_;
}
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_type_1918_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2013_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2012_, v_f_1916_, v_args_1921_, v_instMVars_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
return v___x_2013_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2014_, lean_object* v_xs_2015_, lean_object* v_type_2016_, lean_object* v_i_2017_, lean_object* v_j_2018_, lean_object* v_args_2019_, lean_object* v_instMVars_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2014_, v_xs_2015_, v_type_2016_, v_i_2017_, v_j_2018_, v_args_2019_, v_instMVars_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec_ref(v_xs_2015_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2029_, lean_object* v_fType_2030_, lean_object* v_xs_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_){
_start:
{
lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2037_ = lean_unsigned_to_nat(0u);
v___x_2038_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2039_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2029_, v_xs_2031_, v_fType_2030_, v___x_2037_, v___x_2037_, v___x_2038_, v___x_2038_, v_a_2032_, v_a_2033_, v_a_2034_, v_a_2035_);
return v___x_2039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2040_, lean_object* v_fType_2041_, lean_object* v_xs_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2040_, v_fType_2041_, v_xs_2042_, v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
lean_dec_ref(v_xs_2042_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2049_, lean_object* v_x_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_){
_start:
{
if (lean_obj_tag(v_x_2049_) == 0)
{
lean_object* v___x_2056_; lean_object* v___x_2057_; 
v___x_2056_ = l_List_reverse___redArg(v_x_2050_);
v___x_2057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2057_, 0, v___x_2056_);
return v___x_2057_;
}
else
{
lean_object* v_tail_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2076_; 
v_tail_2058_ = lean_ctor_get(v_x_2049_, 1);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_x_2049_);
if (v_isSharedCheck_2076_ == 0)
{
lean_object* v_unused_2077_; 
v_unused_2077_ = lean_ctor_get(v_x_2049_, 0);
lean_dec(v_unused_2077_);
v___x_2060_ = v_x_2049_;
v_isShared_2061_ = v_isSharedCheck_2076_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_tail_2058_);
lean_dec(v_x_2049_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2076_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; 
v___x_2062_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_);
if (lean_obj_tag(v___x_2062_) == 0)
{
lean_object* v_a_2063_; lean_object* v___x_2065_; 
v_a_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2062_, 1);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v_x_2050_);
lean_ctor_set(v___x_2060_, 0, v_a_2063_);
v___x_2065_ = v___x_2060_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2063_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_x_2050_);
v___x_2065_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v_x_2049_ = v_tail_2058_;
v_x_2050_ = v___x_2065_;
goto _start;
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_del_object(v___x_2060_);
lean_dec(v_tail_2058_);
lean_dec(v_x_2050_);
v_a_2068_ = lean_ctor_get(v___x_2062_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2062_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2062_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2062_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2078_, lean_object* v_x_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
lean_object* v_res_2085_; 
v_res_2085_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2078_, v_x_2079_, v___y_2080_, v___y_2081_, v___y_2082_, v___y_2083_);
lean_dec(v___y_2083_);
lean_dec_ref(v___y_2082_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2087_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2088_, 0, v___x_2087_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2090_ = lean_unsigned_to_nat(0u);
v___x_2091_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_2091_, 0, v___x_2090_);
lean_ctor_set(v___x_2091_, 1, v___x_2090_);
lean_ctor_set(v___x_2091_, 2, v___x_2090_);
lean_ctor_set(v___x_2091_, 3, v___x_2090_);
lean_ctor_set(v___x_2091_, 4, v___x_2089_);
lean_ctor_set(v___x_2091_, 5, v___x_2089_);
lean_ctor_set(v___x_2091_, 6, v___x_2089_);
lean_ctor_set(v___x_2091_, 7, v___x_2089_);
lean_ctor_set(v___x_2091_, 8, v___x_2089_);
lean_ctor_set(v___x_2091_, 9, v___x_2089_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v___x_2092_ = lean_unsigned_to_nat(32u);
v___x_2093_ = lean_mk_empty_array_with_capacity(v___x_2092_);
v___x_2094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2093_);
return v___x_2094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2095_ = ((size_t)5ULL);
v___x_2096_ = lean_unsigned_to_nat(0u);
v___x_2097_ = lean_unsigned_to_nat(32u);
v___x_2098_ = lean_mk_empty_array_with_capacity(v___x_2097_);
v___x_2099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2100_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2100_, 0, v___x_2099_);
lean_ctor_set(v___x_2100_, 1, v___x_2098_);
lean_ctor_set(v___x_2100_, 2, v___x_2096_);
lean_ctor_set(v___x_2100_, 3, v___x_2096_);
lean_ctor_set_usize(v___x_2100_, 4, v___x_2095_);
return v___x_2100_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2101_ = lean_box(1);
v___x_2102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2103_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2104_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2104_, 0, v___x_2103_);
lean_ctor_set(v___x_2104_, 1, v___x_2102_);
lean_ctor_set(v___x_2104_, 2, v___x_2101_);
return v___x_2104_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2106_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2107_ = l_Lean_stringToMessageData(v___x_2106_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2110_ = l_Lean_stringToMessageData(v___x_2109_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2112_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2113_ = l_Lean_stringToMessageData(v___x_2112_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; 
v___x_2115_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2116_ = l_Lean_stringToMessageData(v___x_2115_);
return v___x_2116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2118_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2119_ = l_Lean_stringToMessageData(v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2121_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2122_ = l_Lean_stringToMessageData(v___x_2121_);
return v___x_2122_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2125_ = l_Lean_stringToMessageData(v___x_2124_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2126_, lean_object* v_declHint_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; lean_object* v_env_2131_; uint8_t v___x_2132_; 
v___x_2130_ = lean_st_ref_get(v___y_2128_);
v_env_2131_ = lean_ctor_get(v___x_2130_, 0);
lean_inc_ref(v_env_2131_);
lean_dec(v___x_2130_);
v___x_2132_ = l_Lean_Name_isAnonymous(v_declHint_2127_);
if (v___x_2132_ == 0)
{
uint8_t v_isExporting_2133_; 
v_isExporting_2133_ = lean_ctor_get_uint8(v_env_2131_, sizeof(void*)*8);
if (v_isExporting_2133_ == 0)
{
lean_object* v___x_2134_; 
lean_dec_ref(v_env_2131_);
lean_dec(v_declHint_2127_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v_msg_2126_);
return v___x_2134_;
}
else
{
lean_object* v___x_2135_; uint8_t v___x_2136_; 
lean_inc_ref(v_env_2131_);
v___x_2135_ = l_Lean_Environment_setExporting(v_env_2131_, v___x_2132_);
lean_inc(v_declHint_2127_);
lean_inc_ref(v___x_2135_);
v___x_2136_ = l_Lean_Environment_contains(v___x_2135_, v_declHint_2127_, v_isExporting_2133_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref(v___x_2135_);
lean_dec_ref(v_env_2131_);
lean_dec(v_declHint_2127_);
v___x_2137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2137_, 0, v_msg_2126_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_c_2143_; lean_object* v___x_2144_; 
v___x_2138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2140_ = l_Lean_Options_empty;
v___x_2141_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2135_);
lean_ctor_set(v___x_2141_, 1, v___x_2138_);
lean_ctor_set(v___x_2141_, 2, v___x_2139_);
lean_ctor_set(v___x_2141_, 3, v___x_2140_);
lean_inc(v_declHint_2127_);
v___x_2142_ = l_Lean_MessageData_ofConstName(v_declHint_2127_, v___x_2132_);
v_c_2143_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2143_, 0, v___x_2141_);
lean_ctor_set(v_c_2143_, 1, v___x_2142_);
v___x_2144_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2131_, v_declHint_2127_);
if (lean_obj_tag(v___x_2144_) == 0)
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_env_2131_);
lean_dec(v_declHint_2127_);
v___x_2145_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
lean_ctor_set(v___x_2146_, 1, v_c_2143_);
v___x_2147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2146_);
lean_ctor_set(v___x_2148_, 1, v___x_2147_);
v___x_2149_ = l_Lean_MessageData_note(v___x_2148_);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v_msg_2126_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2150_);
return v___x_2151_;
}
else
{
lean_object* v_val_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2187_; 
v_val_2152_ = lean_ctor_get(v___x_2144_, 0);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2144_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2154_ = v___x_2144_;
v_isShared_2155_ = v_isSharedCheck_2187_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_val_2152_);
lean_dec(v___x_2144_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2187_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v_mod_2159_; uint8_t v___x_2160_; 
v___x_2156_ = lean_box(0);
v___x_2157_ = l_Lean_Environment_header(v_env_2131_);
lean_dec_ref(v_env_2131_);
v___x_2158_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2157_);
v_mod_2159_ = lean_array_get(v___x_2156_, v___x_2158_, v_val_2152_);
lean_dec(v_val_2152_);
lean_dec_ref(v___x_2158_);
v___x_2160_ = l_Lean_isPrivateName(v_declHint_2127_);
lean_dec(v_declHint_2127_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2172_; 
v___x_2161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v_c_2143_);
v___x_2163_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = l_Lean_MessageData_ofName(v_mod_2159_);
v___x_2166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2164_);
lean_ctor_set(v___x_2166_, 1, v___x_2165_);
v___x_2167_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2168_, 0, v___x_2166_);
lean_ctor_set(v___x_2168_, 1, v___x_2167_);
v___x_2169_ = l_Lean_MessageData_note(v___x_2168_);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v_msg_2126_);
lean_ctor_set(v___x_2170_, 1, v___x_2169_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set_tag(v___x_2154_, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2170_);
v___x_2172_ = v___x_2154_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2170_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
else
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2185_; 
v___x_2174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v_c_2143_);
v___x_2176_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2177_, 0, v___x_2175_);
lean_ctor_set(v___x_2177_, 1, v___x_2176_);
v___x_2178_ = l_Lean_MessageData_ofName(v_mod_2159_);
v___x_2179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2177_);
lean_ctor_set(v___x_2179_, 1, v___x_2178_);
v___x_2180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2179_);
lean_ctor_set(v___x_2181_, 1, v___x_2180_);
v___x_2182_ = l_Lean_MessageData_note(v___x_2181_);
v___x_2183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2183_, 0, v_msg_2126_);
lean_ctor_set(v___x_2183_, 1, v___x_2182_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set_tag(v___x_2154_, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2183_);
v___x_2185_ = v___x_2154_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2186_; 
v_reuseFailAlloc_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2186_, 0, v___x_2183_);
v___x_2185_ = v_reuseFailAlloc_2186_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
return v___x_2185_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2188_; 
lean_dec_ref(v_env_2131_);
lean_dec(v_declHint_2127_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_msg_2126_);
return v___x_2188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2189_, lean_object* v_declHint_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v_res_2193_; 
v_res_2193_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2189_, v_declHint_2190_, v___y_2191_);
lean_dec(v___y_2191_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2194_, lean_object* v_declHint_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_){
_start:
{
lean_object* v___x_2201_; lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2211_; 
v___x_2201_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2194_, v_declHint_2195_, v___y_2199_);
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
v_isSharedCheck_2211_ = !lean_is_exclusive(v___x_2201_);
if (v_isSharedCheck_2211_ == 0)
{
v___x_2204_ = v___x_2201_;
v_isShared_2205_ = v_isSharedCheck_2211_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2201_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2211_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2206_ = l_Lean_unknownIdentifierMessageTag;
v___x_2207_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
lean_ctor_set(v___x_2207_, 1, v_a_2202_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 0, v___x_2207_);
v___x_2209_ = v___x_2204_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2210_; 
v_reuseFailAlloc_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2210_, 0, v___x_2207_);
v___x_2209_ = v_reuseFailAlloc_2210_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
return v___x_2209_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2212_, lean_object* v_declHint_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2212_, v_declHint_2213_, v___y_2214_, v___y_2215_, v___y_2216_, v___y_2217_);
lean_dec(v___y_2217_);
lean_dec_ref(v___y_2216_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2220_, lean_object* v_msg_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_fileName_2227_; lean_object* v_fileMap_2228_; lean_object* v_options_2229_; lean_object* v_currRecDepth_2230_; lean_object* v_maxRecDepth_2231_; lean_object* v_ref_2232_; lean_object* v_currNamespace_2233_; lean_object* v_openDecls_2234_; lean_object* v_initHeartbeats_2235_; lean_object* v_maxHeartbeats_2236_; lean_object* v_quotContext_2237_; lean_object* v_currMacroScope_2238_; uint8_t v_diag_2239_; lean_object* v_cancelTk_x3f_2240_; uint8_t v_suppressElabErrors_2241_; lean_object* v_inheritedTraceOptions_2242_; lean_object* v_ref_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_fileName_2227_ = lean_ctor_get(v___y_2224_, 0);
v_fileMap_2228_ = lean_ctor_get(v___y_2224_, 1);
v_options_2229_ = lean_ctor_get(v___y_2224_, 2);
v_currRecDepth_2230_ = lean_ctor_get(v___y_2224_, 3);
v_maxRecDepth_2231_ = lean_ctor_get(v___y_2224_, 4);
v_ref_2232_ = lean_ctor_get(v___y_2224_, 5);
v_currNamespace_2233_ = lean_ctor_get(v___y_2224_, 6);
v_openDecls_2234_ = lean_ctor_get(v___y_2224_, 7);
v_initHeartbeats_2235_ = lean_ctor_get(v___y_2224_, 8);
v_maxHeartbeats_2236_ = lean_ctor_get(v___y_2224_, 9);
v_quotContext_2237_ = lean_ctor_get(v___y_2224_, 10);
v_currMacroScope_2238_ = lean_ctor_get(v___y_2224_, 11);
v_diag_2239_ = lean_ctor_get_uint8(v___y_2224_, sizeof(void*)*14);
v_cancelTk_x3f_2240_ = lean_ctor_get(v___y_2224_, 12);
v_suppressElabErrors_2241_ = lean_ctor_get_uint8(v___y_2224_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2242_ = lean_ctor_get(v___y_2224_, 13);
v_ref_2243_ = l_Lean_replaceRef(v_ref_2220_, v_ref_2232_);
lean_inc_ref(v_inheritedTraceOptions_2242_);
lean_inc(v_cancelTk_x3f_2240_);
lean_inc(v_currMacroScope_2238_);
lean_inc(v_quotContext_2237_);
lean_inc(v_maxHeartbeats_2236_);
lean_inc(v_initHeartbeats_2235_);
lean_inc(v_openDecls_2234_);
lean_inc(v_currNamespace_2233_);
lean_inc(v_maxRecDepth_2231_);
lean_inc(v_currRecDepth_2230_);
lean_inc_ref(v_options_2229_);
lean_inc_ref(v_fileMap_2228_);
lean_inc_ref(v_fileName_2227_);
v___x_2244_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2244_, 0, v_fileName_2227_);
lean_ctor_set(v___x_2244_, 1, v_fileMap_2228_);
lean_ctor_set(v___x_2244_, 2, v_options_2229_);
lean_ctor_set(v___x_2244_, 3, v_currRecDepth_2230_);
lean_ctor_set(v___x_2244_, 4, v_maxRecDepth_2231_);
lean_ctor_set(v___x_2244_, 5, v_ref_2243_);
lean_ctor_set(v___x_2244_, 6, v_currNamespace_2233_);
lean_ctor_set(v___x_2244_, 7, v_openDecls_2234_);
lean_ctor_set(v___x_2244_, 8, v_initHeartbeats_2235_);
lean_ctor_set(v___x_2244_, 9, v_maxHeartbeats_2236_);
lean_ctor_set(v___x_2244_, 10, v_quotContext_2237_);
lean_ctor_set(v___x_2244_, 11, v_currMacroScope_2238_);
lean_ctor_set(v___x_2244_, 12, v_cancelTk_x3f_2240_);
lean_ctor_set(v___x_2244_, 13, v_inheritedTraceOptions_2242_);
lean_ctor_set_uint8(v___x_2244_, sizeof(void*)*14, v_diag_2239_);
lean_ctor_set_uint8(v___x_2244_, sizeof(void*)*14 + 1, v_suppressElabErrors_2241_);
v___x_2245_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2221_, v___y_2222_, v___y_2223_, v___x_2244_, v___y_2225_);
lean_dec_ref_known(v___x_2244_, 14);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2246_, lean_object* v_msg_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2246_, v_msg_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
lean_dec(v___y_2251_);
lean_dec_ref(v___y_2250_);
lean_dec(v___y_2249_);
lean_dec_ref(v___y_2248_);
lean_dec(v_ref_2246_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2254_, lean_object* v_msg_2255_, lean_object* v_declHint_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; lean_object* v_a_2263_; lean_object* v___x_2264_; 
v___x_2262_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2255_, v_declHint_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref(v___x_2262_);
v___x_2264_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2254_, v_a_2263_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
return v___x_2264_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2265_, lean_object* v_msg_2266_, lean_object* v_declHint_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2265_, v_msg_2266_, v_declHint_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
lean_dec(v_ref_2265_);
return v_res_2273_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2275_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2276_ = l_Lean_stringToMessageData(v___x_2275_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2279_ = l_Lean_stringToMessageData(v___x_2278_);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2280_, lean_object* v_constName_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v___x_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2287_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2288_ = 0;
lean_inc(v_constName_2281_);
v___x_2289_ = l_Lean_MessageData_ofConstName(v_constName_2281_, v___x_2288_);
v___x_2290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2287_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2292_, 0, v___x_2290_);
lean_ctor_set(v___x_2292_, 1, v___x_2291_);
v___x_2293_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2280_, v___x_2292_, v_constName_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2294_, lean_object* v_constName_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
lean_object* v_res_2301_; 
v_res_2301_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2294_, v_constName_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec(v_ref_2294_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_ref_2308_; lean_object* v___x_2309_; 
v_ref_2308_ = lean_ctor_get(v___y_2305_, 5);
v___x_2309_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2308_, v_constName_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2310_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
lean_dec(v___y_2314_);
lean_dec_ref(v___y_2313_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v___x_2323_; lean_object* v_env_2324_; uint8_t v___x_2325_; lean_object* v___x_2326_; 
v___x_2323_ = lean_st_ref_get(v___y_2321_);
v_env_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc_ref(v_env_2324_);
lean_dec(v___x_2323_);
v___x_2325_ = 0;
lean_inc(v_constName_2317_);
v___x_2326_ = l_Lean_Environment_findConstVal_x3f(v_env_2324_, v_constName_2317_, v___x_2325_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v___x_2327_; 
v___x_2327_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2327_;
}
else
{
lean_object* v_val_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2335_; 
lean_dec(v_constName_2317_);
v_val_2328_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2335_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2335_ == 0)
{
v___x_2330_ = v___x_2326_;
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_val_2328_);
lean_dec(v___x_2326_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2335_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2333_; 
if (v_isShared_2331_ == 0)
{
lean_ctor_set_tag(v___x_2330_, 0);
v___x_2333_ = v___x_2330_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v_val_2328_);
v___x_2333_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
return v___x_2333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
lean_object* v_res_2342_; 
v_res_2342_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2336_, v___y_2337_, v___y_2338_, v___y_2339_, v___y_2340_);
lean_dec(v___y_2340_);
lean_dec_ref(v___y_2339_);
lean_dec(v___y_2338_);
lean_dec_ref(v___y_2337_);
return v_res_2342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_){
_start:
{
lean_object* v___x_2349_; 
lean_inc(v_constName_2343_);
v___x_2349_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v_levelParams_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v_levelParams_2351_ = lean_ctor_get(v_a_2350_, 1);
v___x_2352_ = lean_box(0);
lean_inc(v_levelParams_2351_);
v___x_2353_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2351_, v___x_2352_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_object* v_a_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; 
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
lean_inc_n(v_a_2354_, 2);
lean_dec_ref_known(v___x_2353_, 1);
v___x_2355_ = l_Lean_mkConst(v_constName_2343_, v_a_2354_);
v___x_2356_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2350_, v_a_2354_, v_a_2347_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2365_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2359_ = v___x_2356_;
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2365_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2361_; lean_object* v___x_2363_; 
v___x_2361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2361_, 0, v___x_2355_);
lean_ctor_set(v___x_2361_, 1, v_a_2357_);
if (v_isShared_2360_ == 0)
{
lean_ctor_set(v___x_2359_, 0, v___x_2361_);
v___x_2363_ = v___x_2359_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v___x_2361_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
lean_dec_ref(v___x_2355_);
v_a_2366_ = lean_ctor_get(v___x_2356_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v___x_2356_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v___x_2356_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v_a_2350_);
lean_dec(v_constName_2343_);
v_a_2374_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2353_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2353_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v_constName_2343_);
v_a_2382_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2349_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2349_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_){
_start:
{
lean_object* v_res_2396_; 
v_res_2396_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2390_, v_a_2391_, v_a_2392_, v_a_2393_, v_a_2394_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
return v_res_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2397_, lean_object* v_constName_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v___x_2404_; 
v___x_2404_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2405_, lean_object* v_constName_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2405_, v_constName_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2413_, lean_object* v_ref_2414_, lean_object* v_constName_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v___x_2421_; 
v___x_2421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2414_, v_constName_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2422_, lean_object* v_ref_2423_, lean_object* v_constName_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2422_, v_ref_2423_, v_constName_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v_ref_2423_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2431_, lean_object* v_ref_2432_, lean_object* v_msg_2433_, lean_object* v_declHint_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v___x_2440_; 
v___x_2440_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2432_, v_msg_2433_, v_declHint_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2441_, lean_object* v_ref_2442_, lean_object* v_msg_2443_, lean_object* v_declHint_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2441_, v_ref_2442_, v_msg_2443_, v_declHint_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
lean_dec(v_ref_2442_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2451_, lean_object* v_declHint_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v___x_2458_; 
v___x_2458_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2451_, v_declHint_2452_, v___y_2456_);
return v___x_2458_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2459_, lean_object* v_declHint_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
lean_object* v_res_2466_; 
v_res_2466_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2459_, v_declHint_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2467_, lean_object* v_ref_2468_, lean_object* v_msg_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v___x_2475_; 
v___x_2475_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2468_, v_msg_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2476_, lean_object* v_ref_2477_, lean_object* v_msg_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_res_2484_; 
v_res_2484_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2476_, v_ref_2477_, v_msg_2478_, v___y_2479_, v___y_2480_, v___y_2481_, v___y_2482_);
lean_dec(v___y_2482_);
lean_dec_ref(v___y_2481_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v_ref_2477_);
return v_res_2484_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2486_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2487_ = l_Lean_stringToMessageData(v___x_2486_);
return v___x_2487_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; 
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2490_ = l_Lean_stringToMessageData(v___x_2489_);
return v___x_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2491_, lean_object* v_f_2492_, lean_object* v_inst_2493_, lean_object* v_xs_2494_, lean_object* v_x_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2501_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2502_ = lean_apply_1(v_inst_2491_, v_f_2492_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2505_, 0, v___x_2503_);
lean_ctor_set(v___x_2505_, 1, v___x_2504_);
v___x_2506_ = lean_apply_1(v_inst_2493_, v_xs_2494_);
v___x_2507_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2505_);
lean_ctor_set(v___x_2507_, 1, v___x_2506_);
v___x_2508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2508_, 0, v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2509_, lean_object* v_f_2510_, lean_object* v_inst_2511_, lean_object* v_xs_2512_, lean_object* v_x_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_){
_start:
{
lean_object* v_res_2519_; 
v_res_2519_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2509_, v_f_2510_, v_inst_2511_, v_xs_2512_, v_x_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v___y_2515_);
lean_dec_ref(v___y_2514_);
lean_dec_ref(v_x_2513_);
return v_res_2519_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2520_; 
v___x_2520_ = l_instMonadEIO(lean_box(0));
return v___x_2520_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2521_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2522_ = l_StateRefT_x27_instMonad___redArg(v___x_2521_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2529_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2530_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2531_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2530_, v___x_2529_);
return v___x_2531_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; 
v___x_2532_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2533_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2534_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2533_, v___x_2532_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2537_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2539_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2540_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2539_, v___x_2538_, v___x_2537_);
return v___x_2540_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___f_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; 
v___x_2541_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2542_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2543_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2544_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2543_, v___f_2542_, v___x_2541_);
return v___x_2544_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2545_; 
v___x_2545_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2545_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2547_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2549_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2551_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2550_);
return v___x_2551_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2552_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2553_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2552_);
return v___x_2553_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2565_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2566_ = l_Lean_Name_append(v___x_2565_, v___x_2564_);
return v___x_2566_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2573_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2574_ = l_Lean_Name_append(v___x_2573_, v___x_2572_);
return v___x_2574_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2575_; double v___x_2576_; 
v___x_2575_ = lean_unsigned_to_nat(1000000000u);
v___x_2576_ = lean_float_of_nat(v___x_2575_);
return v___x_2576_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2583_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2584_ = l_Lean_Name_append(v___x_2583_, v___x_2582_);
return v___x_2584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2585_, lean_object* v_inst_2586_, lean_object* v_f_2587_, lean_object* v_xs_2588_, lean_object* v_k_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v_toApplicative_2596_; lean_object* v_toFunctor_2597_; lean_object* v_toSeq_2598_; lean_object* v_toSeqLeft_2599_; lean_object* v_toSeqRight_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; lean_object* v___f_2607_; lean_object* v___f_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v_toApplicative_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2851_; 
v___x_2595_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2596_ = lean_ctor_get(v___x_2595_, 0);
v_toFunctor_2597_ = lean_ctor_get(v_toApplicative_2596_, 0);
v_toSeq_2598_ = lean_ctor_get(v_toApplicative_2596_, 2);
v_toSeqLeft_2599_ = lean_ctor_get(v_toApplicative_2596_, 3);
v_toSeqRight_2600_ = lean_ctor_get(v_toApplicative_2596_, 4);
v___f_2601_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2602_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2597_, 2);
v___f_2603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2603_, 0, v_toFunctor_2597_);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toFunctor_2597_);
v___x_2605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___f_2603_);
lean_ctor_set(v___x_2605_, 1, v___f_2604_);
lean_inc(v_toSeqRight_2600_);
v___f_2606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2606_, 0, v_toSeqRight_2600_);
lean_inc(v_toSeqLeft_2599_);
v___f_2607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2607_, 0, v_toSeqLeft_2599_);
lean_inc(v_toSeq_2598_);
v___f_2608_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2608_, 0, v_toSeq_2598_);
v___x_2609_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2605_);
lean_ctor_set(v___x_2609_, 1, v___f_2601_);
lean_ctor_set(v___x_2609_, 2, v___f_2608_);
lean_ctor_set(v___x_2609_, 3, v___f_2607_);
lean_ctor_set(v___x_2609_, 4, v___f_2606_);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___f_2602_);
v___x_2611_ = l_StateRefT_x27_instMonad___redArg(v___x_2610_);
v_toApplicative_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2851_ == 0)
{
lean_object* v_unused_2852_; 
v_unused_2852_ = lean_ctor_get(v___x_2611_, 1);
lean_dec(v_unused_2852_);
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2851_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_toApplicative_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2851_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v_toFunctor_2616_; lean_object* v_toSeq_2617_; lean_object* v_toSeqLeft_2618_; lean_object* v_toSeqRight_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2849_; 
v_toFunctor_2616_ = lean_ctor_get(v_toApplicative_2612_, 0);
v_toSeq_2617_ = lean_ctor_get(v_toApplicative_2612_, 2);
v_toSeqLeft_2618_ = lean_ctor_get(v_toApplicative_2612_, 3);
v_toSeqRight_2619_ = lean_ctor_get(v_toApplicative_2612_, 4);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_toApplicative_2612_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v_toApplicative_2612_, 1);
lean_dec(v_unused_2850_);
v___x_2621_ = v_toApplicative_2612_;
v_isShared_2622_ = v_isSharedCheck_2849_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_toSeqRight_2619_);
lean_inc(v_toSeqLeft_2618_);
lean_inc(v_toSeq_2617_);
lean_inc(v_toFunctor_2616_);
lean_dec(v_toApplicative_2612_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2849_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___f_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___x_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___f_2630_; lean_object* v___x_2632_; 
v___f_2623_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2624_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2616_);
v___f_2625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2625_, 0, v_toFunctor_2616_);
v___f_2626_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2626_, 0, v_toFunctor_2616_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___f_2625_);
lean_ctor_set(v___x_2627_, 1, v___f_2626_);
v___f_2628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2628_, 0, v_toSeqRight_2619_);
v___f_2629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2629_, 0, v_toSeqLeft_2618_);
v___f_2630_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2630_, 0, v_toSeq_2617_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 4, v___f_2628_);
lean_ctor_set(v___x_2621_, 3, v___f_2629_);
lean_ctor_set(v___x_2621_, 2, v___f_2630_);
lean_ctor_set(v___x_2621_, 1, v___f_2623_);
lean_ctor_set(v___x_2621_, 0, v___x_2627_);
v___x_2632_ = v___x_2621_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2627_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v___f_2623_);
lean_ctor_set(v_reuseFailAlloc_2848_, 2, v___f_2630_);
lean_ctor_set(v_reuseFailAlloc_2848_, 3, v___f_2629_);
lean_ctor_set(v_reuseFailAlloc_2848_, 4, v___f_2628_);
v___x_2632_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
lean_object* v___x_2634_; 
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 1, v___f_2624_);
lean_ctor_set(v___x_2614_, 0, v___x_2632_);
v___x_2634_ = v___x_2614_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2632_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v___f_2624_);
v___x_2634_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v_toMonadRef_2637_; lean_object* v___x_2638_; lean_object* v_options_2639_; uint8_t v_hasTrace_2640_; 
v___x_2635_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2636_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2637_ = lean_ctor_get(v___x_2636_, 0);
v___x_2638_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v_options_2639_ = lean_ctor_get(v_a_2592_, 2);
v_hasTrace_2640_ = lean_ctor_get_uint8(v_options_2639_, sizeof(void*)*1);
if (v_hasTrace_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref(v___x_2634_);
lean_dec(v_xs_2588_);
lean_dec(v_f_2587_);
lean_dec_ref(v_inst_2586_);
lean_dec_ref(v_inst_2585_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2641_ = lean_apply_5(v_k_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2641_) == 0)
{
return v___x_2641_;
}
else
{
lean_object* v_a_2642_; uint8_t v___y_2644_; uint8_t v___x_2653_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
v___x_2653_ = l_Lean_Exception_isInterrupt(v_a_2642_);
if (v___x_2653_ == 0)
{
uint8_t v___x_2654_; 
lean_inc(v_a_2642_);
v___x_2654_ = l_Lean_Exception_isRuntime(v_a_2642_);
v___y_2644_ = v___x_2654_;
goto v___jp_2643_;
}
else
{
v___y_2644_ = v___x_2653_;
goto v___jp_2643_;
}
v___jp_2643_:
{
if (v___y_2644_ == 0)
{
lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2651_ == 0)
{
lean_object* v_unused_2652_; 
v_unused_2652_ = lean_ctor_get(v___x_2641_, 0);
lean_dec(v_unused_2652_);
v___x_2646_ = v___x_2641_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_dec(v___x_2641_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2649_; 
if (v_isShared_2647_ == 0)
{
v___x_2649_ = v___x_2646_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2642_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_dec(v_a_2642_);
return v___x_2641_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2655_; lean_object* v___x_2656_; lean_object* v___y_2658_; lean_object* v___y_2659_; uint8_t v___y_2660_; lean_object* v___y_2685_; lean_object* v_a_2686_; lean_object* v___f_2689_; lean_object* v___f_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; uint8_t v___x_2694_; lean_object* v___y_2696_; lean_object* v___y_2697_; lean_object* v_a_2698_; lean_object* v___y_2712_; lean_object* v___y_2713_; lean_object* v_a_2714_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___y_2719_; uint8_t v___y_2720_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v_a_2731_; lean_object* v___y_2735_; lean_object* v___y_2736_; lean_object* v_a_2737_; lean_object* v___y_2740_; lean_object* v___y_2741_; lean_object* v_a_2742_; lean_object* v___y_2753_; lean_object* v___y_2754_; lean_object* v_a_2755_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2761_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v_a_2772_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v_a_2778_; 
v_inheritedTraceOptions_2655_ = lean_ctor_get(v_a_2592_, 13);
v___x_2656_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2689_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2689_, 0, v_inst_2585_);
lean_closure_set(v___f_2689_, 1, v_f_2587_);
lean_closure_set(v___f_2689_, 2, v_inst_2586_);
lean_closure_set(v___f_2689_, 3, v_xs_2588_);
v___f_2690_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2694_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; uint8_t v___x_2821_; 
v___x_2818_ = l_Lean_KVMap_instValueBool;
v___x_2819_ = l_Lean_trace_profiler;
v___x_2820_ = l_Lean_Option_get___redArg(v___x_2818_, v_options_2639_, v___x_2819_);
v___x_2821_ = lean_unbox(v___x_2820_);
lean_dec(v___x_2820_);
if (v___x_2821_ == 0)
{
lean_object* v___x_2822_; 
lean_dec_ref(v___f_2689_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2822_ = lean_apply_5(v_k_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; uint8_t v___x_2826_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
v___x_2824_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2825_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2826_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2825_);
if (v___x_2826_ == 0)
{
lean_dec(v_a_2823_);
lean_dec_ref(v___x_2634_);
return v___x_2822_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_9744__overap_2828_; lean_object* v___x_2829_; 
lean_dec_ref_known(v___x_2822_, 1);
lean_inc(v_a_2823_);
v___x_2827_ = l_Lean_MessageData_ofExpr(v_a_2823_);
lean_inc_ref(v_toMonadRef_2637_);
lean_inc_ref(v___x_2634_);
v___x_9744__overap_2828_ = l_Lean_addTrace___redArg(v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, v___x_2824_, v___x_2827_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2829_ = lean_apply_5(v___x_9744__overap_2828_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec_ref(v___x_2634_);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2829_, 0);
lean_dec(v_unused_2837_);
v___x_2831_ = v___x_2829_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_dec(v___x_2829_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v_a_2823_);
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2823_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_a_2823_);
v_a_2838_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2829_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2829_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
lean_inc(v_a_2838_);
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
v___y_2685_ = v___x_2843_;
v_a_2686_ = v_a_2838_;
goto v___jp_2684_;
}
}
}
}
}
else
{
lean_object* v_a_2846_; 
v_a_2846_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2846_);
v___y_2685_ = v___x_2822_;
v_a_2686_ = v_a_2846_;
goto v___jp_2684_;
}
}
else
{
goto v___jp_2780_;
}
}
else
{
goto v___jp_2780_;
}
v___jp_2657_:
{
if (v___y_2660_ == 0)
{
lean_object* v___x_2661_; lean_object* v___x_2662_; uint8_t v___x_2663_; 
lean_dec_ref(v___y_2658_);
v___x_2661_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2662_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2662_);
if (v___x_2663_ == 0)
{
lean_object* v___x_2664_; 
lean_dec_ref(v___x_2634_);
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___y_2659_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_9526__overap_2666_; lean_object* v___x_2667_; 
lean_inc_ref(v___y_2659_);
v___x_2665_ = l_Lean_Exception_toMessageData(v___y_2659_);
lean_inc_ref(v_toMonadRef_2637_);
v___x_9526__overap_2666_ = l_Lean_addTrace___redArg(v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, v___x_2661_, v___x_2665_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2667_ = lean_apply_5(v___x_9526__overap_2666_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; 
v_unused_2675_ = lean_ctor_get(v___x_2667_, 0);
lean_dec(v_unused_2675_);
v___x_2669_ = v___x_2667_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_dec(v___x_2667_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set_tag(v___x_2669_, 1);
lean_ctor_set(v___x_2669_, 0, v___y_2659_);
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v___y_2659_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec_ref(v___y_2659_);
v_a_2676_ = lean_ctor_get(v___x_2667_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2667_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2667_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2667_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2659_);
lean_dec_ref(v___x_2634_);
return v___y_2658_;
}
}
v___jp_2684_:
{
uint8_t v___x_2687_; 
v___x_2687_ = l_Lean_Exception_isInterrupt(v_a_2686_);
if (v___x_2687_ == 0)
{
uint8_t v___x_2688_; 
lean_inc_ref(v_a_2686_);
v___x_2688_ = l_Lean_Exception_isRuntime(v_a_2686_);
v___y_2658_ = v___y_2685_;
v___y_2659_ = v_a_2686_;
v___y_2660_ = v___x_2688_;
goto v___jp_2657_;
}
else
{
v___y_2658_ = v___y_2685_;
v___y_2659_ = v_a_2686_;
v___y_2660_ = v___x_2687_;
goto v___jp_2657_;
}
}
v___jp_2695_:
{
lean_object* v___x_2699_; double v___x_2700_; double v___x_2701_; double v___x_2702_; double v___x_2703_; double v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_9620__overap_2709_; lean_object* v___x_2710_; 
v___x_2699_ = lean_io_mono_nanos_now();
v___x_2700_ = lean_float_of_nat(v___y_2697_);
v___x_2701_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2702_ = lean_float_div(v___x_2700_, v___x_2701_);
v___x_2703_ = lean_float_of_nat(v___x_2699_);
v___x_2704_ = lean_float_div(v___x_2703_, v___x_2701_);
v___x_2705_ = lean_box_float(v___x_2702_);
v___x_2706_ = lean_box_float(v___x_2704_);
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v_a_2698_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
lean_inc_ref(v_toMonadRef_2637_);
v___x_9620__overap_2709_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, lean_box(0), v___x_2638_, v___f_2690_, v___x_2691_, v_hasTrace_2640_, v___x_2692_, v_options_2639_, v___x_2694_, v___y_2696_, v___f_2689_, v___x_2708_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2710_ = lean_apply_5(v___x_9620__overap_2709_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
return v___x_2710_;
}
v___jp_2711_:
{
lean_object* v___x_2715_; 
v___x_2715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2715_, 0, v_a_2714_);
v___y_2696_ = v___y_2712_;
v___y_2697_ = v___y_2713_;
v_a_2698_ = v___x_2715_;
goto v___jp_2695_;
}
v___jp_2716_:
{
if (v___y_2720_ == 0)
{
lean_object* v___x_2721_; lean_object* v___x_2722_; uint8_t v___x_2723_; 
v___x_2721_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2722_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2722_);
if (v___x_2723_ == 0)
{
v___y_2712_ = v___y_2717_;
v___y_2713_ = v___y_2718_;
v_a_2714_ = v___y_2719_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_9638__overap_2725_; lean_object* v___x_2726_; 
lean_inc_ref(v___y_2719_);
v___x_2724_ = l_Lean_Exception_toMessageData(v___y_2719_);
lean_inc_ref(v_toMonadRef_2637_);
lean_inc_ref(v___x_2634_);
v___x_9638__overap_2725_ = l_Lean_addTrace___redArg(v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, v___x_2721_, v___x_2724_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2726_ = lean_apply_5(v___x_9638__overap_2725_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_dec_ref_known(v___x_2726_, 1);
v___y_2712_ = v___y_2717_;
v___y_2713_ = v___y_2718_;
v_a_2714_ = v___y_2719_;
goto v___jp_2711_;
}
else
{
lean_object* v_a_2727_; 
lean_dec_ref(v___y_2719_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___y_2712_ = v___y_2717_;
v___y_2713_ = v___y_2718_;
v_a_2714_ = v_a_2727_;
goto v___jp_2711_;
}
}
}
else
{
v___y_2712_ = v___y_2717_;
v___y_2713_ = v___y_2718_;
v_a_2714_ = v___y_2719_;
goto v___jp_2711_;
}
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
v___y_2717_ = v___y_2729_;
v___y_2718_ = v___y_2730_;
v___y_2719_ = v_a_2731_;
v___y_2720_ = v___x_2733_;
goto v___jp_2716_;
}
else
{
v___y_2717_ = v___y_2729_;
v___y_2718_ = v___y_2730_;
v___y_2719_ = v_a_2731_;
v___y_2720_ = v___x_2732_;
goto v___jp_2716_;
}
}
v___jp_2734_:
{
lean_object* v___x_2738_; 
v___x_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2738_, 0, v_a_2737_);
v___y_2696_ = v___y_2735_;
v___y_2697_ = v___y_2736_;
v_a_2698_ = v___x_2738_;
goto v___jp_2695_;
}
v___jp_2739_:
{
lean_object* v___x_2743_; double v___x_2744_; double v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_9680__overap_2750_; lean_object* v___x_2751_; 
v___x_2743_ = lean_io_get_num_heartbeats();
v___x_2744_ = lean_float_of_nat(v___y_2741_);
v___x_2745_ = lean_float_of_nat(v___x_2743_);
v___x_2746_ = lean_box_float(v___x_2744_);
v___x_2747_ = lean_box_float(v___x_2745_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_a_2742_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
lean_inc_ref(v_toMonadRef_2637_);
v___x_9680__overap_2750_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, lean_box(0), v___x_2638_, v___f_2690_, v___x_2691_, v_hasTrace_2640_, v___x_2692_, v_options_2639_, v___x_2694_, v___y_2740_, v___f_2689_, v___x_2749_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2751_ = lean_apply_5(v___x_9680__overap_2750_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
return v___x_2751_;
}
v___jp_2752_:
{
lean_object* v___x_2756_; 
v___x_2756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2756_, 0, v_a_2755_);
v___y_2740_ = v___y_2753_;
v___y_2741_ = v___y_2754_;
v_a_2742_ = v___x_2756_;
goto v___jp_2739_;
}
v___jp_2757_:
{
if (v___y_2761_ == 0)
{
lean_object* v___x_2762_; lean_object* v___x_2763_; uint8_t v___x_2764_; 
v___x_2762_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2763_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2763_);
if (v___x_2764_ == 0)
{
v___y_2753_ = v___y_2758_;
v___y_2754_ = v___y_2760_;
v_a_2755_ = v___y_2759_;
goto v___jp_2752_;
}
else
{
lean_object* v___x_2765_; lean_object* v___x_9698__overap_2766_; lean_object* v___x_2767_; 
lean_inc_ref(v___y_2759_);
v___x_2765_ = l_Lean_Exception_toMessageData(v___y_2759_);
lean_inc_ref(v_toMonadRef_2637_);
lean_inc_ref(v___x_2634_);
v___x_9698__overap_2766_ = l_Lean_addTrace___redArg(v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, v___x_2762_, v___x_2765_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2767_ = lean_apply_5(v___x_9698__overap_2766_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_dec_ref_known(v___x_2767_, 1);
v___y_2753_ = v___y_2758_;
v___y_2754_ = v___y_2760_;
v_a_2755_ = v___y_2759_;
goto v___jp_2752_;
}
else
{
lean_object* v_a_2768_; 
lean_dec_ref(v___y_2759_);
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref_known(v___x_2767_, 1);
v___y_2753_ = v___y_2758_;
v___y_2754_ = v___y_2760_;
v_a_2755_ = v_a_2768_;
goto v___jp_2752_;
}
}
}
else
{
v___y_2753_ = v___y_2758_;
v___y_2754_ = v___y_2760_;
v_a_2755_ = v___y_2759_;
goto v___jp_2752_;
}
}
v___jp_2769_:
{
uint8_t v___x_2773_; 
v___x_2773_ = l_Lean_Exception_isInterrupt(v_a_2772_);
if (v___x_2773_ == 0)
{
uint8_t v___x_2774_; 
lean_inc_ref(v_a_2772_);
v___x_2774_ = l_Lean_Exception_isRuntime(v_a_2772_);
v___y_2758_ = v___y_2770_;
v___y_2759_ = v_a_2772_;
v___y_2760_ = v___y_2771_;
v___y_2761_ = v___x_2774_;
goto v___jp_2757_;
}
else
{
v___y_2758_ = v___y_2770_;
v___y_2759_ = v_a_2772_;
v___y_2760_ = v___y_2771_;
v___y_2761_ = v___x_2773_;
goto v___jp_2757_;
}
}
v___jp_2775_:
{
lean_object* v___x_2779_; 
v___x_2779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2779_, 0, v_a_2778_);
v___y_2740_ = v___y_2776_;
v___y_2741_ = v___y_2777_;
v_a_2742_ = v___x_2779_;
goto v___jp_2739_;
}
v___jp_2780_:
{
lean_object* v___x_9597__overap_2781_; lean_object* v___x_2782_; 
lean_inc_ref(v___x_2634_);
v___x_9597__overap_2781_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2634_, v___x_2635_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2782_ = lean_apply_5(v___x_9597__overap_2781_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = l_Lean_KVMap_instValueBool;
v___x_2785_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2786_ = l_Lean_Option_get___redArg(v___x_2784_, v_options_2639_, v___x_2785_);
v___x_2787_ = lean_unbox(v___x_2786_);
lean_dec(v___x_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = lean_io_mono_nanos_now();
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2789_ = lean_apply_5(v_k_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2789_) == 0)
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; 
v_a_2790_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2789_, 1);
v___x_2791_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2792_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2792_);
if (v___x_2793_ == 0)
{
v___y_2735_ = v_a_2783_;
v___y_2736_ = v___x_2788_;
v_a_2737_ = v_a_2790_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2794_; lean_object* v___x_9660__overap_2795_; lean_object* v___x_2796_; 
lean_inc(v_a_2790_);
v___x_2794_ = l_Lean_MessageData_ofExpr(v_a_2790_);
lean_inc_ref(v_toMonadRef_2637_);
lean_inc_ref(v___x_2634_);
v___x_9660__overap_2795_ = l_Lean_addTrace___redArg(v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, v___x_2791_, v___x_2794_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2796_ = lean_apply_5(v___x_9660__overap_2795_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_dec_ref_known(v___x_2796_, 1);
v___y_2735_ = v_a_2783_;
v___y_2736_ = v___x_2788_;
v_a_2737_ = v_a_2790_;
goto v___jp_2734_;
}
else
{
lean_object* v_a_2797_; 
lean_dec(v_a_2790_);
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v___y_2729_ = v_a_2783_;
v___y_2730_ = v___x_2788_;
v_a_2731_ = v_a_2797_;
goto v___jp_2728_;
}
}
}
else
{
lean_object* v_a_2798_; 
v_a_2798_ = lean_ctor_get(v___x_2789_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2789_, 1);
v___y_2729_ = v_a_2783_;
v___y_2730_ = v___x_2788_;
v_a_2731_ = v_a_2798_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2800_ = lean_apply_5(v_k_2589_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2800_) == 0)
{
lean_object* v_a_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; uint8_t v___x_2804_; 
v_a_2801_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2800_, 1);
v___x_2802_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2803_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2803_);
if (v___x_2804_ == 0)
{
v___y_2776_ = v_a_2783_;
v___y_2777_ = v___x_2799_;
v_a_2778_ = v_a_2801_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2805_; lean_object* v___x_9720__overap_2806_; lean_object* v___x_2807_; 
lean_inc(v_a_2801_);
v___x_2805_ = l_Lean_MessageData_ofExpr(v_a_2801_);
lean_inc_ref(v_toMonadRef_2637_);
lean_inc_ref(v___x_2634_);
v___x_9720__overap_2806_ = l_Lean_addTrace___redArg(v___x_2634_, v___x_2635_, v_toMonadRef_2637_, v___x_2656_, v___x_2802_, v___x_2805_);
lean_inc(v_a_2593_);
lean_inc_ref(v_a_2592_);
lean_inc(v_a_2591_);
lean_inc_ref(v_a_2590_);
v___x_2807_ = lean_apply_5(v___x_9720__overap_2806_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_, lean_box(0));
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_dec_ref_known(v___x_2807_, 1);
v___y_2776_ = v_a_2783_;
v___y_2777_ = v___x_2799_;
v_a_2778_ = v_a_2801_;
goto v___jp_2775_;
}
else
{
lean_object* v_a_2808_; 
lean_dec(v_a_2801_);
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___y_2770_ = v_a_2783_;
v___y_2771_ = v___x_2799_;
v_a_2772_ = v_a_2808_;
goto v___jp_2769_;
}
}
}
else
{
lean_object* v_a_2809_; 
v_a_2809_ = lean_ctor_get(v___x_2800_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2800_, 1);
v___y_2770_ = v_a_2783_;
v___y_2771_ = v___x_2799_;
v_a_2772_ = v_a_2809_;
goto v___jp_2769_;
}
}
}
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec_ref(v___f_2689_);
lean_dec_ref(v___x_2634_);
lean_dec_ref(v_k_2589_);
v_a_2810_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2782_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2782_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2853_, lean_object* v_inst_2854_, lean_object* v_f_2855_, lean_object* v_xs_2856_, lean_object* v_k_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2853_, v_inst_2854_, v_f_2855_, v_xs_2856_, v_k_2857_, v_a_2858_, v_a_2859_, v_a_2860_, v_a_2861_);
lean_dec(v_a_2861_);
lean_dec_ref(v_a_2860_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
return v_res_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2864_, lean_object* v_00_u03b2_2865_, lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_f_2868_, lean_object* v_xs_2869_, lean_object* v_k_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_){
_start:
{
lean_object* v___x_2876_; 
v___x_2876_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2866_, v_inst_2867_, v_f_2868_, v_xs_2869_, v_k_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_f_2881_, lean_object* v_xs_2882_, lean_object* v_k_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_, lean_object* v_a_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2877_, v_00_u03b2_2878_, v_inst_2879_, v_inst_2880_, v_f_2881_, v_xs_2882_, v_k_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
lean_dec(v_a_2887_);
lean_dec_ref(v_a_2886_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2890_, uint8_t v_allowLevelAssignments_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_, lean_object* v___y_2894_, lean_object* v___y_2895_){
_start:
{
lean_object* v___x_2897_; 
v___x_2897_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2891_, v_k_2890_, v___y_2892_, v___y_2893_, v___y_2894_, v___y_2895_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2897_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2897_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
v_a_2906_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2897_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2897_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2914_, lean_object* v_allowLevelAssignments_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2921_; lean_object* v_res_2922_; 
v_allowLevelAssignments_boxed_2921_ = lean_unbox(v_allowLevelAssignments_2915_);
v_res_2922_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2914_, v_allowLevelAssignments_boxed_2921_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2923_, lean_object* v_k_2924_, uint8_t v_allowLevelAssignments_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
lean_object* v___x_2931_; 
v___x_2931_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2924_, v_allowLevelAssignments_2925_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2932_, lean_object* v_k_2933_, lean_object* v_allowLevelAssignments_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_, lean_object* v___y_2939_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2940_; lean_object* v_res_2941_; 
v_allowLevelAssignments_boxed_2940_ = lean_unbox(v_allowLevelAssignments_2934_);
v_res_2941_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2932_, v_k_2933_, v_allowLevelAssignments_boxed_2940_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
lean_dec(v___y_2938_);
lean_dec_ref(v___y_2937_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
return v_res_2941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2942_, lean_object* v_xs_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_){
_start:
{
lean_object* v___x_2949_; 
v___x_2949_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2942_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v_fst_2951_; lean_object* v_snd_2952_; lean_object* v___x_2953_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v_fst_2951_ = lean_ctor_get(v_a_2950_, 0);
lean_inc(v_fst_2951_);
v_snd_2952_ = lean_ctor_get(v_a_2950_, 1);
lean_inc(v_snd_2952_);
lean_dec(v_a_2950_);
v___x_2953_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2951_, v_snd_2952_, v_xs_2943_, v___y_2944_, v___y_2945_, v___y_2946_, v___y_2947_);
return v___x_2953_;
}
else
{
lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
v_a_2954_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2949_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2949_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2962_, lean_object* v_xs_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_){
_start:
{
lean_object* v_res_2969_; 
v_res_2969_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2962_, v_xs_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
lean_dec(v___y_2967_);
lean_dec_ref(v___y_2966_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec_ref(v_xs_2963_);
return v_res_2969_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2970_ = lean_unsigned_to_nat(32u);
v___x_2971_ = lean_mk_empty_array_with_capacity(v___x_2970_);
v___x_2972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2971_);
return v___x_2972_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2973_ = ((size_t)5ULL);
v___x_2974_ = lean_unsigned_to_nat(0u);
v___x_2975_ = lean_unsigned_to_nat(32u);
v___x_2976_ = lean_mk_empty_array_with_capacity(v___x_2975_);
v___x_2977_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2978_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
lean_ctor_set(v___x_2978_, 1, v___x_2976_);
lean_ctor_set(v___x_2978_, 2, v___x_2974_);
lean_ctor_set(v___x_2978_, 3, v___x_2974_);
lean_ctor_set_usize(v___x_2978_, 4, v___x_2973_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2979_){
_start:
{
lean_object* v___x_2981_; lean_object* v_traceState_2982_; lean_object* v_traces_2983_; lean_object* v___x_2984_; lean_object* v_traceState_2985_; lean_object* v_env_2986_; lean_object* v_nextMacroScope_2987_; lean_object* v_ngen_2988_; lean_object* v_auxDeclNGen_2989_; lean_object* v_cache_2990_; lean_object* v_messages_2991_; lean_object* v_infoState_2992_; lean_object* v_snapshotTasks_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3012_; 
v___x_2981_ = lean_st_ref_get(v___y_2979_);
v_traceState_2982_ = lean_ctor_get(v___x_2981_, 4);
lean_inc_ref(v_traceState_2982_);
lean_dec(v___x_2981_);
v_traces_2983_ = lean_ctor_get(v_traceState_2982_, 0);
lean_inc_ref(v_traces_2983_);
lean_dec_ref(v_traceState_2982_);
v___x_2984_ = lean_st_ref_take(v___y_2979_);
v_traceState_2985_ = lean_ctor_get(v___x_2984_, 4);
v_env_2986_ = lean_ctor_get(v___x_2984_, 0);
v_nextMacroScope_2987_ = lean_ctor_get(v___x_2984_, 1);
v_ngen_2988_ = lean_ctor_get(v___x_2984_, 2);
v_auxDeclNGen_2989_ = lean_ctor_get(v___x_2984_, 3);
v_cache_2990_ = lean_ctor_get(v___x_2984_, 5);
v_messages_2991_ = lean_ctor_get(v___x_2984_, 6);
v_infoState_2992_ = lean_ctor_get(v___x_2984_, 7);
v_snapshotTasks_2993_ = lean_ctor_get(v___x_2984_, 8);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2995_ = v___x_2984_;
v_isShared_2996_ = v_isSharedCheck_3012_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_snapshotTasks_2993_);
lean_inc(v_infoState_2992_);
lean_inc(v_messages_2991_);
lean_inc(v_cache_2990_);
lean_inc(v_traceState_2985_);
lean_inc(v_auxDeclNGen_2989_);
lean_inc(v_ngen_2988_);
lean_inc(v_nextMacroScope_2987_);
lean_inc(v_env_2986_);
lean_dec(v___x_2984_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3012_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
uint64_t v_tid_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3010_; 
v_tid_2997_ = lean_ctor_get_uint64(v_traceState_2985_, sizeof(void*)*1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v_traceState_2985_);
if (v_isSharedCheck_3010_ == 0)
{
lean_object* v_unused_3011_; 
v_unused_3011_ = lean_ctor_get(v_traceState_2985_, 0);
lean_dec(v_unused_3011_);
v___x_2999_ = v_traceState_2985_;
v_isShared_3000_ = v_isSharedCheck_3010_;
goto v_resetjp_2998_;
}
else
{
lean_dec(v_traceState_2985_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3010_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3001_; lean_object* v___x_3003_; 
v___x_3001_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_3000_ == 0)
{
lean_ctor_set(v___x_2999_, 0, v___x_3001_);
v___x_3003_ = v___x_2999_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v___x_3001_);
lean_ctor_set_uint64(v_reuseFailAlloc_3009_, sizeof(void*)*1, v_tid_2997_);
v___x_3003_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3005_; 
if (v_isShared_2996_ == 0)
{
lean_ctor_set(v___x_2995_, 4, v___x_3003_);
v___x_3005_ = v___x_2995_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3008_; 
v_reuseFailAlloc_3008_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3008_, 0, v_env_2986_);
lean_ctor_set(v_reuseFailAlloc_3008_, 1, v_nextMacroScope_2987_);
lean_ctor_set(v_reuseFailAlloc_3008_, 2, v_ngen_2988_);
lean_ctor_set(v_reuseFailAlloc_3008_, 3, v_auxDeclNGen_2989_);
lean_ctor_set(v_reuseFailAlloc_3008_, 4, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3008_, 5, v_cache_2990_);
lean_ctor_set(v_reuseFailAlloc_3008_, 6, v_messages_2991_);
lean_ctor_set(v_reuseFailAlloc_3008_, 7, v_infoState_2992_);
lean_ctor_set(v_reuseFailAlloc_3008_, 8, v_snapshotTasks_2993_);
v___x_3005_ = v_reuseFailAlloc_3008_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_3006_ = lean_st_ref_set(v___y_2979_, v___x_3005_);
v___x_3007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3007_, 0, v_traces_2983_);
return v___x_3007_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3013_, lean_object* v___y_3014_){
_start:
{
lean_object* v_res_3015_; 
v_res_3015_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3013_);
lean_dec(v___y_3013_);
return v_res_3015_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3016_, lean_object* v_opt_3017_){
_start:
{
lean_object* v_name_3018_; lean_object* v_defValue_3019_; lean_object* v_map_3020_; lean_object* v___x_3021_; 
v_name_3018_ = lean_ctor_get(v_opt_3017_, 0);
v_defValue_3019_ = lean_ctor_get(v_opt_3017_, 1);
v_map_3020_ = lean_ctor_get(v_opts_3016_, 0);
v___x_3021_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3020_, v_name_3018_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_inc(v_defValue_3019_);
return v_defValue_3019_;
}
else
{
lean_object* v_val_3022_; 
v_val_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_val_3022_);
lean_dec_ref_known(v___x_3021_, 1);
if (lean_obj_tag(v_val_3022_) == 3)
{
lean_object* v_v_3023_; 
v_v_3023_ = lean_ctor_get(v_val_3022_, 0);
lean_inc(v_v_3023_);
lean_dec_ref_known(v_val_3022_, 1);
return v_v_3023_;
}
else
{
lean_dec(v_val_3022_);
lean_inc(v_defValue_3019_);
return v_defValue_3019_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3024_, lean_object* v_opt_3025_){
_start:
{
lean_object* v_res_3026_; 
v_res_3026_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3024_, v_opt_3025_);
lean_dec_ref(v_opt_3025_);
lean_dec_ref(v_opts_3024_);
return v_res_3026_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3027_, lean_object* v_opt_3028_){
_start:
{
lean_object* v_name_3029_; lean_object* v_defValue_3030_; lean_object* v_map_3031_; lean_object* v___x_3032_; 
v_name_3029_ = lean_ctor_get(v_opt_3028_, 0);
v_defValue_3030_ = lean_ctor_get(v_opt_3028_, 1);
v_map_3031_ = lean_ctor_get(v_opts_3027_, 0);
v___x_3032_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3031_, v_name_3029_);
if (lean_obj_tag(v___x_3032_) == 0)
{
uint8_t v___x_3033_; 
v___x_3033_ = lean_unbox(v_defValue_3030_);
return v___x_3033_;
}
else
{
lean_object* v_val_3034_; 
v_val_3034_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_val_3034_);
lean_dec_ref_known(v___x_3032_, 1);
if (lean_obj_tag(v_val_3034_) == 1)
{
uint8_t v_v_3035_; 
v_v_3035_ = lean_ctor_get_uint8(v_val_3034_, 0);
lean_dec_ref_known(v_val_3034_, 0);
return v_v_3035_;
}
else
{
uint8_t v___x_3036_; 
lean_dec(v_val_3034_);
v___x_3036_ = lean_unbox(v_defValue_3030_);
return v___x_3036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3037_, lean_object* v_opt_3038_){
_start:
{
uint8_t v_res_3039_; lean_object* v_r_3040_; 
v_res_3039_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3037_, v_opt_3038_);
lean_dec_ref(v_opt_3038_);
lean_dec_ref(v_opts_3037_);
v_r_3040_ = lean_box(v_res_3039_);
return v_r_3040_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3041_){
_start:
{
if (lean_obj_tag(v_e_3041_) == 0)
{
uint8_t v___x_3042_; 
v___x_3042_ = 2;
return v___x_3042_;
}
else
{
lean_object* v_a_3043_; uint8_t v___x_3044_; 
v_a_3043_ = lean_ctor_get(v_e_3041_, 0);
v___x_3044_ = l_Lean_Expr_hasSyntheticSorry(v_a_3043_);
if (v___x_3044_ == 0)
{
uint8_t v___x_3045_; 
v___x_3045_ = 0;
return v___x_3045_;
}
else
{
uint8_t v___x_3046_; 
v___x_3046_ = 1;
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3047_){
_start:
{
uint8_t v_res_3048_; lean_object* v_r_3049_; 
v_res_3048_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3047_);
lean_dec_ref(v_e_3047_);
v_r_3049_ = lean_box(v_res_3048_);
return v_r_3049_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3050_, size_t v_i_3051_, lean_object* v_bs_3052_){
_start:
{
uint8_t v___x_3053_; 
v___x_3053_ = lean_usize_dec_lt(v_i_3051_, v_sz_3050_);
if (v___x_3053_ == 0)
{
return v_bs_3052_;
}
else
{
lean_object* v_v_3054_; lean_object* v_msg_3055_; lean_object* v___x_3056_; lean_object* v_bs_x27_3057_; size_t v___x_3058_; size_t v___x_3059_; lean_object* v___x_3060_; 
v_v_3054_ = lean_array_uget_borrowed(v_bs_3052_, v_i_3051_);
v_msg_3055_ = lean_ctor_get(v_v_3054_, 1);
lean_inc_ref(v_msg_3055_);
v___x_3056_ = lean_unsigned_to_nat(0u);
v_bs_x27_3057_ = lean_array_uset(v_bs_3052_, v_i_3051_, v___x_3056_);
v___x_3058_ = ((size_t)1ULL);
v___x_3059_ = lean_usize_add(v_i_3051_, v___x_3058_);
v___x_3060_ = lean_array_uset(v_bs_x27_3057_, v_i_3051_, v_msg_3055_);
v_i_3051_ = v___x_3059_;
v_bs_3052_ = v___x_3060_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3062_, lean_object* v_i_3063_, lean_object* v_bs_3064_){
_start:
{
size_t v_sz_boxed_3065_; size_t v_i_boxed_3066_; lean_object* v_res_3067_; 
v_sz_boxed_3065_ = lean_unbox_usize(v_sz_3062_);
lean_dec(v_sz_3062_);
v_i_boxed_3066_ = lean_unbox_usize(v_i_3063_);
lean_dec(v_i_3063_);
v_res_3067_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3065_, v_i_boxed_3066_, v_bs_3064_);
return v_res_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3068_, lean_object* v_data_3069_, lean_object* v_ref_3070_, lean_object* v_msg_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_fileName_3077_; lean_object* v_fileMap_3078_; lean_object* v_options_3079_; lean_object* v_currRecDepth_3080_; lean_object* v_maxRecDepth_3081_; lean_object* v_ref_3082_; lean_object* v_currNamespace_3083_; lean_object* v_openDecls_3084_; lean_object* v_initHeartbeats_3085_; lean_object* v_maxHeartbeats_3086_; lean_object* v_quotContext_3087_; lean_object* v_currMacroScope_3088_; uint8_t v_diag_3089_; lean_object* v_cancelTk_x3f_3090_; uint8_t v_suppressElabErrors_3091_; lean_object* v_inheritedTraceOptions_3092_; lean_object* v___x_3093_; lean_object* v_traceState_3094_; lean_object* v_traces_3095_; lean_object* v_ref_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; size_t v_sz_3099_; size_t v___x_3100_; lean_object* v___x_3101_; lean_object* v_msg_3102_; lean_object* v___x_3103_; lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3141_; 
v_fileName_3077_ = lean_ctor_get(v___y_3074_, 0);
v_fileMap_3078_ = lean_ctor_get(v___y_3074_, 1);
v_options_3079_ = lean_ctor_get(v___y_3074_, 2);
v_currRecDepth_3080_ = lean_ctor_get(v___y_3074_, 3);
v_maxRecDepth_3081_ = lean_ctor_get(v___y_3074_, 4);
v_ref_3082_ = lean_ctor_get(v___y_3074_, 5);
v_currNamespace_3083_ = lean_ctor_get(v___y_3074_, 6);
v_openDecls_3084_ = lean_ctor_get(v___y_3074_, 7);
v_initHeartbeats_3085_ = lean_ctor_get(v___y_3074_, 8);
v_maxHeartbeats_3086_ = lean_ctor_get(v___y_3074_, 9);
v_quotContext_3087_ = lean_ctor_get(v___y_3074_, 10);
v_currMacroScope_3088_ = lean_ctor_get(v___y_3074_, 11);
v_diag_3089_ = lean_ctor_get_uint8(v___y_3074_, sizeof(void*)*14);
v_cancelTk_x3f_3090_ = lean_ctor_get(v___y_3074_, 12);
v_suppressElabErrors_3091_ = lean_ctor_get_uint8(v___y_3074_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3092_ = lean_ctor_get(v___y_3074_, 13);
v___x_3093_ = lean_st_ref_get(v___y_3075_);
v_traceState_3094_ = lean_ctor_get(v___x_3093_, 4);
lean_inc_ref(v_traceState_3094_);
lean_dec(v___x_3093_);
v_traces_3095_ = lean_ctor_get(v_traceState_3094_, 0);
lean_inc_ref(v_traces_3095_);
lean_dec_ref(v_traceState_3094_);
v_ref_3096_ = l_Lean_replaceRef(v_ref_3070_, v_ref_3082_);
lean_inc_ref(v_inheritedTraceOptions_3092_);
lean_inc(v_cancelTk_x3f_3090_);
lean_inc(v_currMacroScope_3088_);
lean_inc(v_quotContext_3087_);
lean_inc(v_maxHeartbeats_3086_);
lean_inc(v_initHeartbeats_3085_);
lean_inc(v_openDecls_3084_);
lean_inc(v_currNamespace_3083_);
lean_inc(v_maxRecDepth_3081_);
lean_inc(v_currRecDepth_3080_);
lean_inc_ref(v_options_3079_);
lean_inc_ref(v_fileMap_3078_);
lean_inc_ref(v_fileName_3077_);
v___x_3097_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3097_, 0, v_fileName_3077_);
lean_ctor_set(v___x_3097_, 1, v_fileMap_3078_);
lean_ctor_set(v___x_3097_, 2, v_options_3079_);
lean_ctor_set(v___x_3097_, 3, v_currRecDepth_3080_);
lean_ctor_set(v___x_3097_, 4, v_maxRecDepth_3081_);
lean_ctor_set(v___x_3097_, 5, v_ref_3096_);
lean_ctor_set(v___x_3097_, 6, v_currNamespace_3083_);
lean_ctor_set(v___x_3097_, 7, v_openDecls_3084_);
lean_ctor_set(v___x_3097_, 8, v_initHeartbeats_3085_);
lean_ctor_set(v___x_3097_, 9, v_maxHeartbeats_3086_);
lean_ctor_set(v___x_3097_, 10, v_quotContext_3087_);
lean_ctor_set(v___x_3097_, 11, v_currMacroScope_3088_);
lean_ctor_set(v___x_3097_, 12, v_cancelTk_x3f_3090_);
lean_ctor_set(v___x_3097_, 13, v_inheritedTraceOptions_3092_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*14, v_diag_3089_);
lean_ctor_set_uint8(v___x_3097_, sizeof(void*)*14 + 1, v_suppressElabErrors_3091_);
v___x_3098_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3095_);
lean_dec_ref(v_traces_3095_);
v_sz_3099_ = lean_array_size(v___x_3098_);
v___x_3100_ = ((size_t)0ULL);
v___x_3101_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3099_, v___x_3100_, v___x_3098_);
v_msg_3102_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3102_, 0, v_data_3069_);
lean_ctor_set(v_msg_3102_, 1, v_msg_3071_);
lean_ctor_set(v_msg_3102_, 2, v___x_3101_);
v___x_3103_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3102_, v___y_3072_, v___y_3073_, v___x_3097_, v___y_3075_);
lean_dec_ref_known(v___x_3097_, 14);
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3106_ = v___x_3103_;
v_isShared_3107_ = v_isSharedCheck_3141_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3141_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v_traceState_3109_; lean_object* v_env_3110_; lean_object* v_nextMacroScope_3111_; lean_object* v_ngen_3112_; lean_object* v_auxDeclNGen_3113_; lean_object* v_cache_3114_; lean_object* v_messages_3115_; lean_object* v_infoState_3116_; lean_object* v_snapshotTasks_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3140_; 
v___x_3108_ = lean_st_ref_take(v___y_3075_);
v_traceState_3109_ = lean_ctor_get(v___x_3108_, 4);
v_env_3110_ = lean_ctor_get(v___x_3108_, 0);
v_nextMacroScope_3111_ = lean_ctor_get(v___x_3108_, 1);
v_ngen_3112_ = lean_ctor_get(v___x_3108_, 2);
v_auxDeclNGen_3113_ = lean_ctor_get(v___x_3108_, 3);
v_cache_3114_ = lean_ctor_get(v___x_3108_, 5);
v_messages_3115_ = lean_ctor_get(v___x_3108_, 6);
v_infoState_3116_ = lean_ctor_get(v___x_3108_, 7);
v_snapshotTasks_3117_ = lean_ctor_get(v___x_3108_, 8);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3119_ = v___x_3108_;
v_isShared_3120_ = v_isSharedCheck_3140_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_snapshotTasks_3117_);
lean_inc(v_infoState_3116_);
lean_inc(v_messages_3115_);
lean_inc(v_cache_3114_);
lean_inc(v_traceState_3109_);
lean_inc(v_auxDeclNGen_3113_);
lean_inc(v_ngen_3112_);
lean_inc(v_nextMacroScope_3111_);
lean_inc(v_env_3110_);
lean_dec(v___x_3108_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3140_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
uint64_t v_tid_3121_; lean_object* v___x_3123_; uint8_t v_isShared_3124_; uint8_t v_isSharedCheck_3138_; 
v_tid_3121_ = lean_ctor_get_uint64(v_traceState_3109_, sizeof(void*)*1);
v_isSharedCheck_3138_ = !lean_is_exclusive(v_traceState_3109_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v_traceState_3109_, 0);
lean_dec(v_unused_3139_);
v___x_3123_ = v_traceState_3109_;
v_isShared_3124_ = v_isSharedCheck_3138_;
goto v_resetjp_3122_;
}
else
{
lean_dec(v_traceState_3109_);
v___x_3123_ = lean_box(0);
v_isShared_3124_ = v_isSharedCheck_3138_;
goto v_resetjp_3122_;
}
v_resetjp_3122_:
{
lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3125_, 0, v_ref_3070_);
lean_ctor_set(v___x_3125_, 1, v_a_3104_);
v___x_3126_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3068_, v___x_3125_);
if (v_isShared_3124_ == 0)
{
lean_ctor_set(v___x_3123_, 0, v___x_3126_);
v___x_3128_ = v___x_3123_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3126_);
lean_ctor_set_uint64(v_reuseFailAlloc_3137_, sizeof(void*)*1, v_tid_3121_);
v___x_3128_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 4, v___x_3128_);
v___x_3130_ = v___x_3119_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3136_; 
v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_env_3110_);
lean_ctor_set(v_reuseFailAlloc_3136_, 1, v_nextMacroScope_3111_);
lean_ctor_set(v_reuseFailAlloc_3136_, 2, v_ngen_3112_);
lean_ctor_set(v_reuseFailAlloc_3136_, 3, v_auxDeclNGen_3113_);
lean_ctor_set(v_reuseFailAlloc_3136_, 4, v___x_3128_);
lean_ctor_set(v_reuseFailAlloc_3136_, 5, v_cache_3114_);
lean_ctor_set(v_reuseFailAlloc_3136_, 6, v_messages_3115_);
lean_ctor_set(v_reuseFailAlloc_3136_, 7, v_infoState_3116_);
lean_ctor_set(v_reuseFailAlloc_3136_, 8, v_snapshotTasks_3117_);
v___x_3130_ = v_reuseFailAlloc_3136_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3131_ = lean_st_ref_set(v___y_3075_, v___x_3130_);
v___x_3132_ = lean_box(0);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3132_);
v___x_3134_ = v___x_3106_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3142_, lean_object* v_data_3143_, lean_object* v_ref_3144_, lean_object* v_msg_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3142_, v_data_3143_, v_ref_3144_, v_msg_3145_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
lean_dec(v___y_3149_);
lean_dec_ref(v___y_3148_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3152_){
_start:
{
if (lean_obj_tag(v_x_3152_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v_x_3152_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_x_3152_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v_x_3152_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v_x_3152_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 1);
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
else
{
lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
v_a_3162_ = lean_ctor_get(v_x_3152_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v_x_3152_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v_x_3152_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v_x_3152_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3167_; 
if (v_isShared_3165_ == 0)
{
lean_ctor_set_tag(v___x_3164_, 0);
v___x_3167_ = v___x_3164_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3168_; 
v_reuseFailAlloc_3168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3168_, 0, v_a_3162_);
v___x_3167_ = v_reuseFailAlloc_3168_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
return v___x_3167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3170_, lean_object* v___y_3171_){
_start:
{
lean_object* v_res_3172_; 
v_res_3172_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3170_);
return v_res_3172_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3173_; double v___x_3174_; 
v___x_3173_ = lean_unsigned_to_nat(0u);
v___x_3174_ = lean_float_of_nat(v___x_3173_);
return v___x_3174_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3177_ = l_Lean_stringToMessageData(v___x_3176_);
return v___x_3177_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3178_; double v___x_3179_; 
v___x_3178_ = lean_unsigned_to_nat(1000u);
v___x_3179_ = lean_float_of_nat(v___x_3178_);
return v___x_3179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3180_, uint8_t v_collapsed_3181_, lean_object* v_tag_3182_, lean_object* v_opts_3183_, uint8_t v_clsEnabled_3184_, lean_object* v_oldTraces_3185_, lean_object* v_msg_3186_, lean_object* v_resStartStop_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_){
_start:
{
lean_object* v_fst_3193_; lean_object* v_snd_3194_; lean_object* v___y_3196_; lean_object* v___y_3197_; lean_object* v_data_3198_; lean_object* v_fst_3209_; lean_object* v_snd_3210_; lean_object* v___x_3211_; uint8_t v___x_3212_; lean_object* v___y_3214_; lean_object* v_a_3215_; uint8_t v___y_3230_; double v___y_3261_; 
v_fst_3193_ = lean_ctor_get(v_resStartStop_3187_, 0);
lean_inc(v_fst_3193_);
v_snd_3194_ = lean_ctor_get(v_resStartStop_3187_, 1);
lean_inc(v_snd_3194_);
lean_dec_ref(v_resStartStop_3187_);
v_fst_3209_ = lean_ctor_get(v_snd_3194_, 0);
lean_inc(v_fst_3209_);
v_snd_3210_ = lean_ctor_get(v_snd_3194_, 1);
lean_inc(v_snd_3210_);
lean_dec(v_snd_3194_);
v___x_3211_ = l_Lean_trace_profiler;
v___x_3212_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3183_, v___x_3211_);
if (v___x_3212_ == 0)
{
v___y_3230_ = v___x_3212_;
goto v___jp_3229_;
}
else
{
lean_object* v___x_3266_; uint8_t v___x_3267_; 
v___x_3266_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3267_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3183_, v___x_3266_);
if (v___x_3267_ == 0)
{
lean_object* v___x_3268_; lean_object* v___x_3269_; double v___x_3270_; double v___x_3271_; double v___x_3272_; 
v___x_3268_ = l_Lean_trace_profiler_threshold;
v___x_3269_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3183_, v___x_3268_);
v___x_3270_ = lean_float_of_nat(v___x_3269_);
v___x_3271_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3272_ = lean_float_div(v___x_3270_, v___x_3271_);
v___y_3261_ = v___x_3272_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; double v___x_3275_; 
v___x_3273_ = l_Lean_trace_profiler_threshold;
v___x_3274_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3183_, v___x_3273_);
v___x_3275_ = lean_float_of_nat(v___x_3274_);
v___y_3261_ = v___x_3275_;
goto v___jp_3260_;
}
}
v___jp_3195_:
{
lean_object* v___x_3199_; 
lean_inc(v___y_3196_);
v___x_3199_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3185_, v_data_3198_, v___y_3196_, v___y_3197_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_);
if (lean_obj_tag(v___x_3199_) == 0)
{
lean_object* v___x_3200_; 
lean_dec_ref_known(v___x_3199_, 1);
v___x_3200_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3193_);
return v___x_3200_;
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_dec(v_fst_3193_);
v_a_3201_ = lean_ctor_get(v___x_3199_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3199_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3199_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3199_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
v___jp_3213_:
{
uint8_t v_result_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; double v___x_3219_; lean_object* v_data_3220_; 
v_result_3216_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3193_);
v___x_3217_ = lean_box(v_result_3216_);
v___x_3218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3218_, 0, v___x_3217_);
v___x_3219_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3182_);
lean_inc_ref(v___x_3218_);
lean_inc(v_cls_3180_);
v_data_3220_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3220_, 0, v_cls_3180_);
lean_ctor_set(v_data_3220_, 1, v___x_3218_);
lean_ctor_set(v_data_3220_, 2, v_tag_3182_);
lean_ctor_set_float(v_data_3220_, sizeof(void*)*3, v___x_3219_);
lean_ctor_set_float(v_data_3220_, sizeof(void*)*3 + 8, v___x_3219_);
lean_ctor_set_uint8(v_data_3220_, sizeof(void*)*3 + 16, v_collapsed_3181_);
if (v___x_3212_ == 0)
{
lean_dec_ref_known(v___x_3218_, 1);
lean_dec(v_snd_3210_);
lean_dec(v_fst_3209_);
lean_dec_ref(v_tag_3182_);
lean_dec(v_cls_3180_);
v___y_3196_ = v___y_3214_;
v___y_3197_ = v_a_3215_;
v_data_3198_ = v_data_3220_;
goto v___jp_3195_;
}
else
{
lean_object* v_data_3221_; double v___x_3222_; double v___x_3223_; 
lean_dec_ref_known(v_data_3220_, 3);
v_data_3221_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3221_, 0, v_cls_3180_);
lean_ctor_set(v_data_3221_, 1, v___x_3218_);
lean_ctor_set(v_data_3221_, 2, v_tag_3182_);
v___x_3222_ = lean_unbox_float(v_fst_3209_);
lean_dec(v_fst_3209_);
lean_ctor_set_float(v_data_3221_, sizeof(void*)*3, v___x_3222_);
v___x_3223_ = lean_unbox_float(v_snd_3210_);
lean_dec(v_snd_3210_);
lean_ctor_set_float(v_data_3221_, sizeof(void*)*3 + 8, v___x_3223_);
lean_ctor_set_uint8(v_data_3221_, sizeof(void*)*3 + 16, v_collapsed_3181_);
v___y_3196_ = v___y_3214_;
v___y_3197_ = v_a_3215_;
v_data_3198_ = v_data_3221_;
goto v___jp_3195_;
}
}
v___jp_3224_:
{
lean_object* v_ref_3225_; lean_object* v___x_3226_; 
v_ref_3225_ = lean_ctor_get(v___y_3190_, 5);
lean_inc(v___y_3191_);
lean_inc_ref(v___y_3190_);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v_fst_3193_);
v___x_3226_ = lean_apply_6(v_msg_3186_, v_fst_3193_, v___y_3188_, v___y_3189_, v___y_3190_, v___y_3191_, lean_box(0));
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___y_3214_ = v_ref_3225_;
v_a_3215_ = v_a_3227_;
goto v___jp_3213_;
}
else
{
lean_object* v___x_3228_; 
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3214_ = v_ref_3225_;
v_a_3215_ = v___x_3228_;
goto v___jp_3213_;
}
}
v___jp_3229_:
{
if (v_clsEnabled_3184_ == 0)
{
if (v___y_3230_ == 0)
{
lean_object* v___x_3231_; lean_object* v_traceState_3232_; lean_object* v_env_3233_; lean_object* v_nextMacroScope_3234_; lean_object* v_ngen_3235_; lean_object* v_auxDeclNGen_3236_; lean_object* v_cache_3237_; lean_object* v_messages_3238_; lean_object* v_infoState_3239_; lean_object* v_snapshotTasks_3240_; lean_object* v___x_3242_; uint8_t v_isShared_3243_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_snd_3210_);
lean_dec(v_fst_3209_);
lean_dec_ref(v_msg_3186_);
lean_dec_ref(v_tag_3182_);
lean_dec(v_cls_3180_);
v___x_3231_ = lean_st_ref_take(v___y_3191_);
v_traceState_3232_ = lean_ctor_get(v___x_3231_, 4);
v_env_3233_ = lean_ctor_get(v___x_3231_, 0);
v_nextMacroScope_3234_ = lean_ctor_get(v___x_3231_, 1);
v_ngen_3235_ = lean_ctor_get(v___x_3231_, 2);
v_auxDeclNGen_3236_ = lean_ctor_get(v___x_3231_, 3);
v_cache_3237_ = lean_ctor_get(v___x_3231_, 5);
v_messages_3238_ = lean_ctor_get(v___x_3231_, 6);
v_infoState_3239_ = lean_ctor_get(v___x_3231_, 7);
v_snapshotTasks_3240_ = lean_ctor_get(v___x_3231_, 8);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3242_ = v___x_3231_;
v_isShared_3243_ = v_isSharedCheck_3259_;
goto v_resetjp_3241_;
}
else
{
lean_inc(v_snapshotTasks_3240_);
lean_inc(v_infoState_3239_);
lean_inc(v_messages_3238_);
lean_inc(v_cache_3237_);
lean_inc(v_traceState_3232_);
lean_inc(v_auxDeclNGen_3236_);
lean_inc(v_ngen_3235_);
lean_inc(v_nextMacroScope_3234_);
lean_inc(v_env_3233_);
lean_dec(v___x_3231_);
v___x_3242_ = lean_box(0);
v_isShared_3243_ = v_isSharedCheck_3259_;
goto v_resetjp_3241_;
}
v_resetjp_3241_:
{
uint64_t v_tid_3244_; lean_object* v_traces_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3258_; 
v_tid_3244_ = lean_ctor_get_uint64(v_traceState_3232_, sizeof(void*)*1);
v_traces_3245_ = lean_ctor_get(v_traceState_3232_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_traceState_3232_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3247_ = v_traceState_3232_;
v_isShared_3248_ = v_isSharedCheck_3258_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_traces_3245_);
lean_dec(v_traceState_3232_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3258_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; lean_object* v___x_3251_; 
v___x_3249_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3185_, v_traces_3245_);
lean_dec_ref(v_traces_3245_);
if (v_isShared_3248_ == 0)
{
lean_ctor_set(v___x_3247_, 0, v___x_3249_);
v___x_3251_ = v___x_3247_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v___x_3249_);
lean_ctor_set_uint64(v_reuseFailAlloc_3257_, sizeof(void*)*1, v_tid_3244_);
v___x_3251_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3253_; 
if (v_isShared_3243_ == 0)
{
lean_ctor_set(v___x_3242_, 4, v___x_3251_);
v___x_3253_ = v___x_3242_;
goto v_reusejp_3252_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_env_3233_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_nextMacroScope_3234_);
lean_ctor_set(v_reuseFailAlloc_3256_, 2, v_ngen_3235_);
lean_ctor_set(v_reuseFailAlloc_3256_, 3, v_auxDeclNGen_3236_);
lean_ctor_set(v_reuseFailAlloc_3256_, 4, v___x_3251_);
lean_ctor_set(v_reuseFailAlloc_3256_, 5, v_cache_3237_);
lean_ctor_set(v_reuseFailAlloc_3256_, 6, v_messages_3238_);
lean_ctor_set(v_reuseFailAlloc_3256_, 7, v_infoState_3239_);
lean_ctor_set(v_reuseFailAlloc_3256_, 8, v_snapshotTasks_3240_);
v___x_3253_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3252_;
}
v_reusejp_3252_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_st_ref_set(v___y_3191_, v___x_3253_);
v___x_3255_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3193_);
return v___x_3255_;
}
}
}
}
}
else
{
goto v___jp_3224_;
}
}
else
{
goto v___jp_3224_;
}
}
v___jp_3260_:
{
double v___x_3262_; double v___x_3263_; double v___x_3264_; uint8_t v___x_3265_; 
v___x_3262_ = lean_unbox_float(v_snd_3210_);
v___x_3263_ = lean_unbox_float(v_fst_3209_);
v___x_3264_ = lean_float_sub(v___x_3262_, v___x_3263_);
v___x_3265_ = lean_float_decLt(v___y_3261_, v___x_3264_);
v___y_3230_ = v___x_3265_;
goto v___jp_3229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3276_, lean_object* v_collapsed_3277_, lean_object* v_tag_3278_, lean_object* v_opts_3279_, lean_object* v_clsEnabled_3280_, lean_object* v_oldTraces_3281_, lean_object* v_msg_3282_, lean_object* v_resStartStop_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
uint8_t v_collapsed_boxed_3289_; uint8_t v_clsEnabled_boxed_3290_; lean_object* v_res_3291_; 
v_collapsed_boxed_3289_ = lean_unbox(v_collapsed_3277_);
v_clsEnabled_boxed_3290_ = lean_unbox(v_clsEnabled_3280_);
v_res_3291_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3276_, v_collapsed_boxed_3289_, v_tag_3278_, v_opts_3279_, v_clsEnabled_boxed_3290_, v_oldTraces_3281_, v_msg_3282_, v_resStartStop_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec_ref(v_opts_3279_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3292_, lean_object* v_a_3293_){
_start:
{
if (lean_obj_tag(v_a_3292_) == 0)
{
lean_object* v___x_3294_; 
v___x_3294_ = l_List_reverse___redArg(v_a_3293_);
return v___x_3294_;
}
else
{
lean_object* v_head_3295_; lean_object* v_tail_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3305_; 
v_head_3295_ = lean_ctor_get(v_a_3292_, 0);
v_tail_3296_ = lean_ctor_get(v_a_3292_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v_a_3292_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3298_ = v_a_3292_;
v_isShared_3299_ = v_isSharedCheck_3305_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_tail_3296_);
lean_inc(v_head_3295_);
lean_dec(v_a_3292_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3305_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3300_; lean_object* v___x_3302_; 
v___x_3300_ = l_Lean_MessageData_ofExpr(v_head_3295_);
if (v_isShared_3299_ == 0)
{
lean_ctor_set(v___x_3298_, 1, v_a_3293_);
lean_ctor_set(v___x_3298_, 0, v___x_3300_);
v___x_3302_ = v___x_3298_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3300_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_a_3293_);
v___x_3302_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
v_a_3292_ = v_tail_3296_;
v_a_3293_ = v___x_3302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3306_, lean_object* v_xs_3307_, lean_object* v_x_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; 
v___x_3314_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3315_ = l_Lean_MessageData_ofName(v_f_3306_);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = lean_array_to_list(v_xs_3307_);
v___x_3320_ = lean_box(0);
v___x_3321_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3319_, v___x_3320_);
v___x_3322_ = l_Lean_MessageData_ofList(v___x_3321_);
v___x_3323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3323_, 0, v___x_3318_);
lean_ctor_set(v___x_3323_, 1, v___x_3322_);
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3325_, lean_object* v_xs_3326_, lean_object* v_x_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3325_, v_xs_3326_, v_x_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec_ref(v_x_3327_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3336_, lean_object* v_msg_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_){
_start:
{
lean_object* v_ref_3343_; lean_object* v___x_3344_; lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3389_; 
v_ref_3343_ = lean_ctor_get(v___y_3340_, 5);
v___x_3344_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3337_, v___y_3338_, v___y_3339_, v___y_3340_, v___y_3341_);
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3344_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3347_ = v___x_3344_;
v_isShared_3348_ = v_isSharedCheck_3389_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_dec(v___x_3344_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3389_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3349_; lean_object* v_traceState_3350_; lean_object* v_env_3351_; lean_object* v_nextMacroScope_3352_; lean_object* v_ngen_3353_; lean_object* v_auxDeclNGen_3354_; lean_object* v_cache_3355_; lean_object* v_messages_3356_; lean_object* v_infoState_3357_; lean_object* v_snapshotTasks_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3388_; 
v___x_3349_ = lean_st_ref_take(v___y_3341_);
v_traceState_3350_ = lean_ctor_get(v___x_3349_, 4);
v_env_3351_ = lean_ctor_get(v___x_3349_, 0);
v_nextMacroScope_3352_ = lean_ctor_get(v___x_3349_, 1);
v_ngen_3353_ = lean_ctor_get(v___x_3349_, 2);
v_auxDeclNGen_3354_ = lean_ctor_get(v___x_3349_, 3);
v_cache_3355_ = lean_ctor_get(v___x_3349_, 5);
v_messages_3356_ = lean_ctor_get(v___x_3349_, 6);
v_infoState_3357_ = lean_ctor_get(v___x_3349_, 7);
v_snapshotTasks_3358_ = lean_ctor_get(v___x_3349_, 8);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3360_ = v___x_3349_;
v_isShared_3361_ = v_isSharedCheck_3388_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snapshotTasks_3358_);
lean_inc(v_infoState_3357_);
lean_inc(v_messages_3356_);
lean_inc(v_cache_3355_);
lean_inc(v_traceState_3350_);
lean_inc(v_auxDeclNGen_3354_);
lean_inc(v_ngen_3353_);
lean_inc(v_nextMacroScope_3352_);
lean_inc(v_env_3351_);
lean_dec(v___x_3349_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3388_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
uint64_t v_tid_3362_; lean_object* v_traces_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3387_; 
v_tid_3362_ = lean_ctor_get_uint64(v_traceState_3350_, sizeof(void*)*1);
v_traces_3363_ = lean_ctor_get(v_traceState_3350_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v_traceState_3350_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3365_ = v_traceState_3350_;
v_isShared_3366_ = v_isSharedCheck_3387_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_traces_3363_);
lean_dec(v_traceState_3350_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3387_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; double v___x_3368_; uint8_t v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3367_ = lean_box(0);
v___x_3368_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3369_ = 0;
v___x_3370_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3371_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3371_, 0, v_cls_3336_);
lean_ctor_set(v___x_3371_, 1, v___x_3367_);
lean_ctor_set(v___x_3371_, 2, v___x_3370_);
lean_ctor_set_float(v___x_3371_, sizeof(void*)*3, v___x_3368_);
lean_ctor_set_float(v___x_3371_, sizeof(void*)*3 + 8, v___x_3368_);
lean_ctor_set_uint8(v___x_3371_, sizeof(void*)*3 + 16, v___x_3369_);
v___x_3372_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3373_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v_a_3345_);
lean_ctor_set(v___x_3373_, 2, v___x_3372_);
lean_inc(v_ref_3343_);
v___x_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3374_, 0, v_ref_3343_);
lean_ctor_set(v___x_3374_, 1, v___x_3373_);
v___x_3375_ = l_Lean_PersistentArray_push___redArg(v_traces_3363_, v___x_3374_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3375_);
v___x_3377_ = v___x_3365_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v___x_3375_);
lean_ctor_set_uint64(v_reuseFailAlloc_3386_, sizeof(void*)*1, v_tid_3362_);
v___x_3377_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 4, v___x_3377_);
v___x_3379_ = v___x_3360_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_env_3351_);
lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_nextMacroScope_3352_);
lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_ngen_3353_);
lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_auxDeclNGen_3354_);
lean_ctor_set(v_reuseFailAlloc_3385_, 4, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3385_, 5, v_cache_3355_);
lean_ctor_set(v_reuseFailAlloc_3385_, 6, v_messages_3356_);
lean_ctor_set(v_reuseFailAlloc_3385_, 7, v_infoState_3357_);
lean_ctor_set(v_reuseFailAlloc_3385_, 8, v_snapshotTasks_3358_);
v___x_3379_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3380_ = lean_st_ref_set(v___y_3341_, v___x_3379_);
v___x_3381_ = lean_box(0);
if (v_isShared_3348_ == 0)
{
lean_ctor_set(v___x_3347_, 0, v___x_3381_);
v___x_3383_ = v___x_3347_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3381_);
v___x_3383_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
return v___x_3383_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3390_, lean_object* v_msg_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3390_, v_msg_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3398_, lean_object* v_xs_3399_, lean_object* v_k_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_, lean_object* v_a_3403_, lean_object* v_a_3404_){
_start:
{
lean_object* v_options_3406_; uint8_t v_hasTrace_3407_; 
v_options_3406_ = lean_ctor_get(v_a_3403_, 2);
v_hasTrace_3407_ = lean_ctor_get_uint8(v_options_3406_, sizeof(void*)*1);
if (v_hasTrace_3407_ == 0)
{
lean_object* v___x_3408_; 
lean_dec_ref(v_xs_3399_);
lean_dec(v_f_3398_);
lean_inc(v_a_3404_);
lean_inc_ref(v_a_3403_);
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
v___x_3408_ = lean_apply_5(v_k_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, lean_box(0));
return v___x_3408_;
}
else
{
lean_object* v_inheritedTraceOptions_3409_; lean_object* v___f_3410_; lean_object* v___y_3412_; lean_object* v___y_3413_; uint8_t v___y_3414_; lean_object* v___y_3438_; lean_object* v_a_3439_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; uint8_t v___x_3445_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v_a_3449_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v_a_3464_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v_a_3480_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v_a_3486_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v_a_3491_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v_a_3503_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; uint8_t v___y_3509_; lean_object* v___y_3517_; lean_object* v___y_3518_; lean_object* v_a_3519_; lean_object* v___y_3523_; lean_object* v___y_3524_; lean_object* v_a_3525_; 
v_inheritedTraceOptions_3409_ = lean_ctor_get(v_a_3403_, 13);
v___f_3410_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3410_, 0, v_f_3398_);
lean_closure_set(v___f_3410_, 1, v_xs_3399_);
v___x_3442_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3443_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3444_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3445_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3406_, v___x_3444_);
if (v___x_3445_ == 0)
{
lean_object* v___x_3552_; uint8_t v___x_3553_; 
v___x_3552_ = l_Lean_trace_profiler;
v___x_3553_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3406_, v___x_3552_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
lean_dec_ref(v___f_3410_);
lean_inc(v_a_3404_);
lean_inc_ref(v_a_3403_);
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
v___x_3554_ = lean_apply_5(v_k_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, lean_box(0));
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; uint8_t v___x_3558_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
v___x_3556_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3557_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3406_, v___x_3557_);
if (v___x_3558_ == 0)
{
lean_dec(v_a_3555_);
return v___x_3554_;
}
else
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
lean_dec_ref_known(v___x_3554_, 1);
lean_inc(v_a_3555_);
v___x_3559_ = l_Lean_MessageData_ofExpr(v_a_3555_);
v___x_3560_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3556_, v___x_3559_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v___x_3560_, 0);
lean_dec(v_unused_3568_);
v___x_3562_ = v___x_3560_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_dec(v___x_3560_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
lean_ctor_set(v___x_3562_, 0, v_a_3555_);
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3555_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_a_3555_);
v_a_3569_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3560_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3560_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
lean_inc(v_a_3569_);
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
v___y_3438_ = v___x_3574_;
v_a_3439_ = v_a_3569_;
goto v___jp_3437_;
}
}
}
}
}
else
{
lean_object* v_a_3577_; 
v_a_3577_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3577_);
v___y_3438_ = v___x_3554_;
v_a_3439_ = v_a_3577_;
goto v___jp_3437_;
}
}
else
{
goto v___jp_3527_;
}
}
else
{
goto v___jp_3527_;
}
v___jp_3411_:
{
if (v___y_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v___x_3416_; uint8_t v___x_3417_; 
lean_dec_ref(v___y_3412_);
v___x_3415_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3416_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3417_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3406_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v___x_3418_; 
v___x_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3418_, 0, v___y_3413_);
return v___x_3418_;
}
else
{
lean_object* v___x_3419_; lean_object* v___x_3420_; 
lean_inc_ref(v___y_3413_);
v___x_3419_ = l_Lean_Exception_toMessageData(v___y_3413_);
v___x_3420_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3415_, v___x_3419_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
if (lean_obj_tag(v___x_3420_) == 0)
{
lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v___x_3420_, 0);
lean_dec(v_unused_3428_);
v___x_3422_ = v___x_3420_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_dec(v___x_3420_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set_tag(v___x_3422_, 1);
lean_ctor_set(v___x_3422_, 0, v___y_3413_);
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v___y_3413_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_dec_ref(v___y_3413_);
v_a_3429_ = lean_ctor_get(v___x_3420_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3420_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3420_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3413_);
return v___y_3412_;
}
}
v___jp_3437_:
{
uint8_t v___x_3440_; 
v___x_3440_ = l_Lean_Exception_isInterrupt(v_a_3439_);
if (v___x_3440_ == 0)
{
uint8_t v___x_3441_; 
lean_inc_ref(v_a_3439_);
v___x_3441_ = l_Lean_Exception_isRuntime(v_a_3439_);
v___y_3412_ = v___y_3438_;
v___y_3413_ = v_a_3439_;
v___y_3414_ = v___x_3441_;
goto v___jp_3411_;
}
else
{
v___y_3412_ = v___y_3438_;
v___y_3413_ = v_a_3439_;
v___y_3414_ = v___x_3440_;
goto v___jp_3411_;
}
}
v___jp_3446_:
{
lean_object* v___x_3450_; double v___x_3451_; double v___x_3452_; double v___x_3453_; double v___x_3454_; double v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v___x_3450_ = lean_io_mono_nanos_now();
v___x_3451_ = lean_float_of_nat(v___y_3448_);
v___x_3452_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3453_ = lean_float_div(v___x_3451_, v___x_3452_);
v___x_3454_ = lean_float_of_nat(v___x_3450_);
v___x_3455_ = lean_float_div(v___x_3454_, v___x_3452_);
v___x_3456_ = lean_box_float(v___x_3453_);
v___x_3457_ = lean_box_float(v___x_3455_);
v___x_3458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3456_);
lean_ctor_set(v___x_3458_, 1, v___x_3457_);
v___x_3459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3459_, 0, v_a_3449_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
v___x_3460_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3442_, v_hasTrace_3407_, v___x_3443_, v_options_3406_, v___x_3445_, v___y_3447_, v___f_3410_, v___x_3459_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3460_;
}
v___jp_3461_:
{
lean_object* v___x_3465_; 
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v_a_3464_);
v___y_3447_ = v___y_3462_;
v___y_3448_ = v___y_3463_;
v_a_3449_ = v___x_3465_;
goto v___jp_3446_;
}
v___jp_3466_:
{
if (v___y_3470_ == 0)
{
lean_object* v___x_3471_; lean_object* v___x_3472_; uint8_t v___x_3473_; 
v___x_3471_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3472_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3473_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3406_, v___x_3472_);
if (v___x_3473_ == 0)
{
v___y_3462_ = v___y_3468_;
v___y_3463_ = v___y_3469_;
v_a_3464_ = v___y_3467_;
goto v___jp_3461_;
}
else
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
lean_inc_ref(v___y_3467_);
v___x_3474_ = l_Lean_Exception_toMessageData(v___y_3467_);
v___x_3475_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3471_, v___x_3474_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_dec_ref_known(v___x_3475_, 1);
v___y_3462_ = v___y_3468_;
v___y_3463_ = v___y_3469_;
v_a_3464_ = v___y_3467_;
goto v___jp_3461_;
}
else
{
lean_object* v_a_3476_; 
lean_dec_ref(v___y_3467_);
v_a_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_a_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___y_3462_ = v___y_3468_;
v___y_3463_ = v___y_3469_;
v_a_3464_ = v_a_3476_;
goto v___jp_3461_;
}
}
}
else
{
v___y_3462_ = v___y_3468_;
v___y_3463_ = v___y_3469_;
v_a_3464_ = v___y_3467_;
goto v___jp_3461_;
}
}
v___jp_3477_:
{
uint8_t v___x_3481_; 
v___x_3481_ = l_Lean_Exception_isInterrupt(v_a_3480_);
if (v___x_3481_ == 0)
{
uint8_t v___x_3482_; 
lean_inc_ref(v_a_3480_);
v___x_3482_ = l_Lean_Exception_isRuntime(v_a_3480_);
v___y_3467_ = v_a_3480_;
v___y_3468_ = v___y_3478_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___x_3482_;
goto v___jp_3466_;
}
else
{
v___y_3467_ = v_a_3480_;
v___y_3468_ = v___y_3478_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___x_3481_;
goto v___jp_3466_;
}
}
v___jp_3483_:
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3487_, 0, v_a_3486_);
v___y_3447_ = v___y_3484_;
v___y_3448_ = v___y_3485_;
v_a_3449_ = v___x_3487_;
goto v___jp_3446_;
}
v___jp_3488_:
{
lean_object* v___x_3492_; double v___x_3493_; double v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v___x_3492_ = lean_io_get_num_heartbeats();
v___x_3493_ = lean_float_of_nat(v___y_3489_);
v___x_3494_ = lean_float_of_nat(v___x_3492_);
v___x_3495_ = lean_box_float(v___x_3493_);
v___x_3496_ = lean_box_float(v___x_3494_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3495_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v_a_3491_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
v___x_3499_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3442_, v_hasTrace_3407_, v___x_3443_, v_options_3406_, v___x_3445_, v___y_3490_, v___f_3410_, v___x_3498_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
return v___x_3499_;
}
v___jp_3500_:
{
lean_object* v___x_3504_; 
v___x_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3504_, 0, v_a_3503_);
v___y_3489_ = v___y_3501_;
v___y_3490_ = v___y_3502_;
v_a_3491_ = v___x_3504_;
goto v___jp_3488_;
}
v___jp_3505_:
{
if (v___y_3509_ == 0)
{
lean_object* v___x_3510_; lean_object* v___x_3511_; uint8_t v___x_3512_; 
v___x_3510_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3511_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3512_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3406_, v___x_3511_);
if (v___x_3512_ == 0)
{
v___y_3501_ = v___y_3506_;
v___y_3502_ = v___y_3507_;
v_a_3503_ = v___y_3508_;
goto v___jp_3500_;
}
else
{
lean_object* v___x_3513_; lean_object* v___x_3514_; 
lean_inc_ref(v___y_3508_);
v___x_3513_ = l_Lean_Exception_toMessageData(v___y_3508_);
v___x_3514_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3510_, v___x_3513_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_dec_ref_known(v___x_3514_, 1);
v___y_3501_ = v___y_3506_;
v___y_3502_ = v___y_3507_;
v_a_3503_ = v___y_3508_;
goto v___jp_3500_;
}
else
{
lean_object* v_a_3515_; 
lean_dec_ref(v___y_3508_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___y_3501_ = v___y_3506_;
v___y_3502_ = v___y_3507_;
v_a_3503_ = v_a_3515_;
goto v___jp_3500_;
}
}
}
else
{
v___y_3501_ = v___y_3506_;
v___y_3502_ = v___y_3507_;
v_a_3503_ = v___y_3508_;
goto v___jp_3500_;
}
}
v___jp_3516_:
{
uint8_t v___x_3520_; 
v___x_3520_ = l_Lean_Exception_isInterrupt(v_a_3519_);
if (v___x_3520_ == 0)
{
uint8_t v___x_3521_; 
lean_inc_ref(v_a_3519_);
v___x_3521_ = l_Lean_Exception_isRuntime(v_a_3519_);
v___y_3506_ = v___y_3517_;
v___y_3507_ = v___y_3518_;
v___y_3508_ = v_a_3519_;
v___y_3509_ = v___x_3521_;
goto v___jp_3505_;
}
else
{
v___y_3506_ = v___y_3517_;
v___y_3507_ = v___y_3518_;
v___y_3508_ = v_a_3519_;
v___y_3509_ = v___x_3520_;
goto v___jp_3505_;
}
}
v___jp_3522_:
{
lean_object* v___x_3526_; 
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_a_3525_);
v___y_3489_ = v___y_3523_;
v___y_3490_ = v___y_3524_;
v_a_3491_ = v___x_3526_;
goto v___jp_3488_;
}
v___jp_3527_:
{
lean_object* v___x_3528_; lean_object* v_a_3529_; lean_object* v___x_3530_; uint8_t v___x_3531_; 
v___x_3528_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3404_);
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref(v___x_3528_);
v___x_3530_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3531_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3406_, v___x_3530_);
if (v___x_3531_ == 0)
{
lean_object* v___x_3532_; lean_object* v___x_3533_; 
v___x_3532_ = lean_io_mono_nanos_now();
lean_inc(v_a_3404_);
lean_inc_ref(v_a_3403_);
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
v___x_3533_ = lean_apply_5(v_k_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, lean_box(0));
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; uint8_t v___x_3537_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3533_, 1);
v___x_3535_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3536_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3537_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3406_, v___x_3536_);
if (v___x_3537_ == 0)
{
v___y_3484_ = v_a_3529_;
v___y_3485_ = v___x_3532_;
v_a_3486_ = v_a_3534_;
goto v___jp_3483_;
}
else
{
lean_object* v___x_3538_; lean_object* v___x_3539_; 
lean_inc(v_a_3534_);
v___x_3538_ = l_Lean_MessageData_ofExpr(v_a_3534_);
v___x_3539_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3535_, v___x_3538_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
if (lean_obj_tag(v___x_3539_) == 0)
{
lean_dec_ref_known(v___x_3539_, 1);
v___y_3484_ = v_a_3529_;
v___y_3485_ = v___x_3532_;
v_a_3486_ = v_a_3534_;
goto v___jp_3483_;
}
else
{
lean_object* v_a_3540_; 
lean_dec(v_a_3534_);
v_a_3540_ = lean_ctor_get(v___x_3539_, 0);
lean_inc(v_a_3540_);
lean_dec_ref_known(v___x_3539_, 1);
v___y_3478_ = v_a_3529_;
v___y_3479_ = v___x_3532_;
v_a_3480_ = v_a_3540_;
goto v___jp_3477_;
}
}
}
else
{
lean_object* v_a_3541_; 
v_a_3541_ = lean_ctor_get(v___x_3533_, 0);
lean_inc(v_a_3541_);
lean_dec_ref_known(v___x_3533_, 1);
v___y_3478_ = v_a_3529_;
v___y_3479_ = v___x_3532_;
v_a_3480_ = v_a_3541_;
goto v___jp_3477_;
}
}
else
{
lean_object* v___x_3542_; lean_object* v___x_3543_; 
v___x_3542_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3404_);
lean_inc_ref(v_a_3403_);
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
v___x_3543_ = lean_apply_5(v_k_3400_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_, lean_box(0));
if (lean_obj_tag(v___x_3543_) == 0)
{
lean_object* v_a_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; uint8_t v___x_3547_; 
v_a_3544_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3543_, 1);
v___x_3545_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3546_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3409_, v_options_3406_, v___x_3546_);
if (v___x_3547_ == 0)
{
v___y_3523_ = v___x_3542_;
v___y_3524_ = v_a_3529_;
v_a_3525_ = v_a_3544_;
goto v___jp_3522_;
}
else
{
lean_object* v___x_3548_; lean_object* v___x_3549_; 
lean_inc(v_a_3544_);
v___x_3548_ = l_Lean_MessageData_ofExpr(v_a_3544_);
v___x_3549_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3545_, v___x_3548_, v_a_3401_, v_a_3402_, v_a_3403_, v_a_3404_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_dec_ref_known(v___x_3549_, 1);
v___y_3523_ = v___x_3542_;
v___y_3524_ = v_a_3529_;
v_a_3525_ = v_a_3544_;
goto v___jp_3522_;
}
else
{
lean_object* v_a_3550_; 
lean_dec(v_a_3544_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc(v_a_3550_);
lean_dec_ref_known(v___x_3549_, 1);
v___y_3517_ = v___x_3542_;
v___y_3518_ = v_a_3529_;
v_a_3519_ = v_a_3550_;
goto v___jp_3516_;
}
}
}
else
{
lean_object* v_a_3551_; 
v_a_3551_ = lean_ctor_get(v___x_3543_, 0);
lean_inc(v_a_3551_);
lean_dec_ref_known(v___x_3543_, 1);
v___y_3517_ = v___x_3542_;
v___y_3518_ = v_a_3529_;
v_a_3519_ = v_a_3551_;
goto v___jp_3516_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3578_, lean_object* v_xs_3579_, lean_object* v_k_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3578_, v_xs_3579_, v_k_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3587_, lean_object* v_xs_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_){
_start:
{
lean_object* v___f_3594_; uint8_t v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_inc_ref(v_xs_3588_);
lean_inc(v_constName_3587_);
v___f_3594_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3594_, 0, v_constName_3587_);
lean_closure_set(v___f_3594_, 1, v_xs_3588_);
v___x_3595_ = 0;
v___x_3596_ = lean_box(v___x_3595_);
v___x_3597_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3597_, 0, lean_box(0));
lean_closure_set(v___x_3597_, 1, v___f_3594_);
lean_closure_set(v___x_3597_, 2, v___x_3596_);
v___x_3598_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3587_, v_xs_3588_, v___x_3597_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3599_, lean_object* v_xs_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_, lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v_res_3606_; 
v_res_3606_ = l_Lean_Meta_mkAppM(v_constName_3599_, v_xs_3600_, v_a_3601_, v_a_3602_, v_a_3603_, v_a_3604_);
lean_dec(v_a_3604_);
lean_dec_ref(v_a_3603_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
return v_res_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3610_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v_res_3618_; 
v_res_3618_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
return v_res_3618_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3619_, lean_object* v_x_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
lean_object* v___x_3626_; 
v___x_3626_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3620_);
return v___x_3626_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3627_, lean_object* v_x_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3627_, v_x_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3635_, lean_object* v_xs_3636_, lean_object* v_x_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3643_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3644_ = l_Lean_MessageData_ofExpr(v_f_3635_);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3643_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_array_to_list(v_xs_3636_);
v___x_3649_ = lean_box(0);
v___x_3650_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3648_, v___x_3649_);
v___x_3651_ = l_Lean_MessageData_ofList(v___x_3650_);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3647_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3654_, lean_object* v_xs_3655_, lean_object* v_x_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v_res_3662_; 
v_res_3662_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3654_, v_xs_3655_, v_x_3656_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
lean_dec(v___y_3660_);
lean_dec_ref(v___y_3659_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec_ref(v_x_3656_);
return v_res_3662_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3663_, lean_object* v_xs_3664_, lean_object* v_k_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_, lean_object* v_a_3668_, lean_object* v_a_3669_){
_start:
{
lean_object* v_options_3671_; uint8_t v_hasTrace_3672_; 
v_options_3671_ = lean_ctor_get(v_a_3668_, 2);
v_hasTrace_3672_ = lean_ctor_get_uint8(v_options_3671_, sizeof(void*)*1);
if (v_hasTrace_3672_ == 0)
{
lean_object* v___x_3673_; 
lean_dec_ref(v_xs_3664_);
lean_dec_ref(v_f_3663_);
lean_inc(v_a_3669_);
lean_inc_ref(v_a_3668_);
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
v___x_3673_ = lean_apply_5(v_k_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, lean_box(0));
return v___x_3673_;
}
else
{
lean_object* v_inheritedTraceOptions_3674_; lean_object* v___f_3675_; lean_object* v___y_3677_; lean_object* v___y_3678_; uint8_t v___y_3679_; lean_object* v___y_3703_; lean_object* v_a_3704_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v_a_3714_; lean_object* v___y_3727_; lean_object* v___y_3728_; lean_object* v_a_3729_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; uint8_t v___y_3735_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v_a_3745_; lean_object* v___y_3749_; lean_object* v___y_3750_; lean_object* v_a_3751_; lean_object* v___y_3754_; lean_object* v___y_3755_; lean_object* v_a_3756_; lean_object* v___y_3766_; lean_object* v___y_3767_; lean_object* v_a_3768_; lean_object* v___y_3771_; lean_object* v___y_3772_; lean_object* v___y_3773_; uint8_t v___y_3774_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v_a_3784_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v_a_3790_; 
v_inheritedTraceOptions_3674_ = lean_ctor_get(v_a_3668_, 13);
v___f_3675_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3675_, 0, v_f_3663_);
lean_closure_set(v___f_3675_, 1, v_xs_3664_);
v___x_3707_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3708_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3709_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3710_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3674_, v_options_3671_, v___x_3709_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3817_; uint8_t v___x_3818_; 
v___x_3817_ = l_Lean_trace_profiler;
v___x_3818_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3671_, v___x_3817_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; 
lean_dec_ref(v___f_3675_);
lean_inc(v_a_3669_);
lean_inc_ref(v_a_3668_);
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
v___x_3819_ = lean_apply_5(v_k_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, lean_box(0));
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; uint8_t v___x_3823_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3820_);
v___x_3821_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3822_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3823_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3674_, v_options_3671_, v___x_3822_);
if (v___x_3823_ == 0)
{
lean_dec(v_a_3820_);
return v___x_3819_;
}
else
{
lean_object* v___x_3824_; lean_object* v___x_3825_; 
lean_dec_ref_known(v___x_3819_, 1);
lean_inc(v_a_3820_);
v___x_3824_ = l_Lean_MessageData_ofExpr(v_a_3820_);
v___x_3825_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3821_, v___x_3824_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3825_) == 0)
{
lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v___x_3825_, 0);
lean_dec(v_unused_3833_);
v___x_3827_ = v___x_3825_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_dec(v___x_3825_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v_a_3820_);
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3820_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
lean_dec(v_a_3820_);
v_a_3834_ = lean_ctor_get(v___x_3825_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3836_ = v___x_3825_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3825_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
lean_inc(v_a_3834_);
if (v_isShared_3837_ == 0)
{
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3834_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
v___y_3703_ = v___x_3839_;
v_a_3704_ = v_a_3834_;
goto v___jp_3702_;
}
}
}
}
}
else
{
lean_object* v_a_3842_; 
v_a_3842_ = lean_ctor_get(v___x_3819_, 0);
lean_inc(v_a_3842_);
v___y_3703_ = v___x_3819_;
v_a_3704_ = v_a_3842_;
goto v___jp_3702_;
}
}
else
{
goto v___jp_3792_;
}
}
else
{
goto v___jp_3792_;
}
v___jp_3676_:
{
if (v___y_3679_ == 0)
{
lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
lean_dec_ref(v___y_3678_);
v___x_3680_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3681_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3674_, v_options_3671_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; 
v___x_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___y_3677_);
return v___x_3683_;
}
else
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
lean_inc_ref(v___y_3677_);
v___x_3684_ = l_Lean_Exception_toMessageData(v___y_3677_);
v___x_3685_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3680_, v___x_3684_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3692_; 
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v___x_3685_, 0);
lean_dec(v_unused_3693_);
v___x_3687_ = v___x_3685_;
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
else
{
lean_dec(v___x_3685_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3692_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3690_; 
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 1);
lean_ctor_set(v___x_3687_, 0, v___y_3677_);
v___x_3690_ = v___x_3687_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___y_3677_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec_ref(v___y_3677_);
v_a_3694_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3685_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3685_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3677_);
return v___y_3678_;
}
}
v___jp_3702_:
{
uint8_t v___x_3705_; 
v___x_3705_ = l_Lean_Exception_isInterrupt(v_a_3704_);
if (v___x_3705_ == 0)
{
uint8_t v___x_3706_; 
lean_inc_ref(v_a_3704_);
v___x_3706_ = l_Lean_Exception_isRuntime(v_a_3704_);
v___y_3677_ = v_a_3704_;
v___y_3678_ = v___y_3703_;
v___y_3679_ = v___x_3706_;
goto v___jp_3676_;
}
else
{
v___y_3677_ = v_a_3704_;
v___y_3678_ = v___y_3703_;
v___y_3679_ = v___x_3705_;
goto v___jp_3676_;
}
}
v___jp_3711_:
{
lean_object* v___x_3715_; double v___x_3716_; double v___x_3717_; double v___x_3718_; double v___x_3719_; double v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3715_ = lean_io_mono_nanos_now();
v___x_3716_ = lean_float_of_nat(v___y_3713_);
v___x_3717_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3718_ = lean_float_div(v___x_3716_, v___x_3717_);
v___x_3719_ = lean_float_of_nat(v___x_3715_);
v___x_3720_ = lean_float_div(v___x_3719_, v___x_3717_);
v___x_3721_ = lean_box_float(v___x_3718_);
v___x_3722_ = lean_box_float(v___x_3720_);
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3721_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v_a_3714_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
v___x_3725_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3707_, v_hasTrace_3672_, v___x_3708_, v_options_3671_, v___x_3710_, v___y_3712_, v___f_3675_, v___x_3724_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
return v___x_3725_;
}
v___jp_3726_:
{
lean_object* v___x_3730_; 
v___x_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3730_, 0, v_a_3729_);
v___y_3712_ = v___y_3727_;
v___y_3713_ = v___y_3728_;
v_a_3714_ = v___x_3730_;
goto v___jp_3711_;
}
v___jp_3731_:
{
if (v___y_3735_ == 0)
{
lean_object* v___x_3736_; lean_object* v___x_3737_; uint8_t v___x_3738_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3737_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3674_, v_options_3671_, v___x_3737_);
if (v___x_3738_ == 0)
{
v___y_3727_ = v___y_3733_;
v___y_3728_ = v___y_3734_;
v_a_3729_ = v___y_3732_;
goto v___jp_3726_;
}
else
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
lean_inc_ref(v___y_3732_);
v___x_3739_ = l_Lean_Exception_toMessageData(v___y_3732_);
v___x_3740_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3736_, v___x_3739_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_dec_ref_known(v___x_3740_, 1);
v___y_3727_ = v___y_3733_;
v___y_3728_ = v___y_3734_;
v_a_3729_ = v___y_3732_;
goto v___jp_3726_;
}
else
{
lean_object* v_a_3741_; 
lean_dec_ref(v___y_3732_);
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc(v_a_3741_);
lean_dec_ref_known(v___x_3740_, 1);
v___y_3727_ = v___y_3733_;
v___y_3728_ = v___y_3734_;
v_a_3729_ = v_a_3741_;
goto v___jp_3726_;
}
}
}
else
{
v___y_3727_ = v___y_3733_;
v___y_3728_ = v___y_3734_;
v_a_3729_ = v___y_3732_;
goto v___jp_3726_;
}
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
v___y_3732_ = v_a_3745_;
v___y_3733_ = v___y_3743_;
v___y_3734_ = v___y_3744_;
v___y_3735_ = v___x_3747_;
goto v___jp_3731_;
}
else
{
v___y_3732_ = v_a_3745_;
v___y_3733_ = v___y_3743_;
v___y_3734_ = v___y_3744_;
v___y_3735_ = v___x_3746_;
goto v___jp_3731_;
}
}
v___jp_3748_:
{
lean_object* v___x_3752_; 
v___x_3752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3752_, 0, v_a_3751_);
v___y_3712_ = v___y_3749_;
v___y_3713_ = v___y_3750_;
v_a_3714_ = v___x_3752_;
goto v___jp_3711_;
}
v___jp_3753_:
{
lean_object* v___x_3757_; double v___x_3758_; double v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3757_ = lean_io_get_num_heartbeats();
v___x_3758_ = lean_float_of_nat(v___y_3755_);
v___x_3759_ = lean_float_of_nat(v___x_3757_);
v___x_3760_ = lean_box_float(v___x_3758_);
v___x_3761_ = lean_box_float(v___x_3759_);
v___x_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3760_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3756_);
lean_ctor_set(v___x_3763_, 1, v___x_3762_);
v___x_3764_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3707_, v_hasTrace_3672_, v___x_3708_, v_options_3671_, v___x_3710_, v___y_3754_, v___f_3675_, v___x_3763_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
return v___x_3764_;
}
v___jp_3765_:
{
lean_object* v___x_3769_; 
v___x_3769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3769_, 0, v_a_3768_);
v___y_3754_ = v___y_3766_;
v___y_3755_ = v___y_3767_;
v_a_3756_ = v___x_3769_;
goto v___jp_3753_;
}
v___jp_3770_:
{
if (v___y_3774_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3775_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3776_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3777_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3674_, v_options_3671_, v___x_3776_);
if (v___x_3777_ == 0)
{
v___y_3766_ = v___y_3771_;
v___y_3767_ = v___y_3772_;
v_a_3768_ = v___y_3773_;
goto v___jp_3765_;
}
else
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_inc_ref(v___y_3773_);
v___x_3778_ = l_Lean_Exception_toMessageData(v___y_3773_);
v___x_3779_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3775_, v___x_3778_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_dec_ref_known(v___x_3779_, 1);
v___y_3766_ = v___y_3771_;
v___y_3767_ = v___y_3772_;
v_a_3768_ = v___y_3773_;
goto v___jp_3765_;
}
else
{
lean_object* v_a_3780_; 
lean_dec_ref(v___y_3773_);
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___y_3766_ = v___y_3771_;
v___y_3767_ = v___y_3772_;
v_a_3768_ = v_a_3780_;
goto v___jp_3765_;
}
}
}
else
{
v___y_3766_ = v___y_3771_;
v___y_3767_ = v___y_3772_;
v_a_3768_ = v___y_3773_;
goto v___jp_3765_;
}
}
v___jp_3781_:
{
uint8_t v___x_3785_; 
v___x_3785_ = l_Lean_Exception_isInterrupt(v_a_3784_);
if (v___x_3785_ == 0)
{
uint8_t v___x_3786_; 
lean_inc_ref(v_a_3784_);
v___x_3786_ = l_Lean_Exception_isRuntime(v_a_3784_);
v___y_3771_ = v___y_3782_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v_a_3784_;
v___y_3774_ = v___x_3786_;
goto v___jp_3770_;
}
else
{
v___y_3771_ = v___y_3782_;
v___y_3772_ = v___y_3783_;
v___y_3773_ = v_a_3784_;
v___y_3774_ = v___x_3785_;
goto v___jp_3770_;
}
}
v___jp_3787_:
{
lean_object* v___x_3791_; 
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v_a_3790_);
v___y_3754_ = v___y_3788_;
v___y_3755_ = v___y_3789_;
v_a_3756_ = v___x_3791_;
goto v___jp_3753_;
}
v___jp_3792_:
{
lean_object* v___x_3793_; lean_object* v_a_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v___x_3793_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3669_);
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
lean_inc(v_a_3794_);
lean_dec_ref(v___x_3793_);
v___x_3795_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3796_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3671_, v___x_3795_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
v___x_3797_ = lean_io_mono_nanos_now();
lean_inc(v_a_3669_);
lean_inc_ref(v_a_3668_);
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
v___x_3798_ = lean_apply_5(v_k_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, lean_box(0));
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; uint8_t v___x_3802_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v___x_3800_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3801_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3802_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3674_, v_options_3671_, v___x_3801_);
if (v___x_3802_ == 0)
{
v___y_3749_ = v_a_3794_;
v___y_3750_ = v___x_3797_;
v_a_3751_ = v_a_3799_;
goto v___jp_3748_;
}
else
{
lean_object* v___x_3803_; lean_object* v___x_3804_; 
lean_inc(v_a_3799_);
v___x_3803_ = l_Lean_MessageData_ofExpr(v_a_3799_);
v___x_3804_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3800_, v___x_3803_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_dec_ref_known(v___x_3804_, 1);
v___y_3749_ = v_a_3794_;
v___y_3750_ = v___x_3797_;
v_a_3751_ = v_a_3799_;
goto v___jp_3748_;
}
else
{
lean_object* v_a_3805_; 
lean_dec(v_a_3799_);
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
v___y_3743_ = v_a_3794_;
v___y_3744_ = v___x_3797_;
v_a_3745_ = v_a_3805_;
goto v___jp_3742_;
}
}
}
else
{
lean_object* v_a_3806_; 
v_a_3806_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3806_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3743_ = v_a_3794_;
v___y_3744_ = v___x_3797_;
v_a_3745_ = v_a_3806_;
goto v___jp_3742_;
}
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
v___x_3807_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3669_);
lean_inc_ref(v_a_3668_);
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
v___x_3808_ = lean_apply_5(v_k_3665_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_, lean_box(0));
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_object* v_a_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; uint8_t v___x_3812_; 
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v___x_3808_, 1);
v___x_3810_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3811_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3812_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3674_, v_options_3671_, v___x_3811_);
if (v___x_3812_ == 0)
{
v___y_3788_ = v_a_3794_;
v___y_3789_ = v___x_3807_;
v_a_3790_ = v_a_3809_;
goto v___jp_3787_;
}
else
{
lean_object* v___x_3813_; lean_object* v___x_3814_; 
lean_inc(v_a_3809_);
v___x_3813_ = l_Lean_MessageData_ofExpr(v_a_3809_);
v___x_3814_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3810_, v___x_3813_, v_a_3666_, v_a_3667_, v_a_3668_, v_a_3669_);
if (lean_obj_tag(v___x_3814_) == 0)
{
lean_dec_ref_known(v___x_3814_, 1);
v___y_3788_ = v_a_3794_;
v___y_3789_ = v___x_3807_;
v_a_3790_ = v_a_3809_;
goto v___jp_3787_;
}
else
{
lean_object* v_a_3815_; 
lean_dec(v_a_3809_);
v_a_3815_ = lean_ctor_get(v___x_3814_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3814_, 1);
v___y_3782_ = v_a_3794_;
v___y_3783_ = v___x_3807_;
v_a_3784_ = v_a_3815_;
goto v___jp_3781_;
}
}
}
else
{
lean_object* v_a_3816_; 
v_a_3816_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3808_, 1);
v___y_3782_ = v_a_3794_;
v___y_3783_ = v___x_3807_;
v_a_3784_ = v_a_3816_;
goto v___jp_3781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3843_, lean_object* v_xs_3844_, lean_object* v_k_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_){
_start:
{
lean_object* v_res_3851_; 
v_res_3851_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3843_, v_xs_3844_, v_k_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_);
lean_dec(v_a_3849_);
lean_dec_ref(v_a_3848_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3852_, lean_object* v_xs_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v___x_3859_; 
lean_inc(v_a_3857_);
lean_inc_ref(v_a_3856_);
lean_inc(v_a_3855_);
lean_inc_ref(v_a_3854_);
lean_inc_ref(v_f_3852_);
v___x_3859_ = lean_infer_type(v_f_3852_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3859_, 1);
lean_inc_ref(v_xs_3853_);
lean_inc_ref(v_f_3852_);
v___x_3861_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3861_, 0, v_f_3852_);
lean_closure_set(v___x_3861_, 1, v_a_3860_);
lean_closure_set(v___x_3861_, 2, v_xs_3853_);
v___x_3862_ = 0;
v___x_3863_ = lean_box(v___x_3862_);
v___x_3864_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3864_, 0, lean_box(0));
lean_closure_set(v___x_3864_, 1, v___x_3861_);
lean_closure_set(v___x_3864_, 2, v___x_3863_);
v___x_3865_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3852_, v_xs_3853_, v___x_3864_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
return v___x_3865_;
}
else
{
lean_dec_ref(v_xs_3853_);
lean_dec_ref(v_f_3852_);
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3866_, lean_object* v_xs_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v_res_3873_; 
v_res_3873_ = l_Lean_Meta_mkAppM_x27(v_f_3866_, v_xs_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
return v_res_3873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3874_, size_t v_i_3875_, size_t v_stop_3876_, lean_object* v_b_3877_){
_start:
{
lean_object* v___y_3879_; uint8_t v___x_3883_; 
v___x_3883_ = lean_usize_dec_eq(v_i_3875_, v_stop_3876_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
v___x_3884_ = lean_array_uget_borrowed(v_as_3874_, v_i_3875_);
if (lean_obj_tag(v___x_3884_) == 0)
{
v___y_3879_ = v_b_3877_;
goto v___jp_3878_;
}
else
{
lean_object* v_val_3885_; lean_object* v___x_3886_; 
v_val_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_val_3885_);
v___x_3886_ = lean_array_push(v_b_3877_, v_val_3885_);
v___y_3879_ = v___x_3886_;
goto v___jp_3878_;
}
}
else
{
return v_b_3877_;
}
v___jp_3878_:
{
size_t v___x_3880_; size_t v___x_3881_; 
v___x_3880_ = ((size_t)1ULL);
v___x_3881_ = lean_usize_add(v_i_3875_, v___x_3880_);
v_i_3875_ = v___x_3881_;
v_b_3877_ = v___y_3879_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3887_, lean_object* v_i_3888_, lean_object* v_stop_3889_, lean_object* v_b_3890_){
_start:
{
size_t v_i_boxed_3891_; size_t v_stop_boxed_3892_; lean_object* v_res_3893_; 
v_i_boxed_3891_ = lean_unbox_usize(v_i_3888_);
lean_dec(v_i_3888_);
v_stop_boxed_3892_ = lean_unbox_usize(v_stop_3889_);
lean_dec(v_stop_3889_);
v_res_3893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3887_, v_i_boxed_3891_, v_stop_boxed_3892_, v_b_3890_);
lean_dec_ref(v_as_3887_);
return v_res_3893_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3901_ = l_Lean_MessageData_ofFormat(v___x_3900_);
return v___x_3901_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_box(1);
v___x_3903_ = l_Lean_MessageData_ofFormat(v___x_3902_);
return v___x_3903_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3908_ = l_Lean_MessageData_ofFormat(v___x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3909_, lean_object* v_xs_3910_, lean_object* v_x_3911_, lean_object* v_x_3912_, lean_object* v_x_3913_, lean_object* v_x_3914_, lean_object* v_x_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
if (lean_obj_tag(v_x_3915_) == 7)
{
lean_object* v_binderName_3921_; lean_object* v_binderType_3922_; lean_object* v_body_3923_; uint8_t v_binderInfo_3924_; lean_object* v___x_3925_; uint8_t v___x_3926_; 
v_binderName_3921_ = lean_ctor_get(v_x_3915_, 0);
lean_inc(v_binderName_3921_);
v_binderType_3922_ = lean_ctor_get(v_x_3915_, 1);
lean_inc_ref(v_binderType_3922_);
v_body_3923_ = lean_ctor_get(v_x_3915_, 2);
lean_inc_ref(v_body_3923_);
v_binderInfo_3924_ = lean_ctor_get_uint8(v_x_3915_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3915_, 3);
v___x_3925_ = lean_array_get_size(v_xs_3910_);
v___x_3926_ = lean_nat_dec_lt(v_x_3911_, v___x_3925_);
if (v___x_3926_ == 0)
{
lean_object* v___x_3927_; lean_object* v___x_3928_; 
lean_dec_ref(v_body_3923_);
lean_dec_ref(v_binderType_3922_);
lean_dec(v_binderName_3921_);
lean_dec(v_x_3913_);
lean_dec(v_x_3911_);
v___x_3927_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3928_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3927_, v_f_3909_, v_x_3912_, v_x_3914_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
lean_dec_ref(v_x_3914_);
lean_dec_ref(v_x_3912_);
return v___x_3928_;
}
else
{
lean_object* v___x_3929_; lean_object* v_d_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_array_get_size(v_x_3912_);
v_d_3930_ = lean_expr_instantiate_rev_range(v_binderType_3922_, v_x_3913_, v___x_3929_, v_x_3912_);
lean_dec_ref(v_binderType_3922_);
v___x_3931_ = lean_array_fget_borrowed(v_xs_3910_, v_x_3911_);
if (lean_obj_tag(v___x_3931_) == 0)
{
if (v_binderInfo_3924_ == 3)
{
lean_object* v___x_3932_; uint8_t v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v_d_3930_);
v___x_3933_ = 1;
v___x_3934_ = l_Lean_Meta_mkFreshExprMVar(v___x_3932_, v___x_3933_, v_binderName_3921_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc_n(v_a_3935_, 2);
lean_dec_ref_known(v___x_3934_, 1);
v___x_3936_ = lean_unsigned_to_nat(1u);
v___x_3937_ = lean_nat_add(v_x_3911_, v___x_3936_);
lean_dec(v_x_3911_);
v___x_3938_ = lean_array_push(v_x_3912_, v_a_3935_);
v___x_3939_ = l_Lean_Expr_mvarId_x21(v_a_3935_);
lean_dec(v_a_3935_);
v___x_3940_ = lean_array_push(v_x_3914_, v___x_3939_);
v_x_3911_ = v___x_3937_;
v_x_3912_ = v___x_3938_;
v_x_3914_ = v___x_3940_;
v_x_3915_ = v_body_3923_;
goto _start;
}
else
{
lean_dec_ref(v_body_3923_);
lean_dec_ref(v_x_3914_);
lean_dec(v_x_3913_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_f_3909_);
return v___x_3934_;
}
}
else
{
lean_object* v___x_3942_; uint8_t v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3942_, 0, v_d_3930_);
v___x_3943_ = 0;
v___x_3944_ = l_Lean_Meta_mkFreshExprMVar(v___x_3942_, v___x_3943_, v_binderName_3921_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3944_) == 0)
{
lean_object* v_a_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; 
v_a_3945_ = lean_ctor_get(v___x_3944_, 0);
lean_inc(v_a_3945_);
lean_dec_ref_known(v___x_3944_, 1);
v___x_3946_ = lean_unsigned_to_nat(1u);
v___x_3947_ = lean_nat_add(v_x_3911_, v___x_3946_);
lean_dec(v_x_3911_);
v___x_3948_ = lean_array_push(v_x_3912_, v_a_3945_);
v_x_3911_ = v___x_3947_;
v_x_3912_ = v___x_3948_;
v_x_3915_ = v_body_3923_;
goto _start;
}
else
{
lean_dec_ref(v_body_3923_);
lean_dec_ref(v_x_3914_);
lean_dec(v_x_3913_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_f_3909_);
return v___x_3944_;
}
}
}
else
{
lean_object* v_val_3950_; lean_object* v___x_3951_; 
lean_dec(v_binderName_3921_);
v_val_3950_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3919_);
lean_inc_ref(v_a_3918_);
lean_inc(v_a_3917_);
lean_inc_ref(v_a_3916_);
lean_inc(v_val_3950_);
v___x_3951_ = lean_infer_type(v_val_3950_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = l_Lean_Meta_isExprDefEq(v_d_3930_, v_a_3952_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; uint8_t v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_unbox(v_a_3954_);
lean_dec(v_a_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; lean_object* v___x_3957_; 
lean_dec_ref(v_body_3923_);
lean_dec_ref(v_x_3914_);
lean_dec(v_x_3913_);
lean_dec(v_x_3911_);
v___x_3956_ = l_Lean_mkAppN(v_f_3909_, v_x_3912_);
lean_dec_ref(v_x_3912_);
lean_inc(v_val_3950_);
v___x_3957_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3956_, v_val_3950_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3957_;
}
else
{
lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_nat_add(v_x_3911_, v___x_3958_);
lean_dec(v_x_3911_);
lean_inc(v_val_3950_);
v___x_3960_ = lean_array_push(v_x_3912_, v_val_3950_);
v_x_3911_ = v___x_3959_;
v_x_3912_ = v___x_3960_;
v_x_3915_ = v_body_3923_;
goto _start;
}
}
else
{
lean_object* v_a_3962_; lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3969_; 
lean_dec_ref(v_body_3923_);
lean_dec_ref(v_x_3914_);
lean_dec(v_x_3913_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_f_3909_);
v_a_3962_ = lean_ctor_get(v___x_3953_, 0);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3953_);
if (v_isSharedCheck_3969_ == 0)
{
v___x_3964_ = v___x_3953_;
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
else
{
lean_inc(v_a_3962_);
lean_dec(v___x_3953_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3969_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3967_; 
if (v_isShared_3965_ == 0)
{
v___x_3967_ = v___x_3964_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v_a_3962_);
v___x_3967_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
return v___x_3967_;
}
}
}
}
else
{
lean_dec_ref(v_d_3930_);
lean_dec_ref(v_body_3923_);
lean_dec_ref(v_x_3914_);
lean_dec(v_x_3913_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_f_3909_);
return v___x_3951_;
}
}
}
}
else
{
lean_object* v___x_3970_; lean_object* v_type_3971_; lean_object* v___x_3972_; 
v___x_3970_ = lean_array_get_size(v_x_3912_);
v_type_3971_ = lean_expr_instantiate_rev_range(v_x_3915_, v_x_3913_, v___x_3970_, v_x_3912_);
lean_dec(v_x_3913_);
lean_dec_ref(v_x_3915_);
v___x_3972_ = l_Lean_Meta_whnfD(v_type_3971_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3972_) == 0)
{
lean_object* v_a_3973_; uint8_t v___x_3974_; 
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref_known(v___x_3972_, 1);
v___x_3974_ = l_Lean_Expr_isForall(v_a_3973_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; uint8_t v___x_3976_; 
lean_dec(v_a_3973_);
v___x_3975_ = lean_array_get_size(v_xs_3910_);
v___x_3976_ = lean_nat_dec_eq(v_x_3911_, v___x_3975_);
lean_dec(v_x_3911_);
if (v___x_3976_ == 0)
{
lean_object* v___x_3977_; lean_object* v___y_3979_; lean_object* v___x_3992_; uint8_t v___x_3993_; 
lean_dec_ref(v_x_3914_);
lean_dec_ref(v_x_3912_);
v___x_3977_ = lean_unsigned_to_nat(0u);
v___x_3992_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3993_ = lean_nat_dec_lt(v___x_3977_, v___x_3975_);
if (v___x_3993_ == 0)
{
v___y_3979_ = v___x_3992_;
goto v___jp_3978_;
}
else
{
uint8_t v___x_3994_; 
v___x_3994_ = lean_nat_dec_le(v___x_3975_, v___x_3975_);
if (v___x_3994_ == 0)
{
if (v___x_3993_ == 0)
{
v___y_3979_ = v___x_3992_;
goto v___jp_3978_;
}
else
{
size_t v___x_3995_; size_t v___x_3996_; lean_object* v___x_3997_; 
v___x_3995_ = ((size_t)0ULL);
v___x_3996_ = lean_usize_of_nat(v___x_3975_);
v___x_3997_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3910_, v___x_3995_, v___x_3996_, v___x_3992_);
v___y_3979_ = v___x_3997_;
goto v___jp_3978_;
}
}
else
{
size_t v___x_3998_; size_t v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = ((size_t)0ULL);
v___x_3999_ = lean_usize_of_nat(v___x_3975_);
v___x_4000_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3910_, v___x_3998_, v___x_3999_, v___x_3992_);
v___y_3979_ = v___x_4000_;
goto v___jp_3978_;
}
}
v___jp_3978_:
{
lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; 
v___x_3980_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3981_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3982_ = l_Lean_indentExpr(v_f_3909_);
v___x_3983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3981_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3987_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3985_);
lean_ctor_set(v___x_3987_, 1, v___x_3986_);
v___x_3988_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3989_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3979_, v___x_3977_, v___x_3988_);
lean_dec_ref(v___y_3979_);
v___x_3990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3987_);
lean_ctor_set(v___x_3990_, 1, v___x_3989_);
v___x_3991_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3980_, v___x_3990_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3991_;
}
}
else
{
lean_object* v___x_4001_; lean_object* v___x_4002_; 
v___x_4001_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_4002_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_4001_, v_f_3909_, v_x_3912_, v_x_3914_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
lean_dec_ref(v_x_3914_);
lean_dec_ref(v_x_3912_);
return v___x_4002_;
}
}
else
{
v_x_3913_ = v___x_3970_;
v_x_3915_ = v_a_3973_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3914_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_f_3909_);
return v___x_3972_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_4004_, lean_object* v_xs_4005_, lean_object* v_x_4006_, lean_object* v_x_4007_, lean_object* v_x_4008_, lean_object* v_x_4009_, lean_object* v_x_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_){
_start:
{
lean_object* v_res_4016_; 
v_res_4016_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_4004_, v_xs_4005_, v_x_4006_, v_x_4007_, v_x_4008_, v_x_4009_, v_x_4010_, v_a_4011_, v_a_4012_, v_a_4013_, v_a_4014_);
lean_dec(v_a_4014_);
lean_dec_ref(v_a_4013_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec_ref(v_xs_4005_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_4017_, lean_object* v_xs_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_4017_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v_fst_4026_; lean_object* v_snd_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v_fst_4026_ = lean_ctor_get(v_a_4025_, 0);
lean_inc(v_fst_4026_);
v_snd_4027_ = lean_ctor_get(v_a_4025_, 1);
lean_inc(v_snd_4027_);
lean_dec(v_a_4025_);
v___x_4028_ = lean_unsigned_to_nat(0u);
v___x_4029_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4030_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4026_, v_xs_4018_, v___x_4028_, v___x_4029_, v___x_4028_, v___x_4029_, v_snd_4027_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4030_;
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4038_; 
v_a_4031_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4038_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4038_ == 0)
{
v___x_4033_ = v___x_4024_;
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4024_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4038_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4036_; 
if (v_isShared_4034_ == 0)
{
v___x_4036_ = v___x_4033_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4031_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4039_, lean_object* v_xs_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4039_, v_xs_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec_ref(v_xs_4040_);
return v_res_4046_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4051_ = l_Lean_MessageData_ofFormat(v___x_4050_);
return v___x_4051_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4052_, lean_object* v_a_4053_){
_start:
{
if (lean_obj_tag(v_a_4052_) == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = l_List_reverse___redArg(v_a_4053_);
return v___x_4054_;
}
else
{
lean_object* v_head_4055_; lean_object* v_tail_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4069_; 
v_head_4055_ = lean_ctor_get(v_a_4052_, 0);
v_tail_4056_ = lean_ctor_get(v_a_4052_, 1);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_a_4052_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4058_ = v_a_4052_;
v_isShared_4059_ = v_isSharedCheck_4069_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_tail_4056_);
lean_inc(v_head_4055_);
lean_dec(v_a_4052_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4069_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___y_4061_; 
if (lean_obj_tag(v_head_4055_) == 0)
{
lean_object* v___x_4066_; 
v___x_4066_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4061_ = v___x_4066_;
goto v___jp_4060_;
}
else
{
lean_object* v_val_4067_; lean_object* v___x_4068_; 
v_val_4067_ = lean_ctor_get(v_head_4055_, 0);
lean_inc(v_val_4067_);
lean_dec_ref_known(v_head_4055_, 1);
v___x_4068_ = l_Lean_MessageData_ofExpr(v_val_4067_);
v___y_4061_ = v___x_4068_;
goto v___jp_4060_;
}
v___jp_4060_:
{
lean_object* v___x_4063_; 
if (v_isShared_4059_ == 0)
{
lean_ctor_set(v___x_4058_, 1, v_a_4053_);
lean_ctor_set(v___x_4058_, 0, v___y_4061_);
v___x_4063_ = v___x_4058_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___y_4061_);
lean_ctor_set(v_reuseFailAlloc_4065_, 1, v_a_4053_);
v___x_4063_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
v_a_4052_ = v_tail_4056_;
v_a_4053_ = v___x_4063_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4070_, lean_object* v_xs_4071_, lean_object* v_x_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4078_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4079_ = l_Lean_MessageData_ofName(v_f_4070_);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4078_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4082_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4080_);
lean_ctor_set(v___x_4082_, 1, v___x_4081_);
v___x_4083_ = lean_array_to_list(v_xs_4071_);
v___x_4084_ = lean_box(0);
v___x_4085_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4083_, v___x_4084_);
v___x_4086_ = l_Lean_MessageData_ofList(v___x_4085_);
v___x_4087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4082_);
lean_ctor_set(v___x_4087_, 1, v___x_4086_);
v___x_4088_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4088_, 0, v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4089_, lean_object* v_xs_4090_, lean_object* v_x_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4089_, v_xs_4090_, v_x_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec_ref(v_x_4091_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4098_, lean_object* v_xs_4099_, lean_object* v_k_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_, lean_object* v_a_4103_, lean_object* v_a_4104_){
_start:
{
lean_object* v_options_4106_; uint8_t v_hasTrace_4107_; 
v_options_4106_ = lean_ctor_get(v_a_4103_, 2);
v_hasTrace_4107_ = lean_ctor_get_uint8(v_options_4106_, sizeof(void*)*1);
if (v_hasTrace_4107_ == 0)
{
lean_object* v___x_4108_; 
lean_dec_ref(v_xs_4099_);
lean_dec(v_f_4098_);
lean_inc(v_a_4104_);
lean_inc_ref(v_a_4103_);
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
v___x_4108_ = lean_apply_5(v_k_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, lean_box(0));
return v___x_4108_;
}
else
{
lean_object* v_inheritedTraceOptions_4109_; lean_object* v___f_4110_; lean_object* v___y_4112_; lean_object* v___y_4113_; uint8_t v___y_4114_; lean_object* v___y_4138_; lean_object* v_a_4139_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; uint8_t v___x_4145_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v_a_4149_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v_a_4164_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; uint8_t v___y_4170_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v_a_4180_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v_a_4186_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v_a_4191_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v_a_4203_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; uint8_t v___y_4209_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v_a_4219_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v_a_4225_; 
v_inheritedTraceOptions_4109_ = lean_ctor_get(v_a_4103_, 13);
v___f_4110_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4110_, 0, v_f_4098_);
lean_closure_set(v___f_4110_, 1, v_xs_4099_);
v___x_4142_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4143_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4144_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4145_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4106_, v___x_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4252_; uint8_t v___x_4253_; 
v___x_4252_ = l_Lean_trace_profiler;
v___x_4253_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4106_, v___x_4252_);
if (v___x_4253_ == 0)
{
lean_object* v___x_4254_; 
lean_dec_ref(v___f_4110_);
lean_inc(v_a_4104_);
lean_inc_ref(v_a_4103_);
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
v___x_4254_ = lean_apply_5(v_k_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, lean_box(0));
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; uint8_t v___x_4258_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
v___x_4256_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4257_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4258_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4106_, v___x_4257_);
if (v___x_4258_ == 0)
{
lean_dec(v_a_4255_);
return v___x_4254_;
}
else
{
lean_object* v___x_4259_; lean_object* v___x_4260_; 
lean_dec_ref_known(v___x_4254_, 1);
lean_inc(v_a_4255_);
v___x_4259_ = l_Lean_MessageData_ofExpr(v_a_4255_);
v___x_4260_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4256_, v___x_4259_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4267_ == 0)
{
lean_object* v_unused_4268_; 
v_unused_4268_ = lean_ctor_get(v___x_4260_, 0);
lean_dec(v_unused_4268_);
v___x_4262_ = v___x_4260_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_dec(v___x_4260_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
lean_ctor_set(v___x_4262_, 0, v_a_4255_);
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4255_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_dec(v_a_4255_);
v_a_4269_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4260_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4260_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
lean_inc(v_a_4269_);
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
v___y_4138_ = v___x_4274_;
v_a_4139_ = v_a_4269_;
goto v___jp_4137_;
}
}
}
}
}
else
{
lean_object* v_a_4277_; 
v_a_4277_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4277_);
v___y_4138_ = v___x_4254_;
v_a_4139_ = v_a_4277_;
goto v___jp_4137_;
}
}
else
{
goto v___jp_4227_;
}
}
else
{
goto v___jp_4227_;
}
v___jp_4111_:
{
if (v___y_4114_ == 0)
{
lean_object* v___x_4115_; lean_object* v___x_4116_; uint8_t v___x_4117_; 
lean_dec_ref(v___y_4113_);
v___x_4115_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4116_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4117_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4106_, v___x_4116_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4118_; 
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___y_4112_);
return v___x_4118_;
}
else
{
lean_object* v___x_4119_; lean_object* v___x_4120_; 
lean_inc_ref(v___y_4112_);
v___x_4119_ = l_Lean_Exception_toMessageData(v___y_4112_);
v___x_4120_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4115_, v___x_4119_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
if (lean_obj_tag(v___x_4120_) == 0)
{
lean_object* v___x_4122_; uint8_t v_isShared_4123_; uint8_t v_isSharedCheck_4127_; 
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; 
v_unused_4128_ = lean_ctor_get(v___x_4120_, 0);
lean_dec(v_unused_4128_);
v___x_4122_ = v___x_4120_;
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
else
{
lean_dec(v___x_4120_);
v___x_4122_ = lean_box(0);
v_isShared_4123_ = v_isSharedCheck_4127_;
goto v_resetjp_4121_;
}
v_resetjp_4121_:
{
lean_object* v___x_4125_; 
if (v_isShared_4123_ == 0)
{
lean_ctor_set_tag(v___x_4122_, 1);
lean_ctor_set(v___x_4122_, 0, v___y_4112_);
v___x_4125_ = v___x_4122_;
goto v_reusejp_4124_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___y_4112_);
v___x_4125_ = v_reuseFailAlloc_4126_;
goto v_reusejp_4124_;
}
v_reusejp_4124_:
{
return v___x_4125_;
}
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
lean_dec_ref(v___y_4112_);
v_a_4129_ = lean_ctor_get(v___x_4120_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4120_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4120_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4120_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4112_);
return v___y_4113_;
}
}
v___jp_4137_:
{
uint8_t v___x_4140_; 
v___x_4140_ = l_Lean_Exception_isInterrupt(v_a_4139_);
if (v___x_4140_ == 0)
{
uint8_t v___x_4141_; 
lean_inc_ref(v_a_4139_);
v___x_4141_ = l_Lean_Exception_isRuntime(v_a_4139_);
v___y_4112_ = v_a_4139_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___x_4141_;
goto v___jp_4111_;
}
else
{
v___y_4112_ = v_a_4139_;
v___y_4113_ = v___y_4138_;
v___y_4114_ = v___x_4140_;
goto v___jp_4111_;
}
}
v___jp_4146_:
{
lean_object* v___x_4150_; double v___x_4151_; double v___x_4152_; double v___x_4153_; double v___x_4154_; double v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4150_ = lean_io_mono_nanos_now();
v___x_4151_ = lean_float_of_nat(v___y_4147_);
v___x_4152_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4153_ = lean_float_div(v___x_4151_, v___x_4152_);
v___x_4154_ = lean_float_of_nat(v___x_4150_);
v___x_4155_ = lean_float_div(v___x_4154_, v___x_4152_);
v___x_4156_ = lean_box_float(v___x_4153_);
v___x_4157_ = lean_box_float(v___x_4155_);
v___x_4158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v_a_4149_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4142_, v_hasTrace_4107_, v___x_4143_, v_options_4106_, v___x_4145_, v___y_4148_, v___f_4110_, v___x_4159_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
return v___x_4160_;
}
v___jp_4161_:
{
lean_object* v___x_4165_; 
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v_a_4164_);
v___y_4147_ = v___y_4162_;
v___y_4148_ = v___y_4163_;
v_a_4149_ = v___x_4165_;
goto v___jp_4146_;
}
v___jp_4166_:
{
if (v___y_4170_ == 0)
{
lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; 
v___x_4171_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4172_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4173_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4106_, v___x_4172_);
if (v___x_4173_ == 0)
{
v___y_4162_ = v___y_4167_;
v___y_4163_ = v___y_4168_;
v_a_4164_ = v___y_4169_;
goto v___jp_4161_;
}
else
{
lean_object* v___x_4174_; lean_object* v___x_4175_; 
lean_inc_ref(v___y_4169_);
v___x_4174_ = l_Lean_Exception_toMessageData(v___y_4169_);
v___x_4175_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4171_, v___x_4174_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_dec_ref_known(v___x_4175_, 1);
v___y_4162_ = v___y_4167_;
v___y_4163_ = v___y_4168_;
v_a_4164_ = v___y_4169_;
goto v___jp_4161_;
}
else
{
lean_object* v_a_4176_; 
lean_dec_ref(v___y_4169_);
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref_known(v___x_4175_, 1);
v___y_4162_ = v___y_4167_;
v___y_4163_ = v___y_4168_;
v_a_4164_ = v_a_4176_;
goto v___jp_4161_;
}
}
}
else
{
v___y_4162_ = v___y_4167_;
v___y_4163_ = v___y_4168_;
v_a_4164_ = v___y_4169_;
goto v___jp_4161_;
}
}
v___jp_4177_:
{
uint8_t v___x_4181_; 
v___x_4181_ = l_Lean_Exception_isInterrupt(v_a_4180_);
if (v___x_4181_ == 0)
{
uint8_t v___x_4182_; 
lean_inc_ref(v_a_4180_);
v___x_4182_ = l_Lean_Exception_isRuntime(v_a_4180_);
v___y_4167_ = v___y_4178_;
v___y_4168_ = v___y_4179_;
v___y_4169_ = v_a_4180_;
v___y_4170_ = v___x_4182_;
goto v___jp_4166_;
}
else
{
v___y_4167_ = v___y_4178_;
v___y_4168_ = v___y_4179_;
v___y_4169_ = v_a_4180_;
v___y_4170_ = v___x_4181_;
goto v___jp_4166_;
}
}
v___jp_4183_:
{
lean_object* v___x_4187_; 
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v_a_4186_);
v___y_4147_ = v___y_4184_;
v___y_4148_ = v___y_4185_;
v_a_4149_ = v___x_4187_;
goto v___jp_4146_;
}
v___jp_4188_:
{
lean_object* v___x_4192_; double v___x_4193_; double v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4192_ = lean_io_get_num_heartbeats();
v___x_4193_ = lean_float_of_nat(v___y_4189_);
v___x_4194_ = lean_float_of_nat(v___x_4192_);
v___x_4195_ = lean_box_float(v___x_4193_);
v___x_4196_ = lean_box_float(v___x_4194_);
v___x_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_a_4191_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4142_, v_hasTrace_4107_, v___x_4143_, v_options_4106_, v___x_4145_, v___y_4190_, v___f_4110_, v___x_4198_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
return v___x_4199_;
}
v___jp_4200_:
{
lean_object* v___x_4204_; 
v___x_4204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4204_, 0, v_a_4203_);
v___y_4189_ = v___y_4201_;
v___y_4190_ = v___y_4202_;
v_a_4191_ = v___x_4204_;
goto v___jp_4188_;
}
v___jp_4205_:
{
if (v___y_4209_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4211_; uint8_t v___x_4212_; 
v___x_4210_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4211_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4212_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4106_, v___x_4211_);
if (v___x_4212_ == 0)
{
v___y_4201_ = v___y_4206_;
v___y_4202_ = v___y_4207_;
v_a_4203_ = v___y_4208_;
goto v___jp_4200_;
}
else
{
lean_object* v___x_4213_; lean_object* v___x_4214_; 
lean_inc_ref(v___y_4208_);
v___x_4213_ = l_Lean_Exception_toMessageData(v___y_4208_);
v___x_4214_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4210_, v___x_4213_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_dec_ref_known(v___x_4214_, 1);
v___y_4201_ = v___y_4206_;
v___y_4202_ = v___y_4207_;
v_a_4203_ = v___y_4208_;
goto v___jp_4200_;
}
else
{
lean_object* v_a_4215_; 
lean_dec_ref(v___y_4208_);
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
v___y_4201_ = v___y_4206_;
v___y_4202_ = v___y_4207_;
v_a_4203_ = v_a_4215_;
goto v___jp_4200_;
}
}
}
else
{
v___y_4201_ = v___y_4206_;
v___y_4202_ = v___y_4207_;
v_a_4203_ = v___y_4208_;
goto v___jp_4200_;
}
}
v___jp_4216_:
{
uint8_t v___x_4220_; 
v___x_4220_ = l_Lean_Exception_isInterrupt(v_a_4219_);
if (v___x_4220_ == 0)
{
uint8_t v___x_4221_; 
lean_inc_ref(v_a_4219_);
v___x_4221_ = l_Lean_Exception_isRuntime(v_a_4219_);
v___y_4206_ = v___y_4217_;
v___y_4207_ = v___y_4218_;
v___y_4208_ = v_a_4219_;
v___y_4209_ = v___x_4221_;
goto v___jp_4205_;
}
else
{
v___y_4206_ = v___y_4217_;
v___y_4207_ = v___y_4218_;
v___y_4208_ = v_a_4219_;
v___y_4209_ = v___x_4220_;
goto v___jp_4205_;
}
}
v___jp_4222_:
{
lean_object* v___x_4226_; 
v___x_4226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4226_, 0, v_a_4225_);
v___y_4189_ = v___y_4223_;
v___y_4190_ = v___y_4224_;
v_a_4191_ = v___x_4226_;
goto v___jp_4188_;
}
v___jp_4227_:
{
lean_object* v___x_4228_; lean_object* v_a_4229_; lean_object* v___x_4230_; uint8_t v___x_4231_; 
v___x_4228_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4104_);
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref(v___x_4228_);
v___x_4230_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4231_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4106_, v___x_4230_);
if (v___x_4231_ == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4232_ = lean_io_mono_nanos_now();
lean_inc(v_a_4104_);
lean_inc_ref(v_a_4103_);
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
v___x_4233_ = lean_apply_5(v_k_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, lean_box(0));
if (lean_obj_tag(v___x_4233_) == 0)
{
lean_object* v_a_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; uint8_t v___x_4237_; 
v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4234_);
lean_dec_ref_known(v___x_4233_, 1);
v___x_4235_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4236_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4106_, v___x_4236_);
if (v___x_4237_ == 0)
{
v___y_4184_ = v___x_4232_;
v___y_4185_ = v_a_4229_;
v_a_4186_ = v_a_4234_;
goto v___jp_4183_;
}
else
{
lean_object* v___x_4238_; lean_object* v___x_4239_; 
lean_inc(v_a_4234_);
v___x_4238_ = l_Lean_MessageData_ofExpr(v_a_4234_);
v___x_4239_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4235_, v___x_4238_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
if (lean_obj_tag(v___x_4239_) == 0)
{
lean_dec_ref_known(v___x_4239_, 1);
v___y_4184_ = v___x_4232_;
v___y_4185_ = v_a_4229_;
v_a_4186_ = v_a_4234_;
goto v___jp_4183_;
}
else
{
lean_object* v_a_4240_; 
lean_dec(v_a_4234_);
v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
lean_inc(v_a_4240_);
lean_dec_ref_known(v___x_4239_, 1);
v___y_4178_ = v___x_4232_;
v___y_4179_ = v_a_4229_;
v_a_4180_ = v_a_4240_;
goto v___jp_4177_;
}
}
}
else
{
lean_object* v_a_4241_; 
v_a_4241_ = lean_ctor_get(v___x_4233_, 0);
lean_inc(v_a_4241_);
lean_dec_ref_known(v___x_4233_, 1);
v___y_4178_ = v___x_4232_;
v___y_4179_ = v_a_4229_;
v_a_4180_ = v_a_4241_;
goto v___jp_4177_;
}
}
else
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4104_);
lean_inc_ref(v_a_4103_);
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
v___x_4243_ = lean_apply_5(v_k_4100_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_, lean_box(0));
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
v___x_4245_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4246_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4109_, v_options_4106_, v___x_4246_);
if (v___x_4247_ == 0)
{
v___y_4223_ = v___x_4242_;
v___y_4224_ = v_a_4229_;
v_a_4225_ = v_a_4244_;
goto v___jp_4222_;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_inc(v_a_4244_);
v___x_4248_ = l_Lean_MessageData_ofExpr(v_a_4244_);
v___x_4249_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4245_, v___x_4248_, v_a_4101_, v_a_4102_, v_a_4103_, v_a_4104_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_dec_ref_known(v___x_4249_, 1);
v___y_4223_ = v___x_4242_;
v___y_4224_ = v_a_4229_;
v_a_4225_ = v_a_4244_;
goto v___jp_4222_;
}
else
{
lean_object* v_a_4250_; 
lean_dec(v_a_4244_);
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref_known(v___x_4249_, 1);
v___y_4217_ = v___x_4242_;
v___y_4218_ = v_a_4229_;
v_a_4219_ = v_a_4250_;
goto v___jp_4216_;
}
}
}
else
{
lean_object* v_a_4251_; 
v_a_4251_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v___x_4243_, 1);
v___y_4217_ = v___x_4242_;
v___y_4218_ = v_a_4229_;
v_a_4219_ = v_a_4251_;
goto v___jp_4216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4278_, lean_object* v_xs_4279_, lean_object* v_k_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v_res_4286_; 
v_res_4286_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4278_, v_xs_4279_, v_k_4280_, v_a_4281_, v_a_4282_, v_a_4283_, v_a_4284_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
return v_res_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4287_, lean_object* v_xs_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_){
_start:
{
lean_object* v___f_4294_; uint8_t v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; 
lean_inc_ref(v_xs_4288_);
lean_inc(v_constName_4287_);
v___f_4294_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4294_, 0, v_constName_4287_);
lean_closure_set(v___f_4294_, 1, v_xs_4288_);
v___x_4295_ = 0;
v___x_4296_ = lean_box(v___x_4295_);
v___x_4297_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4297_, 0, lean_box(0));
lean_closure_set(v___x_4297_, 1, v___f_4294_);
lean_closure_set(v___x_4297_, 2, v___x_4296_);
v___x_4298_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4287_, v_xs_4288_, v___x_4297_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_);
return v___x_4298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4299_, lean_object* v_xs_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_, lean_object* v_a_4304_, lean_object* v_a_4305_){
_start:
{
lean_object* v_res_4306_; 
v_res_4306_ = l_Lean_Meta_mkAppOptM(v_constName_4299_, v_xs_4300_, v_a_4301_, v_a_4302_, v_a_4303_, v_a_4304_);
lean_dec(v_a_4304_);
lean_dec_ref(v_a_4303_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
return v_res_4306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4307_, lean_object* v_xs_4308_, lean_object* v_x_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4315_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4316_ = l_Lean_MessageData_ofExpr(v_f_4307_);
v___x_4317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4315_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
v___x_4318_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4317_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = lean_array_to_list(v_xs_4308_);
v___x_4321_ = lean_box(0);
v___x_4322_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4320_, v___x_4321_);
v___x_4323_ = l_Lean_MessageData_ofList(v___x_4322_);
v___x_4324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4319_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
v___x_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4325_, 0, v___x_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4326_, lean_object* v_xs_4327_, lean_object* v_x_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v_res_4334_; 
v_res_4334_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4326_, v_xs_4327_, v_x_4328_, v___y_4329_, v___y_4330_, v___y_4331_, v___y_4332_);
lean_dec(v___y_4332_);
lean_dec_ref(v___y_4331_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec_ref(v_x_4328_);
return v_res_4334_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4335_, lean_object* v_xs_4336_, lean_object* v_k_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_){
_start:
{
lean_object* v_options_4343_; uint8_t v_hasTrace_4344_; 
v_options_4343_ = lean_ctor_get(v_a_4340_, 2);
v_hasTrace_4344_ = lean_ctor_get_uint8(v_options_4343_, sizeof(void*)*1);
if (v_hasTrace_4344_ == 0)
{
lean_object* v___x_4345_; 
lean_dec_ref(v_xs_4336_);
lean_dec_ref(v_f_4335_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
v___x_4345_ = lean_apply_5(v_k_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, lean_box(0));
return v___x_4345_;
}
else
{
lean_object* v_inheritedTraceOptions_4346_; lean_object* v___f_4347_; lean_object* v___y_4349_; lean_object* v___y_4350_; uint8_t v___y_4351_; lean_object* v___y_4375_; lean_object* v_a_4376_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v_a_4386_; lean_object* v___y_4399_; lean_object* v___y_4400_; lean_object* v_a_4401_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4406_; uint8_t v___y_4407_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v_a_4417_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v_a_4423_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v_a_4428_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v_a_4440_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; uint8_t v___y_4446_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v_a_4456_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v_a_4462_; 
v_inheritedTraceOptions_4346_ = lean_ctor_get(v_a_4340_, 13);
v___f_4347_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4347_, 0, v_f_4335_);
lean_closure_set(v___f_4347_, 1, v_xs_4336_);
v___x_4379_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4380_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4381_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4382_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4343_, v___x_4381_);
if (v___x_4382_ == 0)
{
lean_object* v___x_4489_; uint8_t v___x_4490_; 
v___x_4489_ = l_Lean_trace_profiler;
v___x_4490_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4343_, v___x_4489_);
if (v___x_4490_ == 0)
{
lean_object* v___x_4491_; 
lean_dec_ref(v___f_4347_);
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
v___x_4491_ = lean_apply_5(v_k_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, lean_box(0));
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
v___x_4493_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4494_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4343_, v___x_4494_);
if (v___x_4495_ == 0)
{
lean_dec(v_a_4492_);
return v___x_4491_;
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
lean_dec_ref_known(v___x_4491_, 1);
lean_inc(v_a_4492_);
v___x_4496_ = l_Lean_MessageData_ofExpr(v_a_4492_);
v___x_4497_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4493_, v___x_4496_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4504_; 
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4504_ == 0)
{
lean_object* v_unused_4505_; 
v_unused_4505_ = lean_ctor_get(v___x_4497_, 0);
lean_dec(v_unused_4505_);
v___x_4499_ = v___x_4497_;
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
else
{
lean_dec(v___x_4497_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4504_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4502_; 
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v_a_4492_);
v___x_4502_ = v___x_4499_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4503_; 
v_reuseFailAlloc_4503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4503_, 0, v_a_4492_);
v___x_4502_ = v_reuseFailAlloc_4503_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
return v___x_4502_;
}
}
}
else
{
lean_object* v_a_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4513_; 
lean_dec(v_a_4492_);
v_a_4506_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4513_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4513_ == 0)
{
v___x_4508_ = v___x_4497_;
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
else
{
lean_inc(v_a_4506_);
lean_dec(v___x_4497_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4513_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4511_; 
lean_inc(v_a_4506_);
if (v_isShared_4509_ == 0)
{
v___x_4511_ = v___x_4508_;
goto v_reusejp_4510_;
}
else
{
lean_object* v_reuseFailAlloc_4512_; 
v_reuseFailAlloc_4512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4512_, 0, v_a_4506_);
v___x_4511_ = v_reuseFailAlloc_4512_;
goto v_reusejp_4510_;
}
v_reusejp_4510_:
{
v___y_4375_ = v___x_4511_;
v_a_4376_ = v_a_4506_;
goto v___jp_4374_;
}
}
}
}
}
else
{
lean_object* v_a_4514_; 
v_a_4514_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4514_);
v___y_4375_ = v___x_4491_;
v_a_4376_ = v_a_4514_;
goto v___jp_4374_;
}
}
else
{
goto v___jp_4464_;
}
}
else
{
goto v___jp_4464_;
}
v___jp_4348_:
{
if (v___y_4351_ == 0)
{
lean_object* v___x_4352_; lean_object* v___x_4353_; uint8_t v___x_4354_; 
lean_dec_ref(v___y_4350_);
v___x_4352_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4353_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4354_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4343_, v___x_4353_);
if (v___x_4354_ == 0)
{
lean_object* v___x_4355_; 
v___x_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4355_, 0, v___y_4349_);
return v___x_4355_;
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; 
lean_inc_ref(v___y_4349_);
v___x_4356_ = l_Lean_Exception_toMessageData(v___y_4349_);
v___x_4357_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4352_, v___x_4356_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4364_; 
v_isSharedCheck_4364_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4364_ == 0)
{
lean_object* v_unused_4365_; 
v_unused_4365_ = lean_ctor_get(v___x_4357_, 0);
lean_dec(v_unused_4365_);
v___x_4359_ = v___x_4357_;
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
else
{
lean_dec(v___x_4357_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4364_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v___x_4362_; 
if (v_isShared_4360_ == 0)
{
lean_ctor_set_tag(v___x_4359_, 1);
lean_ctor_set(v___x_4359_, 0, v___y_4349_);
v___x_4362_ = v___x_4359_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___y_4349_);
v___x_4362_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
return v___x_4362_;
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_dec_ref(v___y_4349_);
v_a_4366_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4357_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4357_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4349_);
return v___y_4350_;
}
}
v___jp_4374_:
{
uint8_t v___x_4377_; 
v___x_4377_ = l_Lean_Exception_isInterrupt(v_a_4376_);
if (v___x_4377_ == 0)
{
uint8_t v___x_4378_; 
lean_inc_ref(v_a_4376_);
v___x_4378_ = l_Lean_Exception_isRuntime(v_a_4376_);
v___y_4349_ = v_a_4376_;
v___y_4350_ = v___y_4375_;
v___y_4351_ = v___x_4378_;
goto v___jp_4348_;
}
else
{
v___y_4349_ = v_a_4376_;
v___y_4350_ = v___y_4375_;
v___y_4351_ = v___x_4377_;
goto v___jp_4348_;
}
}
v___jp_4383_:
{
lean_object* v___x_4387_; double v___x_4388_; double v___x_4389_; double v___x_4390_; double v___x_4391_; double v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4387_ = lean_io_mono_nanos_now();
v___x_4388_ = lean_float_of_nat(v___y_4385_);
v___x_4389_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4390_ = lean_float_div(v___x_4388_, v___x_4389_);
v___x_4391_ = lean_float_of_nat(v___x_4387_);
v___x_4392_ = lean_float_div(v___x_4391_, v___x_4389_);
v___x_4393_ = lean_box_float(v___x_4390_);
v___x_4394_ = lean_box_float(v___x_4392_);
v___x_4395_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4396_, 0, v_a_4386_);
lean_ctor_set(v___x_4396_, 1, v___x_4395_);
v___x_4397_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4379_, v_hasTrace_4344_, v___x_4380_, v_options_4343_, v___x_4382_, v___y_4384_, v___f_4347_, v___x_4396_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
return v___x_4397_;
}
v___jp_4398_:
{
lean_object* v___x_4402_; 
v___x_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4402_, 0, v_a_4401_);
v___y_4384_ = v___y_4399_;
v___y_4385_ = v___y_4400_;
v_a_4386_ = v___x_4402_;
goto v___jp_4383_;
}
v___jp_4403_:
{
if (v___y_4407_ == 0)
{
lean_object* v___x_4408_; lean_object* v___x_4409_; uint8_t v___x_4410_; 
v___x_4408_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4409_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4410_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4343_, v___x_4409_);
if (v___x_4410_ == 0)
{
v___y_4399_ = v___y_4405_;
v___y_4400_ = v___y_4406_;
v_a_4401_ = v___y_4404_;
goto v___jp_4398_;
}
else
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
lean_inc_ref(v___y_4404_);
v___x_4411_ = l_Lean_Exception_toMessageData(v___y_4404_);
v___x_4412_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4408_, v___x_4411_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_dec_ref_known(v___x_4412_, 1);
v___y_4399_ = v___y_4405_;
v___y_4400_ = v___y_4406_;
v_a_4401_ = v___y_4404_;
goto v___jp_4398_;
}
else
{
lean_object* v_a_4413_; 
lean_dec_ref(v___y_4404_);
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___y_4399_ = v___y_4405_;
v___y_4400_ = v___y_4406_;
v_a_4401_ = v_a_4413_;
goto v___jp_4398_;
}
}
}
else
{
v___y_4399_ = v___y_4405_;
v___y_4400_ = v___y_4406_;
v_a_4401_ = v___y_4404_;
goto v___jp_4398_;
}
}
v___jp_4414_:
{
uint8_t v___x_4418_; 
v___x_4418_ = l_Lean_Exception_isInterrupt(v_a_4417_);
if (v___x_4418_ == 0)
{
uint8_t v___x_4419_; 
lean_inc_ref(v_a_4417_);
v___x_4419_ = l_Lean_Exception_isRuntime(v_a_4417_);
v___y_4404_ = v_a_4417_;
v___y_4405_ = v___y_4415_;
v___y_4406_ = v___y_4416_;
v___y_4407_ = v___x_4419_;
goto v___jp_4403_;
}
else
{
v___y_4404_ = v_a_4417_;
v___y_4405_ = v___y_4415_;
v___y_4406_ = v___y_4416_;
v___y_4407_ = v___x_4418_;
goto v___jp_4403_;
}
}
v___jp_4420_:
{
lean_object* v___x_4424_; 
v___x_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4424_, 0, v_a_4423_);
v___y_4384_ = v___y_4421_;
v___y_4385_ = v___y_4422_;
v_a_4386_ = v___x_4424_;
goto v___jp_4383_;
}
v___jp_4425_:
{
lean_object* v___x_4429_; double v___x_4430_; double v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; 
v___x_4429_ = lean_io_get_num_heartbeats();
v___x_4430_ = lean_float_of_nat(v___y_4427_);
v___x_4431_ = lean_float_of_nat(v___x_4429_);
v___x_4432_ = lean_box_float(v___x_4430_);
v___x_4433_ = lean_box_float(v___x_4431_);
v___x_4434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4434_, 0, v___x_4432_);
lean_ctor_set(v___x_4434_, 1, v___x_4433_);
v___x_4435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4435_, 0, v_a_4428_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
v___x_4436_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4379_, v_hasTrace_4344_, v___x_4380_, v_options_4343_, v___x_4382_, v___y_4426_, v___f_4347_, v___x_4435_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
return v___x_4436_;
}
v___jp_4437_:
{
lean_object* v___x_4441_; 
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v_a_4440_);
v___y_4426_ = v___y_4438_;
v___y_4427_ = v___y_4439_;
v_a_4428_ = v___x_4441_;
goto v___jp_4425_;
}
v___jp_4442_:
{
if (v___y_4446_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; uint8_t v___x_4449_; 
v___x_4447_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4448_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4449_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4343_, v___x_4448_);
if (v___x_4449_ == 0)
{
v___y_4438_ = v___y_4443_;
v___y_4439_ = v___y_4444_;
v_a_4440_ = v___y_4445_;
goto v___jp_4437_;
}
else
{
lean_object* v___x_4450_; lean_object* v___x_4451_; 
lean_inc_ref(v___y_4445_);
v___x_4450_ = l_Lean_Exception_toMessageData(v___y_4445_);
v___x_4451_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4447_, v___x_4450_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4451_) == 0)
{
lean_dec_ref_known(v___x_4451_, 1);
v___y_4438_ = v___y_4443_;
v___y_4439_ = v___y_4444_;
v_a_4440_ = v___y_4445_;
goto v___jp_4437_;
}
else
{
lean_object* v_a_4452_; 
lean_dec_ref(v___y_4445_);
v_a_4452_ = lean_ctor_get(v___x_4451_, 0);
lean_inc(v_a_4452_);
lean_dec_ref_known(v___x_4451_, 1);
v___y_4438_ = v___y_4443_;
v___y_4439_ = v___y_4444_;
v_a_4440_ = v_a_4452_;
goto v___jp_4437_;
}
}
}
else
{
v___y_4438_ = v___y_4443_;
v___y_4439_ = v___y_4444_;
v_a_4440_ = v___y_4445_;
goto v___jp_4437_;
}
}
v___jp_4453_:
{
uint8_t v___x_4457_; 
v___x_4457_ = l_Lean_Exception_isInterrupt(v_a_4456_);
if (v___x_4457_ == 0)
{
uint8_t v___x_4458_; 
lean_inc_ref(v_a_4456_);
v___x_4458_ = l_Lean_Exception_isRuntime(v_a_4456_);
v___y_4443_ = v___y_4454_;
v___y_4444_ = v___y_4455_;
v___y_4445_ = v_a_4456_;
v___y_4446_ = v___x_4458_;
goto v___jp_4442_;
}
else
{
v___y_4443_ = v___y_4454_;
v___y_4444_ = v___y_4455_;
v___y_4445_ = v_a_4456_;
v___y_4446_ = v___x_4457_;
goto v___jp_4442_;
}
}
v___jp_4459_:
{
lean_object* v___x_4463_; 
v___x_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4463_, 0, v_a_4462_);
v___y_4426_ = v___y_4460_;
v___y_4427_ = v___y_4461_;
v_a_4428_ = v___x_4463_;
goto v___jp_4425_;
}
v___jp_4464_:
{
lean_object* v___x_4465_; lean_object* v_a_4466_; lean_object* v___x_4467_; uint8_t v___x_4468_; 
v___x_4465_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4341_);
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref(v___x_4465_);
v___x_4467_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4468_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4343_, v___x_4467_);
if (v___x_4468_ == 0)
{
lean_object* v___x_4469_; lean_object* v___x_4470_; 
v___x_4469_ = lean_io_mono_nanos_now();
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
v___x_4470_ = lean_apply_5(v_k_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, lean_box(0));
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; uint8_t v___x_4474_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4471_);
lean_dec_ref_known(v___x_4470_, 1);
v___x_4472_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4473_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4474_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4343_, v___x_4473_);
if (v___x_4474_ == 0)
{
v___y_4421_ = v_a_4466_;
v___y_4422_ = v___x_4469_;
v_a_4423_ = v_a_4471_;
goto v___jp_4420_;
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
lean_inc(v_a_4471_);
v___x_4475_ = l_Lean_MessageData_ofExpr(v_a_4471_);
v___x_4476_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4472_, v___x_4475_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_dec_ref_known(v___x_4476_, 1);
v___y_4421_ = v_a_4466_;
v___y_4422_ = v___x_4469_;
v_a_4423_ = v_a_4471_;
goto v___jp_4420_;
}
else
{
lean_object* v_a_4477_; 
lean_dec(v_a_4471_);
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
v___y_4415_ = v_a_4466_;
v___y_4416_ = v___x_4469_;
v_a_4417_ = v_a_4477_;
goto v___jp_4414_;
}
}
}
else
{
lean_object* v_a_4478_; 
v_a_4478_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4478_);
lean_dec_ref_known(v___x_4470_, 1);
v___y_4415_ = v_a_4466_;
v___y_4416_ = v___x_4469_;
v_a_4417_ = v_a_4478_;
goto v___jp_4414_;
}
}
else
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
v___x_4479_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4341_);
lean_inc_ref(v_a_4340_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
v___x_4480_ = lean_apply_5(v_k_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, lean_box(0));
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref_known(v___x_4480_, 1);
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4483_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4346_, v_options_4343_, v___x_4483_);
if (v___x_4484_ == 0)
{
v___y_4460_ = v_a_4466_;
v___y_4461_ = v___x_4479_;
v_a_4462_ = v_a_4481_;
goto v___jp_4459_;
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; 
lean_inc(v_a_4481_);
v___x_4485_ = l_Lean_MessageData_ofExpr(v_a_4481_);
v___x_4486_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4482_, v___x_4485_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_dec_ref_known(v___x_4486_, 1);
v___y_4460_ = v_a_4466_;
v___y_4461_ = v___x_4479_;
v_a_4462_ = v_a_4481_;
goto v___jp_4459_;
}
else
{
lean_object* v_a_4487_; 
lean_dec(v_a_4481_);
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___y_4454_ = v_a_4466_;
v___y_4455_ = v___x_4479_;
v_a_4456_ = v_a_4487_;
goto v___jp_4453_;
}
}
}
else
{
lean_object* v_a_4488_; 
v_a_4488_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4480_, 1);
v___y_4454_ = v_a_4466_;
v___y_4455_ = v___x_4479_;
v_a_4456_ = v_a_4488_;
goto v___jp_4453_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4515_, lean_object* v_xs_4516_, lean_object* v_k_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_, lean_object* v_a_4521_, lean_object* v_a_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4515_, v_xs_4516_, v_k_4517_, v_a_4518_, v_a_4519_, v_a_4520_, v_a_4521_);
lean_dec(v_a_4521_);
lean_dec_ref(v_a_4520_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4524_, lean_object* v_xs_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v___x_4531_; 
lean_inc(v_a_4529_);
lean_inc_ref(v_a_4528_);
lean_inc(v_a_4527_);
lean_inc_ref(v_a_4526_);
lean_inc_ref(v_f_4524_);
v___x_4531_ = lean_infer_type(v_f_4524_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; uint8_t v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc(v_a_4532_);
lean_dec_ref_known(v___x_4531_, 1);
v___x_4533_ = lean_unsigned_to_nat(0u);
v___x_4534_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4525_);
lean_inc_ref(v_f_4524_);
v___x_4535_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4535_, 0, v_f_4524_);
lean_closure_set(v___x_4535_, 1, v_xs_4525_);
lean_closure_set(v___x_4535_, 2, v___x_4533_);
lean_closure_set(v___x_4535_, 3, v___x_4534_);
lean_closure_set(v___x_4535_, 4, v___x_4533_);
lean_closure_set(v___x_4535_, 5, v___x_4534_);
lean_closure_set(v___x_4535_, 6, v_a_4532_);
v___x_4536_ = 0;
v___x_4537_ = lean_box(v___x_4536_);
v___x_4538_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4538_, 0, lean_box(0));
lean_closure_set(v___x_4538_, 1, v___x_4535_);
lean_closure_set(v___x_4538_, 2, v___x_4537_);
v___x_4539_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4524_, v_xs_4525_, v___x_4538_, v_a_4526_, v_a_4527_, v_a_4528_, v_a_4529_);
return v___x_4539_;
}
else
{
lean_dec_ref(v_xs_4525_);
lean_dec_ref(v_f_4524_);
return v___x_4531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4540_, lean_object* v_xs_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l_Lean_Meta_mkAppOptM_x27(v_f_4540_, v_xs_4541_, v_a_4542_, v_a_4543_, v_a_4544_, v_a_4545_);
lean_dec(v_a_4545_);
lean_dec_ref(v_a_4544_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
return v_res_4547_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
v___x_4555_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4556_ = l_Lean_MessageData_ofFormat(v___x_4555_);
return v___x_4556_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4557_, lean_object* v_h1_4558_, lean_object* v_h2_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_){
_start:
{
lean_object* v___x_4565_; uint8_t v___x_4566_; 
v___x_4565_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4566_ = l_Lean_Expr_isAppOf(v_h2_4559_, v___x_4565_);
if (v___x_4566_ == 0)
{
lean_object* v___x_4567_; 
lean_inc_ref(v_h2_4559_);
v___x_4567_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4559_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4567_) == 0)
{
lean_object* v_a_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; uint8_t v___x_4571_; 
v_a_4568_ = lean_ctor_get(v___x_4567_, 0);
lean_inc(v_a_4568_);
lean_dec_ref_known(v___x_4567_, 1);
v___x_4569_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4570_ = lean_unsigned_to_nat(3u);
v___x_4571_ = l_Lean_Expr_isAppOfArity(v_a_4568_, v___x_4569_, v___x_4570_);
if (v___x_4571_ == 0)
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
lean_dec_ref(v_h1_4558_);
lean_dec_ref(v_motive_4557_);
v___x_4572_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4573_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4574_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4559_, v_a_4568_);
v___x_4575_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___x_4573_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4572_, v___x_4575_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
return v___x_4576_;
}
else
{
lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; 
v___x_4577_ = l_Lean_Expr_appFn_x21(v_a_4568_);
v___x_4578_ = l_Lean_Expr_appFn_x21(v___x_4577_);
v___x_4579_ = l_Lean_Expr_appArg_x21(v___x_4578_);
lean_dec_ref(v___x_4578_);
lean_inc_ref(v___x_4579_);
v___x_4580_ = l_Lean_Meta_getLevel(v___x_4579_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4582_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref_known(v___x_4580_, 1);
lean_inc_ref(v_motive_4557_);
v___x_4582_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4557_, v_a_4560_, v_a_4561_, v_a_4562_, v_a_4563_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4618_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4618_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4618_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
lean_object* v___y_4588_; lean_object* v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; 
if (lean_obj_tag(v_a_4583_) == 7)
{
lean_object* v_body_4597_; 
v_body_4597_ = lean_ctor_get(v_a_4583_, 2);
lean_inc_ref(v_body_4597_);
lean_dec_ref_known(v_a_4583_, 3);
if (lean_obj_tag(v_body_4597_) == 3)
{
lean_object* v_u_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4616_; 
v_u_4598_ = lean_ctor_get(v_body_4597_, 0);
lean_inc(v_u_4598_);
lean_dec_ref_known(v_body_4597_, 1);
v___x_4599_ = l_Lean_Expr_appArg_x21(v___x_4577_);
lean_dec_ref(v___x_4577_);
v___x_4600_ = l_Lean_Expr_appArg_x21(v_a_4568_);
lean_dec(v_a_4568_);
v___x_4601_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4602_ = lean_box(0);
v___x_4603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4603_, 0, v_a_4581_);
lean_ctor_set(v___x_4603_, 1, v___x_4602_);
v___x_4604_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4604_, 0, v_u_4598_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = l_Lean_mkConst(v___x_4601_, v___x_4604_);
v___x_4606_ = lean_unsigned_to_nat(6u);
v___x_4607_ = lean_mk_empty_array_with_capacity(v___x_4606_);
v___x_4608_ = lean_array_push(v___x_4607_, v___x_4579_);
v___x_4609_ = lean_array_push(v___x_4608_, v___x_4599_);
v___x_4610_ = lean_array_push(v___x_4609_, v_motive_4557_);
v___x_4611_ = lean_array_push(v___x_4610_, v_h1_4558_);
v___x_4612_ = lean_array_push(v___x_4611_, v___x_4600_);
v___x_4613_ = lean_array_push(v___x_4612_, v_h2_4559_);
v___x_4614_ = l_Lean_mkAppN(v___x_4605_, v___x_4613_);
lean_dec_ref(v___x_4613_);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v___x_4614_);
v___x_4616_ = v___x_4585_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4614_);
v___x_4616_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
return v___x_4616_;
}
}
else
{
lean_dec_ref(v_body_4597_);
lean_del_object(v___x_4585_);
lean_dec(v_a_4581_);
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4577_);
lean_dec(v_a_4568_);
lean_dec_ref(v_h2_4559_);
lean_dec_ref(v_h1_4558_);
v___y_4588_ = v_a_4560_;
v___y_4589_ = v_a_4561_;
v___y_4590_ = v_a_4562_;
v___y_4591_ = v_a_4563_;
goto v___jp_4587_;
}
}
else
{
lean_del_object(v___x_4585_);
lean_dec(v_a_4583_);
lean_dec(v_a_4581_);
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4577_);
lean_dec(v_a_4568_);
lean_dec_ref(v_h2_4559_);
lean_dec_ref(v_h1_4558_);
v___y_4588_ = v_a_4560_;
v___y_4589_ = v_a_4561_;
v___y_4590_ = v_a_4562_;
v___y_4591_ = v_a_4563_;
goto v___jp_4587_;
}
v___jp_4587_:
{
lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4592_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4593_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4594_ = l_Lean_indentExpr(v_motive_4557_);
v___x_4595_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4593_);
lean_ctor_set(v___x_4595_, 1, v___x_4594_);
v___x_4596_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4592_, v___x_4595_, v___y_4588_, v___y_4589_, v___y_4590_, v___y_4591_);
return v___x_4596_;
}
}
}
else
{
lean_dec(v_a_4581_);
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4577_);
lean_dec(v_a_4568_);
lean_dec_ref(v_h2_4559_);
lean_dec_ref(v_h1_4558_);
lean_dec_ref(v_motive_4557_);
return v___x_4582_;
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4577_);
lean_dec(v_a_4568_);
lean_dec_ref(v_h2_4559_);
lean_dec_ref(v_h1_4558_);
lean_dec_ref(v_motive_4557_);
v_a_4619_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4580_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4580_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4559_);
lean_dec_ref(v_h1_4558_);
lean_dec_ref(v_motive_4557_);
return v___x_4567_;
}
}
else
{
lean_object* v___x_4627_; 
lean_dec_ref(v_h2_4559_);
lean_dec_ref(v_motive_4557_);
v___x_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4627_, 0, v_h1_4558_);
return v___x_4627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4628_, lean_object* v_h1_4629_, lean_object* v_h2_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
lean_object* v_res_4636_; 
v_res_4636_ = l_Lean_Meta_mkEqNDRec(v_motive_4628_, v_h1_4629_, v_h2_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
lean_dec(v_a_4634_);
lean_dec_ref(v_a_4633_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
return v_res_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4641_, lean_object* v_h1_4642_, lean_object* v_h2_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
lean_object* v___x_4649_; uint8_t v___x_4650_; 
v___x_4649_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4650_ = l_Lean_Expr_isAppOf(v_h2_4643_, v___x_4649_);
if (v___x_4650_ == 0)
{
lean_object* v___x_4651_; 
lean_inc_ref(v_h2_4643_);
v___x_4651_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4643_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
if (lean_obj_tag(v___x_4651_) == 0)
{
lean_object* v_a_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; uint8_t v___x_4655_; 
v_a_4652_ = lean_ctor_get(v___x_4651_, 0);
lean_inc(v_a_4652_);
lean_dec_ref_known(v___x_4651_, 1);
v___x_4653_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4654_ = lean_unsigned_to_nat(3u);
v___x_4655_ = l_Lean_Expr_isAppOfArity(v_a_4652_, v___x_4653_, v___x_4654_);
if (v___x_4655_ == 0)
{
lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
lean_dec(v_a_4652_);
lean_dec_ref(v_h1_4642_);
lean_dec_ref(v_motive_4641_);
v___x_4656_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4657_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4658_ = l_Lean_indentExpr(v_h2_4643_);
v___x_4659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4659_, 0, v___x_4657_);
lean_ctor_set(v___x_4659_, 1, v___x_4658_);
v___x_4660_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4656_, v___x_4659_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
return v___x_4660_;
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4661_ = l_Lean_Expr_appFn_x21(v_a_4652_);
v___x_4662_ = l_Lean_Expr_appFn_x21(v___x_4661_);
v___x_4663_ = l_Lean_Expr_appArg_x21(v___x_4662_);
lean_dec_ref(v___x_4662_);
lean_inc_ref(v___x_4663_);
v___x_4664_ = l_Lean_Meta_getLevel(v___x_4663_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4666_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
lean_inc(v_a_4665_);
lean_dec_ref_known(v___x_4664_, 1);
lean_inc_ref(v_motive_4641_);
v___x_4666_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4641_, v_a_4644_, v_a_4645_, v_a_4646_, v_a_4647_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4703_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4669_ = v___x_4666_;
v_isShared_4670_ = v_isSharedCheck_4703_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4666_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4703_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
lean_object* v___y_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4675_; 
if (lean_obj_tag(v_a_4667_) == 7)
{
lean_object* v_body_4681_; 
v_body_4681_ = lean_ctor_get(v_a_4667_, 2);
lean_inc_ref(v_body_4681_);
lean_dec_ref_known(v_a_4667_, 3);
if (lean_obj_tag(v_body_4681_) == 7)
{
lean_object* v_body_4682_; 
v_body_4682_ = lean_ctor_get(v_body_4681_, 2);
lean_inc_ref(v_body_4682_);
lean_dec_ref_known(v_body_4681_, 3);
if (lean_obj_tag(v_body_4682_) == 3)
{
lean_object* v_u_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4701_; 
v_u_4683_ = lean_ctor_get(v_body_4682_, 0);
lean_inc(v_u_4683_);
lean_dec_ref_known(v_body_4682_, 1);
v___x_4684_ = l_Lean_Expr_appArg_x21(v___x_4661_);
lean_dec_ref(v___x_4661_);
v___x_4685_ = l_Lean_Expr_appArg_x21(v_a_4652_);
lean_dec(v_a_4652_);
v___x_4686_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4687_ = lean_box(0);
v___x_4688_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4688_, 0, v_a_4665_);
lean_ctor_set(v___x_4688_, 1, v___x_4687_);
v___x_4689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4689_, 0, v_u_4683_);
lean_ctor_set(v___x_4689_, 1, v___x_4688_);
v___x_4690_ = l_Lean_mkConst(v___x_4686_, v___x_4689_);
v___x_4691_ = lean_unsigned_to_nat(6u);
v___x_4692_ = lean_mk_empty_array_with_capacity(v___x_4691_);
v___x_4693_ = lean_array_push(v___x_4692_, v___x_4663_);
v___x_4694_ = lean_array_push(v___x_4693_, v___x_4684_);
v___x_4695_ = lean_array_push(v___x_4694_, v_motive_4641_);
v___x_4696_ = lean_array_push(v___x_4695_, v_h1_4642_);
v___x_4697_ = lean_array_push(v___x_4696_, v___x_4685_);
v___x_4698_ = lean_array_push(v___x_4697_, v_h2_4643_);
v___x_4699_ = l_Lean_mkAppN(v___x_4690_, v___x_4698_);
lean_dec_ref(v___x_4698_);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v___x_4699_);
v___x_4701_ = v___x_4669_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v___x_4699_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
else
{
lean_dec_ref(v_body_4682_);
lean_del_object(v___x_4669_);
lean_dec(v_a_4665_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4661_);
lean_dec(v_a_4652_);
lean_dec_ref(v_h2_4643_);
lean_dec_ref(v_h1_4642_);
v___y_4672_ = v_a_4644_;
v___y_4673_ = v_a_4645_;
v___y_4674_ = v_a_4646_;
v___y_4675_ = v_a_4647_;
goto v___jp_4671_;
}
}
else
{
lean_dec_ref(v_body_4681_);
lean_del_object(v___x_4669_);
lean_dec(v_a_4665_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4661_);
lean_dec(v_a_4652_);
lean_dec_ref(v_h2_4643_);
lean_dec_ref(v_h1_4642_);
v___y_4672_ = v_a_4644_;
v___y_4673_ = v_a_4645_;
v___y_4674_ = v_a_4646_;
v___y_4675_ = v_a_4647_;
goto v___jp_4671_;
}
}
else
{
lean_del_object(v___x_4669_);
lean_dec(v_a_4667_);
lean_dec(v_a_4665_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4661_);
lean_dec(v_a_4652_);
lean_dec_ref(v_h2_4643_);
lean_dec_ref(v_h1_4642_);
v___y_4672_ = v_a_4644_;
v___y_4673_ = v_a_4645_;
v___y_4674_ = v_a_4646_;
v___y_4675_ = v_a_4647_;
goto v___jp_4671_;
}
v___jp_4671_:
{
lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; 
v___x_4676_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4677_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4678_ = l_Lean_indentExpr(v_motive_4641_);
v___x_4679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4677_);
lean_ctor_set(v___x_4679_, 1, v___x_4678_);
v___x_4680_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4676_, v___x_4679_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
return v___x_4680_;
}
}
}
else
{
lean_dec(v_a_4665_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4661_);
lean_dec(v_a_4652_);
lean_dec_ref(v_h2_4643_);
lean_dec_ref(v_h1_4642_);
lean_dec_ref(v_motive_4641_);
return v___x_4666_;
}
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4661_);
lean_dec(v_a_4652_);
lean_dec_ref(v_h2_4643_);
lean_dec_ref(v_h1_4642_);
lean_dec_ref(v_motive_4641_);
v_a_4704_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4664_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4664_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4643_);
lean_dec_ref(v_h1_4642_);
lean_dec_ref(v_motive_4641_);
return v___x_4651_;
}
}
else
{
lean_object* v___x_4712_; 
lean_dec_ref(v_h2_4643_);
lean_dec_ref(v_motive_4641_);
v___x_4712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4712_, 0, v_h1_4642_);
return v___x_4712_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4713_, lean_object* v_h1_4714_, lean_object* v_h2_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean_Meta_mkEqRec(v_motive_4713_, v_h1_4714_, v_h2_4715_, v_a_4716_, v_a_4717_, v_a_4718_, v_a_4719_);
lean_dec(v_a_4719_);
lean_dec_ref(v_a_4718_);
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4726_, lean_object* v_pr_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v___x_4733_ = ((lean_object*)(l_Lean_Meta_mkEqMP___closed__1));
v___x_4734_ = lean_unsigned_to_nat(2u);
v___x_4735_ = lean_mk_empty_array_with_capacity(v___x_4734_);
v___x_4736_ = lean_array_push(v___x_4735_, v_eqProof_4726_);
v___x_4737_ = lean_array_push(v___x_4736_, v_pr_4727_);
v___x_4738_ = l_Lean_Meta_mkAppM(v___x_4733_, v___x_4737_, v_a_4728_, v_a_4729_, v_a_4730_, v_a_4731_);
return v___x_4738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4739_, lean_object* v_pr_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v_res_4746_; 
v_res_4746_ = l_Lean_Meta_mkEqMP(v_eqProof_4739_, v_pr_4740_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
lean_dec(v_a_4744_);
lean_dec_ref(v_a_4743_);
lean_dec(v_a_4742_);
lean_dec_ref(v_a_4741_);
return v_res_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4751_, lean_object* v_pr_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_){
_start:
{
lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; 
v___x_4758_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4759_ = lean_unsigned_to_nat(2u);
v___x_4760_ = lean_mk_empty_array_with_capacity(v___x_4759_);
v___x_4761_ = lean_array_push(v___x_4760_, v_eqProof_4751_);
v___x_4762_ = lean_array_push(v___x_4761_, v_pr_4752_);
v___x_4763_ = l_Lean_Meta_mkAppM(v___x_4758_, v___x_4762_, v_a_4753_, v_a_4754_, v_a_4755_, v_a_4756_);
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4764_, lean_object* v_pr_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_){
_start:
{
lean_object* v_res_4771_; 
v_res_4771_ = l_Lean_Meta_mkEqMPR(v_eqProof_4764_, v_pr_4765_, v_a_4766_, v_a_4767_, v_a_4768_, v_a_4769_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
return v_res_4771_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v___f_4778_; lean_object* v___x_13117__overap_4779_; lean_object* v___x_4780_; 
v___f_4778_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_13117__overap_4779_ = lean_panic_fn_borrowed(v___f_4778_, v_msg_4772_);
lean_inc(v___y_4776_);
lean_inc_ref(v___y_4775_);
lean_inc(v___y_4774_);
lean_inc_ref(v___y_4773_);
v___x_4780_ = lean_apply_5(v___x_13117__overap_4779_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, lean_box(0));
return v___x_4780_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v_res_4787_; 
v_res_4787_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_);
lean_dec(v___y_4785_);
lean_dec_ref(v___y_4784_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
return v_res_4787_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4788_, uint8_t v_skipRealize_4789_, lean_object* v___y_4790_){
_start:
{
lean_object* v___x_4792_; lean_object* v_env_4793_; uint8_t v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; 
v___x_4792_ = lean_st_ref_get(v___y_4790_);
v_env_4793_ = lean_ctor_get(v___x_4792_, 0);
lean_inc_ref(v_env_4793_);
lean_dec(v___x_4792_);
v___x_4794_ = l_Lean_Environment_contains(v_env_4793_, v_constName_4788_, v_skipRealize_4789_);
v___x_4795_ = lean_box(v___x_4794_);
v___x_4796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4795_);
return v___x_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4797_, lean_object* v_skipRealize_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
uint8_t v_skipRealize_boxed_4801_; lean_object* v_res_4802_; 
v_skipRealize_boxed_4801_ = lean_unbox(v_skipRealize_4798_);
v_res_4802_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4797_, v_skipRealize_boxed_4801_, v___y_4799_);
lean_dec(v___y_4799_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4803_, uint8_t v_skipRealize_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v___x_4810_; 
v___x_4810_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4803_, v_skipRealize_4804_, v___y_4808_);
return v___x_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4811_, lean_object* v_skipRealize_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_){
_start:
{
uint8_t v_skipRealize_boxed_4818_; lean_object* v_res_4819_; 
v_skipRealize_boxed_4818_ = lean_unbox(v_skipRealize_4812_);
v_res_4819_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4811_, v_skipRealize_boxed_4818_, v___y_4813_, v___y_4814_, v___y_4815_, v___y_4816_);
lean_dec(v___y_4816_);
lean_dec_ref(v___y_4815_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___x_4820_, lean_object* v_P_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; uint8_t v___x_4831_; lean_object* v___x_4832_; 
v___x_4827_ = lean_unsigned_to_nat(1u);
v___x_4828_ = lean_mk_empty_array_with_capacity(v___x_4827_);
lean_inc_ref(v_P_4821_);
v___x_4829_ = lean_array_push(v___x_4828_, v_P_4821_);
v___x_4830_ = 0;
v___x_4831_ = 1;
v___x_4832_ = l_Lean_Meta_mkLambdaFVars(v___x_4829_, v_P_4821_, v___x_4830_, v___x_4820_, v___x_4830_, v___x_4820_, v___x_4831_, v___y_4822_, v___y_4823_, v___y_4824_, v___y_4825_);
lean_dec_ref(v___x_4829_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___x_4833_, lean_object* v_P_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
uint8_t v___x_14332__boxed_4840_; lean_object* v_res_4841_; 
v___x_14332__boxed_4840_ = lean_unbox(v___x_4833_);
v_res_4841_ = l_Lean_Meta_mkNoConfusion___lam__0(v___x_14332__boxed_4840_, v_P_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
return v_res_4841_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4844_ = l_Lean_stringToMessageData(v___x_4843_);
return v___x_4844_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4847_ = l_Lean_stringToMessageData(v___x_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4848_, lean_object* v_b_4849_, lean_object* v_i_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v_stop_4856_; lean_object* v_step_4857_; lean_object* v_a_4859_; uint8_t v___x_4862_; 
v_stop_4856_ = lean_ctor_get(v_range_4848_, 1);
v_step_4857_ = lean_ctor_get(v_range_4848_, 2);
v___x_4862_ = lean_nat_dec_lt(v_i_4850_, v_stop_4856_);
if (v___x_4862_ == 0)
{
lean_object* v___x_4863_; 
lean_dec(v_i_4850_);
v___x_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4863_, 0, v_b_4849_);
return v___x_4863_;
}
else
{
lean_object* v___x_4864_; 
lean_inc(v___y_4854_);
lean_inc_ref(v___y_4853_);
lean_inc(v___y_4852_);
lean_inc_ref(v___y_4851_);
lean_inc_ref(v_b_4849_);
v___x_4864_ = lean_infer_type(v_b_4849_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = l_Lean_Meta_whnfForall(v_a_4865_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref_known(v___x_4866_, 1);
v___x_4868_ = l_Lean_Expr_bindingDomain_x21(v_a_4867_);
lean_dec(v_a_4867_);
lean_inc(v___y_4854_);
lean_inc_ref(v___y_4853_);
lean_inc(v___y_4852_);
lean_inc_ref(v___y_4851_);
v___x_4869_ = lean_whnf(v___x_4868_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; uint8_t v___x_4873_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
lean_inc(v_a_4870_);
lean_dec_ref_known(v___x_4869_, 1);
v___x_4871_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4872_ = lean_unsigned_to_nat(4u);
v___x_4873_ = l_Lean_Expr_isAppOfArity(v_a_4870_, v___x_4871_, v___x_4872_);
if (v___x_4873_ == 0)
{
lean_object* v___x_4874_; lean_object* v___x_4875_; uint8_t v___x_4876_; 
v___x_4874_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4875_ = lean_unsigned_to_nat(3u);
v___x_4876_ = l_Lean_Expr_isAppOfArity(v_a_4870_, v___x_4874_, v___x_4875_);
if (v___x_4876_ == 0)
{
lean_object* v___x_4877_; 
lean_dec(v_i_4850_);
lean_inc(v___y_4854_);
lean_inc_ref(v___y_4853_);
lean_inc(v___y_4852_);
lean_inc_ref(v___y_4851_);
v___x_4877_ = lean_infer_type(v_b_4849_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_object* v_a_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
v_a_4878_ = lean_ctor_get(v___x_4877_, 0);
lean_inc(v_a_4878_);
lean_dec_ref_known(v___x_4877_, 1);
v___x_4879_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4880_ = l_Lean_MessageData_ofExpr(v_a_4870_);
v___x_4881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4879_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4881_);
lean_ctor_set(v___x_4883_, 1, v___x_4882_);
v___x_4884_ = lean_unsigned_to_nat(30u);
v___x_4885_ = l_Lean_inlineExpr(v_a_4878_, v___x_4884_);
v___x_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4883_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4886_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
else
{
lean_dec(v_a_4870_);
return v___x_4877_;
}
}
else
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; 
v___x_4896_ = l_Lean_Expr_appFn_x21(v_a_4870_);
lean_dec(v_a_4870_);
v___x_4897_ = l_Lean_Expr_appArg_x21(v___x_4896_);
lean_dec_ref(v___x_4896_);
v___x_4898_ = l_Lean_Meta_mkEqRefl(v___x_4897_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4898_) == 0)
{
lean_object* v_a_4899_; lean_object* v___x_4900_; 
v_a_4899_ = lean_ctor_get(v___x_4898_, 0);
lean_inc(v_a_4899_);
lean_dec_ref_known(v___x_4898_, 1);
v___x_4900_ = l_Lean_Expr_app___override(v_b_4849_, v_a_4899_);
v_a_4859_ = v___x_4900_;
goto v___jp_4858_;
}
else
{
lean_dec(v_i_4850_);
lean_dec_ref(v_b_4849_);
return v___x_4898_;
}
}
}
else
{
lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4901_ = l_Lean_Expr_appFn_x21(v_a_4870_);
lean_dec(v_a_4870_);
v___x_4902_ = l_Lean_Expr_appFn_x21(v___x_4901_);
lean_dec_ref(v___x_4901_);
v___x_4903_ = l_Lean_Expr_appArg_x21(v___x_4902_);
lean_dec_ref(v___x_4902_);
v___x_4904_ = l_Lean_Meta_mkHEqRefl(v___x_4903_, v___y_4851_, v___y_4852_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v_a_4905_; lean_object* v___x_4906_; 
v_a_4905_ = lean_ctor_get(v___x_4904_, 0);
lean_inc(v_a_4905_);
lean_dec_ref_known(v___x_4904_, 1);
v___x_4906_ = l_Lean_Expr_app___override(v_b_4849_, v_a_4905_);
v_a_4859_ = v___x_4906_;
goto v___jp_4858_;
}
else
{
lean_dec(v_i_4850_);
lean_dec_ref(v_b_4849_);
return v___x_4904_;
}
}
}
else
{
lean_dec(v_i_4850_);
lean_dec_ref(v_b_4849_);
return v___x_4869_;
}
}
else
{
lean_dec(v_i_4850_);
lean_dec_ref(v_b_4849_);
return v___x_4866_;
}
}
else
{
lean_dec(v_i_4850_);
lean_dec_ref(v_b_4849_);
return v___x_4864_;
}
}
v___jp_4858_:
{
lean_object* v___x_4860_; 
v___x_4860_ = lean_nat_add(v_i_4850_, v_step_4857_);
lean_dec(v_i_4850_);
v_b_4849_ = v_a_4859_;
v_i_4850_ = v___x_4860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4907_, lean_object* v_b_4908_, lean_object* v_i_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4907_, v_b_4908_, v_i_4909_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_);
lean_dec(v___y_4913_);
lean_dec_ref(v___y_4912_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec_ref(v_range_4907_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4916_, lean_object* v_b_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_){
_start:
{
lean_object* v___x_4923_; 
lean_inc(v___y_4921_);
lean_inc_ref(v___y_4920_);
lean_inc(v___y_4919_);
lean_inc_ref(v___y_4918_);
v___x_4923_ = lean_apply_6(v_k_4916_, v_b_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, lean_box(0));
return v___x_4923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4924_, lean_object* v_b_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_){
_start:
{
lean_object* v_res_4931_; 
v_res_4931_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4924_, v_b_4925_, v___y_4926_, v___y_4927_, v___y_4928_, v___y_4929_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
return v_res_4931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4932_, uint8_t v_bi_4933_, lean_object* v_type_4934_, lean_object* v_k_4935_, uint8_t v_kind_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_){
_start:
{
lean_object* v___f_4942_; lean_object* v___x_4943_; 
v___f_4942_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4942_, 0, v_k_4935_);
v___x_4943_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4932_, v_bi_4933_, v_type_4934_, v___f_4942_, v_kind_4936_, v___y_4937_, v___y_4938_, v___y_4939_, v___y_4940_);
if (lean_obj_tag(v___x_4943_) == 0)
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4951_; 
v_a_4944_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4946_ = v___x_4943_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4943_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4949_; 
if (v_isShared_4947_ == 0)
{
v___x_4949_ = v___x_4946_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4944_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
else
{
lean_object* v_a_4952_; lean_object* v___x_4954_; uint8_t v_isShared_4955_; uint8_t v_isSharedCheck_4959_; 
v_a_4952_ = lean_ctor_get(v___x_4943_, 0);
v_isSharedCheck_4959_ = !lean_is_exclusive(v___x_4943_);
if (v_isSharedCheck_4959_ == 0)
{
v___x_4954_ = v___x_4943_;
v_isShared_4955_ = v_isSharedCheck_4959_;
goto v_resetjp_4953_;
}
else
{
lean_inc(v_a_4952_);
lean_dec(v___x_4943_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_4960_, lean_object* v_bi_4961_, lean_object* v_type_4962_, lean_object* v_k_4963_, lean_object* v_kind_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_){
_start:
{
uint8_t v_bi_boxed_4970_; uint8_t v_kind_boxed_4971_; lean_object* v_res_4972_; 
v_bi_boxed_4970_ = lean_unbox(v_bi_4961_);
v_kind_boxed_4971_ = lean_unbox(v_kind_4964_);
v_res_4972_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4960_, v_bi_boxed_4970_, v_type_4962_, v_k_4963_, v_kind_boxed_4971_, v___y_4965_, v___y_4966_, v___y_4967_, v___y_4968_);
lean_dec(v___y_4968_);
lean_dec_ref(v___y_4967_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
return v_res_4972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_4973_, lean_object* v_type_4974_, lean_object* v_k_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_){
_start:
{
uint8_t v___x_4981_; uint8_t v___x_4982_; lean_object* v___x_4983_; 
v___x_4981_ = 0;
v___x_4982_ = 0;
v___x_4983_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4973_, v___x_4981_, v_type_4974_, v_k_4975_, v___x_4982_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_4984_, lean_object* v_type_4985_, lean_object* v_k_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_4984_, v_type_4985_, v_k_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
return v_res_4992_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; 
v___x_4999_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_5000_ = l_Lean_MessageData_ofFormat(v___x_4999_);
return v___x_5000_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__7(void){
_start:
{
lean_object* v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__6));
v___x_5005_ = l_Lean_MessageData_ofFormat(v___x_5004_);
return v___x_5005_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__9(void){
_start:
{
lean_object* v___x_5007_; lean_object* v___x_5008_; 
v___x_5007_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__8));
v___x_5008_ = l_Lean_stringToMessageData(v___x_5007_);
return v___x_5008_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_5010_; lean_object* v___x_5011_; 
v___x_5010_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_5011_ = l_Lean_stringToMessageData(v___x_5010_);
return v___x_5011_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__14(void){
_start:
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5014_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__13));
v___x_5015_ = lean_unsigned_to_nat(10u);
v___x_5016_ = lean_unsigned_to_nat(490u);
v___x_5017_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5018_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5019_ = l_mkPanicMessageWithDecl(v___x_5018_, v___x_5017_, v___x_5016_, v___x_5015_, v___x_5014_);
return v___x_5019_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; 
v___x_5021_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5022_ = l_Lean_stringToMessageData(v___x_5021_);
return v___x_5022_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__23(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__22));
v___x_5032_ = l_Lean_stringToMessageData(v___x_5031_);
return v___x_5032_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__24(void){
_start:
{
lean_object* v___x_5033_; lean_object* v___x_5034_; 
v___x_5033_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5034_ = l_Lean_MessageData_ofName(v___x_5033_);
return v___x_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5035_, lean_object* v_h_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_, lean_object* v_a_5039_, lean_object* v_a_5040_){
_start:
{
lean_object* v___x_5042_; 
lean_inc(v_a_5040_);
lean_inc_ref(v_a_5039_);
lean_inc(v_a_5038_);
lean_inc_ref(v_a_5037_);
lean_inc_ref(v_h_5036_);
v___x_5042_ = lean_infer_type(v_h_5036_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5044_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
lean_inc(v_a_5040_);
lean_inc_ref(v_a_5039_);
lean_inc(v_a_5038_);
lean_inc_ref(v_a_5037_);
v___x_5044_ = lean_whnf(v_a_5043_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5044_) == 0)
{
lean_object* v_a_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; uint8_t v___x_5048_; 
v_a_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc(v_a_5045_);
lean_dec_ref_known(v___x_5044_, 1);
v___x_5046_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5047_ = lean_unsigned_to_nat(3u);
v___x_5048_ = l_Lean_Expr_isAppOfArity(v_a_5045_, v___x_5046_, v___x_5047_);
if (v___x_5048_ == 0)
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
lean_dec_ref(v_target_5035_);
v___x_5049_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5050_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5051_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5036_, v_a_5045_);
v___x_5052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5050_);
lean_ctor_set(v___x_5052_, 1, v___x_5051_);
v___x_5053_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5049_, v___x_5052_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
return v___x_5053_;
}
else
{
lean_object* v___x_5054_; lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; 
v___x_5054_ = l_Lean_Expr_appFn_x21(v_a_5045_);
v___x_5055_ = l_Lean_Expr_appFn_x21(v___x_5054_);
v___x_5056_ = l_Lean_Expr_appArg_x21(v___x_5055_);
lean_dec_ref(v___x_5055_);
v___x_5057_ = l_Lean_Meta_whnfD(v___x_5056_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5057_) == 0)
{
lean_object* v_a_5058_; lean_object* v___y_5060_; lean_object* v___y_5061_; lean_object* v___y_5062_; lean_object* v___y_5063_; lean_object* v___x_5069_; 
v_a_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc(v_a_5058_);
lean_dec_ref_known(v___x_5057_, 1);
v___x_5069_ = l_Lean_Expr_getAppFn(v_a_5058_);
if (lean_obj_tag(v___x_5069_) == 4)
{
lean_object* v_declName_5070_; lean_object* v_us_5071_; lean_object* v___x_5072_; lean_object* v_env_5073_; uint8_t v___x_5074_; lean_object* v___x_5075_; 
v_declName_5070_ = lean_ctor_get(v___x_5069_, 0);
lean_inc(v_declName_5070_);
v_us_5071_ = lean_ctor_get(v___x_5069_, 1);
lean_inc(v_us_5071_);
lean_dec_ref_known(v___x_5069_, 2);
v___x_5072_ = lean_st_ref_get(v_a_5040_);
v_env_5073_ = lean_ctor_get(v___x_5072_, 0);
lean_inc_ref(v_env_5073_);
lean_dec(v___x_5072_);
v___x_5074_ = 0;
v___x_5075_ = l_Lean_Environment_find_x3f(v_env_5073_, v_declName_5070_, v___x_5074_);
if (lean_obj_tag(v___x_5075_) == 0)
{
lean_dec(v_us_5071_);
lean_dec_ref(v___x_5054_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___y_5060_ = v_a_5037_;
v___y_5061_ = v_a_5038_;
v___y_5062_ = v_a_5039_;
v___y_5063_ = v_a_5040_;
goto v___jp_5059_;
}
else
{
lean_object* v_val_5076_; 
v_val_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_val_5076_);
lean_dec_ref_known(v___x_5075_, 1);
if (lean_obj_tag(v_val_5076_) == 5)
{
lean_object* v_val_5077_; lean_object* v___x_5078_; 
v_val_5077_ = lean_ctor_get(v_val_5076_, 0);
lean_inc_ref(v_val_5077_);
lean_dec_ref_known(v_val_5076_, 1);
lean_inc_ref(v_target_5035_);
v___x_5078_ = l_Lean_Meta_getLevel(v_target_5035_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_object* v_a_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v_a_5079_ = lean_ctor_get(v___x_5078_, 0);
lean_inc(v_a_5079_);
lean_dec_ref_known(v___x_5078_, 1);
v___x_5080_ = l_Lean_Expr_appArg_x21(v___x_5054_);
lean_dec_ref(v___x_5054_);
lean_inc_ref(v___x_5080_);
v___x_5081_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5080_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_object* v_a_5082_; lean_object* v___x_5083_; lean_object* v___y_5085_; lean_object* v___y_5086_; lean_object* v___y_5087_; lean_object* v___y_5088_; 
v_a_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_a_5082_);
lean_dec_ref_known(v___x_5081_, 1);
v___x_5083_ = l_Lean_Expr_appArg_x21(v_a_5045_);
lean_dec(v_a_5045_);
if (lean_obj_tag(v_a_5082_) == 1)
{
lean_object* v_val_5097_; lean_object* v_fst_5098_; lean_object* v_snd_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5311_; 
v_val_5097_ = lean_ctor_get(v_a_5082_, 0);
lean_inc(v_val_5097_);
lean_dec_ref_known(v_a_5082_, 1);
v_fst_5098_ = lean_ctor_get(v_val_5097_, 0);
v_snd_5099_ = lean_ctor_get(v_val_5097_, 1);
v_isSharedCheck_5311_ = !lean_is_exclusive(v_val_5097_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5101_ = v_val_5097_;
v_isShared_5102_ = v_isSharedCheck_5311_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_snd_5099_);
lean_inc(v_fst_5098_);
lean_dec(v_val_5097_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5311_;
goto v_resetjp_5100_;
}
v_resetjp_5100_:
{
lean_object* v___x_5103_; 
lean_inc_ref(v___x_5083_);
v___x_5103_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5083_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v_a_5104_; 
v_a_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc(v_a_5104_);
lean_dec_ref_known(v___x_5103_, 1);
if (lean_obj_tag(v_a_5104_) == 1)
{
lean_object* v_val_5105_; lean_object* v_fst_5106_; lean_object* v_snd_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5302_; 
v_val_5105_ = lean_ctor_get(v_a_5104_, 0);
lean_inc(v_val_5105_);
lean_dec_ref_known(v_a_5104_, 1);
v_fst_5106_ = lean_ctor_get(v_val_5105_, 0);
v_snd_5107_ = lean_ctor_get(v_val_5105_, 1);
v_isSharedCheck_5302_ = !lean_is_exclusive(v_val_5105_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5109_ = v_val_5105_;
v_isShared_5110_ = v_isSharedCheck_5302_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_snd_5107_);
lean_inc(v_fst_5106_);
lean_dec(v_val_5105_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5302_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v_toConstantVal_5111_; lean_object* v_cidx_5112_; lean_object* v_numParams_5113_; lean_object* v_numFields_5114_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; lean_object* v_cidx_5205_; lean_object* v___x_5206_; lean_object* v___f_5207_; uint8_t v___x_5233_; 
v_toConstantVal_5111_ = lean_ctor_get(v_fst_5098_, 0);
lean_inc_ref(v_toConstantVal_5111_);
v_cidx_5112_ = lean_ctor_get(v_fst_5098_, 2);
lean_inc(v_cidx_5112_);
v_numParams_5113_ = lean_ctor_get(v_fst_5098_, 3);
lean_inc(v_numParams_5113_);
v_numFields_5114_ = lean_ctor_get(v_fst_5098_, 4);
lean_inc(v_numFields_5114_);
lean_dec(v_fst_5098_);
v_cidx_5205_ = lean_ctor_get(v_fst_5106_, 2);
lean_inc(v_cidx_5205_);
lean_dec(v_fst_5106_);
v___x_5206_ = lean_box(v___x_5048_);
v___f_5207_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5207_, 0, v___x_5206_);
v___x_5233_ = lean_nat_dec_eq(v_cidx_5112_, v_cidx_5205_);
lean_dec(v_cidx_5205_);
lean_dec(v_cidx_5112_);
if (v___x_5233_ == 0)
{
if (v___x_5048_ == 0)
{
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec_ref(v_val_5077_);
goto v___jp_5208_;
}
else
{
lean_object* v_toConstantVal_5234_; lean_object* v_name_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v_a_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v_a_5242_; uint8_t v___x_5260_; 
lean_dec_ref(v___f_5207_);
lean_dec(v_numFields_5114_);
lean_dec(v_numParams_5113_);
lean_dec_ref(v_toConstantVal_5111_);
lean_del_object(v___x_5109_);
lean_dec(v_snd_5107_);
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
v_toConstantVal_5234_ = lean_ctor_get(v_val_5077_, 0);
lean_inc_ref(v_toConstantVal_5234_);
lean_dec_ref(v_val_5077_);
v_name_5235_ = lean_ctor_get(v_toConstantVal_5234_, 0);
lean_inc(v_name_5235_);
lean_dec_ref(v_toConstantVal_5234_);
v___x_5236_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5237_ = l_Lean_Name_str___override(v_name_5235_, v___x_5236_);
lean_inc(v___x_5237_);
v___x_5238_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5237_, v___x_5048_, v_a_5040_);
v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_a_5239_);
lean_dec_ref(v___x_5238_);
v___x_5240_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5241_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5240_, v___x_5048_, v_a_5040_);
v_a_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc(v_a_5242_);
lean_dec_ref(v___x_5241_);
v___x_5260_ = lean_unbox(v_a_5239_);
lean_dec(v_a_5239_);
if (v___x_5260_ == 0)
{
lean_dec(v_a_5242_);
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
goto v___jp_5243_;
}
else
{
uint8_t v___x_5261_; 
v___x_5261_ = lean_unbox(v_a_5242_);
lean_dec(v_a_5242_);
if (v___x_5261_ == 0)
{
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
goto v___jp_5243_;
}
else
{
lean_object* v_dummy_5262_; lean_object* v_nargs_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v_dummy_5262_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5263_ = l_Lean_Expr_getAppNumArgs(v_a_5058_);
lean_inc(v_nargs_5263_);
v___x_5264_ = lean_mk_array(v_nargs_5263_, v_dummy_5262_);
v___x_5265_ = lean_unsigned_to_nat(1u);
v___x_5266_ = lean_nat_sub(v_nargs_5263_, v___x_5265_);
lean_dec(v_nargs_5263_);
lean_inc_n(v_a_5058_, 2);
v___x_5267_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5058_, v___x_5264_, v___x_5266_);
v___x_5268_ = l_Lean_Meta_getLevel(v_a_5058_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5268_) == 0)
{
lean_object* v_a_5269_; lean_object* v___x_5271_; uint8_t v_isShared_5272_; uint8_t v_isSharedCheck_5293_; 
v_a_5269_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5293_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5293_ == 0)
{
v___x_5271_ = v___x_5268_;
v_isShared_5272_ = v_isSharedCheck_5293_;
goto v_resetjp_5270_;
}
else
{
lean_inc(v_a_5269_);
lean_dec(v___x_5268_);
v___x_5271_ = lean_box(0);
v_isShared_5272_ = v_isSharedCheck_5293_;
goto v_resetjp_5270_;
}
v_resetjp_5270_:
{
lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5291_; 
v___x_5273_ = l_Lean_mkConst(v___x_5237_, v_us_5071_);
v___x_5274_ = l_Lean_mkAppN(v___x_5273_, v___x_5267_);
lean_dec_ref(v___x_5267_);
v___x_5275_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5276_ = lean_box(0);
v___x_5277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5277_, 0, v_a_5079_);
lean_ctor_set(v___x_5277_, 1, v___x_5276_);
v___x_5278_ = l_Lean_mkConst(v___x_5275_, v___x_5277_);
v___x_5279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5279_, 0, v_a_5269_);
lean_ctor_set(v___x_5279_, 1, v___x_5276_);
v___x_5280_ = l_Lean_mkConst(v___x_5240_, v___x_5279_);
v___x_5281_ = lean_unsigned_to_nat(5u);
v___x_5282_ = lean_mk_empty_array_with_capacity(v___x_5281_);
v___x_5283_ = lean_array_push(v___x_5282_, v_a_5058_);
v___x_5284_ = lean_array_push(v___x_5283_, v___x_5274_);
v___x_5285_ = lean_array_push(v___x_5284_, v___x_5080_);
v___x_5286_ = lean_array_push(v___x_5285_, v___x_5083_);
v___x_5287_ = lean_array_push(v___x_5286_, v_h_5036_);
v___x_5288_ = l_Lean_mkAppN(v___x_5280_, v___x_5287_);
lean_dec_ref(v___x_5287_);
v___x_5289_ = l_Lean_mkAppB(v___x_5278_, v_target_5035_, v___x_5288_);
if (v_isShared_5272_ == 0)
{
lean_ctor_set(v___x_5271_, 0, v___x_5289_);
v___x_5291_ = v___x_5271_;
goto v_reusejp_5290_;
}
else
{
lean_object* v_reuseFailAlloc_5292_; 
v_reuseFailAlloc_5292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5292_, 0, v___x_5289_);
v___x_5291_ = v_reuseFailAlloc_5292_;
goto v_reusejp_5290_;
}
v_reusejp_5290_:
{
return v___x_5291_;
}
}
}
else
{
lean_object* v_a_5294_; lean_object* v___x_5296_; uint8_t v_isShared_5297_; uint8_t v_isSharedCheck_5301_; 
lean_dec_ref(v___x_5267_);
lean_dec(v___x_5237_);
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5294_ = lean_ctor_get(v___x_5268_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___x_5268_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5296_ = v___x_5268_;
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
else
{
lean_inc(v_a_5294_);
lean_dec(v___x_5268_);
v___x_5296_ = lean_box(0);
v_isShared_5297_ = v_isSharedCheck_5301_;
goto v_resetjp_5295_;
}
v_resetjp_5295_:
{
lean_object* v___x_5299_; 
if (v_isShared_5297_ == 0)
{
v___x_5299_ = v___x_5296_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
}
}
v___jp_5243_:
{
lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v_a_5252_; lean_object* v___x_5254_; uint8_t v_isShared_5255_; uint8_t v_isSharedCheck_5259_; 
v___x_5244_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5245_ = l_Lean_MessageData_ofName(v___x_5237_);
v___x_5246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5246_, 0, v___x_5244_);
lean_ctor_set(v___x_5246_, 1, v___x_5245_);
v___x_5247_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__23, &l_Lean_Meta_mkNoConfusion___closed__23_once, _init_l_Lean_Meta_mkNoConfusion___closed__23);
v___x_5248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5246_);
lean_ctor_set(v___x_5248_, 1, v___x_5247_);
v___x_5249_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__24, &l_Lean_Meta_mkNoConfusion___closed__24_once, _init_l_Lean_Meta_mkNoConfusion___closed__24);
v___x_5250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5248_);
lean_ctor_set(v___x_5250_, 1, v___x_5249_);
v___x_5251_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5250_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
v_a_5252_ = lean_ctor_get(v___x_5251_, 0);
v_isSharedCheck_5259_ = !lean_is_exclusive(v___x_5251_);
if (v_isSharedCheck_5259_ == 0)
{
v___x_5254_ = v___x_5251_;
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
else
{
lean_inc(v_a_5252_);
lean_dec(v___x_5251_);
v___x_5254_ = lean_box(0);
v_isShared_5255_ = v_isSharedCheck_5259_;
goto v_resetjp_5253_;
}
v_resetjp_5253_:
{
lean_object* v___x_5257_; 
if (v_isShared_5255_ == 0)
{
v___x_5257_ = v___x_5254_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5258_; 
v_reuseFailAlloc_5258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5258_, 0, v_a_5252_);
v___x_5257_ = v_reuseFailAlloc_5258_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
return v___x_5257_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec_ref(v_val_5077_);
goto v___jp_5208_;
}
v___jp_5115_:
{
lean_object* v___x_5122_; 
lean_inc(v___y_5116_);
v___x_5122_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5116_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5122_) == 0)
{
lean_object* v_a_5123_; lean_object* v_nargs_5124_; lean_object* v_type_5125_; lean_object* v___x_5127_; uint8_t v_isShared_5128_; uint8_t v_isSharedCheck_5194_; 
v_a_5123_ = lean_ctor_get(v___x_5122_, 0);
lean_inc(v_a_5123_);
lean_dec_ref_known(v___x_5122_, 1);
v_nargs_5124_ = l_Lean_Expr_getAppNumArgs(v_a_5058_);
v_type_5125_ = lean_ctor_get(v_a_5123_, 2);
v_isSharedCheck_5194_ = !lean_is_exclusive(v_a_5123_);
if (v_isSharedCheck_5194_ == 0)
{
lean_object* v_unused_5195_; lean_object* v_unused_5196_; 
v_unused_5195_ = lean_ctor_get(v_a_5123_, 1);
lean_dec(v_unused_5195_);
v_unused_5196_ = lean_ctor_get(v_a_5123_, 0);
lean_dec(v_unused_5196_);
v___x_5127_ = v_a_5123_;
v_isShared_5128_ = v_isSharedCheck_5194_;
goto v_resetjp_5126_;
}
else
{
lean_inc(v_type_5125_);
lean_dec(v_a_5123_);
v___x_5127_ = lean_box(0);
v_isShared_5128_ = v_isSharedCheck_5194_;
goto v_resetjp_5126_;
}
v_resetjp_5126_:
{
lean_object* v_dummy_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v_start_5135_; lean_object* v_stop_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; uint8_t v___x_5150_; 
v_dummy_5129_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
lean_inc(v_nargs_5124_);
v___x_5130_ = lean_mk_array(v_nargs_5124_, v_dummy_5129_);
v___x_5131_ = lean_unsigned_to_nat(1u);
v___x_5132_ = lean_nat_sub(v_nargs_5124_, v___x_5131_);
lean_dec(v_nargs_5124_);
v___x_5133_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5058_, v___x_5130_, v___x_5132_);
lean_inc_n(v_numParams_5113_, 2);
lean_inc(v___y_5117_);
v___x_5134_ = l_Array_toSubarray___redArg(v___x_5133_, v___y_5117_, v_numParams_5113_);
v_start_5135_ = lean_ctor_get(v___x_5134_, 1);
lean_inc(v_start_5135_);
v_stop_5136_ = lean_ctor_get(v___x_5134_, 2);
lean_inc(v_stop_5136_);
v___x_5137_ = lean_array_get_size(v_snd_5099_);
v___x_5138_ = l_Array_toSubarray___redArg(v_snd_5099_, v_numParams_5113_, v___x_5137_);
v___x_5139_ = lean_array_get_size(v_snd_5107_);
v___x_5140_ = l_Subarray_copy___redArg(v___x_5138_);
v___x_5141_ = l_Array_toSubarray___redArg(v_snd_5107_, v_numParams_5113_, v___x_5139_);
v___x_5142_ = l_Subarray_copy___redArg(v___x_5141_);
v___x_5143_ = l_Lean_Expr_getNumHeadForalls(v_type_5125_);
lean_dec_ref(v_type_5125_);
v___x_5144_ = lean_nat_sub(v_stop_5136_, v_start_5135_);
lean_dec(v_start_5135_);
lean_dec(v_stop_5136_);
v___x_5145_ = lean_array_get_size(v___x_5140_);
v___x_5146_ = lean_nat_add(v___x_5144_, v___x_5145_);
lean_dec(v___x_5144_);
v___x_5147_ = lean_array_get_size(v___x_5142_);
v___x_5148_ = lean_nat_add(v___x_5146_, v___x_5147_);
lean_dec(v___x_5146_);
v___x_5149_ = lean_nat_add(v___x_5148_, v___x_5047_);
lean_dec(v___x_5148_);
v___x_5150_ = lean_nat_dec_le(v___x_5149_, v___x_5143_);
if (v___x_5150_ == 0)
{
lean_object* v___x_5151_; lean_object* v___x_5152_; 
lean_dec(v___x_5149_);
lean_dec(v___x_5143_);
lean_dec_ref(v___x_5142_);
lean_dec_ref(v___x_5140_);
lean_dec_ref(v___x_5134_);
lean_del_object(v___x_5127_);
lean_dec(v___y_5117_);
lean_dec(v___y_5116_);
lean_del_object(v___x_5109_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___x_5151_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__14, &l_Lean_Meta_mkNoConfusion___closed__14_once, _init_l_Lean_Meta_mkNoConfusion___closed__14);
v___x_5152_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5151_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
return v___x_5152_;
}
else
{
lean_object* v___x_5154_; 
if (v_isShared_5110_ == 0)
{
lean_ctor_set_tag(v___x_5109_, 1);
lean_ctor_set(v___x_5109_, 1, v_us_5071_);
lean_ctor_set(v___x_5109_, 0, v_a_5079_);
v___x_5154_ = v___x_5109_;
goto v_reusejp_5153_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5079_);
lean_ctor_set(v_reuseFailAlloc_5193_, 1, v_us_5071_);
v___x_5154_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5153_;
}
v_reusejp_5153_:
{
lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; lean_object* v___x_5165_; 
v___x_5155_ = l_Lean_mkConst(v___y_5116_, v___x_5154_);
v___x_5156_ = l_Subarray_copy___redArg(v___x_5134_);
v___x_5157_ = l_Lean_mkAppN(v___x_5155_, v___x_5156_);
lean_dec_ref(v___x_5156_);
v___x_5158_ = lean_mk_empty_array_with_capacity(v___x_5131_);
v___x_5159_ = lean_array_push(v___x_5158_, v_target_5035_);
v___x_5160_ = l_Array_append___redArg(v___x_5159_, v___x_5140_);
lean_dec_ref(v___x_5140_);
v___x_5161_ = l_Array_append___redArg(v___x_5160_, v___x_5142_);
lean_dec_ref(v___x_5142_);
v___x_5162_ = l_Lean_mkAppN(v___x_5157_, v___x_5161_);
lean_dec_ref(v___x_5161_);
v___x_5163_ = lean_nat_sub(v___x_5143_, v___x_5149_);
lean_dec(v___x_5149_);
lean_dec(v___x_5143_);
lean_inc(v___y_5117_);
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 2, v___x_5131_);
lean_ctor_set(v___x_5127_, 1, v___x_5163_);
lean_ctor_set(v___x_5127_, 0, v___y_5117_);
v___x_5165_ = v___x_5127_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___y_5117_);
lean_ctor_set(v_reuseFailAlloc_5192_, 1, v___x_5163_);
lean_ctor_set(v_reuseFailAlloc_5192_, 2, v___x_5131_);
v___x_5165_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
lean_object* v___x_5166_; 
v___x_5166_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5165_, v___x_5162_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
lean_dec_ref(v___x_5165_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5168_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc_n(v_a_5167_, 2);
lean_dec_ref_known(v___x_5166_, 1);
lean_inc(v___y_5121_);
lean_inc_ref(v___y_5120_);
lean_inc(v___y_5119_);
lean_inc_ref(v___y_5118_);
v___x_5168_ = lean_infer_type(v_a_5167_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v___x_5170_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
lean_inc(v_a_5169_);
lean_dec_ref_known(v___x_5168_, 1);
v___x_5170_ = l_Lean_Meta_whnfForall(v_a_5169_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5170_) == 0)
{
lean_object* v_a_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5191_; 
v_a_5171_ = lean_ctor_get(v___x_5170_, 0);
v_isSharedCheck_5191_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5191_ == 0)
{
v___x_5173_ = v___x_5170_;
v_isShared_5174_ = v_isSharedCheck_5191_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_a_5171_);
lean_dec(v___x_5170_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5191_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
lean_object* v___x_5175_; uint8_t v___x_5176_; 
v___x_5175_ = l_Lean_Expr_bindingDomain_x21(v_a_5171_);
lean_dec(v_a_5171_);
v___x_5176_ = l_Lean_Expr_isHEq(v___x_5175_);
lean_dec_ref(v___x_5175_);
if (v___x_5176_ == 0)
{
lean_object* v___x_5177_; lean_object* v___x_5179_; 
v___x_5177_ = l_Lean_Expr_app___override(v_a_5167_, v_h_5036_);
if (v_isShared_5174_ == 0)
{
lean_ctor_set(v___x_5173_, 0, v___x_5177_);
v___x_5179_ = v___x_5173_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5180_; 
v_reuseFailAlloc_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5180_, 0, v___x_5177_);
v___x_5179_ = v_reuseFailAlloc_5180_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
return v___x_5179_;
}
}
else
{
lean_object* v___x_5181_; 
lean_del_object(v___x_5173_);
v___x_5181_ = l_Lean_Meta_mkHEqOfEq(v_h_5036_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5181_) == 0)
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5190_; 
v_a_5182_ = lean_ctor_get(v___x_5181_, 0);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5181_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5184_ = v___x_5181_;
v_isShared_5185_ = v_isSharedCheck_5190_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5181_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5190_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5186_; lean_object* v___x_5188_; 
v___x_5186_ = l_Lean_Expr_app___override(v_a_5167_, v_a_5182_);
if (v_isShared_5185_ == 0)
{
lean_ctor_set(v___x_5184_, 0, v___x_5186_);
v___x_5188_ = v___x_5184_;
goto v_reusejp_5187_;
}
else
{
lean_object* v_reuseFailAlloc_5189_; 
v_reuseFailAlloc_5189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5189_, 0, v___x_5186_);
v___x_5188_ = v_reuseFailAlloc_5189_;
goto v_reusejp_5187_;
}
v_reusejp_5187_:
{
return v___x_5188_;
}
}
}
else
{
lean_dec(v_a_5167_);
return v___x_5181_;
}
}
}
}
else
{
lean_dec(v_a_5167_);
lean_dec_ref(v_h_5036_);
return v___x_5170_;
}
}
else
{
lean_dec(v_a_5167_);
lean_dec_ref(v_h_5036_);
return v___x_5168_;
}
}
else
{
lean_dec_ref(v_h_5036_);
return v___x_5166_;
}
}
}
}
}
}
else
{
lean_object* v_a_5197_; lean_object* v___x_5199_; uint8_t v_isShared_5200_; uint8_t v_isSharedCheck_5204_; 
lean_dec(v___y_5117_);
lean_dec(v___y_5116_);
lean_dec(v_numParams_5113_);
lean_del_object(v___x_5109_);
lean_dec(v_snd_5107_);
lean_dec(v_snd_5099_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5197_ = lean_ctor_get(v___x_5122_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5199_ = v___x_5122_;
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
else
{
lean_inc(v_a_5197_);
lean_dec(v___x_5122_);
v___x_5199_ = lean_box(0);
v_isShared_5200_ = v_isSharedCheck_5204_;
goto v_resetjp_5198_;
}
v_resetjp_5198_:
{
lean_object* v___x_5202_; 
if (v_isShared_5200_ == 0)
{
v___x_5202_ = v___x_5199_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_a_5197_);
v___x_5202_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
return v___x_5202_;
}
}
}
}
v___jp_5208_:
{
lean_object* v___x_5209_; uint8_t v___x_5210_; 
v___x_5209_ = lean_unsigned_to_nat(0u);
v___x_5210_ = lean_nat_dec_eq(v_numFields_5114_, v___x_5209_);
lean_dec(v_numFields_5114_);
if (v___x_5210_ == 0)
{
lean_object* v_name_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v_a_5215_; uint8_t v___x_5216_; 
lean_dec_ref(v___f_5207_);
v_name_5211_ = lean_ctor_get(v_toConstantVal_5111_, 0);
lean_inc(v_name_5211_);
lean_dec_ref(v_toConstantVal_5111_);
v___x_5212_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5213_ = l_Lean_Name_str___override(v_name_5211_, v___x_5212_);
lean_inc(v___x_5213_);
v___x_5214_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5213_, v___x_5048_, v_a_5040_);
v_a_5215_ = lean_ctor_get(v___x_5214_, 0);
lean_inc(v_a_5215_);
lean_dec_ref(v___x_5214_);
v___x_5216_ = lean_unbox(v_a_5215_);
lean_dec(v_a_5215_);
if (v___x_5216_ == 0)
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5220_; 
lean_dec(v_numParams_5113_);
lean_del_object(v___x_5109_);
lean_dec(v_snd_5107_);
lean_dec(v_snd_5099_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___x_5217_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5218_ = l_Lean_MessageData_ofName(v___x_5213_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set_tag(v___x_5101_, 7);
lean_ctor_set(v___x_5101_, 1, v___x_5218_);
lean_ctor_set(v___x_5101_, 0, v___x_5217_);
v___x_5220_ = v___x_5101_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5230_; 
v_reuseFailAlloc_5230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5230_, 0, v___x_5217_);
lean_ctor_set(v_reuseFailAlloc_5230_, 1, v___x_5218_);
v___x_5220_ = v_reuseFailAlloc_5230_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5221_; lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
v___x_5221_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5220_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5221_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5221_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5221_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
else
{
lean_del_object(v___x_5101_);
v___y_5116_ = v___x_5213_;
v___y_5117_ = v___x_5209_;
v___y_5118_ = v_a_5037_;
v___y_5119_ = v_a_5038_;
v___y_5120_ = v_a_5039_;
v___y_5121_ = v_a_5040_;
goto v___jp_5115_;
}
}
else
{
lean_object* v___x_5231_; lean_object* v___x_5232_; 
lean_dec(v_numParams_5113_);
lean_dec_ref(v_toConstantVal_5111_);
lean_del_object(v___x_5109_);
lean_dec(v_snd_5107_);
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
v___x_5231_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5232_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5231_, v_target_5035_, v___f_5207_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
return v___x_5232_;
}
}
}
}
else
{
lean_dec(v_a_5104_);
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_dec(v_a_5079_);
lean_dec_ref(v_val_5077_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___y_5085_ = v_a_5037_;
v___y_5086_ = v_a_5038_;
v___y_5087_ = v_a_5039_;
v___y_5088_ = v_a_5040_;
goto v___jp_5084_;
}
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
lean_dec(v_fst_5098_);
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_val_5077_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5303_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___x_5103_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5103_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
lean_object* v___x_5308_; 
if (v_isShared_5306_ == 0)
{
v___x_5308_ = v___x_5305_;
goto v_reusejp_5307_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5303_);
v___x_5308_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5307_;
}
v_reusejp_5307_:
{
return v___x_5308_;
}
}
}
}
}
else
{
lean_dec(v_a_5082_);
lean_dec(v_a_5079_);
lean_dec_ref(v_val_5077_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___y_5085_ = v_a_5037_;
v___y_5086_ = v_a_5038_;
v___y_5087_ = v_a_5039_;
v___y_5088_ = v_a_5040_;
goto v___jp_5084_;
}
v___jp_5084_:
{
lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5089_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__9, &l_Lean_Meta_mkNoConfusion___closed__9_once, _init_l_Lean_Meta_mkNoConfusion___closed__9);
v___x_5090_ = l_Lean_MessageData_ofExpr(v___x_5080_);
v___x_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5089_);
lean_ctor_set(v___x_5091_, 1, v___x_5090_);
v___x_5092_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5091_);
lean_ctor_set(v___x_5093_, 1, v___x_5092_);
v___x_5094_ = l_Lean_MessageData_ofExpr(v___x_5083_);
v___x_5095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5095_, 0, v___x_5093_);
lean_ctor_set(v___x_5095_, 1, v___x_5094_);
v___x_5096_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5095_, v___y_5085_, v___y_5086_, v___y_5087_, v___y_5088_);
return v___x_5096_;
}
}
else
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_val_5077_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5312_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5081_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5081_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v___x_5317_; 
if (v_isShared_5315_ == 0)
{
v___x_5317_ = v___x_5314_;
goto v_reusejp_5316_;
}
else
{
lean_object* v_reuseFailAlloc_5318_; 
v_reuseFailAlloc_5318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5318_, 0, v_a_5312_);
v___x_5317_ = v_reuseFailAlloc_5318_;
goto v_reusejp_5316_;
}
v_reusejp_5316_:
{
return v___x_5317_;
}
}
}
}
else
{
lean_object* v_a_5320_; lean_object* v___x_5322_; uint8_t v_isShared_5323_; uint8_t v_isSharedCheck_5327_; 
lean_dec_ref(v_val_5077_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v___x_5054_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5320_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5078_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5078_);
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
else
{
lean_dec(v_val_5076_);
lean_dec(v_us_5071_);
lean_dec_ref(v___x_5054_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___y_5060_ = v_a_5037_;
v___y_5061_ = v_a_5038_;
v___y_5062_ = v_a_5039_;
v___y_5063_ = v_a_5040_;
goto v___jp_5059_;
}
}
}
else
{
lean_dec_ref(v___x_5069_);
lean_dec_ref(v___x_5054_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___y_5060_ = v_a_5037_;
v___y_5061_ = v_a_5038_;
v___y_5062_ = v_a_5039_;
v___y_5063_ = v_a_5040_;
goto v___jp_5059_;
}
v___jp_5059_:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5064_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5065_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__7, &l_Lean_Meta_mkNoConfusion___closed__7_once, _init_l_Lean_Meta_mkNoConfusion___closed__7);
v___x_5066_ = l_Lean_indentExpr(v_a_5058_);
v___x_5067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5067_, 0, v___x_5065_);
lean_ctor_set(v___x_5067_, 1, v___x_5066_);
v___x_5068_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5064_, v___x_5067_, v___y_5060_, v___y_5061_, v___y_5062_, v___y_5063_);
return v___x_5068_;
}
}
else
{
lean_dec_ref(v___x_5054_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
return v___x_5057_;
}
}
}
else
{
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
return v___x_5044_;
}
}
else
{
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
return v___x_5042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5328_, lean_object* v_h_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_){
_start:
{
lean_object* v_res_5335_; 
v_res_5335_ = l_Lean_Meta_mkNoConfusion(v_target_5328_, v_h_5329_, v_a_5330_, v_a_5331_, v_a_5332_, v_a_5333_);
lean_dec(v_a_5333_);
lean_dec_ref(v_a_5332_);
lean_dec(v_a_5331_);
lean_dec_ref(v_a_5330_);
return v_res_5335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5336_, lean_object* v_b_5337_, lean_object* v_i_5338_, lean_object* v_hs_5339_, lean_object* v_hl_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_){
_start:
{
lean_object* v___x_5346_; 
v___x_5346_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5336_, v_b_5337_, v_i_5338_, v___y_5341_, v___y_5342_, v___y_5343_, v___y_5344_);
return v___x_5346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5347_, lean_object* v_b_5348_, lean_object* v_i_5349_, lean_object* v_hs_5350_, lean_object* v_hl_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_){
_start:
{
lean_object* v_res_5357_; 
v_res_5357_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5347_, v_b_5348_, v_i_5349_, v_hs_5350_, v_hl_5351_, v___y_5352_, v___y_5353_, v___y_5354_, v___y_5355_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec(v___y_5353_);
lean_dec_ref(v___y_5352_);
lean_dec_ref(v_range_5347_);
return v_res_5357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5358_, lean_object* v_name_5359_, uint8_t v_bi_5360_, lean_object* v_type_5361_, lean_object* v_k_5362_, uint8_t v_kind_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_){
_start:
{
lean_object* v___x_5369_; 
v___x_5369_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5359_, v_bi_5360_, v_type_5361_, v_k_5362_, v_kind_5363_, v___y_5364_, v___y_5365_, v___y_5366_, v___y_5367_);
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5370_, lean_object* v_name_5371_, lean_object* v_bi_5372_, lean_object* v_type_5373_, lean_object* v_k_5374_, lean_object* v_kind_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_){
_start:
{
uint8_t v_bi_boxed_5381_; uint8_t v_kind_boxed_5382_; lean_object* v_res_5383_; 
v_bi_boxed_5381_ = lean_unbox(v_bi_5372_);
v_kind_boxed_5382_ = lean_unbox(v_kind_5375_);
v_res_5383_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5370_, v_name_5371_, v_bi_boxed_5381_, v_type_5373_, v_k_5374_, v_kind_boxed_5382_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
lean_dec(v___y_5377_);
lean_dec_ref(v___y_5376_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5384_, lean_object* v_name_5385_, lean_object* v_type_5386_, lean_object* v_k_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_){
_start:
{
lean_object* v___x_5393_; 
v___x_5393_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5385_, v_type_5386_, v_k_5387_, v___y_5388_, v___y_5389_, v___y_5390_, v___y_5391_);
return v___x_5393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5394_, lean_object* v_name_5395_, lean_object* v_type_5396_, lean_object* v_k_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_){
_start:
{
lean_object* v_res_5403_; 
v_res_5403_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5394_, v_name_5395_, v_type_5396_, v_k_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
lean_dec(v___y_5399_);
lean_dec_ref(v___y_5398_);
return v_res_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5409_, lean_object* v_e_5410_, lean_object* v_a_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_){
_start:
{
lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; 
v___x_5416_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5417_, 0, v_monad_5409_);
v___x_5418_ = lean_box(0);
v___x_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5419_, 0, v_e_5410_);
v___x_5420_ = lean_unsigned_to_nat(4u);
v___x_5421_ = lean_mk_empty_array_with_capacity(v___x_5420_);
v___x_5422_ = lean_array_push(v___x_5421_, v___x_5417_);
v___x_5423_ = lean_array_push(v___x_5422_, v___x_5418_);
v___x_5424_ = lean_array_push(v___x_5423_, v___x_5418_);
v___x_5425_ = lean_array_push(v___x_5424_, v___x_5419_);
v___x_5426_ = l_Lean_Meta_mkAppOptM(v___x_5416_, v___x_5425_, v_a_5411_, v_a_5412_, v_a_5413_, v_a_5414_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5427_, lean_object* v_e_5428_, lean_object* v_a_5429_, lean_object* v_a_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_Meta_mkPure(v_monad_5427_, v_e_5428_, v_a_5429_, v_a_5430_, v_a_5431_, v_a_5432_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
lean_dec(v_a_5430_);
lean_dec_ref(v_a_5429_);
return v_res_5434_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5444_; lean_object* v___x_5445_; 
v___x_5444_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5445_ = l_Lean_MessageData_ofFormat(v___x_5444_);
return v___x_5445_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5449_; lean_object* v___x_5450_; 
v___x_5449_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5450_ = l_Lean_MessageData_ofFormat(v___x_5449_);
return v___x_5450_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5454_; lean_object* v___x_5455_; 
v___x_5454_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5455_ = l_Lean_MessageData_ofFormat(v___x_5454_);
return v___x_5455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5456_, lean_object* v_fieldName_5457_, lean_object* v_a_5458_, lean_object* v_a_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_){
_start:
{
lean_object* v___x_5463_; 
lean_inc(v_a_5461_);
lean_inc_ref(v_a_5460_);
lean_inc(v_a_5459_);
lean_inc_ref(v_a_5458_);
lean_inc_ref(v_s_5456_);
v___x_5463_ = lean_infer_type(v_s_5456_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_);
if (lean_obj_tag(v___x_5463_) == 0)
{
lean_object* v_a_5464_; lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5560_; 
v_a_5464_ = lean_ctor_get(v___x_5463_, 0);
v_isSharedCheck_5560_ = !lean_is_exclusive(v___x_5463_);
if (v_isSharedCheck_5560_ == 0)
{
v___x_5466_ = v___x_5463_;
v_isShared_5467_ = v_isSharedCheck_5560_;
goto v_resetjp_5465_;
}
else
{
lean_inc(v_a_5464_);
lean_dec(v___x_5463_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5560_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v___x_5468_; 
lean_inc(v_a_5461_);
lean_inc_ref(v_a_5460_);
lean_inc(v_a_5459_);
lean_inc_ref(v_a_5458_);
v___x_5468_ = lean_whnf(v_a_5464_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_);
if (lean_obj_tag(v___x_5468_) == 0)
{
lean_object* v_a_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5559_; 
v_a_5469_ = lean_ctor_get(v___x_5468_, 0);
v_isSharedCheck_5559_ = !lean_is_exclusive(v___x_5468_);
if (v_isSharedCheck_5559_ == 0)
{
v___x_5471_ = v___x_5468_;
v_isShared_5472_ = v_isSharedCheck_5559_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_a_5469_);
lean_dec(v___x_5468_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5559_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___y_5474_; lean_object* v___y_5475_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___x_5492_; 
v___x_5492_ = l_Lean_Expr_getAppFn(v_a_5469_);
if (lean_obj_tag(v___x_5492_) == 4)
{
lean_object* v_declName_5493_; lean_object* v_us_5494_; lean_object* v___x_5495_; lean_object* v_env_5496_; lean_object* v___y_5498_; lean_object* v___y_5499_; lean_object* v___y_5500_; lean_object* v___y_5501_; uint8_t v___x_5540_; 
v_declName_5493_ = lean_ctor_get(v___x_5492_, 0);
lean_inc_n(v_declName_5493_, 2);
v_us_5494_ = lean_ctor_get(v___x_5492_, 1);
lean_inc(v_us_5494_);
lean_dec_ref_known(v___x_5492_, 2);
v___x_5495_ = lean_st_ref_get(v_a_5461_);
v_env_5496_ = lean_ctor_get(v___x_5495_, 0);
lean_inc_ref_n(v_env_5496_, 2);
lean_dec(v___x_5495_);
v___x_5540_ = l_Lean_isStructure(v_env_5496_, v_declName_5493_);
if (v___x_5540_ == 0)
{
lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; 
v___x_5541_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5542_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5469_);
lean_inc_ref(v_s_5456_);
v___x_5543_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5456_, v_a_5469_);
v___x_5544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5542_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
v___x_5545_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5541_, v___x_5544_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_);
if (lean_obj_tag(v___x_5545_) == 0)
{
lean_dec_ref_known(v___x_5545_, 1);
v___y_5498_ = v_a_5458_;
v___y_5499_ = v_a_5459_;
v___y_5500_ = v_a_5460_;
v___y_5501_ = v_a_5461_;
goto v___jp_5497_;
}
else
{
lean_object* v_a_5546_; lean_object* v___x_5548_; uint8_t v_isShared_5549_; uint8_t v_isSharedCheck_5553_; 
lean_dec_ref(v_env_5496_);
lean_dec(v_us_5494_);
lean_dec(v_declName_5493_);
lean_del_object(v___x_5471_);
lean_dec(v_a_5469_);
lean_del_object(v___x_5466_);
lean_dec(v_fieldName_5457_);
lean_dec_ref(v_s_5456_);
v_a_5546_ = lean_ctor_get(v___x_5545_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5545_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5548_ = v___x_5545_;
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
else
{
lean_inc(v_a_5546_);
lean_dec(v___x_5545_);
v___x_5548_ = lean_box(0);
v_isShared_5549_ = v_isSharedCheck_5553_;
goto v_resetjp_5547_;
}
v_resetjp_5547_:
{
lean_object* v___x_5551_; 
if (v_isShared_5549_ == 0)
{
v___x_5551_ = v___x_5548_;
goto v_reusejp_5550_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_a_5546_);
v___x_5551_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5550_;
}
v_reusejp_5550_:
{
return v___x_5551_;
}
}
}
}
else
{
v___y_5498_ = v_a_5458_;
v___y_5499_ = v_a_5459_;
v___y_5500_ = v_a_5460_;
v___y_5501_ = v_a_5461_;
goto v___jp_5497_;
}
v___jp_5497_:
{
lean_object* v___x_5502_; 
lean_inc(v_fieldName_5457_);
lean_inc(v_declName_5493_);
lean_inc_ref(v_env_5496_);
v___x_5502_ = l_Lean_getProjFnForField_x3f(v_env_5496_, v_declName_5493_, v_fieldName_5457_);
if (lean_obj_tag(v___x_5502_) == 0)
{
lean_object* v___x_5503_; lean_object* v___x_5504_; size_t v_sz_5505_; size_t v___x_5506_; lean_object* v___x_5507_; 
lean_dec(v_us_5494_);
lean_del_object(v___x_5471_);
lean_inc(v_declName_5493_);
lean_inc_ref(v_env_5496_);
v___x_5503_ = l_Lean_getStructureFields(v_env_5496_, v_declName_5493_);
v___x_5504_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5505_ = lean_array_size(v___x_5503_);
v___x_5506_ = ((size_t)0ULL);
lean_inc(v_fieldName_5457_);
lean_inc_ref(v_s_5456_);
v___x_5507_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5496_, v_declName_5493_, v_s_5456_, v_fieldName_5457_, v___x_5503_, v_sz_5505_, v___x_5506_, v___x_5504_, v___y_5498_, v___y_5499_, v___y_5500_, v___y_5501_);
lean_dec_ref(v___x_5503_);
if (lean_obj_tag(v___x_5507_) == 0)
{
lean_object* v_a_5508_; lean_object* v___x_5510_; uint8_t v_isShared_5511_; uint8_t v_isSharedCheck_5518_; 
v_a_5508_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5518_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5518_ == 0)
{
v___x_5510_ = v___x_5507_;
v_isShared_5511_ = v_isSharedCheck_5518_;
goto v_resetjp_5509_;
}
else
{
lean_inc(v_a_5508_);
lean_dec(v___x_5507_);
v___x_5510_ = lean_box(0);
v_isShared_5511_ = v_isSharedCheck_5518_;
goto v_resetjp_5509_;
}
v_resetjp_5509_:
{
lean_object* v_fst_5512_; 
v_fst_5512_ = lean_ctor_get(v_a_5508_, 0);
lean_inc(v_fst_5512_);
lean_dec(v_a_5508_);
if (lean_obj_tag(v_fst_5512_) == 0)
{
lean_del_object(v___x_5510_);
v___y_5474_ = v___y_5498_;
v___y_5475_ = v___y_5499_;
v___y_5476_ = v___y_5501_;
v___y_5477_ = v___y_5500_;
goto v___jp_5473_;
}
else
{
lean_object* v_val_5513_; 
v_val_5513_ = lean_ctor_get(v_fst_5512_, 0);
lean_inc(v_val_5513_);
lean_dec_ref_known(v_fst_5512_, 1);
if (lean_obj_tag(v_val_5513_) == 0)
{
lean_del_object(v___x_5510_);
v___y_5474_ = v___y_5498_;
v___y_5475_ = v___y_5499_;
v___y_5476_ = v___y_5501_;
v___y_5477_ = v___y_5500_;
goto v___jp_5473_;
}
else
{
lean_object* v_val_5514_; lean_object* v___x_5516_; 
lean_dec(v_a_5469_);
lean_del_object(v___x_5466_);
lean_dec(v_fieldName_5457_);
lean_dec_ref(v_s_5456_);
v_val_5514_ = lean_ctor_get(v_val_5513_, 0);
lean_inc(v_val_5514_);
lean_dec_ref_known(v_val_5513_, 1);
if (v_isShared_5511_ == 0)
{
lean_ctor_set(v___x_5510_, 0, v_val_5514_);
v___x_5516_ = v___x_5510_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5517_; 
v_reuseFailAlloc_5517_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5517_, 0, v_val_5514_);
v___x_5516_ = v_reuseFailAlloc_5517_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
return v___x_5516_;
}
}
}
}
}
else
{
lean_object* v_a_5519_; lean_object* v___x_5521_; uint8_t v_isShared_5522_; uint8_t v_isSharedCheck_5526_; 
lean_dec(v_a_5469_);
lean_del_object(v___x_5466_);
lean_dec(v_fieldName_5457_);
lean_dec_ref(v_s_5456_);
v_a_5519_ = lean_ctor_get(v___x_5507_, 0);
v_isSharedCheck_5526_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5526_ == 0)
{
v___x_5521_ = v___x_5507_;
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
else
{
lean_inc(v_a_5519_);
lean_dec(v___x_5507_);
v___x_5521_ = lean_box(0);
v_isShared_5522_ = v_isSharedCheck_5526_;
goto v_resetjp_5520_;
}
v_resetjp_5520_:
{
lean_object* v___x_5524_; 
if (v_isShared_5522_ == 0)
{
v___x_5524_ = v___x_5521_;
goto v_reusejp_5523_;
}
else
{
lean_object* v_reuseFailAlloc_5525_; 
v_reuseFailAlloc_5525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5525_, 0, v_a_5519_);
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
lean_object* v_val_5527_; lean_object* v_dummy_5528_; lean_object* v_nargs_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5538_; 
lean_dec_ref(v_env_5496_);
lean_dec(v_declName_5493_);
lean_del_object(v___x_5466_);
lean_dec(v_fieldName_5457_);
v_val_5527_ = lean_ctor_get(v___x_5502_, 0);
lean_inc(v_val_5527_);
lean_dec_ref_known(v___x_5502_, 1);
v_dummy_5528_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5529_ = l_Lean_Expr_getAppNumArgs(v_a_5469_);
lean_inc(v_nargs_5529_);
v___x_5530_ = lean_mk_array(v_nargs_5529_, v_dummy_5528_);
v___x_5531_ = lean_unsigned_to_nat(1u);
v___x_5532_ = lean_nat_sub(v_nargs_5529_, v___x_5531_);
lean_dec(v_nargs_5529_);
v___x_5533_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5469_, v___x_5530_, v___x_5532_);
v___x_5534_ = l_Lean_mkConst(v_val_5527_, v_us_5494_);
v___x_5535_ = l_Lean_mkAppN(v___x_5534_, v___x_5533_);
lean_dec_ref(v___x_5533_);
v___x_5536_ = l_Lean_Expr_app___override(v___x_5535_, v_s_5456_);
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 0, v___x_5536_);
v___x_5538_ = v___x_5471_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v___x_5536_);
v___x_5538_ = v_reuseFailAlloc_5539_;
goto v_reusejp_5537_;
}
v_reusejp_5537_:
{
return v___x_5538_;
}
}
}
}
else
{
lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; 
lean_dec_ref(v___x_5492_);
lean_del_object(v___x_5471_);
lean_del_object(v___x_5466_);
lean_dec(v_fieldName_5457_);
v___x_5554_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5555_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5556_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5456_, v_a_5469_);
v___x_5557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5557_, 0, v___x_5555_);
lean_ctor_set(v___x_5557_, 1, v___x_5556_);
v___x_5558_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5554_, v___x_5557_, v_a_5458_, v_a_5459_, v_a_5460_, v_a_5461_);
return v___x_5558_;
}
v___jp_5473_:
{
lean_object* v___x_5478_; lean_object* v___x_5479_; uint8_t v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5483_; 
v___x_5478_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5479_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5480_ = 1;
v___x_5481_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5457_, v___x_5480_);
if (v_isShared_5467_ == 0)
{
lean_ctor_set_tag(v___x_5466_, 3);
lean_ctor_set(v___x_5466_, 0, v___x_5481_);
v___x_5483_ = v___x_5466_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5481_);
v___x_5483_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5484_ = l_Lean_MessageData_ofFormat(v___x_5483_);
v___x_5485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5485_, 0, v___x_5479_);
lean_ctor_set(v___x_5485_, 1, v___x_5484_);
v___x_5486_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5487_, 0, v___x_5485_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
v___x_5488_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5456_, v_a_5469_);
v___x_5489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5487_);
lean_ctor_set(v___x_5489_, 1, v___x_5488_);
v___x_5490_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5478_, v___x_5489_, v___y_5474_, v___y_5475_, v___y_5477_, v___y_5476_);
return v___x_5490_;
}
}
}
}
else
{
lean_del_object(v___x_5466_);
lean_dec(v_fieldName_5457_);
lean_dec_ref(v_s_5456_);
return v___x_5468_;
}
}
}
else
{
lean_dec(v_fieldName_5457_);
lean_dec_ref(v_s_5456_);
return v___x_5463_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5561_, lean_object* v_declName_5562_, lean_object* v_s_5563_, lean_object* v_fieldName_5564_, lean_object* v_as_5565_, size_t v_sz_5566_, size_t v_i_5567_, lean_object* v_b_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_){
_start:
{
lean_object* v_a_5575_; uint8_t v___x_5579_; 
v___x_5579_ = lean_usize_dec_lt(v_i_5567_, v_sz_5566_);
if (v___x_5579_ == 0)
{
lean_object* v___x_5580_; 
lean_dec(v_fieldName_5564_);
lean_dec_ref(v_s_5563_);
lean_dec(v_declName_5562_);
lean_dec_ref(v___x_5561_);
v___x_5580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5580_, 0, v_b_5568_);
return v___x_5580_;
}
else
{
lean_object* v___x_5581_; lean_object* v___x_5582_; lean_object* v_a_5583_; lean_object* v___x_5584_; 
lean_dec_ref(v_b_5568_);
v___x_5581_ = lean_box(0);
v___x_5582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5583_ = lean_array_uget_borrowed(v_as_5565_, v_i_5567_);
lean_inc(v_a_5583_);
lean_inc(v_declName_5562_);
lean_inc_ref(v___x_5561_);
v___x_5584_ = l_Lean_isSubobjectField_x3f(v___x_5561_, v_declName_5562_, v_a_5583_);
if (lean_obj_tag(v___x_5584_) == 0)
{
v_a_5575_ = v___x_5582_;
goto v___jp_5574_;
}
else
{
lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5643_; 
v_isSharedCheck_5643_ = !lean_is_exclusive(v___x_5584_);
if (v_isSharedCheck_5643_ == 0)
{
lean_object* v_unused_5644_; 
v_unused_5644_ = lean_ctor_get(v___x_5584_, 0);
lean_dec(v_unused_5644_);
v___x_5586_ = v___x_5584_;
v_isShared_5587_ = v_isSharedCheck_5643_;
goto v_resetjp_5585_;
}
else
{
lean_dec(v___x_5584_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5643_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5588_; 
lean_inc(v_a_5583_);
lean_inc_ref(v_s_5563_);
v___x_5588_ = l_Lean_Meta_mkProjection(v_s_5563_, v_a_5583_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_);
if (lean_obj_tag(v___x_5588_) == 0)
{
lean_object* v_a_5589_; lean_object* v___x_5590_; 
v_a_5589_ = lean_ctor_get(v___x_5588_, 0);
lean_inc(v_a_5589_);
lean_dec_ref_known(v___x_5588_, 1);
v___x_5590_ = l_Lean_Meta_saveState___redArg(v___y_5570_, v___y_5572_);
if (lean_obj_tag(v___x_5590_) == 0)
{
lean_object* v_a_5591_; lean_object* v___x_5592_; 
v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
lean_inc(v_a_5591_);
lean_dec_ref_known(v___x_5590_, 1);
lean_inc(v_fieldName_5564_);
v___x_5592_ = l_Lean_Meta_mkProjection(v_a_5589_, v_fieldName_5564_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5605_; 
lean_dec(v_a_5591_);
lean_dec(v_fieldName_5564_);
lean_dec_ref(v_s_5563_);
lean_dec(v_declName_5562_);
lean_dec_ref(v___x_5561_);
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5605_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5605_ == 0)
{
v___x_5595_ = v___x_5592_;
v_isShared_5596_ = v_isSharedCheck_5605_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5592_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5605_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
lean_object* v___x_5598_; 
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 0, v_a_5593_);
v___x_5598_ = v___x_5586_;
goto v_reusejp_5597_;
}
else
{
lean_object* v_reuseFailAlloc_5604_; 
v_reuseFailAlloc_5604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5604_, 0, v_a_5593_);
v___x_5598_ = v_reuseFailAlloc_5604_;
goto v_reusejp_5597_;
}
v_reusejp_5597_:
{
lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5602_; 
v___x_5599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5599_, 0, v___x_5598_);
v___x_5600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5600_, 0, v___x_5599_);
lean_ctor_set(v___x_5600_, 1, v___x_5581_);
if (v_isShared_5596_ == 0)
{
lean_ctor_set(v___x_5595_, 0, v___x_5600_);
v___x_5602_ = v___x_5595_;
goto v_reusejp_5601_;
}
else
{
lean_object* v_reuseFailAlloc_5603_; 
v_reuseFailAlloc_5603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5600_);
v___x_5602_ = v_reuseFailAlloc_5603_;
goto v_reusejp_5601_;
}
v_reusejp_5601_:
{
return v___x_5602_;
}
}
}
}
else
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5626_; 
lean_del_object(v___x_5586_);
v_a_5606_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5626_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5626_ == 0)
{
v___x_5608_ = v___x_5592_;
v_isShared_5609_ = v_isSharedCheck_5626_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5592_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5626_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
uint8_t v___y_5611_; uint8_t v___x_5624_; 
v___x_5624_ = l_Lean_Exception_isInterrupt(v_a_5606_);
if (v___x_5624_ == 0)
{
uint8_t v___x_5625_; 
lean_inc(v_a_5606_);
v___x_5625_ = l_Lean_Exception_isRuntime(v_a_5606_);
v___y_5611_ = v___x_5625_;
goto v___jp_5610_;
}
else
{
v___y_5611_ = v___x_5624_;
goto v___jp_5610_;
}
v___jp_5610_:
{
if (v___y_5611_ == 0)
{
lean_object* v___x_5612_; 
lean_del_object(v___x_5608_);
lean_dec(v_a_5606_);
v___x_5612_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5591_, v___y_5570_, v___y_5572_);
lean_dec(v_a_5591_);
if (lean_obj_tag(v___x_5612_) == 0)
{
lean_dec_ref_known(v___x_5612_, 1);
v_a_5575_ = v___x_5582_;
goto v___jp_5574_;
}
else
{
lean_object* v_a_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
lean_dec(v_fieldName_5564_);
lean_dec_ref(v_s_5563_);
lean_dec(v_declName_5562_);
lean_dec_ref(v___x_5561_);
v_a_5613_ = lean_ctor_get(v___x_5612_, 0);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5612_);
if (v_isSharedCheck_5620_ == 0)
{
v___x_5615_ = v___x_5612_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_inc(v_a_5613_);
lean_dec(v___x_5612_);
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
lean_object* v___x_5622_; 
lean_dec(v_a_5591_);
lean_dec(v_fieldName_5564_);
lean_dec_ref(v_s_5563_);
lean_dec(v_declName_5562_);
lean_dec_ref(v___x_5561_);
if (v_isShared_5609_ == 0)
{
v___x_5622_ = v___x_5608_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v_a_5606_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
}
}
}
else
{
lean_object* v_a_5627_; lean_object* v___x_5629_; uint8_t v_isShared_5630_; uint8_t v_isSharedCheck_5634_; 
lean_dec(v_a_5589_);
lean_del_object(v___x_5586_);
lean_dec(v_fieldName_5564_);
lean_dec_ref(v_s_5563_);
lean_dec(v_declName_5562_);
lean_dec_ref(v___x_5561_);
v_a_5627_ = lean_ctor_get(v___x_5590_, 0);
v_isSharedCheck_5634_ = !lean_is_exclusive(v___x_5590_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5629_ = v___x_5590_;
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
else
{
lean_inc(v_a_5627_);
lean_dec(v___x_5590_);
v___x_5629_ = lean_box(0);
v_isShared_5630_ = v_isSharedCheck_5634_;
goto v_resetjp_5628_;
}
v_resetjp_5628_:
{
lean_object* v___x_5632_; 
if (v_isShared_5630_ == 0)
{
v___x_5632_ = v___x_5629_;
goto v_reusejp_5631_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v_a_5627_);
v___x_5632_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5631_;
}
v_reusejp_5631_:
{
return v___x_5632_;
}
}
}
}
else
{
lean_object* v_a_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5642_; 
lean_del_object(v___x_5586_);
lean_dec(v_fieldName_5564_);
lean_dec_ref(v_s_5563_);
lean_dec(v_declName_5562_);
lean_dec_ref(v___x_5561_);
v_a_5635_ = lean_ctor_get(v___x_5588_, 0);
v_isSharedCheck_5642_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5642_ == 0)
{
v___x_5637_ = v___x_5588_;
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_a_5635_);
lean_dec(v___x_5588_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5642_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v___x_5640_; 
if (v_isShared_5638_ == 0)
{
v___x_5640_ = v___x_5637_;
goto v_reusejp_5639_;
}
else
{
lean_object* v_reuseFailAlloc_5641_; 
v_reuseFailAlloc_5641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5641_, 0, v_a_5635_);
v___x_5640_ = v_reuseFailAlloc_5641_;
goto v_reusejp_5639_;
}
v_reusejp_5639_:
{
return v___x_5640_;
}
}
}
}
}
}
v___jp_5574_:
{
size_t v___x_5576_; size_t v___x_5577_; 
v___x_5576_ = ((size_t)1ULL);
v___x_5577_ = lean_usize_add(v_i_5567_, v___x_5576_);
lean_inc_ref(v_a_5575_);
v_i_5567_ = v___x_5577_;
v_b_5568_ = v_a_5575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5645_, lean_object* v_declName_5646_, lean_object* v_s_5647_, lean_object* v_fieldName_5648_, lean_object* v_as_5649_, lean_object* v_sz_5650_, lean_object* v_i_5651_, lean_object* v_b_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_){
_start:
{
size_t v_sz_boxed_5658_; size_t v_i_boxed_5659_; lean_object* v_res_5660_; 
v_sz_boxed_5658_ = lean_unbox_usize(v_sz_5650_);
lean_dec(v_sz_5650_);
v_i_boxed_5659_ = lean_unbox_usize(v_i_5651_);
lean_dec(v_i_5651_);
v_res_5660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5645_, v_declName_5646_, v_s_5647_, v_fieldName_5648_, v_as_5649_, v_sz_boxed_5658_, v_i_boxed_5659_, v_b_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec(v___y_5654_);
lean_dec_ref(v___y_5653_);
lean_dec_ref(v_as_5649_);
return v_res_5660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5661_, lean_object* v_fieldName_5662_, lean_object* v_a_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v_res_5668_; 
v_res_5668_ = l_Lean_Meta_mkProjection(v_s_5661_, v_fieldName_5662_, v_a_5663_, v_a_5664_, v_a_5665_, v_a_5666_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
lean_dec(v_a_5664_);
lean_dec_ref(v_a_5663_);
return v_res_5668_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5669_, lean_object* v_cons_5670_, lean_object* v_x_5671_){
_start:
{
if (lean_obj_tag(v_x_5671_) == 0)
{
lean_dec_ref(v_cons_5670_);
lean_inc_ref(v_nil_5669_);
return v_nil_5669_;
}
else
{
lean_object* v_head_5672_; lean_object* v_tail_5673_; lean_object* v___x_5674_; lean_object* v___x_5675_; lean_object* v___x_5676_; 
v_head_5672_ = lean_ctor_get(v_x_5671_, 0);
lean_inc(v_head_5672_);
v_tail_5673_ = lean_ctor_get(v_x_5671_, 1);
lean_inc(v_tail_5673_);
lean_dec_ref_known(v_x_5671_, 2);
lean_inc_ref(v_cons_5670_);
v___x_5674_ = l_Lean_Expr_app___override(v_cons_5670_, v_head_5672_);
v___x_5675_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5669_, v_cons_5670_, v_tail_5673_);
v___x_5676_ = l_Lean_Expr_app___override(v___x_5674_, v___x_5675_);
return v___x_5676_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5677_, lean_object* v_cons_5678_, lean_object* v_x_5679_){
_start:
{
lean_object* v_res_5680_; 
v_res_5680_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5677_, v_cons_5678_, v_x_5679_);
lean_dec_ref(v_nil_5677_);
return v_res_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5690_, lean_object* v_xs_5691_, lean_object* v_a_5692_, lean_object* v_a_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_){
_start:
{
lean_object* v___x_5697_; 
lean_inc_ref(v_type_5690_);
v___x_5697_ = l_Lean_Meta_getDecLevel(v_type_5690_, v_a_5692_, v_a_5693_, v_a_5694_, v_a_5695_);
if (lean_obj_tag(v___x_5697_) == 0)
{
lean_object* v_a_5698_; lean_object* v___x_5700_; uint8_t v_isShared_5701_; uint8_t v_isSharedCheck_5717_; 
v_a_5698_ = lean_ctor_get(v___x_5697_, 0);
v_isSharedCheck_5717_ = !lean_is_exclusive(v___x_5697_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5700_ = v___x_5697_;
v_isShared_5701_ = v_isSharedCheck_5717_;
goto v_resetjp_5699_;
}
else
{
lean_inc(v_a_5698_);
lean_dec(v___x_5697_);
v___x_5700_ = lean_box(0);
v_isShared_5701_ = v_isSharedCheck_5717_;
goto v_resetjp_5699_;
}
v_resetjp_5699_:
{
lean_object* v___x_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; 
v___x_5702_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5703_ = lean_box(0);
v___x_5704_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5704_, 0, v_a_5698_);
lean_ctor_set(v___x_5704_, 1, v___x_5703_);
lean_inc_ref(v___x_5704_);
v___x_5705_ = l_Lean_mkConst(v___x_5702_, v___x_5704_);
lean_inc_ref(v_type_5690_);
v___x_5706_ = l_Lean_Expr_app___override(v___x_5705_, v_type_5690_);
if (lean_obj_tag(v_xs_5691_) == 0)
{
lean_object* v___x_5708_; 
lean_dec_ref_known(v___x_5704_, 2);
lean_dec_ref(v_type_5690_);
if (v_isShared_5701_ == 0)
{
lean_ctor_set(v___x_5700_, 0, v___x_5706_);
v___x_5708_ = v___x_5700_;
goto v_reusejp_5707_;
}
else
{
lean_object* v_reuseFailAlloc_5709_; 
v_reuseFailAlloc_5709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5709_, 0, v___x_5706_);
v___x_5708_ = v_reuseFailAlloc_5709_;
goto v_reusejp_5707_;
}
v_reusejp_5707_:
{
return v___x_5708_;
}
}
else
{
lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5715_; 
v___x_5710_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5711_ = l_Lean_mkConst(v___x_5710_, v___x_5704_);
v___x_5712_ = l_Lean_Expr_app___override(v___x_5711_, v_type_5690_);
v___x_5713_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5706_, v___x_5712_, v_xs_5691_);
lean_dec_ref(v___x_5706_);
if (v_isShared_5701_ == 0)
{
lean_ctor_set(v___x_5700_, 0, v___x_5713_);
v___x_5715_ = v___x_5700_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5713_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
}
}
else
{
lean_object* v_a_5718_; lean_object* v___x_5720_; uint8_t v_isShared_5721_; uint8_t v_isSharedCheck_5725_; 
lean_dec(v_xs_5691_);
lean_dec_ref(v_type_5690_);
v_a_5718_ = lean_ctor_get(v___x_5697_, 0);
v_isSharedCheck_5725_ = !lean_is_exclusive(v___x_5697_);
if (v_isSharedCheck_5725_ == 0)
{
v___x_5720_ = v___x_5697_;
v_isShared_5721_ = v_isSharedCheck_5725_;
goto v_resetjp_5719_;
}
else
{
lean_inc(v_a_5718_);
lean_dec(v___x_5697_);
v___x_5720_ = lean_box(0);
v_isShared_5721_ = v_isSharedCheck_5725_;
goto v_resetjp_5719_;
}
v_resetjp_5719_:
{
lean_object* v___x_5723_; 
if (v_isShared_5721_ == 0)
{
v___x_5723_ = v___x_5720_;
goto v_reusejp_5722_;
}
else
{
lean_object* v_reuseFailAlloc_5724_; 
v_reuseFailAlloc_5724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_a_5718_);
v___x_5723_ = v_reuseFailAlloc_5724_;
goto v_reusejp_5722_;
}
v_reusejp_5722_:
{
return v___x_5723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5726_, lean_object* v_xs_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_){
_start:
{
lean_object* v_res_5733_; 
v_res_5733_ = l_Lean_Meta_mkListLit(v_type_5726_, v_xs_5727_, v_a_5728_, v_a_5729_, v_a_5730_, v_a_5731_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
lean_dec(v_a_5729_);
lean_dec_ref(v_a_5728_);
return v_res_5733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5738_, lean_object* v_xs_5739_, lean_object* v_a_5740_, lean_object* v_a_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_){
_start:
{
lean_object* v___x_5745_; 
lean_inc_ref(v_type_5738_);
v___x_5745_ = l_Lean_Meta_getDecLevel(v_type_5738_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_);
if (lean_obj_tag(v___x_5745_) == 0)
{
lean_object* v_a_5746_; lean_object* v___x_5747_; 
v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
lean_inc(v_a_5746_);
lean_dec_ref_known(v___x_5745_, 1);
lean_inc_ref(v_type_5738_);
v___x_5747_ = l_Lean_Meta_mkListLit(v_type_5738_, v_xs_5739_, v_a_5740_, v_a_5741_, v_a_5742_, v_a_5743_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v_a_5748_; lean_object* v___x_5750_; uint8_t v_isShared_5751_; uint8_t v_isSharedCheck_5761_; 
v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5761_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5761_ == 0)
{
v___x_5750_ = v___x_5747_;
v_isShared_5751_ = v_isSharedCheck_5761_;
goto v_resetjp_5749_;
}
else
{
lean_inc(v_a_5748_);
lean_dec(v___x_5747_);
v___x_5750_ = lean_box(0);
v_isShared_5751_ = v_isSharedCheck_5761_;
goto v_resetjp_5749_;
}
v_resetjp_5749_:
{
lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5759_; 
v___x_5752_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5753_ = lean_box(0);
v___x_5754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5754_, 0, v_a_5746_);
lean_ctor_set(v___x_5754_, 1, v___x_5753_);
v___x_5755_ = l_Lean_mkConst(v___x_5752_, v___x_5754_);
v___x_5756_ = l_Lean_Expr_app___override(v___x_5755_, v_type_5738_);
v___x_5757_ = l_Lean_Expr_app___override(v___x_5756_, v_a_5748_);
if (v_isShared_5751_ == 0)
{
lean_ctor_set(v___x_5750_, 0, v___x_5757_);
v___x_5759_ = v___x_5750_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5757_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
else
{
lean_dec(v_a_5746_);
lean_dec_ref(v_type_5738_);
return v___x_5747_;
}
}
else
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5769_; 
lean_dec(v_xs_5739_);
lean_dec_ref(v_type_5738_);
v_a_5762_ = lean_ctor_get(v___x_5745_, 0);
v_isSharedCheck_5769_ = !lean_is_exclusive(v___x_5745_);
if (v_isSharedCheck_5769_ == 0)
{
v___x_5764_ = v___x_5745_;
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5745_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5769_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5767_; 
if (v_isShared_5765_ == 0)
{
v___x_5767_ = v___x_5764_;
goto v_reusejp_5766_;
}
else
{
lean_object* v_reuseFailAlloc_5768_; 
v_reuseFailAlloc_5768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5768_, 0, v_a_5762_);
v___x_5767_ = v_reuseFailAlloc_5768_;
goto v_reusejp_5766_;
}
v_reusejp_5766_:
{
return v___x_5767_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5770_, lean_object* v_xs_5771_, lean_object* v_a_5772_, lean_object* v_a_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_){
_start:
{
lean_object* v_res_5777_; 
v_res_5777_ = l_Lean_Meta_mkArrayLit(v_type_5770_, v_xs_5771_, v_a_5772_, v_a_5773_, v_a_5774_, v_a_5775_);
lean_dec(v_a_5775_);
lean_dec_ref(v_a_5774_);
lean_dec(v_a_5773_);
lean_dec_ref(v_a_5772_);
return v_res_5777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5783_, lean_object* v_a_5784_, lean_object* v_a_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_){
_start:
{
lean_object* v___x_5789_; 
lean_inc_ref(v_type_5783_);
v___x_5789_ = l_Lean_Meta_getDecLevel(v_type_5783_, v_a_5784_, v_a_5785_, v_a_5786_, v_a_5787_);
if (lean_obj_tag(v___x_5789_) == 0)
{
lean_object* v_a_5790_; lean_object* v___x_5792_; uint8_t v_isShared_5793_; uint8_t v_isSharedCheck_5802_; 
v_a_5790_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5802_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5802_ == 0)
{
v___x_5792_ = v___x_5789_;
v_isShared_5793_ = v_isSharedCheck_5802_;
goto v_resetjp_5791_;
}
else
{
lean_inc(v_a_5790_);
lean_dec(v___x_5789_);
v___x_5792_ = lean_box(0);
v_isShared_5793_ = v_isSharedCheck_5802_;
goto v_resetjp_5791_;
}
v_resetjp_5791_:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5800_; 
v___x_5794_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5795_ = lean_box(0);
v___x_5796_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5796_, 0, v_a_5790_);
lean_ctor_set(v___x_5796_, 1, v___x_5795_);
v___x_5797_ = l_Lean_mkConst(v___x_5794_, v___x_5796_);
v___x_5798_ = l_Lean_Expr_app___override(v___x_5797_, v_type_5783_);
if (v_isShared_5793_ == 0)
{
lean_ctor_set(v___x_5792_, 0, v___x_5798_);
v___x_5800_ = v___x_5792_;
goto v_reusejp_5799_;
}
else
{
lean_object* v_reuseFailAlloc_5801_; 
v_reuseFailAlloc_5801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5801_, 0, v___x_5798_);
v___x_5800_ = v_reuseFailAlloc_5801_;
goto v_reusejp_5799_;
}
v_reusejp_5799_:
{
return v___x_5800_;
}
}
}
else
{
lean_object* v_a_5803_; lean_object* v___x_5805_; uint8_t v_isShared_5806_; uint8_t v_isSharedCheck_5810_; 
lean_dec_ref(v_type_5783_);
v_a_5803_ = lean_ctor_get(v___x_5789_, 0);
v_isSharedCheck_5810_ = !lean_is_exclusive(v___x_5789_);
if (v_isSharedCheck_5810_ == 0)
{
v___x_5805_ = v___x_5789_;
v_isShared_5806_ = v_isSharedCheck_5810_;
goto v_resetjp_5804_;
}
else
{
lean_inc(v_a_5803_);
lean_dec(v___x_5789_);
v___x_5805_ = lean_box(0);
v_isShared_5806_ = v_isSharedCheck_5810_;
goto v_resetjp_5804_;
}
v_resetjp_5804_:
{
lean_object* v___x_5808_; 
if (v_isShared_5806_ == 0)
{
v___x_5808_ = v___x_5805_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5809_; 
v_reuseFailAlloc_5809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5809_, 0, v_a_5803_);
v___x_5808_ = v_reuseFailAlloc_5809_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
return v___x_5808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5811_, lean_object* v_a_5812_, lean_object* v_a_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_){
_start:
{
lean_object* v_res_5817_; 
v_res_5817_ = l_Lean_Meta_mkNone(v_type_5811_, v_a_5812_, v_a_5813_, v_a_5814_, v_a_5815_);
lean_dec(v_a_5815_);
lean_dec_ref(v_a_5814_);
lean_dec(v_a_5813_);
lean_dec_ref(v_a_5812_);
return v_res_5817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5822_, lean_object* v_value_5823_, lean_object* v_a_5824_, lean_object* v_a_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_){
_start:
{
lean_object* v___x_5829_; 
lean_inc_ref(v_type_5822_);
v___x_5829_ = l_Lean_Meta_getDecLevel(v_type_5822_, v_a_5824_, v_a_5825_, v_a_5826_, v_a_5827_);
if (lean_obj_tag(v___x_5829_) == 0)
{
lean_object* v_a_5830_; lean_object* v___x_5832_; uint8_t v_isShared_5833_; uint8_t v_isSharedCheck_5842_; 
v_a_5830_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5842_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5842_ == 0)
{
v___x_5832_ = v___x_5829_;
v_isShared_5833_ = v_isSharedCheck_5842_;
goto v_resetjp_5831_;
}
else
{
lean_inc(v_a_5830_);
lean_dec(v___x_5829_);
v___x_5832_ = lean_box(0);
v_isShared_5833_ = v_isSharedCheck_5842_;
goto v_resetjp_5831_;
}
v_resetjp_5831_:
{
lean_object* v___x_5834_; lean_object* v___x_5835_; lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5840_; 
v___x_5834_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5835_ = lean_box(0);
v___x_5836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5836_, 0, v_a_5830_);
lean_ctor_set(v___x_5836_, 1, v___x_5835_);
v___x_5837_ = l_Lean_mkConst(v___x_5834_, v___x_5836_);
v___x_5838_ = l_Lean_mkAppB(v___x_5837_, v_type_5822_, v_value_5823_);
if (v_isShared_5833_ == 0)
{
lean_ctor_set(v___x_5832_, 0, v___x_5838_);
v___x_5840_ = v___x_5832_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v___x_5838_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
else
{
lean_object* v_a_5843_; lean_object* v___x_5845_; uint8_t v_isShared_5846_; uint8_t v_isSharedCheck_5850_; 
lean_dec_ref(v_value_5823_);
lean_dec_ref(v_type_5822_);
v_a_5843_ = lean_ctor_get(v___x_5829_, 0);
v_isSharedCheck_5850_ = !lean_is_exclusive(v___x_5829_);
if (v_isSharedCheck_5850_ == 0)
{
v___x_5845_ = v___x_5829_;
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
else
{
lean_inc(v_a_5843_);
lean_dec(v___x_5829_);
v___x_5845_ = lean_box(0);
v_isShared_5846_ = v_isSharedCheck_5850_;
goto v_resetjp_5844_;
}
v_resetjp_5844_:
{
lean_object* v___x_5848_; 
if (v_isShared_5846_ == 0)
{
v___x_5848_ = v___x_5845_;
goto v_reusejp_5847_;
}
else
{
lean_object* v_reuseFailAlloc_5849_; 
v_reuseFailAlloc_5849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5849_, 0, v_a_5843_);
v___x_5848_ = v_reuseFailAlloc_5849_;
goto v_reusejp_5847_;
}
v_reusejp_5847_:
{
return v___x_5848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5851_, lean_object* v_value_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_){
_start:
{
lean_object* v_res_5858_; 
v_res_5858_ = l_Lean_Meta_mkSome(v_type_5851_, v_value_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_);
lean_dec(v_a_5856_);
lean_dec_ref(v_a_5855_);
lean_dec(v_a_5854_);
lean_dec_ref(v_a_5853_);
return v_res_5858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5864_, lean_object* v_a_5865_, lean_object* v_a_5866_, lean_object* v_a_5867_, lean_object* v_a_5868_){
_start:
{
lean_object* v___x_5870_; lean_object* v___x_5871_; lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; 
v___x_5870_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5871_, 0, v_p_5864_);
v___x_5872_ = lean_box(0);
v___x_5873_ = lean_unsigned_to_nat(2u);
v___x_5874_ = lean_mk_empty_array_with_capacity(v___x_5873_);
v___x_5875_ = lean_array_push(v___x_5874_, v___x_5871_);
v___x_5876_ = lean_array_push(v___x_5875_, v___x_5872_);
v___x_5877_ = l_Lean_Meta_mkAppOptM(v___x_5870_, v___x_5876_, v_a_5865_, v_a_5866_, v_a_5867_, v_a_5868_);
return v___x_5877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_){
_start:
{
lean_object* v_res_5884_; 
v_res_5884_ = l_Lean_Meta_mkDecide(v_p_5878_, v_a_5879_, v_a_5880_, v_a_5881_, v_a_5882_);
lean_dec(v_a_5882_);
lean_dec_ref(v_a_5881_);
lean_dec(v_a_5880_);
lean_dec_ref(v_a_5879_);
return v_res_5884_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; 
v___x_5890_ = lean_box(0);
v___x_5891_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5892_ = l_Lean_mkConst(v___x_5891_, v___x_5890_);
return v___x_5892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5896_, lean_object* v_a_5897_, lean_object* v_a_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_){
_start:
{
lean_object* v___x_5902_; 
v___x_5902_ = l_Lean_Meta_mkDecide(v_p_5896_, v_a_5897_, v_a_5898_, v_a_5899_, v_a_5900_);
if (lean_obj_tag(v___x_5902_) == 0)
{
lean_object* v_a_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
v_a_5903_ = lean_ctor_get(v___x_5902_, 0);
lean_inc(v_a_5903_);
lean_dec_ref_known(v___x_5902_, 1);
v___x_5904_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5905_ = l_Lean_Meta_mkEq(v_a_5903_, v___x_5904_, v_a_5897_, v_a_5898_, v_a_5899_, v_a_5900_);
if (lean_obj_tag(v___x_5905_) == 0)
{
lean_object* v_a_5906_; lean_object* v___x_5907_; 
v_a_5906_ = lean_ctor_get(v___x_5905_, 0);
lean_inc(v_a_5906_);
lean_dec_ref_known(v___x_5905_, 1);
v___x_5907_ = l_Lean_Meta_mkEqRefl(v___x_5904_, v_a_5897_, v_a_5898_, v_a_5899_, v_a_5900_);
if (lean_obj_tag(v___x_5907_) == 0)
{
lean_object* v_a_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; 
v_a_5908_ = lean_ctor_get(v___x_5907_, 0);
lean_inc(v_a_5908_);
lean_dec_ref_known(v___x_5907_, 1);
v___x_5909_ = l_Lean_Meta_mkExpectedPropHint(v_a_5908_, v_a_5906_);
v___x_5910_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5911_ = lean_unsigned_to_nat(1u);
v___x_5912_ = lean_mk_empty_array_with_capacity(v___x_5911_);
v___x_5913_ = lean_array_push(v___x_5912_, v___x_5909_);
v___x_5914_ = l_Lean_Meta_mkAppM(v___x_5910_, v___x_5913_, v_a_5897_, v_a_5898_, v_a_5899_, v_a_5900_);
return v___x_5914_;
}
else
{
lean_dec(v_a_5906_);
return v___x_5907_;
}
}
else
{
return v___x_5905_;
}
}
else
{
return v___x_5902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5915_, lean_object* v_a_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_){
_start:
{
lean_object* v_res_5921_; 
v_res_5921_ = l_Lean_Meta_mkDecideProof(v_p_5915_, v_a_5916_, v_a_5917_, v_a_5918_, v_a_5919_);
lean_dec(v_a_5919_);
lean_dec_ref(v_a_5918_);
lean_dec(v_a_5917_);
lean_dec_ref(v_a_5916_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5927_, lean_object* v_b_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_){
_start:
{
lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; 
v___x_5934_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_5935_ = lean_unsigned_to_nat(2u);
v___x_5936_ = lean_mk_empty_array_with_capacity(v___x_5935_);
v___x_5937_ = lean_array_push(v___x_5936_, v_a_5927_);
v___x_5938_ = lean_array_push(v___x_5937_, v_b_5928_);
v___x_5939_ = l_Lean_Meta_mkAppM(v___x_5934_, v___x_5938_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_);
return v___x_5939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_5940_, lean_object* v_b_5941_, lean_object* v_a_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_){
_start:
{
lean_object* v_res_5947_; 
v_res_5947_ = l_Lean_Meta_mkLt(v_a_5940_, v_b_5941_, v_a_5942_, v_a_5943_, v_a_5944_, v_a_5945_);
lean_dec(v_a_5945_);
lean_dec_ref(v_a_5944_);
lean_dec(v_a_5943_);
lean_dec_ref(v_a_5942_);
return v_res_5947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_5953_, lean_object* v_b_5954_, lean_object* v_a_5955_, lean_object* v_a_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_){
_start:
{
lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5960_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_5961_ = lean_unsigned_to_nat(2u);
v___x_5962_ = lean_mk_empty_array_with_capacity(v___x_5961_);
v___x_5963_ = lean_array_push(v___x_5962_, v_a_5953_);
v___x_5964_ = lean_array_push(v___x_5963_, v_b_5954_);
v___x_5965_ = l_Lean_Meta_mkAppM(v___x_5960_, v___x_5964_, v_a_5955_, v_a_5956_, v_a_5957_, v_a_5958_);
return v___x_5965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_5966_, lean_object* v_b_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_){
_start:
{
lean_object* v_res_5973_; 
v_res_5973_ = l_Lean_Meta_mkLe(v_a_5966_, v_b_5967_, v_a_5968_, v_a_5969_, v_a_5970_, v_a_5971_);
lean_dec(v_a_5971_);
lean_dec_ref(v_a_5970_);
lean_dec(v_a_5969_);
lean_dec_ref(v_a_5968_);
return v_res_5973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_){
_start:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5985_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_5986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5986_, 0, v_00_u03b1_5979_);
v___x_5987_ = lean_box(0);
v___x_5988_ = lean_unsigned_to_nat(2u);
v___x_5989_ = lean_mk_empty_array_with_capacity(v___x_5988_);
v___x_5990_ = lean_array_push(v___x_5989_, v___x_5986_);
v___x_5991_ = lean_array_push(v___x_5990_, v___x_5987_);
v___x_5992_ = l_Lean_Meta_mkAppOptM(v___x_5985_, v___x_5991_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_);
return v___x_5992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_){
_start:
{
lean_object* v_res_5999_; 
v_res_5999_ = l_Lean_Meta_mkDefault(v_00_u03b1_5993_, v_a_5994_, v_a_5995_, v_a_5996_, v_a_5997_);
lean_dec(v_a_5997_);
lean_dec_ref(v_a_5996_);
lean_dec(v_a_5995_);
lean_dec_ref(v_a_5994_);
return v_res_5999_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_){
_start:
{
lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; 
v___x_6011_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_6012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6012_, 0, v_00_u03b1_6005_);
v___x_6013_ = lean_box(0);
v___x_6014_ = lean_unsigned_to_nat(2u);
v___x_6015_ = lean_mk_empty_array_with_capacity(v___x_6014_);
v___x_6016_ = lean_array_push(v___x_6015_, v___x_6012_);
v___x_6017_ = lean_array_push(v___x_6016_, v___x_6013_);
v___x_6018_ = l_Lean_Meta_mkAppOptM(v___x_6011_, v___x_6017_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
return v___x_6018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_){
_start:
{
lean_object* v_res_6025_; 
v_res_6025_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6019_, v_a_6020_, v_a_6021_, v_a_6022_, v_a_6023_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
lean_dec(v_a_6021_);
lean_dec_ref(v_a_6020_);
return v_res_6025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6029_, lean_object* v_a_6030_, lean_object* v_a_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_){
_start:
{
lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; 
v___x_6035_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6036_ = lean_unsigned_to_nat(1u);
v___x_6037_ = lean_mk_empty_array_with_capacity(v___x_6036_);
v___x_6038_ = lean_array_push(v___x_6037_, v_h_6029_);
v___x_6039_ = l_Lean_Meta_mkAppM(v___x_6035_, v___x_6038_, v_a_6030_, v_a_6031_, v_a_6032_, v_a_6033_);
return v___x_6039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6040_, lean_object* v_a_6041_, lean_object* v_a_6042_, lean_object* v_a_6043_, lean_object* v_a_6044_, lean_object* v_a_6045_){
_start:
{
lean_object* v_res_6046_; 
v_res_6046_ = l_Lean_Meta_mkFunExt(v_h_6040_, v_a_6041_, v_a_6042_, v_a_6043_, v_a_6044_);
lean_dec(v_a_6044_);
lean_dec_ref(v_a_6043_);
lean_dec(v_a_6042_);
lean_dec_ref(v_a_6041_);
return v_res_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6050_, lean_object* v_a_6051_, lean_object* v_a_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_){
_start:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6056_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6057_ = lean_unsigned_to_nat(1u);
v___x_6058_ = lean_mk_empty_array_with_capacity(v___x_6057_);
v___x_6059_ = lean_array_push(v___x_6058_, v_h_6050_);
v___x_6060_ = l_Lean_Meta_mkAppM(v___x_6056_, v___x_6059_, v_a_6051_, v_a_6052_, v_a_6053_, v_a_6054_);
return v___x_6060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_){
_start:
{
lean_object* v_res_6067_; 
v_res_6067_ = l_Lean_Meta_mkPropExt(v_h_6061_, v_a_6062_, v_a_6063_, v_a_6064_, v_a_6065_);
lean_dec(v_a_6065_);
lean_dec_ref(v_a_6064_);
lean_dec(v_a_6063_);
lean_dec_ref(v_a_6062_);
return v_res_6067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6071_, lean_object* v_h_u2082_6072_, lean_object* v_a_6073_, lean_object* v_a_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_){
_start:
{
lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; 
v___x_6078_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6079_ = lean_unsigned_to_nat(2u);
v___x_6080_ = lean_mk_empty_array_with_capacity(v___x_6079_);
v___x_6081_ = lean_array_push(v___x_6080_, v_h_u2081_6071_);
v___x_6082_ = lean_array_push(v___x_6081_, v_h_u2082_6072_);
v___x_6083_ = l_Lean_Meta_mkAppM(v___x_6078_, v___x_6082_, v_a_6073_, v_a_6074_, v_a_6075_, v_a_6076_);
return v___x_6083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6084_, lean_object* v_h_u2082_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_, lean_object* v_a_6090_){
_start:
{
lean_object* v_res_6091_; 
v_res_6091_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6084_, v_h_u2082_6085_, v_a_6086_, v_a_6087_, v_a_6088_, v_a_6089_);
lean_dec(v_a_6089_);
lean_dec_ref(v_a_6088_);
lean_dec(v_a_6087_);
lean_dec_ref(v_a_6086_);
return v_res_6091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6095_, lean_object* v_h_6096_, lean_object* v_a_6097_, lean_object* v_a_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_){
_start:
{
lean_object* v___x_6102_; lean_object* v___x_6103_; lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6102_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6103_ = lean_unsigned_to_nat(2u);
v___x_6104_ = lean_mk_empty_array_with_capacity(v___x_6103_);
v___x_6105_ = lean_array_push(v___x_6104_, v_b_6095_);
v___x_6106_ = lean_array_push(v___x_6105_, v_h_6096_);
v___x_6107_ = l_Lean_Meta_mkAppM(v___x_6102_, v___x_6106_, v_a_6097_, v_a_6098_, v_a_6099_, v_a_6100_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6108_, lean_object* v_h_6109_, lean_object* v_a_6110_, lean_object* v_a_6111_, lean_object* v_a_6112_, lean_object* v_a_6113_, lean_object* v_a_6114_){
_start:
{
lean_object* v_res_6115_; 
v_res_6115_ = l_Lean_Meta_mkLetValCongr(v_b_6108_, v_h_6109_, v_a_6110_, v_a_6111_, v_a_6112_, v_a_6113_);
lean_dec(v_a_6113_);
lean_dec_ref(v_a_6112_);
lean_dec(v_a_6111_);
lean_dec_ref(v_a_6110_);
return v_res_6115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6119_, lean_object* v_h_6120_, lean_object* v_a_6121_, lean_object* v_a_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_){
_start:
{
lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; 
v___x_6126_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6127_ = lean_unsigned_to_nat(2u);
v___x_6128_ = lean_mk_empty_array_with_capacity(v___x_6127_);
v___x_6129_ = lean_array_push(v___x_6128_, v_a_6119_);
v___x_6130_ = lean_array_push(v___x_6129_, v_h_6120_);
v___x_6131_ = l_Lean_Meta_mkAppM(v___x_6126_, v___x_6130_, v_a_6121_, v_a_6122_, v_a_6123_, v_a_6124_);
return v___x_6131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6132_, lean_object* v_h_6133_, lean_object* v_a_6134_, lean_object* v_a_6135_, lean_object* v_a_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_){
_start:
{
lean_object* v_res_6139_; 
v_res_6139_ = l_Lean_Meta_mkLetBodyCongr(v_a_6132_, v_h_6133_, v_a_6134_, v_a_6135_, v_a_6136_, v_a_6137_);
lean_dec(v_a_6137_);
lean_dec_ref(v_a_6136_);
lean_dec(v_a_6135_);
lean_dec_ref(v_a_6134_);
return v_res_6139_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; 
v___x_6143_ = lean_box(0);
v___x_6144_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6145_ = l_Lean_mkConst(v___x_6144_, v___x_6143_);
return v___x_6145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6149_, lean_object* v_h_6150_){
_start:
{
lean_object* v___x_6154_; uint8_t v___x_6155_; 
lean_inc_ref(v_h_6150_);
v___x_6154_ = l_Lean_Expr_cleanupAnnotations(v_h_6150_);
v___x_6155_ = l_Lean_Expr_isApp(v___x_6154_);
if (v___x_6155_ == 0)
{
lean_dec_ref(v___x_6154_);
goto v___jp_6151_;
}
else
{
lean_object* v_arg_6156_; lean_object* v___x_6157_; uint8_t v___x_6158_; 
v_arg_6156_ = lean_ctor_get(v___x_6154_, 1);
lean_inc_ref(v_arg_6156_);
v___x_6157_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6154_);
v___x_6158_ = l_Lean_Expr_isApp(v___x_6157_);
if (v___x_6158_ == 0)
{
lean_dec_ref(v___x_6157_);
lean_dec_ref(v_arg_6156_);
goto v___jp_6151_;
}
else
{
lean_object* v___x_6159_; lean_object* v___x_6160_; uint8_t v___x_6161_; 
v___x_6159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6157_);
v___x_6160_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6161_ = l_Lean_Expr_isConstOf(v___x_6159_, v___x_6160_);
lean_dec_ref(v___x_6159_);
if (v___x_6161_ == 0)
{
lean_dec_ref(v_arg_6156_);
goto v___jp_6151_;
}
else
{
lean_dec_ref(v_h_6150_);
lean_dec_ref(v_p_6149_);
return v_arg_6156_;
}
}
}
v___jp_6151_:
{
lean_object* v___x_6152_; lean_object* v___x_6153_; 
v___x_6152_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6153_ = l_Lean_mkAppB(v___x_6152_, v_p_6149_, v_h_6150_);
return v___x_6153_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6162_, lean_object* v_a_6163_, lean_object* v_a_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_){
_start:
{
lean_object* v___x_6168_; 
lean_inc_ref(v_h_6162_);
v___x_6168_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6162_, v_a_6164_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v_a_6169_; lean_object* v___x_6171_; uint8_t v_isShared_6172_; uint8_t v_isSharedCheck_6194_; 
v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6194_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6194_ == 0)
{
v___x_6171_ = v___x_6168_;
v_isShared_6172_ = v_isSharedCheck_6194_;
goto v_resetjp_6170_;
}
else
{
lean_inc(v_a_6169_);
lean_dec(v___x_6168_);
v___x_6171_ = lean_box(0);
v_isShared_6172_ = v_isSharedCheck_6194_;
goto v_resetjp_6170_;
}
v_resetjp_6170_:
{
lean_object* v___y_6174_; lean_object* v___y_6175_; lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___x_6183_; uint8_t v___x_6184_; 
v___x_6183_ = l_Lean_Expr_cleanupAnnotations(v_a_6169_);
v___x_6184_ = l_Lean_Expr_isApp(v___x_6183_);
if (v___x_6184_ == 0)
{
lean_dec_ref(v___x_6183_);
lean_del_object(v___x_6171_);
v___y_6174_ = v_a_6163_;
v___y_6175_ = v_a_6164_;
v___y_6176_ = v_a_6165_;
v___y_6177_ = v_a_6166_;
goto v___jp_6173_;
}
else
{
lean_object* v_arg_6185_; lean_object* v___x_6186_; uint8_t v___x_6187_; 
v_arg_6185_ = lean_ctor_get(v___x_6183_, 1);
lean_inc_ref(v_arg_6185_);
v___x_6186_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6183_);
v___x_6187_ = l_Lean_Expr_isApp(v___x_6186_);
if (v___x_6187_ == 0)
{
lean_dec_ref(v___x_6186_);
lean_dec_ref(v_arg_6185_);
lean_del_object(v___x_6171_);
v___y_6174_ = v_a_6163_;
v___y_6175_ = v_a_6164_;
v___y_6176_ = v_a_6165_;
v___y_6177_ = v_a_6166_;
goto v___jp_6173_;
}
else
{
lean_object* v___x_6188_; lean_object* v___x_6189_; uint8_t v___x_6190_; 
v___x_6188_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6186_);
v___x_6189_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6190_ = l_Lean_Expr_isConstOf(v___x_6188_, v___x_6189_);
lean_dec_ref(v___x_6188_);
if (v___x_6190_ == 0)
{
lean_dec_ref(v_arg_6185_);
lean_del_object(v___x_6171_);
v___y_6174_ = v_a_6163_;
v___y_6175_ = v_a_6164_;
v___y_6176_ = v_a_6165_;
v___y_6177_ = v_a_6166_;
goto v___jp_6173_;
}
else
{
lean_object* v___x_6192_; 
lean_dec_ref(v_h_6162_);
if (v_isShared_6172_ == 0)
{
lean_ctor_set(v___x_6171_, 0, v_arg_6185_);
v___x_6192_ = v___x_6171_;
goto v_reusejp_6191_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v_arg_6185_);
v___x_6192_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6191_;
}
v_reusejp_6191_:
{
return v___x_6192_;
}
}
}
}
v___jp_6173_:
{
lean_object* v___x_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; 
v___x_6178_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6179_ = lean_unsigned_to_nat(1u);
v___x_6180_ = lean_mk_empty_array_with_capacity(v___x_6179_);
v___x_6181_ = lean_array_push(v___x_6180_, v_h_6162_);
v___x_6182_ = l_Lean_Meta_mkAppM(v___x_6178_, v___x_6181_, v___y_6174_, v___y_6175_, v___y_6176_, v___y_6177_);
return v___x_6182_;
}
}
}
else
{
lean_dec_ref(v_h_6162_);
return v___x_6168_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6195_, lean_object* v_a_6196_, lean_object* v_a_6197_, lean_object* v_a_6198_, lean_object* v_a_6199_, lean_object* v_a_6200_){
_start:
{
lean_object* v_res_6201_; 
v_res_6201_ = l_Lean_Meta_mkOfEqFalse(v_h_6195_, v_a_6196_, v_a_6197_, v_a_6198_, v_a_6199_);
lean_dec(v_a_6199_);
lean_dec_ref(v_a_6198_);
lean_dec(v_a_6197_);
lean_dec_ref(v_a_6196_);
return v_res_6201_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; 
v___x_6205_ = lean_box(0);
v___x_6206_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6207_ = l_Lean_mkConst(v___x_6206_, v___x_6205_);
return v___x_6207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6211_, lean_object* v_h_6212_){
_start:
{
lean_object* v___x_6216_; uint8_t v___x_6217_; 
lean_inc_ref(v_h_6212_);
v___x_6216_ = l_Lean_Expr_cleanupAnnotations(v_h_6212_);
v___x_6217_ = l_Lean_Expr_isApp(v___x_6216_);
if (v___x_6217_ == 0)
{
lean_dec_ref(v___x_6216_);
goto v___jp_6213_;
}
else
{
lean_object* v_arg_6218_; lean_object* v___x_6219_; uint8_t v___x_6220_; 
v_arg_6218_ = lean_ctor_get(v___x_6216_, 1);
lean_inc_ref(v_arg_6218_);
v___x_6219_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6216_);
v___x_6220_ = l_Lean_Expr_isApp(v___x_6219_);
if (v___x_6220_ == 0)
{
lean_dec_ref(v___x_6219_);
lean_dec_ref(v_arg_6218_);
goto v___jp_6213_;
}
else
{
lean_object* v___x_6221_; lean_object* v___x_6222_; uint8_t v___x_6223_; 
v___x_6221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6219_);
v___x_6222_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6223_ = l_Lean_Expr_isConstOf(v___x_6221_, v___x_6222_);
lean_dec_ref(v___x_6221_);
if (v___x_6223_ == 0)
{
lean_dec_ref(v_arg_6218_);
goto v___jp_6213_;
}
else
{
lean_dec_ref(v_h_6212_);
lean_dec_ref(v_p_6211_);
return v_arg_6218_;
}
}
}
v___jp_6213_:
{
lean_object* v___x_6214_; lean_object* v___x_6215_; 
v___x_6214_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6215_ = l_Lean_mkAppB(v___x_6214_, v_p_6211_, v_h_6212_);
return v___x_6215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6224_, lean_object* v_a_6225_, lean_object* v_a_6226_, lean_object* v_a_6227_, lean_object* v_a_6228_){
_start:
{
lean_object* v___x_6230_; 
lean_inc_ref(v_h_6224_);
v___x_6230_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6224_, v_a_6226_);
if (lean_obj_tag(v___x_6230_) == 0)
{
lean_object* v_a_6231_; lean_object* v___x_6233_; uint8_t v_isShared_6234_; uint8_t v_isSharedCheck_6256_; 
v_a_6231_ = lean_ctor_get(v___x_6230_, 0);
v_isSharedCheck_6256_ = !lean_is_exclusive(v___x_6230_);
if (v_isSharedCheck_6256_ == 0)
{
v___x_6233_ = v___x_6230_;
v_isShared_6234_ = v_isSharedCheck_6256_;
goto v_resetjp_6232_;
}
else
{
lean_inc(v_a_6231_);
lean_dec(v___x_6230_);
v___x_6233_ = lean_box(0);
v_isShared_6234_ = v_isSharedCheck_6256_;
goto v_resetjp_6232_;
}
v_resetjp_6232_:
{
lean_object* v___y_6236_; lean_object* v___y_6237_; lean_object* v___y_6238_; lean_object* v___y_6239_; lean_object* v___x_6245_; uint8_t v___x_6246_; 
v___x_6245_ = l_Lean_Expr_cleanupAnnotations(v_a_6231_);
v___x_6246_ = l_Lean_Expr_isApp(v___x_6245_);
if (v___x_6246_ == 0)
{
lean_dec_ref(v___x_6245_);
lean_del_object(v___x_6233_);
v___y_6236_ = v_a_6225_;
v___y_6237_ = v_a_6226_;
v___y_6238_ = v_a_6227_;
v___y_6239_ = v_a_6228_;
goto v___jp_6235_;
}
else
{
lean_object* v_arg_6247_; lean_object* v___x_6248_; uint8_t v___x_6249_; 
v_arg_6247_ = lean_ctor_get(v___x_6245_, 1);
lean_inc_ref(v_arg_6247_);
v___x_6248_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6245_);
v___x_6249_ = l_Lean_Expr_isApp(v___x_6248_);
if (v___x_6249_ == 0)
{
lean_dec_ref(v___x_6248_);
lean_dec_ref(v_arg_6247_);
lean_del_object(v___x_6233_);
v___y_6236_ = v_a_6225_;
v___y_6237_ = v_a_6226_;
v___y_6238_ = v_a_6227_;
v___y_6239_ = v_a_6228_;
goto v___jp_6235_;
}
else
{
lean_object* v___x_6250_; lean_object* v___x_6251_; uint8_t v___x_6252_; 
v___x_6250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6248_);
v___x_6251_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6252_ = l_Lean_Expr_isConstOf(v___x_6250_, v___x_6251_);
lean_dec_ref(v___x_6250_);
if (v___x_6252_ == 0)
{
lean_dec_ref(v_arg_6247_);
lean_del_object(v___x_6233_);
v___y_6236_ = v_a_6225_;
v___y_6237_ = v_a_6226_;
v___y_6238_ = v_a_6227_;
v___y_6239_ = v_a_6228_;
goto v___jp_6235_;
}
else
{
lean_object* v___x_6254_; 
lean_dec_ref(v_h_6224_);
if (v_isShared_6234_ == 0)
{
lean_ctor_set(v___x_6233_, 0, v_arg_6247_);
v___x_6254_ = v___x_6233_;
goto v_reusejp_6253_;
}
else
{
lean_object* v_reuseFailAlloc_6255_; 
v_reuseFailAlloc_6255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6255_, 0, v_arg_6247_);
v___x_6254_ = v_reuseFailAlloc_6255_;
goto v_reusejp_6253_;
}
v_reusejp_6253_:
{
return v___x_6254_;
}
}
}
}
v___jp_6235_:
{
lean_object* v___x_6240_; lean_object* v___x_6241_; lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; 
v___x_6240_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6241_ = lean_unsigned_to_nat(1u);
v___x_6242_ = lean_mk_empty_array_with_capacity(v___x_6241_);
v___x_6243_ = lean_array_push(v___x_6242_, v_h_6224_);
v___x_6244_ = l_Lean_Meta_mkAppM(v___x_6240_, v___x_6243_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_);
return v___x_6244_;
}
}
}
else
{
lean_dec_ref(v_h_6224_);
return v___x_6230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6257_, lean_object* v_a_6258_, lean_object* v_a_6259_, lean_object* v_a_6260_, lean_object* v_a_6261_, lean_object* v_a_6262_){
_start:
{
lean_object* v_res_6263_; 
v_res_6263_ = l_Lean_Meta_mkOfEqTrue(v_h_6257_, v_a_6258_, v_a_6259_, v_a_6260_, v_a_6261_);
lean_dec(v_a_6261_);
lean_dec_ref(v_a_6260_);
lean_dec(v_a_6259_);
lean_dec_ref(v_a_6258_);
return v_res_6263_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6264_; lean_object* v___x_6265_; lean_object* v___x_6266_; 
v___x_6264_ = lean_box(0);
v___x_6265_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6266_ = l_Lean_mkConst(v___x_6265_, v___x_6264_);
return v___x_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6267_, lean_object* v_h_6268_){
_start:
{
lean_object* v___x_6272_; uint8_t v___x_6273_; 
lean_inc_ref(v_h_6268_);
v___x_6272_ = l_Lean_Expr_cleanupAnnotations(v_h_6268_);
v___x_6273_ = l_Lean_Expr_isApp(v___x_6272_);
if (v___x_6273_ == 0)
{
lean_dec_ref(v___x_6272_);
goto v___jp_6269_;
}
else
{
lean_object* v_arg_6274_; lean_object* v___x_6275_; uint8_t v___x_6276_; 
v_arg_6274_ = lean_ctor_get(v___x_6272_, 1);
lean_inc_ref(v_arg_6274_);
v___x_6275_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6272_);
v___x_6276_ = l_Lean_Expr_isApp(v___x_6275_);
if (v___x_6276_ == 0)
{
lean_dec_ref(v___x_6275_);
lean_dec_ref(v_arg_6274_);
goto v___jp_6269_;
}
else
{
lean_object* v___x_6277_; lean_object* v___x_6278_; uint8_t v___x_6279_; 
v___x_6277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6275_);
v___x_6278_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6279_ = l_Lean_Expr_isConstOf(v___x_6277_, v___x_6278_);
lean_dec_ref(v___x_6277_);
if (v___x_6279_ == 0)
{
lean_dec_ref(v_arg_6274_);
goto v___jp_6269_;
}
else
{
lean_dec_ref(v_h_6268_);
lean_dec_ref(v_p_6267_);
return v_arg_6274_;
}
}
}
v___jp_6269_:
{
lean_object* v___x_6270_; lean_object* v___x_6271_; 
v___x_6270_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6271_ = l_Lean_mkAppB(v___x_6270_, v_p_6267_, v_h_6268_);
return v___x_6271_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6280_, lean_object* v_a_6281_, lean_object* v_a_6282_, lean_object* v_a_6283_, lean_object* v_a_6284_){
_start:
{
lean_object* v___x_6286_; 
lean_inc_ref(v_h_6280_);
v___x_6286_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6280_, v_a_6282_);
if (lean_obj_tag(v___x_6286_) == 0)
{
lean_object* v_a_6287_; lean_object* v___x_6289_; uint8_t v_isShared_6290_; uint8_t v_isSharedCheck_6318_; 
v_a_6287_ = lean_ctor_get(v___x_6286_, 0);
v_isSharedCheck_6318_ = !lean_is_exclusive(v___x_6286_);
if (v_isSharedCheck_6318_ == 0)
{
v___x_6289_ = v___x_6286_;
v_isShared_6290_ = v_isSharedCheck_6318_;
goto v_resetjp_6288_;
}
else
{
lean_inc(v_a_6287_);
lean_dec(v___x_6286_);
v___x_6289_ = lean_box(0);
v_isShared_6290_ = v_isSharedCheck_6318_;
goto v_resetjp_6288_;
}
v_resetjp_6288_:
{
lean_object* v___y_6292_; lean_object* v___y_6293_; lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___x_6307_; uint8_t v___x_6308_; 
v___x_6307_ = l_Lean_Expr_cleanupAnnotations(v_a_6287_);
v___x_6308_ = l_Lean_Expr_isApp(v___x_6307_);
if (v___x_6308_ == 0)
{
lean_dec_ref(v___x_6307_);
lean_del_object(v___x_6289_);
v___y_6292_ = v_a_6281_;
v___y_6293_ = v_a_6282_;
v___y_6294_ = v_a_6283_;
v___y_6295_ = v_a_6284_;
goto v___jp_6291_;
}
else
{
lean_object* v_arg_6309_; lean_object* v___x_6310_; uint8_t v___x_6311_; 
v_arg_6309_ = lean_ctor_get(v___x_6307_, 1);
lean_inc_ref(v_arg_6309_);
v___x_6310_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6307_);
v___x_6311_ = l_Lean_Expr_isApp(v___x_6310_);
if (v___x_6311_ == 0)
{
lean_dec_ref(v___x_6310_);
lean_dec_ref(v_arg_6309_);
lean_del_object(v___x_6289_);
v___y_6292_ = v_a_6281_;
v___y_6293_ = v_a_6282_;
v___y_6294_ = v_a_6283_;
v___y_6295_ = v_a_6284_;
goto v___jp_6291_;
}
else
{
lean_object* v___x_6312_; lean_object* v___x_6313_; uint8_t v___x_6314_; 
v___x_6312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6310_);
v___x_6313_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6314_ = l_Lean_Expr_isConstOf(v___x_6312_, v___x_6313_);
lean_dec_ref(v___x_6312_);
if (v___x_6314_ == 0)
{
lean_dec_ref(v_arg_6309_);
lean_del_object(v___x_6289_);
v___y_6292_ = v_a_6281_;
v___y_6293_ = v_a_6282_;
v___y_6294_ = v_a_6283_;
v___y_6295_ = v_a_6284_;
goto v___jp_6291_;
}
else
{
lean_object* v___x_6316_; 
lean_dec_ref(v_h_6280_);
if (v_isShared_6290_ == 0)
{
lean_ctor_set(v___x_6289_, 0, v_arg_6309_);
v___x_6316_ = v___x_6289_;
goto v_reusejp_6315_;
}
else
{
lean_object* v_reuseFailAlloc_6317_; 
v_reuseFailAlloc_6317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_arg_6309_);
v___x_6316_ = v_reuseFailAlloc_6317_;
goto v_reusejp_6315_;
}
v_reusejp_6315_:
{
return v___x_6316_;
}
}
}
}
v___jp_6291_:
{
lean_object* v___x_6296_; 
lean_inc(v___y_6295_);
lean_inc_ref(v___y_6294_);
lean_inc(v___y_6293_);
lean_inc_ref(v___y_6292_);
lean_inc_ref(v_h_6280_);
v___x_6296_ = lean_infer_type(v_h_6280_, v___y_6292_, v___y_6293_, v___y_6294_, v___y_6295_);
if (lean_obj_tag(v___x_6296_) == 0)
{
lean_object* v_a_6297_; lean_object* v___x_6299_; uint8_t v_isShared_6300_; uint8_t v_isSharedCheck_6306_; 
v_a_6297_ = lean_ctor_get(v___x_6296_, 0);
v_isSharedCheck_6306_ = !lean_is_exclusive(v___x_6296_);
if (v_isSharedCheck_6306_ == 0)
{
v___x_6299_ = v___x_6296_;
v_isShared_6300_ = v_isSharedCheck_6306_;
goto v_resetjp_6298_;
}
else
{
lean_inc(v_a_6297_);
lean_dec(v___x_6296_);
v___x_6299_ = lean_box(0);
v_isShared_6300_ = v_isSharedCheck_6306_;
goto v_resetjp_6298_;
}
v_resetjp_6298_:
{
lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6304_; 
v___x_6301_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6302_ = l_Lean_mkAppB(v___x_6301_, v_a_6297_, v_h_6280_);
if (v_isShared_6300_ == 0)
{
lean_ctor_set(v___x_6299_, 0, v___x_6302_);
v___x_6304_ = v___x_6299_;
goto v_reusejp_6303_;
}
else
{
lean_object* v_reuseFailAlloc_6305_; 
v_reuseFailAlloc_6305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6305_, 0, v___x_6302_);
v___x_6304_ = v_reuseFailAlloc_6305_;
goto v_reusejp_6303_;
}
v_reusejp_6303_:
{
return v___x_6304_;
}
}
}
else
{
lean_dec_ref(v_h_6280_);
return v___x_6296_;
}
}
}
}
else
{
lean_dec_ref(v_h_6280_);
return v___x_6286_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6319_, lean_object* v_a_6320_, lean_object* v_a_6321_, lean_object* v_a_6322_, lean_object* v_a_6323_, lean_object* v_a_6324_){
_start:
{
lean_object* v_res_6325_; 
v_res_6325_ = l_Lean_Meta_mkEqTrue(v_h_6319_, v_a_6320_, v_a_6321_, v_a_6322_, v_a_6323_);
lean_dec(v_a_6323_);
lean_dec_ref(v_a_6322_);
lean_dec(v_a_6321_);
lean_dec_ref(v_a_6320_);
return v_res_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6326_, lean_object* v_a_6327_, lean_object* v_a_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_){
_start:
{
lean_object* v___y_6333_; lean_object* v___y_6334_; lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___x_6342_; uint8_t v___x_6343_; 
lean_inc_ref(v_h_6326_);
v___x_6342_ = l_Lean_Expr_cleanupAnnotations(v_h_6326_);
v___x_6343_ = l_Lean_Expr_isApp(v___x_6342_);
if (v___x_6343_ == 0)
{
lean_dec_ref(v___x_6342_);
v___y_6333_ = v_a_6327_;
v___y_6334_ = v_a_6328_;
v___y_6335_ = v_a_6329_;
v___y_6336_ = v_a_6330_;
goto v___jp_6332_;
}
else
{
lean_object* v_arg_6344_; lean_object* v___x_6345_; uint8_t v___x_6346_; 
v_arg_6344_ = lean_ctor_get(v___x_6342_, 1);
lean_inc_ref(v_arg_6344_);
v___x_6345_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6342_);
v___x_6346_ = l_Lean_Expr_isApp(v___x_6345_);
if (v___x_6346_ == 0)
{
lean_dec_ref(v___x_6345_);
lean_dec_ref(v_arg_6344_);
v___y_6333_ = v_a_6327_;
v___y_6334_ = v_a_6328_;
v___y_6335_ = v_a_6329_;
v___y_6336_ = v_a_6330_;
goto v___jp_6332_;
}
else
{
lean_object* v___x_6347_; lean_object* v___x_6348_; uint8_t v___x_6349_; 
v___x_6347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6345_);
v___x_6348_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6349_ = l_Lean_Expr_isConstOf(v___x_6347_, v___x_6348_);
lean_dec_ref(v___x_6347_);
if (v___x_6349_ == 0)
{
lean_dec_ref(v_arg_6344_);
v___y_6333_ = v_a_6327_;
v___y_6334_ = v_a_6328_;
v___y_6335_ = v_a_6329_;
v___y_6336_ = v_a_6330_;
goto v___jp_6332_;
}
else
{
lean_object* v___x_6350_; 
lean_dec_ref(v_h_6326_);
v___x_6350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6350_, 0, v_arg_6344_);
return v___x_6350_;
}
}
}
v___jp_6332_:
{
lean_object* v___x_6337_; lean_object* v___x_6338_; lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; 
v___x_6337_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6338_ = lean_unsigned_to_nat(1u);
v___x_6339_ = lean_mk_empty_array_with_capacity(v___x_6338_);
v___x_6340_ = lean_array_push(v___x_6339_, v_h_6326_);
v___x_6341_ = l_Lean_Meta_mkAppM(v___x_6337_, v___x_6340_, v___y_6333_, v___y_6334_, v___y_6335_, v___y_6336_);
return v___x_6341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6351_, lean_object* v_a_6352_, lean_object* v_a_6353_, lean_object* v_a_6354_, lean_object* v_a_6355_, lean_object* v_a_6356_){
_start:
{
lean_object* v_res_6357_; 
v_res_6357_ = l_Lean_Meta_mkEqFalse(v_h_6351_, v_a_6352_, v_a_6353_, v_a_6354_, v_a_6355_);
lean_dec(v_a_6355_);
lean_dec_ref(v_a_6354_);
lean_dec(v_a_6353_);
lean_dec_ref(v_a_6352_);
return v_res_6357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6361_, lean_object* v_a_6362_, lean_object* v_a_6363_, lean_object* v_a_6364_, lean_object* v_a_6365_){
_start:
{
lean_object* v___x_6367_; lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; 
v___x_6367_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6368_ = lean_unsigned_to_nat(1u);
v___x_6369_ = lean_mk_empty_array_with_capacity(v___x_6368_);
v___x_6370_ = lean_array_push(v___x_6369_, v_h_6361_);
v___x_6371_ = l_Lean_Meta_mkAppM(v___x_6367_, v___x_6370_, v_a_6362_, v_a_6363_, v_a_6364_, v_a_6365_);
return v___x_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6372_, lean_object* v_a_6373_, lean_object* v_a_6374_, lean_object* v_a_6375_, lean_object* v_a_6376_, lean_object* v_a_6377_){
_start:
{
lean_object* v_res_6378_; 
v_res_6378_ = l_Lean_Meta_mkEqFalse_x27(v_h_6372_, v_a_6373_, v_a_6374_, v_a_6375_, v_a_6376_);
lean_dec(v_a_6376_);
lean_dec_ref(v_a_6375_);
lean_dec(v_a_6374_);
lean_dec_ref(v_a_6373_);
return v_res_6378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6382_, lean_object* v_h_u2082_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_){
_start:
{
lean_object* v___x_6389_; lean_object* v___x_6390_; lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; 
v___x_6389_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6390_ = lean_unsigned_to_nat(2u);
v___x_6391_ = lean_mk_empty_array_with_capacity(v___x_6390_);
v___x_6392_ = lean_array_push(v___x_6391_, v_h_u2081_6382_);
v___x_6393_ = lean_array_push(v___x_6392_, v_h_u2082_6383_);
v___x_6394_ = l_Lean_Meta_mkAppM(v___x_6389_, v___x_6393_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
return v___x_6394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6395_, lean_object* v_h_u2082_6396_, lean_object* v_a_6397_, lean_object* v_a_6398_, lean_object* v_a_6399_, lean_object* v_a_6400_, lean_object* v_a_6401_){
_start:
{
lean_object* v_res_6402_; 
v_res_6402_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6395_, v_h_u2082_6396_, v_a_6397_, v_a_6398_, v_a_6399_, v_a_6400_);
lean_dec(v_a_6400_);
lean_dec_ref(v_a_6399_);
lean_dec(v_a_6398_);
lean_dec_ref(v_a_6397_);
return v_res_6402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6406_, lean_object* v_h_u2082_6407_, lean_object* v_a_6408_, lean_object* v_a_6409_, lean_object* v_a_6410_, lean_object* v_a_6411_){
_start:
{
lean_object* v___x_6413_; lean_object* v___x_6414_; lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; 
v___x_6413_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6414_ = lean_unsigned_to_nat(2u);
v___x_6415_ = lean_mk_empty_array_with_capacity(v___x_6414_);
v___x_6416_ = lean_array_push(v___x_6415_, v_h_u2081_6406_);
v___x_6417_ = lean_array_push(v___x_6416_, v_h_u2082_6407_);
v___x_6418_ = l_Lean_Meta_mkAppM(v___x_6413_, v___x_6417_, v_a_6408_, v_a_6409_, v_a_6410_, v_a_6411_);
return v___x_6418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6419_, lean_object* v_h_u2082_6420_, lean_object* v_a_6421_, lean_object* v_a_6422_, lean_object* v_a_6423_, lean_object* v_a_6424_, lean_object* v_a_6425_){
_start:
{
lean_object* v_res_6426_; 
v_res_6426_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6419_, v_h_u2082_6420_, v_a_6421_, v_a_6422_, v_a_6423_, v_a_6424_);
lean_dec(v_a_6424_);
lean_dec_ref(v_a_6423_);
lean_dec(v_a_6422_);
lean_dec_ref(v_a_6421_);
return v_res_6426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6430_, lean_object* v_h_u2082_6431_, lean_object* v_a_6432_, lean_object* v_a_6433_, lean_object* v_a_6434_, lean_object* v_a_6435_){
_start:
{
lean_object* v___x_6437_; lean_object* v___x_6438_; lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; 
v___x_6437_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6438_ = lean_unsigned_to_nat(2u);
v___x_6439_ = lean_mk_empty_array_with_capacity(v___x_6438_);
v___x_6440_ = lean_array_push(v___x_6439_, v_h_u2081_6430_);
v___x_6441_ = lean_array_push(v___x_6440_, v_h_u2082_6431_);
v___x_6442_ = l_Lean_Meta_mkAppM(v___x_6437_, v___x_6441_, v_a_6432_, v_a_6433_, v_a_6434_, v_a_6435_);
return v___x_6442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6443_, lean_object* v_h_u2082_6444_, lean_object* v_a_6445_, lean_object* v_a_6446_, lean_object* v_a_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_){
_start:
{
lean_object* v_res_6450_; 
v_res_6450_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6443_, v_h_u2082_6444_, v_a_6445_, v_a_6446_, v_a_6447_, v_a_6448_);
lean_dec(v_a_6448_);
lean_dec_ref(v_a_6447_);
lean_dec(v_a_6446_);
lean_dec_ref(v_a_6445_);
return v_res_6450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6454_, lean_object* v_a_6455_, lean_object* v_a_6456_, lean_object* v_a_6457_, lean_object* v_a_6458_){
_start:
{
lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; 
v___x_6460_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6461_ = lean_unsigned_to_nat(1u);
v___x_6462_ = lean_mk_empty_array_with_capacity(v___x_6461_);
v___x_6463_ = lean_array_push(v___x_6462_, v_h_6454_);
v___x_6464_ = l_Lean_Meta_mkAppM(v___x_6460_, v___x_6463_, v_a_6455_, v_a_6456_, v_a_6457_, v_a_6458_);
return v___x_6464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6465_, lean_object* v_a_6466_, lean_object* v_a_6467_, lean_object* v_a_6468_, lean_object* v_a_6469_, lean_object* v_a_6470_){
_start:
{
lean_object* v_res_6471_; 
v_res_6471_ = l_Lean_Meta_mkForallCongr(v_h_6465_, v_a_6466_, v_a_6467_, v_a_6468_, v_a_6469_);
lean_dec(v_a_6469_);
lean_dec_ref(v_a_6468_);
lean_dec(v_a_6467_);
lean_dec_ref(v_a_6466_);
return v_res_6471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6475_, lean_object* v_a_6476_, lean_object* v_a_6477_, lean_object* v_a_6478_, lean_object* v_a_6479_){
_start:
{
lean_object* v___y_6482_; uint8_t v___y_6483_; lean_object* v___y_6487_; lean_object* v_a_6488_; lean_object* v___x_6491_; lean_object* v___x_6492_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; 
v___x_6491_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6492_ = lean_unsigned_to_nat(1u);
v___x_6493_ = lean_mk_empty_array_with_capacity(v___x_6492_);
v___x_6494_ = lean_array_push(v___x_6493_, v_m_6475_);
v___x_6495_ = l_Lean_Meta_mkAppM(v___x_6491_, v___x_6494_, v_a_6476_, v_a_6477_, v_a_6478_, v_a_6479_);
if (lean_obj_tag(v___x_6495_) == 0)
{
lean_object* v_a_6496_; lean_object* v___x_6497_; lean_object* v___x_6498_; 
v_a_6496_ = lean_ctor_get(v___x_6495_, 0);
lean_inc(v_a_6496_);
lean_dec_ref_known(v___x_6495_, 1);
v___x_6497_ = lean_box(0);
v___x_6498_ = l_Lean_Meta_trySynthInstance(v_a_6496_, v___x_6497_, v_a_6476_, v_a_6477_, v_a_6478_, v_a_6479_);
if (lean_obj_tag(v___x_6498_) == 0)
{
lean_object* v_a_6499_; lean_object* v___x_6501_; uint8_t v_isShared_6502_; uint8_t v_isSharedCheck_6517_; 
v_a_6499_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6517_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6517_ == 0)
{
v___x_6501_ = v___x_6498_;
v_isShared_6502_ = v_isSharedCheck_6517_;
goto v_resetjp_6500_;
}
else
{
lean_inc(v_a_6499_);
lean_dec(v___x_6498_);
v___x_6501_ = lean_box(0);
v_isShared_6502_ = v_isSharedCheck_6517_;
goto v_resetjp_6500_;
}
v_resetjp_6500_:
{
if (lean_obj_tag(v_a_6499_) == 1)
{
lean_object* v_a_6503_; lean_object* v___x_6505_; uint8_t v_isShared_6506_; uint8_t v_isSharedCheck_6513_; 
v_a_6503_ = lean_ctor_get(v_a_6499_, 0);
v_isSharedCheck_6513_ = !lean_is_exclusive(v_a_6499_);
if (v_isSharedCheck_6513_ == 0)
{
v___x_6505_ = v_a_6499_;
v_isShared_6506_ = v_isSharedCheck_6513_;
goto v_resetjp_6504_;
}
else
{
lean_inc(v_a_6503_);
lean_dec(v_a_6499_);
v___x_6505_ = lean_box(0);
v_isShared_6506_ = v_isSharedCheck_6513_;
goto v_resetjp_6504_;
}
v_resetjp_6504_:
{
lean_object* v___x_6508_; 
if (v_isShared_6506_ == 0)
{
v___x_6508_ = v___x_6505_;
goto v_reusejp_6507_;
}
else
{
lean_object* v_reuseFailAlloc_6512_; 
v_reuseFailAlloc_6512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6512_, 0, v_a_6503_);
v___x_6508_ = v_reuseFailAlloc_6512_;
goto v_reusejp_6507_;
}
v_reusejp_6507_:
{
lean_object* v___x_6510_; 
if (v_isShared_6502_ == 0)
{
lean_ctor_set(v___x_6501_, 0, v___x_6508_);
v___x_6510_ = v___x_6501_;
goto v_reusejp_6509_;
}
else
{
lean_object* v_reuseFailAlloc_6511_; 
v_reuseFailAlloc_6511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6511_, 0, v___x_6508_);
v___x_6510_ = v_reuseFailAlloc_6511_;
goto v_reusejp_6509_;
}
v_reusejp_6509_:
{
return v___x_6510_;
}
}
}
}
else
{
lean_object* v___x_6515_; 
lean_dec(v_a_6499_);
if (v_isShared_6502_ == 0)
{
lean_ctor_set(v___x_6501_, 0, v___x_6497_);
v___x_6515_ = v___x_6501_;
goto v_reusejp_6514_;
}
else
{
lean_object* v_reuseFailAlloc_6516_; 
v_reuseFailAlloc_6516_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6516_, 0, v___x_6497_);
v___x_6515_ = v_reuseFailAlloc_6516_;
goto v_reusejp_6514_;
}
v_reusejp_6514_:
{
return v___x_6515_;
}
}
}
}
else
{
lean_object* v_a_6518_; lean_object* v___x_6520_; uint8_t v_isShared_6521_; uint8_t v_isSharedCheck_6525_; 
v_a_6518_ = lean_ctor_get(v___x_6498_, 0);
v_isSharedCheck_6525_ = !lean_is_exclusive(v___x_6498_);
if (v_isSharedCheck_6525_ == 0)
{
v___x_6520_ = v___x_6498_;
v_isShared_6521_ = v_isSharedCheck_6525_;
goto v_resetjp_6519_;
}
else
{
lean_inc(v_a_6518_);
lean_dec(v___x_6498_);
v___x_6520_ = lean_box(0);
v_isShared_6521_ = v_isSharedCheck_6525_;
goto v_resetjp_6519_;
}
v_resetjp_6519_:
{
lean_object* v___x_6523_; 
lean_inc(v_a_6518_);
if (v_isShared_6521_ == 0)
{
v___x_6523_ = v___x_6520_;
goto v_reusejp_6522_;
}
else
{
lean_object* v_reuseFailAlloc_6524_; 
v_reuseFailAlloc_6524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6524_, 0, v_a_6518_);
v___x_6523_ = v_reuseFailAlloc_6524_;
goto v_reusejp_6522_;
}
v_reusejp_6522_:
{
v___y_6487_ = v___x_6523_;
v_a_6488_ = v_a_6518_;
goto v___jp_6486_;
}
}
}
}
else
{
lean_object* v_a_6526_; lean_object* v___x_6528_; uint8_t v_isShared_6529_; uint8_t v_isSharedCheck_6533_; 
v_a_6526_ = lean_ctor_get(v___x_6495_, 0);
v_isSharedCheck_6533_ = !lean_is_exclusive(v___x_6495_);
if (v_isSharedCheck_6533_ == 0)
{
v___x_6528_ = v___x_6495_;
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
else
{
lean_inc(v_a_6526_);
lean_dec(v___x_6495_);
v___x_6528_ = lean_box(0);
v_isShared_6529_ = v_isSharedCheck_6533_;
goto v_resetjp_6527_;
}
v_resetjp_6527_:
{
lean_object* v___x_6531_; 
lean_inc(v_a_6526_);
if (v_isShared_6529_ == 0)
{
v___x_6531_ = v___x_6528_;
goto v_reusejp_6530_;
}
else
{
lean_object* v_reuseFailAlloc_6532_; 
v_reuseFailAlloc_6532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6532_, 0, v_a_6526_);
v___x_6531_ = v_reuseFailAlloc_6532_;
goto v_reusejp_6530_;
}
v_reusejp_6530_:
{
v___y_6487_ = v___x_6531_;
v_a_6488_ = v_a_6526_;
goto v___jp_6486_;
}
}
}
v___jp_6481_:
{
if (v___y_6483_ == 0)
{
lean_object* v___x_6484_; lean_object* v___x_6485_; 
lean_dec_ref(v___y_6482_);
v___x_6484_ = lean_box(0);
v___x_6485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6485_, 0, v___x_6484_);
return v___x_6485_;
}
else
{
return v___y_6482_;
}
}
v___jp_6486_:
{
uint8_t v___x_6489_; 
v___x_6489_ = l_Lean_Exception_isInterrupt(v_a_6488_);
if (v___x_6489_ == 0)
{
uint8_t v___x_6490_; 
v___x_6490_ = l_Lean_Exception_isRuntime(v_a_6488_);
v___y_6482_ = v___y_6487_;
v___y_6483_ = v___x_6490_;
goto v___jp_6481_;
}
else
{
lean_dec_ref(v_a_6488_);
v___y_6482_ = v___y_6487_;
v___y_6483_ = v___x_6489_;
goto v___jp_6481_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6534_, lean_object* v_a_6535_, lean_object* v_a_6536_, lean_object* v_a_6537_, lean_object* v_a_6538_, lean_object* v_a_6539_){
_start:
{
lean_object* v_res_6540_; 
v_res_6540_ = l_Lean_Meta_isMonad_x3f(v_m_6534_, v_a_6535_, v_a_6536_, v_a_6537_, v_a_6538_);
lean_dec(v_a_6538_);
lean_dec_ref(v_a_6537_);
lean_dec(v_a_6536_);
lean_dec_ref(v_a_6535_);
return v_res_6540_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6548_, lean_object* v_n_6549_, lean_object* v_a_6550_, lean_object* v_a_6551_, lean_object* v_a_6552_, lean_object* v_a_6553_){
_start:
{
lean_object* v___x_6555_; 
lean_inc_ref(v_type_6548_);
v___x_6555_ = l_Lean_Meta_getDecLevel(v_type_6548_, v_a_6550_, v_a_6551_, v_a_6552_, v_a_6553_);
if (lean_obj_tag(v___x_6555_) == 0)
{
lean_object* v_a_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; 
v_a_6556_ = lean_ctor_get(v___x_6555_, 0);
lean_inc(v_a_6556_);
lean_dec_ref_known(v___x_6555_, 1);
v___x_6557_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6558_ = lean_box(0);
v___x_6559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6559_, 0, v_a_6556_);
lean_ctor_set(v___x_6559_, 1, v___x_6558_);
lean_inc_ref(v___x_6559_);
v___x_6560_ = l_Lean_mkConst(v___x_6557_, v___x_6559_);
v___x_6561_ = l_Lean_mkRawNatLit(v_n_6549_);
lean_inc_ref(v___x_6561_);
lean_inc_ref(v_type_6548_);
v___x_6562_ = l_Lean_mkAppB(v___x_6560_, v_type_6548_, v___x_6561_);
v___x_6563_ = lean_box(0);
v___x_6564_ = l_Lean_Meta_synthInstance(v___x_6562_, v___x_6563_, v_a_6550_, v_a_6551_, v_a_6552_, v_a_6553_);
if (lean_obj_tag(v___x_6564_) == 0)
{
lean_object* v_a_6565_; lean_object* v___x_6567_; uint8_t v_isShared_6568_; uint8_t v_isSharedCheck_6575_; 
v_a_6565_ = lean_ctor_get(v___x_6564_, 0);
v_isSharedCheck_6575_ = !lean_is_exclusive(v___x_6564_);
if (v_isSharedCheck_6575_ == 0)
{
v___x_6567_ = v___x_6564_;
v_isShared_6568_ = v_isSharedCheck_6575_;
goto v_resetjp_6566_;
}
else
{
lean_inc(v_a_6565_);
lean_dec(v___x_6564_);
v___x_6567_ = lean_box(0);
v_isShared_6568_ = v_isSharedCheck_6575_;
goto v_resetjp_6566_;
}
v_resetjp_6566_:
{
lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; lean_object* v___x_6573_; 
v___x_6569_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6570_ = l_Lean_mkConst(v___x_6569_, v___x_6559_);
v___x_6571_ = l_Lean_mkApp3(v___x_6570_, v_type_6548_, v___x_6561_, v_a_6565_);
if (v_isShared_6568_ == 0)
{
lean_ctor_set(v___x_6567_, 0, v___x_6571_);
v___x_6573_ = v___x_6567_;
goto v_reusejp_6572_;
}
else
{
lean_object* v_reuseFailAlloc_6574_; 
v_reuseFailAlloc_6574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6574_, 0, v___x_6571_);
v___x_6573_ = v_reuseFailAlloc_6574_;
goto v_reusejp_6572_;
}
v_reusejp_6572_:
{
return v___x_6573_;
}
}
}
else
{
lean_dec_ref(v___x_6561_);
lean_dec_ref_known(v___x_6559_, 2);
lean_dec_ref(v_type_6548_);
return v___x_6564_;
}
}
else
{
lean_object* v_a_6576_; lean_object* v___x_6578_; uint8_t v_isShared_6579_; uint8_t v_isSharedCheck_6583_; 
lean_dec(v_n_6549_);
lean_dec_ref(v_type_6548_);
v_a_6576_ = lean_ctor_get(v___x_6555_, 0);
v_isSharedCheck_6583_ = !lean_is_exclusive(v___x_6555_);
if (v_isSharedCheck_6583_ == 0)
{
v___x_6578_ = v___x_6555_;
v_isShared_6579_ = v_isSharedCheck_6583_;
goto v_resetjp_6577_;
}
else
{
lean_inc(v_a_6576_);
lean_dec(v___x_6555_);
v___x_6578_ = lean_box(0);
v_isShared_6579_ = v_isSharedCheck_6583_;
goto v_resetjp_6577_;
}
v_resetjp_6577_:
{
lean_object* v___x_6581_; 
if (v_isShared_6579_ == 0)
{
v___x_6581_ = v___x_6578_;
goto v_reusejp_6580_;
}
else
{
lean_object* v_reuseFailAlloc_6582_; 
v_reuseFailAlloc_6582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6582_, 0, v_a_6576_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6584_, lean_object* v_n_6585_, lean_object* v_a_6586_, lean_object* v_a_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_){
_start:
{
lean_object* v_res_6591_; 
v_res_6591_ = l_Lean_Meta_mkNumeral(v_type_6584_, v_n_6585_, v_a_6586_, v_a_6587_, v_a_6588_, v_a_6589_);
lean_dec(v_a_6589_);
lean_dec_ref(v_a_6588_);
lean_dec(v_a_6587_);
lean_dec_ref(v_a_6586_);
return v_res_6591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6592_, lean_object* v_opName_6593_, lean_object* v_a_6594_, lean_object* v_b_6595_, lean_object* v_a_6596_, lean_object* v_a_6597_, lean_object* v_a_6598_, lean_object* v_a_6599_){
_start:
{
lean_object* v___x_6601_; 
lean_inc(v_a_6599_);
lean_inc_ref(v_a_6598_);
lean_inc(v_a_6597_);
lean_inc_ref(v_a_6596_);
lean_inc_ref(v_a_6594_);
v___x_6601_ = lean_infer_type(v_a_6594_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_);
if (lean_obj_tag(v___x_6601_) == 0)
{
lean_object* v_a_6602_; lean_object* v___x_6603_; 
v_a_6602_ = lean_ctor_get(v___x_6601_, 0);
lean_inc_n(v_a_6602_, 2);
lean_dec_ref_known(v___x_6601_, 1);
v___x_6603_ = l_Lean_Meta_getDecLevel(v_a_6602_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_);
if (lean_obj_tag(v___x_6603_) == 0)
{
lean_object* v_a_6604_; lean_object* v___x_6605_; lean_object* v___x_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; 
v_a_6604_ = lean_ctor_get(v___x_6603_, 0);
lean_inc_n(v_a_6604_, 3);
lean_dec_ref_known(v___x_6603_, 1);
v___x_6605_ = lean_box(0);
v___x_6606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6606_, 0, v_a_6604_);
lean_ctor_set(v___x_6606_, 1, v___x_6605_);
v___x_6607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6607_, 0, v_a_6604_);
lean_ctor_set(v___x_6607_, 1, v___x_6606_);
v___x_6608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6608_, 0, v_a_6604_);
lean_ctor_set(v___x_6608_, 1, v___x_6607_);
lean_inc_ref(v___x_6608_);
v___x_6609_ = l_Lean_mkConst(v_className_6592_, v___x_6608_);
lean_inc_n(v_a_6602_, 3);
v___x_6610_ = l_Lean_mkApp3(v___x_6609_, v_a_6602_, v_a_6602_, v_a_6602_);
v___x_6611_ = lean_box(0);
v___x_6612_ = l_Lean_Meta_synthInstance(v___x_6610_, v___x_6611_, v_a_6596_, v_a_6597_, v_a_6598_, v_a_6599_);
if (lean_obj_tag(v___x_6612_) == 0)
{
lean_object* v_a_6613_; lean_object* v___x_6615_; uint8_t v_isShared_6616_; uint8_t v_isSharedCheck_6622_; 
v_a_6613_ = lean_ctor_get(v___x_6612_, 0);
v_isSharedCheck_6622_ = !lean_is_exclusive(v___x_6612_);
if (v_isSharedCheck_6622_ == 0)
{
v___x_6615_ = v___x_6612_;
v_isShared_6616_ = v_isSharedCheck_6622_;
goto v_resetjp_6614_;
}
else
{
lean_inc(v_a_6613_);
lean_dec(v___x_6612_);
v___x_6615_ = lean_box(0);
v_isShared_6616_ = v_isSharedCheck_6622_;
goto v_resetjp_6614_;
}
v_resetjp_6614_:
{
lean_object* v___x_6617_; lean_object* v___x_6618_; lean_object* v___x_6620_; 
v___x_6617_ = l_Lean_mkConst(v_opName_6593_, v___x_6608_);
lean_inc_n(v_a_6602_, 2);
v___x_6618_ = l_Lean_mkApp6(v___x_6617_, v_a_6602_, v_a_6602_, v_a_6602_, v_a_6613_, v_a_6594_, v_b_6595_);
if (v_isShared_6616_ == 0)
{
lean_ctor_set(v___x_6615_, 0, v___x_6618_);
v___x_6620_ = v___x_6615_;
goto v_reusejp_6619_;
}
else
{
lean_object* v_reuseFailAlloc_6621_; 
v_reuseFailAlloc_6621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6621_, 0, v___x_6618_);
v___x_6620_ = v_reuseFailAlloc_6621_;
goto v_reusejp_6619_;
}
v_reusejp_6619_:
{
return v___x_6620_;
}
}
}
else
{
lean_dec_ref_known(v___x_6608_, 2);
lean_dec(v_a_6602_);
lean_dec_ref(v_b_6595_);
lean_dec_ref(v_a_6594_);
lean_dec(v_opName_6593_);
return v___x_6612_;
}
}
else
{
lean_object* v_a_6623_; lean_object* v___x_6625_; uint8_t v_isShared_6626_; uint8_t v_isSharedCheck_6630_; 
lean_dec(v_a_6602_);
lean_dec_ref(v_b_6595_);
lean_dec_ref(v_a_6594_);
lean_dec(v_opName_6593_);
lean_dec(v_className_6592_);
v_a_6623_ = lean_ctor_get(v___x_6603_, 0);
v_isSharedCheck_6630_ = !lean_is_exclusive(v___x_6603_);
if (v_isSharedCheck_6630_ == 0)
{
v___x_6625_ = v___x_6603_;
v_isShared_6626_ = v_isSharedCheck_6630_;
goto v_resetjp_6624_;
}
else
{
lean_inc(v_a_6623_);
lean_dec(v___x_6603_);
v___x_6625_ = lean_box(0);
v_isShared_6626_ = v_isSharedCheck_6630_;
goto v_resetjp_6624_;
}
v_resetjp_6624_:
{
lean_object* v___x_6628_; 
if (v_isShared_6626_ == 0)
{
v___x_6628_ = v___x_6625_;
goto v_reusejp_6627_;
}
else
{
lean_object* v_reuseFailAlloc_6629_; 
v_reuseFailAlloc_6629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6629_, 0, v_a_6623_);
v___x_6628_ = v_reuseFailAlloc_6629_;
goto v_reusejp_6627_;
}
v_reusejp_6627_:
{
return v___x_6628_;
}
}
}
}
else
{
lean_dec_ref(v_b_6595_);
lean_dec_ref(v_a_6594_);
lean_dec(v_opName_6593_);
lean_dec(v_className_6592_);
return v___x_6601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6631_, lean_object* v_opName_6632_, lean_object* v_a_6633_, lean_object* v_b_6634_, lean_object* v_a_6635_, lean_object* v_a_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_){
_start:
{
lean_object* v_res_6640_; 
v_res_6640_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6631_, v_opName_6632_, v_a_6633_, v_b_6634_, v_a_6635_, v_a_6636_, v_a_6637_, v_a_6638_);
lean_dec(v_a_6638_);
lean_dec_ref(v_a_6637_);
lean_dec(v_a_6636_);
lean_dec_ref(v_a_6635_);
return v_res_6640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6648_, lean_object* v_b_6649_, lean_object* v_a_6650_, lean_object* v_a_6651_, lean_object* v_a_6652_, lean_object* v_a_6653_){
_start:
{
lean_object* v___x_6655_; lean_object* v___x_6656_; lean_object* v___x_6657_; 
v___x_6655_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6656_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6657_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6655_, v___x_6656_, v_a_6648_, v_b_6649_, v_a_6650_, v_a_6651_, v_a_6652_, v_a_6653_);
return v___x_6657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6658_, lean_object* v_b_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_){
_start:
{
lean_object* v_res_6665_; 
v_res_6665_ = l_Lean_Meta_mkAdd(v_a_6658_, v_b_6659_, v_a_6660_, v_a_6661_, v_a_6662_, v_a_6663_);
lean_dec(v_a_6663_);
lean_dec_ref(v_a_6662_);
lean_dec(v_a_6661_);
lean_dec_ref(v_a_6660_);
return v_res_6665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6673_, lean_object* v_b_6674_, lean_object* v_a_6675_, lean_object* v_a_6676_, lean_object* v_a_6677_, lean_object* v_a_6678_){
_start:
{
lean_object* v___x_6680_; lean_object* v___x_6681_; lean_object* v___x_6682_; 
v___x_6680_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6681_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6682_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6680_, v___x_6681_, v_a_6673_, v_b_6674_, v_a_6675_, v_a_6676_, v_a_6677_, v_a_6678_);
return v___x_6682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6683_, lean_object* v_b_6684_, lean_object* v_a_6685_, lean_object* v_a_6686_, lean_object* v_a_6687_, lean_object* v_a_6688_, lean_object* v_a_6689_){
_start:
{
lean_object* v_res_6690_; 
v_res_6690_ = l_Lean_Meta_mkSub(v_a_6683_, v_b_6684_, v_a_6685_, v_a_6686_, v_a_6687_, v_a_6688_);
lean_dec(v_a_6688_);
lean_dec_ref(v_a_6687_);
lean_dec(v_a_6686_);
lean_dec_ref(v_a_6685_);
return v_res_6690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6698_, lean_object* v_b_6699_, lean_object* v_a_6700_, lean_object* v_a_6701_, lean_object* v_a_6702_, lean_object* v_a_6703_){
_start:
{
lean_object* v___x_6705_; lean_object* v___x_6706_; lean_object* v___x_6707_; 
v___x_6705_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6706_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6707_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6705_, v___x_6706_, v_a_6698_, v_b_6699_, v_a_6700_, v_a_6701_, v_a_6702_, v_a_6703_);
return v___x_6707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6708_, lean_object* v_b_6709_, lean_object* v_a_6710_, lean_object* v_a_6711_, lean_object* v_a_6712_, lean_object* v_a_6713_, lean_object* v_a_6714_){
_start:
{
lean_object* v_res_6715_; 
v_res_6715_ = l_Lean_Meta_mkMul(v_a_6708_, v_b_6709_, v_a_6710_, v_a_6711_, v_a_6712_, v_a_6713_);
lean_dec(v_a_6713_);
lean_dec_ref(v_a_6712_);
lean_dec(v_a_6711_);
lean_dec_ref(v_a_6710_);
return v_res_6715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6716_, lean_object* v_rName_6717_, lean_object* v_a_6718_, lean_object* v_b_6719_, lean_object* v_a_6720_, lean_object* v_a_6721_, lean_object* v_a_6722_, lean_object* v_a_6723_){
_start:
{
lean_object* v___x_6725_; 
lean_inc(v_a_6723_);
lean_inc_ref(v_a_6722_);
lean_inc(v_a_6721_);
lean_inc_ref(v_a_6720_);
lean_inc_ref(v_a_6718_);
v___x_6725_ = lean_infer_type(v_a_6718_, v_a_6720_, v_a_6721_, v_a_6722_, v_a_6723_);
if (lean_obj_tag(v___x_6725_) == 0)
{
lean_object* v_a_6726_; lean_object* v___x_6727_; 
v_a_6726_ = lean_ctor_get(v___x_6725_, 0);
lean_inc_n(v_a_6726_, 2);
lean_dec_ref_known(v___x_6725_, 1);
v___x_6727_ = l_Lean_Meta_getDecLevel(v_a_6726_, v_a_6720_, v_a_6721_, v_a_6722_, v_a_6723_);
if (lean_obj_tag(v___x_6727_) == 0)
{
lean_object* v_a_6728_; lean_object* v___x_6729_; lean_object* v___x_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; lean_object* v___x_6733_; lean_object* v___x_6734_; 
v_a_6728_ = lean_ctor_get(v___x_6727_, 0);
lean_inc(v_a_6728_);
lean_dec_ref_known(v___x_6727_, 1);
v___x_6729_ = lean_box(0);
v___x_6730_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6730_, 0, v_a_6728_);
lean_ctor_set(v___x_6730_, 1, v___x_6729_);
lean_inc_ref(v___x_6730_);
v___x_6731_ = l_Lean_mkConst(v_className_6716_, v___x_6730_);
lean_inc(v_a_6726_);
v___x_6732_ = l_Lean_Expr_app___override(v___x_6731_, v_a_6726_);
v___x_6733_ = lean_box(0);
v___x_6734_ = l_Lean_Meta_synthInstance(v___x_6732_, v___x_6733_, v_a_6720_, v_a_6721_, v_a_6722_, v_a_6723_);
if (lean_obj_tag(v___x_6734_) == 0)
{
lean_object* v_a_6735_; lean_object* v___x_6737_; uint8_t v_isShared_6738_; uint8_t v_isSharedCheck_6744_; 
v_a_6735_ = lean_ctor_get(v___x_6734_, 0);
v_isSharedCheck_6744_ = !lean_is_exclusive(v___x_6734_);
if (v_isSharedCheck_6744_ == 0)
{
v___x_6737_ = v___x_6734_;
v_isShared_6738_ = v_isSharedCheck_6744_;
goto v_resetjp_6736_;
}
else
{
lean_inc(v_a_6735_);
lean_dec(v___x_6734_);
v___x_6737_ = lean_box(0);
v_isShared_6738_ = v_isSharedCheck_6744_;
goto v_resetjp_6736_;
}
v_resetjp_6736_:
{
lean_object* v___x_6739_; lean_object* v___x_6740_; lean_object* v___x_6742_; 
v___x_6739_ = l_Lean_mkConst(v_rName_6717_, v___x_6730_);
v___x_6740_ = l_Lean_mkApp4(v___x_6739_, v_a_6726_, v_a_6735_, v_a_6718_, v_b_6719_);
if (v_isShared_6738_ == 0)
{
lean_ctor_set(v___x_6737_, 0, v___x_6740_);
v___x_6742_ = v___x_6737_;
goto v_reusejp_6741_;
}
else
{
lean_object* v_reuseFailAlloc_6743_; 
v_reuseFailAlloc_6743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6743_, 0, v___x_6740_);
v___x_6742_ = v_reuseFailAlloc_6743_;
goto v_reusejp_6741_;
}
v_reusejp_6741_:
{
return v___x_6742_;
}
}
}
else
{
lean_dec_ref_known(v___x_6730_, 2);
lean_dec(v_a_6726_);
lean_dec_ref(v_b_6719_);
lean_dec_ref(v_a_6718_);
lean_dec(v_rName_6717_);
return v___x_6734_;
}
}
else
{
lean_object* v_a_6745_; lean_object* v___x_6747_; uint8_t v_isShared_6748_; uint8_t v_isSharedCheck_6752_; 
lean_dec(v_a_6726_);
lean_dec_ref(v_b_6719_);
lean_dec_ref(v_a_6718_);
lean_dec(v_rName_6717_);
lean_dec(v_className_6716_);
v_a_6745_ = lean_ctor_get(v___x_6727_, 0);
v_isSharedCheck_6752_ = !lean_is_exclusive(v___x_6727_);
if (v_isSharedCheck_6752_ == 0)
{
v___x_6747_ = v___x_6727_;
v_isShared_6748_ = v_isSharedCheck_6752_;
goto v_resetjp_6746_;
}
else
{
lean_inc(v_a_6745_);
lean_dec(v___x_6727_);
v___x_6747_ = lean_box(0);
v_isShared_6748_ = v_isSharedCheck_6752_;
goto v_resetjp_6746_;
}
v_resetjp_6746_:
{
lean_object* v___x_6750_; 
if (v_isShared_6748_ == 0)
{
v___x_6750_ = v___x_6747_;
goto v_reusejp_6749_;
}
else
{
lean_object* v_reuseFailAlloc_6751_; 
v_reuseFailAlloc_6751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6751_, 0, v_a_6745_);
v___x_6750_ = v_reuseFailAlloc_6751_;
goto v_reusejp_6749_;
}
v_reusejp_6749_:
{
return v___x_6750_;
}
}
}
}
else
{
lean_dec_ref(v_b_6719_);
lean_dec_ref(v_a_6718_);
lean_dec(v_rName_6717_);
lean_dec(v_className_6716_);
return v___x_6725_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6753_, lean_object* v_rName_6754_, lean_object* v_a_6755_, lean_object* v_b_6756_, lean_object* v_a_6757_, lean_object* v_a_6758_, lean_object* v_a_6759_, lean_object* v_a_6760_, lean_object* v_a_6761_){
_start:
{
lean_object* v_res_6762_; 
v_res_6762_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6753_, v_rName_6754_, v_a_6755_, v_b_6756_, v_a_6757_, v_a_6758_, v_a_6759_, v_a_6760_);
lean_dec(v_a_6760_);
lean_dec_ref(v_a_6759_);
lean_dec(v_a_6758_);
lean_dec_ref(v_a_6757_);
return v_res_6762_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6765_, lean_object* v_b_6766_, lean_object* v_a_6767_, lean_object* v_a_6768_, lean_object* v_a_6769_, lean_object* v_a_6770_){
_start:
{
lean_object* v___x_6772_; lean_object* v___x_6773_; lean_object* v___x_6774_; 
v___x_6772_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6773_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6774_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6772_, v___x_6773_, v_a_6765_, v_b_6766_, v_a_6767_, v_a_6768_, v_a_6769_, v_a_6770_);
return v___x_6774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6775_, lean_object* v_b_6776_, lean_object* v_a_6777_, lean_object* v_a_6778_, lean_object* v_a_6779_, lean_object* v_a_6780_, lean_object* v_a_6781_){
_start:
{
lean_object* v_res_6782_; 
v_res_6782_ = l_Lean_Meta_mkLE(v_a_6775_, v_b_6776_, v_a_6777_, v_a_6778_, v_a_6779_, v_a_6780_);
lean_dec(v_a_6780_);
lean_dec_ref(v_a_6779_);
lean_dec(v_a_6778_);
lean_dec_ref(v_a_6777_);
return v_res_6782_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6785_, lean_object* v_b_6786_, lean_object* v_a_6787_, lean_object* v_a_6788_, lean_object* v_a_6789_, lean_object* v_a_6790_){
_start:
{
lean_object* v___x_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; 
v___x_6792_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6793_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6794_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6792_, v___x_6793_, v_a_6785_, v_b_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_);
return v___x_6794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6795_, lean_object* v_b_6796_, lean_object* v_a_6797_, lean_object* v_a_6798_, lean_object* v_a_6799_, lean_object* v_a_6800_, lean_object* v_a_6801_){
_start:
{
lean_object* v_res_6802_; 
v_res_6802_ = l_Lean_Meta_mkLT(v_a_6795_, v_b_6796_, v_a_6797_, v_a_6798_, v_a_6799_, v_a_6800_);
lean_dec(v_a_6800_);
lean_dec_ref(v_a_6799_);
lean_dec(v_a_6798_);
lean_dec_ref(v_a_6797_);
return v_res_6802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6808_, lean_object* v_a_6809_, lean_object* v_a_6810_, lean_object* v_a_6811_, lean_object* v_a_6812_){
_start:
{
lean_object* v___x_6814_; lean_object* v___x_6815_; uint8_t v___x_6816_; 
v___x_6814_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6815_ = lean_unsigned_to_nat(3u);
v___x_6816_ = l_Lean_Expr_isAppOfArity(v_h_6808_, v___x_6814_, v___x_6815_);
if (v___x_6816_ == 0)
{
lean_object* v___x_6817_; lean_object* v___x_6818_; lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; 
v___x_6817_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6818_ = lean_unsigned_to_nat(1u);
v___x_6819_ = lean_mk_empty_array_with_capacity(v___x_6818_);
v___x_6820_ = lean_array_push(v___x_6819_, v_h_6808_);
v___x_6821_ = l_Lean_Meta_mkAppM(v___x_6817_, v___x_6820_, v_a_6809_, v_a_6810_, v_a_6811_, v_a_6812_);
return v___x_6821_;
}
else
{
lean_object* v___x_6822_; lean_object* v___x_6823_; 
v___x_6822_ = l_Lean_Expr_appArg_x21(v_h_6808_);
lean_dec_ref(v_h_6808_);
v___x_6823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6823_, 0, v___x_6822_);
return v___x_6823_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6824_, lean_object* v_a_6825_, lean_object* v_a_6826_, lean_object* v_a_6827_, lean_object* v_a_6828_, lean_object* v_a_6829_){
_start:
{
lean_object* v_res_6830_; 
v_res_6830_ = l_Lean_Meta_mkIffOfEq(v_h_6824_, v_a_6825_, v_a_6826_, v_a_6827_, v_a_6828_);
lean_dec(v_a_6828_);
lean_dec_ref(v_a_6827_);
lean_dec(v_a_6826_);
lean_dec_ref(v_a_6825_);
return v_res_6830_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; 
v___x_6836_ = lean_box(0);
v___x_6837_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6838_ = l_Lean_mkConst(v___x_6837_, v___x_6836_);
return v___x_6838_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6841_; lean_object* v___x_6842_; lean_object* v___x_6843_; 
v___x_6841_ = lean_box(0);
v___x_6842_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6843_ = l_Lean_mkConst(v___x_6842_, v___x_6841_);
return v___x_6843_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6844_; lean_object* v___x_6845_; lean_object* v___x_6846_; 
v___x_6844_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6845_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6846_, 0, v___x_6845_);
lean_ctor_set(v___x_6846_, 1, v___x_6844_);
return v___x_6846_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6851_; lean_object* v___x_6852_; lean_object* v___x_6853_; 
v___x_6851_ = lean_box(0);
v___x_6852_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6853_ = l_Lean_mkConst(v___x_6852_, v___x_6851_);
return v___x_6853_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6856_; lean_object* v___x_6857_; lean_object* v___x_6858_; 
v___x_6856_ = lean_box(0);
v___x_6857_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6858_ = l_Lean_mkConst(v___x_6857_, v___x_6856_);
return v___x_6858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6859_, lean_object* v_a_6860_, lean_object* v_a_6861_, lean_object* v_a_6862_, lean_object* v_a_6863_){
_start:
{
if (lean_obj_tag(v_a_6859_) == 0)
{
lean_object* v___x_6865_; lean_object* v___x_6866_; 
v___x_6865_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6866_, 0, v___x_6865_);
return v___x_6866_;
}
else
{
lean_object* v_tail_6867_; 
v_tail_6867_ = lean_ctor_get(v_a_6859_, 1);
if (lean_obj_tag(v_tail_6867_) == 0)
{
lean_object* v_head_6868_; lean_object* v___x_6870_; uint8_t v_isShared_6871_; uint8_t v_isSharedCheck_6892_; 
v_head_6868_ = lean_ctor_get(v_a_6859_, 0);
v_isSharedCheck_6892_ = !lean_is_exclusive(v_a_6859_);
if (v_isSharedCheck_6892_ == 0)
{
lean_object* v_unused_6893_; 
v_unused_6893_ = lean_ctor_get(v_a_6859_, 1);
lean_dec(v_unused_6893_);
v___x_6870_ = v_a_6859_;
v_isShared_6871_ = v_isSharedCheck_6892_;
goto v_resetjp_6869_;
}
else
{
lean_inc(v_head_6868_);
lean_dec(v_a_6859_);
v___x_6870_ = lean_box(0);
v_isShared_6871_ = v_isSharedCheck_6892_;
goto v_resetjp_6869_;
}
v_resetjp_6869_:
{
lean_object* v___x_6872_; 
lean_inc(v_a_6863_);
lean_inc_ref(v_a_6862_);
lean_inc(v_a_6861_);
lean_inc_ref(v_a_6860_);
lean_inc(v_head_6868_);
v___x_6872_ = lean_infer_type(v_head_6868_, v_a_6860_, v_a_6861_, v_a_6862_, v_a_6863_);
if (lean_obj_tag(v___x_6872_) == 0)
{
lean_object* v_a_6873_; lean_object* v___x_6875_; uint8_t v_isShared_6876_; uint8_t v_isSharedCheck_6883_; 
v_a_6873_ = lean_ctor_get(v___x_6872_, 0);
v_isSharedCheck_6883_ = !lean_is_exclusive(v___x_6872_);
if (v_isSharedCheck_6883_ == 0)
{
v___x_6875_ = v___x_6872_;
v_isShared_6876_ = v_isSharedCheck_6883_;
goto v_resetjp_6874_;
}
else
{
lean_inc(v_a_6873_);
lean_dec(v___x_6872_);
v___x_6875_ = lean_box(0);
v_isShared_6876_ = v_isSharedCheck_6883_;
goto v_resetjp_6874_;
}
v_resetjp_6874_:
{
lean_object* v___x_6878_; 
if (v_isShared_6871_ == 0)
{
lean_ctor_set_tag(v___x_6870_, 0);
lean_ctor_set(v___x_6870_, 1, v_a_6873_);
v___x_6878_ = v___x_6870_;
goto v_reusejp_6877_;
}
else
{
lean_object* v_reuseFailAlloc_6882_; 
v_reuseFailAlloc_6882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6882_, 0, v_head_6868_);
lean_ctor_set(v_reuseFailAlloc_6882_, 1, v_a_6873_);
v___x_6878_ = v_reuseFailAlloc_6882_;
goto v_reusejp_6877_;
}
v_reusejp_6877_:
{
lean_object* v___x_6880_; 
if (v_isShared_6876_ == 0)
{
lean_ctor_set(v___x_6875_, 0, v___x_6878_);
v___x_6880_ = v___x_6875_;
goto v_reusejp_6879_;
}
else
{
lean_object* v_reuseFailAlloc_6881_; 
v_reuseFailAlloc_6881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6881_, 0, v___x_6878_);
v___x_6880_ = v_reuseFailAlloc_6881_;
goto v_reusejp_6879_;
}
v_reusejp_6879_:
{
return v___x_6880_;
}
}
}
}
else
{
lean_object* v_a_6884_; lean_object* v___x_6886_; uint8_t v_isShared_6887_; uint8_t v_isSharedCheck_6891_; 
lean_del_object(v___x_6870_);
lean_dec(v_head_6868_);
v_a_6884_ = lean_ctor_get(v___x_6872_, 0);
v_isSharedCheck_6891_ = !lean_is_exclusive(v___x_6872_);
if (v_isSharedCheck_6891_ == 0)
{
v___x_6886_ = v___x_6872_;
v_isShared_6887_ = v_isSharedCheck_6891_;
goto v_resetjp_6885_;
}
else
{
lean_inc(v_a_6884_);
lean_dec(v___x_6872_);
v___x_6886_ = lean_box(0);
v_isShared_6887_ = v_isSharedCheck_6891_;
goto v_resetjp_6885_;
}
v_resetjp_6885_:
{
lean_object* v___x_6889_; 
if (v_isShared_6887_ == 0)
{
v___x_6889_ = v___x_6886_;
goto v_reusejp_6888_;
}
else
{
lean_object* v_reuseFailAlloc_6890_; 
v_reuseFailAlloc_6890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6890_, 0, v_a_6884_);
v___x_6889_ = v_reuseFailAlloc_6890_;
goto v_reusejp_6888_;
}
v_reusejp_6888_:
{
return v___x_6889_;
}
}
}
}
}
else
{
lean_object* v_head_6894_; lean_object* v___x_6895_; 
lean_inc(v_tail_6867_);
v_head_6894_ = lean_ctor_get(v_a_6859_, 0);
lean_inc(v_head_6894_);
lean_dec_ref_known(v_a_6859_, 2);
v___x_6895_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6867_, v_a_6860_, v_a_6861_, v_a_6862_, v_a_6863_);
if (lean_obj_tag(v___x_6895_) == 0)
{
lean_object* v_a_6896_; lean_object* v_fst_6897_; lean_object* v_snd_6898_; lean_object* v___x_6900_; uint8_t v_isShared_6901_; uint8_t v_isSharedCheck_6926_; 
v_a_6896_ = lean_ctor_get(v___x_6895_, 0);
lean_inc(v_a_6896_);
lean_dec_ref_known(v___x_6895_, 1);
v_fst_6897_ = lean_ctor_get(v_a_6896_, 0);
v_snd_6898_ = lean_ctor_get(v_a_6896_, 1);
v_isSharedCheck_6926_ = !lean_is_exclusive(v_a_6896_);
if (v_isSharedCheck_6926_ == 0)
{
v___x_6900_ = v_a_6896_;
v_isShared_6901_ = v_isSharedCheck_6926_;
goto v_resetjp_6899_;
}
else
{
lean_inc(v_snd_6898_);
lean_inc(v_fst_6897_);
lean_dec(v_a_6896_);
v___x_6900_ = lean_box(0);
v_isShared_6901_ = v_isSharedCheck_6926_;
goto v_resetjp_6899_;
}
v_resetjp_6899_:
{
lean_object* v___x_6902_; 
lean_inc(v_a_6863_);
lean_inc_ref(v_a_6862_);
lean_inc(v_a_6861_);
lean_inc_ref(v_a_6860_);
lean_inc(v_head_6894_);
v___x_6902_ = lean_infer_type(v_head_6894_, v_a_6860_, v_a_6861_, v_a_6862_, v_a_6863_);
if (lean_obj_tag(v___x_6902_) == 0)
{
lean_object* v_a_6903_; lean_object* v___x_6905_; uint8_t v_isShared_6906_; uint8_t v_isSharedCheck_6917_; 
v_a_6903_ = lean_ctor_get(v___x_6902_, 0);
v_isSharedCheck_6917_ = !lean_is_exclusive(v___x_6902_);
if (v_isSharedCheck_6917_ == 0)
{
v___x_6905_ = v___x_6902_;
v_isShared_6906_ = v_isSharedCheck_6917_;
goto v_resetjp_6904_;
}
else
{
lean_inc(v_a_6903_);
lean_dec(v___x_6902_);
v___x_6905_ = lean_box(0);
v_isShared_6906_ = v_isSharedCheck_6917_;
goto v_resetjp_6904_;
}
v_resetjp_6904_:
{
lean_object* v___x_6907_; lean_object* v___x_6908_; lean_object* v___x_6909_; lean_object* v___x_6910_; lean_object* v___x_6912_; 
v___x_6907_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6898_);
lean_inc(v_a_6903_);
v___x_6908_ = l_Lean_mkApp4(v___x_6907_, v_a_6903_, v_snd_6898_, v_head_6894_, v_fst_6897_);
v___x_6909_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6910_ = l_Lean_mkAppB(v___x_6909_, v_a_6903_, v_snd_6898_);
if (v_isShared_6901_ == 0)
{
lean_ctor_set(v___x_6900_, 1, v___x_6910_);
lean_ctor_set(v___x_6900_, 0, v___x_6908_);
v___x_6912_ = v___x_6900_;
goto v_reusejp_6911_;
}
else
{
lean_object* v_reuseFailAlloc_6916_; 
v_reuseFailAlloc_6916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6916_, 0, v___x_6908_);
lean_ctor_set(v_reuseFailAlloc_6916_, 1, v___x_6910_);
v___x_6912_ = v_reuseFailAlloc_6916_;
goto v_reusejp_6911_;
}
v_reusejp_6911_:
{
lean_object* v___x_6914_; 
if (v_isShared_6906_ == 0)
{
lean_ctor_set(v___x_6905_, 0, v___x_6912_);
v___x_6914_ = v___x_6905_;
goto v_reusejp_6913_;
}
else
{
lean_object* v_reuseFailAlloc_6915_; 
v_reuseFailAlloc_6915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6915_, 0, v___x_6912_);
v___x_6914_ = v_reuseFailAlloc_6915_;
goto v_reusejp_6913_;
}
v_reusejp_6913_:
{
return v___x_6914_;
}
}
}
}
else
{
lean_object* v_a_6918_; lean_object* v___x_6920_; uint8_t v_isShared_6921_; uint8_t v_isSharedCheck_6925_; 
lean_del_object(v___x_6900_);
lean_dec(v_snd_6898_);
lean_dec(v_fst_6897_);
lean_dec(v_head_6894_);
v_a_6918_ = lean_ctor_get(v___x_6902_, 0);
v_isSharedCheck_6925_ = !lean_is_exclusive(v___x_6902_);
if (v_isSharedCheck_6925_ == 0)
{
v___x_6920_ = v___x_6902_;
v_isShared_6921_ = v_isSharedCheck_6925_;
goto v_resetjp_6919_;
}
else
{
lean_inc(v_a_6918_);
lean_dec(v___x_6902_);
v___x_6920_ = lean_box(0);
v_isShared_6921_ = v_isSharedCheck_6925_;
goto v_resetjp_6919_;
}
v_resetjp_6919_:
{
lean_object* v___x_6923_; 
if (v_isShared_6921_ == 0)
{
v___x_6923_ = v___x_6920_;
goto v_reusejp_6922_;
}
else
{
lean_object* v_reuseFailAlloc_6924_; 
v_reuseFailAlloc_6924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_a_6918_);
v___x_6923_ = v_reuseFailAlloc_6924_;
goto v_reusejp_6922_;
}
v_reusejp_6922_:
{
return v___x_6923_;
}
}
}
}
}
else
{
lean_dec(v_head_6894_);
return v___x_6895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_, lean_object* v_a_6930_, lean_object* v_a_6931_, lean_object* v_a_6932_){
_start:
{
lean_object* v_res_6933_; 
v_res_6933_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6927_, v_a_6928_, v_a_6929_, v_a_6930_, v_a_6931_);
lean_dec(v_a_6931_);
lean_dec_ref(v_a_6930_);
lean_dec(v_a_6929_);
lean_dec_ref(v_a_6928_);
return v_res_6933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6934_, lean_object* v_a_6935_, lean_object* v_a_6936_, lean_object* v_a_6937_, lean_object* v_a_6938_){
_start:
{
lean_object* v___x_6940_; 
v___x_6940_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6934_, v_a_6935_, v_a_6936_, v_a_6937_, v_a_6938_);
if (lean_obj_tag(v___x_6940_) == 0)
{
lean_object* v_a_6941_; lean_object* v___x_6943_; uint8_t v_isShared_6944_; uint8_t v_isSharedCheck_6949_; 
v_a_6941_ = lean_ctor_get(v___x_6940_, 0);
v_isSharedCheck_6949_ = !lean_is_exclusive(v___x_6940_);
if (v_isSharedCheck_6949_ == 0)
{
v___x_6943_ = v___x_6940_;
v_isShared_6944_ = v_isSharedCheck_6949_;
goto v_resetjp_6942_;
}
else
{
lean_inc(v_a_6941_);
lean_dec(v___x_6940_);
v___x_6943_ = lean_box(0);
v_isShared_6944_ = v_isSharedCheck_6949_;
goto v_resetjp_6942_;
}
v_resetjp_6942_:
{
lean_object* v_fst_6945_; lean_object* v___x_6947_; 
v_fst_6945_ = lean_ctor_get(v_a_6941_, 0);
lean_inc(v_fst_6945_);
lean_dec(v_a_6941_);
if (v_isShared_6944_ == 0)
{
lean_ctor_set(v___x_6943_, 0, v_fst_6945_);
v___x_6947_ = v___x_6943_;
goto v_reusejp_6946_;
}
else
{
lean_object* v_reuseFailAlloc_6948_; 
v_reuseFailAlloc_6948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6948_, 0, v_fst_6945_);
v___x_6947_ = v_reuseFailAlloc_6948_;
goto v_reusejp_6946_;
}
v_reusejp_6946_:
{
return v___x_6947_;
}
}
}
else
{
lean_object* v_a_6950_; lean_object* v___x_6952_; uint8_t v_isShared_6953_; uint8_t v_isSharedCheck_6957_; 
v_a_6950_ = lean_ctor_get(v___x_6940_, 0);
v_isSharedCheck_6957_ = !lean_is_exclusive(v___x_6940_);
if (v_isSharedCheck_6957_ == 0)
{
v___x_6952_ = v___x_6940_;
v_isShared_6953_ = v_isSharedCheck_6957_;
goto v_resetjp_6951_;
}
else
{
lean_inc(v_a_6950_);
lean_dec(v___x_6940_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_6958_, lean_object* v_a_6959_, lean_object* v_a_6960_, lean_object* v_a_6961_, lean_object* v_a_6962_, lean_object* v_a_6963_){
_start:
{
lean_object* v_res_6964_; 
v_res_6964_ = l_Lean_Meta_mkAndIntroN(v_hs_6958_, v_a_6959_, v_a_6960_, v_a_6961_, v_a_6962_);
lean_dec(v_a_6962_);
lean_dec_ref(v_a_6961_);
lean_dec(v_a_6960_);
lean_dec_ref(v_a_6959_);
return v_res_6964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7021_; uint8_t v___x_7022_; lean_object* v___x_7023_; lean_object* v___x_7024_; 
v___x_7021_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7022_ = 0;
v___x_7023_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7024_ = l_Lean_registerTraceClass(v___x_7021_, v___x_7022_, v___x_7023_);
if (lean_obj_tag(v___x_7024_) == 0)
{
lean_object* v___x_7025_; uint8_t v___x_7026_; lean_object* v___x_7027_; 
lean_dec_ref_known(v___x_7024_, 1);
v___x_7025_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7026_ = 1;
v___x_7027_ = l_Lean_registerTraceClass(v___x_7025_, v___x_7026_, v___x_7023_);
if (lean_obj_tag(v___x_7027_) == 0)
{
lean_object* v___x_7028_; lean_object* v___x_7029_; 
lean_dec_ref_known(v___x_7027_, 1);
v___x_7028_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7029_ = l_Lean_registerTraceClass(v___x_7028_, v___x_7026_, v___x_7023_);
return v___x_7029_;
}
else
{
return v___x_7027_;
}
}
else
{
return v___x_7024_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7030_){
_start:
{
lean_object* v_res_7031_; 
v_res_7031_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7031_;
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
