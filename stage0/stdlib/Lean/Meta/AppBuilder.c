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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
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
lean_object* v___f_1019_; lean_object* v___x_854__overap_1020_; lean_object* v___x_1021_; 
v___f_1019_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_854__overap_1020_ = lean_panic_fn_borrowed(v___f_1019_, v_msg_1013_);
lean_inc(v___y_1017_);
lean_inc_ref(v___y_1016_);
lean_inc(v___y_1015_);
lean_inc_ref(v___y_1014_);
v___x_1021_ = lean_apply_5(v___x_854__overap_1020_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, lean_box(0));
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
v___x_1490_ = lean_st_ref_put(v___y_1471_, v___x_1489_);
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
lean_object* v_ks_1600_; lean_object* v_vs_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1619_; 
v_ks_1600_ = lean_ctor_get(v_x_1549_, 0);
v_vs_1601_ = lean_ctor_get(v_x_1549_, 1);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_x_1549_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1603_ = v_x_1549_;
v_isShared_1604_ = v_isSharedCheck_1619_;
goto v_resetjp_1602_;
}
else
{
lean_inc(v_vs_1601_);
lean_inc(v_ks_1600_);
lean_dec(v_x_1549_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1619_;
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
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v_ks_1600_);
lean_ctor_set(v_reuseFailAlloc_1618_, 1, v_vs_1601_);
v___x_1606_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
lean_object* v_newNode_1607_; size_t v___x_1608_; uint8_t v___x_1609_; 
v_newNode_1607_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v___x_1606_, v_x_1552_, v_x_1553_);
v___x_1608_ = ((size_t)7ULL);
v___x_1609_ = lean_usize_dec_le(v___x_1608_, v_x_1551_);
if (v___x_1609_ == 0)
{
lean_object* v___x_1610_; lean_object* v___x_1611_; uint8_t v___x_1612_; 
v___x_1610_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1607_);
v___x_1611_ = lean_unsigned_to_nat(4u);
v___x_1612_ = lean_nat_dec_lt(v___x_1610_, v___x_1611_);
lean_dec(v___x_1610_);
if (v___x_1612_ == 0)
{
lean_object* v_ks_1613_; lean_object* v_vs_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; 
v_ks_1613_ = lean_ctor_get(v_newNode_1607_, 0);
lean_inc_ref(v_ks_1613_);
v_vs_1614_ = lean_ctor_get(v_newNode_1607_, 1);
lean_inc_ref(v_vs_1614_);
lean_dec_ref(v_newNode_1607_);
v___x_1615_ = lean_unsigned_to_nat(0u);
v___x_1616_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1617_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1551_, v_ks_1613_, v_vs_1614_, v___x_1615_, v___x_1616_);
lean_dec_ref(v_vs_1614_);
lean_dec_ref(v_ks_1613_);
return v___x_1617_;
}
else
{
return v_newNode_1607_;
}
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
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_1620_, lean_object* v_keys_1621_, lean_object* v_vals_1622_, lean_object* v_i_1623_, lean_object* v_entries_1624_){
_start:
{
lean_object* v___x_1625_; uint8_t v___x_1626_; 
v___x_1625_ = lean_array_get_size(v_keys_1621_);
v___x_1626_ = lean_nat_dec_lt(v_i_1623_, v___x_1625_);
if (v___x_1626_ == 0)
{
lean_dec(v_i_1623_);
return v_entries_1624_;
}
else
{
lean_object* v_k_1627_; lean_object* v_v_1628_; uint64_t v___x_1629_; size_t v_h_1630_; size_t v___x_1631_; lean_object* v___x_1632_; size_t v___x_1633_; size_t v___x_1634_; size_t v___x_1635_; size_t v_h_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; 
v_k_1627_ = lean_array_fget_borrowed(v_keys_1621_, v_i_1623_);
v_v_1628_ = lean_array_fget_borrowed(v_vals_1622_, v_i_1623_);
v___x_1629_ = l_Lean_instHashableMVarId_hash(v_k_1627_);
v_h_1630_ = lean_uint64_to_usize(v___x_1629_);
v___x_1631_ = ((size_t)5ULL);
v___x_1632_ = lean_unsigned_to_nat(1u);
v___x_1633_ = ((size_t)1ULL);
v___x_1634_ = lean_usize_sub(v_depth_1620_, v___x_1633_);
v___x_1635_ = lean_usize_mul(v___x_1631_, v___x_1634_);
v_h_1636_ = lean_usize_shift_right(v_h_1630_, v___x_1635_);
v___x_1637_ = lean_nat_add(v_i_1623_, v___x_1632_);
lean_dec(v_i_1623_);
lean_inc(v_v_1628_);
lean_inc(v_k_1627_);
v___x_1638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_entries_1624_, v_h_1636_, v_depth_1620_, v_k_1627_, v_v_1628_);
v_i_1623_ = v___x_1637_;
v_entries_1624_ = v___x_1638_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1640_, lean_object* v_keys_1641_, lean_object* v_vals_1642_, lean_object* v_i_1643_, lean_object* v_entries_1644_){
_start:
{
size_t v_depth_boxed_1645_; lean_object* v_res_1646_; 
v_depth_boxed_1645_ = lean_unbox_usize(v_depth_1640_);
lean_dec(v_depth_1640_);
v_res_1646_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_1645_, v_keys_1641_, v_vals_1642_, v_i_1643_, v_entries_1644_);
lean_dec_ref(v_vals_1642_);
lean_dec_ref(v_keys_1641_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
size_t v_x_1967__boxed_1652_; size_t v_x_1968__boxed_1653_; lean_object* v_res_1654_; 
v_x_1967__boxed_1652_ = lean_unbox_usize(v_x_1648_);
lean_dec(v_x_1648_);
v_x_1968__boxed_1653_ = lean_unbox_usize(v_x_1649_);
lean_dec(v_x_1649_);
v_res_1654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1647_, v_x_1967__boxed_1652_, v_x_1968__boxed_1653_, v_x_1650_, v_x_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object* v_x_1655_, lean_object* v_x_1656_, lean_object* v_x_1657_){
_start:
{
uint64_t v___x_1658_; size_t v___x_1659_; size_t v___x_1660_; lean_object* v___x_1661_; 
v___x_1658_ = l_Lean_instHashableMVarId_hash(v_x_1656_);
v___x_1659_ = lean_uint64_to_usize(v___x_1658_);
v___x_1660_ = ((size_t)1ULL);
v___x_1661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1655_, v___x_1659_, v___x_1660_, v_x_1656_, v_x_1657_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(lean_object* v_mvarId_1662_, lean_object* v_val_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1666_; lean_object* v_mctx_1667_; lean_object* v_cache_1668_; lean_object* v_zetaDeltaFVarIds_1669_; lean_object* v_postponed_1670_; lean_object* v_diag_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1700_; 
v___x_1666_ = lean_st_ref_take(v___y_1664_);
v_mctx_1667_ = lean_ctor_get(v___x_1666_, 0);
v_cache_1668_ = lean_ctor_get(v___x_1666_, 1);
v_zetaDeltaFVarIds_1669_ = lean_ctor_get(v___x_1666_, 2);
v_postponed_1670_ = lean_ctor_get(v___x_1666_, 3);
v_diag_1671_ = lean_ctor_get(v___x_1666_, 4);
v_isSharedCheck_1700_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1673_ = v___x_1666_;
v_isShared_1674_ = v_isSharedCheck_1700_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_diag_1671_);
lean_inc(v_postponed_1670_);
lean_inc(v_zetaDeltaFVarIds_1669_);
lean_inc(v_cache_1668_);
lean_inc(v_mctx_1667_);
lean_dec(v___x_1666_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1700_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v_depth_1675_; lean_object* v_levelAssignDepth_1676_; lean_object* v_lmvarCounter_1677_; lean_object* v_mvarCounter_1678_; lean_object* v_lDecls_1679_; lean_object* v_decls_1680_; lean_object* v_userNames_1681_; lean_object* v_lAssignment_1682_; lean_object* v_eAssignment_1683_; lean_object* v_dAssignment_1684_; lean_object* v_instanceTypedMVars_1685_; lean_object* v___x_1687_; uint8_t v_isShared_1688_; uint8_t v_isSharedCheck_1699_; 
v_depth_1675_ = lean_ctor_get(v_mctx_1667_, 0);
v_levelAssignDepth_1676_ = lean_ctor_get(v_mctx_1667_, 1);
v_lmvarCounter_1677_ = lean_ctor_get(v_mctx_1667_, 2);
v_mvarCounter_1678_ = lean_ctor_get(v_mctx_1667_, 3);
v_lDecls_1679_ = lean_ctor_get(v_mctx_1667_, 4);
v_decls_1680_ = lean_ctor_get(v_mctx_1667_, 5);
v_userNames_1681_ = lean_ctor_get(v_mctx_1667_, 6);
v_lAssignment_1682_ = lean_ctor_get(v_mctx_1667_, 7);
v_eAssignment_1683_ = lean_ctor_get(v_mctx_1667_, 8);
v_dAssignment_1684_ = lean_ctor_get(v_mctx_1667_, 9);
v_instanceTypedMVars_1685_ = lean_ctor_get(v_mctx_1667_, 10);
v_isSharedCheck_1699_ = !lean_is_exclusive(v_mctx_1667_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1687_ = v_mctx_1667_;
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
else
{
lean_inc(v_instanceTypedMVars_1685_);
lean_inc(v_dAssignment_1684_);
lean_inc(v_eAssignment_1683_);
lean_inc(v_lAssignment_1682_);
lean_inc(v_userNames_1681_);
lean_inc(v_decls_1680_);
lean_inc(v_lDecls_1679_);
lean_inc(v_mvarCounter_1678_);
lean_inc(v_lmvarCounter_1677_);
lean_inc(v_levelAssignDepth_1676_);
lean_inc(v_depth_1675_);
lean_dec(v_mctx_1667_);
v___x_1687_ = lean_box(0);
v_isShared_1688_ = v_isSharedCheck_1699_;
goto v_resetjp_1686_;
}
v_resetjp_1686_:
{
lean_object* v___x_1689_; lean_object* v___x_1691_; 
v___x_1689_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_eAssignment_1683_, v_mvarId_1662_, v_val_1663_);
if (v_isShared_1688_ == 0)
{
lean_ctor_set(v___x_1687_, 8, v___x_1689_);
v___x_1691_ = v___x_1687_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v_depth_1675_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_levelAssignDepth_1676_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_lmvarCounter_1677_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_mvarCounter_1678_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_lDecls_1679_);
lean_ctor_set(v_reuseFailAlloc_1698_, 5, v_decls_1680_);
lean_ctor_set(v_reuseFailAlloc_1698_, 6, v_userNames_1681_);
lean_ctor_set(v_reuseFailAlloc_1698_, 7, v_lAssignment_1682_);
lean_ctor_set(v_reuseFailAlloc_1698_, 8, v___x_1689_);
lean_ctor_set(v_reuseFailAlloc_1698_, 9, v_dAssignment_1684_);
lean_ctor_set(v_reuseFailAlloc_1698_, 10, v_instanceTypedMVars_1685_);
v___x_1691_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1693_; 
if (v_isShared_1674_ == 0)
{
lean_ctor_set(v___x_1673_, 0, v___x_1691_);
v___x_1693_ = v___x_1673_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_cache_1668_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v_zetaDeltaFVarIds_1669_);
lean_ctor_set(v_reuseFailAlloc_1697_, 3, v_postponed_1670_);
lean_ctor_set(v_reuseFailAlloc_1697_, 4, v_diag_1671_);
v___x_1693_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1694_ = lean_st_ref_put(v___y_1664_, v___x_1693_);
v___x_1695_ = lean_box(0);
v___x_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1696_, 0, v___x_1695_);
return v___x_1696_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg___boxed(lean_object* v_mvarId_1701_, lean_object* v_val_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v_res_1705_; 
v_res_1705_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1701_, v_val_1702_, v___y_1703_);
lean_dec(v___y_1703_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(lean_object* v_as_1706_, size_t v_i_1707_, size_t v_stop_1708_, lean_object* v_b_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_usize_dec_eq(v_i_1707_, v_stop_1708_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1716_ = lean_array_uget_borrowed(v_as_1706_, v_i_1707_);
lean_inc(v___x_1716_);
v___x_1717_ = l_Lean_MVarId_getDecl(v___x_1716_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v_type_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v_type_1719_ = lean_ctor_get(v_a_1718_, 2);
lean_inc_ref(v_type_1719_);
lean_dec(v_a_1718_);
v___x_1720_ = lean_box(0);
v___x_1721_ = l_Lean_Meta_synthInstance(v_type_1719_, v___x_1720_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
lean_inc(v___x_1716_);
v___x_1723_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v___x_1716_, v_a_1722_, v___y_1711_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; size_t v___x_1725_; size_t v___x_1726_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = ((size_t)1ULL);
v___x_1726_ = lean_usize_add(v_i_1707_, v___x_1725_);
v_i_1707_ = v___x_1726_;
v_b_1709_ = v_a_1724_;
goto _start;
}
else
{
return v___x_1723_;
}
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1735_; 
v_a_1728_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1735_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1730_ = v___x_1721_;
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_a_1728_);
lean_dec(v___x_1721_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1735_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1733_; 
if (v_isShared_1731_ == 0)
{
v___x_1733_ = v___x_1730_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1734_; 
v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
v___x_1733_ = v_reuseFailAlloc_1734_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
return v___x_1733_;
}
}
}
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1738_; uint8_t v_isShared_1739_; uint8_t v_isSharedCheck_1743_; 
v_a_1736_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1738_ = v___x_1717_;
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
else
{
lean_inc(v_a_1736_);
lean_dec(v___x_1717_);
v___x_1738_ = lean_box(0);
v_isShared_1739_ = v_isSharedCheck_1743_;
goto v_resetjp_1737_;
}
v_resetjp_1737_:
{
lean_object* v___x_1741_; 
if (v_isShared_1739_ == 0)
{
v___x_1741_ = v___x_1738_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1742_; 
v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
v___x_1741_ = v_reuseFailAlloc_1742_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
return v___x_1741_;
}
}
}
}
else
{
lean_object* v___x_1744_; 
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v_b_1709_);
return v___x_1744_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2___boxed(lean_object* v_as_1745_, lean_object* v_i_1746_, lean_object* v_stop_1747_, lean_object* v_b_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
size_t v_i_boxed_1754_; size_t v_stop_boxed_1755_; lean_object* v_res_1756_; 
v_i_boxed_1754_ = lean_unbox_usize(v_i_1746_);
lean_dec(v_i_1746_);
v_stop_boxed_1755_ = lean_unbox_usize(v_stop_1747_);
lean_dec(v_stop_1747_);
v_res_1756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_as_1745_, v_i_boxed_1754_, v_stop_boxed_1755_, v_b_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec_ref(v_as_1745_);
return v_res_1756_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1));
v___x_1761_ = l_Lean_MessageData_ofFormat(v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* v_methodName_1762_, lean_object* v_f_1763_, lean_object* v_args_1764_, lean_object* v_instMVars_1765_, lean_object* v_a_1766_, lean_object* v_a_1767_, lean_object* v_a_1768_, lean_object* v_a_1769_){
_start:
{
lean_object* v___y_1806_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1817_; 
v___x_1815_ = lean_unsigned_to_nat(0u);
v___x_1816_ = lean_array_get_size(v_instMVars_1765_);
v___x_1817_ = lean_nat_dec_lt(v___x_1815_, v___x_1816_);
if (v___x_1817_ == 0)
{
goto v___jp_1771_;
}
else
{
lean_object* v___x_1818_; uint8_t v___x_1819_; 
v___x_1818_ = lean_box(0);
v___x_1819_ = lean_nat_dec_le(v___x_1816_, v___x_1816_);
if (v___x_1819_ == 0)
{
if (v___x_1817_ == 0)
{
goto v___jp_1771_;
}
else
{
size_t v___x_1820_; size_t v___x_1821_; lean_object* v___x_1822_; 
v___x_1820_ = ((size_t)0ULL);
v___x_1821_ = lean_usize_of_nat(v___x_1816_);
v___x_1822_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1765_, v___x_1820_, v___x_1821_, v___x_1818_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
v___y_1806_ = v___x_1822_;
goto v___jp_1805_;
}
}
else
{
size_t v___x_1823_; size_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1823_ = ((size_t)0ULL);
v___x_1824_ = lean_usize_of_nat(v___x_1816_);
v___x_1825_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1765_, v___x_1823_, v___x_1824_, v___x_1818_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
v___y_1806_ = v___x_1825_;
goto v___jp_1805_;
}
}
v___jp_1771_:
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v_a_1774_; lean_object* v___x_1775_; 
v___x_1772_ = l_Lean_mkAppN(v_f_1763_, v_args_1764_);
v___x_1773_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v___x_1772_, v_a_1767_);
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc_n(v_a_1774_, 2);
lean_dec_ref(v___x_1773_);
v___x_1775_ = l_Lean_Meta_hasAssignableMVar(v_a_1774_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1796_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1778_ = v___x_1775_;
v_isShared_1779_ = v_isSharedCheck_1796_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1775_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1796_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
uint8_t v___x_1780_; 
v___x_1780_ = lean_unbox(v_a_1776_);
lean_dec(v_a_1776_);
if (v___x_1780_ == 0)
{
lean_object* v___x_1782_; 
lean_dec(v_methodName_1762_);
if (v_isShared_1779_ == 0)
{
lean_ctor_set(v___x_1778_, 0, v_a_1774_);
v___x_1782_ = v___x_1778_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1774_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_del_object(v___x_1778_);
v___x_1784_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2);
v___x_1785_ = l_Lean_indentExpr(v_a_1774_);
v___x_1786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1786_, 0, v___x_1784_);
lean_ctor_set(v___x_1786_, 1, v___x_1785_);
v___x_1787_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_methodName_1762_, v___x_1786_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1793_; 
if (v_isShared_1791_ == 0)
{
v___x_1793_ = v___x_1790_;
goto v_reusejp_1792_;
}
else
{
lean_object* v_reuseFailAlloc_1794_; 
v_reuseFailAlloc_1794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_a_1788_);
v___x_1793_ = v_reuseFailAlloc_1794_;
goto v_reusejp_1792_;
}
v_reusejp_1792_:
{
return v___x_1793_;
}
}
}
}
}
else
{
lean_object* v_a_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1804_; 
lean_dec(v_a_1774_);
lean_dec(v_methodName_1762_);
v_a_1797_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1804_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1804_ == 0)
{
v___x_1799_ = v___x_1775_;
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_a_1797_);
lean_dec(v___x_1775_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1804_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1802_; 
if (v_isShared_1800_ == 0)
{
v___x_1802_ = v___x_1799_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1803_; 
v_reuseFailAlloc_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1803_, 0, v_a_1797_);
v___x_1802_ = v_reuseFailAlloc_1803_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
return v___x_1802_;
}
}
}
}
v___jp_1805_:
{
if (lean_obj_tag(v___y_1806_) == 0)
{
lean_dec_ref_known(v___y_1806_, 1);
goto v___jp_1771_;
}
else
{
lean_object* v_a_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1814_; 
lean_dec_ref(v_f_1763_);
lean_dec(v_methodName_1762_);
v_a_1807_ = lean_ctor_get(v___y_1806_, 0);
v_isSharedCheck_1814_ = !lean_is_exclusive(v___y_1806_);
if (v_isSharedCheck_1814_ == 0)
{
v___x_1809_ = v___y_1806_;
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_a_1807_);
lean_dec(v___y_1806_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1814_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1812_; 
if (v_isShared_1810_ == 0)
{
v___x_1812_ = v___x_1809_;
goto v_reusejp_1811_;
}
else
{
lean_object* v_reuseFailAlloc_1813_; 
v_reuseFailAlloc_1813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1813_, 0, v_a_1807_);
v___x_1812_ = v_reuseFailAlloc_1813_;
goto v_reusejp_1811_;
}
v_reusejp_1811_:
{
return v___x_1812_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* v_methodName_1826_, lean_object* v_f_1827_, lean_object* v_args_1828_, lean_object* v_instMVars_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v_methodName_1826_, v_f_1827_, v_args_1828_, v_instMVars_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec_ref(v_instMVars_1829_);
lean_dec_ref(v_args_1828_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* v_mvarId_1836_, lean_object* v_val_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1836_, v_val_1837_, v___y_1839_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* v_mvarId_1844_, lean_object* v_val_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_){
_start:
{
lean_object* v_res_1851_; 
v_res_1851_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(v_mvarId_1844_, v_val_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* v_00_u03b2_1852_, lean_object* v_x_1853_, lean_object* v_x_1854_, lean_object* v_x_1855_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_x_1853_, v_x_1854_, v_x_1855_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1857_, lean_object* v_x_1858_, size_t v_x_1859_, size_t v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1858_, v_x_1859_, v_x_1860_, v_x_1861_, v_x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
size_t v_x_2407__boxed_1870_; size_t v_x_2408__boxed_1871_; lean_object* v_res_1872_; 
v_x_2407__boxed_1870_ = lean_unbox_usize(v_x_1866_);
lean_dec(v_x_1866_);
v_x_2408__boxed_1871_ = lean_unbox_usize(v_x_1867_);
lean_dec(v_x_1867_);
v_res_1872_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1864_, v_x_1865_, v_x_2407__boxed_1870_, v_x_2408__boxed_1871_, v_x_1868_, v_x_1869_);
return v_res_1872_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1873_, lean_object* v_n_1874_, lean_object* v_k_1875_, lean_object* v_v_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1874_, v_k_1875_, v_v_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1878_, size_t v_depth_1879_, lean_object* v_keys_1880_, lean_object* v_vals_1881_, lean_object* v_heq_1882_, lean_object* v_i_1883_, lean_object* v_entries_1884_){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1879_, v_keys_1880_, v_vals_1881_, v_i_1883_, v_entries_1884_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1886_, lean_object* v_depth_1887_, lean_object* v_keys_1888_, lean_object* v_vals_1889_, lean_object* v_heq_1890_, lean_object* v_i_1891_, lean_object* v_entries_1892_){
_start:
{
size_t v_depth_boxed_1893_; lean_object* v_res_1894_; 
v_depth_boxed_1893_ = lean_unbox_usize(v_depth_1887_);
lean_dec(v_depth_1887_);
v_res_1894_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1886_, v_depth_boxed_1893_, v_keys_1888_, v_vals_1889_, v_heq_1890_, v_i_1891_, v_entries_1892_);
lean_dec_ref(v_vals_1889_);
lean_dec_ref(v_keys_1888_);
return v_res_1894_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1895_, lean_object* v_x_1896_, lean_object* v_x_1897_, lean_object* v_x_1898_, lean_object* v_x_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1896_, v_x_1897_, v_x_1898_, v_x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3(void){
_start:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1905_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2));
v___x_1906_ = l_Lean_stringToMessageData(v___x_1905_);
return v___x_1906_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4));
v___x_1909_ = l_Lean_stringToMessageData(v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1913_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7));
v___x_1914_ = l_Lean_MessageData_ofFormat(v___x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* v_f_1915_, lean_object* v_xs_1916_, lean_object* v_type_1917_, lean_object* v_i_1918_, lean_object* v_j_1919_, lean_object* v_args_1920_, lean_object* v_instMVars_1921_, lean_object* v_a_1922_, lean_object* v_a_1923_, lean_object* v_a_1924_, lean_object* v_a_1925_){
_start:
{
lean_object* v___x_1927_; uint8_t v___x_1928_; 
v___x_1927_ = lean_array_get_size(v_xs_1916_);
v___x_1928_ = lean_nat_dec_le(v___x_1927_, v_i_1918_);
if (v___x_1928_ == 0)
{
if (lean_obj_tag(v_type_1917_) == 7)
{
lean_object* v_binderName_1929_; lean_object* v_binderType_1930_; lean_object* v_body_1931_; uint8_t v_binderInfo_1932_; lean_object* v___x_1933_; lean_object* v_d_1934_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; 
v_binderName_1929_ = lean_ctor_get(v_type_1917_, 0);
lean_inc(v_binderName_1929_);
v_binderType_1930_ = lean_ctor_get(v_type_1917_, 1);
lean_inc_ref(v_binderType_1930_);
v_body_1931_ = lean_ctor_get(v_type_1917_, 2);
lean_inc_ref(v_body_1931_);
v_binderInfo_1932_ = lean_ctor_get_uint8(v_type_1917_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1917_, 3);
v___x_1933_ = lean_array_get_size(v_args_1920_);
v_d_1934_ = lean_expr_instantiate_rev_range(v_binderType_1930_, v_j_1919_, v___x_1933_, v_args_1920_);
lean_dec_ref(v_binderType_1930_);
switch(v_binderInfo_1932_)
{
case 1:
{
v___y_1936_ = v_a_1922_;
v___y_1937_ = v_a_1923_;
v___y_1938_ = v_a_1924_;
v___y_1939_ = v_a_1925_;
goto v___jp_1935_;
}
case 2:
{
v___y_1936_ = v_a_1922_;
v___y_1937_ = v_a_1923_;
v___y_1938_ = v_a_1924_;
v___y_1939_ = v_a_1925_;
goto v___jp_1935_;
}
case 3:
{
lean_object* v___x_1946_; uint8_t v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_d_1934_);
v___x_1947_ = 1;
v___x_1948_ = l_Lean_Meta_mkFreshExprMVar(v___x_1946_, v___x_1947_, v_binderName_1929_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1948_) == 0)
{
lean_object* v_a_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v_a_1949_ = lean_ctor_get(v___x_1948_, 0);
lean_inc_n(v_a_1949_, 2);
lean_dec_ref_known(v___x_1948_, 1);
v___x_1950_ = lean_array_push(v_args_1920_, v_a_1949_);
v___x_1951_ = l_Lean_Expr_mvarId_x21(v_a_1949_);
lean_dec(v_a_1949_);
v___x_1952_ = lean_array_push(v_instMVars_1921_, v___x_1951_);
v_type_1917_ = v_body_1931_;
v_args_1920_ = v___x_1950_;
v_instMVars_1921_ = v___x_1952_;
goto _start;
}
else
{
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
lean_dec_ref(v_f_1915_);
return v___x_1948_;
}
}
default: 
{
lean_object* v_x_1954_; lean_object* v___x_1955_; 
lean_dec(v_binderName_1929_);
v_x_1954_ = lean_array_fget_borrowed(v_xs_1916_, v_i_1918_);
lean_inc(v_a_1925_);
lean_inc_ref(v_a_1924_);
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_x_1954_);
v___x_1955_ = lean_infer_type(v_x_1954_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1955_) == 0)
{
lean_object* v_a_1956_; uint8_t v___y_1958_; lean_object* v___x_1989_; uint8_t v_transparency_1990_; uint8_t v___x_1991_; uint8_t v___x_1992_; 
v_a_1956_ = lean_ctor_get(v___x_1955_, 0);
lean_inc(v_a_1956_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1989_ = l_Lean_Meta_Context_config(v_a_1922_);
v_transparency_1990_ = lean_ctor_get_uint8(v___x_1989_, 9);
lean_dec_ref(v___x_1989_);
v___x_1991_ = 1;
v___x_1992_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1990_, v___x_1991_);
if (v___x_1992_ == 0)
{
v___y_1958_ = v_transparency_1990_;
goto v___jp_1957_;
}
else
{
v___y_1958_ = v___x_1991_;
goto v___jp_1957_;
}
v___jp_1957_:
{
lean_object* v_keyedConfig_1959_; uint8_t v_trackZetaDelta_1960_; lean_object* v_zetaDeltaSet_1961_; lean_object* v_lctx_1962_; lean_object* v_localInstances_1963_; lean_object* v_defEqCtx_x3f_1964_; lean_object* v_synthPendingDepth_1965_; lean_object* v_customCanUnfoldPredicate_x3f_1966_; uint8_t v_univApprox_1967_; uint8_t v_inTypeClassResolution_1968_; uint8_t v_cacheInferType_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; 
v_keyedConfig_1959_ = lean_ctor_get(v_a_1922_, 0);
v_trackZetaDelta_1960_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7);
v_zetaDeltaSet_1961_ = lean_ctor_get(v_a_1922_, 1);
v_lctx_1962_ = lean_ctor_get(v_a_1922_, 2);
v_localInstances_1963_ = lean_ctor_get(v_a_1922_, 3);
v_defEqCtx_x3f_1964_ = lean_ctor_get(v_a_1922_, 4);
v_synthPendingDepth_1965_ = lean_ctor_get(v_a_1922_, 5);
v_customCanUnfoldPredicate_x3f_1966_ = lean_ctor_get(v_a_1922_, 6);
v_univApprox_1967_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1968_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7 + 2);
v_cacheInferType_1969_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1959_);
v___x_1970_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_1958_, v_keyedConfig_1959_);
lean_inc(v_customCanUnfoldPredicate_x3f_1966_);
lean_inc(v_synthPendingDepth_1965_);
lean_inc(v_defEqCtx_x3f_1964_);
lean_inc_ref(v_localInstances_1963_);
lean_inc_ref(v_lctx_1962_);
lean_inc(v_zetaDeltaSet_1961_);
v___x_1971_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v_zetaDeltaSet_1961_);
lean_ctor_set(v___x_1971_, 2, v_lctx_1962_);
lean_ctor_set(v___x_1971_, 3, v_localInstances_1963_);
lean_ctor_set(v___x_1971_, 4, v_defEqCtx_x3f_1964_);
lean_ctor_set(v___x_1971_, 5, v_synthPendingDepth_1965_);
lean_ctor_set(v___x_1971_, 6, v_customCanUnfoldPredicate_x3f_1966_);
lean_ctor_set_uint8(v___x_1971_, sizeof(void*)*7, v_trackZetaDelta_1960_);
lean_ctor_set_uint8(v___x_1971_, sizeof(void*)*7 + 1, v_univApprox_1967_);
lean_ctor_set_uint8(v___x_1971_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1968_);
lean_ctor_set_uint8(v___x_1971_, sizeof(void*)*7 + 3, v_cacheInferType_1969_);
v___x_1972_ = l_Lean_Meta_isExprDefEq(v_d_1934_, v_a_1956_, v___x_1971_, v_a_1923_, v_a_1924_, v_a_1925_);
lean_dec_ref_known(v___x_1971_, 7);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; uint8_t v___x_1974_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
lean_inc(v_a_1973_);
lean_dec_ref_known(v___x_1972_, 1);
v___x_1974_ = lean_unbox(v_a_1973_);
lean_dec(v_a_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_instMVars_1921_);
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
v___x_1975_ = l_Lean_mkAppN(v_f_1915_, v_args_1920_);
lean_dec_ref(v_args_1920_);
lean_inc(v_x_1954_);
v___x_1976_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1975_, v_x_1954_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
return v___x_1976_;
}
else
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = lean_unsigned_to_nat(1u);
v___x_1978_ = lean_nat_add(v_i_1918_, v___x_1977_);
lean_dec(v_i_1918_);
lean_inc(v_x_1954_);
v___x_1979_ = lean_array_push(v_args_1920_, v_x_1954_);
v_type_1917_ = v_body_1931_;
v_i_1918_ = v___x_1978_;
v_args_1920_ = v___x_1979_;
goto _start;
}
}
else
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1988_; 
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
lean_dec_ref(v_f_1915_);
v_a_1981_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_1988_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_1988_ == 0)
{
v___x_1983_ = v___x_1972_;
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1972_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1988_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v___x_1986_; 
if (v_isShared_1984_ == 0)
{
v___x_1986_ = v___x_1983_;
goto v_reusejp_1985_;
}
else
{
lean_object* v_reuseFailAlloc_1987_; 
v_reuseFailAlloc_1987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1987_, 0, v_a_1981_);
v___x_1986_ = v_reuseFailAlloc_1987_;
goto v_reusejp_1985_;
}
v_reusejp_1985_:
{
return v___x_1986_;
}
}
}
}
}
else
{
lean_dec_ref(v_d_1934_);
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
lean_dec_ref(v_f_1915_);
return v___x_1955_;
}
}
}
v___jp_1935_:
{
lean_object* v___x_1940_; uint8_t v___x_1941_; lean_object* v___x_1942_; 
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_d_1934_);
v___x_1941_ = 0;
v___x_1942_ = l_Lean_Meta_mkFreshExprMVar(v___x_1940_, v___x_1941_, v_binderName_1929_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_object* v_a_1943_; lean_object* v___x_1944_; 
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
lean_inc(v_a_1943_);
lean_dec_ref_known(v___x_1942_, 1);
v___x_1944_ = lean_array_push(v_args_1920_, v_a_1943_);
v_type_1917_ = v_body_1931_;
v_args_1920_ = v___x_1944_;
v_a_1922_ = v___y_1936_;
v_a_1923_ = v___y_1937_;
v_a_1924_ = v___y_1938_;
v_a_1925_ = v___y_1939_;
goto _start;
}
else
{
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
lean_dec_ref(v_f_1915_);
return v___x_1942_;
}
}
}
else
{
lean_object* v___x_1993_; lean_object* v_type_1994_; lean_object* v___x_1995_; 
v___x_1993_ = lean_array_get_size(v_args_1920_);
v_type_1994_ = lean_expr_instantiate_rev_range(v_type_1917_, v_j_1919_, v___x_1993_, v_args_1920_);
lean_dec(v_j_1919_);
lean_dec_ref(v_type_1917_);
v___x_1995_ = l_Lean_Meta_whnfD(v_type_1994_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; uint8_t v___x_1997_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = l_Lean_Expr_isForall(v_a_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
lean_dec(v_a_1996_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_i_1918_);
v___x_1998_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_1999_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2000_ = l_Lean_indentExpr(v_f_1915_);
v___x_2001_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2001_, 0, v___x_1999_);
lean_ctor_set(v___x_2001_, 1, v___x_2000_);
v___x_2002_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_unsigned_to_nat(0u);
v___x_2005_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2006_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1916_, v___x_2004_, v___x_2005_);
v___x_2007_ = l_Lean_indentD(v___x_2006_);
v___x_2008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2008_, 0, v___x_2003_);
lean_ctor_set(v___x_2008_, 1, v___x_2007_);
v___x_2009_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1998_, v___x_2008_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
return v___x_2009_;
}
else
{
v_type_1917_ = v_a_1996_;
v_j_1919_ = v___x_1993_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_i_1918_);
lean_dec_ref(v_f_1915_);
return v___x_1995_;
}
}
}
else
{
lean_object* v___x_2011_; lean_object* v___x_2012_; 
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
lean_dec_ref(v_type_1917_);
v___x_2011_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2012_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2011_, v_f_1915_, v_args_1920_, v_instMVars_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
return v___x_2012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2013_, lean_object* v_xs_2014_, lean_object* v_type_2015_, lean_object* v_i_2016_, lean_object* v_j_2017_, lean_object* v_args_2018_, lean_object* v_instMVars_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v_res_2025_; 
v_res_2025_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2013_, v_xs_2014_, v_type_2015_, v_i_2016_, v_j_2017_, v_args_2018_, v_instMVars_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec(v_a_2021_);
lean_dec_ref(v_a_2020_);
lean_dec_ref(v_xs_2014_);
return v_res_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2028_, lean_object* v_fType_2029_, lean_object* v_xs_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2038_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2028_, v_xs_2030_, v_fType_2029_, v___x_2036_, v___x_2036_, v___x_2037_, v___x_2037_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2039_, lean_object* v_fType_2040_, lean_object* v_xs_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_){
_start:
{
lean_object* v_res_2047_; 
v_res_2047_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2039_, v_fType_2040_, v_xs_2041_, v_a_2042_, v_a_2043_, v_a_2044_, v_a_2045_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec(v_a_2043_);
lean_dec_ref(v_a_2042_);
lean_dec_ref(v_xs_2041_);
return v_res_2047_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2048_, lean_object* v_x_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_){
_start:
{
if (lean_obj_tag(v_x_2048_) == 0)
{
lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2055_ = l_List_reverse___redArg(v_x_2049_);
v___x_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2056_, 0, v___x_2055_);
return v___x_2056_;
}
else
{
lean_object* v_tail_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2075_; 
v_tail_2057_ = lean_ctor_get(v_x_2048_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_x_2048_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_x_2048_, 0);
lean_dec(v_unused_2076_);
v___x_2059_ = v_x_2048_;
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_tail_2057_);
lean_dec(v_x_2048_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2075_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; 
v___x_2061_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2050_, v___y_2051_, v___y_2052_, v___y_2053_);
if (lean_obj_tag(v___x_2061_) == 0)
{
lean_object* v_a_2062_; lean_object* v___x_2064_; 
v_a_2062_ = lean_ctor_get(v___x_2061_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2061_, 1);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v_x_2049_);
lean_ctor_set(v___x_2059_, 0, v_a_2062_);
v___x_2064_ = v___x_2059_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2062_);
lean_ctor_set(v_reuseFailAlloc_2066_, 1, v_x_2049_);
v___x_2064_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
v_x_2048_ = v_tail_2057_;
v_x_2049_ = v___x_2064_;
goto _start;
}
}
else
{
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_del_object(v___x_2059_);
lean_dec(v_tail_2057_);
lean_dec(v_x_2049_);
v_a_2067_ = lean_ctor_get(v___x_2061_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2061_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2061_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2061_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2077_, lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2077_, v_x_2078_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2089_ = lean_unsigned_to_nat(0u);
v___x_2090_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
lean_ctor_set(v___x_2090_, 1, v___x_2089_);
lean_ctor_set(v___x_2090_, 2, v___x_2089_);
lean_ctor_set(v___x_2090_, 3, v___x_2089_);
lean_ctor_set(v___x_2090_, 4, v___x_2088_);
lean_ctor_set(v___x_2090_, 5, v___x_2088_);
lean_ctor_set(v___x_2090_, 6, v___x_2088_);
lean_ctor_set(v___x_2090_, 7, v___x_2088_);
lean_ctor_set(v___x_2090_, 8, v___x_2088_);
lean_ctor_set(v___x_2090_, 9, v___x_2088_);
lean_ctor_set(v___x_2090_, 10, v___x_2088_);
return v___x_2090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; 
v___x_2091_ = lean_unsigned_to_nat(32u);
v___x_2092_ = lean_mk_empty_array_with_capacity(v___x_2091_);
v___x_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2093_, 0, v___x_2092_);
return v___x_2093_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2094_ = ((size_t)5ULL);
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_unsigned_to_nat(32u);
v___x_2097_ = lean_mk_empty_array_with_capacity(v___x_2096_);
v___x_2098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2099_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2099_, 0, v___x_2098_);
lean_ctor_set(v___x_2099_, 1, v___x_2097_);
lean_ctor_set(v___x_2099_, 2, v___x_2095_);
lean_ctor_set(v___x_2099_, 3, v___x_2095_);
lean_ctor_set_usize(v___x_2099_, 4, v___x_2094_);
return v___x_2099_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v___x_2100_ = lean_box(1);
v___x_2101_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2102_);
lean_ctor_set(v___x_2103_, 1, v___x_2101_);
lean_ctor_set(v___x_2103_, 2, v___x_2100_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; 
v___x_2105_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2106_ = l_Lean_stringToMessageData(v___x_2105_);
return v___x_2106_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2108_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2109_ = l_Lean_stringToMessageData(v___x_2108_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2112_ = l_Lean_stringToMessageData(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2115_ = l_Lean_stringToMessageData(v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2118_ = l_Lean_stringToMessageData(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2121_ = l_Lean_stringToMessageData(v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2123_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2124_ = l_Lean_stringToMessageData(v___x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2125_, lean_object* v_declHint_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v___x_2129_; lean_object* v_env_2130_; uint8_t v___x_2131_; 
v___x_2129_ = lean_st_ref_get(v___y_2127_);
v_env_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc_ref(v_env_2130_);
lean_dec(v___x_2129_);
v___x_2131_ = l_Lean_Name_isAnonymous(v_declHint_2126_);
if (v___x_2131_ == 0)
{
uint8_t v_isExporting_2132_; 
v_isExporting_2132_ = lean_ctor_get_uint8(v_env_2130_, sizeof(void*)*8);
if (v_isExporting_2132_ == 0)
{
lean_object* v___x_2133_; 
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_msg_2125_);
return v___x_2133_;
}
else
{
lean_object* v___x_2134_; uint8_t v___x_2135_; 
lean_inc_ref(v_env_2130_);
v___x_2134_ = l_Lean_Environment_setExporting(v_env_2130_, v___x_2131_);
lean_inc(v_declHint_2126_);
lean_inc_ref(v___x_2134_);
v___x_2135_ = l_Lean_Environment_contains(v___x_2134_, v_declHint_2126_, v_isExporting_2132_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec_ref(v___x_2134_);
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_msg_2125_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v_c_2142_; lean_object* v___x_2143_; 
v___x_2137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2139_ = l_Lean_Options_empty;
v___x_2140_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2134_);
lean_ctor_set(v___x_2140_, 1, v___x_2137_);
lean_ctor_set(v___x_2140_, 2, v___x_2138_);
lean_ctor_set(v___x_2140_, 3, v___x_2139_);
lean_inc(v_declHint_2126_);
v___x_2141_ = l_Lean_MessageData_ofConstName(v_declHint_2126_, v___x_2131_);
v_c_2142_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2142_, 0, v___x_2140_);
lean_ctor_set(v_c_2142_, 1, v___x_2141_);
v___x_2143_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2130_, v_declHint_2126_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; 
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2144_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v_c_2142_);
v___x_2146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2145_);
lean_ctor_set(v___x_2147_, 1, v___x_2146_);
v___x_2148_ = l_Lean_MessageData_note(v___x_2147_);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v_msg_2125_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2149_);
return v___x_2150_;
}
else
{
lean_object* v_val_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2186_; 
v_val_2151_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2153_ = v___x_2143_;
v_isShared_2154_ = v_isSharedCheck_2186_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_val_2151_);
lean_dec(v___x_2143_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2186_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v_mod_2158_; uint8_t v___x_2159_; 
v___x_2155_ = lean_box(0);
v___x_2156_ = l_Lean_Environment_header(v_env_2130_);
lean_dec_ref(v_env_2130_);
v___x_2157_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2156_);
v_mod_2158_ = lean_array_get(v___x_2155_, v___x_2157_, v_val_2151_);
lean_dec(v_val_2151_);
lean_dec_ref(v___x_2157_);
v___x_2159_ = l_Lean_isPrivateName(v_declHint_2126_);
lean_dec(v_declHint_2126_);
if (v___x_2159_ == 0)
{
lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v_c_2142_);
v___x_2162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2161_);
lean_ctor_set(v___x_2163_, 1, v___x_2162_);
v___x_2164_ = l_Lean_MessageData_ofName(v_mod_2158_);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = l_Lean_MessageData_note(v___x_2167_);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v_msg_2125_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2169_);
v___x_2171_ = v___x_2153_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v___x_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2173_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v___x_2173_);
lean_ctor_set(v___x_2174_, 1, v_c_2142_);
v___x_2175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2174_);
lean_ctor_set(v___x_2176_, 1, v___x_2175_);
v___x_2177_ = l_Lean_MessageData_ofName(v_mod_2158_);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = l_Lean_MessageData_note(v___x_2180_);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v_msg_2125_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
if (v_isShared_2154_ == 0)
{
lean_ctor_set_tag(v___x_2153_, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2182_);
v___x_2184_ = v___x_2153_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2187_; 
lean_dec_ref(v_env_2130_);
lean_dec(v_declHint_2126_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_msg_2125_);
return v___x_2187_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2188_, lean_object* v_declHint_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2188_, v_declHint_2189_, v___y_2190_);
lean_dec(v___y_2190_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2193_, lean_object* v_declHint_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2210_; 
v___x_2200_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2193_, v_declHint_2194_, v___y_2198_);
v_a_2201_ = lean_ctor_get(v___x_2200_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2200_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2203_ = v___x_2200_;
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2200_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2210_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2205_ = l_Lean_unknownIdentifierMessageTag;
v___x_2206_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v_a_2201_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 0, v___x_2206_);
v___x_2208_ = v___x_2203_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2211_, lean_object* v_declHint_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2211_, v_declHint_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2219_, lean_object* v_msg_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_fileName_2226_; lean_object* v_fileMap_2227_; lean_object* v_options_2228_; lean_object* v_currRecDepth_2229_; lean_object* v_maxRecDepth_2230_; lean_object* v_ref_2231_; lean_object* v_currNamespace_2232_; lean_object* v_openDecls_2233_; lean_object* v_initHeartbeats_2234_; lean_object* v_maxHeartbeats_2235_; lean_object* v_quotContext_2236_; lean_object* v_currMacroScope_2237_; uint8_t v_diag_2238_; lean_object* v_cancelTk_x3f_2239_; uint8_t v_suppressElabErrors_2240_; lean_object* v_inheritedTraceOptions_2241_; lean_object* v_ref_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v_fileName_2226_ = lean_ctor_get(v___y_2223_, 0);
v_fileMap_2227_ = lean_ctor_get(v___y_2223_, 1);
v_options_2228_ = lean_ctor_get(v___y_2223_, 2);
v_currRecDepth_2229_ = lean_ctor_get(v___y_2223_, 3);
v_maxRecDepth_2230_ = lean_ctor_get(v___y_2223_, 4);
v_ref_2231_ = lean_ctor_get(v___y_2223_, 5);
v_currNamespace_2232_ = lean_ctor_get(v___y_2223_, 6);
v_openDecls_2233_ = lean_ctor_get(v___y_2223_, 7);
v_initHeartbeats_2234_ = lean_ctor_get(v___y_2223_, 8);
v_maxHeartbeats_2235_ = lean_ctor_get(v___y_2223_, 9);
v_quotContext_2236_ = lean_ctor_get(v___y_2223_, 10);
v_currMacroScope_2237_ = lean_ctor_get(v___y_2223_, 11);
v_diag_2238_ = lean_ctor_get_uint8(v___y_2223_, sizeof(void*)*14);
v_cancelTk_x3f_2239_ = lean_ctor_get(v___y_2223_, 12);
v_suppressElabErrors_2240_ = lean_ctor_get_uint8(v___y_2223_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2241_ = lean_ctor_get(v___y_2223_, 13);
v_ref_2242_ = l_Lean_replaceRef(v_ref_2219_, v_ref_2231_);
lean_inc_ref(v_inheritedTraceOptions_2241_);
lean_inc(v_cancelTk_x3f_2239_);
lean_inc(v_currMacroScope_2237_);
lean_inc(v_quotContext_2236_);
lean_inc(v_maxHeartbeats_2235_);
lean_inc(v_initHeartbeats_2234_);
lean_inc(v_openDecls_2233_);
lean_inc(v_currNamespace_2232_);
lean_inc(v_maxRecDepth_2230_);
lean_inc(v_currRecDepth_2229_);
lean_inc_ref(v_options_2228_);
lean_inc_ref(v_fileMap_2227_);
lean_inc_ref(v_fileName_2226_);
v___x_2243_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2243_, 0, v_fileName_2226_);
lean_ctor_set(v___x_2243_, 1, v_fileMap_2227_);
lean_ctor_set(v___x_2243_, 2, v_options_2228_);
lean_ctor_set(v___x_2243_, 3, v_currRecDepth_2229_);
lean_ctor_set(v___x_2243_, 4, v_maxRecDepth_2230_);
lean_ctor_set(v___x_2243_, 5, v_ref_2242_);
lean_ctor_set(v___x_2243_, 6, v_currNamespace_2232_);
lean_ctor_set(v___x_2243_, 7, v_openDecls_2233_);
lean_ctor_set(v___x_2243_, 8, v_initHeartbeats_2234_);
lean_ctor_set(v___x_2243_, 9, v_maxHeartbeats_2235_);
lean_ctor_set(v___x_2243_, 10, v_quotContext_2236_);
lean_ctor_set(v___x_2243_, 11, v_currMacroScope_2237_);
lean_ctor_set(v___x_2243_, 12, v_cancelTk_x3f_2239_);
lean_ctor_set(v___x_2243_, 13, v_inheritedTraceOptions_2241_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*14, v_diag_2238_);
lean_ctor_set_uint8(v___x_2243_, sizeof(void*)*14 + 1, v_suppressElabErrors_2240_);
v___x_2244_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2220_, v___y_2221_, v___y_2222_, v___x_2243_, v___y_2224_);
lean_dec_ref_known(v___x_2243_, 14);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2245_, lean_object* v_msg_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2245_, v_msg_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
lean_dec(v_ref_2245_);
return v_res_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2253_, lean_object* v_msg_2254_, lean_object* v_declHint_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v___x_2261_; lean_object* v_a_2262_; lean_object* v___x_2263_; 
v___x_2261_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2254_, v_declHint_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref(v___x_2261_);
v___x_2263_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2253_, v_a_2262_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2264_, lean_object* v_msg_2265_, lean_object* v_declHint_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v_res_2272_; 
v_res_2272_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2264_, v_msg_2265_, v_declHint_2266_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
lean_dec(v___y_2270_);
lean_dec_ref(v___y_2269_);
lean_dec(v___y_2268_);
lean_dec_ref(v___y_2267_);
lean_dec(v_ref_2264_);
return v_res_2272_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2277_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2278_ = l_Lean_stringToMessageData(v___x_2277_);
return v___x_2278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2279_, lean_object* v_constName_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v___x_2286_; uint8_t v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2286_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2287_ = 0;
lean_inc(v_constName_2280_);
v___x_2288_ = l_Lean_MessageData_ofConstName(v_constName_2280_, v___x_2287_);
v___x_2289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2286_);
lean_ctor_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2289_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2279_, v___x_2291_, v_constName_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2293_, lean_object* v_constName_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2293_, v_constName_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec(v_ref_2293_);
return v_res_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_ref_2307_; lean_object* v___x_2308_; 
v_ref_2307_ = lean_ctor_get(v___y_2304_, 5);
v___x_2308_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2307_, v_constName_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
lean_object* v_res_2315_; 
v_res_2315_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
lean_dec(v___y_2313_);
lean_dec_ref(v___y_2312_);
lean_dec(v___y_2311_);
lean_dec_ref(v___y_2310_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_, lean_object* v___y_2320_){
_start:
{
lean_object* v___x_2322_; lean_object* v_env_2323_; uint8_t v___x_2324_; lean_object* v___x_2325_; 
v___x_2322_ = lean_st_ref_get(v___y_2320_);
v_env_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc_ref(v_env_2323_);
lean_dec(v___x_2322_);
v___x_2324_ = 0;
lean_inc(v_constName_2316_);
v___x_2325_ = l_Lean_Environment_findConstVal_x3f(v_env_2323_, v_constName_2316_, v___x_2324_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v___x_2326_; 
v___x_2326_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_);
return v___x_2326_;
}
else
{
lean_object* v_val_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_constName_2316_);
v_val_2327_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2325_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_val_2327_);
lean_dec(v___x_2325_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
lean_ctor_set_tag(v___x_2329_, 0);
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_val_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
lean_dec(v___y_2339_);
lean_dec_ref(v___y_2338_);
lean_dec(v___y_2337_);
lean_dec_ref(v___y_2336_);
return v_res_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2348_; 
lean_inc(v_constName_2342_);
v___x_2348_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2342_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v_levelParams_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v_levelParams_2350_ = lean_ctor_get(v_a_2349_, 1);
v___x_2351_ = lean_box(0);
lean_inc(v_levelParams_2350_);
v___x_2352_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2350_, v___x_2351_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
lean_inc_n(v_a_2353_, 2);
lean_dec_ref_known(v___x_2352_, 1);
v___x_2354_ = l_Lean_mkConst(v_constName_2342_, v_a_2353_);
v___x_2355_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2349_, v_a_2353_, v_a_2346_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2364_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2358_ = v___x_2355_;
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2355_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2364_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2360_; lean_object* v___x_2362_; 
v___x_2360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2360_, 0, v___x_2354_);
lean_ctor_set(v___x_2360_, 1, v_a_2356_);
if (v_isShared_2359_ == 0)
{
lean_ctor_set(v___x_2358_, 0, v___x_2360_);
v___x_2362_ = v___x_2358_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2360_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec_ref(v___x_2354_);
v_a_2365_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2355_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2355_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v_a_2349_);
lean_dec(v_constName_2342_);
v_a_2373_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2352_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2352_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v_constName_2342_);
v_a_2381_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2348_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2348_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_, lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2389_, v_a_2390_, v_a_2391_, v_a_2392_, v_a_2393_);
lean_dec(v_a_2393_);
lean_dec_ref(v_a_2392_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2396_, lean_object* v_constName_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v___x_2403_; 
v___x_2403_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
return v___x_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2404_, lean_object* v_constName_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2404_, v_constName_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2412_, lean_object* v_ref_2413_, lean_object* v_constName_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2413_, v_constName_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_ref_2422_, lean_object* v_constName_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v_res_2429_; 
v_res_2429_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2421_, v_ref_2422_, v_constName_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v_ref_2422_);
return v_res_2429_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2430_, lean_object* v_ref_2431_, lean_object* v_msg_2432_, lean_object* v_declHint_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
lean_object* v___x_2439_; 
v___x_2439_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2431_, v_msg_2432_, v_declHint_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2440_, lean_object* v_ref_2441_, lean_object* v_msg_2442_, lean_object* v_declHint_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2440_, v_ref_2441_, v_msg_2442_, v_declHint_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v_ref_2441_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2450_, lean_object* v_declHint_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2450_, v_declHint_2451_, v___y_2455_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2458_, lean_object* v_declHint_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2458_, v_declHint_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2466_, lean_object* v_ref_2467_, lean_object* v_msg_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_){
_start:
{
lean_object* v___x_2474_; 
v___x_2474_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2467_, v_msg_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2475_, lean_object* v_ref_2476_, lean_object* v_msg_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2475_, v_ref_2476_, v_msg_2477_, v___y_2478_, v___y_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec(v_ref_2476_);
return v_res_2483_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2488_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2489_ = l_Lean_stringToMessageData(v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2490_, lean_object* v_f_2491_, lean_object* v_inst_2492_, lean_object* v_xs_2493_, lean_object* v_x_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; 
v___x_2500_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2501_ = lean_apply_1(v_inst_2490_, v_f_2491_);
v___x_2502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2502_, 0, v___x_2500_);
lean_ctor_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2502_);
lean_ctor_set(v___x_2504_, 1, v___x_2503_);
v___x_2505_ = lean_apply_1(v_inst_2492_, v_xs_2493_);
v___x_2506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2506_, 0, v___x_2504_);
lean_ctor_set(v___x_2506_, 1, v___x_2505_);
v___x_2507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2508_, lean_object* v_f_2509_, lean_object* v_inst_2510_, lean_object* v_xs_2511_, lean_object* v_x_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v_res_2518_; 
v_res_2518_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2508_, v_f_2509_, v_inst_2510_, v_xs_2511_, v_x_2512_, v___y_2513_, v___y_2514_, v___y_2515_, v___y_2516_);
lean_dec(v___y_2516_);
lean_dec_ref(v___y_2515_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec_ref(v_x_2512_);
return v_res_2518_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_instMonadEIO(lean_box(0));
return v___x_2519_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2520_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2521_ = l_StateRefT_x27_instMonad___redArg(v___x_2520_);
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2528_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2529_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2530_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___f_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2532_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2533_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2532_, v___x_2531_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2537_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2538_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2539_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2538_, v___x_2537_, v___x_2536_);
return v___x_2539_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___f_2541_; lean_object* v___f_2542_; lean_object* v___x_2543_; 
v___x_2540_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2541_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2542_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2543_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2542_, v___f_2541_, v___x_2540_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2544_; 
v___x_2544_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2544_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; 
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2546_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2545_);
return v___x_2546_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2547_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2548_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2547_);
return v___x_2548_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2549_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2550_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2549_);
return v___x_2550_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2552_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2551_);
return v___x_2552_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2565_ = l_Lean_Name_append(v___x_2564_, v___x_2563_);
return v___x_2565_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2572_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2573_ = l_Lean_Name_append(v___x_2572_, v___x_2571_);
return v___x_2573_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2574_; double v___x_2575_; 
v___x_2574_ = lean_unsigned_to_nat(1000000000u);
v___x_2575_ = lean_float_of_nat(v___x_2574_);
return v___x_2575_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2582_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2583_ = l_Lean_Name_append(v___x_2582_, v___x_2581_);
return v___x_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2584_, lean_object* v_inst_2585_, lean_object* v_f_2586_, lean_object* v_xs_2587_, lean_object* v_k_2588_, lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; lean_object* v_toApplicative_2595_; lean_object* v_toFunctor_2596_; lean_object* v_toSeq_2597_; lean_object* v_toSeqLeft_2598_; lean_object* v_toSeqRight_2599_; lean_object* v___f_2600_; lean_object* v___f_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___x_2604_; lean_object* v___f_2605_; lean_object* v___f_2606_; lean_object* v___f_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v_toApplicative_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2849_; 
v___x_2594_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2595_ = lean_ctor_get(v___x_2594_, 0);
v_toFunctor_2596_ = lean_ctor_get(v_toApplicative_2595_, 0);
v_toSeq_2597_ = lean_ctor_get(v_toApplicative_2595_, 2);
v_toSeqLeft_2598_ = lean_ctor_get(v_toApplicative_2595_, 3);
v_toSeqRight_2599_ = lean_ctor_get(v_toApplicative_2595_, 4);
v___f_2600_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2601_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2596_, 2);
v___f_2602_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2602_, 0, v_toFunctor_2596_);
v___f_2603_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2603_, 0, v_toFunctor_2596_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___f_2602_);
lean_ctor_set(v___x_2604_, 1, v___f_2603_);
lean_inc(v_toSeqRight_2599_);
v___f_2605_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2605_, 0, v_toSeqRight_2599_);
lean_inc(v_toSeqLeft_2598_);
v___f_2606_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2606_, 0, v_toSeqLeft_2598_);
lean_inc(v_toSeq_2597_);
v___f_2607_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2607_, 0, v_toSeq_2597_);
v___x_2608_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2604_);
lean_ctor_set(v___x_2608_, 1, v___f_2600_);
lean_ctor_set(v___x_2608_, 2, v___f_2607_);
lean_ctor_set(v___x_2608_, 3, v___f_2606_);
lean_ctor_set(v___x_2608_, 4, v___f_2605_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___f_2601_);
v___x_2610_ = l_StateRefT_x27_instMonad___redArg(v___x_2609_);
v_toApplicative_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2610_, 1);
lean_dec(v_unused_2850_);
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2849_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_toApplicative_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2849_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v_toFunctor_2615_; lean_object* v_toSeq_2616_; lean_object* v_toSeqLeft_2617_; lean_object* v_toSeqRight_2618_; lean_object* v___x_2620_; uint8_t v_isShared_2621_; uint8_t v_isSharedCheck_2847_; 
v_toFunctor_2615_ = lean_ctor_get(v_toApplicative_2611_, 0);
v_toSeq_2616_ = lean_ctor_get(v_toApplicative_2611_, 2);
v_toSeqLeft_2617_ = lean_ctor_get(v_toApplicative_2611_, 3);
v_toSeqRight_2618_ = lean_ctor_get(v_toApplicative_2611_, 4);
v_isSharedCheck_2847_ = !lean_is_exclusive(v_toApplicative_2611_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v_toApplicative_2611_, 1);
lean_dec(v_unused_2848_);
v___x_2620_ = v_toApplicative_2611_;
v_isShared_2621_ = v_isSharedCheck_2847_;
goto v_resetjp_2619_;
}
else
{
lean_inc(v_toSeqRight_2618_);
lean_inc(v_toSeqLeft_2617_);
lean_inc(v_toSeq_2616_);
lean_inc(v_toFunctor_2615_);
lean_dec(v_toApplicative_2611_);
v___x_2620_ = lean_box(0);
v_isShared_2621_ = v_isSharedCheck_2847_;
goto v_resetjp_2619_;
}
v_resetjp_2619_:
{
lean_object* v___f_2622_; lean_object* v___f_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___x_2626_; lean_object* v___f_2627_; lean_object* v___f_2628_; lean_object* v___f_2629_; lean_object* v___x_2631_; 
v___f_2622_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2623_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2615_);
v___f_2624_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2624_, 0, v_toFunctor_2615_);
v___f_2625_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2625_, 0, v_toFunctor_2615_);
v___x_2626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___f_2624_);
lean_ctor_set(v___x_2626_, 1, v___f_2625_);
v___f_2627_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2627_, 0, v_toSeqRight_2618_);
v___f_2628_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2628_, 0, v_toSeqLeft_2617_);
v___f_2629_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2629_, 0, v_toSeq_2616_);
if (v_isShared_2621_ == 0)
{
lean_ctor_set(v___x_2620_, 4, v___f_2627_);
lean_ctor_set(v___x_2620_, 3, v___f_2628_);
lean_ctor_set(v___x_2620_, 2, v___f_2629_);
lean_ctor_set(v___x_2620_, 1, v___f_2622_);
lean_ctor_set(v___x_2620_, 0, v___x_2626_);
v___x_2631_ = v___x_2620_;
goto v_reusejp_2630_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2626_);
lean_ctor_set(v_reuseFailAlloc_2846_, 1, v___f_2622_);
lean_ctor_set(v_reuseFailAlloc_2846_, 2, v___f_2629_);
lean_ctor_set(v_reuseFailAlloc_2846_, 3, v___f_2628_);
lean_ctor_set(v_reuseFailAlloc_2846_, 4, v___f_2627_);
v___x_2631_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2630_;
}
v_reusejp_2630_:
{
lean_object* v___x_2633_; 
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 1, v___f_2623_);
lean_ctor_set(v___x_2613_, 0, v___x_2631_);
v___x_2633_ = v___x_2613_;
goto v_reusejp_2632_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2631_);
lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___f_2623_);
v___x_2633_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2632_;
}
v_reusejp_2632_:
{
lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_toMonadRef_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v_options_2639_; uint8_t v_hasTrace_2640_; 
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2635_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2636_ = lean_ctor_get(v___x_2635_, 0);
v___x_2637_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2638_ = l_Lean_KVMap_instValueBool;
v_options_2639_ = lean_ctor_get(v_a_2591_, 2);
v_hasTrace_2640_ = lean_ctor_get_uint8(v_options_2639_, sizeof(void*)*1);
if (v_hasTrace_2640_ == 0)
{
lean_object* v___x_2641_; 
lean_dec_ref(v___x_2633_);
lean_dec(v_xs_2587_);
lean_dec(v_f_2586_);
lean_dec_ref(v_inst_2585_);
lean_dec_ref(v_inst_2584_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2641_ = lean_apply_5(v_k_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
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
v_inheritedTraceOptions_2655_ = lean_ctor_get(v_a_2591_, 13);
v___x_2656_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2689_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2689_, 0, v_inst_2584_);
lean_closure_set(v___f_2689_, 1, v_f_2586_);
lean_closure_set(v___f_2689_, 2, v_inst_2585_);
lean_closure_set(v___f_2689_, 3, v_xs_2587_);
v___f_2690_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2692_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2693_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2694_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2693_);
if (v___x_2694_ == 0)
{
lean_object* v___x_2817_; lean_object* v___x_2818_; uint8_t v___x_2819_; 
v___x_2817_ = l_Lean_trace_profiler;
v___x_2818_ = l_Lean_Option_get___redArg(v___x_2638_, v_options_2639_, v___x_2817_);
v___x_2819_ = lean_unbox(v___x_2818_);
lean_dec(v___x_2818_);
if (v___x_2819_ == 0)
{
lean_object* v___x_2820_; 
lean_dec_ref(v___f_2689_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2820_ = lean_apply_5(v_k_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2823_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2824_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2633_);
return v___x_2820_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_8690__overap_2826_; lean_object* v___x_2827_; 
lean_dec_ref_known(v___x_2820_, 1);
lean_inc(v_a_2821_);
v___x_2825_ = l_Lean_MessageData_ofExpr(v_a_2821_);
lean_inc_ref(v_toMonadRef_2636_);
lean_inc_ref(v___x_2633_);
v___x_8690__overap_2826_ = l_Lean_addTrace___redArg(v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, v___x_2822_, v___x_2825_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2827_ = lean_apply_5(v___x_8690__overap_2826_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2827_) == 0)
{
lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref(v___x_2633_);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2834_ == 0)
{
lean_object* v_unused_2835_; 
v_unused_2835_ = lean_ctor_get(v___x_2827_, 0);
lean_dec(v_unused_2835_);
v___x_2829_ = v___x_2827_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_dec(v___x_2827_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
lean_ctor_set(v___x_2829_, 0, v_a_2821_);
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2821_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
else
{
lean_object* v_a_2836_; lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
lean_dec(v_a_2821_);
v_a_2836_ = lean_ctor_get(v___x_2827_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2827_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2838_ = v___x_2827_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_inc(v_a_2836_);
lean_dec(v___x_2827_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
lean_inc(v_a_2836_);
if (v_isShared_2839_ == 0)
{
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
v___y_2685_ = v___x_2841_;
v_a_2686_ = v_a_2836_;
goto v___jp_2684_;
}
}
}
}
}
else
{
lean_object* v_a_2844_; 
v_a_2844_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2844_);
v___y_2685_ = v___x_2820_;
v_a_2686_ = v_a_2844_;
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
lean_dec_ref(v___x_2633_);
v___x_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2664_, 0, v___y_2659_);
return v___x_2664_;
}
else
{
lean_object* v___x_2665_; lean_object* v___x_8471__overap_2666_; lean_object* v___x_2667_; 
lean_inc_ref(v___y_2659_);
v___x_2665_ = l_Lean_Exception_toMessageData(v___y_2659_);
lean_inc_ref(v_toMonadRef_2636_);
v___x_8471__overap_2666_ = l_Lean_addTrace___redArg(v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, v___x_2661_, v___x_2665_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2667_ = lean_apply_5(v___x_8471__overap_2666_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
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
lean_dec_ref(v___x_2633_);
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
lean_object* v___x_2699_; double v___x_2700_; double v___x_2701_; double v___x_2702_; double v___x_2703_; double v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_8567__overap_2709_; lean_object* v___x_2710_; 
v___x_2699_ = lean_io_mono_nanos_now();
v___x_2700_ = lean_float_of_nat(v___y_2696_);
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
lean_inc_ref(v_toMonadRef_2636_);
v___x_8567__overap_2709_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, lean_box(0), v___x_2637_, v___f_2690_, v___x_2691_, v_hasTrace_2640_, v___x_2692_, v_options_2639_, v___x_2694_, v___y_2697_, v___f_2689_, v___x_2708_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2710_ = lean_apply_5(v___x_8567__overap_2709_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
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
v___y_2712_ = v___y_2718_;
v___y_2713_ = v___y_2719_;
v_a_2714_ = v___y_2717_;
goto v___jp_2711_;
}
else
{
lean_object* v___x_2724_; lean_object* v___x_8585__overap_2725_; lean_object* v___x_2726_; 
lean_inc_ref(v___y_2717_);
v___x_2724_ = l_Lean_Exception_toMessageData(v___y_2717_);
lean_inc_ref(v_toMonadRef_2636_);
lean_inc_ref(v___x_2633_);
v___x_8585__overap_2725_ = l_Lean_addTrace___redArg(v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, v___x_2721_, v___x_2724_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2726_ = lean_apply_5(v___x_8585__overap_2725_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_dec_ref_known(v___x_2726_, 1);
v___y_2712_ = v___y_2718_;
v___y_2713_ = v___y_2719_;
v_a_2714_ = v___y_2717_;
goto v___jp_2711_;
}
else
{
lean_object* v_a_2727_; 
lean_dec_ref(v___y_2717_);
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
v___y_2712_ = v___y_2718_;
v___y_2713_ = v___y_2719_;
v_a_2714_ = v_a_2727_;
goto v___jp_2711_;
}
}
}
else
{
v___y_2712_ = v___y_2718_;
v___y_2713_ = v___y_2719_;
v_a_2714_ = v___y_2717_;
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
v___y_2717_ = v_a_2731_;
v___y_2718_ = v___y_2729_;
v___y_2719_ = v___y_2730_;
v___y_2720_ = v___x_2733_;
goto v___jp_2716_;
}
else
{
v___y_2717_ = v_a_2731_;
v___y_2718_ = v___y_2729_;
v___y_2719_ = v___y_2730_;
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
lean_object* v___x_2743_; double v___x_2744_; double v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_8627__overap_2750_; lean_object* v___x_2751_; 
v___x_2743_ = lean_io_get_num_heartbeats();
v___x_2744_ = lean_float_of_nat(v___y_2740_);
v___x_2745_ = lean_float_of_nat(v___x_2743_);
v___x_2746_ = lean_box_float(v___x_2744_);
v___x_2747_ = lean_box_float(v___x_2745_);
v___x_2748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2748_, 0, v___x_2746_);
lean_ctor_set(v___x_2748_, 1, v___x_2747_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_a_2742_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
lean_inc_ref(v_toMonadRef_2636_);
v___x_8627__overap_2750_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, lean_box(0), v___x_2637_, v___f_2690_, v___x_2691_, v_hasTrace_2640_, v___x_2692_, v_options_2639_, v___x_2694_, v___y_2741_, v___f_2689_, v___x_2749_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2751_ = lean_apply_5(v___x_8627__overap_2750_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
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
lean_object* v___x_2765_; lean_object* v___x_8645__overap_2766_; lean_object* v___x_2767_; 
lean_inc_ref(v___y_2759_);
v___x_2765_ = l_Lean_Exception_toMessageData(v___y_2759_);
lean_inc_ref(v_toMonadRef_2636_);
lean_inc_ref(v___x_2633_);
v___x_8645__overap_2766_ = l_Lean_addTrace___redArg(v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, v___x_2762_, v___x_2765_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2767_ = lean_apply_5(v___x_8645__overap_2766_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
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
lean_object* v___x_8545__overap_2781_; lean_object* v___x_2782_; 
lean_inc_ref(v___x_2633_);
v___x_8545__overap_2781_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2633_, v___x_2634_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2782_ = lean_apply_5(v___x_8545__overap_2781_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v_a_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; uint8_t v___x_2786_; 
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___x_2784_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2785_ = l_Lean_Option_get___redArg(v___x_2638_, v_options_2639_, v___x_2784_);
v___x_2786_ = lean_unbox(v___x_2785_);
lean_dec(v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_io_mono_nanos_now();
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2788_ = lean_apply_5(v_k_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; uint8_t v___x_2792_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___x_2790_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2791_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2792_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2791_);
if (v___x_2792_ == 0)
{
v___y_2735_ = v___x_2787_;
v___y_2736_ = v_a_2783_;
v_a_2737_ = v_a_2789_;
goto v___jp_2734_;
}
else
{
lean_object* v___x_2793_; lean_object* v___x_8607__overap_2794_; lean_object* v___x_2795_; 
lean_inc(v_a_2789_);
v___x_2793_ = l_Lean_MessageData_ofExpr(v_a_2789_);
lean_inc_ref(v_toMonadRef_2636_);
lean_inc_ref(v___x_2633_);
v___x_8607__overap_2794_ = l_Lean_addTrace___redArg(v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, v___x_2790_, v___x_2793_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2795_ = lean_apply_5(v___x_8607__overap_2794_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_dec_ref_known(v___x_2795_, 1);
v___y_2735_ = v___x_2787_;
v___y_2736_ = v_a_2783_;
v_a_2737_ = v_a_2789_;
goto v___jp_2734_;
}
else
{
lean_object* v_a_2796_; 
lean_dec(v_a_2789_);
v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
lean_inc(v_a_2796_);
lean_dec_ref_known(v___x_2795_, 1);
v___y_2729_ = v___x_2787_;
v___y_2730_ = v_a_2783_;
v_a_2731_ = v_a_2796_;
goto v___jp_2728_;
}
}
}
else
{
lean_object* v_a_2797_; 
v_a_2797_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2788_, 1);
v___y_2729_ = v___x_2787_;
v___y_2730_ = v_a_2783_;
v_a_2731_ = v_a_2797_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2798_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2799_ = lean_apply_5(v_k_2588_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_object* v_a_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; uint8_t v___x_2803_; 
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___x_2801_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2802_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2655_, v_options_2639_, v___x_2802_);
if (v___x_2803_ == 0)
{
v___y_2776_ = v___x_2798_;
v___y_2777_ = v_a_2783_;
v_a_2778_ = v_a_2800_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2804_; lean_object* v___x_8667__overap_2805_; lean_object* v___x_2806_; 
lean_inc(v_a_2800_);
v___x_2804_ = l_Lean_MessageData_ofExpr(v_a_2800_);
lean_inc_ref(v_toMonadRef_2636_);
lean_inc_ref(v___x_2633_);
v___x_8667__overap_2805_ = l_Lean_addTrace___redArg(v___x_2633_, v___x_2634_, v_toMonadRef_2636_, v___x_2656_, v___x_2801_, v___x_2804_);
lean_inc(v_a_2592_);
lean_inc_ref(v_a_2591_);
lean_inc(v_a_2590_);
lean_inc_ref(v_a_2589_);
v___x_2806_ = lean_apply_5(v___x_8667__overap_2805_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_, lean_box(0));
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_dec_ref_known(v___x_2806_, 1);
v___y_2776_ = v___x_2798_;
v___y_2777_ = v_a_2783_;
v_a_2778_ = v_a_2800_;
goto v___jp_2775_;
}
else
{
lean_object* v_a_2807_; 
lean_dec(v_a_2800_);
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___y_2770_ = v___x_2798_;
v___y_2771_ = v_a_2783_;
v_a_2772_ = v_a_2807_;
goto v___jp_2769_;
}
}
}
else
{
lean_object* v_a_2808_; 
v_a_2808_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2770_ = v___x_2798_;
v___y_2771_ = v_a_2783_;
v_a_2772_ = v_a_2808_;
goto v___jp_2769_;
}
}
}
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec_ref(v___f_2689_);
lean_dec_ref(v___x_2633_);
lean_dec_ref(v_k_2588_);
v_a_2809_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2782_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2782_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2851_, lean_object* v_inst_2852_, lean_object* v_f_2853_, lean_object* v_xs_2854_, lean_object* v_k_2855_, lean_object* v_a_2856_, lean_object* v_a_2857_, lean_object* v_a_2858_, lean_object* v_a_2859_, lean_object* v_a_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2851_, v_inst_2852_, v_f_2853_, v_xs_2854_, v_k_2855_, v_a_2856_, v_a_2857_, v_a_2858_, v_a_2859_);
lean_dec(v_a_2859_);
lean_dec_ref(v_a_2858_);
lean_dec(v_a_2857_);
lean_dec_ref(v_a_2856_);
return v_res_2861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2862_, lean_object* v_00_u03b2_2863_, lean_object* v_inst_2864_, lean_object* v_inst_2865_, lean_object* v_f_2866_, lean_object* v_xs_2867_, lean_object* v_k_2868_, lean_object* v_a_2869_, lean_object* v_a_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_){
_start:
{
lean_object* v___x_2874_; 
v___x_2874_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2864_, v_inst_2865_, v_f_2866_, v_xs_2867_, v_k_2868_, v_a_2869_, v_a_2870_, v_a_2871_, v_a_2872_);
return v___x_2874_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2875_, lean_object* v_00_u03b2_2876_, lean_object* v_inst_2877_, lean_object* v_inst_2878_, lean_object* v_f_2879_, lean_object* v_xs_2880_, lean_object* v_k_2881_, lean_object* v_a_2882_, lean_object* v_a_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2875_, v_00_u03b2_2876_, v_inst_2877_, v_inst_2878_, v_f_2879_, v_xs_2880_, v_k_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_);
lean_dec(v_a_2885_);
lean_dec_ref(v_a_2884_);
lean_dec(v_a_2883_);
lean_dec_ref(v_a_2882_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2888_, uint8_t v_allowLevelAssignments_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2889_, v_k_2888_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2895_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2895_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
v_a_2904_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2895_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2895_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2912_, lean_object* v_allowLevelAssignments_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2919_; lean_object* v_res_2920_; 
v_allowLevelAssignments_boxed_2919_ = lean_unbox(v_allowLevelAssignments_2913_);
v_res_2920_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2912_, v_allowLevelAssignments_boxed_2919_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_);
lean_dec(v___y_2917_);
lean_dec_ref(v___y_2916_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2921_, lean_object* v_k_2922_, uint8_t v_allowLevelAssignments_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v___x_2929_; 
v___x_2929_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2922_, v_allowLevelAssignments_2923_, v___y_2924_, v___y_2925_, v___y_2926_, v___y_2927_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2930_, lean_object* v_k_2931_, lean_object* v_allowLevelAssignments_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2938_; lean_object* v_res_2939_; 
v_allowLevelAssignments_boxed_2938_ = lean_unbox(v_allowLevelAssignments_2932_);
v_res_2939_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2930_, v_k_2931_, v_allowLevelAssignments_boxed_2938_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
lean_dec(v___y_2936_);
lean_dec_ref(v___y_2935_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
return v_res_2939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2940_, lean_object* v_xs_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_){
_start:
{
lean_object* v___x_2947_; 
v___x_2947_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2940_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; lean_object* v_fst_2949_; lean_object* v_snd_2950_; lean_object* v___x_2951_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
v_fst_2949_ = lean_ctor_get(v_a_2948_, 0);
lean_inc(v_fst_2949_);
v_snd_2950_ = lean_ctor_get(v_a_2948_, 1);
lean_inc(v_snd_2950_);
lean_dec(v_a_2948_);
v___x_2951_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2949_, v_snd_2950_, v_xs_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
return v___x_2951_;
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
v_a_2952_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2947_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2947_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2960_, lean_object* v_xs_2961_, lean_object* v___y_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2960_, v_xs_2961_, v___y_2962_, v___y_2963_, v___y_2964_, v___y_2965_);
lean_dec(v___y_2965_);
lean_dec_ref(v___y_2964_);
lean_dec(v___y_2963_);
lean_dec_ref(v___y_2962_);
lean_dec_ref(v_xs_2961_);
return v_res_2967_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; 
v___x_2968_ = lean_unsigned_to_nat(32u);
v___x_2969_ = lean_mk_empty_array_with_capacity(v___x_2968_);
v___x_2970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2970_, 0, v___x_2969_);
return v___x_2970_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2971_ = ((size_t)5ULL);
v___x_2972_ = lean_unsigned_to_nat(0u);
v___x_2973_ = lean_unsigned_to_nat(32u);
v___x_2974_ = lean_mk_empty_array_with_capacity(v___x_2973_);
v___x_2975_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2976_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2976_, 0, v___x_2975_);
lean_ctor_set(v___x_2976_, 1, v___x_2974_);
lean_ctor_set(v___x_2976_, 2, v___x_2972_);
lean_ctor_set(v___x_2976_, 3, v___x_2972_);
lean_ctor_set_usize(v___x_2976_, 4, v___x_2971_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2977_){
_start:
{
lean_object* v___x_2979_; lean_object* v_traceState_2980_; lean_object* v_traces_2981_; lean_object* v___x_2982_; lean_object* v_traceState_2983_; lean_object* v_env_2984_; lean_object* v_nextMacroScope_2985_; lean_object* v_ngen_2986_; lean_object* v_auxDeclNGen_2987_; lean_object* v_cache_2988_; lean_object* v_messages_2989_; lean_object* v_infoState_2990_; lean_object* v_snapshotTasks_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_3010_; 
v___x_2979_ = lean_st_ref_get(v___y_2977_);
v_traceState_2980_ = lean_ctor_get(v___x_2979_, 4);
lean_inc_ref(v_traceState_2980_);
lean_dec(v___x_2979_);
v_traces_2981_ = lean_ctor_get(v_traceState_2980_, 0);
lean_inc_ref(v_traces_2981_);
lean_dec_ref(v_traceState_2980_);
v___x_2982_ = lean_st_ref_take(v___y_2977_);
v_traceState_2983_ = lean_ctor_get(v___x_2982_, 4);
v_env_2984_ = lean_ctor_get(v___x_2982_, 0);
v_nextMacroScope_2985_ = lean_ctor_get(v___x_2982_, 1);
v_ngen_2986_ = lean_ctor_get(v___x_2982_, 2);
v_auxDeclNGen_2987_ = lean_ctor_get(v___x_2982_, 3);
v_cache_2988_ = lean_ctor_get(v___x_2982_, 5);
v_messages_2989_ = lean_ctor_get(v___x_2982_, 6);
v_infoState_2990_ = lean_ctor_get(v___x_2982_, 7);
v_snapshotTasks_2991_ = lean_ctor_get(v___x_2982_, 8);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_2993_ = v___x_2982_;
v_isShared_2994_ = v_isSharedCheck_3010_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_snapshotTasks_2991_);
lean_inc(v_infoState_2990_);
lean_inc(v_messages_2989_);
lean_inc(v_cache_2988_);
lean_inc(v_traceState_2983_);
lean_inc(v_auxDeclNGen_2987_);
lean_inc(v_ngen_2986_);
lean_inc(v_nextMacroScope_2985_);
lean_inc(v_env_2984_);
lean_dec(v___x_2982_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_3010_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
uint64_t v_tid_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3008_; 
v_tid_2995_ = lean_ctor_get_uint64(v_traceState_2983_, sizeof(void*)*1);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_traceState_2983_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v_traceState_2983_, 0);
lean_dec(v_unused_3009_);
v___x_2997_ = v_traceState_2983_;
v_isShared_2998_ = v_isSharedCheck_3008_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v_traceState_2983_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3008_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_2999_; lean_object* v___x_3001_; 
v___x_2999_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_2999_);
v___x_3001_ = v___x_2997_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v___x_2999_);
lean_ctor_set_uint64(v_reuseFailAlloc_3007_, sizeof(void*)*1, v_tid_2995_);
v___x_3001_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3003_; 
if (v_isShared_2994_ == 0)
{
lean_ctor_set(v___x_2993_, 4, v___x_3001_);
v___x_3003_ = v___x_2993_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_env_2984_);
lean_ctor_set(v_reuseFailAlloc_3006_, 1, v_nextMacroScope_2985_);
lean_ctor_set(v_reuseFailAlloc_3006_, 2, v_ngen_2986_);
lean_ctor_set(v_reuseFailAlloc_3006_, 3, v_auxDeclNGen_2987_);
lean_ctor_set(v_reuseFailAlloc_3006_, 4, v___x_3001_);
lean_ctor_set(v_reuseFailAlloc_3006_, 5, v_cache_2988_);
lean_ctor_set(v_reuseFailAlloc_3006_, 6, v_messages_2989_);
lean_ctor_set(v_reuseFailAlloc_3006_, 7, v_infoState_2990_);
lean_ctor_set(v_reuseFailAlloc_3006_, 8, v_snapshotTasks_2991_);
v___x_3003_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
lean_object* v___x_3004_; lean_object* v___x_3005_; 
v___x_3004_ = lean_st_ref_put(v___y_2977_, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3005_, 0, v_traces_2981_);
return v___x_3005_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3011_, lean_object* v___y_3012_){
_start:
{
lean_object* v_res_3013_; 
v_res_3013_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3011_);
lean_dec(v___y_3011_);
return v_res_3013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3014_, lean_object* v_opt_3015_){
_start:
{
lean_object* v_name_3016_; lean_object* v_defValue_3017_; lean_object* v_map_3018_; lean_object* v___x_3019_; 
v_name_3016_ = lean_ctor_get(v_opt_3015_, 0);
v_defValue_3017_ = lean_ctor_get(v_opt_3015_, 1);
v_map_3018_ = lean_ctor_get(v_opts_3014_, 0);
v___x_3019_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3018_, v_name_3016_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_inc(v_defValue_3017_);
return v_defValue_3017_;
}
else
{
lean_object* v_val_3020_; 
v_val_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_val_3020_);
lean_dec_ref_known(v___x_3019_, 1);
if (lean_obj_tag(v_val_3020_) == 3)
{
lean_object* v_v_3021_; 
v_v_3021_ = lean_ctor_get(v_val_3020_, 0);
lean_inc(v_v_3021_);
lean_dec_ref_known(v_val_3020_, 1);
return v_v_3021_;
}
else
{
lean_dec(v_val_3020_);
lean_inc(v_defValue_3017_);
return v_defValue_3017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3022_, lean_object* v_opt_3023_){
_start:
{
lean_object* v_res_3024_; 
v_res_3024_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3022_, v_opt_3023_);
lean_dec_ref(v_opt_3023_);
lean_dec_ref(v_opts_3022_);
return v_res_3024_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3025_, lean_object* v_opt_3026_){
_start:
{
lean_object* v_name_3027_; lean_object* v_defValue_3028_; lean_object* v_map_3029_; lean_object* v___x_3030_; 
v_name_3027_ = lean_ctor_get(v_opt_3026_, 0);
v_defValue_3028_ = lean_ctor_get(v_opt_3026_, 1);
v_map_3029_ = lean_ctor_get(v_opts_3025_, 0);
v___x_3030_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3029_, v_name_3027_);
if (lean_obj_tag(v___x_3030_) == 0)
{
uint8_t v___x_3031_; 
v___x_3031_ = lean_unbox(v_defValue_3028_);
return v___x_3031_;
}
else
{
lean_object* v_val_3032_; 
v_val_3032_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_val_3032_);
lean_dec_ref_known(v___x_3030_, 1);
if (lean_obj_tag(v_val_3032_) == 1)
{
uint8_t v_v_3033_; 
v_v_3033_ = lean_ctor_get_uint8(v_val_3032_, 0);
lean_dec_ref_known(v_val_3032_, 0);
return v_v_3033_;
}
else
{
uint8_t v___x_3034_; 
lean_dec(v_val_3032_);
v___x_3034_ = lean_unbox(v_defValue_3028_);
return v___x_3034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3035_, lean_object* v_opt_3036_){
_start:
{
uint8_t v_res_3037_; lean_object* v_r_3038_; 
v_res_3037_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3035_, v_opt_3036_);
lean_dec_ref(v_opt_3036_);
lean_dec_ref(v_opts_3035_);
v_r_3038_ = lean_box(v_res_3037_);
return v_r_3038_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3039_){
_start:
{
if (lean_obj_tag(v_e_3039_) == 0)
{
uint8_t v___x_3040_; 
v___x_3040_ = 2;
return v___x_3040_;
}
else
{
lean_object* v_a_3041_; uint8_t v___x_3042_; 
v_a_3041_ = lean_ctor_get(v_e_3039_, 0);
v___x_3042_ = l_Lean_Expr_hasSyntheticSorry(v_a_3041_);
if (v___x_3042_ == 0)
{
uint8_t v___x_3043_; 
v___x_3043_ = 0;
return v___x_3043_;
}
else
{
uint8_t v___x_3044_; 
v___x_3044_ = 1;
return v___x_3044_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3045_){
_start:
{
uint8_t v_res_3046_; lean_object* v_r_3047_; 
v_res_3046_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3045_);
lean_dec_ref(v_e_3045_);
v_r_3047_ = lean_box(v_res_3046_);
return v_r_3047_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3048_, size_t v_i_3049_, lean_object* v_bs_3050_){
_start:
{
uint8_t v___x_3051_; 
v___x_3051_ = lean_usize_dec_lt(v_i_3049_, v_sz_3048_);
if (v___x_3051_ == 0)
{
return v_bs_3050_;
}
else
{
lean_object* v_v_3052_; lean_object* v_msg_3053_; lean_object* v___x_3054_; lean_object* v_bs_x27_3055_; size_t v___x_3056_; size_t v___x_3057_; lean_object* v___x_3058_; 
v_v_3052_ = lean_array_uget_borrowed(v_bs_3050_, v_i_3049_);
v_msg_3053_ = lean_ctor_get(v_v_3052_, 1);
lean_inc_ref(v_msg_3053_);
v___x_3054_ = lean_unsigned_to_nat(0u);
v_bs_x27_3055_ = lean_array_uset(v_bs_3050_, v_i_3049_, v___x_3054_);
v___x_3056_ = ((size_t)1ULL);
v___x_3057_ = lean_usize_add(v_i_3049_, v___x_3056_);
v___x_3058_ = lean_array_uset(v_bs_x27_3055_, v_i_3049_, v_msg_3053_);
v_i_3049_ = v___x_3057_;
v_bs_3050_ = v___x_3058_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3060_, lean_object* v_i_3061_, lean_object* v_bs_3062_){
_start:
{
size_t v_sz_boxed_3063_; size_t v_i_boxed_3064_; lean_object* v_res_3065_; 
v_sz_boxed_3063_ = lean_unbox_usize(v_sz_3060_);
lean_dec(v_sz_3060_);
v_i_boxed_3064_ = lean_unbox_usize(v_i_3061_);
lean_dec(v_i_3061_);
v_res_3065_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3063_, v_i_boxed_3064_, v_bs_3062_);
return v_res_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3066_, lean_object* v_data_3067_, lean_object* v_ref_3068_, lean_object* v_msg_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_fileName_3075_; lean_object* v_fileMap_3076_; lean_object* v_options_3077_; lean_object* v_currRecDepth_3078_; lean_object* v_maxRecDepth_3079_; lean_object* v_ref_3080_; lean_object* v_currNamespace_3081_; lean_object* v_openDecls_3082_; lean_object* v_initHeartbeats_3083_; lean_object* v_maxHeartbeats_3084_; lean_object* v_quotContext_3085_; lean_object* v_currMacroScope_3086_; uint8_t v_diag_3087_; lean_object* v_cancelTk_x3f_3088_; uint8_t v_suppressElabErrors_3089_; lean_object* v_inheritedTraceOptions_3090_; lean_object* v___x_3091_; lean_object* v_traceState_3092_; lean_object* v_traces_3093_; lean_object* v_ref_3094_; lean_object* v___x_3095_; lean_object* v___x_3096_; size_t v_sz_3097_; size_t v___x_3098_; lean_object* v___x_3099_; lean_object* v_msg_3100_; lean_object* v___x_3101_; lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3139_; 
v_fileName_3075_ = lean_ctor_get(v___y_3072_, 0);
v_fileMap_3076_ = lean_ctor_get(v___y_3072_, 1);
v_options_3077_ = lean_ctor_get(v___y_3072_, 2);
v_currRecDepth_3078_ = lean_ctor_get(v___y_3072_, 3);
v_maxRecDepth_3079_ = lean_ctor_get(v___y_3072_, 4);
v_ref_3080_ = lean_ctor_get(v___y_3072_, 5);
v_currNamespace_3081_ = lean_ctor_get(v___y_3072_, 6);
v_openDecls_3082_ = lean_ctor_get(v___y_3072_, 7);
v_initHeartbeats_3083_ = lean_ctor_get(v___y_3072_, 8);
v_maxHeartbeats_3084_ = lean_ctor_get(v___y_3072_, 9);
v_quotContext_3085_ = lean_ctor_get(v___y_3072_, 10);
v_currMacroScope_3086_ = lean_ctor_get(v___y_3072_, 11);
v_diag_3087_ = lean_ctor_get_uint8(v___y_3072_, sizeof(void*)*14);
v_cancelTk_x3f_3088_ = lean_ctor_get(v___y_3072_, 12);
v_suppressElabErrors_3089_ = lean_ctor_get_uint8(v___y_3072_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3090_ = lean_ctor_get(v___y_3072_, 13);
v___x_3091_ = lean_st_ref_get(v___y_3073_);
v_traceState_3092_ = lean_ctor_get(v___x_3091_, 4);
lean_inc_ref(v_traceState_3092_);
lean_dec(v___x_3091_);
v_traces_3093_ = lean_ctor_get(v_traceState_3092_, 0);
lean_inc_ref(v_traces_3093_);
lean_dec_ref(v_traceState_3092_);
v_ref_3094_ = l_Lean_replaceRef(v_ref_3068_, v_ref_3080_);
lean_inc_ref(v_inheritedTraceOptions_3090_);
lean_inc(v_cancelTk_x3f_3088_);
lean_inc(v_currMacroScope_3086_);
lean_inc(v_quotContext_3085_);
lean_inc(v_maxHeartbeats_3084_);
lean_inc(v_initHeartbeats_3083_);
lean_inc(v_openDecls_3082_);
lean_inc(v_currNamespace_3081_);
lean_inc(v_maxRecDepth_3079_);
lean_inc(v_currRecDepth_3078_);
lean_inc_ref(v_options_3077_);
lean_inc_ref(v_fileMap_3076_);
lean_inc_ref(v_fileName_3075_);
v___x_3095_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3095_, 0, v_fileName_3075_);
lean_ctor_set(v___x_3095_, 1, v_fileMap_3076_);
lean_ctor_set(v___x_3095_, 2, v_options_3077_);
lean_ctor_set(v___x_3095_, 3, v_currRecDepth_3078_);
lean_ctor_set(v___x_3095_, 4, v_maxRecDepth_3079_);
lean_ctor_set(v___x_3095_, 5, v_ref_3094_);
lean_ctor_set(v___x_3095_, 6, v_currNamespace_3081_);
lean_ctor_set(v___x_3095_, 7, v_openDecls_3082_);
lean_ctor_set(v___x_3095_, 8, v_initHeartbeats_3083_);
lean_ctor_set(v___x_3095_, 9, v_maxHeartbeats_3084_);
lean_ctor_set(v___x_3095_, 10, v_quotContext_3085_);
lean_ctor_set(v___x_3095_, 11, v_currMacroScope_3086_);
lean_ctor_set(v___x_3095_, 12, v_cancelTk_x3f_3088_);
lean_ctor_set(v___x_3095_, 13, v_inheritedTraceOptions_3090_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*14, v_diag_3087_);
lean_ctor_set_uint8(v___x_3095_, sizeof(void*)*14 + 1, v_suppressElabErrors_3089_);
v___x_3096_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3093_);
lean_dec_ref(v_traces_3093_);
v_sz_3097_ = lean_array_size(v___x_3096_);
v___x_3098_ = ((size_t)0ULL);
v___x_3099_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3097_, v___x_3098_, v___x_3096_);
v_msg_3100_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3100_, 0, v_data_3067_);
lean_ctor_set(v_msg_3100_, 1, v_msg_3069_);
lean_ctor_set(v_msg_3100_, 2, v___x_3099_);
v___x_3101_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3100_, v___y_3070_, v___y_3071_, v___x_3095_, v___y_3073_);
lean_dec_ref_known(v___x_3095_, 14);
v_a_3102_ = lean_ctor_get(v___x_3101_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3101_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3104_ = v___x_3101_;
v_isShared_3105_ = v_isSharedCheck_3139_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3101_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3139_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3106_; lean_object* v_traceState_3107_; lean_object* v_env_3108_; lean_object* v_nextMacroScope_3109_; lean_object* v_ngen_3110_; lean_object* v_auxDeclNGen_3111_; lean_object* v_cache_3112_; lean_object* v_messages_3113_; lean_object* v_infoState_3114_; lean_object* v_snapshotTasks_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3138_; 
v___x_3106_ = lean_st_ref_take(v___y_3073_);
v_traceState_3107_ = lean_ctor_get(v___x_3106_, 4);
v_env_3108_ = lean_ctor_get(v___x_3106_, 0);
v_nextMacroScope_3109_ = lean_ctor_get(v___x_3106_, 1);
v_ngen_3110_ = lean_ctor_get(v___x_3106_, 2);
v_auxDeclNGen_3111_ = lean_ctor_get(v___x_3106_, 3);
v_cache_3112_ = lean_ctor_get(v___x_3106_, 5);
v_messages_3113_ = lean_ctor_get(v___x_3106_, 6);
v_infoState_3114_ = lean_ctor_get(v___x_3106_, 7);
v_snapshotTasks_3115_ = lean_ctor_get(v___x_3106_, 8);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3117_ = v___x_3106_;
v_isShared_3118_ = v_isSharedCheck_3138_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_snapshotTasks_3115_);
lean_inc(v_infoState_3114_);
lean_inc(v_messages_3113_);
lean_inc(v_cache_3112_);
lean_inc(v_traceState_3107_);
lean_inc(v_auxDeclNGen_3111_);
lean_inc(v_ngen_3110_);
lean_inc(v_nextMacroScope_3109_);
lean_inc(v_env_3108_);
lean_dec(v___x_3106_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3138_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
uint64_t v_tid_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3136_; 
v_tid_3119_ = lean_ctor_get_uint64(v_traceState_3107_, sizeof(void*)*1);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_traceState_3107_);
if (v_isSharedCheck_3136_ == 0)
{
lean_object* v_unused_3137_; 
v_unused_3137_ = lean_ctor_get(v_traceState_3107_, 0);
lean_dec(v_unused_3137_);
v___x_3121_ = v_traceState_3107_;
v_isShared_3122_ = v_isSharedCheck_3136_;
goto v_resetjp_3120_;
}
else
{
lean_dec(v_traceState_3107_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3136_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3123_, 0, v_ref_3068_);
lean_ctor_set(v___x_3123_, 1, v_a_3102_);
v___x_3124_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3066_, v___x_3123_);
if (v_isShared_3122_ == 0)
{
lean_ctor_set(v___x_3121_, 0, v___x_3124_);
v___x_3126_ = v___x_3121_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3124_);
lean_ctor_set_uint64(v_reuseFailAlloc_3135_, sizeof(void*)*1, v_tid_3119_);
v___x_3126_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
lean_object* v___x_3128_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set(v___x_3117_, 4, v___x_3126_);
v___x_3128_ = v___x_3117_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_env_3108_);
lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_nextMacroScope_3109_);
lean_ctor_set(v_reuseFailAlloc_3134_, 2, v_ngen_3110_);
lean_ctor_set(v_reuseFailAlloc_3134_, 3, v_auxDeclNGen_3111_);
lean_ctor_set(v_reuseFailAlloc_3134_, 4, v___x_3126_);
lean_ctor_set(v_reuseFailAlloc_3134_, 5, v_cache_3112_);
lean_ctor_set(v_reuseFailAlloc_3134_, 6, v_messages_3113_);
lean_ctor_set(v_reuseFailAlloc_3134_, 7, v_infoState_3114_);
lean_ctor_set(v_reuseFailAlloc_3134_, 8, v_snapshotTasks_3115_);
v___x_3128_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3129_ = lean_st_ref_put(v___y_3073_, v___x_3128_);
v___x_3130_ = lean_box(0);
if (v_isShared_3105_ == 0)
{
lean_ctor_set(v___x_3104_, 0, v___x_3130_);
v___x_3132_ = v___x_3104_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3140_, lean_object* v_data_3141_, lean_object* v_ref_3142_, lean_object* v_msg_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3140_, v_data_3141_, v_ref_3142_, v_msg_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
lean_dec(v___y_3147_);
lean_dec_ref(v___y_3146_);
lean_dec(v___y_3145_);
lean_dec_ref(v___y_3144_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3150_){
_start:
{
if (lean_obj_tag(v_x_3150_) == 0)
{
lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
v_a_3152_ = lean_ctor_get(v_x_3150_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v_x_3150_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v_x_3150_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v_x_3150_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
lean_ctor_set_tag(v___x_3154_, 1);
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
else
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v_x_3150_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v_x_3150_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v_x_3150_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v_x_3150_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
lean_ctor_set_tag(v___x_3162_, 0);
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_res_3170_; 
v_res_3170_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3168_);
return v_res_3170_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3171_; double v___x_3172_; 
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = lean_float_of_nat(v___x_3171_);
return v___x_3172_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3174_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3175_ = l_Lean_stringToMessageData(v___x_3174_);
return v___x_3175_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3176_; double v___x_3177_; 
v___x_3176_ = lean_unsigned_to_nat(1000u);
v___x_3177_ = lean_float_of_nat(v___x_3176_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3178_, uint8_t v_collapsed_3179_, lean_object* v_tag_3180_, lean_object* v_opts_3181_, uint8_t v_clsEnabled_3182_, lean_object* v_oldTraces_3183_, lean_object* v_msg_3184_, lean_object* v_resStartStop_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_fst_3191_; lean_object* v_snd_3192_; lean_object* v___y_3194_; lean_object* v___y_3195_; lean_object* v_data_3196_; lean_object* v_fst_3207_; lean_object* v_snd_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; lean_object* v___y_3212_; lean_object* v_a_3213_; uint8_t v___y_3228_; double v___y_3259_; 
v_fst_3191_ = lean_ctor_get(v_resStartStop_3185_, 0);
lean_inc(v_fst_3191_);
v_snd_3192_ = lean_ctor_get(v_resStartStop_3185_, 1);
lean_inc(v_snd_3192_);
lean_dec_ref(v_resStartStop_3185_);
v_fst_3207_ = lean_ctor_get(v_snd_3192_, 0);
lean_inc(v_fst_3207_);
v_snd_3208_ = lean_ctor_get(v_snd_3192_, 1);
lean_inc(v_snd_3208_);
lean_dec(v_snd_3192_);
v___x_3209_ = l_Lean_trace_profiler;
v___x_3210_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3181_, v___x_3209_);
if (v___x_3210_ == 0)
{
v___y_3228_ = v___x_3210_;
goto v___jp_3227_;
}
else
{
lean_object* v___x_3264_; uint8_t v___x_3265_; 
v___x_3264_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3265_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3181_, v___x_3264_);
if (v___x_3265_ == 0)
{
lean_object* v___x_3266_; lean_object* v___x_3267_; double v___x_3268_; double v___x_3269_; double v___x_3270_; 
v___x_3266_ = l_Lean_trace_profiler_threshold;
v___x_3267_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3181_, v___x_3266_);
v___x_3268_ = lean_float_of_nat(v___x_3267_);
v___x_3269_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3270_ = lean_float_div(v___x_3268_, v___x_3269_);
v___y_3259_ = v___x_3270_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3271_; lean_object* v___x_3272_; double v___x_3273_; 
v___x_3271_ = l_Lean_trace_profiler_threshold;
v___x_3272_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3181_, v___x_3271_);
v___x_3273_ = lean_float_of_nat(v___x_3272_);
v___y_3259_ = v___x_3273_;
goto v___jp_3258_;
}
}
v___jp_3193_:
{
lean_object* v___x_3197_; 
lean_inc(v___y_3194_);
v___x_3197_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3183_, v_data_3196_, v___y_3194_, v___y_3195_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_);
if (lean_obj_tag(v___x_3197_) == 0)
{
lean_object* v___x_3198_; 
lean_dec_ref_known(v___x_3197_, 1);
v___x_3198_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3191_);
return v___x_3198_;
}
else
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3206_; 
lean_dec(v_fst_3191_);
v_a_3199_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3201_ = v___x_3197_;
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3197_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3206_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3204_; 
if (v_isShared_3202_ == 0)
{
v___x_3204_ = v___x_3201_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3205_; 
v_reuseFailAlloc_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3205_, 0, v_a_3199_);
v___x_3204_ = v_reuseFailAlloc_3205_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
return v___x_3204_;
}
}
}
}
v___jp_3211_:
{
uint8_t v_result_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; double v___x_3217_; lean_object* v_data_3218_; 
v_result_3214_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3191_);
v___x_3215_ = lean_box(v_result_3214_);
v___x_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3215_);
v___x_3217_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3180_);
lean_inc_ref(v___x_3216_);
lean_inc(v_cls_3178_);
v_data_3218_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3218_, 0, v_cls_3178_);
lean_ctor_set(v_data_3218_, 1, v___x_3216_);
lean_ctor_set(v_data_3218_, 2, v_tag_3180_);
lean_ctor_set_float(v_data_3218_, sizeof(void*)*3, v___x_3217_);
lean_ctor_set_float(v_data_3218_, sizeof(void*)*3 + 8, v___x_3217_);
lean_ctor_set_uint8(v_data_3218_, sizeof(void*)*3 + 16, v_collapsed_3179_);
if (v___x_3210_ == 0)
{
lean_dec_ref_known(v___x_3216_, 1);
lean_dec(v_snd_3208_);
lean_dec(v_fst_3207_);
lean_dec_ref(v_tag_3180_);
lean_dec(v_cls_3178_);
v___y_3194_ = v___y_3212_;
v___y_3195_ = v_a_3213_;
v_data_3196_ = v_data_3218_;
goto v___jp_3193_;
}
else
{
lean_object* v_data_3219_; double v___x_3220_; double v___x_3221_; 
lean_dec_ref_known(v_data_3218_, 3);
v_data_3219_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3219_, 0, v_cls_3178_);
lean_ctor_set(v_data_3219_, 1, v___x_3216_);
lean_ctor_set(v_data_3219_, 2, v_tag_3180_);
v___x_3220_ = lean_unbox_float(v_fst_3207_);
lean_dec(v_fst_3207_);
lean_ctor_set_float(v_data_3219_, sizeof(void*)*3, v___x_3220_);
v___x_3221_ = lean_unbox_float(v_snd_3208_);
lean_dec(v_snd_3208_);
lean_ctor_set_float(v_data_3219_, sizeof(void*)*3 + 8, v___x_3221_);
lean_ctor_set_uint8(v_data_3219_, sizeof(void*)*3 + 16, v_collapsed_3179_);
v___y_3194_ = v___y_3212_;
v___y_3195_ = v_a_3213_;
v_data_3196_ = v_data_3219_;
goto v___jp_3193_;
}
}
v___jp_3222_:
{
lean_object* v_ref_3223_; lean_object* v___x_3224_; 
v_ref_3223_ = lean_ctor_get(v___y_3188_, 5);
lean_inc(v___y_3189_);
lean_inc_ref(v___y_3188_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v_fst_3191_);
v___x_3224_ = lean_apply_6(v_msg_3184_, v_fst_3191_, v___y_3186_, v___y_3187_, v___y_3188_, v___y_3189_, lean_box(0));
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v___y_3212_ = v_ref_3223_;
v_a_3213_ = v_a_3225_;
goto v___jp_3211_;
}
else
{
lean_object* v___x_3226_; 
lean_dec_ref_known(v___x_3224_, 1);
v___x_3226_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3212_ = v_ref_3223_;
v_a_3213_ = v___x_3226_;
goto v___jp_3211_;
}
}
v___jp_3227_:
{
if (v_clsEnabled_3182_ == 0)
{
if (v___y_3228_ == 0)
{
lean_object* v___x_3229_; lean_object* v_traceState_3230_; lean_object* v_env_3231_; lean_object* v_nextMacroScope_3232_; lean_object* v_ngen_3233_; lean_object* v_auxDeclNGen_3234_; lean_object* v_cache_3235_; lean_object* v_messages_3236_; lean_object* v_infoState_3237_; lean_object* v_snapshotTasks_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v_snd_3208_);
lean_dec(v_fst_3207_);
lean_dec_ref(v_msg_3184_);
lean_dec_ref(v_tag_3180_);
lean_dec(v_cls_3178_);
v___x_3229_ = lean_st_ref_take(v___y_3189_);
v_traceState_3230_ = lean_ctor_get(v___x_3229_, 4);
v_env_3231_ = lean_ctor_get(v___x_3229_, 0);
v_nextMacroScope_3232_ = lean_ctor_get(v___x_3229_, 1);
v_ngen_3233_ = lean_ctor_get(v___x_3229_, 2);
v_auxDeclNGen_3234_ = lean_ctor_get(v___x_3229_, 3);
v_cache_3235_ = lean_ctor_get(v___x_3229_, 5);
v_messages_3236_ = lean_ctor_get(v___x_3229_, 6);
v_infoState_3237_ = lean_ctor_get(v___x_3229_, 7);
v_snapshotTasks_3238_ = lean_ctor_get(v___x_3229_, 8);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3240_ = v___x_3229_;
v_isShared_3241_ = v_isSharedCheck_3257_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_snapshotTasks_3238_);
lean_inc(v_infoState_3237_);
lean_inc(v_messages_3236_);
lean_inc(v_cache_3235_);
lean_inc(v_traceState_3230_);
lean_inc(v_auxDeclNGen_3234_);
lean_inc(v_ngen_3233_);
lean_inc(v_nextMacroScope_3232_);
lean_inc(v_env_3231_);
lean_dec(v___x_3229_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3257_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
uint64_t v_tid_3242_; lean_object* v_traces_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3256_; 
v_tid_3242_ = lean_ctor_get_uint64(v_traceState_3230_, sizeof(void*)*1);
v_traces_3243_ = lean_ctor_get(v_traceState_3230_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v_traceState_3230_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3245_ = v_traceState_3230_;
v_isShared_3246_ = v_isSharedCheck_3256_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_traces_3243_);
lean_dec(v_traceState_3230_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3256_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3247_; lean_object* v___x_3249_; 
v___x_3247_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3183_, v_traces_3243_);
lean_dec_ref(v_traces_3243_);
if (v_isShared_3246_ == 0)
{
lean_ctor_set(v___x_3245_, 0, v___x_3247_);
v___x_3249_ = v___x_3245_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3247_);
lean_ctor_set_uint64(v_reuseFailAlloc_3255_, sizeof(void*)*1, v_tid_3242_);
v___x_3249_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
lean_object* v___x_3251_; 
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 4, v___x_3249_);
v___x_3251_ = v___x_3240_;
goto v_reusejp_3250_;
}
else
{
lean_object* v_reuseFailAlloc_3254_; 
v_reuseFailAlloc_3254_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_env_3231_);
lean_ctor_set(v_reuseFailAlloc_3254_, 1, v_nextMacroScope_3232_);
lean_ctor_set(v_reuseFailAlloc_3254_, 2, v_ngen_3233_);
lean_ctor_set(v_reuseFailAlloc_3254_, 3, v_auxDeclNGen_3234_);
lean_ctor_set(v_reuseFailAlloc_3254_, 4, v___x_3249_);
lean_ctor_set(v_reuseFailAlloc_3254_, 5, v_cache_3235_);
lean_ctor_set(v_reuseFailAlloc_3254_, 6, v_messages_3236_);
lean_ctor_set(v_reuseFailAlloc_3254_, 7, v_infoState_3237_);
lean_ctor_set(v_reuseFailAlloc_3254_, 8, v_snapshotTasks_3238_);
v___x_3251_ = v_reuseFailAlloc_3254_;
goto v_reusejp_3250_;
}
v_reusejp_3250_:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = lean_st_ref_put(v___y_3189_, v___x_3251_);
v___x_3253_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3191_);
return v___x_3253_;
}
}
}
}
}
else
{
goto v___jp_3222_;
}
}
else
{
goto v___jp_3222_;
}
}
v___jp_3258_:
{
double v___x_3260_; double v___x_3261_; double v___x_3262_; uint8_t v___x_3263_; 
v___x_3260_ = lean_unbox_float(v_snd_3208_);
v___x_3261_ = lean_unbox_float(v_fst_3207_);
v___x_3262_ = lean_float_sub(v___x_3260_, v___x_3261_);
v___x_3263_ = lean_float_decLt(v___y_3259_, v___x_3262_);
v___y_3228_ = v___x_3263_;
goto v___jp_3227_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3274_, lean_object* v_collapsed_3275_, lean_object* v_tag_3276_, lean_object* v_opts_3277_, lean_object* v_clsEnabled_3278_, lean_object* v_oldTraces_3279_, lean_object* v_msg_3280_, lean_object* v_resStartStop_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
uint8_t v_collapsed_boxed_3287_; uint8_t v_clsEnabled_boxed_3288_; lean_object* v_res_3289_; 
v_collapsed_boxed_3287_ = lean_unbox(v_collapsed_3275_);
v_clsEnabled_boxed_3288_ = lean_unbox(v_clsEnabled_3278_);
v_res_3289_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3274_, v_collapsed_boxed_3287_, v_tag_3276_, v_opts_3277_, v_clsEnabled_boxed_3288_, v_oldTraces_3279_, v_msg_3280_, v_resStartStop_3281_, v___y_3282_, v___y_3283_, v___y_3284_, v___y_3285_);
lean_dec(v___y_3285_);
lean_dec_ref(v___y_3284_);
lean_dec(v___y_3283_);
lean_dec_ref(v___y_3282_);
lean_dec_ref(v_opts_3277_);
return v_res_3289_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3290_, lean_object* v_a_3291_){
_start:
{
if (lean_obj_tag(v_a_3290_) == 0)
{
lean_object* v___x_3292_; 
v___x_3292_ = l_List_reverse___redArg(v_a_3291_);
return v___x_3292_;
}
else
{
lean_object* v_head_3293_; lean_object* v_tail_3294_; lean_object* v___x_3296_; uint8_t v_isShared_3297_; uint8_t v_isSharedCheck_3303_; 
v_head_3293_ = lean_ctor_get(v_a_3290_, 0);
v_tail_3294_ = lean_ctor_get(v_a_3290_, 1);
v_isSharedCheck_3303_ = !lean_is_exclusive(v_a_3290_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3296_ = v_a_3290_;
v_isShared_3297_ = v_isSharedCheck_3303_;
goto v_resetjp_3295_;
}
else
{
lean_inc(v_tail_3294_);
lean_inc(v_head_3293_);
lean_dec(v_a_3290_);
v___x_3296_ = lean_box(0);
v_isShared_3297_ = v_isSharedCheck_3303_;
goto v_resetjp_3295_;
}
v_resetjp_3295_:
{
lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3298_ = l_Lean_MessageData_ofExpr(v_head_3293_);
if (v_isShared_3297_ == 0)
{
lean_ctor_set(v___x_3296_, 1, v_a_3291_);
lean_ctor_set(v___x_3296_, 0, v___x_3298_);
v___x_3300_ = v___x_3296_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3302_, 1, v_a_3291_);
v___x_3300_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
v_a_3290_ = v_tail_3294_;
v_a_3291_ = v___x_3300_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3304_, lean_object* v_xs_3305_, lean_object* v_x_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_){
_start:
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3312_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3313_ = l_Lean_MessageData_ofName(v_f_3304_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = lean_array_to_list(v_xs_3305_);
v___x_3318_ = lean_box(0);
v___x_3319_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3317_, v___x_3318_);
v___x_3320_ = l_Lean_MessageData_ofList(v___x_3319_);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3316_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3323_, lean_object* v_xs_3324_, lean_object* v_x_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3323_, v_xs_3324_, v_x_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v_x_3325_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3334_, lean_object* v_msg_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_ref_3341_; lean_object* v___x_3342_; lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3387_; 
v_ref_3341_ = lean_ctor_get(v___y_3338_, 5);
v___x_3342_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
v_a_3343_ = lean_ctor_get(v___x_3342_, 0);
v_isSharedCheck_3387_ = !lean_is_exclusive(v___x_3342_);
if (v_isSharedCheck_3387_ == 0)
{
v___x_3345_ = v___x_3342_;
v_isShared_3346_ = v_isSharedCheck_3387_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3342_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3387_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3347_; lean_object* v_traceState_3348_; lean_object* v_env_3349_; lean_object* v_nextMacroScope_3350_; lean_object* v_ngen_3351_; lean_object* v_auxDeclNGen_3352_; lean_object* v_cache_3353_; lean_object* v_messages_3354_; lean_object* v_infoState_3355_; lean_object* v_snapshotTasks_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3386_; 
v___x_3347_ = lean_st_ref_take(v___y_3339_);
v_traceState_3348_ = lean_ctor_get(v___x_3347_, 4);
v_env_3349_ = lean_ctor_get(v___x_3347_, 0);
v_nextMacroScope_3350_ = lean_ctor_get(v___x_3347_, 1);
v_ngen_3351_ = lean_ctor_get(v___x_3347_, 2);
v_auxDeclNGen_3352_ = lean_ctor_get(v___x_3347_, 3);
v_cache_3353_ = lean_ctor_get(v___x_3347_, 5);
v_messages_3354_ = lean_ctor_get(v___x_3347_, 6);
v_infoState_3355_ = lean_ctor_get(v___x_3347_, 7);
v_snapshotTasks_3356_ = lean_ctor_get(v___x_3347_, 8);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3358_ = v___x_3347_;
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_snapshotTasks_3356_);
lean_inc(v_infoState_3355_);
lean_inc(v_messages_3354_);
lean_inc(v_cache_3353_);
lean_inc(v_traceState_3348_);
lean_inc(v_auxDeclNGen_3352_);
lean_inc(v_ngen_3351_);
lean_inc(v_nextMacroScope_3350_);
lean_inc(v_env_3349_);
lean_dec(v___x_3347_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3386_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
uint64_t v_tid_3360_; lean_object* v_traces_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3385_; 
v_tid_3360_ = lean_ctor_get_uint64(v_traceState_3348_, sizeof(void*)*1);
v_traces_3361_ = lean_ctor_get(v_traceState_3348_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v_traceState_3348_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3363_ = v_traceState_3348_;
v_isShared_3364_ = v_isSharedCheck_3385_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_traces_3361_);
lean_dec(v_traceState_3348_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3385_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
lean_object* v___x_3365_; double v___x_3366_; uint8_t v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3365_ = lean_box(0);
v___x_3366_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3367_ = 0;
v___x_3368_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3369_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3369_, 0, v_cls_3334_);
lean_ctor_set(v___x_3369_, 1, v___x_3365_);
lean_ctor_set(v___x_3369_, 2, v___x_3368_);
lean_ctor_set_float(v___x_3369_, sizeof(void*)*3, v___x_3366_);
lean_ctor_set_float(v___x_3369_, sizeof(void*)*3 + 8, v___x_3366_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*3 + 16, v___x_3367_);
v___x_3370_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3371_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3369_);
lean_ctor_set(v___x_3371_, 1, v_a_3343_);
lean_ctor_set(v___x_3371_, 2, v___x_3370_);
lean_inc(v_ref_3341_);
v___x_3372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3372_, 0, v_ref_3341_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = l_Lean_PersistentArray_push___redArg(v_traces_3361_, v___x_3372_);
if (v_isShared_3364_ == 0)
{
lean_ctor_set(v___x_3363_, 0, v___x_3373_);
v___x_3375_ = v___x_3363_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3384_; 
v_reuseFailAlloc_3384_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3384_, 0, v___x_3373_);
lean_ctor_set_uint64(v_reuseFailAlloc_3384_, sizeof(void*)*1, v_tid_3360_);
v___x_3375_ = v_reuseFailAlloc_3384_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
lean_object* v___x_3377_; 
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 4, v___x_3375_);
v___x_3377_ = v___x_3358_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_env_3349_);
lean_ctor_set(v_reuseFailAlloc_3383_, 1, v_nextMacroScope_3350_);
lean_ctor_set(v_reuseFailAlloc_3383_, 2, v_ngen_3351_);
lean_ctor_set(v_reuseFailAlloc_3383_, 3, v_auxDeclNGen_3352_);
lean_ctor_set(v_reuseFailAlloc_3383_, 4, v___x_3375_);
lean_ctor_set(v_reuseFailAlloc_3383_, 5, v_cache_3353_);
lean_ctor_set(v_reuseFailAlloc_3383_, 6, v_messages_3354_);
lean_ctor_set(v_reuseFailAlloc_3383_, 7, v_infoState_3355_);
lean_ctor_set(v_reuseFailAlloc_3383_, 8, v_snapshotTasks_3356_);
v___x_3377_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3381_; 
v___x_3378_ = lean_st_ref_put(v___y_3339_, v___x_3377_);
v___x_3379_ = lean_box(0);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 0, v___x_3379_);
v___x_3381_ = v___x_3345_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3379_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3388_, lean_object* v_msg_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3388_, v_msg_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3396_, lean_object* v_xs_3397_, lean_object* v_k_3398_, lean_object* v_a_3399_, lean_object* v_a_3400_, lean_object* v_a_3401_, lean_object* v_a_3402_){
_start:
{
lean_object* v_options_3404_; uint8_t v_hasTrace_3405_; 
v_options_3404_ = lean_ctor_get(v_a_3401_, 2);
v_hasTrace_3405_ = lean_ctor_get_uint8(v_options_3404_, sizeof(void*)*1);
if (v_hasTrace_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_dec_ref(v_xs_3397_);
lean_dec(v_f_3396_);
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
lean_inc(v_a_3400_);
lean_inc_ref(v_a_3399_);
v___x_3406_ = lean_apply_5(v_k_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, lean_box(0));
return v___x_3406_;
}
else
{
lean_object* v_inheritedTraceOptions_3407_; lean_object* v___f_3408_; lean_object* v___y_3410_; lean_object* v___y_3411_; uint8_t v___y_3412_; lean_object* v___y_3436_; lean_object* v_a_3437_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; uint8_t v___x_3443_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v_a_3447_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v_a_3462_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; uint8_t v___y_3468_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v_a_3478_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v_a_3484_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_a_3489_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v_a_3501_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; uint8_t v___y_3507_; lean_object* v___y_3515_; lean_object* v___y_3516_; lean_object* v_a_3517_; lean_object* v___y_3521_; lean_object* v___y_3522_; lean_object* v_a_3523_; 
v_inheritedTraceOptions_3407_ = lean_ctor_get(v_a_3401_, 13);
v___f_3408_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3408_, 0, v_f_3396_);
lean_closure_set(v___f_3408_, 1, v_xs_3397_);
v___x_3440_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3441_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3442_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3443_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3404_, v___x_3442_);
if (v___x_3443_ == 0)
{
lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3550_ = l_Lean_trace_profiler;
v___x_3551_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3404_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; 
lean_dec_ref(v___f_3408_);
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
lean_inc(v_a_3400_);
lean_inc_ref(v_a_3399_);
v___x_3552_ = lean_apply_5(v_k_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, lean_box(0));
if (lean_obj_tag(v___x_3552_) == 0)
{
lean_object* v_a_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; uint8_t v___x_3556_; 
v_a_3553_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3553_);
v___x_3554_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3555_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3556_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3404_, v___x_3555_);
if (v___x_3556_ == 0)
{
lean_dec(v_a_3553_);
return v___x_3552_;
}
else
{
lean_object* v___x_3557_; lean_object* v___x_3558_; 
lean_dec_ref_known(v___x_3552_, 1);
lean_inc(v_a_3553_);
v___x_3557_ = l_Lean_MessageData_ofExpr(v_a_3553_);
v___x_3558_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3554_, v___x_3557_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v___x_3558_, 0);
lean_dec(v_unused_3566_);
v___x_3560_ = v___x_3558_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v___x_3558_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v_a_3553_);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3553_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec(v_a_3553_);
v_a_3567_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3558_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3558_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
lean_inc(v_a_3567_);
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
v___y_3436_ = v___x_3572_;
v_a_3437_ = v_a_3567_;
goto v___jp_3435_;
}
}
}
}
}
else
{
lean_object* v_a_3575_; 
v_a_3575_ = lean_ctor_get(v___x_3552_, 0);
lean_inc(v_a_3575_);
v___y_3436_ = v___x_3552_;
v_a_3437_ = v_a_3575_;
goto v___jp_3435_;
}
}
else
{
goto v___jp_3525_;
}
}
else
{
goto v___jp_3525_;
}
v___jp_3409_:
{
if (v___y_3412_ == 0)
{
lean_object* v___x_3413_; lean_object* v___x_3414_; uint8_t v___x_3415_; 
lean_dec_ref(v___y_3410_);
v___x_3413_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3414_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3415_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3404_, v___x_3414_);
if (v___x_3415_ == 0)
{
lean_object* v___x_3416_; 
v___x_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___y_3411_);
return v___x_3416_;
}
else
{
lean_object* v___x_3417_; lean_object* v___x_3418_; 
lean_inc_ref(v___y_3411_);
v___x_3417_ = l_Lean_Exception_toMessageData(v___y_3411_);
v___x_3418_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3413_, v___x_3417_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3418_) == 0)
{
lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3425_ == 0)
{
lean_object* v_unused_3426_; 
v_unused_3426_ = lean_ctor_get(v___x_3418_, 0);
lean_dec(v_unused_3426_);
v___x_3420_ = v___x_3418_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_dec(v___x_3418_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
lean_ctor_set_tag(v___x_3420_, 1);
lean_ctor_set(v___x_3420_, 0, v___y_3411_);
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v___y_3411_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3429_; uint8_t v_isShared_3430_; uint8_t v_isSharedCheck_3434_; 
lean_dec_ref(v___y_3411_);
v_a_3427_ = lean_ctor_get(v___x_3418_, 0);
v_isSharedCheck_3434_ = !lean_is_exclusive(v___x_3418_);
if (v_isSharedCheck_3434_ == 0)
{
v___x_3429_ = v___x_3418_;
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
else
{
lean_inc(v_a_3427_);
lean_dec(v___x_3418_);
v___x_3429_ = lean_box(0);
v_isShared_3430_ = v_isSharedCheck_3434_;
goto v_resetjp_3428_;
}
v_resetjp_3428_:
{
lean_object* v___x_3432_; 
if (v_isShared_3430_ == 0)
{
v___x_3432_ = v___x_3429_;
goto v_reusejp_3431_;
}
else
{
lean_object* v_reuseFailAlloc_3433_; 
v_reuseFailAlloc_3433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3433_, 0, v_a_3427_);
v___x_3432_ = v_reuseFailAlloc_3433_;
goto v_reusejp_3431_;
}
v_reusejp_3431_:
{
return v___x_3432_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3411_);
return v___y_3410_;
}
}
v___jp_3435_:
{
uint8_t v___x_3438_; 
v___x_3438_ = l_Lean_Exception_isInterrupt(v_a_3437_);
if (v___x_3438_ == 0)
{
uint8_t v___x_3439_; 
lean_inc_ref(v_a_3437_);
v___x_3439_ = l_Lean_Exception_isRuntime(v_a_3437_);
v___y_3410_ = v___y_3436_;
v___y_3411_ = v_a_3437_;
v___y_3412_ = v___x_3439_;
goto v___jp_3409_;
}
else
{
v___y_3410_ = v___y_3436_;
v___y_3411_ = v_a_3437_;
v___y_3412_ = v___x_3438_;
goto v___jp_3409_;
}
}
v___jp_3444_:
{
lean_object* v___x_3448_; double v___x_3449_; double v___x_3450_; double v___x_3451_; double v___x_3452_; double v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3448_ = lean_io_mono_nanos_now();
v___x_3449_ = lean_float_of_nat(v___y_3445_);
v___x_3450_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3451_ = lean_float_div(v___x_3449_, v___x_3450_);
v___x_3452_ = lean_float_of_nat(v___x_3448_);
v___x_3453_ = lean_float_div(v___x_3452_, v___x_3450_);
v___x_3454_ = lean_box_float(v___x_3451_);
v___x_3455_ = lean_box_float(v___x_3453_);
v___x_3456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3454_);
lean_ctor_set(v___x_3456_, 1, v___x_3455_);
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v_a_3447_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3440_, v_hasTrace_3405_, v___x_3441_, v_options_3404_, v___x_3443_, v___y_3446_, v___f_3408_, v___x_3457_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
return v___x_3458_;
}
v___jp_3459_:
{
lean_object* v___x_3463_; 
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v_a_3462_);
v___y_3445_ = v___y_3460_;
v___y_3446_ = v___y_3461_;
v_a_3447_ = v___x_3463_;
goto v___jp_3444_;
}
v___jp_3464_:
{
if (v___y_3468_ == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3470_; uint8_t v___x_3471_; 
v___x_3469_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3470_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3471_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3404_, v___x_3470_);
if (v___x_3471_ == 0)
{
v___y_3460_ = v___y_3466_;
v___y_3461_ = v___y_3467_;
v_a_3462_ = v___y_3465_;
goto v___jp_3459_;
}
else
{
lean_object* v___x_3472_; lean_object* v___x_3473_; 
lean_inc_ref(v___y_3465_);
v___x_3472_ = l_Lean_Exception_toMessageData(v___y_3465_);
v___x_3473_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3469_, v___x_3472_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_dec_ref_known(v___x_3473_, 1);
v___y_3460_ = v___y_3466_;
v___y_3461_ = v___y_3467_;
v_a_3462_ = v___y_3465_;
goto v___jp_3459_;
}
else
{
lean_object* v_a_3474_; 
lean_dec_ref(v___y_3465_);
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_a_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___y_3460_ = v___y_3466_;
v___y_3461_ = v___y_3467_;
v_a_3462_ = v_a_3474_;
goto v___jp_3459_;
}
}
}
else
{
v___y_3460_ = v___y_3466_;
v___y_3461_ = v___y_3467_;
v_a_3462_ = v___y_3465_;
goto v___jp_3459_;
}
}
v___jp_3475_:
{
uint8_t v___x_3479_; 
v___x_3479_ = l_Lean_Exception_isInterrupt(v_a_3478_);
if (v___x_3479_ == 0)
{
uint8_t v___x_3480_; 
lean_inc_ref(v_a_3478_);
v___x_3480_ = l_Lean_Exception_isRuntime(v_a_3478_);
v___y_3465_ = v_a_3478_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___x_3480_;
goto v___jp_3464_;
}
else
{
v___y_3465_ = v_a_3478_;
v___y_3466_ = v___y_3476_;
v___y_3467_ = v___y_3477_;
v___y_3468_ = v___x_3479_;
goto v___jp_3464_;
}
}
v___jp_3481_:
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3485_, 0, v_a_3484_);
v___y_3445_ = v___y_3482_;
v___y_3446_ = v___y_3483_;
v_a_3447_ = v___x_3485_;
goto v___jp_3444_;
}
v___jp_3486_:
{
lean_object* v___x_3490_; double v___x_3491_; double v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3490_ = lean_io_get_num_heartbeats();
v___x_3491_ = lean_float_of_nat(v___y_3487_);
v___x_3492_ = lean_float_of_nat(v___x_3490_);
v___x_3493_ = lean_box_float(v___x_3491_);
v___x_3494_ = lean_box_float(v___x_3492_);
v___x_3495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3493_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3496_, 0, v_a_3489_);
lean_ctor_set(v___x_3496_, 1, v___x_3495_);
v___x_3497_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3440_, v_hasTrace_3405_, v___x_3441_, v_options_3404_, v___x_3443_, v___y_3488_, v___f_3408_, v___x_3496_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
return v___x_3497_;
}
v___jp_3498_:
{
lean_object* v___x_3502_; 
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_a_3501_);
v___y_3487_ = v___y_3499_;
v___y_3488_ = v___y_3500_;
v_a_3489_ = v___x_3502_;
goto v___jp_3486_;
}
v___jp_3503_:
{
if (v___y_3507_ == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; uint8_t v___x_3510_; 
v___x_3508_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3509_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3510_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3404_, v___x_3509_);
if (v___x_3510_ == 0)
{
v___y_3499_ = v___y_3504_;
v___y_3500_ = v___y_3505_;
v_a_3501_ = v___y_3506_;
goto v___jp_3498_;
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_inc_ref(v___y_3506_);
v___x_3511_ = l_Lean_Exception_toMessageData(v___y_3506_);
v___x_3512_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3508_, v___x_3511_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_dec_ref_known(v___x_3512_, 1);
v___y_3499_ = v___y_3504_;
v___y_3500_ = v___y_3505_;
v_a_3501_ = v___y_3506_;
goto v___jp_3498_;
}
else
{
lean_object* v_a_3513_; 
lean_dec_ref(v___y_3506_);
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
v___y_3499_ = v___y_3504_;
v___y_3500_ = v___y_3505_;
v_a_3501_ = v_a_3513_;
goto v___jp_3498_;
}
}
}
else
{
v___y_3499_ = v___y_3504_;
v___y_3500_ = v___y_3505_;
v_a_3501_ = v___y_3506_;
goto v___jp_3498_;
}
}
v___jp_3514_:
{
uint8_t v___x_3518_; 
v___x_3518_ = l_Lean_Exception_isInterrupt(v_a_3517_);
if (v___x_3518_ == 0)
{
uint8_t v___x_3519_; 
lean_inc_ref(v_a_3517_);
v___x_3519_ = l_Lean_Exception_isRuntime(v_a_3517_);
v___y_3504_ = v___y_3515_;
v___y_3505_ = v___y_3516_;
v___y_3506_ = v_a_3517_;
v___y_3507_ = v___x_3519_;
goto v___jp_3503_;
}
else
{
v___y_3504_ = v___y_3515_;
v___y_3505_ = v___y_3516_;
v___y_3506_ = v_a_3517_;
v___y_3507_ = v___x_3518_;
goto v___jp_3503_;
}
}
v___jp_3520_:
{
lean_object* v___x_3524_; 
v___x_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3524_, 0, v_a_3523_);
v___y_3487_ = v___y_3521_;
v___y_3488_ = v___y_3522_;
v_a_3489_ = v___x_3524_;
goto v___jp_3486_;
}
v___jp_3525_:
{
lean_object* v___x_3526_; lean_object* v_a_3527_; lean_object* v___x_3528_; uint8_t v___x_3529_; 
v___x_3526_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3402_);
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3526_);
v___x_3528_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3529_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3404_, v___x_3528_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; lean_object* v___x_3531_; 
v___x_3530_ = lean_io_mono_nanos_now();
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
lean_inc(v_a_3400_);
lean_inc_ref(v_a_3399_);
v___x_3531_ = lean_apply_5(v_k_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, lean_box(0));
if (lean_obj_tag(v___x_3531_) == 0)
{
lean_object* v_a_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; uint8_t v___x_3535_; 
v_a_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3532_);
lean_dec_ref_known(v___x_3531_, 1);
v___x_3533_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3534_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3535_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3404_, v___x_3534_);
if (v___x_3535_ == 0)
{
v___y_3482_ = v___x_3530_;
v___y_3483_ = v_a_3527_;
v_a_3484_ = v_a_3532_;
goto v___jp_3481_;
}
else
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
lean_inc(v_a_3532_);
v___x_3536_ = l_Lean_MessageData_ofExpr(v_a_3532_);
v___x_3537_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3533_, v___x_3536_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3537_) == 0)
{
lean_dec_ref_known(v___x_3537_, 1);
v___y_3482_ = v___x_3530_;
v___y_3483_ = v_a_3527_;
v_a_3484_ = v_a_3532_;
goto v___jp_3481_;
}
else
{
lean_object* v_a_3538_; 
lean_dec(v_a_3532_);
v_a_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc(v_a_3538_);
lean_dec_ref_known(v___x_3537_, 1);
v___y_3476_ = v___x_3530_;
v___y_3477_ = v_a_3527_;
v_a_3478_ = v_a_3538_;
goto v___jp_3475_;
}
}
}
else
{
lean_object* v_a_3539_; 
v_a_3539_ = lean_ctor_get(v___x_3531_, 0);
lean_inc(v_a_3539_);
lean_dec_ref_known(v___x_3531_, 1);
v___y_3476_ = v___x_3530_;
v___y_3477_ = v_a_3527_;
v_a_3478_ = v_a_3539_;
goto v___jp_3475_;
}
}
else
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3402_);
lean_inc_ref(v_a_3401_);
lean_inc(v_a_3400_);
lean_inc_ref(v_a_3399_);
v___x_3541_ = lean_apply_5(v_k_3398_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_, lean_box(0));
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3544_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3407_, v_options_3404_, v___x_3544_);
if (v___x_3545_ == 0)
{
v___y_3521_ = v___x_3540_;
v___y_3522_ = v_a_3527_;
v_a_3523_ = v_a_3542_;
goto v___jp_3520_;
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_inc(v_a_3542_);
v___x_3546_ = l_Lean_MessageData_ofExpr(v_a_3542_);
v___x_3547_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3543_, v___x_3546_, v_a_3399_, v_a_3400_, v_a_3401_, v_a_3402_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref_known(v___x_3547_, 1);
v___y_3521_ = v___x_3540_;
v___y_3522_ = v_a_3527_;
v_a_3523_ = v_a_3542_;
goto v___jp_3520_;
}
else
{
lean_object* v_a_3548_; 
lean_dec(v_a_3542_);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v___y_3515_ = v___x_3540_;
v___y_3516_ = v_a_3527_;
v_a_3517_ = v_a_3548_;
goto v___jp_3514_;
}
}
}
else
{
lean_object* v_a_3549_; 
v_a_3549_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3541_, 1);
v___y_3515_ = v___x_3540_;
v___y_3516_ = v_a_3527_;
v_a_3517_ = v_a_3549_;
goto v___jp_3514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3576_, lean_object* v_xs_3577_, lean_object* v_k_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_){
_start:
{
lean_object* v_res_3584_; 
v_res_3584_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3576_, v_xs_3577_, v_k_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
lean_dec(v_a_3580_);
lean_dec_ref(v_a_3579_);
return v_res_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3585_, lean_object* v_xs_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_){
_start:
{
lean_object* v___f_3592_; uint8_t v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
lean_inc_ref(v_xs_3586_);
lean_inc(v_constName_3585_);
v___f_3592_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3592_, 0, v_constName_3585_);
lean_closure_set(v___f_3592_, 1, v_xs_3586_);
v___x_3593_ = 0;
v___x_3594_ = lean_box(v___x_3593_);
v___x_3595_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3595_, 0, lean_box(0));
lean_closure_set(v___x_3595_, 1, v___f_3592_);
lean_closure_set(v___x_3595_, 2, v___x_3594_);
v___x_3596_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3585_, v_xs_3586_, v___x_3595_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3597_, lean_object* v_xs_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_, lean_object* v_a_3601_, lean_object* v_a_3602_, lean_object* v_a_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Meta_mkAppM(v_constName_3597_, v_xs_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_);
lean_dec(v_a_3602_);
lean_dec_ref(v_a_3601_);
lean_dec(v_a_3600_);
lean_dec_ref(v_a_3599_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v___x_3610_; 
v___x_3610_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3608_);
return v___x_3610_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
lean_object* v_res_3616_; 
v_res_3616_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3611_, v___y_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
return v_res_3616_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3617_, lean_object* v_x_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_){
_start:
{
lean_object* v___x_3624_; 
v___x_3624_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3618_);
return v___x_3624_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3625_, lean_object* v_x_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_){
_start:
{
lean_object* v_res_3632_; 
v_res_3632_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3625_, v_x_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec_ref(v___y_3627_);
return v_res_3632_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3633_, lean_object* v_xs_3634_, lean_object* v_x_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_){
_start:
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v___x_3641_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3642_ = l_Lean_MessageData_ofExpr(v_f_3633_);
v___x_3643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3641_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3643_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_array_to_list(v_xs_3634_);
v___x_3647_ = lean_box(0);
v___x_3648_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3646_, v___x_3647_);
v___x_3649_ = l_Lean_MessageData_ofList(v___x_3648_);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3645_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3650_);
return v___x_3651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3652_, lean_object* v_xs_3653_, lean_object* v_x_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_){
_start:
{
lean_object* v_res_3660_; 
v_res_3660_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3652_, v_xs_3653_, v_x_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_);
lean_dec(v___y_3658_);
lean_dec_ref(v___y_3657_);
lean_dec(v___y_3656_);
lean_dec_ref(v___y_3655_);
lean_dec_ref(v_x_3654_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3661_, lean_object* v_xs_3662_, lean_object* v_k_3663_, lean_object* v_a_3664_, lean_object* v_a_3665_, lean_object* v_a_3666_, lean_object* v_a_3667_){
_start:
{
lean_object* v_options_3669_; uint8_t v_hasTrace_3670_; 
v_options_3669_ = lean_ctor_get(v_a_3666_, 2);
v_hasTrace_3670_ = lean_ctor_get_uint8(v_options_3669_, sizeof(void*)*1);
if (v_hasTrace_3670_ == 0)
{
lean_object* v___x_3671_; 
lean_dec_ref(v_xs_3662_);
lean_dec_ref(v_f_3661_);
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
lean_inc(v_a_3665_);
lean_inc_ref(v_a_3664_);
v___x_3671_ = lean_apply_5(v_k_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, lean_box(0));
return v___x_3671_;
}
else
{
lean_object* v_inheritedTraceOptions_3672_; lean_object* v___f_3673_; lean_object* v___y_3675_; lean_object* v___y_3676_; uint8_t v___y_3677_; lean_object* v___y_3701_; lean_object* v_a_3702_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___x_3708_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v_a_3712_; lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_a_3727_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; uint8_t v___y_3733_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v_a_3743_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v_a_3749_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v_a_3754_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v_a_3766_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v___y_3771_; uint8_t v___y_3772_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v_a_3782_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v_a_3788_; 
v_inheritedTraceOptions_3672_ = lean_ctor_get(v_a_3666_, 13);
v___f_3673_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3673_, 0, v_f_3661_);
lean_closure_set(v___f_3673_, 1, v_xs_3662_);
v___x_3705_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3706_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3707_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3708_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3672_, v_options_3669_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3815_; uint8_t v___x_3816_; 
v___x_3815_ = l_Lean_trace_profiler;
v___x_3816_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3669_, v___x_3815_);
if (v___x_3816_ == 0)
{
lean_object* v___x_3817_; 
lean_dec_ref(v___f_3673_);
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
lean_inc(v_a_3665_);
lean_inc_ref(v_a_3664_);
v___x_3817_ = lean_apply_5(v_k_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, lean_box(0));
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
v___x_3819_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3820_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3672_, v_options_3669_, v___x_3820_);
if (v___x_3821_ == 0)
{
lean_dec(v_a_3818_);
return v___x_3817_;
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
lean_dec_ref_known(v___x_3817_, 1);
lean_inc(v_a_3818_);
v___x_3822_ = l_Lean_MessageData_ofExpr(v_a_3818_);
v___x_3823_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3819_, v___x_3822_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; 
v_unused_3831_ = lean_ctor_get(v___x_3823_, 0);
lean_dec(v_unused_3831_);
v___x_3825_ = v___x_3823_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_dec(v___x_3823_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
lean_ctor_set(v___x_3825_, 0, v_a_3818_);
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3818_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_dec(v_a_3818_);
v_a_3832_ = lean_ctor_get(v___x_3823_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3823_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3823_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
lean_inc(v_a_3832_);
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
v___y_3701_ = v___x_3837_;
v_a_3702_ = v_a_3832_;
goto v___jp_3700_;
}
}
}
}
}
else
{
lean_object* v_a_3840_; 
v_a_3840_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3840_);
v___y_3701_ = v___x_3817_;
v_a_3702_ = v_a_3840_;
goto v___jp_3700_;
}
}
else
{
goto v___jp_3790_;
}
}
else
{
goto v___jp_3790_;
}
v___jp_3674_:
{
if (v___y_3677_ == 0)
{
lean_object* v___x_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
lean_dec_ref(v___y_3675_);
v___x_3678_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3679_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3672_, v_options_3669_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; 
v___x_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3681_, 0, v___y_3676_);
return v___x_3681_;
}
else
{
lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_inc_ref(v___y_3676_);
v___x_3682_ = l_Lean_Exception_toMessageData(v___y_3676_);
v___x_3683_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3678_, v___x_3682_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3690_ == 0)
{
lean_object* v_unused_3691_; 
v_unused_3691_ = lean_ctor_get(v___x_3683_, 0);
lean_dec(v_unused_3691_);
v___x_3685_ = v___x_3683_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_dec(v___x_3683_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 1);
lean_ctor_set(v___x_3685_, 0, v___y_3676_);
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___y_3676_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
lean_dec_ref(v___y_3676_);
v_a_3692_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3683_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3683_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3676_);
return v___y_3675_;
}
}
v___jp_3700_:
{
uint8_t v___x_3703_; 
v___x_3703_ = l_Lean_Exception_isInterrupt(v_a_3702_);
if (v___x_3703_ == 0)
{
uint8_t v___x_3704_; 
lean_inc_ref(v_a_3702_);
v___x_3704_ = l_Lean_Exception_isRuntime(v_a_3702_);
v___y_3675_ = v___y_3701_;
v___y_3676_ = v_a_3702_;
v___y_3677_ = v___x_3704_;
goto v___jp_3674_;
}
else
{
v___y_3675_ = v___y_3701_;
v___y_3676_ = v_a_3702_;
v___y_3677_ = v___x_3703_;
goto v___jp_3674_;
}
}
v___jp_3709_:
{
lean_object* v___x_3713_; double v___x_3714_; double v___x_3715_; double v___x_3716_; double v___x_3717_; double v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3713_ = lean_io_mono_nanos_now();
v___x_3714_ = lean_float_of_nat(v___y_3711_);
v___x_3715_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3716_ = lean_float_div(v___x_3714_, v___x_3715_);
v___x_3717_ = lean_float_of_nat(v___x_3713_);
v___x_3718_ = lean_float_div(v___x_3717_, v___x_3715_);
v___x_3719_ = lean_box_float(v___x_3716_);
v___x_3720_ = lean_box_float(v___x_3718_);
v___x_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3719_);
lean_ctor_set(v___x_3721_, 1, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v_a_3712_);
lean_ctor_set(v___x_3722_, 1, v___x_3721_);
v___x_3723_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3705_, v_hasTrace_3670_, v___x_3706_, v_options_3669_, v___x_3708_, v___y_3710_, v___f_3673_, v___x_3722_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
return v___x_3723_;
}
v___jp_3724_:
{
lean_object* v___x_3728_; 
v___x_3728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3728_, 0, v_a_3727_);
v___y_3710_ = v___y_3725_;
v___y_3711_ = v___y_3726_;
v_a_3712_ = v___x_3728_;
goto v___jp_3709_;
}
v___jp_3729_:
{
if (v___y_3733_ == 0)
{
lean_object* v___x_3734_; lean_object* v___x_3735_; uint8_t v___x_3736_; 
v___x_3734_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3735_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3736_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3672_, v_options_3669_, v___x_3735_);
if (v___x_3736_ == 0)
{
v___y_3725_ = v___y_3731_;
v___y_3726_ = v___y_3732_;
v_a_3727_ = v___y_3730_;
goto v___jp_3724_;
}
else
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
lean_inc_ref(v___y_3730_);
v___x_3737_ = l_Lean_Exception_toMessageData(v___y_3730_);
v___x_3738_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3734_, v___x_3737_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_dec_ref_known(v___x_3738_, 1);
v___y_3725_ = v___y_3731_;
v___y_3726_ = v___y_3732_;
v_a_3727_ = v___y_3730_;
goto v___jp_3724_;
}
else
{
lean_object* v_a_3739_; 
lean_dec_ref(v___y_3730_);
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3738_, 1);
v___y_3725_ = v___y_3731_;
v___y_3726_ = v___y_3732_;
v_a_3727_ = v_a_3739_;
goto v___jp_3724_;
}
}
}
else
{
v___y_3725_ = v___y_3731_;
v___y_3726_ = v___y_3732_;
v_a_3727_ = v___y_3730_;
goto v___jp_3724_;
}
}
v___jp_3740_:
{
uint8_t v___x_3744_; 
v___x_3744_ = l_Lean_Exception_isInterrupt(v_a_3743_);
if (v___x_3744_ == 0)
{
uint8_t v___x_3745_; 
lean_inc_ref(v_a_3743_);
v___x_3745_ = l_Lean_Exception_isRuntime(v_a_3743_);
v___y_3730_ = v_a_3743_;
v___y_3731_ = v___y_3741_;
v___y_3732_ = v___y_3742_;
v___y_3733_ = v___x_3745_;
goto v___jp_3729_;
}
else
{
v___y_3730_ = v_a_3743_;
v___y_3731_ = v___y_3741_;
v___y_3732_ = v___y_3742_;
v___y_3733_ = v___x_3744_;
goto v___jp_3729_;
}
}
v___jp_3746_:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3749_);
v___y_3710_ = v___y_3747_;
v___y_3711_ = v___y_3748_;
v_a_3712_ = v___x_3750_;
goto v___jp_3709_;
}
v___jp_3751_:
{
lean_object* v___x_3755_; double v___x_3756_; double v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3755_ = lean_io_get_num_heartbeats();
v___x_3756_ = lean_float_of_nat(v___y_3752_);
v___x_3757_ = lean_float_of_nat(v___x_3755_);
v___x_3758_ = lean_box_float(v___x_3756_);
v___x_3759_ = lean_box_float(v___x_3757_);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3758_);
lean_ctor_set(v___x_3760_, 1, v___x_3759_);
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3754_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3762_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3705_, v_hasTrace_3670_, v___x_3706_, v_options_3669_, v___x_3708_, v___y_3753_, v___f_3673_, v___x_3761_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
return v___x_3762_;
}
v___jp_3763_:
{
lean_object* v___x_3767_; 
v___x_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3767_, 0, v_a_3766_);
v___y_3752_ = v___y_3764_;
v___y_3753_ = v___y_3765_;
v_a_3754_ = v___x_3767_;
goto v___jp_3751_;
}
v___jp_3768_:
{
if (v___y_3772_ == 0)
{
lean_object* v___x_3773_; lean_object* v___x_3774_; uint8_t v___x_3775_; 
v___x_3773_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3774_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3775_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3672_, v_options_3669_, v___x_3774_);
if (v___x_3775_ == 0)
{
v___y_3764_ = v___y_3769_;
v___y_3765_ = v___y_3770_;
v_a_3766_ = v___y_3771_;
goto v___jp_3763_;
}
else
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_inc_ref(v___y_3771_);
v___x_3776_ = l_Lean_Exception_toMessageData(v___y_3771_);
v___x_3777_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3773_, v___x_3776_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_dec_ref_known(v___x_3777_, 1);
v___y_3764_ = v___y_3769_;
v___y_3765_ = v___y_3770_;
v_a_3766_ = v___y_3771_;
goto v___jp_3763_;
}
else
{
lean_object* v_a_3778_; 
lean_dec_ref(v___y_3771_);
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc(v_a_3778_);
lean_dec_ref_known(v___x_3777_, 1);
v___y_3764_ = v___y_3769_;
v___y_3765_ = v___y_3770_;
v_a_3766_ = v_a_3778_;
goto v___jp_3763_;
}
}
}
else
{
v___y_3764_ = v___y_3769_;
v___y_3765_ = v___y_3770_;
v_a_3766_ = v___y_3771_;
goto v___jp_3763_;
}
}
v___jp_3779_:
{
uint8_t v___x_3783_; 
v___x_3783_ = l_Lean_Exception_isInterrupt(v_a_3782_);
if (v___x_3783_ == 0)
{
uint8_t v___x_3784_; 
lean_inc_ref(v_a_3782_);
v___x_3784_ = l_Lean_Exception_isRuntime(v_a_3782_);
v___y_3769_ = v___y_3780_;
v___y_3770_ = v___y_3781_;
v___y_3771_ = v_a_3782_;
v___y_3772_ = v___x_3784_;
goto v___jp_3768_;
}
else
{
v___y_3769_ = v___y_3780_;
v___y_3770_ = v___y_3781_;
v___y_3771_ = v_a_3782_;
v___y_3772_ = v___x_3783_;
goto v___jp_3768_;
}
}
v___jp_3785_:
{
lean_object* v___x_3789_; 
v___x_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3789_, 0, v_a_3788_);
v___y_3752_ = v___y_3786_;
v___y_3753_ = v___y_3787_;
v_a_3754_ = v___x_3789_;
goto v___jp_3751_;
}
v___jp_3790_:
{
lean_object* v___x_3791_; lean_object* v_a_3792_; lean_object* v___x_3793_; uint8_t v___x_3794_; 
v___x_3791_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3667_);
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref(v___x_3791_);
v___x_3793_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3794_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3669_, v___x_3793_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; lean_object* v___x_3796_; 
v___x_3795_ = lean_io_mono_nanos_now();
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
lean_inc(v_a_3665_);
lean_inc_ref(v_a_3664_);
v___x_3796_ = lean_apply_5(v_k_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, lean_box(0));
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; uint8_t v___x_3800_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3799_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3800_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3672_, v_options_3669_, v___x_3799_);
if (v___x_3800_ == 0)
{
v___y_3747_ = v_a_3792_;
v___y_3748_ = v___x_3795_;
v_a_3749_ = v_a_3797_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
lean_inc(v_a_3797_);
v___x_3801_ = l_Lean_MessageData_ofExpr(v_a_3797_);
v___x_3802_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3798_, v___x_3801_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_dec_ref_known(v___x_3802_, 1);
v___y_3747_ = v_a_3792_;
v___y_3748_ = v___x_3795_;
v_a_3749_ = v_a_3797_;
goto v___jp_3746_;
}
else
{
lean_object* v_a_3803_; 
lean_dec(v_a_3797_);
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
v___y_3741_ = v_a_3792_;
v___y_3742_ = v___x_3795_;
v_a_3743_ = v_a_3803_;
goto v___jp_3740_;
}
}
}
else
{
lean_object* v_a_3804_; 
v_a_3804_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3804_);
lean_dec_ref_known(v___x_3796_, 1);
v___y_3741_ = v_a_3792_;
v___y_3742_ = v___x_3795_;
v_a_3743_ = v_a_3804_;
goto v___jp_3740_;
}
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3805_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3667_);
lean_inc_ref(v_a_3666_);
lean_inc(v_a_3665_);
lean_inc_ref(v_a_3664_);
v___x_3806_ = lean_apply_5(v_k_3663_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_, lean_box(0));
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3809_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3810_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3672_, v_options_3669_, v___x_3809_);
if (v___x_3810_ == 0)
{
v___y_3786_ = v___x_3805_;
v___y_3787_ = v_a_3792_;
v_a_3788_ = v_a_3807_;
goto v___jp_3785_;
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_inc(v_a_3807_);
v___x_3811_ = l_Lean_MessageData_ofExpr(v_a_3807_);
v___x_3812_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3808_, v___x_3811_, v_a_3664_, v_a_3665_, v_a_3666_, v_a_3667_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_dec_ref_known(v___x_3812_, 1);
v___y_3786_ = v___x_3805_;
v___y_3787_ = v_a_3792_;
v_a_3788_ = v_a_3807_;
goto v___jp_3785_;
}
else
{
lean_object* v_a_3813_; 
lean_dec(v_a_3807_);
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v___y_3780_ = v___x_3805_;
v___y_3781_ = v_a_3792_;
v_a_3782_ = v_a_3813_;
goto v___jp_3779_;
}
}
}
else
{
lean_object* v_a_3814_; 
v_a_3814_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3806_, 1);
v___y_3780_ = v___x_3805_;
v___y_3781_ = v_a_3792_;
v_a_3782_ = v_a_3814_;
goto v___jp_3779_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3841_, lean_object* v_xs_3842_, lean_object* v_k_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_){
_start:
{
lean_object* v_res_3849_; 
v_res_3849_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3841_, v_xs_3842_, v_k_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
lean_dec(v_a_3847_);
lean_dec_ref(v_a_3846_);
lean_dec(v_a_3845_);
lean_dec_ref(v_a_3844_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3850_, lean_object* v_xs_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_){
_start:
{
lean_object* v___x_3857_; 
lean_inc(v_a_3855_);
lean_inc_ref(v_a_3854_);
lean_inc(v_a_3853_);
lean_inc_ref(v_a_3852_);
lean_inc_ref(v_f_3850_);
v___x_3857_ = lean_infer_type(v_f_3850_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
if (lean_obj_tag(v___x_3857_) == 0)
{
lean_object* v_a_3858_; lean_object* v___x_3859_; uint8_t v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; 
v_a_3858_ = lean_ctor_get(v___x_3857_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3857_, 1);
lean_inc_ref(v_xs_3851_);
lean_inc_ref(v_f_3850_);
v___x_3859_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3859_, 0, v_f_3850_);
lean_closure_set(v___x_3859_, 1, v_a_3858_);
lean_closure_set(v___x_3859_, 2, v_xs_3851_);
v___x_3860_ = 0;
v___x_3861_ = lean_box(v___x_3860_);
v___x_3862_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3862_, 0, lean_box(0));
lean_closure_set(v___x_3862_, 1, v___x_3859_);
lean_closure_set(v___x_3862_, 2, v___x_3861_);
v___x_3863_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3850_, v_xs_3851_, v___x_3862_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
return v___x_3863_;
}
else
{
lean_dec_ref(v_xs_3851_);
lean_dec_ref(v_f_3850_);
return v___x_3857_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3864_, lean_object* v_xs_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_){
_start:
{
lean_object* v_res_3871_; 
v_res_3871_ = l_Lean_Meta_mkAppM_x27(v_f_3864_, v_xs_3865_, v_a_3866_, v_a_3867_, v_a_3868_, v_a_3869_);
lean_dec(v_a_3869_);
lean_dec_ref(v_a_3868_);
lean_dec(v_a_3867_);
lean_dec_ref(v_a_3866_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3872_, size_t v_i_3873_, size_t v_stop_3874_, lean_object* v_b_3875_){
_start:
{
lean_object* v___y_3877_; uint8_t v___x_3881_; 
v___x_3881_ = lean_usize_dec_eq(v_i_3873_, v_stop_3874_);
if (v___x_3881_ == 0)
{
lean_object* v___x_3882_; 
v___x_3882_ = lean_array_uget_borrowed(v_as_3872_, v_i_3873_);
if (lean_obj_tag(v___x_3882_) == 0)
{
v___y_3877_ = v_b_3875_;
goto v___jp_3876_;
}
else
{
lean_object* v_val_3883_; lean_object* v___x_3884_; 
v_val_3883_ = lean_ctor_get(v___x_3882_, 0);
lean_inc(v_val_3883_);
v___x_3884_ = lean_array_push(v_b_3875_, v_val_3883_);
v___y_3877_ = v___x_3884_;
goto v___jp_3876_;
}
}
else
{
return v_b_3875_;
}
v___jp_3876_:
{
size_t v___x_3878_; size_t v___x_3879_; 
v___x_3878_ = ((size_t)1ULL);
v___x_3879_ = lean_usize_add(v_i_3873_, v___x_3878_);
v_i_3873_ = v___x_3879_;
v_b_3875_ = v___y_3877_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3885_, lean_object* v_i_3886_, lean_object* v_stop_3887_, lean_object* v_b_3888_){
_start:
{
size_t v_i_boxed_3889_; size_t v_stop_boxed_3890_; lean_object* v_res_3891_; 
v_i_boxed_3889_ = lean_unbox_usize(v_i_3886_);
lean_dec(v_i_3886_);
v_stop_boxed_3890_ = lean_unbox_usize(v_stop_3887_);
lean_dec(v_stop_3887_);
v_res_3891_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3885_, v_i_boxed_3889_, v_stop_boxed_3890_, v_b_3888_);
lean_dec_ref(v_as_3885_);
return v_res_3891_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; 
v___x_3898_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3899_ = l_Lean_MessageData_ofFormat(v___x_3898_);
return v___x_3899_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = lean_box(1);
v___x_3901_ = l_Lean_MessageData_ofFormat(v___x_3900_);
return v___x_3901_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3906_ = l_Lean_MessageData_ofFormat(v___x_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3907_, lean_object* v_xs_3908_, lean_object* v_x_3909_, lean_object* v_x_3910_, lean_object* v_x_3911_, lean_object* v_x_3912_, lean_object* v_x_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_){
_start:
{
if (lean_obj_tag(v_x_3913_) == 7)
{
lean_object* v_binderName_3919_; lean_object* v_binderType_3920_; lean_object* v_body_3921_; uint8_t v_binderInfo_3922_; lean_object* v___x_3923_; uint8_t v___x_3924_; 
v_binderName_3919_ = lean_ctor_get(v_x_3913_, 0);
lean_inc(v_binderName_3919_);
v_binderType_3920_ = lean_ctor_get(v_x_3913_, 1);
lean_inc_ref(v_binderType_3920_);
v_body_3921_ = lean_ctor_get(v_x_3913_, 2);
lean_inc_ref(v_body_3921_);
v_binderInfo_3922_ = lean_ctor_get_uint8(v_x_3913_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3913_, 3);
v___x_3923_ = lean_array_get_size(v_xs_3908_);
v___x_3924_ = lean_nat_dec_lt(v_x_3909_, v___x_3923_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_dec_ref(v_body_3921_);
lean_dec_ref(v_binderType_3920_);
lean_dec(v_binderName_3919_);
lean_dec(v_x_3911_);
lean_dec(v_x_3909_);
v___x_3925_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3926_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3925_, v_f_3907_, v_x_3910_, v_x_3912_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
lean_dec_ref(v_x_3912_);
lean_dec_ref(v_x_3910_);
return v___x_3926_;
}
else
{
lean_object* v___x_3927_; lean_object* v_d_3928_; lean_object* v___x_3929_; 
v___x_3927_ = lean_array_get_size(v_x_3910_);
v_d_3928_ = lean_expr_instantiate_rev_range(v_binderType_3920_, v_x_3911_, v___x_3927_, v_x_3910_);
lean_dec_ref(v_binderType_3920_);
v___x_3929_ = lean_array_fget_borrowed(v_xs_3908_, v_x_3909_);
if (lean_obj_tag(v___x_3929_) == 0)
{
if (v_binderInfo_3922_ == 3)
{
lean_object* v___x_3930_; uint8_t v___x_3931_; lean_object* v___x_3932_; 
v___x_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3930_, 0, v_d_3928_);
v___x_3931_ = 1;
v___x_3932_ = l_Lean_Meta_mkFreshExprMVar(v___x_3930_, v___x_3931_, v_binderName_3919_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc_n(v_a_3933_, 2);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3934_ = lean_unsigned_to_nat(1u);
v___x_3935_ = lean_nat_add(v_x_3909_, v___x_3934_);
lean_dec(v_x_3909_);
v___x_3936_ = lean_array_push(v_x_3910_, v_a_3933_);
v___x_3937_ = l_Lean_Expr_mvarId_x21(v_a_3933_);
lean_dec(v_a_3933_);
v___x_3938_ = lean_array_push(v_x_3912_, v___x_3937_);
v_x_3909_ = v___x_3935_;
v_x_3910_ = v___x_3936_;
v_x_3912_ = v___x_3938_;
v_x_3913_ = v_body_3921_;
goto _start;
}
else
{
lean_dec_ref(v_body_3921_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_x_3910_);
lean_dec(v_x_3909_);
lean_dec_ref(v_f_3907_);
return v___x_3932_;
}
}
else
{
lean_object* v___x_3940_; uint8_t v___x_3941_; lean_object* v___x_3942_; 
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v_d_3928_);
v___x_3941_ = 0;
v___x_3942_ = l_Lean_Meta_mkFreshExprMVar(v___x_3940_, v___x_3941_, v_binderName_3919_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
lean_inc(v_a_3943_);
lean_dec_ref_known(v___x_3942_, 1);
v___x_3944_ = lean_unsigned_to_nat(1u);
v___x_3945_ = lean_nat_add(v_x_3909_, v___x_3944_);
lean_dec(v_x_3909_);
v___x_3946_ = lean_array_push(v_x_3910_, v_a_3943_);
v_x_3909_ = v___x_3945_;
v_x_3910_ = v___x_3946_;
v_x_3913_ = v_body_3921_;
goto _start;
}
else
{
lean_dec_ref(v_body_3921_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_x_3910_);
lean_dec(v_x_3909_);
lean_dec_ref(v_f_3907_);
return v___x_3942_;
}
}
}
else
{
lean_object* v_val_3948_; lean_object* v___x_3949_; 
lean_dec(v_binderName_3919_);
v_val_3948_ = lean_ctor_get(v___x_3929_, 0);
lean_inc(v_a_3917_);
lean_inc_ref(v_a_3916_);
lean_inc(v_a_3915_);
lean_inc_ref(v_a_3914_);
lean_inc(v_val_3948_);
v___x_3949_ = lean_infer_type(v_val_3948_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v___x_3951_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
lean_inc(v_a_3950_);
lean_dec_ref_known(v___x_3949_, 1);
v___x_3951_ = l_Lean_Meta_isExprDefEq(v_d_3928_, v_a_3950_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; uint8_t v___x_3953_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref_known(v___x_3951_, 1);
v___x_3953_ = lean_unbox(v_a_3952_);
lean_dec(v_a_3952_);
if (v___x_3953_ == 0)
{
lean_object* v___x_3954_; lean_object* v___x_3955_; 
lean_dec_ref(v_body_3921_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec(v_x_3909_);
v___x_3954_ = l_Lean_mkAppN(v_f_3907_, v_x_3910_);
lean_dec_ref(v_x_3910_);
lean_inc(v_val_3948_);
v___x_3955_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3954_, v_val_3948_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = lean_unsigned_to_nat(1u);
v___x_3957_ = lean_nat_add(v_x_3909_, v___x_3956_);
lean_dec(v_x_3909_);
lean_inc(v_val_3948_);
v___x_3958_ = lean_array_push(v_x_3910_, v_val_3948_);
v_x_3909_ = v___x_3957_;
v_x_3910_ = v___x_3958_;
v_x_3913_ = v_body_3921_;
goto _start;
}
}
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_dec_ref(v_body_3921_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_x_3910_);
lean_dec(v_x_3909_);
lean_dec_ref(v_f_3907_);
v_a_3960_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3951_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3951_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
lean_dec_ref(v_d_3928_);
lean_dec_ref(v_body_3921_);
lean_dec_ref(v_x_3912_);
lean_dec(v_x_3911_);
lean_dec_ref(v_x_3910_);
lean_dec(v_x_3909_);
lean_dec_ref(v_f_3907_);
return v___x_3949_;
}
}
}
}
else
{
lean_object* v___x_3968_; lean_object* v_type_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_array_get_size(v_x_3910_);
v_type_3969_ = lean_expr_instantiate_rev_range(v_x_3913_, v_x_3911_, v___x_3968_, v_x_3910_);
lean_dec(v_x_3911_);
lean_dec_ref(v_x_3913_);
v___x_3970_ = l_Lean_Meta_whnfD(v_type_3969_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v_a_3971_; uint8_t v___x_3972_; 
v_a_3971_ = lean_ctor_get(v___x_3970_, 0);
lean_inc(v_a_3971_);
lean_dec_ref_known(v___x_3970_, 1);
v___x_3972_ = l_Lean_Expr_isForall(v_a_3971_);
if (v___x_3972_ == 0)
{
lean_object* v___x_3973_; uint8_t v___x_3974_; 
lean_dec(v_a_3971_);
v___x_3973_ = lean_array_get_size(v_xs_3908_);
v___x_3974_ = lean_nat_dec_eq(v_x_3909_, v___x_3973_);
lean_dec(v_x_3909_);
if (v___x_3974_ == 0)
{
lean_object* v___x_3975_; lean_object* v___y_3977_; lean_object* v___x_3990_; uint8_t v___x_3991_; 
lean_dec_ref(v_x_3912_);
lean_dec_ref(v_x_3910_);
v___x_3975_ = lean_unsigned_to_nat(0u);
v___x_3990_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3991_ = lean_nat_dec_lt(v___x_3975_, v___x_3973_);
if (v___x_3991_ == 0)
{
v___y_3977_ = v___x_3990_;
goto v___jp_3976_;
}
else
{
uint8_t v___x_3992_; 
v___x_3992_ = lean_nat_dec_le(v___x_3973_, v___x_3973_);
if (v___x_3992_ == 0)
{
if (v___x_3991_ == 0)
{
v___y_3977_ = v___x_3990_;
goto v___jp_3976_;
}
else
{
size_t v___x_3993_; size_t v___x_3994_; lean_object* v___x_3995_; 
v___x_3993_ = ((size_t)0ULL);
v___x_3994_ = lean_usize_of_nat(v___x_3973_);
v___x_3995_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3908_, v___x_3993_, v___x_3994_, v___x_3990_);
v___y_3977_ = v___x_3995_;
goto v___jp_3976_;
}
}
else
{
size_t v___x_3996_; size_t v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = ((size_t)0ULL);
v___x_3997_ = lean_usize_of_nat(v___x_3973_);
v___x_3998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3908_, v___x_3996_, v___x_3997_, v___x_3990_);
v___y_3977_ = v___x_3998_;
goto v___jp_3976_;
}
}
v___jp_3976_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3978_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3979_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3980_ = l_Lean_indentExpr(v_f_3907_);
v___x_3981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3983_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3981_);
lean_ctor_set(v___x_3983_, 1, v___x_3982_);
v___x_3984_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3985_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3983_);
lean_ctor_set(v___x_3985_, 1, v___x_3984_);
v___x_3986_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3987_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3977_, v___x_3975_, v___x_3986_);
lean_dec_ref(v___y_3977_);
v___x_3988_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3988_, 0, v___x_3985_);
lean_ctor_set(v___x_3988_, 1, v___x_3987_);
v___x_3989_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3978_, v___x_3988_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
return v___x_3989_;
}
}
else
{
lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3999_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_4000_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3999_, v_f_3907_, v_x_3910_, v_x_3912_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_);
lean_dec_ref(v_x_3912_);
lean_dec_ref(v_x_3910_);
return v___x_4000_;
}
}
else
{
v_x_3911_ = v___x_3968_;
v_x_3913_ = v_a_3971_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3912_);
lean_dec_ref(v_x_3910_);
lean_dec(v_x_3909_);
lean_dec_ref(v_f_3907_);
return v___x_3970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_4002_, lean_object* v_xs_4003_, lean_object* v_x_4004_, lean_object* v_x_4005_, lean_object* v_x_4006_, lean_object* v_x_4007_, lean_object* v_x_4008_, lean_object* v_a_4009_, lean_object* v_a_4010_, lean_object* v_a_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_4002_, v_xs_4003_, v_x_4004_, v_x_4005_, v_x_4006_, v_x_4007_, v_x_4008_, v_a_4009_, v_a_4010_, v_a_4011_, v_a_4012_);
lean_dec(v_a_4012_);
lean_dec_ref(v_a_4011_);
lean_dec(v_a_4010_);
lean_dec_ref(v_a_4009_);
lean_dec_ref(v_xs_4003_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_4015_, lean_object* v_xs_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_4015_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v_fst_4024_; lean_object* v_snd_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v___x_4022_, 1);
v_fst_4024_ = lean_ctor_get(v_a_4023_, 0);
lean_inc(v_fst_4024_);
v_snd_4025_ = lean_ctor_get(v_a_4023_, 1);
lean_inc(v_snd_4025_);
lean_dec(v_a_4023_);
v___x_4026_ = lean_unsigned_to_nat(0u);
v___x_4027_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4028_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4024_, v_xs_4016_, v___x_4026_, v___x_4027_, v___x_4026_, v___x_4027_, v_snd_4025_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
return v___x_4028_;
}
else
{
lean_object* v_a_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4036_; 
v_a_4029_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4036_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4036_ == 0)
{
v___x_4031_ = v___x_4022_;
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_a_4029_);
lean_dec(v___x_4022_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4036_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4034_; 
if (v_isShared_4032_ == 0)
{
v___x_4034_ = v___x_4031_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4029_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4037_, lean_object* v_xs_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4037_, v_xs_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec_ref(v_xs_4038_);
return v_res_4044_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4049_ = l_Lean_MessageData_ofFormat(v___x_4048_);
return v___x_4049_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4050_, lean_object* v_a_4051_){
_start:
{
if (lean_obj_tag(v_a_4050_) == 0)
{
lean_object* v___x_4052_; 
v___x_4052_ = l_List_reverse___redArg(v_a_4051_);
return v___x_4052_;
}
else
{
lean_object* v_head_4053_; lean_object* v_tail_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4067_; 
v_head_4053_ = lean_ctor_get(v_a_4050_, 0);
v_tail_4054_ = lean_ctor_get(v_a_4050_, 1);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_a_4050_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4056_ = v_a_4050_;
v_isShared_4057_ = v_isSharedCheck_4067_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_tail_4054_);
lean_inc(v_head_4053_);
lean_dec(v_a_4050_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4067_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___y_4059_; 
if (lean_obj_tag(v_head_4053_) == 0)
{
lean_object* v___x_4064_; 
v___x_4064_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4059_ = v___x_4064_;
goto v___jp_4058_;
}
else
{
lean_object* v_val_4065_; lean_object* v___x_4066_; 
v_val_4065_ = lean_ctor_get(v_head_4053_, 0);
lean_inc(v_val_4065_);
lean_dec_ref_known(v_head_4053_, 1);
v___x_4066_ = l_Lean_MessageData_ofExpr(v_val_4065_);
v___y_4059_ = v___x_4066_;
goto v___jp_4058_;
}
v___jp_4058_:
{
lean_object* v___x_4061_; 
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 1, v_a_4051_);
lean_ctor_set(v___x_4056_, 0, v___y_4059_);
v___x_4061_ = v___x_4056_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___y_4059_);
lean_ctor_set(v_reuseFailAlloc_4063_, 1, v_a_4051_);
v___x_4061_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
v_a_4050_ = v_tail_4054_;
v_a_4051_ = v___x_4061_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4068_, lean_object* v_xs_4069_, lean_object* v_x_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4076_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4077_ = l_Lean_MessageData_ofName(v_f_4068_);
v___x_4078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4076_);
lean_ctor_set(v___x_4078_, 1, v___x_4077_);
v___x_4079_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4080_, 0, v___x_4078_);
lean_ctor_set(v___x_4080_, 1, v___x_4079_);
v___x_4081_ = lean_array_to_list(v_xs_4069_);
v___x_4082_ = lean_box(0);
v___x_4083_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4081_, v___x_4082_);
v___x_4084_ = l_Lean_MessageData_ofList(v___x_4083_);
v___x_4085_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4085_, 0, v___x_4080_);
lean_ctor_set(v___x_4085_, 1, v___x_4084_);
v___x_4086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4087_, lean_object* v_xs_4088_, lean_object* v_x_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4087_, v_xs_4088_, v_x_4089_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v___y_4091_);
lean_dec_ref(v___y_4090_);
lean_dec_ref(v_x_4089_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4096_, lean_object* v_xs_4097_, lean_object* v_k_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v_options_4104_; uint8_t v_hasTrace_4105_; 
v_options_4104_ = lean_ctor_get(v_a_4101_, 2);
v_hasTrace_4105_ = lean_ctor_get_uint8(v_options_4104_, sizeof(void*)*1);
if (v_hasTrace_4105_ == 0)
{
lean_object* v___x_4106_; 
lean_dec_ref(v_xs_4097_);
lean_dec(v_f_4096_);
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
lean_inc(v_a_4100_);
lean_inc_ref(v_a_4099_);
v___x_4106_ = lean_apply_5(v_k_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
return v___x_4106_;
}
else
{
lean_object* v_inheritedTraceOptions_4107_; lean_object* v___f_4108_; lean_object* v___y_4110_; lean_object* v___y_4111_; uint8_t v___y_4112_; lean_object* v___y_4136_; lean_object* v_a_4137_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; uint8_t v___x_4143_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v_a_4147_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v_a_4162_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; uint8_t v___y_4168_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v_a_4178_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v_a_4184_; lean_object* v___y_4187_; lean_object* v___y_4188_; lean_object* v_a_4189_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v_a_4201_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; uint8_t v___y_4207_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v_a_4217_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v_a_4223_; 
v_inheritedTraceOptions_4107_ = lean_ctor_get(v_a_4101_, 13);
v___f_4108_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4108_, 0, v_f_4096_);
lean_closure_set(v___f_4108_, 1, v_xs_4097_);
v___x_4140_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4141_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4142_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4143_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4104_, v___x_4142_);
if (v___x_4143_ == 0)
{
lean_object* v___x_4250_; uint8_t v___x_4251_; 
v___x_4250_ = l_Lean_trace_profiler;
v___x_4251_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4104_, v___x_4250_);
if (v___x_4251_ == 0)
{
lean_object* v___x_4252_; 
lean_dec_ref(v___f_4108_);
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
lean_inc(v_a_4100_);
lean_inc_ref(v_a_4099_);
v___x_4252_ = lean_apply_5(v_k_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; uint8_t v___x_4256_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
v___x_4254_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4255_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4104_, v___x_4255_);
if (v___x_4256_ == 0)
{
lean_dec(v_a_4253_);
return v___x_4252_;
}
else
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
lean_dec_ref_known(v___x_4252_, 1);
lean_inc(v_a_4253_);
v___x_4257_ = l_Lean_MessageData_ofExpr(v_a_4253_);
v___x_4258_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4254_, v___x_4257_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4258_) == 0)
{
lean_object* v___x_4260_; uint8_t v_isShared_4261_; uint8_t v_isSharedCheck_4265_; 
v_isSharedCheck_4265_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4265_ == 0)
{
lean_object* v_unused_4266_; 
v_unused_4266_ = lean_ctor_get(v___x_4258_, 0);
lean_dec(v_unused_4266_);
v___x_4260_ = v___x_4258_;
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
else
{
lean_dec(v___x_4258_);
v___x_4260_ = lean_box(0);
v_isShared_4261_ = v_isSharedCheck_4265_;
goto v_resetjp_4259_;
}
v_resetjp_4259_:
{
lean_object* v___x_4263_; 
if (v_isShared_4261_ == 0)
{
lean_ctor_set(v___x_4260_, 0, v_a_4253_);
v___x_4263_ = v___x_4260_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v_a_4253_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
else
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4274_; 
lean_dec(v_a_4253_);
v_a_4267_ = lean_ctor_get(v___x_4258_, 0);
v_isSharedCheck_4274_ = !lean_is_exclusive(v___x_4258_);
if (v_isSharedCheck_4274_ == 0)
{
v___x_4269_ = v___x_4258_;
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4258_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4274_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4272_; 
lean_inc(v_a_4267_);
if (v_isShared_4270_ == 0)
{
v___x_4272_ = v___x_4269_;
goto v_reusejp_4271_;
}
else
{
lean_object* v_reuseFailAlloc_4273_; 
v_reuseFailAlloc_4273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4273_, 0, v_a_4267_);
v___x_4272_ = v_reuseFailAlloc_4273_;
goto v_reusejp_4271_;
}
v_reusejp_4271_:
{
v___y_4136_ = v___x_4272_;
v_a_4137_ = v_a_4267_;
goto v___jp_4135_;
}
}
}
}
}
else
{
lean_object* v_a_4275_; 
v_a_4275_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4275_);
v___y_4136_ = v___x_4252_;
v_a_4137_ = v_a_4275_;
goto v___jp_4135_;
}
}
else
{
goto v___jp_4225_;
}
}
else
{
goto v___jp_4225_;
}
v___jp_4109_:
{
if (v___y_4112_ == 0)
{
lean_object* v___x_4113_; lean_object* v___x_4114_; uint8_t v___x_4115_; 
lean_dec_ref(v___y_4110_);
v___x_4113_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4114_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4115_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4104_, v___x_4114_);
if (v___x_4115_ == 0)
{
lean_object* v___x_4116_; 
v___x_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4116_, 0, v___y_4111_);
return v___x_4116_;
}
else
{
lean_object* v___x_4117_; lean_object* v___x_4118_; 
lean_inc_ref(v___y_4111_);
v___x_4117_ = l_Lean_Exception_toMessageData(v___y_4111_);
v___x_4118_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4113_, v___x_4117_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4125_ == 0)
{
lean_object* v_unused_4126_; 
v_unused_4126_ = lean_ctor_get(v___x_4118_, 0);
lean_dec(v_unused_4126_);
v___x_4120_ = v___x_4118_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_dec(v___x_4118_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
lean_ctor_set_tag(v___x_4120_, 1);
lean_ctor_set(v___x_4120_, 0, v___y_4111_);
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___y_4111_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_dec_ref(v___y_4111_);
v_a_4127_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4118_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4118_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4111_);
return v___y_4110_;
}
}
v___jp_4135_:
{
uint8_t v___x_4138_; 
v___x_4138_ = l_Lean_Exception_isInterrupt(v_a_4137_);
if (v___x_4138_ == 0)
{
uint8_t v___x_4139_; 
lean_inc_ref(v_a_4137_);
v___x_4139_ = l_Lean_Exception_isRuntime(v_a_4137_);
v___y_4110_ = v___y_4136_;
v___y_4111_ = v_a_4137_;
v___y_4112_ = v___x_4139_;
goto v___jp_4109_;
}
else
{
v___y_4110_ = v___y_4136_;
v___y_4111_ = v_a_4137_;
v___y_4112_ = v___x_4138_;
goto v___jp_4109_;
}
}
v___jp_4144_:
{
lean_object* v___x_4148_; double v___x_4149_; double v___x_4150_; double v___x_4151_; double v___x_4152_; double v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v___x_4148_ = lean_io_mono_nanos_now();
v___x_4149_ = lean_float_of_nat(v___y_4146_);
v___x_4150_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4151_ = lean_float_div(v___x_4149_, v___x_4150_);
v___x_4152_ = lean_float_of_nat(v___x_4148_);
v___x_4153_ = lean_float_div(v___x_4152_, v___x_4150_);
v___x_4154_ = lean_box_float(v___x_4151_);
v___x_4155_ = lean_box_float(v___x_4153_);
v___x_4156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4157_, 0, v_a_4147_);
lean_ctor_set(v___x_4157_, 1, v___x_4156_);
v___x_4158_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4140_, v_hasTrace_4105_, v___x_4141_, v_options_4104_, v___x_4143_, v___y_4145_, v___f_4108_, v___x_4157_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4158_;
}
v___jp_4159_:
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_a_4162_);
v___y_4145_ = v___y_4160_;
v___y_4146_ = v___y_4161_;
v_a_4147_ = v___x_4163_;
goto v___jp_4144_;
}
v___jp_4164_:
{
if (v___y_4168_ == 0)
{
lean_object* v___x_4169_; lean_object* v___x_4170_; uint8_t v___x_4171_; 
v___x_4169_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4170_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4171_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4104_, v___x_4170_);
if (v___x_4171_ == 0)
{
v___y_4160_ = v___y_4166_;
v___y_4161_ = v___y_4167_;
v_a_4162_ = v___y_4165_;
goto v___jp_4159_;
}
else
{
lean_object* v___x_4172_; lean_object* v___x_4173_; 
lean_inc_ref(v___y_4165_);
v___x_4172_ = l_Lean_Exception_toMessageData(v___y_4165_);
v___x_4173_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4169_, v___x_4172_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_dec_ref_known(v___x_4173_, 1);
v___y_4160_ = v___y_4166_;
v___y_4161_ = v___y_4167_;
v_a_4162_ = v___y_4165_;
goto v___jp_4159_;
}
else
{
lean_object* v_a_4174_; 
lean_dec_ref(v___y_4165_);
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc(v_a_4174_);
lean_dec_ref_known(v___x_4173_, 1);
v___y_4160_ = v___y_4166_;
v___y_4161_ = v___y_4167_;
v_a_4162_ = v_a_4174_;
goto v___jp_4159_;
}
}
}
else
{
v___y_4160_ = v___y_4166_;
v___y_4161_ = v___y_4167_;
v_a_4162_ = v___y_4165_;
goto v___jp_4159_;
}
}
v___jp_4175_:
{
uint8_t v___x_4179_; 
v___x_4179_ = l_Lean_Exception_isInterrupt(v_a_4178_);
if (v___x_4179_ == 0)
{
uint8_t v___x_4180_; 
lean_inc_ref(v_a_4178_);
v___x_4180_ = l_Lean_Exception_isRuntime(v_a_4178_);
v___y_4165_ = v_a_4178_;
v___y_4166_ = v___y_4176_;
v___y_4167_ = v___y_4177_;
v___y_4168_ = v___x_4180_;
goto v___jp_4164_;
}
else
{
v___y_4165_ = v_a_4178_;
v___y_4166_ = v___y_4176_;
v___y_4167_ = v___y_4177_;
v___y_4168_ = v___x_4179_;
goto v___jp_4164_;
}
}
v___jp_4181_:
{
lean_object* v___x_4185_; 
v___x_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4185_, 0, v_a_4184_);
v___y_4145_ = v___y_4182_;
v___y_4146_ = v___y_4183_;
v_a_4147_ = v___x_4185_;
goto v___jp_4144_;
}
v___jp_4186_:
{
lean_object* v___x_4190_; double v___x_4191_; double v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4190_ = lean_io_get_num_heartbeats();
v___x_4191_ = lean_float_of_nat(v___y_4188_);
v___x_4192_ = lean_float_of_nat(v___x_4190_);
v___x_4193_ = lean_box_float(v___x_4191_);
v___x_4194_ = lean_box_float(v___x_4192_);
v___x_4195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4193_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v_a_4189_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4140_, v_hasTrace_4105_, v___x_4141_, v_options_4104_, v___x_4143_, v___y_4187_, v___f_4108_, v___x_4196_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4197_;
}
v___jp_4198_:
{
lean_object* v___x_4202_; 
v___x_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4202_, 0, v_a_4201_);
v___y_4187_ = v___y_4199_;
v___y_4188_ = v___y_4200_;
v_a_4189_ = v___x_4202_;
goto v___jp_4186_;
}
v___jp_4203_:
{
if (v___y_4207_ == 0)
{
lean_object* v___x_4208_; lean_object* v___x_4209_; uint8_t v___x_4210_; 
v___x_4208_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4209_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4210_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4104_, v___x_4209_);
if (v___x_4210_ == 0)
{
v___y_4199_ = v___y_4204_;
v___y_4200_ = v___y_4205_;
v_a_4201_ = v___y_4206_;
goto v___jp_4198_;
}
else
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_inc_ref(v___y_4206_);
v___x_4211_ = l_Lean_Exception_toMessageData(v___y_4206_);
v___x_4212_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4208_, v___x_4211_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4212_) == 0)
{
lean_dec_ref_known(v___x_4212_, 1);
v___y_4199_ = v___y_4204_;
v___y_4200_ = v___y_4205_;
v_a_4201_ = v___y_4206_;
goto v___jp_4198_;
}
else
{
lean_object* v_a_4213_; 
lean_dec_ref(v___y_4206_);
v_a_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc(v_a_4213_);
lean_dec_ref_known(v___x_4212_, 1);
v___y_4199_ = v___y_4204_;
v___y_4200_ = v___y_4205_;
v_a_4201_ = v_a_4213_;
goto v___jp_4198_;
}
}
}
else
{
v___y_4199_ = v___y_4204_;
v___y_4200_ = v___y_4205_;
v_a_4201_ = v___y_4206_;
goto v___jp_4198_;
}
}
v___jp_4214_:
{
uint8_t v___x_4218_; 
v___x_4218_ = l_Lean_Exception_isInterrupt(v_a_4217_);
if (v___x_4218_ == 0)
{
uint8_t v___x_4219_; 
lean_inc_ref(v_a_4217_);
v___x_4219_ = l_Lean_Exception_isRuntime(v_a_4217_);
v___y_4204_ = v___y_4215_;
v___y_4205_ = v___y_4216_;
v___y_4206_ = v_a_4217_;
v___y_4207_ = v___x_4219_;
goto v___jp_4203_;
}
else
{
v___y_4204_ = v___y_4215_;
v___y_4205_ = v___y_4216_;
v___y_4206_ = v_a_4217_;
v___y_4207_ = v___x_4218_;
goto v___jp_4203_;
}
}
v___jp_4220_:
{
lean_object* v___x_4224_; 
v___x_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4224_, 0, v_a_4223_);
v___y_4187_ = v___y_4221_;
v___y_4188_ = v___y_4222_;
v_a_4189_ = v___x_4224_;
goto v___jp_4186_;
}
v___jp_4225_:
{
lean_object* v___x_4226_; lean_object* v_a_4227_; lean_object* v___x_4228_; uint8_t v___x_4229_; 
v___x_4226_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4102_);
v_a_4227_ = lean_ctor_get(v___x_4226_, 0);
lean_inc(v_a_4227_);
lean_dec_ref(v___x_4226_);
v___x_4228_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4229_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4104_, v___x_4228_);
if (v___x_4229_ == 0)
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_io_mono_nanos_now();
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
lean_inc(v_a_4100_);
lean_inc_ref(v_a_4099_);
v___x_4231_ = lean_apply_5(v_k_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4233_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4234_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4104_, v___x_4234_);
if (v___x_4235_ == 0)
{
v___y_4182_ = v_a_4227_;
v___y_4183_ = v___x_4230_;
v_a_4184_ = v_a_4232_;
goto v___jp_4181_;
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_inc(v_a_4232_);
v___x_4236_ = l_Lean_MessageData_ofExpr(v_a_4232_);
v___x_4237_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4233_, v___x_4236_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_dec_ref_known(v___x_4237_, 1);
v___y_4182_ = v_a_4227_;
v___y_4183_ = v___x_4230_;
v_a_4184_ = v_a_4232_;
goto v___jp_4181_;
}
else
{
lean_object* v_a_4238_; 
lean_dec(v_a_4232_);
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v___y_4176_ = v_a_4227_;
v___y_4177_ = v___x_4230_;
v_a_4178_ = v_a_4238_;
goto v___jp_4175_;
}
}
}
else
{
lean_object* v_a_4239_; 
v_a_4239_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4239_);
lean_dec_ref_known(v___x_4231_, 1);
v___y_4176_ = v_a_4227_;
v___y_4177_ = v___x_4230_;
v_a_4178_ = v_a_4239_;
goto v___jp_4175_;
}
}
else
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4102_);
lean_inc_ref(v_a_4101_);
lean_inc(v_a_4100_);
lean_inc_ref(v_a_4099_);
v___x_4241_ = lean_apply_5(v_k_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_, lean_box(0));
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; uint8_t v___x_4245_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4243_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4244_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4245_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4104_, v___x_4244_);
if (v___x_4245_ == 0)
{
v___y_4221_ = v_a_4227_;
v___y_4222_ = v___x_4240_;
v_a_4223_ = v_a_4242_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
lean_inc(v_a_4242_);
v___x_4246_ = l_Lean_MessageData_ofExpr(v_a_4242_);
v___x_4247_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4243_, v___x_4246_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_dec_ref_known(v___x_4247_, 1);
v___y_4221_ = v_a_4227_;
v___y_4222_ = v___x_4240_;
v_a_4223_ = v_a_4242_;
goto v___jp_4220_;
}
else
{
lean_object* v_a_4248_; 
lean_dec(v_a_4242_);
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
v___y_4215_ = v_a_4227_;
v___y_4216_ = v___x_4240_;
v_a_4217_ = v_a_4248_;
goto v___jp_4214_;
}
}
}
else
{
lean_object* v_a_4249_; 
v_a_4249_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4249_);
lean_dec_ref_known(v___x_4241_, 1);
v___y_4215_ = v_a_4227_;
v___y_4216_ = v___x_4240_;
v_a_4217_ = v_a_4249_;
goto v___jp_4214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4276_, lean_object* v_xs_4277_, lean_object* v_k_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_, lean_object* v_a_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4276_, v_xs_4277_, v_k_4278_, v_a_4279_, v_a_4280_, v_a_4281_, v_a_4282_);
lean_dec(v_a_4282_);
lean_dec_ref(v_a_4281_);
lean_dec(v_a_4280_);
lean_dec_ref(v_a_4279_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4285_, lean_object* v_xs_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_){
_start:
{
lean_object* v___f_4292_; uint8_t v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; lean_object* v___x_4296_; 
lean_inc_ref(v_xs_4286_);
lean_inc(v_constName_4285_);
v___f_4292_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4292_, 0, v_constName_4285_);
lean_closure_set(v___f_4292_, 1, v_xs_4286_);
v___x_4293_ = 0;
v___x_4294_ = lean_box(v___x_4293_);
v___x_4295_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4295_, 0, lean_box(0));
lean_closure_set(v___x_4295_, 1, v___f_4292_);
lean_closure_set(v___x_4295_, 2, v___x_4294_);
v___x_4296_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4285_, v_xs_4286_, v___x_4295_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
return v___x_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4297_, lean_object* v_xs_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Meta_mkAppOptM(v_constName_4297_, v_xs_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4305_, lean_object* v_xs_4306_, lean_object* v_x_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4313_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4314_ = l_Lean_MessageData_ofExpr(v_f_4305_);
v___x_4315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4313_);
lean_ctor_set(v___x_4315_, 1, v___x_4314_);
v___x_4316_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4317_, 0, v___x_4315_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
v___x_4318_ = lean_array_to_list(v_xs_4306_);
v___x_4319_ = lean_box(0);
v___x_4320_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4318_, v___x_4319_);
v___x_4321_ = l_Lean_MessageData_ofList(v___x_4320_);
v___x_4322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4322_, 0, v___x_4317_);
lean_ctor_set(v___x_4322_, 1, v___x_4321_);
v___x_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4324_, lean_object* v_xs_4325_, lean_object* v_x_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4324_, v_xs_4325_, v_x_4326_, v___y_4327_, v___y_4328_, v___y_4329_, v___y_4330_);
lean_dec(v___y_4330_);
lean_dec_ref(v___y_4329_);
lean_dec(v___y_4328_);
lean_dec_ref(v___y_4327_);
lean_dec_ref(v_x_4326_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4333_, lean_object* v_xs_4334_, lean_object* v_k_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_){
_start:
{
lean_object* v_options_4341_; uint8_t v_hasTrace_4342_; 
v_options_4341_ = lean_ctor_get(v_a_4338_, 2);
v_hasTrace_4342_ = lean_ctor_get_uint8(v_options_4341_, sizeof(void*)*1);
if (v_hasTrace_4342_ == 0)
{
lean_object* v___x_4343_; 
lean_dec_ref(v_xs_4334_);
lean_dec_ref(v_f_4333_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
lean_inc_ref(v_a_4336_);
v___x_4343_ = lean_apply_5(v_k_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, lean_box(0));
return v___x_4343_;
}
else
{
lean_object* v_inheritedTraceOptions_4344_; lean_object* v___f_4345_; lean_object* v___y_4347_; lean_object* v___y_4348_; uint8_t v___y_4349_; lean_object* v___y_4373_; lean_object* v_a_4374_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; uint8_t v___x_4380_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v_a_4384_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v_a_4399_; lean_object* v___y_4402_; lean_object* v___y_4403_; lean_object* v___y_4404_; uint8_t v___y_4405_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v_a_4415_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v_a_4421_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v_a_4426_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v_a_4438_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; uint8_t v___y_4444_; lean_object* v___y_4452_; lean_object* v___y_4453_; lean_object* v_a_4454_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v_a_4460_; 
v_inheritedTraceOptions_4344_ = lean_ctor_get(v_a_4338_, 13);
v___f_4345_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4345_, 0, v_f_4333_);
lean_closure_set(v___f_4345_, 1, v_xs_4334_);
v___x_4377_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4378_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4379_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4380_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4344_, v_options_4341_, v___x_4379_);
if (v___x_4380_ == 0)
{
lean_object* v___x_4487_; uint8_t v___x_4488_; 
v___x_4487_ = l_Lean_trace_profiler;
v___x_4488_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4341_, v___x_4487_);
if (v___x_4488_ == 0)
{
lean_object* v___x_4489_; 
lean_dec_ref(v___f_4345_);
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
lean_inc_ref(v_a_4336_);
v___x_4489_ = lean_apply_5(v_k_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, lean_box(0));
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; uint8_t v___x_4493_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
v___x_4491_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4492_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4493_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4344_, v_options_4341_, v___x_4492_);
if (v___x_4493_ == 0)
{
lean_dec(v_a_4490_);
return v___x_4489_;
}
else
{
lean_object* v___x_4494_; lean_object* v___x_4495_; 
lean_dec_ref_known(v___x_4489_, 1);
lean_inc(v_a_4490_);
v___x_4494_ = l_Lean_MessageData_ofExpr(v_a_4490_);
v___x_4495_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4491_, v___x_4494_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4502_ == 0)
{
lean_object* v_unused_4503_; 
v_unused_4503_ = lean_ctor_get(v___x_4495_, 0);
lean_dec(v_unused_4503_);
v___x_4497_ = v___x_4495_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_dec(v___x_4495_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
lean_ctor_set(v___x_4497_, 0, v_a_4490_);
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4490_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v_a_4490_);
v_a_4504_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4495_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4495_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
lean_inc(v_a_4504_);
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
v___y_4373_ = v___x_4509_;
v_a_4374_ = v_a_4504_;
goto v___jp_4372_;
}
}
}
}
}
else
{
lean_object* v_a_4512_; 
v_a_4512_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4512_);
v___y_4373_ = v___x_4489_;
v_a_4374_ = v_a_4512_;
goto v___jp_4372_;
}
}
else
{
goto v___jp_4462_;
}
}
else
{
goto v___jp_4462_;
}
v___jp_4346_:
{
if (v___y_4349_ == 0)
{
lean_object* v___x_4350_; lean_object* v___x_4351_; uint8_t v___x_4352_; 
lean_dec_ref(v___y_4347_);
v___x_4350_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4351_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4352_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4344_, v_options_4341_, v___x_4351_);
if (v___x_4352_ == 0)
{
lean_object* v___x_4353_; 
v___x_4353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4353_, 0, v___y_4348_);
return v___x_4353_;
}
else
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
lean_inc_ref(v___y_4348_);
v___x_4354_ = l_Lean_Exception_toMessageData(v___y_4348_);
v___x_4355_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4350_, v___x_4354_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4362_ == 0)
{
lean_object* v_unused_4363_; 
v_unused_4363_ = lean_ctor_get(v___x_4355_, 0);
lean_dec(v_unused_4363_);
v___x_4357_ = v___x_4355_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_dec(v___x_4355_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
lean_ctor_set_tag(v___x_4357_, 1);
lean_ctor_set(v___x_4357_, 0, v___y_4348_);
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v___y_4348_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
else
{
lean_object* v_a_4364_; lean_object* v___x_4366_; uint8_t v_isShared_4367_; uint8_t v_isSharedCheck_4371_; 
lean_dec_ref(v___y_4348_);
v_a_4364_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4366_ = v___x_4355_;
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
else
{
lean_inc(v_a_4364_);
lean_dec(v___x_4355_);
v___x_4366_ = lean_box(0);
v_isShared_4367_ = v_isSharedCheck_4371_;
goto v_resetjp_4365_;
}
v_resetjp_4365_:
{
lean_object* v___x_4369_; 
if (v_isShared_4367_ == 0)
{
v___x_4369_ = v___x_4366_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4348_);
return v___y_4347_;
}
}
v___jp_4372_:
{
uint8_t v___x_4375_; 
v___x_4375_ = l_Lean_Exception_isInterrupt(v_a_4374_);
if (v___x_4375_ == 0)
{
uint8_t v___x_4376_; 
lean_inc_ref(v_a_4374_);
v___x_4376_ = l_Lean_Exception_isRuntime(v_a_4374_);
v___y_4347_ = v___y_4373_;
v___y_4348_ = v_a_4374_;
v___y_4349_ = v___x_4376_;
goto v___jp_4346_;
}
else
{
v___y_4347_ = v___y_4373_;
v___y_4348_ = v_a_4374_;
v___y_4349_ = v___x_4375_;
goto v___jp_4346_;
}
}
v___jp_4381_:
{
lean_object* v___x_4385_; double v___x_4386_; double v___x_4387_; double v___x_4388_; double v___x_4389_; double v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4385_ = lean_io_mono_nanos_now();
v___x_4386_ = lean_float_of_nat(v___y_4382_);
v___x_4387_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4388_ = lean_float_div(v___x_4386_, v___x_4387_);
v___x_4389_ = lean_float_of_nat(v___x_4385_);
v___x_4390_ = lean_float_div(v___x_4389_, v___x_4387_);
v___x_4391_ = lean_box_float(v___x_4388_);
v___x_4392_ = lean_box_float(v___x_4390_);
v___x_4393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4393_, 0, v___x_4391_);
lean_ctor_set(v___x_4393_, 1, v___x_4392_);
v___x_4394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4394_, 0, v_a_4384_);
lean_ctor_set(v___x_4394_, 1, v___x_4393_);
v___x_4395_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4377_, v_hasTrace_4342_, v___x_4378_, v_options_4341_, v___x_4380_, v___y_4383_, v___f_4345_, v___x_4394_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
return v___x_4395_;
}
v___jp_4396_:
{
lean_object* v___x_4400_; 
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v_a_4399_);
v___y_4382_ = v___y_4397_;
v___y_4383_ = v___y_4398_;
v_a_4384_ = v___x_4400_;
goto v___jp_4381_;
}
v___jp_4401_:
{
if (v___y_4405_ == 0)
{
lean_object* v___x_4406_; lean_object* v___x_4407_; uint8_t v___x_4408_; 
v___x_4406_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4407_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4408_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4344_, v_options_4341_, v___x_4407_);
if (v___x_4408_ == 0)
{
v___y_4397_ = v___y_4402_;
v___y_4398_ = v___y_4404_;
v_a_4399_ = v___y_4403_;
goto v___jp_4396_;
}
else
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
lean_inc_ref(v___y_4403_);
v___x_4409_ = l_Lean_Exception_toMessageData(v___y_4403_);
v___x_4410_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4406_, v___x_4409_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_dec_ref_known(v___x_4410_, 1);
v___y_4397_ = v___y_4402_;
v___y_4398_ = v___y_4404_;
v_a_4399_ = v___y_4403_;
goto v___jp_4396_;
}
else
{
lean_object* v_a_4411_; 
lean_dec_ref(v___y_4403_);
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___y_4397_ = v___y_4402_;
v___y_4398_ = v___y_4404_;
v_a_4399_ = v_a_4411_;
goto v___jp_4396_;
}
}
}
else
{
v___y_4397_ = v___y_4402_;
v___y_4398_ = v___y_4404_;
v_a_4399_ = v___y_4403_;
goto v___jp_4396_;
}
}
v___jp_4412_:
{
uint8_t v___x_4416_; 
v___x_4416_ = l_Lean_Exception_isInterrupt(v_a_4415_);
if (v___x_4416_ == 0)
{
uint8_t v___x_4417_; 
lean_inc_ref(v_a_4415_);
v___x_4417_ = l_Lean_Exception_isRuntime(v_a_4415_);
v___y_4402_ = v___y_4413_;
v___y_4403_ = v_a_4415_;
v___y_4404_ = v___y_4414_;
v___y_4405_ = v___x_4417_;
goto v___jp_4401_;
}
else
{
v___y_4402_ = v___y_4413_;
v___y_4403_ = v_a_4415_;
v___y_4404_ = v___y_4414_;
v___y_4405_ = v___x_4416_;
goto v___jp_4401_;
}
}
v___jp_4418_:
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4422_, 0, v_a_4421_);
v___y_4382_ = v___y_4419_;
v___y_4383_ = v___y_4420_;
v_a_4384_ = v___x_4422_;
goto v___jp_4381_;
}
v___jp_4423_:
{
lean_object* v___x_4427_; double v___x_4428_; double v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; 
v___x_4427_ = lean_io_get_num_heartbeats();
v___x_4428_ = lean_float_of_nat(v___y_4424_);
v___x_4429_ = lean_float_of_nat(v___x_4427_);
v___x_4430_ = lean_box_float(v___x_4428_);
v___x_4431_ = lean_box_float(v___x_4429_);
v___x_4432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4432_, 0, v___x_4430_);
lean_ctor_set(v___x_4432_, 1, v___x_4431_);
v___x_4433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4433_, 0, v_a_4426_);
lean_ctor_set(v___x_4433_, 1, v___x_4432_);
v___x_4434_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4377_, v_hasTrace_4342_, v___x_4378_, v_options_4341_, v___x_4380_, v___y_4425_, v___f_4345_, v___x_4433_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
return v___x_4434_;
}
v___jp_4435_:
{
lean_object* v___x_4439_; 
v___x_4439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4439_, 0, v_a_4438_);
v___y_4424_ = v___y_4436_;
v___y_4425_ = v___y_4437_;
v_a_4426_ = v___x_4439_;
goto v___jp_4423_;
}
v___jp_4440_:
{
if (v___y_4444_ == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4446_; uint8_t v___x_4447_; 
v___x_4445_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4446_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4447_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4344_, v_options_4341_, v___x_4446_);
if (v___x_4447_ == 0)
{
v___y_4436_ = v___y_4441_;
v___y_4437_ = v___y_4443_;
v_a_4438_ = v___y_4442_;
goto v___jp_4435_;
}
else
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
lean_inc_ref(v___y_4442_);
v___x_4448_ = l_Lean_Exception_toMessageData(v___y_4442_);
v___x_4449_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4445_, v___x_4448_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_dec_ref_known(v___x_4449_, 1);
v___y_4436_ = v___y_4441_;
v___y_4437_ = v___y_4443_;
v_a_4438_ = v___y_4442_;
goto v___jp_4435_;
}
else
{
lean_object* v_a_4450_; 
lean_dec_ref(v___y_4442_);
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
v___y_4436_ = v___y_4441_;
v___y_4437_ = v___y_4443_;
v_a_4438_ = v_a_4450_;
goto v___jp_4435_;
}
}
}
else
{
v___y_4436_ = v___y_4441_;
v___y_4437_ = v___y_4443_;
v_a_4438_ = v___y_4442_;
goto v___jp_4435_;
}
}
v___jp_4451_:
{
uint8_t v___x_4455_; 
v___x_4455_ = l_Lean_Exception_isInterrupt(v_a_4454_);
if (v___x_4455_ == 0)
{
uint8_t v___x_4456_; 
lean_inc_ref(v_a_4454_);
v___x_4456_ = l_Lean_Exception_isRuntime(v_a_4454_);
v___y_4441_ = v___y_4452_;
v___y_4442_ = v_a_4454_;
v___y_4443_ = v___y_4453_;
v___y_4444_ = v___x_4456_;
goto v___jp_4440_;
}
else
{
v___y_4441_ = v___y_4452_;
v___y_4442_ = v_a_4454_;
v___y_4443_ = v___y_4453_;
v___y_4444_ = v___x_4455_;
goto v___jp_4440_;
}
}
v___jp_4457_:
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4461_, 0, v_a_4460_);
v___y_4424_ = v___y_4458_;
v___y_4425_ = v___y_4459_;
v_a_4426_ = v___x_4461_;
goto v___jp_4423_;
}
v___jp_4462_:
{
lean_object* v___x_4463_; lean_object* v_a_4464_; lean_object* v___x_4465_; uint8_t v___x_4466_; 
v___x_4463_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4339_);
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref(v___x_4463_);
v___x_4465_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4466_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4341_, v___x_4465_);
if (v___x_4466_ == 0)
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = lean_io_mono_nanos_now();
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
lean_inc_ref(v_a_4336_);
v___x_4468_ = lean_apply_5(v_k_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, lean_box(0));
if (lean_obj_tag(v___x_4468_) == 0)
{
lean_object* v_a_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; uint8_t v___x_4472_; 
v_a_4469_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4469_);
lean_dec_ref_known(v___x_4468_, 1);
v___x_4470_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4471_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4472_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4344_, v_options_4341_, v___x_4471_);
if (v___x_4472_ == 0)
{
v___y_4419_ = v___x_4467_;
v___y_4420_ = v_a_4464_;
v_a_4421_ = v_a_4469_;
goto v___jp_4418_;
}
else
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
lean_inc(v_a_4469_);
v___x_4473_ = l_Lean_MessageData_ofExpr(v_a_4469_);
v___x_4474_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4470_, v___x_4473_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_dec_ref_known(v___x_4474_, 1);
v___y_4419_ = v___x_4467_;
v___y_4420_ = v_a_4464_;
v_a_4421_ = v_a_4469_;
goto v___jp_4418_;
}
else
{
lean_object* v_a_4475_; 
lean_dec(v_a_4469_);
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___y_4413_ = v___x_4467_;
v___y_4414_ = v_a_4464_;
v_a_4415_ = v_a_4475_;
goto v___jp_4412_;
}
}
}
else
{
lean_object* v_a_4476_; 
v_a_4476_ = lean_ctor_get(v___x_4468_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4468_, 1);
v___y_4413_ = v___x_4467_;
v___y_4414_ = v_a_4464_;
v_a_4415_ = v_a_4476_;
goto v___jp_4412_;
}
}
else
{
lean_object* v___x_4477_; lean_object* v___x_4478_; 
v___x_4477_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4339_);
lean_inc_ref(v_a_4338_);
lean_inc(v_a_4337_);
lean_inc_ref(v_a_4336_);
v___x_4478_ = lean_apply_5(v_k_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_, lean_box(0));
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; uint8_t v___x_4482_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref_known(v___x_4478_, 1);
v___x_4480_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4481_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4482_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4344_, v_options_4341_, v___x_4481_);
if (v___x_4482_ == 0)
{
v___y_4458_ = v___x_4477_;
v___y_4459_ = v_a_4464_;
v_a_4460_ = v_a_4479_;
goto v___jp_4457_;
}
else
{
lean_object* v___x_4483_; lean_object* v___x_4484_; 
lean_inc(v_a_4479_);
v___x_4483_ = l_Lean_MessageData_ofExpr(v_a_4479_);
v___x_4484_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4480_, v___x_4483_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_dec_ref_known(v___x_4484_, 1);
v___y_4458_ = v___x_4477_;
v___y_4459_ = v_a_4464_;
v_a_4460_ = v_a_4479_;
goto v___jp_4457_;
}
else
{
lean_object* v_a_4485_; 
lean_dec(v_a_4479_);
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref_known(v___x_4484_, 1);
v___y_4452_ = v___x_4477_;
v___y_4453_ = v_a_4464_;
v_a_4454_ = v_a_4485_;
goto v___jp_4451_;
}
}
}
else
{
lean_object* v_a_4486_; 
v_a_4486_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4478_, 1);
v___y_4452_ = v___x_4477_;
v___y_4453_ = v_a_4464_;
v_a_4454_ = v_a_4486_;
goto v___jp_4451_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4513_, lean_object* v_xs_4514_, lean_object* v_k_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_, lean_object* v_a_4519_, lean_object* v_a_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4513_, v_xs_4514_, v_k_4515_, v_a_4516_, v_a_4517_, v_a_4518_, v_a_4519_);
lean_dec(v_a_4519_);
lean_dec_ref(v_a_4518_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4522_, lean_object* v_xs_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_){
_start:
{
lean_object* v___x_4529_; 
lean_inc(v_a_4527_);
lean_inc_ref(v_a_4526_);
lean_inc(v_a_4525_);
lean_inc_ref(v_a_4524_);
lean_inc_ref(v_f_4522_);
v___x_4529_ = lean_infer_type(v_f_4522_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_object* v_a_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; uint8_t v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v___x_4531_ = lean_unsigned_to_nat(0u);
v___x_4532_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4523_);
lean_inc_ref(v_f_4522_);
v___x_4533_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4533_, 0, v_f_4522_);
lean_closure_set(v___x_4533_, 1, v_xs_4523_);
lean_closure_set(v___x_4533_, 2, v___x_4531_);
lean_closure_set(v___x_4533_, 3, v___x_4532_);
lean_closure_set(v___x_4533_, 4, v___x_4531_);
lean_closure_set(v___x_4533_, 5, v___x_4532_);
lean_closure_set(v___x_4533_, 6, v_a_4530_);
v___x_4534_ = 0;
v___x_4535_ = lean_box(v___x_4534_);
v___x_4536_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4536_, 0, lean_box(0));
lean_closure_set(v___x_4536_, 1, v___x_4533_);
lean_closure_set(v___x_4536_, 2, v___x_4535_);
v___x_4537_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4522_, v_xs_4523_, v___x_4536_, v_a_4524_, v_a_4525_, v_a_4526_, v_a_4527_);
return v___x_4537_;
}
else
{
lean_dec_ref(v_xs_4523_);
lean_dec_ref(v_f_4522_);
return v___x_4529_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4538_, lean_object* v_xs_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_){
_start:
{
lean_object* v_res_4545_; 
v_res_4545_ = l_Lean_Meta_mkAppOptM_x27(v_f_4538_, v_xs_4539_, v_a_4540_, v_a_4541_, v_a_4542_, v_a_4543_);
lean_dec(v_a_4543_);
lean_dec_ref(v_a_4542_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
return v_res_4545_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4553_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4554_ = l_Lean_MessageData_ofFormat(v___x_4553_);
return v___x_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4555_, lean_object* v_h1_4556_, lean_object* v_h2_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_, lean_object* v_a_4560_, lean_object* v_a_4561_){
_start:
{
lean_object* v___x_4563_; uint8_t v___x_4564_; 
v___x_4563_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4564_ = l_Lean_Expr_isAppOf(v_h2_4557_, v___x_4563_);
if (v___x_4564_ == 0)
{
lean_object* v___x_4565_; 
lean_inc_ref(v_h2_4557_);
v___x_4565_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4557_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4567_; lean_object* v___x_4568_; uint8_t v___x_4569_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v___x_4567_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4568_ = lean_unsigned_to_nat(3u);
v___x_4569_ = l_Lean_Expr_isAppOfArity(v_a_4566_, v___x_4567_, v___x_4568_);
if (v___x_4569_ == 0)
{
lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; 
lean_dec_ref(v_h1_4556_);
lean_dec_ref(v_motive_4555_);
v___x_4570_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4571_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4572_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4557_, v_a_4566_);
v___x_4573_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4571_);
lean_ctor_set(v___x_4573_, 1, v___x_4572_);
v___x_4574_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4570_, v___x_4573_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
return v___x_4574_;
}
else
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v___x_4575_ = l_Lean_Expr_appFn_x21(v_a_4566_);
v___x_4576_ = l_Lean_Expr_appFn_x21(v___x_4575_);
v___x_4577_ = l_Lean_Expr_appArg_x21(v___x_4576_);
lean_dec_ref(v___x_4576_);
lean_inc_ref(v___x_4577_);
v___x_4578_ = l_Lean_Meta_getLevel(v___x_4577_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4580_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
lean_inc(v_a_4579_);
lean_dec_ref_known(v___x_4578_, 1);
lean_inc_ref(v_motive_4555_);
v___x_4580_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4555_, v_a_4558_, v_a_4559_, v_a_4560_, v_a_4561_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4583_; uint8_t v_isShared_4584_; uint8_t v_isSharedCheck_4616_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4583_ = v___x_4580_;
v_isShared_4584_ = v_isSharedCheck_4616_;
goto v_resetjp_4582_;
}
else
{
lean_inc(v_a_4581_);
lean_dec(v___x_4580_);
v___x_4583_ = lean_box(0);
v_isShared_4584_ = v_isSharedCheck_4616_;
goto v_resetjp_4582_;
}
v_resetjp_4582_:
{
lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4589_; 
if (lean_obj_tag(v_a_4581_) == 7)
{
lean_object* v_body_4595_; 
v_body_4595_ = lean_ctor_get(v_a_4581_, 2);
lean_inc_ref(v_body_4595_);
lean_dec_ref_known(v_a_4581_, 3);
if (lean_obj_tag(v_body_4595_) == 3)
{
lean_object* v_u_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v_u_4596_ = lean_ctor_get(v_body_4595_, 0);
lean_inc(v_u_4596_);
lean_dec_ref_known(v_body_4595_, 1);
v___x_4597_ = l_Lean_Expr_appArg_x21(v___x_4575_);
lean_dec_ref(v___x_4575_);
v___x_4598_ = l_Lean_Expr_appArg_x21(v_a_4566_);
lean_dec(v_a_4566_);
v___x_4599_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4600_ = lean_box(0);
v___x_4601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4601_, 0, v_a_4579_);
lean_ctor_set(v___x_4601_, 1, v___x_4600_);
v___x_4602_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4602_, 0, v_u_4596_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = l_Lean_mkConst(v___x_4599_, v___x_4602_);
v___x_4604_ = lean_unsigned_to_nat(6u);
v___x_4605_ = lean_mk_empty_array_with_capacity(v___x_4604_);
v___x_4606_ = lean_array_push(v___x_4605_, v___x_4577_);
v___x_4607_ = lean_array_push(v___x_4606_, v___x_4597_);
v___x_4608_ = lean_array_push(v___x_4607_, v_motive_4555_);
v___x_4609_ = lean_array_push(v___x_4608_, v_h1_4556_);
v___x_4610_ = lean_array_push(v___x_4609_, v___x_4598_);
v___x_4611_ = lean_array_push(v___x_4610_, v_h2_4557_);
v___x_4612_ = l_Lean_mkAppN(v___x_4603_, v___x_4611_);
lean_dec_ref(v___x_4611_);
if (v_isShared_4584_ == 0)
{
lean_ctor_set(v___x_4583_, 0, v___x_4612_);
v___x_4614_ = v___x_4583_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4615_; 
v_reuseFailAlloc_4615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4615_, 0, v___x_4612_);
v___x_4614_ = v_reuseFailAlloc_4615_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
return v___x_4614_;
}
}
else
{
lean_dec_ref(v_body_4595_);
lean_del_object(v___x_4583_);
lean_dec(v_a_4579_);
lean_dec_ref(v___x_4577_);
lean_dec_ref(v___x_4575_);
lean_dec(v_a_4566_);
lean_dec_ref(v_h2_4557_);
lean_dec_ref(v_h1_4556_);
v___y_4586_ = v_a_4558_;
v___y_4587_ = v_a_4559_;
v___y_4588_ = v_a_4560_;
v___y_4589_ = v_a_4561_;
goto v___jp_4585_;
}
}
else
{
lean_del_object(v___x_4583_);
lean_dec(v_a_4581_);
lean_dec(v_a_4579_);
lean_dec_ref(v___x_4577_);
lean_dec_ref(v___x_4575_);
lean_dec(v_a_4566_);
lean_dec_ref(v_h2_4557_);
lean_dec_ref(v_h1_4556_);
v___y_4586_ = v_a_4558_;
v___y_4587_ = v_a_4559_;
v___y_4588_ = v_a_4560_;
v___y_4589_ = v_a_4561_;
goto v___jp_4585_;
}
v___jp_4585_:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; 
v___x_4590_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4591_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4592_ = l_Lean_indentExpr(v_motive_4555_);
v___x_4593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4593_, 0, v___x_4591_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4590_, v___x_4593_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
return v___x_4594_;
}
}
}
else
{
lean_dec(v_a_4579_);
lean_dec_ref(v___x_4577_);
lean_dec_ref(v___x_4575_);
lean_dec(v_a_4566_);
lean_dec_ref(v_h2_4557_);
lean_dec_ref(v_h1_4556_);
lean_dec_ref(v_motive_4555_);
return v___x_4580_;
}
}
else
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_dec_ref(v___x_4577_);
lean_dec_ref(v___x_4575_);
lean_dec(v_a_4566_);
lean_dec_ref(v_h2_4557_);
lean_dec_ref(v_h1_4556_);
lean_dec_ref(v_motive_4555_);
v_a_4617_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4578_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4578_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4557_);
lean_dec_ref(v_h1_4556_);
lean_dec_ref(v_motive_4555_);
return v___x_4565_;
}
}
else
{
lean_object* v___x_4625_; 
lean_dec_ref(v_h2_4557_);
lean_dec_ref(v_motive_4555_);
v___x_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4625_, 0, v_h1_4556_);
return v___x_4625_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4626_, lean_object* v_h1_4627_, lean_object* v_h2_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_Meta_mkEqNDRec(v_motive_4626_, v_h1_4627_, v_h2_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
lean_dec(v_a_4632_);
lean_dec_ref(v_a_4631_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
return v_res_4634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4639_, lean_object* v_h1_4640_, lean_object* v_h2_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
lean_object* v___x_4647_; uint8_t v___x_4648_; 
v___x_4647_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4648_ = l_Lean_Expr_isAppOf(v_h2_4641_, v___x_4647_);
if (v___x_4648_ == 0)
{
lean_object* v___x_4649_; 
lean_inc_ref(v_h2_4641_);
v___x_4649_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v___x_4651_; lean_object* v___x_4652_; uint8_t v___x_4653_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
lean_inc(v_a_4650_);
lean_dec_ref_known(v___x_4649_, 1);
v___x_4651_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4652_ = lean_unsigned_to_nat(3u);
v___x_4653_ = l_Lean_Expr_isAppOfArity(v_a_4650_, v___x_4651_, v___x_4652_);
if (v___x_4653_ == 0)
{
lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; 
lean_dec(v_a_4650_);
lean_dec_ref(v_h1_4640_);
lean_dec_ref(v_motive_4639_);
v___x_4654_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4655_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4656_ = l_Lean_indentExpr(v_h2_4641_);
v___x_4657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4657_, 0, v___x_4655_);
lean_ctor_set(v___x_4657_, 1, v___x_4656_);
v___x_4658_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4654_, v___x_4657_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
return v___x_4658_;
}
else
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; 
v___x_4659_ = l_Lean_Expr_appFn_x21(v_a_4650_);
v___x_4660_ = l_Lean_Expr_appFn_x21(v___x_4659_);
v___x_4661_ = l_Lean_Expr_appArg_x21(v___x_4660_);
lean_dec_ref(v___x_4660_);
lean_inc_ref(v___x_4661_);
v___x_4662_ = l_Lean_Meta_getLevel(v___x_4661_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4664_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc(v_a_4663_);
lean_dec_ref_known(v___x_4662_, 1);
lean_inc_ref(v_motive_4639_);
v___x_4664_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4639_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4701_; 
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4667_ = v___x_4664_;
v_isShared_4668_ = v_isSharedCheck_4701_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4701_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4673_; 
if (lean_obj_tag(v_a_4665_) == 7)
{
lean_object* v_body_4679_; 
v_body_4679_ = lean_ctor_get(v_a_4665_, 2);
lean_inc_ref(v_body_4679_);
lean_dec_ref_known(v_a_4665_, 3);
if (lean_obj_tag(v_body_4679_) == 7)
{
lean_object* v_body_4680_; 
v_body_4680_ = lean_ctor_get(v_body_4679_, 2);
lean_inc_ref(v_body_4680_);
lean_dec_ref_known(v_body_4679_, 3);
if (lean_obj_tag(v_body_4680_) == 3)
{
lean_object* v_u_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4699_; 
v_u_4681_ = lean_ctor_get(v_body_4680_, 0);
lean_inc(v_u_4681_);
lean_dec_ref_known(v_body_4680_, 1);
v___x_4682_ = l_Lean_Expr_appArg_x21(v___x_4659_);
lean_dec_ref(v___x_4659_);
v___x_4683_ = l_Lean_Expr_appArg_x21(v_a_4650_);
lean_dec(v_a_4650_);
v___x_4684_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4685_ = lean_box(0);
v___x_4686_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4686_, 0, v_a_4663_);
lean_ctor_set(v___x_4686_, 1, v___x_4685_);
v___x_4687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4687_, 0, v_u_4681_);
lean_ctor_set(v___x_4687_, 1, v___x_4686_);
v___x_4688_ = l_Lean_mkConst(v___x_4684_, v___x_4687_);
v___x_4689_ = lean_unsigned_to_nat(6u);
v___x_4690_ = lean_mk_empty_array_with_capacity(v___x_4689_);
v___x_4691_ = lean_array_push(v___x_4690_, v___x_4661_);
v___x_4692_ = lean_array_push(v___x_4691_, v___x_4682_);
v___x_4693_ = lean_array_push(v___x_4692_, v_motive_4639_);
v___x_4694_ = lean_array_push(v___x_4693_, v_h1_4640_);
v___x_4695_ = lean_array_push(v___x_4694_, v___x_4683_);
v___x_4696_ = lean_array_push(v___x_4695_, v_h2_4641_);
v___x_4697_ = l_Lean_mkAppN(v___x_4688_, v___x_4696_);
lean_dec_ref(v___x_4696_);
if (v_isShared_4668_ == 0)
{
lean_ctor_set(v___x_4667_, 0, v___x_4697_);
v___x_4699_ = v___x_4667_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v___x_4697_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
else
{
lean_dec_ref(v_body_4680_);
lean_del_object(v___x_4667_);
lean_dec(v_a_4663_);
lean_dec_ref(v___x_4661_);
lean_dec_ref(v___x_4659_);
lean_dec(v_a_4650_);
lean_dec_ref(v_h2_4641_);
lean_dec_ref(v_h1_4640_);
v___y_4670_ = v_a_4642_;
v___y_4671_ = v_a_4643_;
v___y_4672_ = v_a_4644_;
v___y_4673_ = v_a_4645_;
goto v___jp_4669_;
}
}
else
{
lean_dec_ref(v_body_4679_);
lean_del_object(v___x_4667_);
lean_dec(v_a_4663_);
lean_dec_ref(v___x_4661_);
lean_dec_ref(v___x_4659_);
lean_dec(v_a_4650_);
lean_dec_ref(v_h2_4641_);
lean_dec_ref(v_h1_4640_);
v___y_4670_ = v_a_4642_;
v___y_4671_ = v_a_4643_;
v___y_4672_ = v_a_4644_;
v___y_4673_ = v_a_4645_;
goto v___jp_4669_;
}
}
else
{
lean_del_object(v___x_4667_);
lean_dec(v_a_4665_);
lean_dec(v_a_4663_);
lean_dec_ref(v___x_4661_);
lean_dec_ref(v___x_4659_);
lean_dec(v_a_4650_);
lean_dec_ref(v_h2_4641_);
lean_dec_ref(v_h1_4640_);
v___y_4670_ = v_a_4642_;
v___y_4671_ = v_a_4643_;
v___y_4672_ = v_a_4644_;
v___y_4673_ = v_a_4645_;
goto v___jp_4669_;
}
v___jp_4669_:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4674_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4675_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4676_ = l_Lean_indentExpr(v_motive_4639_);
v___x_4677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4675_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
v___x_4678_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4674_, v___x_4677_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
return v___x_4678_;
}
}
}
else
{
lean_dec(v_a_4663_);
lean_dec_ref(v___x_4661_);
lean_dec_ref(v___x_4659_);
lean_dec(v_a_4650_);
lean_dec_ref(v_h2_4641_);
lean_dec_ref(v_h1_4640_);
lean_dec_ref(v_motive_4639_);
return v___x_4664_;
}
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_dec_ref(v___x_4661_);
lean_dec_ref(v___x_4659_);
lean_dec(v_a_4650_);
lean_dec_ref(v_h2_4641_);
lean_dec_ref(v_h1_4640_);
lean_dec_ref(v_motive_4639_);
v_a_4702_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4662_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4662_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4707_; 
if (v_isShared_4705_ == 0)
{
v___x_4707_ = v___x_4704_;
goto v_reusejp_4706_;
}
else
{
lean_object* v_reuseFailAlloc_4708_; 
v_reuseFailAlloc_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
v___x_4707_ = v_reuseFailAlloc_4708_;
goto v_reusejp_4706_;
}
v_reusejp_4706_:
{
return v___x_4707_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4641_);
lean_dec_ref(v_h1_4640_);
lean_dec_ref(v_motive_4639_);
return v___x_4649_;
}
}
else
{
lean_object* v___x_4710_; 
lean_dec_ref(v_h2_4641_);
lean_dec_ref(v_motive_4639_);
v___x_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4710_, 0, v_h1_4640_);
return v___x_4710_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4711_, lean_object* v_h1_4712_, lean_object* v_h2_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_){
_start:
{
lean_object* v_res_4719_; 
v_res_4719_ = l_Lean_Meta_mkEqRec(v_motive_4711_, v_h1_4712_, v_h2_4713_, v_a_4714_, v_a_4715_, v_a_4716_, v_a_4717_);
lean_dec(v_a_4717_);
lean_dec_ref(v_a_4716_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
return v_res_4719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4724_, lean_object* v_pr_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_){
_start:
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; 
v___x_4731_ = ((lean_object*)(l_Lean_Meta_mkEqMP___closed__1));
v___x_4732_ = lean_unsigned_to_nat(2u);
v___x_4733_ = lean_mk_empty_array_with_capacity(v___x_4732_);
v___x_4734_ = lean_array_push(v___x_4733_, v_eqProof_4724_);
v___x_4735_ = lean_array_push(v___x_4734_, v_pr_4725_);
v___x_4736_ = l_Lean_Meta_mkAppM(v___x_4731_, v___x_4735_, v_a_4726_, v_a_4727_, v_a_4728_, v_a_4729_);
return v___x_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4737_, lean_object* v_pr_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_){
_start:
{
lean_object* v_res_4744_; 
v_res_4744_ = l_Lean_Meta_mkEqMP(v_eqProof_4737_, v_pr_4738_, v_a_4739_, v_a_4740_, v_a_4741_, v_a_4742_);
lean_dec(v_a_4742_);
lean_dec_ref(v_a_4741_);
lean_dec(v_a_4740_);
lean_dec_ref(v_a_4739_);
return v_res_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4749_, lean_object* v_pr_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_){
_start:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; 
v___x_4756_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4757_ = lean_unsigned_to_nat(2u);
v___x_4758_ = lean_mk_empty_array_with_capacity(v___x_4757_);
v___x_4759_ = lean_array_push(v___x_4758_, v_eqProof_4749_);
v___x_4760_ = lean_array_push(v___x_4759_, v_pr_4750_);
v___x_4761_ = l_Lean_Meta_mkAppM(v___x_4756_, v___x_4760_, v_a_4751_, v_a_4752_, v_a_4753_, v_a_4754_);
return v___x_4761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4762_, lean_object* v_pr_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_){
_start:
{
lean_object* v_res_4769_; 
v_res_4769_ = l_Lean_Meta_mkEqMPR(v_eqProof_4762_, v_pr_4763_, v_a_4764_, v_a_4765_, v_a_4766_, v_a_4767_);
lean_dec(v_a_4767_);
lean_dec_ref(v_a_4766_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v___f_4776_; lean_object* v___x_12328__overap_4777_; lean_object* v___x_4778_; 
v___f_4776_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12328__overap_4777_ = lean_panic_fn_borrowed(v___f_4776_, v_msg_4770_);
lean_inc(v___y_4774_);
lean_inc_ref(v___y_4773_);
lean_inc(v___y_4772_);
lean_inc_ref(v___y_4771_);
v___x_4778_ = lean_apply_5(v___x_12328__overap_4777_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, lean_box(0));
return v___x_4778_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4786_, uint8_t v_skipRealize_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v___x_4790_; lean_object* v_env_4791_; uint8_t v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4790_ = lean_st_ref_get(v___y_4788_);
v_env_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc_ref(v_env_4791_);
lean_dec(v___x_4790_);
v___x_4792_ = l_Lean_Environment_contains(v_env_4791_, v_constName_4786_, v_skipRealize_4787_);
v___x_4793_ = lean_box(v___x_4792_);
v___x_4794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4795_, lean_object* v_skipRealize_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
uint8_t v_skipRealize_boxed_4799_; lean_object* v_res_4800_; 
v_skipRealize_boxed_4799_ = lean_unbox(v_skipRealize_4796_);
v_res_4800_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4795_, v_skipRealize_boxed_4799_, v___y_4797_);
lean_dec(v___y_4797_);
return v_res_4800_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4801_, uint8_t v_skipRealize_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
lean_object* v___x_4808_; 
v___x_4808_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4801_, v_skipRealize_4802_, v___y_4806_);
return v___x_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4809_, lean_object* v_skipRealize_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
uint8_t v_skipRealize_boxed_4816_; lean_object* v_res_4817_; 
v_skipRealize_boxed_4816_ = lean_unbox(v_skipRealize_4810_);
v_res_4817_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4809_, v_skipRealize_boxed_4816_, v___y_4811_, v___y_4812_, v___y_4813_, v___y_4814_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___y_4818_, uint8_t v___x_4819_, lean_object* v_P_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; uint8_t v___x_4829_; lean_object* v___x_4830_; 
v___x_4826_ = lean_unsigned_to_nat(1u);
v___x_4827_ = lean_mk_empty_array_with_capacity(v___x_4826_);
lean_inc_ref(v_P_4820_);
v___x_4828_ = lean_array_push(v___x_4827_, v_P_4820_);
v___x_4829_ = 1;
v___x_4830_ = l_Lean_Meta_mkLambdaFVars(v___x_4828_, v_P_4820_, v___y_4818_, v___x_4819_, v___y_4818_, v___x_4819_, v___x_4829_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
lean_dec_ref(v___x_4828_);
return v___x_4830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___y_4831_, lean_object* v___x_4832_, lean_object* v_P_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_){
_start:
{
uint8_t v___y_13571__boxed_4839_; uint8_t v___x_13572__boxed_4840_; lean_object* v_res_4841_; 
v___y_13571__boxed_4839_ = lean_unbox(v___y_4831_);
v___x_13572__boxed_4840_ = lean_unbox(v___x_4832_);
v_res_4841_ = l_Lean_Meta_mkNoConfusion___lam__0(v___y_13571__boxed_4839_, v___x_13572__boxed_4840_, v_P_4833_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
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
lean_object* v_val_5097_; lean_object* v_fst_5098_; lean_object* v_snd_5099_; lean_object* v___x_5101_; uint8_t v_isShared_5102_; uint8_t v_isSharedCheck_5313_; 
v_val_5097_ = lean_ctor_get(v_a_5082_, 0);
lean_inc(v_val_5097_);
lean_dec_ref_known(v_a_5082_, 1);
v_fst_5098_ = lean_ctor_get(v_val_5097_, 0);
v_snd_5099_ = lean_ctor_get(v_val_5097_, 1);
v_isSharedCheck_5313_ = !lean_is_exclusive(v_val_5097_);
if (v_isSharedCheck_5313_ == 0)
{
v___x_5101_ = v_val_5097_;
v_isShared_5102_ = v_isSharedCheck_5313_;
goto v_resetjp_5100_;
}
else
{
lean_inc(v_snd_5099_);
lean_inc(v_fst_5098_);
lean_dec(v_val_5097_);
v___x_5101_ = lean_box(0);
v_isShared_5102_ = v_isSharedCheck_5313_;
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
lean_object* v_val_5105_; lean_object* v_fst_5106_; lean_object* v_snd_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5304_; 
v_val_5105_ = lean_ctor_get(v_a_5104_, 0);
lean_inc(v_val_5105_);
lean_dec_ref_known(v_a_5104_, 1);
v_fst_5106_ = lean_ctor_get(v_val_5105_, 0);
v_snd_5107_ = lean_ctor_get(v_val_5105_, 1);
v_isSharedCheck_5304_ = !lean_is_exclusive(v_val_5105_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5109_ = v_val_5105_;
v_isShared_5110_ = v_isSharedCheck_5304_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_snd_5107_);
lean_inc(v_fst_5106_);
lean_dec(v_val_5105_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5304_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v_toConstantVal_5111_; lean_object* v_cidx_5112_; lean_object* v_numParams_5113_; lean_object* v_numFields_5114_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; lean_object* v___y_5120_; lean_object* v___y_5121_; uint8_t v___y_5206_; lean_object* v_cidx_5234_; uint8_t v___x_5235_; 
v_toConstantVal_5111_ = lean_ctor_get(v_fst_5098_, 0);
lean_inc_ref(v_toConstantVal_5111_);
v_cidx_5112_ = lean_ctor_get(v_fst_5098_, 2);
lean_inc(v_cidx_5112_);
v_numParams_5113_ = lean_ctor_get(v_fst_5098_, 3);
lean_inc(v_numParams_5113_);
v_numFields_5114_ = lean_ctor_get(v_fst_5098_, 4);
lean_inc(v_numFields_5114_);
lean_dec(v_fst_5098_);
v_cidx_5234_ = lean_ctor_get(v_fst_5106_, 2);
lean_inc(v_cidx_5234_);
lean_dec(v_fst_5106_);
v___x_5235_ = lean_nat_dec_eq(v_cidx_5112_, v_cidx_5234_);
lean_dec(v_cidx_5234_);
lean_dec(v_cidx_5112_);
if (v___x_5235_ == 0)
{
if (v___x_5048_ == 0)
{
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec_ref(v_val_5077_);
v___y_5206_ = v___x_5048_;
goto v___jp_5205_;
}
else
{
lean_object* v_toConstantVal_5236_; lean_object* v_name_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v_a_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v_a_5244_; uint8_t v___x_5262_; 
lean_dec(v_numFields_5114_);
lean_dec(v_numParams_5113_);
lean_dec_ref(v_toConstantVal_5111_);
lean_del_object(v___x_5109_);
lean_dec(v_snd_5107_);
lean_del_object(v___x_5101_);
lean_dec(v_snd_5099_);
v_toConstantVal_5236_ = lean_ctor_get(v_val_5077_, 0);
lean_inc_ref(v_toConstantVal_5236_);
lean_dec_ref(v_val_5077_);
v_name_5237_ = lean_ctor_get(v_toConstantVal_5236_, 0);
lean_inc(v_name_5237_);
lean_dec_ref(v_toConstantVal_5236_);
v___x_5238_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5239_ = l_Lean_Name_str___override(v_name_5237_, v___x_5238_);
lean_inc(v___x_5239_);
v___x_5240_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5239_, v___x_5048_, v_a_5040_);
v_a_5241_ = lean_ctor_get(v___x_5240_, 0);
lean_inc(v_a_5241_);
lean_dec_ref(v___x_5240_);
v___x_5242_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5243_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5242_, v___x_5048_, v_a_5040_);
v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
lean_inc(v_a_5244_);
lean_dec_ref(v___x_5243_);
v___x_5262_ = lean_unbox(v_a_5241_);
lean_dec(v_a_5241_);
if (v___x_5262_ == 0)
{
lean_dec(v_a_5244_);
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
goto v___jp_5245_;
}
else
{
uint8_t v___x_5263_; 
v___x_5263_ = lean_unbox(v_a_5244_);
lean_dec(v_a_5244_);
if (v___x_5263_ == 0)
{
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
goto v___jp_5245_;
}
else
{
lean_object* v_dummy_5264_; lean_object* v_nargs_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; 
v_dummy_5264_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5265_ = l_Lean_Expr_getAppNumArgs(v_a_5058_);
lean_inc(v_nargs_5265_);
v___x_5266_ = lean_mk_array(v_nargs_5265_, v_dummy_5264_);
v___x_5267_ = lean_unsigned_to_nat(1u);
v___x_5268_ = lean_nat_sub(v_nargs_5265_, v___x_5267_);
lean_dec(v_nargs_5265_);
lean_inc_n(v_a_5058_, 2);
v___x_5269_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5058_, v___x_5266_, v___x_5268_);
v___x_5270_ = l_Lean_Meta_getLevel(v_a_5058_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
if (lean_obj_tag(v___x_5270_) == 0)
{
lean_object* v_a_5271_; lean_object* v___x_5273_; uint8_t v_isShared_5274_; uint8_t v_isSharedCheck_5295_; 
v_a_5271_ = lean_ctor_get(v___x_5270_, 0);
v_isSharedCheck_5295_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5273_ = v___x_5270_;
v_isShared_5274_ = v_isSharedCheck_5295_;
goto v_resetjp_5272_;
}
else
{
lean_inc(v_a_5271_);
lean_dec(v___x_5270_);
v___x_5273_ = lean_box(0);
v_isShared_5274_ = v_isSharedCheck_5295_;
goto v_resetjp_5272_;
}
v_resetjp_5272_:
{
lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5293_; 
v___x_5275_ = l_Lean_mkConst(v___x_5239_, v_us_5071_);
v___x_5276_ = l_Lean_mkAppN(v___x_5275_, v___x_5269_);
lean_dec_ref(v___x_5269_);
v___x_5277_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5278_ = lean_box(0);
v___x_5279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5279_, 0, v_a_5079_);
lean_ctor_set(v___x_5279_, 1, v___x_5278_);
v___x_5280_ = l_Lean_mkConst(v___x_5277_, v___x_5279_);
v___x_5281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5281_, 0, v_a_5271_);
lean_ctor_set(v___x_5281_, 1, v___x_5278_);
v___x_5282_ = l_Lean_mkConst(v___x_5242_, v___x_5281_);
v___x_5283_ = lean_unsigned_to_nat(5u);
v___x_5284_ = lean_mk_empty_array_with_capacity(v___x_5283_);
v___x_5285_ = lean_array_push(v___x_5284_, v_a_5058_);
v___x_5286_ = lean_array_push(v___x_5285_, v___x_5276_);
v___x_5287_ = lean_array_push(v___x_5286_, v___x_5080_);
v___x_5288_ = lean_array_push(v___x_5287_, v___x_5083_);
v___x_5289_ = lean_array_push(v___x_5288_, v_h_5036_);
v___x_5290_ = l_Lean_mkAppN(v___x_5282_, v___x_5289_);
lean_dec_ref(v___x_5289_);
v___x_5291_ = l_Lean_mkAppB(v___x_5280_, v_target_5035_, v___x_5290_);
if (v_isShared_5274_ == 0)
{
lean_ctor_set(v___x_5273_, 0, v___x_5291_);
v___x_5293_ = v___x_5273_;
goto v_reusejp_5292_;
}
else
{
lean_object* v_reuseFailAlloc_5294_; 
v_reuseFailAlloc_5294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5294_, 0, v___x_5291_);
v___x_5293_ = v_reuseFailAlloc_5294_;
goto v_reusejp_5292_;
}
v_reusejp_5292_:
{
return v___x_5293_;
}
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
lean_dec_ref(v___x_5269_);
lean_dec(v___x_5239_);
lean_dec_ref(v___x_5083_);
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5296_ = lean_ctor_get(v___x_5270_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5270_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5270_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5270_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
lean_object* v___x_5301_; 
if (v_isShared_5299_ == 0)
{
v___x_5301_ = v___x_5298_;
goto v_reusejp_5300_;
}
else
{
lean_object* v_reuseFailAlloc_5302_; 
v_reuseFailAlloc_5302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5302_, 0, v_a_5296_);
v___x_5301_ = v_reuseFailAlloc_5302_;
goto v_reusejp_5300_;
}
v_reusejp_5300_:
{
return v___x_5301_;
}
}
}
}
}
v___jp_5245_:
{
lean_object* v___x_5246_; lean_object* v___x_5247_; lean_object* v___x_5248_; lean_object* v___x_5249_; lean_object* v___x_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v_a_5254_; lean_object* v___x_5256_; uint8_t v_isShared_5257_; uint8_t v_isSharedCheck_5261_; 
v___x_5246_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5247_ = l_Lean_MessageData_ofName(v___x_5239_);
v___x_5248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5246_);
lean_ctor_set(v___x_5248_, 1, v___x_5247_);
v___x_5249_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__23, &l_Lean_Meta_mkNoConfusion___closed__23_once, _init_l_Lean_Meta_mkNoConfusion___closed__23);
v___x_5250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5250_, 0, v___x_5248_);
lean_ctor_set(v___x_5250_, 1, v___x_5249_);
v___x_5251_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__24, &l_Lean_Meta_mkNoConfusion___closed__24_once, _init_l_Lean_Meta_mkNoConfusion___closed__24);
v___x_5252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5250_);
lean_ctor_set(v___x_5252_, 1, v___x_5251_);
v___x_5253_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5252_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
v_a_5254_ = lean_ctor_get(v___x_5253_, 0);
v_isSharedCheck_5261_ = !lean_is_exclusive(v___x_5253_);
if (v_isSharedCheck_5261_ == 0)
{
v___x_5256_ = v___x_5253_;
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
else
{
lean_inc(v_a_5254_);
lean_dec(v___x_5253_);
v___x_5256_ = lean_box(0);
v_isShared_5257_ = v_isSharedCheck_5261_;
goto v_resetjp_5255_;
}
v_resetjp_5255_:
{
lean_object* v___x_5259_; 
if (v_isShared_5257_ == 0)
{
v___x_5259_ = v___x_5256_;
goto v_reusejp_5258_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_a_5254_);
v___x_5259_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5258_;
}
v_reusejp_5258_:
{
return v___x_5259_;
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
v___y_5206_ = v___x_5074_;
goto v___jp_5205_;
}
v___jp_5115_:
{
lean_object* v___x_5122_; 
lean_inc(v___y_5117_);
v___x_5122_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
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
lean_inc(v___y_5116_);
v___x_5134_ = l_Array_toSubarray___redArg(v___x_5133_, v___y_5116_, v_numParams_5113_);
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
v___x_5155_ = l_Lean_mkConst(v___y_5117_, v___x_5154_);
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
lean_inc(v___y_5116_);
if (v_isShared_5128_ == 0)
{
lean_ctor_set(v___x_5127_, 2, v___x_5131_);
lean_ctor_set(v___x_5127_, 1, v___x_5163_);
lean_ctor_set(v___x_5127_, 0, v___y_5116_);
v___x_5165_ = v___x_5127_;
goto v_reusejp_5164_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___y_5116_);
lean_ctor_set(v_reuseFailAlloc_5192_, 1, v___x_5163_);
lean_ctor_set(v_reuseFailAlloc_5192_, 2, v___x_5131_);
v___x_5165_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5164_;
}
v_reusejp_5164_:
{
lean_object* v___x_5166_; 
v___x_5166_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5165_, v___x_5162_, v___y_5116_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
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
v___jp_5205_:
{
lean_object* v___x_5207_; uint8_t v___x_5208_; 
v___x_5207_ = lean_unsigned_to_nat(0u);
v___x_5208_ = lean_nat_dec_eq(v_numFields_5114_, v___x_5207_);
lean_dec(v_numFields_5114_);
if (v___x_5208_ == 0)
{
lean_object* v_name_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v_a_5213_; uint8_t v___x_5214_; 
v_name_5209_ = lean_ctor_get(v_toConstantVal_5111_, 0);
lean_inc(v_name_5209_);
lean_dec_ref(v_toConstantVal_5111_);
v___x_5210_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5211_ = l_Lean_Name_str___override(v_name_5209_, v___x_5210_);
lean_inc(v___x_5211_);
v___x_5212_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5211_, v___x_5048_, v_a_5040_);
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5213_);
lean_dec_ref(v___x_5212_);
v___x_5214_ = lean_unbox(v_a_5213_);
lean_dec(v_a_5213_);
if (v___x_5214_ == 0)
{
lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5218_; 
lean_dec(v_numParams_5113_);
lean_del_object(v___x_5109_);
lean_dec(v_snd_5107_);
lean_dec(v_snd_5099_);
lean_dec(v_a_5079_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v___x_5215_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5216_ = l_Lean_MessageData_ofName(v___x_5211_);
if (v_isShared_5102_ == 0)
{
lean_ctor_set_tag(v___x_5101_, 7);
lean_ctor_set(v___x_5101_, 1, v___x_5216_);
lean_ctor_set(v___x_5101_, 0, v___x_5215_);
v___x_5218_ = v___x_5101_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v___x_5215_);
lean_ctor_set(v_reuseFailAlloc_5228_, 1, v___x_5216_);
v___x_5218_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5219_; lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
v___x_5219_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5218_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
v_a_5220_ = lean_ctor_get(v___x_5219_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v___x_5219_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v___x_5219_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v___x_5219_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v_a_5220_);
v___x_5225_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5224_;
}
v_reusejp_5224_:
{
return v___x_5225_;
}
}
}
}
else
{
lean_del_object(v___x_5101_);
v___y_5116_ = v___x_5207_;
v___y_5117_ = v___x_5211_;
v___y_5118_ = v_a_5037_;
v___y_5119_ = v_a_5038_;
v___y_5120_ = v_a_5039_;
v___y_5121_ = v_a_5040_;
goto v___jp_5115_;
}
}
else
{
lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___f_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; 
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
v___x_5229_ = lean_box(v___y_5206_);
v___x_5230_ = lean_box(v___x_5208_);
v___f_5231_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5231_, 0, v___x_5229_);
lean_closure_set(v___f_5231_, 1, v___x_5230_);
v___x_5232_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5233_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5232_, v_target_5035_, v___f_5231_, v_a_5037_, v_a_5038_, v_a_5039_, v_a_5040_);
return v___x_5233_;
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
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
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
v_a_5305_ = lean_ctor_get(v___x_5103_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5103_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5103_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5103_);
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
lean_object* v_a_5314_; lean_object* v___x_5316_; uint8_t v_isShared_5317_; uint8_t v_isSharedCheck_5321_; 
lean_dec_ref(v___x_5080_);
lean_dec(v_a_5079_);
lean_dec_ref(v_val_5077_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5314_ = lean_ctor_get(v___x_5081_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___x_5081_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5316_ = v___x_5081_;
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
else
{
lean_inc(v_a_5314_);
lean_dec(v___x_5081_);
v___x_5316_ = lean_box(0);
v_isShared_5317_ = v_isSharedCheck_5321_;
goto v_resetjp_5315_;
}
v_resetjp_5315_:
{
lean_object* v___x_5319_; 
if (v_isShared_5317_ == 0)
{
v___x_5319_ = v___x_5316_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_a_5314_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
return v___x_5319_;
}
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
lean_dec_ref(v_val_5077_);
lean_dec(v_us_5071_);
lean_dec(v_a_5058_);
lean_dec_ref(v___x_5054_);
lean_dec(v_a_5045_);
lean_dec_ref(v_h_5036_);
lean_dec_ref(v_target_5035_);
v_a_5322_ = lean_ctor_get(v___x_5078_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___x_5078_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___x_5078_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___x_5078_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v___x_5327_; 
if (v_isShared_5325_ == 0)
{
v___x_5327_ = v___x_5324_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5328_; 
v_reuseFailAlloc_5328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5328_, 0, v_a_5322_);
v___x_5327_ = v_reuseFailAlloc_5328_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
return v___x_5327_;
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5330_, lean_object* v_h_5331_, lean_object* v_a_5332_, lean_object* v_a_5333_, lean_object* v_a_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l_Lean_Meta_mkNoConfusion(v_target_5330_, v_h_5331_, v_a_5332_, v_a_5333_, v_a_5334_, v_a_5335_);
lean_dec(v_a_5335_);
lean_dec_ref(v_a_5334_);
lean_dec(v_a_5333_);
lean_dec_ref(v_a_5332_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5338_, lean_object* v_b_5339_, lean_object* v_i_5340_, lean_object* v_hs_5341_, lean_object* v_hl_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_){
_start:
{
lean_object* v___x_5348_; 
v___x_5348_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5338_, v_b_5339_, v_i_5340_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
return v___x_5348_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5349_, lean_object* v_b_5350_, lean_object* v_i_5351_, lean_object* v_hs_5352_, lean_object* v_hl_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_){
_start:
{
lean_object* v_res_5359_; 
v_res_5359_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5349_, v_b_5350_, v_i_5351_, v_hs_5352_, v_hl_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
lean_dec_ref(v_range_5349_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5360_, lean_object* v_name_5361_, uint8_t v_bi_5362_, lean_object* v_type_5363_, lean_object* v_k_5364_, uint8_t v_kind_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_, lean_object* v___y_5368_, lean_object* v___y_5369_){
_start:
{
lean_object* v___x_5371_; 
v___x_5371_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5361_, v_bi_5362_, v_type_5363_, v_k_5364_, v_kind_5365_, v___y_5366_, v___y_5367_, v___y_5368_, v___y_5369_);
return v___x_5371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5372_, lean_object* v_name_5373_, lean_object* v_bi_5374_, lean_object* v_type_5375_, lean_object* v_k_5376_, lean_object* v_kind_5377_, lean_object* v___y_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
uint8_t v_bi_boxed_5383_; uint8_t v_kind_boxed_5384_; lean_object* v_res_5385_; 
v_bi_boxed_5383_ = lean_unbox(v_bi_5374_);
v_kind_boxed_5384_ = lean_unbox(v_kind_5377_);
v_res_5385_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5372_, v_name_5373_, v_bi_boxed_5383_, v_type_5375_, v_k_5376_, v_kind_boxed_5384_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_);
lean_dec(v___y_5381_);
lean_dec_ref(v___y_5380_);
lean_dec(v___y_5379_);
lean_dec_ref(v___y_5378_);
return v_res_5385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5386_, lean_object* v_name_5387_, lean_object* v_type_5388_, lean_object* v_k_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_){
_start:
{
lean_object* v___x_5395_; 
v___x_5395_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5387_, v_type_5388_, v_k_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5396_, lean_object* v_name_5397_, lean_object* v_type_5398_, lean_object* v_k_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_, lean_object* v___y_5402_, lean_object* v___y_5403_, lean_object* v___y_5404_){
_start:
{
lean_object* v_res_5405_; 
v_res_5405_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5396_, v_name_5397_, v_type_5398_, v_k_5399_, v___y_5400_, v___y_5401_, v___y_5402_, v___y_5403_);
lean_dec(v___y_5403_);
lean_dec_ref(v___y_5402_);
lean_dec(v___y_5401_);
lean_dec_ref(v___y_5400_);
return v_res_5405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5411_, lean_object* v_e_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_){
_start:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5421_; lean_object* v___x_5422_; lean_object* v___x_5423_; lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v___x_5426_; lean_object* v___x_5427_; lean_object* v___x_5428_; 
v___x_5418_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5419_, 0, v_monad_5411_);
v___x_5420_ = lean_box(0);
v___x_5421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5421_, 0, v_e_5412_);
v___x_5422_ = lean_unsigned_to_nat(4u);
v___x_5423_ = lean_mk_empty_array_with_capacity(v___x_5422_);
v___x_5424_ = lean_array_push(v___x_5423_, v___x_5419_);
v___x_5425_ = lean_array_push(v___x_5424_, v___x_5420_);
v___x_5426_ = lean_array_push(v___x_5425_, v___x_5420_);
v___x_5427_ = lean_array_push(v___x_5426_, v___x_5421_);
v___x_5428_ = l_Lean_Meta_mkAppOptM(v___x_5418_, v___x_5427_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_);
return v___x_5428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5429_, lean_object* v_e_5430_, lean_object* v_a_5431_, lean_object* v_a_5432_, lean_object* v_a_5433_, lean_object* v_a_5434_, lean_object* v_a_5435_){
_start:
{
lean_object* v_res_5436_; 
v_res_5436_ = l_Lean_Meta_mkPure(v_monad_5429_, v_e_5430_, v_a_5431_, v_a_5432_, v_a_5433_, v_a_5434_);
lean_dec(v_a_5434_);
lean_dec_ref(v_a_5433_);
lean_dec(v_a_5432_);
lean_dec_ref(v_a_5431_);
return v_res_5436_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5446_; lean_object* v___x_5447_; 
v___x_5446_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5447_ = l_Lean_MessageData_ofFormat(v___x_5446_);
return v___x_5447_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5451_; lean_object* v___x_5452_; 
v___x_5451_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5452_ = l_Lean_MessageData_ofFormat(v___x_5451_);
return v___x_5452_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5456_; lean_object* v___x_5457_; 
v___x_5456_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5457_ = l_Lean_MessageData_ofFormat(v___x_5456_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5458_, lean_object* v_fieldName_5459_, lean_object* v_a_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_){
_start:
{
lean_object* v___x_5465_; 
lean_inc(v_a_5463_);
lean_inc_ref(v_a_5462_);
lean_inc(v_a_5461_);
lean_inc_ref(v_a_5460_);
lean_inc_ref(v_s_5458_);
v___x_5465_ = lean_infer_type(v_s_5458_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
if (lean_obj_tag(v___x_5465_) == 0)
{
lean_object* v_a_5466_; lean_object* v___x_5468_; uint8_t v_isShared_5469_; uint8_t v_isSharedCheck_5562_; 
v_a_5466_ = lean_ctor_get(v___x_5465_, 0);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5465_);
if (v_isSharedCheck_5562_ == 0)
{
v___x_5468_ = v___x_5465_;
v_isShared_5469_ = v_isSharedCheck_5562_;
goto v_resetjp_5467_;
}
else
{
lean_inc(v_a_5466_);
lean_dec(v___x_5465_);
v___x_5468_ = lean_box(0);
v_isShared_5469_ = v_isSharedCheck_5562_;
goto v_resetjp_5467_;
}
v_resetjp_5467_:
{
lean_object* v___x_5470_; 
lean_inc(v_a_5463_);
lean_inc_ref(v_a_5462_);
lean_inc(v_a_5461_);
lean_inc_ref(v_a_5460_);
v___x_5470_ = lean_whnf(v_a_5466_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
if (lean_obj_tag(v___x_5470_) == 0)
{
lean_object* v_a_5471_; lean_object* v___x_5473_; uint8_t v_isShared_5474_; uint8_t v_isSharedCheck_5561_; 
v_a_5471_ = lean_ctor_get(v___x_5470_, 0);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5561_ == 0)
{
v___x_5473_ = v___x_5470_;
v_isShared_5474_ = v_isSharedCheck_5561_;
goto v_resetjp_5472_;
}
else
{
lean_inc(v_a_5471_);
lean_dec(v___x_5470_);
v___x_5473_ = lean_box(0);
v_isShared_5474_ = v_isSharedCheck_5561_;
goto v_resetjp_5472_;
}
v_resetjp_5472_:
{
lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5479_; lean_object* v___x_5494_; 
v___x_5494_ = l_Lean_Expr_getAppFn(v_a_5471_);
if (lean_obj_tag(v___x_5494_) == 4)
{
lean_object* v_declName_5495_; lean_object* v_us_5496_; lean_object* v___x_5497_; lean_object* v_env_5498_; lean_object* v___y_5500_; lean_object* v___y_5501_; lean_object* v___y_5502_; lean_object* v___y_5503_; uint8_t v___x_5542_; 
v_declName_5495_ = lean_ctor_get(v___x_5494_, 0);
lean_inc_n(v_declName_5495_, 2);
v_us_5496_ = lean_ctor_get(v___x_5494_, 1);
lean_inc(v_us_5496_);
lean_dec_ref_known(v___x_5494_, 2);
v___x_5497_ = lean_st_ref_get(v_a_5463_);
v_env_5498_ = lean_ctor_get(v___x_5497_, 0);
lean_inc_ref_n(v_env_5498_, 2);
lean_dec(v___x_5497_);
v___x_5542_ = l_Lean_isStructure(v_env_5498_, v_declName_5495_);
if (v___x_5542_ == 0)
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5546_; lean_object* v___x_5547_; 
v___x_5543_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5544_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5471_);
lean_inc_ref(v_s_5458_);
v___x_5545_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5458_, v_a_5471_);
v___x_5546_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5546_, 0, v___x_5544_);
lean_ctor_set(v___x_5546_, 1, v___x_5545_);
v___x_5547_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5543_, v___x_5546_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
if (lean_obj_tag(v___x_5547_) == 0)
{
lean_dec_ref_known(v___x_5547_, 1);
v___y_5500_ = v_a_5460_;
v___y_5501_ = v_a_5461_;
v___y_5502_ = v_a_5462_;
v___y_5503_ = v_a_5463_;
goto v___jp_5499_;
}
else
{
lean_object* v_a_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5555_; 
lean_dec_ref(v_env_5498_);
lean_dec(v_us_5496_);
lean_dec(v_declName_5495_);
lean_del_object(v___x_5473_);
lean_dec(v_a_5471_);
lean_del_object(v___x_5468_);
lean_dec(v_fieldName_5459_);
lean_dec_ref(v_s_5458_);
v_a_5548_ = lean_ctor_get(v___x_5547_, 0);
v_isSharedCheck_5555_ = !lean_is_exclusive(v___x_5547_);
if (v_isSharedCheck_5555_ == 0)
{
v___x_5550_ = v___x_5547_;
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_a_5548_);
lean_dec(v___x_5547_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5555_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5553_; 
if (v_isShared_5551_ == 0)
{
v___x_5553_ = v___x_5550_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5554_; 
v_reuseFailAlloc_5554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5554_, 0, v_a_5548_);
v___x_5553_ = v_reuseFailAlloc_5554_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
return v___x_5553_;
}
}
}
}
else
{
v___y_5500_ = v_a_5460_;
v___y_5501_ = v_a_5461_;
v___y_5502_ = v_a_5462_;
v___y_5503_ = v_a_5463_;
goto v___jp_5499_;
}
v___jp_5499_:
{
lean_object* v___x_5504_; 
lean_inc(v_fieldName_5459_);
lean_inc(v_declName_5495_);
lean_inc_ref(v_env_5498_);
v___x_5504_ = l_Lean_getProjFnForField_x3f(v_env_5498_, v_declName_5495_, v_fieldName_5459_);
if (lean_obj_tag(v___x_5504_) == 0)
{
lean_object* v___x_5505_; lean_object* v___x_5506_; size_t v_sz_5507_; size_t v___x_5508_; lean_object* v___x_5509_; 
lean_dec(v_us_5496_);
lean_del_object(v___x_5473_);
lean_inc(v_declName_5495_);
lean_inc_ref(v_env_5498_);
v___x_5505_ = l_Lean_getStructureFields(v_env_5498_, v_declName_5495_);
v___x_5506_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5507_ = lean_array_size(v___x_5505_);
v___x_5508_ = ((size_t)0ULL);
lean_inc(v_fieldName_5459_);
lean_inc_ref(v_s_5458_);
v___x_5509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5498_, v_declName_5495_, v_s_5458_, v_fieldName_5459_, v___x_5505_, v_sz_5507_, v___x_5508_, v___x_5506_, v___y_5500_, v___y_5501_, v___y_5502_, v___y_5503_);
lean_dec_ref(v___x_5505_);
if (lean_obj_tag(v___x_5509_) == 0)
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5520_; 
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5520_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5520_ == 0)
{
v___x_5512_ = v___x_5509_;
v_isShared_5513_ = v_isSharedCheck_5520_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5509_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5520_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v_fst_5514_; 
v_fst_5514_ = lean_ctor_get(v_a_5510_, 0);
lean_inc(v_fst_5514_);
lean_dec(v_a_5510_);
if (lean_obj_tag(v_fst_5514_) == 0)
{
lean_del_object(v___x_5512_);
v___y_5476_ = v___y_5500_;
v___y_5477_ = v___y_5502_;
v___y_5478_ = v___y_5503_;
v___y_5479_ = v___y_5501_;
goto v___jp_5475_;
}
else
{
lean_object* v_val_5515_; 
v_val_5515_ = lean_ctor_get(v_fst_5514_, 0);
lean_inc(v_val_5515_);
lean_dec_ref_known(v_fst_5514_, 1);
if (lean_obj_tag(v_val_5515_) == 0)
{
lean_del_object(v___x_5512_);
v___y_5476_ = v___y_5500_;
v___y_5477_ = v___y_5502_;
v___y_5478_ = v___y_5503_;
v___y_5479_ = v___y_5501_;
goto v___jp_5475_;
}
else
{
lean_object* v_val_5516_; lean_object* v___x_5518_; 
lean_dec(v_a_5471_);
lean_del_object(v___x_5468_);
lean_dec(v_fieldName_5459_);
lean_dec_ref(v_s_5458_);
v_val_5516_ = lean_ctor_get(v_val_5515_, 0);
lean_inc(v_val_5516_);
lean_dec_ref_known(v_val_5515_, 1);
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 0, v_val_5516_);
v___x_5518_ = v___x_5512_;
goto v_reusejp_5517_;
}
else
{
lean_object* v_reuseFailAlloc_5519_; 
v_reuseFailAlloc_5519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_val_5516_);
v___x_5518_ = v_reuseFailAlloc_5519_;
goto v_reusejp_5517_;
}
v_reusejp_5517_:
{
return v___x_5518_;
}
}
}
}
}
else
{
lean_object* v_a_5521_; lean_object* v___x_5523_; uint8_t v_isShared_5524_; uint8_t v_isSharedCheck_5528_; 
lean_dec(v_a_5471_);
lean_del_object(v___x_5468_);
lean_dec(v_fieldName_5459_);
lean_dec_ref(v_s_5458_);
v_a_5521_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5528_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5528_ == 0)
{
v___x_5523_ = v___x_5509_;
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
else
{
lean_inc(v_a_5521_);
lean_dec(v___x_5509_);
v___x_5523_ = lean_box(0);
v_isShared_5524_ = v_isSharedCheck_5528_;
goto v_resetjp_5522_;
}
v_resetjp_5522_:
{
lean_object* v___x_5526_; 
if (v_isShared_5524_ == 0)
{
v___x_5526_ = v___x_5523_;
goto v_reusejp_5525_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
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
lean_object* v_val_5529_; lean_object* v_dummy_5530_; lean_object* v_nargs_5531_; lean_object* v___x_5532_; lean_object* v___x_5533_; lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; lean_object* v___x_5540_; 
lean_dec_ref(v_env_5498_);
lean_dec(v_declName_5495_);
lean_del_object(v___x_5468_);
lean_dec(v_fieldName_5459_);
v_val_5529_ = lean_ctor_get(v___x_5504_, 0);
lean_inc(v_val_5529_);
lean_dec_ref_known(v___x_5504_, 1);
v_dummy_5530_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5531_ = l_Lean_Expr_getAppNumArgs(v_a_5471_);
lean_inc(v_nargs_5531_);
v___x_5532_ = lean_mk_array(v_nargs_5531_, v_dummy_5530_);
v___x_5533_ = lean_unsigned_to_nat(1u);
v___x_5534_ = lean_nat_sub(v_nargs_5531_, v___x_5533_);
lean_dec(v_nargs_5531_);
v___x_5535_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5471_, v___x_5532_, v___x_5534_);
v___x_5536_ = l_Lean_mkConst(v_val_5529_, v_us_5496_);
v___x_5537_ = l_Lean_mkAppN(v___x_5536_, v___x_5535_);
lean_dec_ref(v___x_5535_);
v___x_5538_ = l_Lean_Expr_app___override(v___x_5537_, v_s_5458_);
if (v_isShared_5474_ == 0)
{
lean_ctor_set(v___x_5473_, 0, v___x_5538_);
v___x_5540_ = v___x_5473_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5541_; 
v_reuseFailAlloc_5541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5541_, 0, v___x_5538_);
v___x_5540_ = v_reuseFailAlloc_5541_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
return v___x_5540_;
}
}
}
}
else
{
lean_object* v___x_5556_; lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; 
lean_dec_ref(v___x_5494_);
lean_del_object(v___x_5473_);
lean_del_object(v___x_5468_);
lean_dec(v_fieldName_5459_);
v___x_5556_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5557_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5558_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5458_, v_a_5471_);
v___x_5559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5559_, 0, v___x_5557_);
lean_ctor_set(v___x_5559_, 1, v___x_5558_);
v___x_5560_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5556_, v___x_5559_, v_a_5460_, v_a_5461_, v_a_5462_, v_a_5463_);
return v___x_5560_;
}
v___jp_5475_:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; uint8_t v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5485_; 
v___x_5480_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5481_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5482_ = 1;
v___x_5483_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5459_, v___x_5482_);
if (v_isShared_5469_ == 0)
{
lean_ctor_set_tag(v___x_5468_, 3);
lean_ctor_set(v___x_5468_, 0, v___x_5483_);
v___x_5485_ = v___x_5468_;
goto v_reusejp_5484_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5483_);
v___x_5485_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5484_;
}
v_reusejp_5484_:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5486_ = l_Lean_MessageData_ofFormat(v___x_5485_);
v___x_5487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5487_, 0, v___x_5481_);
lean_ctor_set(v___x_5487_, 1, v___x_5486_);
v___x_5488_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5487_);
lean_ctor_set(v___x_5489_, 1, v___x_5488_);
v___x_5490_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5458_, v_a_5471_);
v___x_5491_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5491_, 0, v___x_5489_);
lean_ctor_set(v___x_5491_, 1, v___x_5490_);
v___x_5492_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5480_, v___x_5491_, v___y_5476_, v___y_5479_, v___y_5477_, v___y_5478_);
return v___x_5492_;
}
}
}
}
else
{
lean_del_object(v___x_5468_);
lean_dec(v_fieldName_5459_);
lean_dec_ref(v_s_5458_);
return v___x_5470_;
}
}
}
else
{
lean_dec(v_fieldName_5459_);
lean_dec_ref(v_s_5458_);
return v___x_5465_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5563_, lean_object* v_declName_5564_, lean_object* v_s_5565_, lean_object* v_fieldName_5566_, lean_object* v_as_5567_, size_t v_sz_5568_, size_t v_i_5569_, lean_object* v_b_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_, lean_object* v___y_5574_){
_start:
{
lean_object* v_a_5577_; uint8_t v___x_5581_; 
v___x_5581_ = lean_usize_dec_lt(v_i_5569_, v_sz_5568_);
if (v___x_5581_ == 0)
{
lean_object* v___x_5582_; 
lean_dec(v_fieldName_5566_);
lean_dec_ref(v_s_5565_);
lean_dec(v_declName_5564_);
lean_dec_ref(v___x_5563_);
v___x_5582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5582_, 0, v_b_5570_);
return v___x_5582_;
}
else
{
lean_object* v___x_5583_; lean_object* v___x_5584_; lean_object* v_a_5585_; lean_object* v___x_5586_; 
lean_dec_ref(v_b_5570_);
v___x_5583_ = lean_box(0);
v___x_5584_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5585_ = lean_array_uget_borrowed(v_as_5567_, v_i_5569_);
lean_inc(v_a_5585_);
lean_inc(v_declName_5564_);
lean_inc_ref(v___x_5563_);
v___x_5586_ = l_Lean_isSubobjectField_x3f(v___x_5563_, v_declName_5564_, v_a_5585_);
if (lean_obj_tag(v___x_5586_) == 0)
{
v_a_5577_ = v___x_5584_;
goto v___jp_5576_;
}
else
{
lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5645_; 
v_isSharedCheck_5645_ = !lean_is_exclusive(v___x_5586_);
if (v_isSharedCheck_5645_ == 0)
{
lean_object* v_unused_5646_; 
v_unused_5646_ = lean_ctor_get(v___x_5586_, 0);
lean_dec(v_unused_5646_);
v___x_5588_ = v___x_5586_;
v_isShared_5589_ = v_isSharedCheck_5645_;
goto v_resetjp_5587_;
}
else
{
lean_dec(v___x_5586_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5645_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5590_; 
lean_inc(v_a_5585_);
lean_inc_ref(v_s_5565_);
v___x_5590_ = l_Lean_Meta_mkProjection(v_s_5565_, v_a_5585_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
if (lean_obj_tag(v___x_5590_) == 0)
{
lean_object* v_a_5591_; lean_object* v___x_5592_; 
v_a_5591_ = lean_ctor_get(v___x_5590_, 0);
lean_inc(v_a_5591_);
lean_dec_ref_known(v___x_5590_, 1);
v___x_5592_ = l_Lean_Meta_saveState___redArg(v___y_5572_, v___y_5574_);
if (lean_obj_tag(v___x_5592_) == 0)
{
lean_object* v_a_5593_; lean_object* v___x_5594_; 
v_a_5593_ = lean_ctor_get(v___x_5592_, 0);
lean_inc(v_a_5593_);
lean_dec_ref_known(v___x_5592_, 1);
lean_inc(v_fieldName_5566_);
v___x_5594_ = l_Lean_Meta_mkProjection(v_a_5591_, v_fieldName_5566_, v___y_5571_, v___y_5572_, v___y_5573_, v___y_5574_);
if (lean_obj_tag(v___x_5594_) == 0)
{
lean_object* v_a_5595_; lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5607_; 
lean_dec(v_a_5593_);
lean_dec(v_fieldName_5566_);
lean_dec_ref(v_s_5565_);
lean_dec(v_declName_5564_);
lean_dec_ref(v___x_5563_);
v_a_5595_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5597_ = v___x_5594_;
v_isShared_5598_ = v_isSharedCheck_5607_;
goto v_resetjp_5596_;
}
else
{
lean_inc(v_a_5595_);
lean_dec(v___x_5594_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5607_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v___x_5600_; 
if (v_isShared_5589_ == 0)
{
lean_ctor_set(v___x_5588_, 0, v_a_5595_);
v___x_5600_ = v___x_5588_;
goto v_reusejp_5599_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5595_);
v___x_5600_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5599_;
}
v_reusejp_5599_:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5601_, 0, v___x_5600_);
v___x_5602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5602_, 0, v___x_5601_);
lean_ctor_set(v___x_5602_, 1, v___x_5583_);
if (v_isShared_5598_ == 0)
{
lean_ctor_set(v___x_5597_, 0, v___x_5602_);
v___x_5604_ = v___x_5597_;
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
lean_object* v_a_5608_; lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5628_; 
lean_del_object(v___x_5588_);
v_a_5608_ = lean_ctor_get(v___x_5594_, 0);
v_isSharedCheck_5628_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5628_ == 0)
{
v___x_5610_ = v___x_5594_;
v_isShared_5611_ = v_isSharedCheck_5628_;
goto v_resetjp_5609_;
}
else
{
lean_inc(v_a_5608_);
lean_dec(v___x_5594_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5628_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
uint8_t v___y_5613_; uint8_t v___x_5626_; 
v___x_5626_ = l_Lean_Exception_isInterrupt(v_a_5608_);
if (v___x_5626_ == 0)
{
uint8_t v___x_5627_; 
lean_inc(v_a_5608_);
v___x_5627_ = l_Lean_Exception_isRuntime(v_a_5608_);
v___y_5613_ = v___x_5627_;
goto v___jp_5612_;
}
else
{
v___y_5613_ = v___x_5626_;
goto v___jp_5612_;
}
v___jp_5612_:
{
if (v___y_5613_ == 0)
{
lean_object* v___x_5614_; 
lean_del_object(v___x_5610_);
lean_dec(v_a_5608_);
v___x_5614_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5593_, v___y_5572_, v___y_5574_);
lean_dec(v_a_5593_);
if (lean_obj_tag(v___x_5614_) == 0)
{
lean_dec_ref_known(v___x_5614_, 1);
v_a_5577_ = v___x_5584_;
goto v___jp_5576_;
}
else
{
lean_object* v_a_5615_; lean_object* v___x_5617_; uint8_t v_isShared_5618_; uint8_t v_isSharedCheck_5622_; 
lean_dec(v_fieldName_5566_);
lean_dec_ref(v_s_5565_);
lean_dec(v_declName_5564_);
lean_dec_ref(v___x_5563_);
v_a_5615_ = lean_ctor_get(v___x_5614_, 0);
v_isSharedCheck_5622_ = !lean_is_exclusive(v___x_5614_);
if (v_isSharedCheck_5622_ == 0)
{
v___x_5617_ = v___x_5614_;
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
else
{
lean_inc(v_a_5615_);
lean_dec(v___x_5614_);
v___x_5617_ = lean_box(0);
v_isShared_5618_ = v_isSharedCheck_5622_;
goto v_resetjp_5616_;
}
v_resetjp_5616_:
{
lean_object* v___x_5620_; 
if (v_isShared_5618_ == 0)
{
v___x_5620_ = v___x_5617_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
}
}
else
{
lean_object* v___x_5624_; 
lean_dec(v_a_5593_);
lean_dec(v_fieldName_5566_);
lean_dec_ref(v_s_5565_);
lean_dec(v_declName_5564_);
lean_dec_ref(v___x_5563_);
if (v_isShared_5611_ == 0)
{
v___x_5624_ = v___x_5610_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5625_; 
v_reuseFailAlloc_5625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5625_, 0, v_a_5608_);
v___x_5624_ = v_reuseFailAlloc_5625_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
return v___x_5624_;
}
}
}
}
}
}
else
{
lean_object* v_a_5629_; lean_object* v___x_5631_; uint8_t v_isShared_5632_; uint8_t v_isSharedCheck_5636_; 
lean_dec(v_a_5591_);
lean_del_object(v___x_5588_);
lean_dec(v_fieldName_5566_);
lean_dec_ref(v_s_5565_);
lean_dec(v_declName_5564_);
lean_dec_ref(v___x_5563_);
v_a_5629_ = lean_ctor_get(v___x_5592_, 0);
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5636_ == 0)
{
v___x_5631_ = v___x_5592_;
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
else
{
lean_inc(v_a_5629_);
lean_dec(v___x_5592_);
v___x_5631_ = lean_box(0);
v_isShared_5632_ = v_isSharedCheck_5636_;
goto v_resetjp_5630_;
}
v_resetjp_5630_:
{
lean_object* v___x_5634_; 
if (v_isShared_5632_ == 0)
{
v___x_5634_ = v___x_5631_;
goto v_reusejp_5633_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_a_5629_);
v___x_5634_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5633_;
}
v_reusejp_5633_:
{
return v___x_5634_;
}
}
}
}
else
{
lean_object* v_a_5637_; lean_object* v___x_5639_; uint8_t v_isShared_5640_; uint8_t v_isSharedCheck_5644_; 
lean_del_object(v___x_5588_);
lean_dec(v_fieldName_5566_);
lean_dec_ref(v_s_5565_);
lean_dec(v_declName_5564_);
lean_dec_ref(v___x_5563_);
v_a_5637_ = lean_ctor_get(v___x_5590_, 0);
v_isSharedCheck_5644_ = !lean_is_exclusive(v___x_5590_);
if (v_isSharedCheck_5644_ == 0)
{
v___x_5639_ = v___x_5590_;
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
else
{
lean_inc(v_a_5637_);
lean_dec(v___x_5590_);
v___x_5639_ = lean_box(0);
v_isShared_5640_ = v_isSharedCheck_5644_;
goto v_resetjp_5638_;
}
v_resetjp_5638_:
{
lean_object* v___x_5642_; 
if (v_isShared_5640_ == 0)
{
v___x_5642_ = v___x_5639_;
goto v_reusejp_5641_;
}
else
{
lean_object* v_reuseFailAlloc_5643_; 
v_reuseFailAlloc_5643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5643_, 0, v_a_5637_);
v___x_5642_ = v_reuseFailAlloc_5643_;
goto v_reusejp_5641_;
}
v_reusejp_5641_:
{
return v___x_5642_;
}
}
}
}
}
}
v___jp_5576_:
{
size_t v___x_5578_; size_t v___x_5579_; 
v___x_5578_ = ((size_t)1ULL);
v___x_5579_ = lean_usize_add(v_i_5569_, v___x_5578_);
lean_inc_ref(v_a_5577_);
v_i_5569_ = v___x_5579_;
v_b_5570_ = v_a_5577_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5647_, lean_object* v_declName_5648_, lean_object* v_s_5649_, lean_object* v_fieldName_5650_, lean_object* v_as_5651_, lean_object* v_sz_5652_, lean_object* v_i_5653_, lean_object* v_b_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_){
_start:
{
size_t v_sz_boxed_5660_; size_t v_i_boxed_5661_; lean_object* v_res_5662_; 
v_sz_boxed_5660_ = lean_unbox_usize(v_sz_5652_);
lean_dec(v_sz_5652_);
v_i_boxed_5661_ = lean_unbox_usize(v_i_5653_);
lean_dec(v_i_5653_);
v_res_5662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5647_, v_declName_5648_, v_s_5649_, v_fieldName_5650_, v_as_5651_, v_sz_boxed_5660_, v_i_boxed_5661_, v_b_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
lean_dec_ref(v_as_5651_);
return v_res_5662_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5663_, lean_object* v_fieldName_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_, lean_object* v_a_5668_, lean_object* v_a_5669_){
_start:
{
lean_object* v_res_5670_; 
v_res_5670_ = l_Lean_Meta_mkProjection(v_s_5663_, v_fieldName_5664_, v_a_5665_, v_a_5666_, v_a_5667_, v_a_5668_);
lean_dec(v_a_5668_);
lean_dec_ref(v_a_5667_);
lean_dec(v_a_5666_);
lean_dec_ref(v_a_5665_);
return v_res_5670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5671_, lean_object* v_cons_5672_, lean_object* v_x_5673_){
_start:
{
if (lean_obj_tag(v_x_5673_) == 0)
{
lean_dec_ref(v_cons_5672_);
lean_inc_ref(v_nil_5671_);
return v_nil_5671_;
}
else
{
lean_object* v_head_5674_; lean_object* v_tail_5675_; lean_object* v___x_5676_; lean_object* v___x_5677_; lean_object* v___x_5678_; 
v_head_5674_ = lean_ctor_get(v_x_5673_, 0);
lean_inc(v_head_5674_);
v_tail_5675_ = lean_ctor_get(v_x_5673_, 1);
lean_inc(v_tail_5675_);
lean_dec_ref_known(v_x_5673_, 2);
lean_inc_ref(v_cons_5672_);
v___x_5676_ = l_Lean_Expr_app___override(v_cons_5672_, v_head_5674_);
v___x_5677_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5671_, v_cons_5672_, v_tail_5675_);
v___x_5678_ = l_Lean_Expr_app___override(v___x_5676_, v___x_5677_);
return v___x_5678_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5679_, lean_object* v_cons_5680_, lean_object* v_x_5681_){
_start:
{
lean_object* v_res_5682_; 
v_res_5682_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5679_, v_cons_5680_, v_x_5681_);
lean_dec_ref(v_nil_5679_);
return v_res_5682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5692_, lean_object* v_xs_5693_, lean_object* v_a_5694_, lean_object* v_a_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_){
_start:
{
lean_object* v___x_5699_; 
lean_inc_ref(v_type_5692_);
v___x_5699_ = l_Lean_Meta_getDecLevel(v_type_5692_, v_a_5694_, v_a_5695_, v_a_5696_, v_a_5697_);
if (lean_obj_tag(v___x_5699_) == 0)
{
lean_object* v_a_5700_; lean_object* v___x_5702_; uint8_t v_isShared_5703_; uint8_t v_isSharedCheck_5719_; 
v_a_5700_ = lean_ctor_get(v___x_5699_, 0);
v_isSharedCheck_5719_ = !lean_is_exclusive(v___x_5699_);
if (v_isSharedCheck_5719_ == 0)
{
v___x_5702_ = v___x_5699_;
v_isShared_5703_ = v_isSharedCheck_5719_;
goto v_resetjp_5701_;
}
else
{
lean_inc(v_a_5700_);
lean_dec(v___x_5699_);
v___x_5702_ = lean_box(0);
v_isShared_5703_ = v_isSharedCheck_5719_;
goto v_resetjp_5701_;
}
v_resetjp_5701_:
{
lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5707_; lean_object* v___x_5708_; 
v___x_5704_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5705_ = lean_box(0);
v___x_5706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5706_, 0, v_a_5700_);
lean_ctor_set(v___x_5706_, 1, v___x_5705_);
lean_inc_ref(v___x_5706_);
v___x_5707_ = l_Lean_mkConst(v___x_5704_, v___x_5706_);
lean_inc_ref(v_type_5692_);
v___x_5708_ = l_Lean_Expr_app___override(v___x_5707_, v_type_5692_);
if (lean_obj_tag(v_xs_5693_) == 0)
{
lean_object* v___x_5710_; 
lean_dec_ref_known(v___x_5706_, 2);
lean_dec_ref(v_type_5692_);
if (v_isShared_5703_ == 0)
{
lean_ctor_set(v___x_5702_, 0, v___x_5708_);
v___x_5710_ = v___x_5702_;
goto v_reusejp_5709_;
}
else
{
lean_object* v_reuseFailAlloc_5711_; 
v_reuseFailAlloc_5711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5711_, 0, v___x_5708_);
v___x_5710_ = v_reuseFailAlloc_5711_;
goto v_reusejp_5709_;
}
v_reusejp_5709_:
{
return v___x_5710_;
}
}
else
{
lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; lean_object* v___x_5717_; 
v___x_5712_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5713_ = l_Lean_mkConst(v___x_5712_, v___x_5706_);
v___x_5714_ = l_Lean_Expr_app___override(v___x_5713_, v_type_5692_);
v___x_5715_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5708_, v___x_5714_, v_xs_5693_);
lean_dec_ref(v___x_5708_);
if (v_isShared_5703_ == 0)
{
lean_ctor_set(v___x_5702_, 0, v___x_5715_);
v___x_5717_ = v___x_5702_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v___x_5715_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
}
}
else
{
lean_object* v_a_5720_; lean_object* v___x_5722_; uint8_t v_isShared_5723_; uint8_t v_isSharedCheck_5727_; 
lean_dec(v_xs_5693_);
lean_dec_ref(v_type_5692_);
v_a_5720_ = lean_ctor_get(v___x_5699_, 0);
v_isSharedCheck_5727_ = !lean_is_exclusive(v___x_5699_);
if (v_isSharedCheck_5727_ == 0)
{
v___x_5722_ = v___x_5699_;
v_isShared_5723_ = v_isSharedCheck_5727_;
goto v_resetjp_5721_;
}
else
{
lean_inc(v_a_5720_);
lean_dec(v___x_5699_);
v___x_5722_ = lean_box(0);
v_isShared_5723_ = v_isSharedCheck_5727_;
goto v_resetjp_5721_;
}
v_resetjp_5721_:
{
lean_object* v___x_5725_; 
if (v_isShared_5723_ == 0)
{
v___x_5725_ = v___x_5722_;
goto v_reusejp_5724_;
}
else
{
lean_object* v_reuseFailAlloc_5726_; 
v_reuseFailAlloc_5726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_a_5720_);
v___x_5725_ = v_reuseFailAlloc_5726_;
goto v_reusejp_5724_;
}
v_reusejp_5724_:
{
return v___x_5725_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5728_, lean_object* v_xs_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_, lean_object* v_a_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_){
_start:
{
lean_object* v_res_5735_; 
v_res_5735_ = l_Lean_Meta_mkListLit(v_type_5728_, v_xs_5729_, v_a_5730_, v_a_5731_, v_a_5732_, v_a_5733_);
lean_dec(v_a_5733_);
lean_dec_ref(v_a_5732_);
lean_dec(v_a_5731_);
lean_dec_ref(v_a_5730_);
return v_res_5735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5740_, lean_object* v_xs_5741_, lean_object* v_a_5742_, lean_object* v_a_5743_, lean_object* v_a_5744_, lean_object* v_a_5745_){
_start:
{
lean_object* v___x_5747_; 
lean_inc_ref(v_type_5740_);
v___x_5747_ = l_Lean_Meta_getDecLevel(v_type_5740_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v_a_5748_; lean_object* v___x_5749_; 
v_a_5748_ = lean_ctor_get(v___x_5747_, 0);
lean_inc(v_a_5748_);
lean_dec_ref_known(v___x_5747_, 1);
lean_inc_ref(v_type_5740_);
v___x_5749_ = l_Lean_Meta_mkListLit(v_type_5740_, v_xs_5741_, v_a_5742_, v_a_5743_, v_a_5744_, v_a_5745_);
if (lean_obj_tag(v___x_5749_) == 0)
{
lean_object* v_a_5750_; lean_object* v___x_5752_; uint8_t v_isShared_5753_; uint8_t v_isSharedCheck_5763_; 
v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
v_isSharedCheck_5763_ = !lean_is_exclusive(v___x_5749_);
if (v_isSharedCheck_5763_ == 0)
{
v___x_5752_ = v___x_5749_;
v_isShared_5753_ = v_isSharedCheck_5763_;
goto v_resetjp_5751_;
}
else
{
lean_inc(v_a_5750_);
lean_dec(v___x_5749_);
v___x_5752_ = lean_box(0);
v_isShared_5753_ = v_isSharedCheck_5763_;
goto v_resetjp_5751_;
}
v_resetjp_5751_:
{
lean_object* v___x_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; lean_object* v___x_5761_; 
v___x_5754_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5755_ = lean_box(0);
v___x_5756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5756_, 0, v_a_5748_);
lean_ctor_set(v___x_5756_, 1, v___x_5755_);
v___x_5757_ = l_Lean_mkConst(v___x_5754_, v___x_5756_);
v___x_5758_ = l_Lean_Expr_app___override(v___x_5757_, v_type_5740_);
v___x_5759_ = l_Lean_Expr_app___override(v___x_5758_, v_a_5750_);
if (v_isShared_5753_ == 0)
{
lean_ctor_set(v___x_5752_, 0, v___x_5759_);
v___x_5761_ = v___x_5752_;
goto v_reusejp_5760_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v___x_5759_);
v___x_5761_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5760_;
}
v_reusejp_5760_:
{
return v___x_5761_;
}
}
}
else
{
lean_dec(v_a_5748_);
lean_dec_ref(v_type_5740_);
return v___x_5749_;
}
}
else
{
lean_object* v_a_5764_; lean_object* v___x_5766_; uint8_t v_isShared_5767_; uint8_t v_isSharedCheck_5771_; 
lean_dec(v_xs_5741_);
lean_dec_ref(v_type_5740_);
v_a_5764_ = lean_ctor_get(v___x_5747_, 0);
v_isSharedCheck_5771_ = !lean_is_exclusive(v___x_5747_);
if (v_isSharedCheck_5771_ == 0)
{
v___x_5766_ = v___x_5747_;
v_isShared_5767_ = v_isSharedCheck_5771_;
goto v_resetjp_5765_;
}
else
{
lean_inc(v_a_5764_);
lean_dec(v___x_5747_);
v___x_5766_ = lean_box(0);
v_isShared_5767_ = v_isSharedCheck_5771_;
goto v_resetjp_5765_;
}
v_resetjp_5765_:
{
lean_object* v___x_5769_; 
if (v_isShared_5767_ == 0)
{
v___x_5769_ = v___x_5766_;
goto v_reusejp_5768_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_a_5764_);
v___x_5769_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5768_;
}
v_reusejp_5768_:
{
return v___x_5769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5772_, lean_object* v_xs_5773_, lean_object* v_a_5774_, lean_object* v_a_5775_, lean_object* v_a_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_){
_start:
{
lean_object* v_res_5779_; 
v_res_5779_ = l_Lean_Meta_mkArrayLit(v_type_5772_, v_xs_5773_, v_a_5774_, v_a_5775_, v_a_5776_, v_a_5777_);
lean_dec(v_a_5777_);
lean_dec_ref(v_a_5776_);
lean_dec(v_a_5775_);
lean_dec_ref(v_a_5774_);
return v_res_5779_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5785_, lean_object* v_a_5786_, lean_object* v_a_5787_, lean_object* v_a_5788_, lean_object* v_a_5789_){
_start:
{
lean_object* v___x_5791_; 
lean_inc_ref(v_type_5785_);
v___x_5791_ = l_Lean_Meta_getDecLevel(v_type_5785_, v_a_5786_, v_a_5787_, v_a_5788_, v_a_5789_);
if (lean_obj_tag(v___x_5791_) == 0)
{
lean_object* v_a_5792_; lean_object* v___x_5794_; uint8_t v_isShared_5795_; uint8_t v_isSharedCheck_5804_; 
v_a_5792_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5804_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5804_ == 0)
{
v___x_5794_ = v___x_5791_;
v_isShared_5795_ = v_isSharedCheck_5804_;
goto v_resetjp_5793_;
}
else
{
lean_inc(v_a_5792_);
lean_dec(v___x_5791_);
v___x_5794_ = lean_box(0);
v_isShared_5795_ = v_isSharedCheck_5804_;
goto v_resetjp_5793_;
}
v_resetjp_5793_:
{
lean_object* v___x_5796_; lean_object* v___x_5797_; lean_object* v___x_5798_; lean_object* v___x_5799_; lean_object* v___x_5800_; lean_object* v___x_5802_; 
v___x_5796_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5797_ = lean_box(0);
v___x_5798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5798_, 0, v_a_5792_);
lean_ctor_set(v___x_5798_, 1, v___x_5797_);
v___x_5799_ = l_Lean_mkConst(v___x_5796_, v___x_5798_);
v___x_5800_ = l_Lean_Expr_app___override(v___x_5799_, v_type_5785_);
if (v_isShared_5795_ == 0)
{
lean_ctor_set(v___x_5794_, 0, v___x_5800_);
v___x_5802_ = v___x_5794_;
goto v_reusejp_5801_;
}
else
{
lean_object* v_reuseFailAlloc_5803_; 
v_reuseFailAlloc_5803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5803_, 0, v___x_5800_);
v___x_5802_ = v_reuseFailAlloc_5803_;
goto v_reusejp_5801_;
}
v_reusejp_5801_:
{
return v___x_5802_;
}
}
}
else
{
lean_object* v_a_5805_; lean_object* v___x_5807_; uint8_t v_isShared_5808_; uint8_t v_isSharedCheck_5812_; 
lean_dec_ref(v_type_5785_);
v_a_5805_ = lean_ctor_get(v___x_5791_, 0);
v_isSharedCheck_5812_ = !lean_is_exclusive(v___x_5791_);
if (v_isSharedCheck_5812_ == 0)
{
v___x_5807_ = v___x_5791_;
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
else
{
lean_inc(v_a_5805_);
lean_dec(v___x_5791_);
v___x_5807_ = lean_box(0);
v_isShared_5808_ = v_isSharedCheck_5812_;
goto v_resetjp_5806_;
}
v_resetjp_5806_:
{
lean_object* v___x_5810_; 
if (v_isShared_5808_ == 0)
{
v___x_5810_ = v___x_5807_;
goto v_reusejp_5809_;
}
else
{
lean_object* v_reuseFailAlloc_5811_; 
v_reuseFailAlloc_5811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5811_, 0, v_a_5805_);
v___x_5810_ = v_reuseFailAlloc_5811_;
goto v_reusejp_5809_;
}
v_reusejp_5809_:
{
return v___x_5810_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5813_, lean_object* v_a_5814_, lean_object* v_a_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_){
_start:
{
lean_object* v_res_5819_; 
v_res_5819_ = l_Lean_Meta_mkNone(v_type_5813_, v_a_5814_, v_a_5815_, v_a_5816_, v_a_5817_);
lean_dec(v_a_5817_);
lean_dec_ref(v_a_5816_);
lean_dec(v_a_5815_);
lean_dec_ref(v_a_5814_);
return v_res_5819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5824_, lean_object* v_value_5825_, lean_object* v_a_5826_, lean_object* v_a_5827_, lean_object* v_a_5828_, lean_object* v_a_5829_){
_start:
{
lean_object* v___x_5831_; 
lean_inc_ref(v_type_5824_);
v___x_5831_ = l_Lean_Meta_getDecLevel(v_type_5824_, v_a_5826_, v_a_5827_, v_a_5828_, v_a_5829_);
if (lean_obj_tag(v___x_5831_) == 0)
{
lean_object* v_a_5832_; lean_object* v___x_5834_; uint8_t v_isShared_5835_; uint8_t v_isSharedCheck_5844_; 
v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5844_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5844_ == 0)
{
v___x_5834_ = v___x_5831_;
v_isShared_5835_ = v_isSharedCheck_5844_;
goto v_resetjp_5833_;
}
else
{
lean_inc(v_a_5832_);
lean_dec(v___x_5831_);
v___x_5834_ = lean_box(0);
v_isShared_5835_ = v_isSharedCheck_5844_;
goto v_resetjp_5833_;
}
v_resetjp_5833_:
{
lean_object* v___x_5836_; lean_object* v___x_5837_; lean_object* v___x_5838_; lean_object* v___x_5839_; lean_object* v___x_5840_; lean_object* v___x_5842_; 
v___x_5836_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5837_ = lean_box(0);
v___x_5838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5838_, 0, v_a_5832_);
lean_ctor_set(v___x_5838_, 1, v___x_5837_);
v___x_5839_ = l_Lean_mkConst(v___x_5836_, v___x_5838_);
v___x_5840_ = l_Lean_mkAppB(v___x_5839_, v_type_5824_, v_value_5825_);
if (v_isShared_5835_ == 0)
{
lean_ctor_set(v___x_5834_, 0, v___x_5840_);
v___x_5842_ = v___x_5834_;
goto v_reusejp_5841_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v___x_5840_);
v___x_5842_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5841_;
}
v_reusejp_5841_:
{
return v___x_5842_;
}
}
}
else
{
lean_object* v_a_5845_; lean_object* v___x_5847_; uint8_t v_isShared_5848_; uint8_t v_isSharedCheck_5852_; 
lean_dec_ref(v_value_5825_);
lean_dec_ref(v_type_5824_);
v_a_5845_ = lean_ctor_get(v___x_5831_, 0);
v_isSharedCheck_5852_ = !lean_is_exclusive(v___x_5831_);
if (v_isSharedCheck_5852_ == 0)
{
v___x_5847_ = v___x_5831_;
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
else
{
lean_inc(v_a_5845_);
lean_dec(v___x_5831_);
v___x_5847_ = lean_box(0);
v_isShared_5848_ = v_isSharedCheck_5852_;
goto v_resetjp_5846_;
}
v_resetjp_5846_:
{
lean_object* v___x_5850_; 
if (v_isShared_5848_ == 0)
{
v___x_5850_ = v___x_5847_;
goto v_reusejp_5849_;
}
else
{
lean_object* v_reuseFailAlloc_5851_; 
v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5851_, 0, v_a_5845_);
v___x_5850_ = v_reuseFailAlloc_5851_;
goto v_reusejp_5849_;
}
v_reusejp_5849_:
{
return v___x_5850_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5853_, lean_object* v_value_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_){
_start:
{
lean_object* v_res_5860_; 
v_res_5860_ = l_Lean_Meta_mkSome(v_type_5853_, v_value_5854_, v_a_5855_, v_a_5856_, v_a_5857_, v_a_5858_);
lean_dec(v_a_5858_);
lean_dec_ref(v_a_5857_);
lean_dec(v_a_5856_);
lean_dec_ref(v_a_5855_);
return v_res_5860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5866_, lean_object* v_a_5867_, lean_object* v_a_5868_, lean_object* v_a_5869_, lean_object* v_a_5870_){
_start:
{
lean_object* v___x_5872_; lean_object* v___x_5873_; lean_object* v___x_5874_; lean_object* v___x_5875_; lean_object* v___x_5876_; lean_object* v___x_5877_; lean_object* v___x_5878_; lean_object* v___x_5879_; 
v___x_5872_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5873_, 0, v_p_5866_);
v___x_5874_ = lean_box(0);
v___x_5875_ = lean_unsigned_to_nat(2u);
v___x_5876_ = lean_mk_empty_array_with_capacity(v___x_5875_);
v___x_5877_ = lean_array_push(v___x_5876_, v___x_5873_);
v___x_5878_ = lean_array_push(v___x_5877_, v___x_5874_);
v___x_5879_ = l_Lean_Meta_mkAppOptM(v___x_5872_, v___x_5878_, v_a_5867_, v_a_5868_, v_a_5869_, v_a_5870_);
return v___x_5879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5880_, lean_object* v_a_5881_, lean_object* v_a_5882_, lean_object* v_a_5883_, lean_object* v_a_5884_, lean_object* v_a_5885_){
_start:
{
lean_object* v_res_5886_; 
v_res_5886_ = l_Lean_Meta_mkDecide(v_p_5880_, v_a_5881_, v_a_5882_, v_a_5883_, v_a_5884_);
lean_dec(v_a_5884_);
lean_dec_ref(v_a_5883_);
lean_dec(v_a_5882_);
lean_dec_ref(v_a_5881_);
return v_res_5886_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; 
v___x_5892_ = lean_box(0);
v___x_5893_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5894_ = l_Lean_mkConst(v___x_5893_, v___x_5892_);
return v___x_5894_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5898_, lean_object* v_a_5899_, lean_object* v_a_5900_, lean_object* v_a_5901_, lean_object* v_a_5902_){
_start:
{
lean_object* v___x_5904_; 
v___x_5904_ = l_Lean_Meta_mkDecide(v_p_5898_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_);
if (lean_obj_tag(v___x_5904_) == 0)
{
lean_object* v_a_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; 
v_a_5905_ = lean_ctor_get(v___x_5904_, 0);
lean_inc(v_a_5905_);
lean_dec_ref_known(v___x_5904_, 1);
v___x_5906_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5907_ = l_Lean_Meta_mkEq(v_a_5905_, v___x_5906_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_);
if (lean_obj_tag(v___x_5907_) == 0)
{
lean_object* v_a_5908_; lean_object* v___x_5909_; 
v_a_5908_ = lean_ctor_get(v___x_5907_, 0);
lean_inc(v_a_5908_);
lean_dec_ref_known(v___x_5907_, 1);
v___x_5909_ = l_Lean_Meta_mkEqRefl(v___x_5906_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_);
if (lean_obj_tag(v___x_5909_) == 0)
{
lean_object* v_a_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; 
v_a_5910_ = lean_ctor_get(v___x_5909_, 0);
lean_inc(v_a_5910_);
lean_dec_ref_known(v___x_5909_, 1);
v___x_5911_ = l_Lean_Meta_mkExpectedPropHint(v_a_5910_, v_a_5908_);
v___x_5912_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5913_ = lean_unsigned_to_nat(1u);
v___x_5914_ = lean_mk_empty_array_with_capacity(v___x_5913_);
v___x_5915_ = lean_array_push(v___x_5914_, v___x_5911_);
v___x_5916_ = l_Lean_Meta_mkAppM(v___x_5912_, v___x_5915_, v_a_5899_, v_a_5900_, v_a_5901_, v_a_5902_);
return v___x_5916_;
}
else
{
lean_dec(v_a_5908_);
return v___x_5909_;
}
}
else
{
return v___x_5907_;
}
}
else
{
return v___x_5904_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_, lean_object* v_a_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_Lean_Meta_mkDecideProof(v_p_5917_, v_a_5918_, v_a_5919_, v_a_5920_, v_a_5921_);
lean_dec(v_a_5921_);
lean_dec_ref(v_a_5920_);
lean_dec(v_a_5919_);
lean_dec_ref(v_a_5918_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5929_, lean_object* v_b_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_, lean_object* v_a_5933_, lean_object* v_a_5934_){
_start:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5936_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_5937_ = lean_unsigned_to_nat(2u);
v___x_5938_ = lean_mk_empty_array_with_capacity(v___x_5937_);
v___x_5939_ = lean_array_push(v___x_5938_, v_a_5929_);
v___x_5940_ = lean_array_push(v___x_5939_, v_b_5930_);
v___x_5941_ = l_Lean_Meta_mkAppM(v___x_5936_, v___x_5940_, v_a_5931_, v_a_5932_, v_a_5933_, v_a_5934_);
return v___x_5941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_5942_, lean_object* v_b_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_){
_start:
{
lean_object* v_res_5949_; 
v_res_5949_ = l_Lean_Meta_mkLt(v_a_5942_, v_b_5943_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_);
lean_dec(v_a_5947_);
lean_dec_ref(v_a_5946_);
lean_dec(v_a_5945_);
lean_dec_ref(v_a_5944_);
return v_res_5949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_5955_, lean_object* v_b_5956_, lean_object* v_a_5957_, lean_object* v_a_5958_, lean_object* v_a_5959_, lean_object* v_a_5960_){
_start:
{
lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; 
v___x_5962_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_5963_ = lean_unsigned_to_nat(2u);
v___x_5964_ = lean_mk_empty_array_with_capacity(v___x_5963_);
v___x_5965_ = lean_array_push(v___x_5964_, v_a_5955_);
v___x_5966_ = lean_array_push(v___x_5965_, v_b_5956_);
v___x_5967_ = l_Lean_Meta_mkAppM(v___x_5962_, v___x_5966_, v_a_5957_, v_a_5958_, v_a_5959_, v_a_5960_);
return v___x_5967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_5968_, lean_object* v_b_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_){
_start:
{
lean_object* v_res_5975_; 
v_res_5975_ = l_Lean_Meta_mkLe(v_a_5968_, v_b_5969_, v_a_5970_, v_a_5971_, v_a_5972_, v_a_5973_);
lean_dec(v_a_5973_);
lean_dec_ref(v_a_5972_);
lean_dec(v_a_5971_);
lean_dec_ref(v_a_5970_);
return v_res_5975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_, lean_object* v_a_5985_){
_start:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; 
v___x_5987_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_5988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5988_, 0, v_00_u03b1_5981_);
v___x_5989_ = lean_box(0);
v___x_5990_ = lean_unsigned_to_nat(2u);
v___x_5991_ = lean_mk_empty_array_with_capacity(v___x_5990_);
v___x_5992_ = lean_array_push(v___x_5991_, v___x_5988_);
v___x_5993_ = lean_array_push(v___x_5992_, v___x_5989_);
v___x_5994_ = l_Lean_Meta_mkAppOptM(v___x_5987_, v___x_5993_, v_a_5982_, v_a_5983_, v_a_5984_, v_a_5985_);
return v___x_5994_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_5995_, lean_object* v_a_5996_, lean_object* v_a_5997_, lean_object* v_a_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_){
_start:
{
lean_object* v_res_6001_; 
v_res_6001_ = l_Lean_Meta_mkDefault(v_00_u03b1_5995_, v_a_5996_, v_a_5997_, v_a_5998_, v_a_5999_);
lean_dec(v_a_5999_);
lean_dec_ref(v_a_5998_);
lean_dec(v_a_5997_);
lean_dec_ref(v_a_5996_);
return v_res_6001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_, lean_object* v_a_6011_){
_start:
{
lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; 
v___x_6013_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_6014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6014_, 0, v_00_u03b1_6007_);
v___x_6015_ = lean_box(0);
v___x_6016_ = lean_unsigned_to_nat(2u);
v___x_6017_ = lean_mk_empty_array_with_capacity(v___x_6016_);
v___x_6018_ = lean_array_push(v___x_6017_, v___x_6014_);
v___x_6019_ = lean_array_push(v___x_6018_, v___x_6015_);
v___x_6020_ = l_Lean_Meta_mkAppOptM(v___x_6013_, v___x_6019_, v_a_6008_, v_a_6009_, v_a_6010_, v_a_6011_);
return v___x_6020_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6021_, lean_object* v_a_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_){
_start:
{
lean_object* v_res_6027_; 
v_res_6027_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6021_, v_a_6022_, v_a_6023_, v_a_6024_, v_a_6025_);
lean_dec(v_a_6025_);
lean_dec_ref(v_a_6024_);
lean_dec(v_a_6023_);
lean_dec_ref(v_a_6022_);
return v_res_6027_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_){
_start:
{
lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; 
v___x_6037_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6038_ = lean_unsigned_to_nat(1u);
v___x_6039_ = lean_mk_empty_array_with_capacity(v___x_6038_);
v___x_6040_ = lean_array_push(v___x_6039_, v_h_6031_);
v___x_6041_ = l_Lean_Meta_mkAppM(v___x_6037_, v___x_6040_, v_a_6032_, v_a_6033_, v_a_6034_, v_a_6035_);
return v___x_6041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6042_, lean_object* v_a_6043_, lean_object* v_a_6044_, lean_object* v_a_6045_, lean_object* v_a_6046_, lean_object* v_a_6047_){
_start:
{
lean_object* v_res_6048_; 
v_res_6048_ = l_Lean_Meta_mkFunExt(v_h_6042_, v_a_6043_, v_a_6044_, v_a_6045_, v_a_6046_);
lean_dec(v_a_6046_);
lean_dec_ref(v_a_6045_);
lean_dec(v_a_6044_);
lean_dec_ref(v_a_6043_);
return v_res_6048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6052_, lean_object* v_a_6053_, lean_object* v_a_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_){
_start:
{
lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6058_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6059_ = lean_unsigned_to_nat(1u);
v___x_6060_ = lean_mk_empty_array_with_capacity(v___x_6059_);
v___x_6061_ = lean_array_push(v___x_6060_, v_h_6052_);
v___x_6062_ = l_Lean_Meta_mkAppM(v___x_6058_, v___x_6061_, v_a_6053_, v_a_6054_, v_a_6055_, v_a_6056_);
return v___x_6062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_){
_start:
{
lean_object* v_res_6069_; 
v_res_6069_ = l_Lean_Meta_mkPropExt(v_h_6063_, v_a_6064_, v_a_6065_, v_a_6066_, v_a_6067_);
lean_dec(v_a_6067_);
lean_dec_ref(v_a_6066_);
lean_dec(v_a_6065_);
lean_dec_ref(v_a_6064_);
return v_res_6069_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6073_, lean_object* v_h_u2082_6074_, lean_object* v_a_6075_, lean_object* v_a_6076_, lean_object* v_a_6077_, lean_object* v_a_6078_){
_start:
{
lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; lean_object* v___x_6083_; lean_object* v___x_6084_; lean_object* v___x_6085_; 
v___x_6080_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6081_ = lean_unsigned_to_nat(2u);
v___x_6082_ = lean_mk_empty_array_with_capacity(v___x_6081_);
v___x_6083_ = lean_array_push(v___x_6082_, v_h_u2081_6073_);
v___x_6084_ = lean_array_push(v___x_6083_, v_h_u2082_6074_);
v___x_6085_ = l_Lean_Meta_mkAppM(v___x_6080_, v___x_6084_, v_a_6075_, v_a_6076_, v_a_6077_, v_a_6078_);
return v___x_6085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6086_, lean_object* v_h_u2082_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_, lean_object* v_a_6090_, lean_object* v_a_6091_, lean_object* v_a_6092_){
_start:
{
lean_object* v_res_6093_; 
v_res_6093_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6086_, v_h_u2082_6087_, v_a_6088_, v_a_6089_, v_a_6090_, v_a_6091_);
lean_dec(v_a_6091_);
lean_dec_ref(v_a_6090_);
lean_dec(v_a_6089_);
lean_dec_ref(v_a_6088_);
return v_res_6093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6097_, lean_object* v_h_6098_, lean_object* v_a_6099_, lean_object* v_a_6100_, lean_object* v_a_6101_, lean_object* v_a_6102_){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; 
v___x_6104_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6105_ = lean_unsigned_to_nat(2u);
v___x_6106_ = lean_mk_empty_array_with_capacity(v___x_6105_);
v___x_6107_ = lean_array_push(v___x_6106_, v_b_6097_);
v___x_6108_ = lean_array_push(v___x_6107_, v_h_6098_);
v___x_6109_ = l_Lean_Meta_mkAppM(v___x_6104_, v___x_6108_, v_a_6099_, v_a_6100_, v_a_6101_, v_a_6102_);
return v___x_6109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6110_, lean_object* v_h_6111_, lean_object* v_a_6112_, lean_object* v_a_6113_, lean_object* v_a_6114_, lean_object* v_a_6115_, lean_object* v_a_6116_){
_start:
{
lean_object* v_res_6117_; 
v_res_6117_ = l_Lean_Meta_mkLetValCongr(v_b_6110_, v_h_6111_, v_a_6112_, v_a_6113_, v_a_6114_, v_a_6115_);
lean_dec(v_a_6115_);
lean_dec_ref(v_a_6114_);
lean_dec(v_a_6113_);
lean_dec_ref(v_a_6112_);
return v_res_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6121_, lean_object* v_h_6122_, lean_object* v_a_6123_, lean_object* v_a_6124_, lean_object* v_a_6125_, lean_object* v_a_6126_){
_start:
{
lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; lean_object* v___x_6132_; lean_object* v___x_6133_; 
v___x_6128_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6129_ = lean_unsigned_to_nat(2u);
v___x_6130_ = lean_mk_empty_array_with_capacity(v___x_6129_);
v___x_6131_ = lean_array_push(v___x_6130_, v_a_6121_);
v___x_6132_ = lean_array_push(v___x_6131_, v_h_6122_);
v___x_6133_ = l_Lean_Meta_mkAppM(v___x_6128_, v___x_6132_, v_a_6123_, v_a_6124_, v_a_6125_, v_a_6126_);
return v___x_6133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6134_, lean_object* v_h_6135_, lean_object* v_a_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_, lean_object* v_a_6139_, lean_object* v_a_6140_){
_start:
{
lean_object* v_res_6141_; 
v_res_6141_ = l_Lean_Meta_mkLetBodyCongr(v_a_6134_, v_h_6135_, v_a_6136_, v_a_6137_, v_a_6138_, v_a_6139_);
lean_dec(v_a_6139_);
lean_dec_ref(v_a_6138_);
lean_dec(v_a_6137_);
lean_dec_ref(v_a_6136_);
return v_res_6141_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; 
v___x_6145_ = lean_box(0);
v___x_6146_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6147_ = l_Lean_mkConst(v___x_6146_, v___x_6145_);
return v___x_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6151_, lean_object* v_h_6152_){
_start:
{
lean_object* v___x_6156_; uint8_t v___x_6157_; 
lean_inc_ref(v_h_6152_);
v___x_6156_ = l_Lean_Expr_cleanupAnnotations(v_h_6152_);
v___x_6157_ = l_Lean_Expr_isApp(v___x_6156_);
if (v___x_6157_ == 0)
{
lean_dec_ref(v___x_6156_);
goto v___jp_6153_;
}
else
{
lean_object* v_arg_6158_; lean_object* v___x_6159_; uint8_t v___x_6160_; 
v_arg_6158_ = lean_ctor_get(v___x_6156_, 1);
lean_inc_ref(v_arg_6158_);
v___x_6159_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6156_);
v___x_6160_ = l_Lean_Expr_isApp(v___x_6159_);
if (v___x_6160_ == 0)
{
lean_dec_ref(v___x_6159_);
lean_dec_ref(v_arg_6158_);
goto v___jp_6153_;
}
else
{
lean_object* v___x_6161_; lean_object* v___x_6162_; uint8_t v___x_6163_; 
v___x_6161_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6159_);
v___x_6162_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6163_ = l_Lean_Expr_isConstOf(v___x_6161_, v___x_6162_);
lean_dec_ref(v___x_6161_);
if (v___x_6163_ == 0)
{
lean_dec_ref(v_arg_6158_);
goto v___jp_6153_;
}
else
{
lean_dec_ref(v_h_6152_);
lean_dec_ref(v_p_6151_);
return v_arg_6158_;
}
}
}
v___jp_6153_:
{
lean_object* v___x_6154_; lean_object* v___x_6155_; 
v___x_6154_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6155_ = l_Lean_mkAppB(v___x_6154_, v_p_6151_, v_h_6152_);
return v___x_6155_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6164_, lean_object* v_a_6165_, lean_object* v_a_6166_, lean_object* v_a_6167_, lean_object* v_a_6168_){
_start:
{
lean_object* v___x_6170_; 
lean_inc_ref(v_h_6164_);
v___x_6170_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6164_, v_a_6166_);
if (lean_obj_tag(v___x_6170_) == 0)
{
lean_object* v_a_6171_; lean_object* v___x_6173_; uint8_t v_isShared_6174_; uint8_t v_isSharedCheck_6196_; 
v_a_6171_ = lean_ctor_get(v___x_6170_, 0);
v_isSharedCheck_6196_ = !lean_is_exclusive(v___x_6170_);
if (v_isSharedCheck_6196_ == 0)
{
v___x_6173_ = v___x_6170_;
v_isShared_6174_ = v_isSharedCheck_6196_;
goto v_resetjp_6172_;
}
else
{
lean_inc(v_a_6171_);
lean_dec(v___x_6170_);
v___x_6173_ = lean_box(0);
v_isShared_6174_ = v_isSharedCheck_6196_;
goto v_resetjp_6172_;
}
v_resetjp_6172_:
{
lean_object* v___y_6176_; lean_object* v___y_6177_; lean_object* v___y_6178_; lean_object* v___y_6179_; lean_object* v___x_6185_; uint8_t v___x_6186_; 
v___x_6185_ = l_Lean_Expr_cleanupAnnotations(v_a_6171_);
v___x_6186_ = l_Lean_Expr_isApp(v___x_6185_);
if (v___x_6186_ == 0)
{
lean_dec_ref(v___x_6185_);
lean_del_object(v___x_6173_);
v___y_6176_ = v_a_6165_;
v___y_6177_ = v_a_6166_;
v___y_6178_ = v_a_6167_;
v___y_6179_ = v_a_6168_;
goto v___jp_6175_;
}
else
{
lean_object* v_arg_6187_; lean_object* v___x_6188_; uint8_t v___x_6189_; 
v_arg_6187_ = lean_ctor_get(v___x_6185_, 1);
lean_inc_ref(v_arg_6187_);
v___x_6188_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6185_);
v___x_6189_ = l_Lean_Expr_isApp(v___x_6188_);
if (v___x_6189_ == 0)
{
lean_dec_ref(v___x_6188_);
lean_dec_ref(v_arg_6187_);
lean_del_object(v___x_6173_);
v___y_6176_ = v_a_6165_;
v___y_6177_ = v_a_6166_;
v___y_6178_ = v_a_6167_;
v___y_6179_ = v_a_6168_;
goto v___jp_6175_;
}
else
{
lean_object* v___x_6190_; lean_object* v___x_6191_; uint8_t v___x_6192_; 
v___x_6190_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6188_);
v___x_6191_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6192_ = l_Lean_Expr_isConstOf(v___x_6190_, v___x_6191_);
lean_dec_ref(v___x_6190_);
if (v___x_6192_ == 0)
{
lean_dec_ref(v_arg_6187_);
lean_del_object(v___x_6173_);
v___y_6176_ = v_a_6165_;
v___y_6177_ = v_a_6166_;
v___y_6178_ = v_a_6167_;
v___y_6179_ = v_a_6168_;
goto v___jp_6175_;
}
else
{
lean_object* v___x_6194_; 
lean_dec_ref(v_h_6164_);
if (v_isShared_6174_ == 0)
{
lean_ctor_set(v___x_6173_, 0, v_arg_6187_);
v___x_6194_ = v___x_6173_;
goto v_reusejp_6193_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_arg_6187_);
v___x_6194_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6193_;
}
v_reusejp_6193_:
{
return v___x_6194_;
}
}
}
}
v___jp_6175_:
{
lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; 
v___x_6180_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6181_ = lean_unsigned_to_nat(1u);
v___x_6182_ = lean_mk_empty_array_with_capacity(v___x_6181_);
v___x_6183_ = lean_array_push(v___x_6182_, v_h_6164_);
v___x_6184_ = l_Lean_Meta_mkAppM(v___x_6180_, v___x_6183_, v___y_6176_, v___y_6177_, v___y_6178_, v___y_6179_);
return v___x_6184_;
}
}
}
else
{
lean_dec_ref(v_h_6164_);
return v___x_6170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6197_, lean_object* v_a_6198_, lean_object* v_a_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_, lean_object* v_a_6202_){
_start:
{
lean_object* v_res_6203_; 
v_res_6203_ = l_Lean_Meta_mkOfEqFalse(v_h_6197_, v_a_6198_, v_a_6199_, v_a_6200_, v_a_6201_);
lean_dec(v_a_6201_);
lean_dec_ref(v_a_6200_);
lean_dec(v_a_6199_);
lean_dec_ref(v_a_6198_);
return v_res_6203_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6207_ = lean_box(0);
v___x_6208_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6209_ = l_Lean_mkConst(v___x_6208_, v___x_6207_);
return v___x_6209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6213_, lean_object* v_h_6214_){
_start:
{
lean_object* v___x_6218_; uint8_t v___x_6219_; 
lean_inc_ref(v_h_6214_);
v___x_6218_ = l_Lean_Expr_cleanupAnnotations(v_h_6214_);
v___x_6219_ = l_Lean_Expr_isApp(v___x_6218_);
if (v___x_6219_ == 0)
{
lean_dec_ref(v___x_6218_);
goto v___jp_6215_;
}
else
{
lean_object* v_arg_6220_; lean_object* v___x_6221_; uint8_t v___x_6222_; 
v_arg_6220_ = lean_ctor_get(v___x_6218_, 1);
lean_inc_ref(v_arg_6220_);
v___x_6221_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6218_);
v___x_6222_ = l_Lean_Expr_isApp(v___x_6221_);
if (v___x_6222_ == 0)
{
lean_dec_ref(v___x_6221_);
lean_dec_ref(v_arg_6220_);
goto v___jp_6215_;
}
else
{
lean_object* v___x_6223_; lean_object* v___x_6224_; uint8_t v___x_6225_; 
v___x_6223_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6221_);
v___x_6224_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6225_ = l_Lean_Expr_isConstOf(v___x_6223_, v___x_6224_);
lean_dec_ref(v___x_6223_);
if (v___x_6225_ == 0)
{
lean_dec_ref(v_arg_6220_);
goto v___jp_6215_;
}
else
{
lean_dec_ref(v_h_6214_);
lean_dec_ref(v_p_6213_);
return v_arg_6220_;
}
}
}
v___jp_6215_:
{
lean_object* v___x_6216_; lean_object* v___x_6217_; 
v___x_6216_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6217_ = l_Lean_mkAppB(v___x_6216_, v_p_6213_, v_h_6214_);
return v___x_6217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6226_, lean_object* v_a_6227_, lean_object* v_a_6228_, lean_object* v_a_6229_, lean_object* v_a_6230_){
_start:
{
lean_object* v___x_6232_; 
lean_inc_ref(v_h_6226_);
v___x_6232_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6226_, v_a_6228_);
if (lean_obj_tag(v___x_6232_) == 0)
{
lean_object* v_a_6233_; lean_object* v___x_6235_; uint8_t v_isShared_6236_; uint8_t v_isSharedCheck_6258_; 
v_a_6233_ = lean_ctor_get(v___x_6232_, 0);
v_isSharedCheck_6258_ = !lean_is_exclusive(v___x_6232_);
if (v_isSharedCheck_6258_ == 0)
{
v___x_6235_ = v___x_6232_;
v_isShared_6236_ = v_isSharedCheck_6258_;
goto v_resetjp_6234_;
}
else
{
lean_inc(v_a_6233_);
lean_dec(v___x_6232_);
v___x_6235_ = lean_box(0);
v_isShared_6236_ = v_isSharedCheck_6258_;
goto v_resetjp_6234_;
}
v_resetjp_6234_:
{
lean_object* v___y_6238_; lean_object* v___y_6239_; lean_object* v___y_6240_; lean_object* v___y_6241_; lean_object* v___x_6247_; uint8_t v___x_6248_; 
v___x_6247_ = l_Lean_Expr_cleanupAnnotations(v_a_6233_);
v___x_6248_ = l_Lean_Expr_isApp(v___x_6247_);
if (v___x_6248_ == 0)
{
lean_dec_ref(v___x_6247_);
lean_del_object(v___x_6235_);
v___y_6238_ = v_a_6227_;
v___y_6239_ = v_a_6228_;
v___y_6240_ = v_a_6229_;
v___y_6241_ = v_a_6230_;
goto v___jp_6237_;
}
else
{
lean_object* v_arg_6249_; lean_object* v___x_6250_; uint8_t v___x_6251_; 
v_arg_6249_ = lean_ctor_get(v___x_6247_, 1);
lean_inc_ref(v_arg_6249_);
v___x_6250_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6247_);
v___x_6251_ = l_Lean_Expr_isApp(v___x_6250_);
if (v___x_6251_ == 0)
{
lean_dec_ref(v___x_6250_);
lean_dec_ref(v_arg_6249_);
lean_del_object(v___x_6235_);
v___y_6238_ = v_a_6227_;
v___y_6239_ = v_a_6228_;
v___y_6240_ = v_a_6229_;
v___y_6241_ = v_a_6230_;
goto v___jp_6237_;
}
else
{
lean_object* v___x_6252_; lean_object* v___x_6253_; uint8_t v___x_6254_; 
v___x_6252_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6250_);
v___x_6253_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6254_ = l_Lean_Expr_isConstOf(v___x_6252_, v___x_6253_);
lean_dec_ref(v___x_6252_);
if (v___x_6254_ == 0)
{
lean_dec_ref(v_arg_6249_);
lean_del_object(v___x_6235_);
v___y_6238_ = v_a_6227_;
v___y_6239_ = v_a_6228_;
v___y_6240_ = v_a_6229_;
v___y_6241_ = v_a_6230_;
goto v___jp_6237_;
}
else
{
lean_object* v___x_6256_; 
lean_dec_ref(v_h_6226_);
if (v_isShared_6236_ == 0)
{
lean_ctor_set(v___x_6235_, 0, v_arg_6249_);
v___x_6256_ = v___x_6235_;
goto v_reusejp_6255_;
}
else
{
lean_object* v_reuseFailAlloc_6257_; 
v_reuseFailAlloc_6257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6257_, 0, v_arg_6249_);
v___x_6256_ = v_reuseFailAlloc_6257_;
goto v_reusejp_6255_;
}
v_reusejp_6255_:
{
return v___x_6256_;
}
}
}
}
v___jp_6237_:
{
lean_object* v___x_6242_; lean_object* v___x_6243_; lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; 
v___x_6242_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6243_ = lean_unsigned_to_nat(1u);
v___x_6244_ = lean_mk_empty_array_with_capacity(v___x_6243_);
v___x_6245_ = lean_array_push(v___x_6244_, v_h_6226_);
v___x_6246_ = l_Lean_Meta_mkAppM(v___x_6242_, v___x_6245_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_);
return v___x_6246_;
}
}
}
else
{
lean_dec_ref(v_h_6226_);
return v___x_6232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6259_, lean_object* v_a_6260_, lean_object* v_a_6261_, lean_object* v_a_6262_, lean_object* v_a_6263_, lean_object* v_a_6264_){
_start:
{
lean_object* v_res_6265_; 
v_res_6265_ = l_Lean_Meta_mkOfEqTrue(v_h_6259_, v_a_6260_, v_a_6261_, v_a_6262_, v_a_6263_);
lean_dec(v_a_6263_);
lean_dec_ref(v_a_6262_);
lean_dec(v_a_6261_);
lean_dec_ref(v_a_6260_);
return v_res_6265_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6266_; lean_object* v___x_6267_; lean_object* v___x_6268_; 
v___x_6266_ = lean_box(0);
v___x_6267_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6268_ = l_Lean_mkConst(v___x_6267_, v___x_6266_);
return v___x_6268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6269_, lean_object* v_h_6270_){
_start:
{
lean_object* v___x_6274_; uint8_t v___x_6275_; 
lean_inc_ref(v_h_6270_);
v___x_6274_ = l_Lean_Expr_cleanupAnnotations(v_h_6270_);
v___x_6275_ = l_Lean_Expr_isApp(v___x_6274_);
if (v___x_6275_ == 0)
{
lean_dec_ref(v___x_6274_);
goto v___jp_6271_;
}
else
{
lean_object* v_arg_6276_; lean_object* v___x_6277_; uint8_t v___x_6278_; 
v_arg_6276_ = lean_ctor_get(v___x_6274_, 1);
lean_inc_ref(v_arg_6276_);
v___x_6277_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6274_);
v___x_6278_ = l_Lean_Expr_isApp(v___x_6277_);
if (v___x_6278_ == 0)
{
lean_dec_ref(v___x_6277_);
lean_dec_ref(v_arg_6276_);
goto v___jp_6271_;
}
else
{
lean_object* v___x_6279_; lean_object* v___x_6280_; uint8_t v___x_6281_; 
v___x_6279_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6277_);
v___x_6280_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6281_ = l_Lean_Expr_isConstOf(v___x_6279_, v___x_6280_);
lean_dec_ref(v___x_6279_);
if (v___x_6281_ == 0)
{
lean_dec_ref(v_arg_6276_);
goto v___jp_6271_;
}
else
{
lean_dec_ref(v_h_6270_);
lean_dec_ref(v_p_6269_);
return v_arg_6276_;
}
}
}
v___jp_6271_:
{
lean_object* v___x_6272_; lean_object* v___x_6273_; 
v___x_6272_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6273_ = l_Lean_mkAppB(v___x_6272_, v_p_6269_, v_h_6270_);
return v___x_6273_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6282_, lean_object* v_a_6283_, lean_object* v_a_6284_, lean_object* v_a_6285_, lean_object* v_a_6286_){
_start:
{
lean_object* v___x_6288_; 
lean_inc_ref(v_h_6282_);
v___x_6288_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6282_, v_a_6284_);
if (lean_obj_tag(v___x_6288_) == 0)
{
lean_object* v_a_6289_; lean_object* v___x_6291_; uint8_t v_isShared_6292_; uint8_t v_isSharedCheck_6320_; 
v_a_6289_ = lean_ctor_get(v___x_6288_, 0);
v_isSharedCheck_6320_ = !lean_is_exclusive(v___x_6288_);
if (v_isSharedCheck_6320_ == 0)
{
v___x_6291_ = v___x_6288_;
v_isShared_6292_ = v_isSharedCheck_6320_;
goto v_resetjp_6290_;
}
else
{
lean_inc(v_a_6289_);
lean_dec(v___x_6288_);
v___x_6291_ = lean_box(0);
v_isShared_6292_ = v_isSharedCheck_6320_;
goto v_resetjp_6290_;
}
v_resetjp_6290_:
{
lean_object* v___y_6294_; lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; lean_object* v___x_6309_; uint8_t v___x_6310_; 
v___x_6309_ = l_Lean_Expr_cleanupAnnotations(v_a_6289_);
v___x_6310_ = l_Lean_Expr_isApp(v___x_6309_);
if (v___x_6310_ == 0)
{
lean_dec_ref(v___x_6309_);
lean_del_object(v___x_6291_);
v___y_6294_ = v_a_6283_;
v___y_6295_ = v_a_6284_;
v___y_6296_ = v_a_6285_;
v___y_6297_ = v_a_6286_;
goto v___jp_6293_;
}
else
{
lean_object* v_arg_6311_; lean_object* v___x_6312_; uint8_t v___x_6313_; 
v_arg_6311_ = lean_ctor_get(v___x_6309_, 1);
lean_inc_ref(v_arg_6311_);
v___x_6312_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6309_);
v___x_6313_ = l_Lean_Expr_isApp(v___x_6312_);
if (v___x_6313_ == 0)
{
lean_dec_ref(v___x_6312_);
lean_dec_ref(v_arg_6311_);
lean_del_object(v___x_6291_);
v___y_6294_ = v_a_6283_;
v___y_6295_ = v_a_6284_;
v___y_6296_ = v_a_6285_;
v___y_6297_ = v_a_6286_;
goto v___jp_6293_;
}
else
{
lean_object* v___x_6314_; lean_object* v___x_6315_; uint8_t v___x_6316_; 
v___x_6314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6312_);
v___x_6315_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6316_ = l_Lean_Expr_isConstOf(v___x_6314_, v___x_6315_);
lean_dec_ref(v___x_6314_);
if (v___x_6316_ == 0)
{
lean_dec_ref(v_arg_6311_);
lean_del_object(v___x_6291_);
v___y_6294_ = v_a_6283_;
v___y_6295_ = v_a_6284_;
v___y_6296_ = v_a_6285_;
v___y_6297_ = v_a_6286_;
goto v___jp_6293_;
}
else
{
lean_object* v___x_6318_; 
lean_dec_ref(v_h_6282_);
if (v_isShared_6292_ == 0)
{
lean_ctor_set(v___x_6291_, 0, v_arg_6311_);
v___x_6318_ = v___x_6291_;
goto v_reusejp_6317_;
}
else
{
lean_object* v_reuseFailAlloc_6319_; 
v_reuseFailAlloc_6319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6319_, 0, v_arg_6311_);
v___x_6318_ = v_reuseFailAlloc_6319_;
goto v_reusejp_6317_;
}
v_reusejp_6317_:
{
return v___x_6318_;
}
}
}
}
v___jp_6293_:
{
lean_object* v___x_6298_; 
lean_inc(v___y_6297_);
lean_inc_ref(v___y_6296_);
lean_inc(v___y_6295_);
lean_inc_ref(v___y_6294_);
lean_inc_ref(v_h_6282_);
v___x_6298_ = lean_infer_type(v_h_6282_, v___y_6294_, v___y_6295_, v___y_6296_, v___y_6297_);
if (lean_obj_tag(v___x_6298_) == 0)
{
lean_object* v_a_6299_; lean_object* v___x_6301_; uint8_t v_isShared_6302_; uint8_t v_isSharedCheck_6308_; 
v_a_6299_ = lean_ctor_get(v___x_6298_, 0);
v_isSharedCheck_6308_ = !lean_is_exclusive(v___x_6298_);
if (v_isSharedCheck_6308_ == 0)
{
v___x_6301_ = v___x_6298_;
v_isShared_6302_ = v_isSharedCheck_6308_;
goto v_resetjp_6300_;
}
else
{
lean_inc(v_a_6299_);
lean_dec(v___x_6298_);
v___x_6301_ = lean_box(0);
v_isShared_6302_ = v_isSharedCheck_6308_;
goto v_resetjp_6300_;
}
v_resetjp_6300_:
{
lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6306_; 
v___x_6303_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6304_ = l_Lean_mkAppB(v___x_6303_, v_a_6299_, v_h_6282_);
if (v_isShared_6302_ == 0)
{
lean_ctor_set(v___x_6301_, 0, v___x_6304_);
v___x_6306_ = v___x_6301_;
goto v_reusejp_6305_;
}
else
{
lean_object* v_reuseFailAlloc_6307_; 
v_reuseFailAlloc_6307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6307_, 0, v___x_6304_);
v___x_6306_ = v_reuseFailAlloc_6307_;
goto v_reusejp_6305_;
}
v_reusejp_6305_:
{
return v___x_6306_;
}
}
}
else
{
lean_dec_ref(v_h_6282_);
return v___x_6298_;
}
}
}
}
else
{
lean_dec_ref(v_h_6282_);
return v___x_6288_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6321_, lean_object* v_a_6322_, lean_object* v_a_6323_, lean_object* v_a_6324_, lean_object* v_a_6325_, lean_object* v_a_6326_){
_start:
{
lean_object* v_res_6327_; 
v_res_6327_ = l_Lean_Meta_mkEqTrue(v_h_6321_, v_a_6322_, v_a_6323_, v_a_6324_, v_a_6325_);
lean_dec(v_a_6325_);
lean_dec_ref(v_a_6324_);
lean_dec(v_a_6323_);
lean_dec_ref(v_a_6322_);
return v_res_6327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6328_, lean_object* v_a_6329_, lean_object* v_a_6330_, lean_object* v_a_6331_, lean_object* v_a_6332_){
_start:
{
lean_object* v___y_6335_; lean_object* v___y_6336_; lean_object* v___y_6337_; lean_object* v___y_6338_; lean_object* v___x_6344_; uint8_t v___x_6345_; 
lean_inc_ref(v_h_6328_);
v___x_6344_ = l_Lean_Expr_cleanupAnnotations(v_h_6328_);
v___x_6345_ = l_Lean_Expr_isApp(v___x_6344_);
if (v___x_6345_ == 0)
{
lean_dec_ref(v___x_6344_);
v___y_6335_ = v_a_6329_;
v___y_6336_ = v_a_6330_;
v___y_6337_ = v_a_6331_;
v___y_6338_ = v_a_6332_;
goto v___jp_6334_;
}
else
{
lean_object* v_arg_6346_; lean_object* v___x_6347_; uint8_t v___x_6348_; 
v_arg_6346_ = lean_ctor_get(v___x_6344_, 1);
lean_inc_ref(v_arg_6346_);
v___x_6347_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6344_);
v___x_6348_ = l_Lean_Expr_isApp(v___x_6347_);
if (v___x_6348_ == 0)
{
lean_dec_ref(v___x_6347_);
lean_dec_ref(v_arg_6346_);
v___y_6335_ = v_a_6329_;
v___y_6336_ = v_a_6330_;
v___y_6337_ = v_a_6331_;
v___y_6338_ = v_a_6332_;
goto v___jp_6334_;
}
else
{
lean_object* v___x_6349_; lean_object* v___x_6350_; uint8_t v___x_6351_; 
v___x_6349_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6347_);
v___x_6350_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6351_ = l_Lean_Expr_isConstOf(v___x_6349_, v___x_6350_);
lean_dec_ref(v___x_6349_);
if (v___x_6351_ == 0)
{
lean_dec_ref(v_arg_6346_);
v___y_6335_ = v_a_6329_;
v___y_6336_ = v_a_6330_;
v___y_6337_ = v_a_6331_;
v___y_6338_ = v_a_6332_;
goto v___jp_6334_;
}
else
{
lean_object* v___x_6352_; 
lean_dec_ref(v_h_6328_);
v___x_6352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6352_, 0, v_arg_6346_);
return v___x_6352_;
}
}
}
v___jp_6334_:
{
lean_object* v___x_6339_; lean_object* v___x_6340_; lean_object* v___x_6341_; lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6339_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6340_ = lean_unsigned_to_nat(1u);
v___x_6341_ = lean_mk_empty_array_with_capacity(v___x_6340_);
v___x_6342_ = lean_array_push(v___x_6341_, v_h_6328_);
v___x_6343_ = l_Lean_Meta_mkAppM(v___x_6339_, v___x_6342_, v___y_6335_, v___y_6336_, v___y_6337_, v___y_6338_);
return v___x_6343_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6353_, lean_object* v_a_6354_, lean_object* v_a_6355_, lean_object* v_a_6356_, lean_object* v_a_6357_, lean_object* v_a_6358_){
_start:
{
lean_object* v_res_6359_; 
v_res_6359_ = l_Lean_Meta_mkEqFalse(v_h_6353_, v_a_6354_, v_a_6355_, v_a_6356_, v_a_6357_);
lean_dec(v_a_6357_);
lean_dec_ref(v_a_6356_);
lean_dec(v_a_6355_);
lean_dec_ref(v_a_6354_);
return v_res_6359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6363_, lean_object* v_a_6364_, lean_object* v_a_6365_, lean_object* v_a_6366_, lean_object* v_a_6367_){
_start:
{
lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6369_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6370_ = lean_unsigned_to_nat(1u);
v___x_6371_ = lean_mk_empty_array_with_capacity(v___x_6370_);
v___x_6372_ = lean_array_push(v___x_6371_, v_h_6363_);
v___x_6373_ = l_Lean_Meta_mkAppM(v___x_6369_, v___x_6372_, v_a_6364_, v_a_6365_, v_a_6366_, v_a_6367_);
return v___x_6373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6374_, lean_object* v_a_6375_, lean_object* v_a_6376_, lean_object* v_a_6377_, lean_object* v_a_6378_, lean_object* v_a_6379_){
_start:
{
lean_object* v_res_6380_; 
v_res_6380_ = l_Lean_Meta_mkEqFalse_x27(v_h_6374_, v_a_6375_, v_a_6376_, v_a_6377_, v_a_6378_);
lean_dec(v_a_6378_);
lean_dec_ref(v_a_6377_);
lean_dec(v_a_6376_);
lean_dec_ref(v_a_6375_);
return v_res_6380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6384_, lean_object* v_h_u2082_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_, lean_object* v_a_6389_){
_start:
{
lean_object* v___x_6391_; lean_object* v___x_6392_; lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; lean_object* v___x_6396_; 
v___x_6391_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6392_ = lean_unsigned_to_nat(2u);
v___x_6393_ = lean_mk_empty_array_with_capacity(v___x_6392_);
v___x_6394_ = lean_array_push(v___x_6393_, v_h_u2081_6384_);
v___x_6395_ = lean_array_push(v___x_6394_, v_h_u2082_6385_);
v___x_6396_ = l_Lean_Meta_mkAppM(v___x_6391_, v___x_6395_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_);
return v___x_6396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6397_, lean_object* v_h_u2082_6398_, lean_object* v_a_6399_, lean_object* v_a_6400_, lean_object* v_a_6401_, lean_object* v_a_6402_, lean_object* v_a_6403_){
_start:
{
lean_object* v_res_6404_; 
v_res_6404_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6397_, v_h_u2082_6398_, v_a_6399_, v_a_6400_, v_a_6401_, v_a_6402_);
lean_dec(v_a_6402_);
lean_dec_ref(v_a_6401_);
lean_dec(v_a_6400_);
lean_dec_ref(v_a_6399_);
return v_res_6404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6408_, lean_object* v_h_u2082_6409_, lean_object* v_a_6410_, lean_object* v_a_6411_, lean_object* v_a_6412_, lean_object* v_a_6413_){
_start:
{
lean_object* v___x_6415_; lean_object* v___x_6416_; lean_object* v___x_6417_; lean_object* v___x_6418_; lean_object* v___x_6419_; lean_object* v___x_6420_; 
v___x_6415_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6416_ = lean_unsigned_to_nat(2u);
v___x_6417_ = lean_mk_empty_array_with_capacity(v___x_6416_);
v___x_6418_ = lean_array_push(v___x_6417_, v_h_u2081_6408_);
v___x_6419_ = lean_array_push(v___x_6418_, v_h_u2082_6409_);
v___x_6420_ = l_Lean_Meta_mkAppM(v___x_6415_, v___x_6419_, v_a_6410_, v_a_6411_, v_a_6412_, v_a_6413_);
return v___x_6420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6421_, lean_object* v_h_u2082_6422_, lean_object* v_a_6423_, lean_object* v_a_6424_, lean_object* v_a_6425_, lean_object* v_a_6426_, lean_object* v_a_6427_){
_start:
{
lean_object* v_res_6428_; 
v_res_6428_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6421_, v_h_u2082_6422_, v_a_6423_, v_a_6424_, v_a_6425_, v_a_6426_);
lean_dec(v_a_6426_);
lean_dec_ref(v_a_6425_);
lean_dec(v_a_6424_);
lean_dec_ref(v_a_6423_);
return v_res_6428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6432_, lean_object* v_h_u2082_6433_, lean_object* v_a_6434_, lean_object* v_a_6435_, lean_object* v_a_6436_, lean_object* v_a_6437_){
_start:
{
lean_object* v___x_6439_; lean_object* v___x_6440_; lean_object* v___x_6441_; lean_object* v___x_6442_; lean_object* v___x_6443_; lean_object* v___x_6444_; 
v___x_6439_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6440_ = lean_unsigned_to_nat(2u);
v___x_6441_ = lean_mk_empty_array_with_capacity(v___x_6440_);
v___x_6442_ = lean_array_push(v___x_6441_, v_h_u2081_6432_);
v___x_6443_ = lean_array_push(v___x_6442_, v_h_u2082_6433_);
v___x_6444_ = l_Lean_Meta_mkAppM(v___x_6439_, v___x_6443_, v_a_6434_, v_a_6435_, v_a_6436_, v_a_6437_);
return v___x_6444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6445_, lean_object* v_h_u2082_6446_, lean_object* v_a_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_, lean_object* v_a_6450_, lean_object* v_a_6451_){
_start:
{
lean_object* v_res_6452_; 
v_res_6452_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6445_, v_h_u2082_6446_, v_a_6447_, v_a_6448_, v_a_6449_, v_a_6450_);
lean_dec(v_a_6450_);
lean_dec_ref(v_a_6449_);
lean_dec(v_a_6448_);
lean_dec_ref(v_a_6447_);
return v_res_6452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6456_, lean_object* v_a_6457_, lean_object* v_a_6458_, lean_object* v_a_6459_, lean_object* v_a_6460_){
_start:
{
lean_object* v___x_6462_; lean_object* v___x_6463_; lean_object* v___x_6464_; lean_object* v___x_6465_; lean_object* v___x_6466_; 
v___x_6462_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6463_ = lean_unsigned_to_nat(1u);
v___x_6464_ = lean_mk_empty_array_with_capacity(v___x_6463_);
v___x_6465_ = lean_array_push(v___x_6464_, v_h_6456_);
v___x_6466_ = l_Lean_Meta_mkAppM(v___x_6462_, v___x_6465_, v_a_6457_, v_a_6458_, v_a_6459_, v_a_6460_);
return v___x_6466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6467_, lean_object* v_a_6468_, lean_object* v_a_6469_, lean_object* v_a_6470_, lean_object* v_a_6471_, lean_object* v_a_6472_){
_start:
{
lean_object* v_res_6473_; 
v_res_6473_ = l_Lean_Meta_mkForallCongr(v_h_6467_, v_a_6468_, v_a_6469_, v_a_6470_, v_a_6471_);
lean_dec(v_a_6471_);
lean_dec_ref(v_a_6470_);
lean_dec(v_a_6469_);
lean_dec_ref(v_a_6468_);
return v_res_6473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6477_, lean_object* v_a_6478_, lean_object* v_a_6479_, lean_object* v_a_6480_, lean_object* v_a_6481_){
_start:
{
lean_object* v___y_6484_; uint8_t v___y_6485_; lean_object* v___y_6489_; lean_object* v_a_6490_; lean_object* v___x_6493_; lean_object* v___x_6494_; lean_object* v___x_6495_; lean_object* v___x_6496_; lean_object* v___x_6497_; 
v___x_6493_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6494_ = lean_unsigned_to_nat(1u);
v___x_6495_ = lean_mk_empty_array_with_capacity(v___x_6494_);
v___x_6496_ = lean_array_push(v___x_6495_, v_m_6477_);
v___x_6497_ = l_Lean_Meta_mkAppM(v___x_6493_, v___x_6496_, v_a_6478_, v_a_6479_, v_a_6480_, v_a_6481_);
if (lean_obj_tag(v___x_6497_) == 0)
{
lean_object* v_a_6498_; lean_object* v___x_6499_; lean_object* v___x_6500_; 
v_a_6498_ = lean_ctor_get(v___x_6497_, 0);
lean_inc(v_a_6498_);
lean_dec_ref_known(v___x_6497_, 1);
v___x_6499_ = lean_box(0);
v___x_6500_ = l_Lean_Meta_trySynthInstance(v_a_6498_, v___x_6499_, v_a_6478_, v_a_6479_, v_a_6480_, v_a_6481_);
if (lean_obj_tag(v___x_6500_) == 0)
{
lean_object* v_a_6501_; lean_object* v___x_6503_; uint8_t v_isShared_6504_; uint8_t v_isSharedCheck_6519_; 
v_a_6501_ = lean_ctor_get(v___x_6500_, 0);
v_isSharedCheck_6519_ = !lean_is_exclusive(v___x_6500_);
if (v_isSharedCheck_6519_ == 0)
{
v___x_6503_ = v___x_6500_;
v_isShared_6504_ = v_isSharedCheck_6519_;
goto v_resetjp_6502_;
}
else
{
lean_inc(v_a_6501_);
lean_dec(v___x_6500_);
v___x_6503_ = lean_box(0);
v_isShared_6504_ = v_isSharedCheck_6519_;
goto v_resetjp_6502_;
}
v_resetjp_6502_:
{
if (lean_obj_tag(v_a_6501_) == 1)
{
lean_object* v_a_6505_; lean_object* v___x_6507_; uint8_t v_isShared_6508_; uint8_t v_isSharedCheck_6515_; 
v_a_6505_ = lean_ctor_get(v_a_6501_, 0);
v_isSharedCheck_6515_ = !lean_is_exclusive(v_a_6501_);
if (v_isSharedCheck_6515_ == 0)
{
v___x_6507_ = v_a_6501_;
v_isShared_6508_ = v_isSharedCheck_6515_;
goto v_resetjp_6506_;
}
else
{
lean_inc(v_a_6505_);
lean_dec(v_a_6501_);
v___x_6507_ = lean_box(0);
v_isShared_6508_ = v_isSharedCheck_6515_;
goto v_resetjp_6506_;
}
v_resetjp_6506_:
{
lean_object* v___x_6510_; 
if (v_isShared_6508_ == 0)
{
v___x_6510_ = v___x_6507_;
goto v_reusejp_6509_;
}
else
{
lean_object* v_reuseFailAlloc_6514_; 
v_reuseFailAlloc_6514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6514_, 0, v_a_6505_);
v___x_6510_ = v_reuseFailAlloc_6514_;
goto v_reusejp_6509_;
}
v_reusejp_6509_:
{
lean_object* v___x_6512_; 
if (v_isShared_6504_ == 0)
{
lean_ctor_set(v___x_6503_, 0, v___x_6510_);
v___x_6512_ = v___x_6503_;
goto v_reusejp_6511_;
}
else
{
lean_object* v_reuseFailAlloc_6513_; 
v_reuseFailAlloc_6513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6513_, 0, v___x_6510_);
v___x_6512_ = v_reuseFailAlloc_6513_;
goto v_reusejp_6511_;
}
v_reusejp_6511_:
{
return v___x_6512_;
}
}
}
}
else
{
lean_object* v___x_6517_; 
lean_dec(v_a_6501_);
if (v_isShared_6504_ == 0)
{
lean_ctor_set(v___x_6503_, 0, v___x_6499_);
v___x_6517_ = v___x_6503_;
goto v_reusejp_6516_;
}
else
{
lean_object* v_reuseFailAlloc_6518_; 
v_reuseFailAlloc_6518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6518_, 0, v___x_6499_);
v___x_6517_ = v_reuseFailAlloc_6518_;
goto v_reusejp_6516_;
}
v_reusejp_6516_:
{
return v___x_6517_;
}
}
}
}
else
{
lean_object* v_a_6520_; lean_object* v___x_6522_; uint8_t v_isShared_6523_; uint8_t v_isSharedCheck_6527_; 
v_a_6520_ = lean_ctor_get(v___x_6500_, 0);
v_isSharedCheck_6527_ = !lean_is_exclusive(v___x_6500_);
if (v_isSharedCheck_6527_ == 0)
{
v___x_6522_ = v___x_6500_;
v_isShared_6523_ = v_isSharedCheck_6527_;
goto v_resetjp_6521_;
}
else
{
lean_inc(v_a_6520_);
lean_dec(v___x_6500_);
v___x_6522_ = lean_box(0);
v_isShared_6523_ = v_isSharedCheck_6527_;
goto v_resetjp_6521_;
}
v_resetjp_6521_:
{
lean_object* v___x_6525_; 
lean_inc(v_a_6520_);
if (v_isShared_6523_ == 0)
{
v___x_6525_ = v___x_6522_;
goto v_reusejp_6524_;
}
else
{
lean_object* v_reuseFailAlloc_6526_; 
v_reuseFailAlloc_6526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_a_6520_);
v___x_6525_ = v_reuseFailAlloc_6526_;
goto v_reusejp_6524_;
}
v_reusejp_6524_:
{
v___y_6489_ = v___x_6525_;
v_a_6490_ = v_a_6520_;
goto v___jp_6488_;
}
}
}
}
else
{
lean_object* v_a_6528_; lean_object* v___x_6530_; uint8_t v_isShared_6531_; uint8_t v_isSharedCheck_6535_; 
v_a_6528_ = lean_ctor_get(v___x_6497_, 0);
v_isSharedCheck_6535_ = !lean_is_exclusive(v___x_6497_);
if (v_isSharedCheck_6535_ == 0)
{
v___x_6530_ = v___x_6497_;
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
else
{
lean_inc(v_a_6528_);
lean_dec(v___x_6497_);
v___x_6530_ = lean_box(0);
v_isShared_6531_ = v_isSharedCheck_6535_;
goto v_resetjp_6529_;
}
v_resetjp_6529_:
{
lean_object* v___x_6533_; 
lean_inc(v_a_6528_);
if (v_isShared_6531_ == 0)
{
v___x_6533_ = v___x_6530_;
goto v_reusejp_6532_;
}
else
{
lean_object* v_reuseFailAlloc_6534_; 
v_reuseFailAlloc_6534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6534_, 0, v_a_6528_);
v___x_6533_ = v_reuseFailAlloc_6534_;
goto v_reusejp_6532_;
}
v_reusejp_6532_:
{
v___y_6489_ = v___x_6533_;
v_a_6490_ = v_a_6528_;
goto v___jp_6488_;
}
}
}
v___jp_6483_:
{
if (v___y_6485_ == 0)
{
lean_object* v___x_6486_; lean_object* v___x_6487_; 
lean_dec_ref(v___y_6484_);
v___x_6486_ = lean_box(0);
v___x_6487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6487_, 0, v___x_6486_);
return v___x_6487_;
}
else
{
return v___y_6484_;
}
}
v___jp_6488_:
{
uint8_t v___x_6491_; 
v___x_6491_ = l_Lean_Exception_isInterrupt(v_a_6490_);
if (v___x_6491_ == 0)
{
uint8_t v___x_6492_; 
v___x_6492_ = l_Lean_Exception_isRuntime(v_a_6490_);
v___y_6484_ = v___y_6489_;
v___y_6485_ = v___x_6492_;
goto v___jp_6483_;
}
else
{
lean_dec_ref(v_a_6490_);
v___y_6484_ = v___y_6489_;
v___y_6485_ = v___x_6491_;
goto v___jp_6483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6536_, lean_object* v_a_6537_, lean_object* v_a_6538_, lean_object* v_a_6539_, lean_object* v_a_6540_, lean_object* v_a_6541_){
_start:
{
lean_object* v_res_6542_; 
v_res_6542_ = l_Lean_Meta_isMonad_x3f(v_m_6536_, v_a_6537_, v_a_6538_, v_a_6539_, v_a_6540_);
lean_dec(v_a_6540_);
lean_dec_ref(v_a_6539_);
lean_dec(v_a_6538_);
lean_dec_ref(v_a_6537_);
return v_res_6542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6550_, lean_object* v_n_6551_, lean_object* v_a_6552_, lean_object* v_a_6553_, lean_object* v_a_6554_, lean_object* v_a_6555_){
_start:
{
lean_object* v___x_6557_; 
lean_inc_ref(v_type_6550_);
v___x_6557_ = l_Lean_Meta_getDecLevel(v_type_6550_, v_a_6552_, v_a_6553_, v_a_6554_, v_a_6555_);
if (lean_obj_tag(v___x_6557_) == 0)
{
lean_object* v_a_6558_; lean_object* v___x_6559_; lean_object* v___x_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6565_; lean_object* v___x_6566_; 
v_a_6558_ = lean_ctor_get(v___x_6557_, 0);
lean_inc(v_a_6558_);
lean_dec_ref_known(v___x_6557_, 1);
v___x_6559_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6560_ = lean_box(0);
v___x_6561_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6561_, 0, v_a_6558_);
lean_ctor_set(v___x_6561_, 1, v___x_6560_);
lean_inc_ref(v___x_6561_);
v___x_6562_ = l_Lean_mkConst(v___x_6559_, v___x_6561_);
v___x_6563_ = l_Lean_mkRawNatLit(v_n_6551_);
lean_inc_ref(v___x_6563_);
lean_inc_ref(v_type_6550_);
v___x_6564_ = l_Lean_mkAppB(v___x_6562_, v_type_6550_, v___x_6563_);
v___x_6565_ = lean_box(0);
v___x_6566_ = l_Lean_Meta_synthInstance(v___x_6564_, v___x_6565_, v_a_6552_, v_a_6553_, v_a_6554_, v_a_6555_);
if (lean_obj_tag(v___x_6566_) == 0)
{
lean_object* v_a_6567_; lean_object* v___x_6569_; uint8_t v_isShared_6570_; uint8_t v_isSharedCheck_6577_; 
v_a_6567_ = lean_ctor_get(v___x_6566_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v___x_6566_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6569_ = v___x_6566_;
v_isShared_6570_ = v_isSharedCheck_6577_;
goto v_resetjp_6568_;
}
else
{
lean_inc(v_a_6567_);
lean_dec(v___x_6566_);
v___x_6569_ = lean_box(0);
v_isShared_6570_ = v_isSharedCheck_6577_;
goto v_resetjp_6568_;
}
v_resetjp_6568_:
{
lean_object* v___x_6571_; lean_object* v___x_6572_; lean_object* v___x_6573_; lean_object* v___x_6575_; 
v___x_6571_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6572_ = l_Lean_mkConst(v___x_6571_, v___x_6561_);
v___x_6573_ = l_Lean_mkApp3(v___x_6572_, v_type_6550_, v___x_6563_, v_a_6567_);
if (v_isShared_6570_ == 0)
{
lean_ctor_set(v___x_6569_, 0, v___x_6573_);
v___x_6575_ = v___x_6569_;
goto v_reusejp_6574_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v___x_6573_);
v___x_6575_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6574_;
}
v_reusejp_6574_:
{
return v___x_6575_;
}
}
}
else
{
lean_dec_ref(v___x_6563_);
lean_dec_ref_known(v___x_6561_, 2);
lean_dec_ref(v_type_6550_);
return v___x_6566_;
}
}
else
{
lean_object* v_a_6578_; lean_object* v___x_6580_; uint8_t v_isShared_6581_; uint8_t v_isSharedCheck_6585_; 
lean_dec(v_n_6551_);
lean_dec_ref(v_type_6550_);
v_a_6578_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6585_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6585_ == 0)
{
v___x_6580_ = v___x_6557_;
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
else
{
lean_inc(v_a_6578_);
lean_dec(v___x_6557_);
v___x_6580_ = lean_box(0);
v_isShared_6581_ = v_isSharedCheck_6585_;
goto v_resetjp_6579_;
}
v_resetjp_6579_:
{
lean_object* v___x_6583_; 
if (v_isShared_6581_ == 0)
{
v___x_6583_ = v___x_6580_;
goto v_reusejp_6582_;
}
else
{
lean_object* v_reuseFailAlloc_6584_; 
v_reuseFailAlloc_6584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6584_, 0, v_a_6578_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6586_, lean_object* v_n_6587_, lean_object* v_a_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_){
_start:
{
lean_object* v_res_6593_; 
v_res_6593_ = l_Lean_Meta_mkNumeral(v_type_6586_, v_n_6587_, v_a_6588_, v_a_6589_, v_a_6590_, v_a_6591_);
lean_dec(v_a_6591_);
lean_dec_ref(v_a_6590_);
lean_dec(v_a_6589_);
lean_dec_ref(v_a_6588_);
return v_res_6593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6594_, lean_object* v_opName_6595_, lean_object* v_a_6596_, lean_object* v_b_6597_, lean_object* v_a_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_){
_start:
{
lean_object* v___x_6603_; 
lean_inc(v_a_6601_);
lean_inc_ref(v_a_6600_);
lean_inc(v_a_6599_);
lean_inc_ref(v_a_6598_);
lean_inc_ref(v_a_6596_);
v___x_6603_ = lean_infer_type(v_a_6596_, v_a_6598_, v_a_6599_, v_a_6600_, v_a_6601_);
if (lean_obj_tag(v___x_6603_) == 0)
{
lean_object* v_a_6604_; lean_object* v___x_6605_; 
v_a_6604_ = lean_ctor_get(v___x_6603_, 0);
lean_inc_n(v_a_6604_, 2);
lean_dec_ref_known(v___x_6603_, 1);
v___x_6605_ = l_Lean_Meta_getDecLevel(v_a_6604_, v_a_6598_, v_a_6599_, v_a_6600_, v_a_6601_);
if (lean_obj_tag(v___x_6605_) == 0)
{
lean_object* v_a_6606_; lean_object* v___x_6607_; lean_object* v___x_6608_; lean_object* v___x_6609_; lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6612_; lean_object* v___x_6613_; lean_object* v___x_6614_; 
v_a_6606_ = lean_ctor_get(v___x_6605_, 0);
lean_inc_n(v_a_6606_, 3);
lean_dec_ref_known(v___x_6605_, 1);
v___x_6607_ = lean_box(0);
v___x_6608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6608_, 0, v_a_6606_);
lean_ctor_set(v___x_6608_, 1, v___x_6607_);
v___x_6609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6609_, 0, v_a_6606_);
lean_ctor_set(v___x_6609_, 1, v___x_6608_);
v___x_6610_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6610_, 0, v_a_6606_);
lean_ctor_set(v___x_6610_, 1, v___x_6609_);
lean_inc_ref(v___x_6610_);
v___x_6611_ = l_Lean_mkConst(v_className_6594_, v___x_6610_);
lean_inc_n(v_a_6604_, 3);
v___x_6612_ = l_Lean_mkApp3(v___x_6611_, v_a_6604_, v_a_6604_, v_a_6604_);
v___x_6613_ = lean_box(0);
v___x_6614_ = l_Lean_Meta_synthInstance(v___x_6612_, v___x_6613_, v_a_6598_, v_a_6599_, v_a_6600_, v_a_6601_);
if (lean_obj_tag(v___x_6614_) == 0)
{
lean_object* v_a_6615_; lean_object* v___x_6617_; uint8_t v_isShared_6618_; uint8_t v_isSharedCheck_6624_; 
v_a_6615_ = lean_ctor_get(v___x_6614_, 0);
v_isSharedCheck_6624_ = !lean_is_exclusive(v___x_6614_);
if (v_isSharedCheck_6624_ == 0)
{
v___x_6617_ = v___x_6614_;
v_isShared_6618_ = v_isSharedCheck_6624_;
goto v_resetjp_6616_;
}
else
{
lean_inc(v_a_6615_);
lean_dec(v___x_6614_);
v___x_6617_ = lean_box(0);
v_isShared_6618_ = v_isSharedCheck_6624_;
goto v_resetjp_6616_;
}
v_resetjp_6616_:
{
lean_object* v___x_6619_; lean_object* v___x_6620_; lean_object* v___x_6622_; 
v___x_6619_ = l_Lean_mkConst(v_opName_6595_, v___x_6610_);
lean_inc_n(v_a_6604_, 2);
v___x_6620_ = l_Lean_mkApp6(v___x_6619_, v_a_6604_, v_a_6604_, v_a_6604_, v_a_6615_, v_a_6596_, v_b_6597_);
if (v_isShared_6618_ == 0)
{
lean_ctor_set(v___x_6617_, 0, v___x_6620_);
v___x_6622_ = v___x_6617_;
goto v_reusejp_6621_;
}
else
{
lean_object* v_reuseFailAlloc_6623_; 
v_reuseFailAlloc_6623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6623_, 0, v___x_6620_);
v___x_6622_ = v_reuseFailAlloc_6623_;
goto v_reusejp_6621_;
}
v_reusejp_6621_:
{
return v___x_6622_;
}
}
}
else
{
lean_dec_ref_known(v___x_6610_, 2);
lean_dec(v_a_6604_);
lean_dec_ref(v_b_6597_);
lean_dec_ref(v_a_6596_);
lean_dec(v_opName_6595_);
return v___x_6614_;
}
}
else
{
lean_object* v_a_6625_; lean_object* v___x_6627_; uint8_t v_isShared_6628_; uint8_t v_isSharedCheck_6632_; 
lean_dec(v_a_6604_);
lean_dec_ref(v_b_6597_);
lean_dec_ref(v_a_6596_);
lean_dec(v_opName_6595_);
lean_dec(v_className_6594_);
v_a_6625_ = lean_ctor_get(v___x_6605_, 0);
v_isSharedCheck_6632_ = !lean_is_exclusive(v___x_6605_);
if (v_isSharedCheck_6632_ == 0)
{
v___x_6627_ = v___x_6605_;
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
else
{
lean_inc(v_a_6625_);
lean_dec(v___x_6605_);
v___x_6627_ = lean_box(0);
v_isShared_6628_ = v_isSharedCheck_6632_;
goto v_resetjp_6626_;
}
v_resetjp_6626_:
{
lean_object* v___x_6630_; 
if (v_isShared_6628_ == 0)
{
v___x_6630_ = v___x_6627_;
goto v_reusejp_6629_;
}
else
{
lean_object* v_reuseFailAlloc_6631_; 
v_reuseFailAlloc_6631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6631_, 0, v_a_6625_);
v___x_6630_ = v_reuseFailAlloc_6631_;
goto v_reusejp_6629_;
}
v_reusejp_6629_:
{
return v___x_6630_;
}
}
}
}
else
{
lean_dec_ref(v_b_6597_);
lean_dec_ref(v_a_6596_);
lean_dec(v_opName_6595_);
lean_dec(v_className_6594_);
return v___x_6603_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6633_, lean_object* v_opName_6634_, lean_object* v_a_6635_, lean_object* v_b_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_, lean_object* v_a_6641_){
_start:
{
lean_object* v_res_6642_; 
v_res_6642_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6633_, v_opName_6634_, v_a_6635_, v_b_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_);
lean_dec(v_a_6640_);
lean_dec_ref(v_a_6639_);
lean_dec(v_a_6638_);
lean_dec_ref(v_a_6637_);
return v_res_6642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6650_, lean_object* v_b_6651_, lean_object* v_a_6652_, lean_object* v_a_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_){
_start:
{
lean_object* v___x_6657_; lean_object* v___x_6658_; lean_object* v___x_6659_; 
v___x_6657_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6658_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6659_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6657_, v___x_6658_, v_a_6650_, v_b_6651_, v_a_6652_, v_a_6653_, v_a_6654_, v_a_6655_);
return v___x_6659_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6660_, lean_object* v_b_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_, lean_object* v_a_6665_, lean_object* v_a_6666_){
_start:
{
lean_object* v_res_6667_; 
v_res_6667_ = l_Lean_Meta_mkAdd(v_a_6660_, v_b_6661_, v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_);
lean_dec(v_a_6665_);
lean_dec_ref(v_a_6664_);
lean_dec(v_a_6663_);
lean_dec_ref(v_a_6662_);
return v_res_6667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6675_, lean_object* v_b_6676_, lean_object* v_a_6677_, lean_object* v_a_6678_, lean_object* v_a_6679_, lean_object* v_a_6680_){
_start:
{
lean_object* v___x_6682_; lean_object* v___x_6683_; lean_object* v___x_6684_; 
v___x_6682_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6683_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6684_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6682_, v___x_6683_, v_a_6675_, v_b_6676_, v_a_6677_, v_a_6678_, v_a_6679_, v_a_6680_);
return v___x_6684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6685_, lean_object* v_b_6686_, lean_object* v_a_6687_, lean_object* v_a_6688_, lean_object* v_a_6689_, lean_object* v_a_6690_, lean_object* v_a_6691_){
_start:
{
lean_object* v_res_6692_; 
v_res_6692_ = l_Lean_Meta_mkSub(v_a_6685_, v_b_6686_, v_a_6687_, v_a_6688_, v_a_6689_, v_a_6690_);
lean_dec(v_a_6690_);
lean_dec_ref(v_a_6689_);
lean_dec(v_a_6688_);
lean_dec_ref(v_a_6687_);
return v_res_6692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6700_, lean_object* v_b_6701_, lean_object* v_a_6702_, lean_object* v_a_6703_, lean_object* v_a_6704_, lean_object* v_a_6705_){
_start:
{
lean_object* v___x_6707_; lean_object* v___x_6708_; lean_object* v___x_6709_; 
v___x_6707_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6708_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6709_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6707_, v___x_6708_, v_a_6700_, v_b_6701_, v_a_6702_, v_a_6703_, v_a_6704_, v_a_6705_);
return v___x_6709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6710_, lean_object* v_b_6711_, lean_object* v_a_6712_, lean_object* v_a_6713_, lean_object* v_a_6714_, lean_object* v_a_6715_, lean_object* v_a_6716_){
_start:
{
lean_object* v_res_6717_; 
v_res_6717_ = l_Lean_Meta_mkMul(v_a_6710_, v_b_6711_, v_a_6712_, v_a_6713_, v_a_6714_, v_a_6715_);
lean_dec(v_a_6715_);
lean_dec_ref(v_a_6714_);
lean_dec(v_a_6713_);
lean_dec_ref(v_a_6712_);
return v_res_6717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6718_, lean_object* v_rName_6719_, lean_object* v_a_6720_, lean_object* v_b_6721_, lean_object* v_a_6722_, lean_object* v_a_6723_, lean_object* v_a_6724_, lean_object* v_a_6725_){
_start:
{
lean_object* v___x_6727_; 
lean_inc(v_a_6725_);
lean_inc_ref(v_a_6724_);
lean_inc(v_a_6723_);
lean_inc_ref(v_a_6722_);
lean_inc_ref(v_a_6720_);
v___x_6727_ = lean_infer_type(v_a_6720_, v_a_6722_, v_a_6723_, v_a_6724_, v_a_6725_);
if (lean_obj_tag(v___x_6727_) == 0)
{
lean_object* v_a_6728_; lean_object* v___x_6729_; 
v_a_6728_ = lean_ctor_get(v___x_6727_, 0);
lean_inc_n(v_a_6728_, 2);
lean_dec_ref_known(v___x_6727_, 1);
v___x_6729_ = l_Lean_Meta_getDecLevel(v_a_6728_, v_a_6722_, v_a_6723_, v_a_6724_, v_a_6725_);
if (lean_obj_tag(v___x_6729_) == 0)
{
lean_object* v_a_6730_; lean_object* v___x_6731_; lean_object* v___x_6732_; lean_object* v___x_6733_; lean_object* v___x_6734_; lean_object* v___x_6735_; lean_object* v___x_6736_; 
v_a_6730_ = lean_ctor_get(v___x_6729_, 0);
lean_inc(v_a_6730_);
lean_dec_ref_known(v___x_6729_, 1);
v___x_6731_ = lean_box(0);
v___x_6732_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6732_, 0, v_a_6730_);
lean_ctor_set(v___x_6732_, 1, v___x_6731_);
lean_inc_ref(v___x_6732_);
v___x_6733_ = l_Lean_mkConst(v_className_6718_, v___x_6732_);
lean_inc(v_a_6728_);
v___x_6734_ = l_Lean_Expr_app___override(v___x_6733_, v_a_6728_);
v___x_6735_ = lean_box(0);
v___x_6736_ = l_Lean_Meta_synthInstance(v___x_6734_, v___x_6735_, v_a_6722_, v_a_6723_, v_a_6724_, v_a_6725_);
if (lean_obj_tag(v___x_6736_) == 0)
{
lean_object* v_a_6737_; lean_object* v___x_6739_; uint8_t v_isShared_6740_; uint8_t v_isSharedCheck_6746_; 
v_a_6737_ = lean_ctor_get(v___x_6736_, 0);
v_isSharedCheck_6746_ = !lean_is_exclusive(v___x_6736_);
if (v_isSharedCheck_6746_ == 0)
{
v___x_6739_ = v___x_6736_;
v_isShared_6740_ = v_isSharedCheck_6746_;
goto v_resetjp_6738_;
}
else
{
lean_inc(v_a_6737_);
lean_dec(v___x_6736_);
v___x_6739_ = lean_box(0);
v_isShared_6740_ = v_isSharedCheck_6746_;
goto v_resetjp_6738_;
}
v_resetjp_6738_:
{
lean_object* v___x_6741_; lean_object* v___x_6742_; lean_object* v___x_6744_; 
v___x_6741_ = l_Lean_mkConst(v_rName_6719_, v___x_6732_);
v___x_6742_ = l_Lean_mkApp4(v___x_6741_, v_a_6728_, v_a_6737_, v_a_6720_, v_b_6721_);
if (v_isShared_6740_ == 0)
{
lean_ctor_set(v___x_6739_, 0, v___x_6742_);
v___x_6744_ = v___x_6739_;
goto v_reusejp_6743_;
}
else
{
lean_object* v_reuseFailAlloc_6745_; 
v_reuseFailAlloc_6745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6745_, 0, v___x_6742_);
v___x_6744_ = v_reuseFailAlloc_6745_;
goto v_reusejp_6743_;
}
v_reusejp_6743_:
{
return v___x_6744_;
}
}
}
else
{
lean_dec_ref_known(v___x_6732_, 2);
lean_dec(v_a_6728_);
lean_dec_ref(v_b_6721_);
lean_dec_ref(v_a_6720_);
lean_dec(v_rName_6719_);
return v___x_6736_;
}
}
else
{
lean_object* v_a_6747_; lean_object* v___x_6749_; uint8_t v_isShared_6750_; uint8_t v_isSharedCheck_6754_; 
lean_dec(v_a_6728_);
lean_dec_ref(v_b_6721_);
lean_dec_ref(v_a_6720_);
lean_dec(v_rName_6719_);
lean_dec(v_className_6718_);
v_a_6747_ = lean_ctor_get(v___x_6729_, 0);
v_isSharedCheck_6754_ = !lean_is_exclusive(v___x_6729_);
if (v_isSharedCheck_6754_ == 0)
{
v___x_6749_ = v___x_6729_;
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
else
{
lean_inc(v_a_6747_);
lean_dec(v___x_6729_);
v___x_6749_ = lean_box(0);
v_isShared_6750_ = v_isSharedCheck_6754_;
goto v_resetjp_6748_;
}
v_resetjp_6748_:
{
lean_object* v___x_6752_; 
if (v_isShared_6750_ == 0)
{
v___x_6752_ = v___x_6749_;
goto v_reusejp_6751_;
}
else
{
lean_object* v_reuseFailAlloc_6753_; 
v_reuseFailAlloc_6753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6753_, 0, v_a_6747_);
v___x_6752_ = v_reuseFailAlloc_6753_;
goto v_reusejp_6751_;
}
v_reusejp_6751_:
{
return v___x_6752_;
}
}
}
}
else
{
lean_dec_ref(v_b_6721_);
lean_dec_ref(v_a_6720_);
lean_dec(v_rName_6719_);
lean_dec(v_className_6718_);
return v___x_6727_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6755_, lean_object* v_rName_6756_, lean_object* v_a_6757_, lean_object* v_b_6758_, lean_object* v_a_6759_, lean_object* v_a_6760_, lean_object* v_a_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_){
_start:
{
lean_object* v_res_6764_; 
v_res_6764_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6755_, v_rName_6756_, v_a_6757_, v_b_6758_, v_a_6759_, v_a_6760_, v_a_6761_, v_a_6762_);
lean_dec(v_a_6762_);
lean_dec_ref(v_a_6761_);
lean_dec(v_a_6760_);
lean_dec_ref(v_a_6759_);
return v_res_6764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6767_, lean_object* v_b_6768_, lean_object* v_a_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_){
_start:
{
lean_object* v___x_6774_; lean_object* v___x_6775_; lean_object* v___x_6776_; 
v___x_6774_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6775_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6776_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6774_, v___x_6775_, v_a_6767_, v_b_6768_, v_a_6769_, v_a_6770_, v_a_6771_, v_a_6772_);
return v___x_6776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6777_, lean_object* v_b_6778_, lean_object* v_a_6779_, lean_object* v_a_6780_, lean_object* v_a_6781_, lean_object* v_a_6782_, lean_object* v_a_6783_){
_start:
{
lean_object* v_res_6784_; 
v_res_6784_ = l_Lean_Meta_mkLE(v_a_6777_, v_b_6778_, v_a_6779_, v_a_6780_, v_a_6781_, v_a_6782_);
lean_dec(v_a_6782_);
lean_dec_ref(v_a_6781_);
lean_dec(v_a_6780_);
lean_dec_ref(v_a_6779_);
return v_res_6784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6787_, lean_object* v_b_6788_, lean_object* v_a_6789_, lean_object* v_a_6790_, lean_object* v_a_6791_, lean_object* v_a_6792_){
_start:
{
lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; 
v___x_6794_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6795_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6796_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6794_, v___x_6795_, v_a_6787_, v_b_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_);
return v___x_6796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6797_, lean_object* v_b_6798_, lean_object* v_a_6799_, lean_object* v_a_6800_, lean_object* v_a_6801_, lean_object* v_a_6802_, lean_object* v_a_6803_){
_start:
{
lean_object* v_res_6804_; 
v_res_6804_ = l_Lean_Meta_mkLT(v_a_6797_, v_b_6798_, v_a_6799_, v_a_6800_, v_a_6801_, v_a_6802_);
lean_dec(v_a_6802_);
lean_dec_ref(v_a_6801_);
lean_dec(v_a_6800_);
lean_dec_ref(v_a_6799_);
return v_res_6804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6810_, lean_object* v_a_6811_, lean_object* v_a_6812_, lean_object* v_a_6813_, lean_object* v_a_6814_){
_start:
{
lean_object* v___x_6816_; lean_object* v___x_6817_; uint8_t v___x_6818_; 
v___x_6816_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6817_ = lean_unsigned_to_nat(3u);
v___x_6818_ = l_Lean_Expr_isAppOfArity(v_h_6810_, v___x_6816_, v___x_6817_);
if (v___x_6818_ == 0)
{
lean_object* v___x_6819_; lean_object* v___x_6820_; lean_object* v___x_6821_; lean_object* v___x_6822_; lean_object* v___x_6823_; 
v___x_6819_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6820_ = lean_unsigned_to_nat(1u);
v___x_6821_ = lean_mk_empty_array_with_capacity(v___x_6820_);
v___x_6822_ = lean_array_push(v___x_6821_, v_h_6810_);
v___x_6823_ = l_Lean_Meta_mkAppM(v___x_6819_, v___x_6822_, v_a_6811_, v_a_6812_, v_a_6813_, v_a_6814_);
return v___x_6823_;
}
else
{
lean_object* v___x_6824_; lean_object* v___x_6825_; 
v___x_6824_ = l_Lean_Expr_appArg_x21(v_h_6810_);
lean_dec_ref(v_h_6810_);
v___x_6825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6825_, 0, v___x_6824_);
return v___x_6825_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6826_, lean_object* v_a_6827_, lean_object* v_a_6828_, lean_object* v_a_6829_, lean_object* v_a_6830_, lean_object* v_a_6831_){
_start:
{
lean_object* v_res_6832_; 
v_res_6832_ = l_Lean_Meta_mkIffOfEq(v_h_6826_, v_a_6827_, v_a_6828_, v_a_6829_, v_a_6830_);
lean_dec(v_a_6830_);
lean_dec_ref(v_a_6829_);
lean_dec(v_a_6828_);
lean_dec_ref(v_a_6827_);
return v_res_6832_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; 
v___x_6838_ = lean_box(0);
v___x_6839_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6840_ = l_Lean_mkConst(v___x_6839_, v___x_6838_);
return v___x_6840_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6843_; lean_object* v___x_6844_; lean_object* v___x_6845_; 
v___x_6843_ = lean_box(0);
v___x_6844_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6845_ = l_Lean_mkConst(v___x_6844_, v___x_6843_);
return v___x_6845_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6846_; lean_object* v___x_6847_; lean_object* v___x_6848_; 
v___x_6846_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6847_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6848_, 0, v___x_6847_);
lean_ctor_set(v___x_6848_, 1, v___x_6846_);
return v___x_6848_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6853_; lean_object* v___x_6854_; lean_object* v___x_6855_; 
v___x_6853_ = lean_box(0);
v___x_6854_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6855_ = l_Lean_mkConst(v___x_6854_, v___x_6853_);
return v___x_6855_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6858_; lean_object* v___x_6859_; lean_object* v___x_6860_; 
v___x_6858_ = lean_box(0);
v___x_6859_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6860_ = l_Lean_mkConst(v___x_6859_, v___x_6858_);
return v___x_6860_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6861_, lean_object* v_a_6862_, lean_object* v_a_6863_, lean_object* v_a_6864_, lean_object* v_a_6865_){
_start:
{
if (lean_obj_tag(v_a_6861_) == 0)
{
lean_object* v___x_6867_; lean_object* v___x_6868_; 
v___x_6867_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6868_, 0, v___x_6867_);
return v___x_6868_;
}
else
{
lean_object* v_tail_6869_; 
v_tail_6869_ = lean_ctor_get(v_a_6861_, 1);
if (lean_obj_tag(v_tail_6869_) == 0)
{
lean_object* v_head_6870_; lean_object* v___x_6872_; uint8_t v_isShared_6873_; uint8_t v_isSharedCheck_6894_; 
v_head_6870_ = lean_ctor_get(v_a_6861_, 0);
v_isSharedCheck_6894_ = !lean_is_exclusive(v_a_6861_);
if (v_isSharedCheck_6894_ == 0)
{
lean_object* v_unused_6895_; 
v_unused_6895_ = lean_ctor_get(v_a_6861_, 1);
lean_dec(v_unused_6895_);
v___x_6872_ = v_a_6861_;
v_isShared_6873_ = v_isSharedCheck_6894_;
goto v_resetjp_6871_;
}
else
{
lean_inc(v_head_6870_);
lean_dec(v_a_6861_);
v___x_6872_ = lean_box(0);
v_isShared_6873_ = v_isSharedCheck_6894_;
goto v_resetjp_6871_;
}
v_resetjp_6871_:
{
lean_object* v___x_6874_; 
lean_inc(v_a_6865_);
lean_inc_ref(v_a_6864_);
lean_inc(v_a_6863_);
lean_inc_ref(v_a_6862_);
lean_inc(v_head_6870_);
v___x_6874_ = lean_infer_type(v_head_6870_, v_a_6862_, v_a_6863_, v_a_6864_, v_a_6865_);
if (lean_obj_tag(v___x_6874_) == 0)
{
lean_object* v_a_6875_; lean_object* v___x_6877_; uint8_t v_isShared_6878_; uint8_t v_isSharedCheck_6885_; 
v_a_6875_ = lean_ctor_get(v___x_6874_, 0);
v_isSharedCheck_6885_ = !lean_is_exclusive(v___x_6874_);
if (v_isSharedCheck_6885_ == 0)
{
v___x_6877_ = v___x_6874_;
v_isShared_6878_ = v_isSharedCheck_6885_;
goto v_resetjp_6876_;
}
else
{
lean_inc(v_a_6875_);
lean_dec(v___x_6874_);
v___x_6877_ = lean_box(0);
v_isShared_6878_ = v_isSharedCheck_6885_;
goto v_resetjp_6876_;
}
v_resetjp_6876_:
{
lean_object* v___x_6880_; 
if (v_isShared_6873_ == 0)
{
lean_ctor_set_tag(v___x_6872_, 0);
lean_ctor_set(v___x_6872_, 1, v_a_6875_);
v___x_6880_ = v___x_6872_;
goto v_reusejp_6879_;
}
else
{
lean_object* v_reuseFailAlloc_6884_; 
v_reuseFailAlloc_6884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6884_, 0, v_head_6870_);
lean_ctor_set(v_reuseFailAlloc_6884_, 1, v_a_6875_);
v___x_6880_ = v_reuseFailAlloc_6884_;
goto v_reusejp_6879_;
}
v_reusejp_6879_:
{
lean_object* v___x_6882_; 
if (v_isShared_6878_ == 0)
{
lean_ctor_set(v___x_6877_, 0, v___x_6880_);
v___x_6882_ = v___x_6877_;
goto v_reusejp_6881_;
}
else
{
lean_object* v_reuseFailAlloc_6883_; 
v_reuseFailAlloc_6883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6883_, 0, v___x_6880_);
v___x_6882_ = v_reuseFailAlloc_6883_;
goto v_reusejp_6881_;
}
v_reusejp_6881_:
{
return v___x_6882_;
}
}
}
}
else
{
lean_object* v_a_6886_; lean_object* v___x_6888_; uint8_t v_isShared_6889_; uint8_t v_isSharedCheck_6893_; 
lean_del_object(v___x_6872_);
lean_dec(v_head_6870_);
v_a_6886_ = lean_ctor_get(v___x_6874_, 0);
v_isSharedCheck_6893_ = !lean_is_exclusive(v___x_6874_);
if (v_isSharedCheck_6893_ == 0)
{
v___x_6888_ = v___x_6874_;
v_isShared_6889_ = v_isSharedCheck_6893_;
goto v_resetjp_6887_;
}
else
{
lean_inc(v_a_6886_);
lean_dec(v___x_6874_);
v___x_6888_ = lean_box(0);
v_isShared_6889_ = v_isSharedCheck_6893_;
goto v_resetjp_6887_;
}
v_resetjp_6887_:
{
lean_object* v___x_6891_; 
if (v_isShared_6889_ == 0)
{
v___x_6891_ = v___x_6888_;
goto v_reusejp_6890_;
}
else
{
lean_object* v_reuseFailAlloc_6892_; 
v_reuseFailAlloc_6892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6892_, 0, v_a_6886_);
v___x_6891_ = v_reuseFailAlloc_6892_;
goto v_reusejp_6890_;
}
v_reusejp_6890_:
{
return v___x_6891_;
}
}
}
}
}
else
{
lean_object* v_head_6896_; lean_object* v___x_6897_; 
lean_inc(v_tail_6869_);
v_head_6896_ = lean_ctor_get(v_a_6861_, 0);
lean_inc(v_head_6896_);
lean_dec_ref_known(v_a_6861_, 2);
v___x_6897_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6869_, v_a_6862_, v_a_6863_, v_a_6864_, v_a_6865_);
if (lean_obj_tag(v___x_6897_) == 0)
{
lean_object* v_a_6898_; lean_object* v_fst_6899_; lean_object* v_snd_6900_; lean_object* v___x_6902_; uint8_t v_isShared_6903_; uint8_t v_isSharedCheck_6928_; 
v_a_6898_ = lean_ctor_get(v___x_6897_, 0);
lean_inc(v_a_6898_);
lean_dec_ref_known(v___x_6897_, 1);
v_fst_6899_ = lean_ctor_get(v_a_6898_, 0);
v_snd_6900_ = lean_ctor_get(v_a_6898_, 1);
v_isSharedCheck_6928_ = !lean_is_exclusive(v_a_6898_);
if (v_isSharedCheck_6928_ == 0)
{
v___x_6902_ = v_a_6898_;
v_isShared_6903_ = v_isSharedCheck_6928_;
goto v_resetjp_6901_;
}
else
{
lean_inc(v_snd_6900_);
lean_inc(v_fst_6899_);
lean_dec(v_a_6898_);
v___x_6902_ = lean_box(0);
v_isShared_6903_ = v_isSharedCheck_6928_;
goto v_resetjp_6901_;
}
v_resetjp_6901_:
{
lean_object* v___x_6904_; 
lean_inc(v_a_6865_);
lean_inc_ref(v_a_6864_);
lean_inc(v_a_6863_);
lean_inc_ref(v_a_6862_);
lean_inc(v_head_6896_);
v___x_6904_ = lean_infer_type(v_head_6896_, v_a_6862_, v_a_6863_, v_a_6864_, v_a_6865_);
if (lean_obj_tag(v___x_6904_) == 0)
{
lean_object* v_a_6905_; lean_object* v___x_6907_; uint8_t v_isShared_6908_; uint8_t v_isSharedCheck_6919_; 
v_a_6905_ = lean_ctor_get(v___x_6904_, 0);
v_isSharedCheck_6919_ = !lean_is_exclusive(v___x_6904_);
if (v_isSharedCheck_6919_ == 0)
{
v___x_6907_ = v___x_6904_;
v_isShared_6908_ = v_isSharedCheck_6919_;
goto v_resetjp_6906_;
}
else
{
lean_inc(v_a_6905_);
lean_dec(v___x_6904_);
v___x_6907_ = lean_box(0);
v_isShared_6908_ = v_isSharedCheck_6919_;
goto v_resetjp_6906_;
}
v_resetjp_6906_:
{
lean_object* v___x_6909_; lean_object* v___x_6910_; lean_object* v___x_6911_; lean_object* v___x_6912_; lean_object* v___x_6914_; 
v___x_6909_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6900_);
lean_inc(v_a_6905_);
v___x_6910_ = l_Lean_mkApp4(v___x_6909_, v_a_6905_, v_snd_6900_, v_head_6896_, v_fst_6899_);
v___x_6911_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6912_ = l_Lean_mkAppB(v___x_6911_, v_a_6905_, v_snd_6900_);
if (v_isShared_6903_ == 0)
{
lean_ctor_set(v___x_6902_, 1, v___x_6912_);
lean_ctor_set(v___x_6902_, 0, v___x_6910_);
v___x_6914_ = v___x_6902_;
goto v_reusejp_6913_;
}
else
{
lean_object* v_reuseFailAlloc_6918_; 
v_reuseFailAlloc_6918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6918_, 0, v___x_6910_);
lean_ctor_set(v_reuseFailAlloc_6918_, 1, v___x_6912_);
v___x_6914_ = v_reuseFailAlloc_6918_;
goto v_reusejp_6913_;
}
v_reusejp_6913_:
{
lean_object* v___x_6916_; 
if (v_isShared_6908_ == 0)
{
lean_ctor_set(v___x_6907_, 0, v___x_6914_);
v___x_6916_ = v___x_6907_;
goto v_reusejp_6915_;
}
else
{
lean_object* v_reuseFailAlloc_6917_; 
v_reuseFailAlloc_6917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6917_, 0, v___x_6914_);
v___x_6916_ = v_reuseFailAlloc_6917_;
goto v_reusejp_6915_;
}
v_reusejp_6915_:
{
return v___x_6916_;
}
}
}
}
else
{
lean_object* v_a_6920_; lean_object* v___x_6922_; uint8_t v_isShared_6923_; uint8_t v_isSharedCheck_6927_; 
lean_del_object(v___x_6902_);
lean_dec(v_snd_6900_);
lean_dec(v_fst_6899_);
lean_dec(v_head_6896_);
v_a_6920_ = lean_ctor_get(v___x_6904_, 0);
v_isSharedCheck_6927_ = !lean_is_exclusive(v___x_6904_);
if (v_isSharedCheck_6927_ == 0)
{
v___x_6922_ = v___x_6904_;
v_isShared_6923_ = v_isSharedCheck_6927_;
goto v_resetjp_6921_;
}
else
{
lean_inc(v_a_6920_);
lean_dec(v___x_6904_);
v___x_6922_ = lean_box(0);
v_isShared_6923_ = v_isSharedCheck_6927_;
goto v_resetjp_6921_;
}
v_resetjp_6921_:
{
lean_object* v___x_6925_; 
if (v_isShared_6923_ == 0)
{
v___x_6925_ = v___x_6922_;
goto v_reusejp_6924_;
}
else
{
lean_object* v_reuseFailAlloc_6926_; 
v_reuseFailAlloc_6926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6926_, 0, v_a_6920_);
v___x_6925_ = v_reuseFailAlloc_6926_;
goto v_reusejp_6924_;
}
v_reusejp_6924_:
{
return v___x_6925_;
}
}
}
}
}
else
{
lean_dec(v_head_6896_);
return v___x_6897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6929_, lean_object* v_a_6930_, lean_object* v_a_6931_, lean_object* v_a_6932_, lean_object* v_a_6933_, lean_object* v_a_6934_){
_start:
{
lean_object* v_res_6935_; 
v_res_6935_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6929_, v_a_6930_, v_a_6931_, v_a_6932_, v_a_6933_);
lean_dec(v_a_6933_);
lean_dec_ref(v_a_6932_);
lean_dec(v_a_6931_);
lean_dec_ref(v_a_6930_);
return v_res_6935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6936_, lean_object* v_a_6937_, lean_object* v_a_6938_, lean_object* v_a_6939_, lean_object* v_a_6940_){
_start:
{
lean_object* v___x_6942_; 
v___x_6942_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6936_, v_a_6937_, v_a_6938_, v_a_6939_, v_a_6940_);
if (lean_obj_tag(v___x_6942_) == 0)
{
lean_object* v_a_6943_; lean_object* v___x_6945_; uint8_t v_isShared_6946_; uint8_t v_isSharedCheck_6951_; 
v_a_6943_ = lean_ctor_get(v___x_6942_, 0);
v_isSharedCheck_6951_ = !lean_is_exclusive(v___x_6942_);
if (v_isSharedCheck_6951_ == 0)
{
v___x_6945_ = v___x_6942_;
v_isShared_6946_ = v_isSharedCheck_6951_;
goto v_resetjp_6944_;
}
else
{
lean_inc(v_a_6943_);
lean_dec(v___x_6942_);
v___x_6945_ = lean_box(0);
v_isShared_6946_ = v_isSharedCheck_6951_;
goto v_resetjp_6944_;
}
v_resetjp_6944_:
{
lean_object* v_fst_6947_; lean_object* v___x_6949_; 
v_fst_6947_ = lean_ctor_get(v_a_6943_, 0);
lean_inc(v_fst_6947_);
lean_dec(v_a_6943_);
if (v_isShared_6946_ == 0)
{
lean_ctor_set(v___x_6945_, 0, v_fst_6947_);
v___x_6949_ = v___x_6945_;
goto v_reusejp_6948_;
}
else
{
lean_object* v_reuseFailAlloc_6950_; 
v_reuseFailAlloc_6950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6950_, 0, v_fst_6947_);
v___x_6949_ = v_reuseFailAlloc_6950_;
goto v_reusejp_6948_;
}
v_reusejp_6948_:
{
return v___x_6949_;
}
}
}
else
{
lean_object* v_a_6952_; lean_object* v___x_6954_; uint8_t v_isShared_6955_; uint8_t v_isSharedCheck_6959_; 
v_a_6952_ = lean_ctor_get(v___x_6942_, 0);
v_isSharedCheck_6959_ = !lean_is_exclusive(v___x_6942_);
if (v_isSharedCheck_6959_ == 0)
{
v___x_6954_ = v___x_6942_;
v_isShared_6955_ = v_isSharedCheck_6959_;
goto v_resetjp_6953_;
}
else
{
lean_inc(v_a_6952_);
lean_dec(v___x_6942_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_6960_, lean_object* v_a_6961_, lean_object* v_a_6962_, lean_object* v_a_6963_, lean_object* v_a_6964_, lean_object* v_a_6965_){
_start:
{
lean_object* v_res_6966_; 
v_res_6966_ = l_Lean_Meta_mkAndIntroN(v_hs_6960_, v_a_6961_, v_a_6962_, v_a_6963_, v_a_6964_);
lean_dec(v_a_6964_);
lean_dec_ref(v_a_6963_);
lean_dec(v_a_6962_);
lean_dec_ref(v_a_6961_);
return v_res_6966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7023_; uint8_t v___x_7024_; lean_object* v___x_7025_; lean_object* v___x_7026_; 
v___x_7023_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7024_ = 0;
v___x_7025_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7026_ = l_Lean_registerTraceClass(v___x_7023_, v___x_7024_, v___x_7025_);
if (lean_obj_tag(v___x_7026_) == 0)
{
lean_object* v___x_7027_; uint8_t v___x_7028_; lean_object* v___x_7029_; 
lean_dec_ref_known(v___x_7026_, 1);
v___x_7027_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7028_ = 1;
v___x_7029_ = l_Lean_registerTraceClass(v___x_7027_, v___x_7028_, v___x_7025_);
if (lean_obj_tag(v___x_7029_) == 0)
{
lean_object* v___x_7030_; lean_object* v___x_7031_; 
lean_dec_ref_known(v___x_7029_, 1);
v___x_7030_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7031_ = l_Lean_registerTraceClass(v___x_7030_, v___x_7028_, v___x_7025_);
return v___x_7031_;
}
else
{
return v___x_7029_;
}
}
else
{
return v___x_7026_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7032_){
_start:
{
lean_object* v_res_7033_; 
v_res_7033_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7033_;
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
