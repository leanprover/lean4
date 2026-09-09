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
v_options_436_ = lean_ctor_get(v___y_428_, 1);
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
v_ref_453_ = lean_ctor_get(v___y_450_, 4);
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
lean_object* v_x_1954_; lean_object* v___y_1956_; lean_object* v___x_1973_; 
lean_dec(v_binderName_1929_);
v_x_1954_ = lean_array_fget_borrowed(v_xs_1916_, v_i_1918_);
lean_inc(v_a_1925_);
lean_inc_ref(v_a_1924_);
lean_inc(v_a_1923_);
lean_inc_ref(v_a_1922_);
lean_inc(v_x_1954_);
v___x_1973_ = lean_infer_type(v_x_1954_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
if (lean_obj_tag(v___x_1973_) == 0)
{
lean_object* v_a_1974_; lean_object* v___x_1975_; uint8_t v_transparency_1976_; uint8_t v___x_1977_; uint8_t v___x_1978_; 
v_a_1974_ = lean_ctor_get(v___x_1973_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1973_, 1);
v___x_1975_ = l_Lean_Meta_Context_config(v_a_1922_);
v_transparency_1976_ = lean_ctor_get_uint8(v___x_1975_, 9);
lean_dec_ref(v___x_1975_);
v___x_1977_ = 1;
v___x_1978_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_Meta_isExprDefEq(v_d_1934_, v_a_1974_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
v___y_1956_ = v___x_1979_;
goto v___jp_1955_;
}
else
{
lean_object* v_keyedConfig_1980_; uint8_t v_trackZetaDelta_1981_; lean_object* v_zetaDeltaSet_1982_; lean_object* v_lctx_1983_; lean_object* v_localInstances_1984_; lean_object* v_defEqCtx_x3f_1985_; lean_object* v_synthPendingDepth_1986_; lean_object* v_customCanUnfoldPredicate_x3f_1987_; uint8_t v_univApprox_1988_; uint8_t v_inTypeClassResolution_1989_; uint8_t v_cacheInferType_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v_keyedConfig_1980_ = lean_ctor_get(v_a_1922_, 0);
v_trackZetaDelta_1981_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7);
v_zetaDeltaSet_1982_ = lean_ctor_get(v_a_1922_, 1);
v_lctx_1983_ = lean_ctor_get(v_a_1922_, 2);
v_localInstances_1984_ = lean_ctor_get(v_a_1922_, 3);
v_defEqCtx_x3f_1985_ = lean_ctor_get(v_a_1922_, 4);
v_synthPendingDepth_1986_ = lean_ctor_get(v_a_1922_, 5);
v_customCanUnfoldPredicate_x3f_1987_ = lean_ctor_get(v_a_1922_, 6);
v_univApprox_1988_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1989_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7 + 2);
v_cacheInferType_1990_ = lean_ctor_get_uint8(v_a_1922_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1980_);
v___x_1991_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1977_, v_keyedConfig_1980_);
lean_inc(v_customCanUnfoldPredicate_x3f_1987_);
lean_inc(v_synthPendingDepth_1986_);
lean_inc(v_defEqCtx_x3f_1985_);
lean_inc_ref(v_localInstances_1984_);
lean_inc_ref(v_lctx_1983_);
lean_inc(v_zetaDeltaSet_1982_);
v___x_1992_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v_zetaDeltaSet_1982_);
lean_ctor_set(v___x_1992_, 2, v_lctx_1983_);
lean_ctor_set(v___x_1992_, 3, v_localInstances_1984_);
lean_ctor_set(v___x_1992_, 4, v_defEqCtx_x3f_1985_);
lean_ctor_set(v___x_1992_, 5, v_synthPendingDepth_1986_);
lean_ctor_set(v___x_1992_, 6, v_customCanUnfoldPredicate_x3f_1987_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*7, v_trackZetaDelta_1981_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*7 + 1, v_univApprox_1988_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1989_);
lean_ctor_set_uint8(v___x_1992_, sizeof(void*)*7 + 3, v_cacheInferType_1990_);
v___x_1993_ = l_Lean_Meta_isExprDefEq(v_d_1934_, v_a_1974_, v___x_1992_, v_a_1923_, v_a_1924_, v_a_1925_);
lean_dec_ref_known(v___x_1992_, 7);
v___y_1956_ = v___x_1993_;
goto v___jp_1955_;
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
return v___x_1973_;
}
v___jp_1955_:
{
if (lean_obj_tag(v___y_1956_) == 0)
{
lean_object* v_a_1957_; uint8_t v___x_1958_; 
v_a_1957_ = lean_ctor_get(v___y_1956_, 0);
lean_inc(v_a_1957_);
lean_dec_ref_known(v___y_1956_, 1);
v___x_1958_ = lean_unbox(v_a_1957_);
lean_dec(v_a_1957_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_instMVars_1921_);
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
v___x_1959_ = l_Lean_mkAppN(v_f_1915_, v_args_1920_);
lean_dec_ref(v_args_1920_);
lean_inc(v_x_1954_);
v___x_1960_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1959_, v_x_1954_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
return v___x_1960_;
}
else
{
lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1961_ = lean_unsigned_to_nat(1u);
v___x_1962_ = lean_nat_add(v_i_1918_, v___x_1961_);
lean_dec(v_i_1918_);
lean_inc(v_x_1954_);
v___x_1963_ = lean_array_push(v_args_1920_, v_x_1954_);
v_type_1917_ = v_body_1931_;
v_i_1918_ = v___x_1962_;
v_args_1920_ = v___x_1963_;
goto _start;
}
}
else
{
lean_object* v_a_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1972_; 
lean_dec_ref(v_body_1931_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
lean_dec_ref(v_f_1915_);
v_a_1965_ = lean_ctor_get(v___y_1956_, 0);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___y_1956_);
if (v_isSharedCheck_1972_ == 0)
{
v___x_1967_ = v___y_1956_;
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
else
{
lean_inc(v_a_1965_);
lean_dec(v___y_1956_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1972_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1970_; 
if (v_isShared_1968_ == 0)
{
v___x_1970_ = v___x_1967_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v_a_1965_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
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
lean_object* v___x_1994_; lean_object* v_type_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_array_get_size(v_args_1920_);
v_type_1995_ = lean_expr_instantiate_rev_range(v_type_1917_, v_j_1919_, v___x_1994_, v_args_1920_);
lean_dec(v_j_1919_);
lean_dec_ref(v_type_1917_);
v___x_1996_ = l_Lean_Meta_whnfD(v_type_1995_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
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
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_i_1918_);
v___x_1999_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2000_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2001_ = l_Lean_indentExpr(v_f_1915_);
v___x_2002_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2002_, 0, v___x_2000_);
lean_ctor_set(v___x_2002_, 1, v___x_2001_);
v___x_2003_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2004_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2002_);
lean_ctor_set(v___x_2004_, 1, v___x_2003_);
v___x_2005_ = lean_unsigned_to_nat(0u);
v___x_2006_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2007_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1916_, v___x_2005_, v___x_2006_);
v___x_2008_ = l_Lean_indentD(v___x_2007_);
v___x_2009_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2004_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1999_, v___x_2009_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
return v___x_2010_;
}
else
{
v_type_1917_ = v_a_1997_;
v_j_1919_ = v___x_1994_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
lean_dec(v_i_1918_);
lean_dec_ref(v_f_1915_);
return v___x_1996_;
}
}
}
else
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_j_1919_);
lean_dec(v_i_1918_);
lean_dec_ref(v_type_1917_);
v___x_2012_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2013_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2012_, v_f_1915_, v_args_1920_, v_instMVars_1921_, v_a_1922_, v_a_1923_, v_a_1924_, v_a_1925_);
lean_dec_ref(v_instMVars_1921_);
lean_dec_ref(v_args_1920_);
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
v___x_2091_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_2091_, 10, v___x_2089_);
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
lean_object* v_toCold_2227_; lean_object* v_options_2228_; lean_object* v_currRecDepth_2229_; lean_object* v_maxRecDepth_2230_; lean_object* v_ref_2231_; lean_object* v_currNamespace_2232_; lean_object* v_openDecls_2233_; lean_object* v_initHeartbeats_2234_; lean_object* v_maxHeartbeats_2235_; lean_object* v_currMacroScope_2236_; uint8_t v_diag_2237_; uint8_t v_suppressElabErrors_2238_; lean_object* v_ref_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v_toCold_2227_ = lean_ctor_get(v___y_2224_, 0);
v_options_2228_ = lean_ctor_get(v___y_2224_, 1);
v_currRecDepth_2229_ = lean_ctor_get(v___y_2224_, 2);
v_maxRecDepth_2230_ = lean_ctor_get(v___y_2224_, 3);
v_ref_2231_ = lean_ctor_get(v___y_2224_, 4);
v_currNamespace_2232_ = lean_ctor_get(v___y_2224_, 5);
v_openDecls_2233_ = lean_ctor_get(v___y_2224_, 6);
v_initHeartbeats_2234_ = lean_ctor_get(v___y_2224_, 7);
v_maxHeartbeats_2235_ = lean_ctor_get(v___y_2224_, 8);
v_currMacroScope_2236_ = lean_ctor_get(v___y_2224_, 9);
v_diag_2237_ = lean_ctor_get_uint8(v___y_2224_, sizeof(void*)*10);
v_suppressElabErrors_2238_ = lean_ctor_get_uint8(v___y_2224_, sizeof(void*)*10 + 1);
v_ref_2239_ = l_Lean_replaceRef(v_ref_2220_, v_ref_2231_);
lean_inc(v_currMacroScope_2236_);
lean_inc(v_maxHeartbeats_2235_);
lean_inc(v_initHeartbeats_2234_);
lean_inc(v_openDecls_2233_);
lean_inc(v_currNamespace_2232_);
lean_inc(v_maxRecDepth_2230_);
lean_inc(v_currRecDepth_2229_);
lean_inc_ref(v_options_2228_);
lean_inc_ref(v_toCold_2227_);
v___x_2240_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2240_, 0, v_toCold_2227_);
lean_ctor_set(v___x_2240_, 1, v_options_2228_);
lean_ctor_set(v___x_2240_, 2, v_currRecDepth_2229_);
lean_ctor_set(v___x_2240_, 3, v_maxRecDepth_2230_);
lean_ctor_set(v___x_2240_, 4, v_ref_2239_);
lean_ctor_set(v___x_2240_, 5, v_currNamespace_2232_);
lean_ctor_set(v___x_2240_, 6, v_openDecls_2233_);
lean_ctor_set(v___x_2240_, 7, v_initHeartbeats_2234_);
lean_ctor_set(v___x_2240_, 8, v_maxHeartbeats_2235_);
lean_ctor_set(v___x_2240_, 9, v_currMacroScope_2236_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*10, v_diag_2237_);
lean_ctor_set_uint8(v___x_2240_, sizeof(void*)*10 + 1, v_suppressElabErrors_2238_);
v___x_2241_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2221_, v___y_2222_, v___y_2223_, v___x_2240_, v___y_2225_);
lean_dec_ref_known(v___x_2240_, 10);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2242_, lean_object* v_msg_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_res_2249_; 
v_res_2249_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2242_, v_msg_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
lean_dec(v___y_2247_);
lean_dec_ref(v___y_2246_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v_ref_2242_);
return v_res_2249_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2250_, lean_object* v_msg_2251_, lean_object* v_declHint_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v___x_2258_; lean_object* v_a_2259_; lean_object* v___x_2260_; 
v___x_2258_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2251_, v_declHint_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref(v___x_2258_);
v___x_2260_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2250_, v_a_2259_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2261_, lean_object* v_msg_2262_, lean_object* v_declHint_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_res_2269_; 
v_res_2269_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2261_, v_msg_2262_, v_declHint_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v_ref_2261_);
return v_res_2269_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; 
v___x_2271_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2272_ = l_Lean_stringToMessageData(v___x_2271_);
return v___x_2272_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2274_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2275_ = l_Lean_stringToMessageData(v___x_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2276_, lean_object* v_constName_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v___x_2283_; uint8_t v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2283_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2284_ = 0;
lean_inc(v_constName_2277_);
v___x_2285_ = l_Lean_MessageData_ofConstName(v_constName_2277_, v___x_2284_);
v___x_2286_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___x_2283_);
lean_ctor_set(v___x_2286_, 1, v___x_2285_);
v___x_2287_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2286_);
lean_ctor_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2276_, v___x_2288_, v_constName_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2290_, lean_object* v_constName_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2290_, v_constName_2291_, v___y_2292_, v___y_2293_, v___y_2294_, v___y_2295_);
lean_dec(v___y_2295_);
lean_dec_ref(v___y_2294_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v_ref_2290_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_){
_start:
{
lean_object* v_ref_2304_; lean_object* v___x_2305_; 
v_ref_2304_ = lean_ctor_get(v___y_2301_, 4);
v___x_2305_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2304_, v_constName_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_);
return v___x_2305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v___x_2319_; lean_object* v_env_2320_; uint8_t v___x_2321_; lean_object* v___x_2322_; 
v___x_2319_ = lean_st_ref_get(v___y_2317_);
v_env_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc_ref(v_env_2320_);
lean_dec(v___x_2319_);
v___x_2321_ = 0;
lean_inc(v_constName_2313_);
v___x_2322_ = l_Lean_Environment_findConstVal_x3f(v_env_2320_, v_constName_2313_, v___x_2321_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v___x_2323_; 
v___x_2323_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2313_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
return v___x_2323_;
}
else
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2331_; 
lean_dec(v_constName_2313_);
v_val_2324_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2326_ = v___x_2322_;
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v___x_2322_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2331_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v___x_2329_; 
if (v_isShared_2327_ == 0)
{
lean_ctor_set_tag(v___x_2326_, 0);
v___x_2329_ = v___x_2326_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_val_2324_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
return v___x_2329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
lean_dec(v___y_2334_);
lean_dec_ref(v___y_2333_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2345_; 
lean_inc(v_constName_2339_);
v___x_2345_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v_a_2346_; lean_object* v_levelParams_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_a_2346_ = lean_ctor_get(v___x_2345_, 0);
lean_inc(v_a_2346_);
lean_dec_ref_known(v___x_2345_, 1);
v_levelParams_2347_ = lean_ctor_get(v_a_2346_, 1);
v___x_2348_ = lean_box(0);
lean_inc(v_levelParams_2347_);
v___x_2349_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2347_, v___x_2348_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc_n(v_a_2350_, 2);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = l_Lean_mkConst(v_constName_2339_, v_a_2350_);
v___x_2352_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2346_, v_a_2350_, v_a_2343_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2361_; 
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2361_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2357_; lean_object* v___x_2359_; 
v___x_2357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2357_, 0, v___x_2351_);
lean_ctor_set(v___x_2357_, 1, v_a_2353_);
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2357_);
v___x_2359_ = v___x_2355_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v___x_2357_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec_ref(v___x_2351_);
v_a_2362_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2352_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2352_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
lean_dec(v_a_2346_);
lean_dec(v_constName_2339_);
v_a_2370_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2349_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2349_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2380_; uint8_t v_isShared_2381_; uint8_t v_isSharedCheck_2385_; 
lean_dec(v_constName_2339_);
v_a_2378_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2385_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2385_ == 0)
{
v___x_2380_ = v___x_2345_;
v_isShared_2381_ = v_isSharedCheck_2385_;
goto v_resetjp_2379_;
}
else
{
lean_inc(v_a_2378_);
lean_dec(v___x_2345_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2386_, v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2393_, lean_object* v_constName_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_){
_start:
{
lean_object* v___x_2400_; 
v___x_2400_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2394_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2401_, lean_object* v_constName_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_){
_start:
{
lean_object* v_res_2408_; 
v_res_2408_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2401_, v_constName_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
return v_res_2408_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2409_, lean_object* v_ref_2410_, lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2410_, v_constName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_ref_2419_, lean_object* v_constName_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2418_, v_ref_2419_, v_constName_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v_ref_2419_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2427_, lean_object* v_ref_2428_, lean_object* v_msg_2429_, lean_object* v_declHint_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2428_, v_msg_2429_, v_declHint_2430_, v___y_2431_, v___y_2432_, v___y_2433_, v___y_2434_);
return v___x_2436_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2437_, lean_object* v_ref_2438_, lean_object* v_msg_2439_, lean_object* v_declHint_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v_res_2446_; 
v_res_2446_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2437_, v_ref_2438_, v_msg_2439_, v_declHint_2440_, v___y_2441_, v___y_2442_, v___y_2443_, v___y_2444_);
lean_dec(v___y_2444_);
lean_dec_ref(v___y_2443_);
lean_dec(v___y_2442_);
lean_dec_ref(v___y_2441_);
lean_dec(v_ref_2438_);
return v_res_2446_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2447_, lean_object* v_declHint_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2447_, v_declHint_2448_, v___y_2452_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2455_, lean_object* v_declHint_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2455_, v_declHint_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2463_, lean_object* v_ref_2464_, lean_object* v_msg_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2464_, v_msg_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2472_, lean_object* v_ref_2473_, lean_object* v_msg_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
lean_object* v_res_2480_; 
v_res_2480_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2472_, v_ref_2473_, v_msg_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
lean_dec(v___y_2476_);
lean_dec_ref(v___y_2475_);
lean_dec(v_ref_2473_);
return v_res_2480_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2482_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2483_ = l_Lean_stringToMessageData(v___x_2482_);
return v___x_2483_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; 
v___x_2485_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2486_ = l_Lean_stringToMessageData(v___x_2485_);
return v___x_2486_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2487_, lean_object* v_f_2488_, lean_object* v_inst_2489_, lean_object* v_xs_2490_, lean_object* v_x_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; 
v___x_2497_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2498_ = lean_apply_1(v_inst_2487_, v_f_2488_);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_apply_1(v_inst_2489_, v_xs_2490_);
v___x_2503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2504_, 0, v___x_2503_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2505_, lean_object* v_f_2506_, lean_object* v_inst_2507_, lean_object* v_xs_2508_, lean_object* v_x_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2505_, v_f_2506_, v_inst_2507_, v_xs_2508_, v_x_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec_ref(v_x_2509_);
return v_res_2515_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2516_; 
v___x_2516_ = l_instMonadEIO(lean_box(0));
return v___x_2516_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2518_ = l_StateRefT_x27_instMonad___redArg(v___x_2517_);
return v___x_2518_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; 
v___x_2525_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2526_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2527_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2526_, v___x_2525_);
return v___x_2527_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___f_2529_; lean_object* v___x_2530_; 
v___x_2528_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2529_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2530_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2529_, v___x_2528_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2533_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2534_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2535_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2536_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2535_, v___x_2534_, v___x_2533_);
return v___x_2536_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___f_2538_; lean_object* v___f_2539_; lean_object* v___x_2540_; 
v___x_2537_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2538_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2539_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2540_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2539_, v___f_2538_, v___x_2537_);
return v___x_2540_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2541_; 
v___x_2541_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2541_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2543_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2544_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2545_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2544_);
return v___x_2545_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2547_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2546_);
return v___x_2547_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2548_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2549_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2548_);
return v___x_2549_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2560_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2561_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2562_ = l_Lean_Name_append(v___x_2561_, v___x_2560_);
return v___x_2562_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; 
v___x_2568_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2569_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2570_ = l_Lean_Name_append(v___x_2569_, v___x_2568_);
return v___x_2570_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2571_; double v___x_2572_; 
v___x_2571_ = lean_unsigned_to_nat(1000000000u);
v___x_2572_ = lean_float_of_nat(v___x_2571_);
return v___x_2572_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2579_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2580_ = l_Lean_Name_append(v___x_2579_, v___x_2578_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2581_, lean_object* v_inst_2582_, lean_object* v_f_2583_, lean_object* v_xs_2584_, lean_object* v_k_2585_, lean_object* v_a_2586_, lean_object* v_a_2587_, lean_object* v_a_2588_, lean_object* v_a_2589_){
_start:
{
lean_object* v___x_2591_; lean_object* v_toApplicative_2592_; lean_object* v_toFunctor_2593_; lean_object* v_toSeq_2594_; lean_object* v_toSeqLeft_2595_; lean_object* v_toSeqRight_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___f_2600_; lean_object* v___x_2601_; lean_object* v___f_2602_; lean_object* v___f_2603_; lean_object* v___f_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v_toApplicative_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2847_; 
v___x_2591_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2592_ = lean_ctor_get(v___x_2591_, 0);
v_toFunctor_2593_ = lean_ctor_get(v_toApplicative_2592_, 0);
v_toSeq_2594_ = lean_ctor_get(v_toApplicative_2592_, 2);
v_toSeqLeft_2595_ = lean_ctor_get(v_toApplicative_2592_, 3);
v_toSeqRight_2596_ = lean_ctor_get(v_toApplicative_2592_, 4);
v___f_2597_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2598_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2593_, 2);
v___f_2599_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2599_, 0, v_toFunctor_2593_);
v___f_2600_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2600_, 0, v_toFunctor_2593_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___f_2599_);
lean_ctor_set(v___x_2601_, 1, v___f_2600_);
lean_inc(v_toSeqRight_2596_);
v___f_2602_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2602_, 0, v_toSeqRight_2596_);
lean_inc(v_toSeqLeft_2595_);
v___f_2603_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2603_, 0, v_toSeqLeft_2595_);
lean_inc(v_toSeq_2594_);
v___f_2604_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2604_, 0, v_toSeq_2594_);
v___x_2605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2601_);
lean_ctor_set(v___x_2605_, 1, v___f_2597_);
lean_ctor_set(v___x_2605_, 2, v___f_2604_);
lean_ctor_set(v___x_2605_, 3, v___f_2603_);
lean_ctor_set(v___x_2605_, 4, v___f_2602_);
v___x_2606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2605_);
lean_ctor_set(v___x_2606_, 1, v___f_2598_);
v___x_2607_ = l_StateRefT_x27_instMonad___redArg(v___x_2606_);
v_toApplicative_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2847_ == 0)
{
lean_object* v_unused_2848_; 
v_unused_2848_ = lean_ctor_get(v___x_2607_, 1);
lean_dec(v_unused_2848_);
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2847_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_toApplicative_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2847_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_toFunctor_2612_; lean_object* v_toSeq_2613_; lean_object* v_toSeqLeft_2614_; lean_object* v_toSeqRight_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2845_; 
v_toFunctor_2612_ = lean_ctor_get(v_toApplicative_2608_, 0);
v_toSeq_2613_ = lean_ctor_get(v_toApplicative_2608_, 2);
v_toSeqLeft_2614_ = lean_ctor_get(v_toApplicative_2608_, 3);
v_toSeqRight_2615_ = lean_ctor_get(v_toApplicative_2608_, 4);
v_isSharedCheck_2845_ = !lean_is_exclusive(v_toApplicative_2608_);
if (v_isSharedCheck_2845_ == 0)
{
lean_object* v_unused_2846_; 
v_unused_2846_ = lean_ctor_get(v_toApplicative_2608_, 1);
lean_dec(v_unused_2846_);
v___x_2617_ = v_toApplicative_2608_;
v_isShared_2618_ = v_isSharedCheck_2845_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_toSeqRight_2615_);
lean_inc(v_toSeqLeft_2614_);
lean_inc(v_toSeq_2613_);
lean_inc(v_toFunctor_2612_);
lean_dec(v_toApplicative_2608_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2845_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___f_2622_; lean_object* v___x_2623_; lean_object* v___f_2624_; lean_object* v___f_2625_; lean_object* v___f_2626_; lean_object* v___x_2628_; 
v___f_2619_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2620_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2612_);
v___f_2621_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2621_, 0, v_toFunctor_2612_);
v___f_2622_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2622_, 0, v_toFunctor_2612_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___f_2621_);
lean_ctor_set(v___x_2623_, 1, v___f_2622_);
v___f_2624_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2624_, 0, v_toSeqRight_2615_);
v___f_2625_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2625_, 0, v_toSeqLeft_2614_);
v___f_2626_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2626_, 0, v_toSeq_2613_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 4, v___f_2624_);
lean_ctor_set(v___x_2617_, 3, v___f_2625_);
lean_ctor_set(v___x_2617_, 2, v___f_2626_);
lean_ctor_set(v___x_2617_, 1, v___f_2619_);
lean_ctor_set(v___x_2617_, 0, v___x_2623_);
v___x_2628_ = v___x_2617_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2844_, 1, v___f_2619_);
lean_ctor_set(v_reuseFailAlloc_2844_, 2, v___f_2626_);
lean_ctor_set(v_reuseFailAlloc_2844_, 3, v___f_2625_);
lean_ctor_set(v_reuseFailAlloc_2844_, 4, v___f_2624_);
v___x_2628_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
lean_object* v___x_2630_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 1, v___f_2620_);
lean_ctor_set(v___x_2610_, 0, v___x_2628_);
v___x_2630_ = v___x_2610_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2628_);
lean_ctor_set(v_reuseFailAlloc_2843_, 1, v___f_2620_);
v___x_2630_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v_toMonadRef_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_options_2636_; uint8_t v_hasTrace_2637_; 
v___x_2631_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2632_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2633_ = lean_ctor_get(v___x_2632_, 0);
v___x_2634_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2635_ = l_Lean_KVMap_instValueBool;
v_options_2636_ = lean_ctor_get(v_a_2588_, 1);
v_hasTrace_2637_ = lean_ctor_get_uint8(v_options_2636_, sizeof(void*)*1);
if (v_hasTrace_2637_ == 0)
{
lean_object* v___x_2638_; 
lean_dec_ref(v___x_2630_);
lean_dec(v_xs_2584_);
lean_dec(v_f_2583_);
lean_dec_ref(v_inst_2582_);
lean_dec_ref(v_inst_2581_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2638_ = lean_apply_5(v_k_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2638_) == 0)
{
return v___x_2638_;
}
else
{
lean_object* v_a_2639_; uint8_t v___y_2641_; uint8_t v___x_2650_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
v___x_2650_ = l_Lean_Exception_isInterrupt(v_a_2639_);
if (v___x_2650_ == 0)
{
uint8_t v___x_2651_; 
lean_inc(v_a_2639_);
v___x_2651_ = l_Lean_Exception_isRuntime(v_a_2639_);
v___y_2641_ = v___x_2651_;
goto v___jp_2640_;
}
else
{
v___y_2641_ = v___x_2650_;
goto v___jp_2640_;
}
v___jp_2640_:
{
if (v___y_2641_ == 0)
{
lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; 
v_unused_2649_ = lean_ctor_get(v___x_2638_, 0);
lean_dec(v_unused_2649_);
v___x_2643_ = v___x_2638_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_dec(v___x_2638_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2639_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
else
{
lean_dec(v_a_2639_);
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_toCold_2652_; lean_object* v_inheritedTraceOptions_2653_; lean_object* v___x_2654_; lean_object* v___y_2656_; lean_object* v___y_2657_; uint8_t v___y_2658_; lean_object* v___y_2683_; lean_object* v_a_2684_; lean_object* v___f_2687_; lean_object* v___f_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; lean_object* v___y_2694_; lean_object* v___y_2695_; lean_object* v_a_2696_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v_a_2712_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; uint8_t v___y_2718_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v_a_2729_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v_a_2735_; lean_object* v___y_2738_; lean_object* v___y_2739_; lean_object* v_a_2740_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v_a_2753_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; uint8_t v___y_2759_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v_a_2770_; lean_object* v___y_2774_; lean_object* v___y_2775_; lean_object* v_a_2776_; 
v_toCold_2652_ = lean_ctor_get(v_a_2588_, 0);
v_inheritedTraceOptions_2653_ = lean_ctor_get(v_toCold_2652_, 4);
v___x_2654_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2687_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2687_, 0, v_inst_2581_);
lean_closure_set(v___f_2687_, 1, v_f_2583_);
lean_closure_set(v___f_2687_, 2, v_inst_2582_);
lean_closure_set(v___f_2687_, 3, v_xs_2584_);
v___f_2688_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2689_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2691_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2692_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2636_, v___x_2691_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v___x_2815_ = l_Lean_trace_profiler;
v___x_2816_ = l_Lean_Option_get___redArg(v___x_2635_, v_options_2636_, v___x_2815_);
v___x_2817_ = lean_unbox(v___x_2816_);
lean_dec(v___x_2816_);
if (v___x_2817_ == 0)
{
lean_object* v___x_2818_; 
lean_dec_ref(v___f_2687_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2818_ = lean_apply_5(v_k_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2821_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2822_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2636_, v___x_2821_);
if (v___x_2822_ == 0)
{
lean_dec(v_a_2819_);
lean_dec_ref(v___x_2630_);
return v___x_2818_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_8804__overap_2824_; lean_object* v___x_2825_; 
lean_dec_ref_known(v___x_2818_, 1);
lean_inc(v_a_2819_);
v___x_2823_ = l_Lean_MessageData_ofExpr(v_a_2819_);
lean_inc_ref(v_toMonadRef_2633_);
lean_inc_ref(v___x_2630_);
v___x_8804__overap_2824_ = l_Lean_addTrace___redArg(v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, v___x_2820_, v___x_2823_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2825_ = lean_apply_5(v___x_8804__overap_2824_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec_ref(v___x_2630_);
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
v___y_2683_ = v___x_2839_;
v_a_2684_ = v_a_2834_;
goto v___jp_2682_;
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
v___y_2683_ = v___x_2818_;
v_a_2684_ = v_a_2842_;
goto v___jp_2682_;
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
v___jp_2655_:
{
if (v___y_2658_ == 0)
{
lean_object* v___x_2659_; lean_object* v___x_2660_; uint8_t v___x_2661_; 
lean_dec_ref(v___y_2656_);
v___x_2659_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2660_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2636_, v___x_2660_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref(v___x_2630_);
v___x_2662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2662_, 0, v___y_2657_);
return v___x_2662_;
}
else
{
lean_object* v___x_2663_; lean_object* v___x_8579__overap_2664_; lean_object* v___x_2665_; 
lean_inc_ref(v___y_2657_);
v___x_2663_ = l_Lean_Exception_toMessageData(v___y_2657_);
lean_inc_ref(v_toMonadRef_2633_);
v___x_8579__overap_2664_ = l_Lean_addTrace___redArg(v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, v___x_2659_, v___x_2663_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2665_ = lean_apply_5(v___x_8579__overap_2664_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2672_; 
v_isSharedCheck_2672_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2672_ == 0)
{
lean_object* v_unused_2673_; 
v_unused_2673_ = lean_ctor_get(v___x_2665_, 0);
lean_dec(v_unused_2673_);
v___x_2667_ = v___x_2665_;
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v___x_2665_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2672_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2670_; 
if (v_isShared_2668_ == 0)
{
lean_ctor_set_tag(v___x_2667_, 1);
lean_ctor_set(v___x_2667_, 0, v___y_2657_);
v___x_2670_ = v___x_2667_;
goto v_reusejp_2669_;
}
else
{
lean_object* v_reuseFailAlloc_2671_; 
v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2671_, 0, v___y_2657_);
v___x_2670_ = v_reuseFailAlloc_2671_;
goto v_reusejp_2669_;
}
v_reusejp_2669_:
{
return v___x_2670_;
}
}
}
else
{
lean_object* v_a_2674_; lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
lean_dec_ref(v___y_2657_);
v_a_2674_ = lean_ctor_get(v___x_2665_, 0);
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2665_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2676_ = v___x_2665_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_inc(v_a_2674_);
lean_dec(v___x_2665_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2674_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2657_);
lean_dec_ref(v___x_2630_);
return v___y_2656_;
}
}
v___jp_2682_:
{
uint8_t v___x_2685_; 
v___x_2685_ = l_Lean_Exception_isInterrupt(v_a_2684_);
if (v___x_2685_ == 0)
{
uint8_t v___x_2686_; 
lean_inc_ref(v_a_2684_);
v___x_2686_ = l_Lean_Exception_isRuntime(v_a_2684_);
v___y_2656_ = v___y_2683_;
v___y_2657_ = v_a_2684_;
v___y_2658_ = v___x_2686_;
goto v___jp_2655_;
}
else
{
v___y_2656_ = v___y_2683_;
v___y_2657_ = v_a_2684_;
v___y_2658_ = v___x_2685_;
goto v___jp_2655_;
}
}
v___jp_2693_:
{
lean_object* v___x_2697_; double v___x_2698_; double v___x_2699_; double v___x_2700_; double v___x_2701_; double v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_8676__overap_2707_; lean_object* v___x_2708_; 
v___x_2697_ = lean_io_mono_nanos_now();
v___x_2698_ = lean_float_of_nat(v___y_2694_);
v___x_2699_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2700_ = lean_float_div(v___x_2698_, v___x_2699_);
v___x_2701_ = lean_float_of_nat(v___x_2697_);
v___x_2702_ = lean_float_div(v___x_2701_, v___x_2699_);
v___x_2703_ = lean_box_float(v___x_2700_);
v___x_2704_ = lean_box_float(v___x_2702_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2706_, 0, v_a_2696_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_inc_ref(v_toMonadRef_2633_);
v___x_8676__overap_2707_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, lean_box(0), v___x_2634_, v___f_2688_, v___x_2689_, v_hasTrace_2637_, v___x_2690_, v_options_2636_, v___x_2692_, v___y_2695_, v___f_2687_, v___x_2706_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2708_ = lean_apply_5(v___x_8676__overap_2707_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
return v___x_2708_;
}
v___jp_2709_:
{
lean_object* v___x_2713_; 
v___x_2713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2713_, 0, v_a_2712_);
v___y_2694_ = v___y_2710_;
v___y_2695_ = v___y_2711_;
v_a_2696_ = v___x_2713_;
goto v___jp_2693_;
}
v___jp_2714_:
{
if (v___y_2718_ == 0)
{
lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v___x_2721_; 
v___x_2719_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2720_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2636_, v___x_2720_);
if (v___x_2721_ == 0)
{
v___y_2710_ = v___y_2715_;
v___y_2711_ = v___y_2717_;
v_a_2712_ = v___y_2716_;
goto v___jp_2709_;
}
else
{
lean_object* v___x_2722_; lean_object* v___x_8695__overap_2723_; lean_object* v___x_2724_; 
lean_inc_ref(v___y_2716_);
v___x_2722_ = l_Lean_Exception_toMessageData(v___y_2716_);
lean_inc_ref(v_toMonadRef_2633_);
lean_inc_ref(v___x_2630_);
v___x_8695__overap_2723_ = l_Lean_addTrace___redArg(v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, v___x_2719_, v___x_2722_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2724_ = lean_apply_5(v___x_8695__overap_2723_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_dec_ref_known(v___x_2724_, 1);
v___y_2710_ = v___y_2715_;
v___y_2711_ = v___y_2717_;
v_a_2712_ = v___y_2716_;
goto v___jp_2709_;
}
else
{
lean_object* v_a_2725_; 
lean_dec_ref(v___y_2716_);
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
v___y_2710_ = v___y_2715_;
v___y_2711_ = v___y_2717_;
v_a_2712_ = v_a_2725_;
goto v___jp_2709_;
}
}
}
else
{
v___y_2710_ = v___y_2715_;
v___y_2711_ = v___y_2717_;
v_a_2712_ = v___y_2716_;
goto v___jp_2709_;
}
}
v___jp_2726_:
{
uint8_t v___x_2730_; 
v___x_2730_ = l_Lean_Exception_isInterrupt(v_a_2729_);
if (v___x_2730_ == 0)
{
uint8_t v___x_2731_; 
lean_inc_ref(v_a_2729_);
v___x_2731_ = l_Lean_Exception_isRuntime(v_a_2729_);
v___y_2715_ = v___y_2727_;
v___y_2716_ = v_a_2729_;
v___y_2717_ = v___y_2728_;
v___y_2718_ = v___x_2731_;
goto v___jp_2714_;
}
else
{
v___y_2715_ = v___y_2727_;
v___y_2716_ = v_a_2729_;
v___y_2717_ = v___y_2728_;
v___y_2718_ = v___x_2730_;
goto v___jp_2714_;
}
}
v___jp_2732_:
{
lean_object* v___x_2736_; 
v___x_2736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2736_, 0, v_a_2735_);
v___y_2694_ = v___y_2733_;
v___y_2695_ = v___y_2734_;
v_a_2696_ = v___x_2736_;
goto v___jp_2693_;
}
v___jp_2737_:
{
lean_object* v___x_2741_; double v___x_2742_; double v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_8738__overap_2748_; lean_object* v___x_2749_; 
v___x_2741_ = lean_io_get_num_heartbeats();
v___x_2742_ = lean_float_of_nat(v___y_2738_);
v___x_2743_ = lean_float_of_nat(v___x_2741_);
v___x_2744_ = lean_box_float(v___x_2742_);
v___x_2745_ = lean_box_float(v___x_2743_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v___x_2744_);
lean_ctor_set(v___x_2746_, 1, v___x_2745_);
v___x_2747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2747_, 0, v_a_2740_);
lean_ctor_set(v___x_2747_, 1, v___x_2746_);
lean_inc_ref(v_toMonadRef_2633_);
v___x_8738__overap_2748_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, lean_box(0), v___x_2634_, v___f_2688_, v___x_2689_, v_hasTrace_2637_, v___x_2690_, v_options_2636_, v___x_2692_, v___y_2739_, v___f_2687_, v___x_2747_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2749_ = lean_apply_5(v___x_8738__overap_2748_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
return v___x_2749_;
}
v___jp_2750_:
{
lean_object* v___x_2754_; 
v___x_2754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2754_, 0, v_a_2753_);
v___y_2738_ = v___y_2751_;
v___y_2739_ = v___y_2752_;
v_a_2740_ = v___x_2754_;
goto v___jp_2737_;
}
v___jp_2755_:
{
if (v___y_2759_ == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; uint8_t v___x_2762_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2761_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2762_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2636_, v___x_2761_);
if (v___x_2762_ == 0)
{
v___y_2751_ = v___y_2756_;
v___y_2752_ = v___y_2757_;
v_a_2753_ = v___y_2758_;
goto v___jp_2750_;
}
else
{
lean_object* v___x_2763_; lean_object* v___x_8757__overap_2764_; lean_object* v___x_2765_; 
lean_inc_ref(v___y_2758_);
v___x_2763_ = l_Lean_Exception_toMessageData(v___y_2758_);
lean_inc_ref(v_toMonadRef_2633_);
lean_inc_ref(v___x_2630_);
v___x_8757__overap_2764_ = l_Lean_addTrace___redArg(v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, v___x_2760_, v___x_2763_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2765_ = lean_apply_5(v___x_8757__overap_2764_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2765_) == 0)
{
lean_dec_ref_known(v___x_2765_, 1);
v___y_2751_ = v___y_2756_;
v___y_2752_ = v___y_2757_;
v_a_2753_ = v___y_2758_;
goto v___jp_2750_;
}
else
{
lean_object* v_a_2766_; 
lean_dec_ref(v___y_2758_);
v_a_2766_ = lean_ctor_get(v___x_2765_, 0);
lean_inc(v_a_2766_);
lean_dec_ref_known(v___x_2765_, 1);
v___y_2751_ = v___y_2756_;
v___y_2752_ = v___y_2757_;
v_a_2753_ = v_a_2766_;
goto v___jp_2750_;
}
}
}
else
{
v___y_2751_ = v___y_2756_;
v___y_2752_ = v___y_2757_;
v_a_2753_ = v___y_2758_;
goto v___jp_2750_;
}
}
v___jp_2767_:
{
uint8_t v___x_2771_; 
v___x_2771_ = l_Lean_Exception_isInterrupt(v_a_2770_);
if (v___x_2771_ == 0)
{
uint8_t v___x_2772_; 
lean_inc_ref(v_a_2770_);
v___x_2772_ = l_Lean_Exception_isRuntime(v_a_2770_);
v___y_2756_ = v___y_2768_;
v___y_2757_ = v___y_2769_;
v___y_2758_ = v_a_2770_;
v___y_2759_ = v___x_2772_;
goto v___jp_2755_;
}
else
{
v___y_2756_ = v___y_2768_;
v___y_2757_ = v___y_2769_;
v___y_2758_ = v_a_2770_;
v___y_2759_ = v___x_2771_;
goto v___jp_2755_;
}
}
v___jp_2773_:
{
lean_object* v___x_2777_; 
v___x_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2777_, 0, v_a_2776_);
v___y_2738_ = v___y_2774_;
v___y_2739_ = v___y_2775_;
v_a_2740_ = v___x_2777_;
goto v___jp_2737_;
}
v___jp_2778_:
{
lean_object* v___x_8654__overap_2779_; lean_object* v___x_2780_; 
lean_inc_ref(v___x_2630_);
v___x_8654__overap_2779_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2630_, v___x_2631_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2780_ = lean_apply_5(v___x_8654__overap_2779_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2783_ = l_Lean_Option_get___redArg(v___x_2635_, v_options_2636_, v___x_2782_);
v___x_2784_ = lean_unbox(v___x_2783_);
lean_dec(v___x_2783_);
if (v___x_2784_ == 0)
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = lean_io_mono_nanos_now();
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2786_ = lean_apply_5(v_k_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2786_) == 0)
{
lean_object* v_a_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; uint8_t v___x_2790_; 
v_a_2787_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2787_);
lean_dec_ref_known(v___x_2786_, 1);
v___x_2788_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2789_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2636_, v___x_2789_);
if (v___x_2790_ == 0)
{
v___y_2733_ = v___x_2785_;
v___y_2734_ = v_a_2781_;
v_a_2735_ = v_a_2787_;
goto v___jp_2732_;
}
else
{
lean_object* v___x_2791_; lean_object* v___x_8718__overap_2792_; lean_object* v___x_2793_; 
lean_inc(v_a_2787_);
v___x_2791_ = l_Lean_MessageData_ofExpr(v_a_2787_);
lean_inc_ref(v_toMonadRef_2633_);
lean_inc_ref(v___x_2630_);
v___x_8718__overap_2792_ = l_Lean_addTrace___redArg(v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, v___x_2788_, v___x_2791_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2793_ = lean_apply_5(v___x_8718__overap_2792_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2793_) == 0)
{
lean_dec_ref_known(v___x_2793_, 1);
v___y_2733_ = v___x_2785_;
v___y_2734_ = v_a_2781_;
v_a_2735_ = v_a_2787_;
goto v___jp_2732_;
}
else
{
lean_object* v_a_2794_; 
lean_dec(v_a_2787_);
v_a_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v___x_2793_, 1);
v___y_2727_ = v___x_2785_;
v___y_2728_ = v_a_2781_;
v_a_2729_ = v_a_2794_;
goto v___jp_2726_;
}
}
}
else
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___x_2786_, 0);
lean_inc(v_a_2795_);
lean_dec_ref_known(v___x_2786_, 1);
v___y_2727_ = v___x_2785_;
v___y_2728_ = v_a_2781_;
v_a_2729_ = v_a_2795_;
goto v___jp_2726_;
}
}
else
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2797_ = lean_apply_5(v_k_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2800_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2801_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2653_, v_options_2636_, v___x_2800_);
if (v___x_2801_ == 0)
{
v___y_2774_ = v___x_2796_;
v___y_2775_ = v_a_2781_;
v_a_2776_ = v_a_2798_;
goto v___jp_2773_;
}
else
{
lean_object* v___x_2802_; lean_object* v___x_8780__overap_2803_; lean_object* v___x_2804_; 
lean_inc(v_a_2798_);
v___x_2802_ = l_Lean_MessageData_ofExpr(v_a_2798_);
lean_inc_ref(v_toMonadRef_2633_);
lean_inc_ref(v___x_2630_);
v___x_8780__overap_2803_ = l_Lean_addTrace___redArg(v___x_2630_, v___x_2631_, v_toMonadRef_2633_, v___x_2654_, v___x_2799_, v___x_2802_);
lean_inc(v_a_2589_);
lean_inc_ref(v_a_2588_);
lean_inc(v_a_2587_);
lean_inc_ref(v_a_2586_);
v___x_2804_ = lean_apply_5(v___x_8780__overap_2803_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_, lean_box(0));
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_dec_ref_known(v___x_2804_, 1);
v___y_2774_ = v___x_2796_;
v___y_2775_ = v_a_2781_;
v_a_2776_ = v_a_2798_;
goto v___jp_2773_;
}
else
{
lean_object* v_a_2805_; 
lean_dec(v_a_2798_);
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___y_2768_ = v___x_2796_;
v___y_2769_ = v_a_2781_;
v_a_2770_ = v_a_2805_;
goto v___jp_2767_;
}
}
}
else
{
lean_object* v_a_2806_; 
v_a_2806_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2797_, 1);
v___y_2768_ = v___x_2796_;
v___y_2769_ = v_a_2781_;
v_a_2770_ = v_a_2806_;
goto v___jp_2767_;
}
}
}
else
{
lean_object* v_a_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2814_; 
lean_dec_ref(v___f_2687_);
lean_dec_ref(v___x_2630_);
lean_dec_ref(v_k_2585_);
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
lean_object* v___x_2977_; lean_object* v_traceState_2978_; lean_object* v_traces_2979_; lean_object* v___x_2980_; lean_object* v_traceState_2981_; lean_object* v_env_2982_; lean_object* v_nextMacroScope_2983_; lean_object* v_ngen_2984_; lean_object* v_auxDeclNGen_2985_; lean_object* v_cache_2986_; lean_object* v_messages_2987_; lean_object* v_infoState_2988_; lean_object* v_snapshotTasks_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3008_; 
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
v_messages_2987_ = lean_ctor_get(v___x_2980_, 6);
v_infoState_2988_ = lean_ctor_get(v___x_2980_, 7);
v_snapshotTasks_2989_ = lean_ctor_get(v___x_2980_, 8);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2991_ = v___x_2980_;
v_isShared_2992_ = v_isSharedCheck_3008_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_snapshotTasks_2989_);
lean_inc(v_infoState_2988_);
lean_inc(v_messages_2987_);
lean_inc(v_cache_2986_);
lean_inc(v_traceState_2981_);
lean_inc(v_auxDeclNGen_2985_);
lean_inc(v_ngen_2984_);
lean_inc(v_nextMacroScope_2983_);
lean_inc(v_env_2982_);
lean_dec(v___x_2980_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3008_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
uint64_t v_tid_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3006_; 
v_tid_2993_ = lean_ctor_get_uint64(v_traceState_2981_, sizeof(void*)*1);
v_isSharedCheck_3006_ = !lean_is_exclusive(v_traceState_2981_);
if (v_isSharedCheck_3006_ == 0)
{
lean_object* v_unused_3007_; 
v_unused_3007_ = lean_ctor_get(v_traceState_2981_, 0);
lean_dec(v_unused_3007_);
v___x_2995_ = v_traceState_2981_;
v_isShared_2996_ = v_isSharedCheck_3006_;
goto v_resetjp_2994_;
}
else
{
lean_dec(v_traceState_2981_);
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
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_env_2982_);
lean_ctor_set(v_reuseFailAlloc_3004_, 1, v_nextMacroScope_2983_);
lean_ctor_set(v_reuseFailAlloc_3004_, 2, v_ngen_2984_);
lean_ctor_set(v_reuseFailAlloc_3004_, 3, v_auxDeclNGen_2985_);
lean_ctor_set(v_reuseFailAlloc_3004_, 4, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3004_, 5, v_cache_2986_);
lean_ctor_set(v_reuseFailAlloc_3004_, 6, v_messages_2987_);
lean_ctor_set(v_reuseFailAlloc_3004_, 7, v_infoState_2988_);
lean_ctor_set(v_reuseFailAlloc_3004_, 8, v_snapshotTasks_2989_);
v___x_3001_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_st_ref_put(v___y_2975_, v___x_3001_);
v___x_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3003_, 0, v_traces_2979_);
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
lean_object* v_toCold_3073_; lean_object* v_options_3074_; lean_object* v_currRecDepth_3075_; lean_object* v_maxRecDepth_3076_; lean_object* v_ref_3077_; lean_object* v_currNamespace_3078_; lean_object* v_openDecls_3079_; lean_object* v_initHeartbeats_3080_; lean_object* v_maxHeartbeats_3081_; lean_object* v_currMacroScope_3082_; uint8_t v_diag_3083_; uint8_t v_suppressElabErrors_3084_; lean_object* v___x_3085_; lean_object* v_traceState_3086_; lean_object* v_traces_3087_; lean_object* v_ref_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; size_t v_sz_3091_; size_t v___x_3092_; lean_object* v___x_3093_; lean_object* v_msg_3094_; lean_object* v___x_3095_; lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3133_; 
v_toCold_3073_ = lean_ctor_get(v___y_3070_, 0);
v_options_3074_ = lean_ctor_get(v___y_3070_, 1);
v_currRecDepth_3075_ = lean_ctor_get(v___y_3070_, 2);
v_maxRecDepth_3076_ = lean_ctor_get(v___y_3070_, 3);
v_ref_3077_ = lean_ctor_get(v___y_3070_, 4);
v_currNamespace_3078_ = lean_ctor_get(v___y_3070_, 5);
v_openDecls_3079_ = lean_ctor_get(v___y_3070_, 6);
v_initHeartbeats_3080_ = lean_ctor_get(v___y_3070_, 7);
v_maxHeartbeats_3081_ = lean_ctor_get(v___y_3070_, 8);
v_currMacroScope_3082_ = lean_ctor_get(v___y_3070_, 9);
v_diag_3083_ = lean_ctor_get_uint8(v___y_3070_, sizeof(void*)*10);
v_suppressElabErrors_3084_ = lean_ctor_get_uint8(v___y_3070_, sizeof(void*)*10 + 1);
v___x_3085_ = lean_st_ref_get(v___y_3071_);
v_traceState_3086_ = lean_ctor_get(v___x_3085_, 4);
lean_inc_ref(v_traceState_3086_);
lean_dec(v___x_3085_);
v_traces_3087_ = lean_ctor_get(v_traceState_3086_, 0);
lean_inc_ref(v_traces_3087_);
lean_dec_ref(v_traceState_3086_);
v_ref_3088_ = l_Lean_replaceRef(v_ref_3066_, v_ref_3077_);
lean_inc(v_currMacroScope_3082_);
lean_inc(v_maxHeartbeats_3081_);
lean_inc(v_initHeartbeats_3080_);
lean_inc(v_openDecls_3079_);
lean_inc(v_currNamespace_3078_);
lean_inc(v_maxRecDepth_3076_);
lean_inc(v_currRecDepth_3075_);
lean_inc_ref(v_options_3074_);
lean_inc_ref(v_toCold_3073_);
v___x_3089_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3089_, 0, v_toCold_3073_);
lean_ctor_set(v___x_3089_, 1, v_options_3074_);
lean_ctor_set(v___x_3089_, 2, v_currRecDepth_3075_);
lean_ctor_set(v___x_3089_, 3, v_maxRecDepth_3076_);
lean_ctor_set(v___x_3089_, 4, v_ref_3088_);
lean_ctor_set(v___x_3089_, 5, v_currNamespace_3078_);
lean_ctor_set(v___x_3089_, 6, v_openDecls_3079_);
lean_ctor_set(v___x_3089_, 7, v_initHeartbeats_3080_);
lean_ctor_set(v___x_3089_, 8, v_maxHeartbeats_3081_);
lean_ctor_set(v___x_3089_, 9, v_currMacroScope_3082_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*10, v_diag_3083_);
lean_ctor_set_uint8(v___x_3089_, sizeof(void*)*10 + 1, v_suppressElabErrors_3084_);
v___x_3090_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3087_);
lean_dec_ref(v_traces_3087_);
v_sz_3091_ = lean_array_size(v___x_3090_);
v___x_3092_ = ((size_t)0ULL);
v___x_3093_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3091_, v___x_3092_, v___x_3090_);
v_msg_3094_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3094_, 0, v_data_3065_);
lean_ctor_set(v_msg_3094_, 1, v_msg_3067_);
lean_ctor_set(v_msg_3094_, 2, v___x_3093_);
v___x_3095_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3094_, v___y_3068_, v___y_3069_, v___x_3089_, v___y_3071_);
lean_dec_ref_known(v___x_3089_, 10);
v_a_3096_ = lean_ctor_get(v___x_3095_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3095_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3098_ = v___x_3095_;
v_isShared_3099_ = v_isSharedCheck_3133_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v___x_3095_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3133_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3100_; lean_object* v_traceState_3101_; lean_object* v_env_3102_; lean_object* v_nextMacroScope_3103_; lean_object* v_ngen_3104_; lean_object* v_auxDeclNGen_3105_; lean_object* v_cache_3106_; lean_object* v_messages_3107_; lean_object* v_infoState_3108_; lean_object* v_snapshotTasks_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3132_; 
v___x_3100_ = lean_st_ref_take(v___y_3071_);
v_traceState_3101_ = lean_ctor_get(v___x_3100_, 4);
v_env_3102_ = lean_ctor_get(v___x_3100_, 0);
v_nextMacroScope_3103_ = lean_ctor_get(v___x_3100_, 1);
v_ngen_3104_ = lean_ctor_get(v___x_3100_, 2);
v_auxDeclNGen_3105_ = lean_ctor_get(v___x_3100_, 3);
v_cache_3106_ = lean_ctor_get(v___x_3100_, 5);
v_messages_3107_ = lean_ctor_get(v___x_3100_, 6);
v_infoState_3108_ = lean_ctor_get(v___x_3100_, 7);
v_snapshotTasks_3109_ = lean_ctor_get(v___x_3100_, 8);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3100_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3111_ = v___x_3100_;
v_isShared_3112_ = v_isSharedCheck_3132_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_snapshotTasks_3109_);
lean_inc(v_infoState_3108_);
lean_inc(v_messages_3107_);
lean_inc(v_cache_3106_);
lean_inc(v_traceState_3101_);
lean_inc(v_auxDeclNGen_3105_);
lean_inc(v_ngen_3104_);
lean_inc(v_nextMacroScope_3103_);
lean_inc(v_env_3102_);
lean_dec(v___x_3100_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3132_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
uint64_t v_tid_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3130_; 
v_tid_3113_ = lean_ctor_get_uint64(v_traceState_3101_, sizeof(void*)*1);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_traceState_3101_);
if (v_isSharedCheck_3130_ == 0)
{
lean_object* v_unused_3131_; 
v_unused_3131_ = lean_ctor_get(v_traceState_3101_, 0);
lean_dec(v_unused_3131_);
v___x_3115_ = v_traceState_3101_;
v_isShared_3116_ = v_isSharedCheck_3130_;
goto v_resetjp_3114_;
}
else
{
lean_dec(v_traceState_3101_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3130_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3120_; 
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v_ref_3066_);
lean_ctor_set(v___x_3117_, 1, v_a_3096_);
v___x_3118_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3064_, v___x_3117_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 0, v___x_3118_);
v___x_3120_ = v___x_3115_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3118_);
lean_ctor_set_uint64(v_reuseFailAlloc_3129_, sizeof(void*)*1, v_tid_3113_);
v___x_3120_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
lean_object* v___x_3122_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set(v___x_3111_, 4, v___x_3120_);
v___x_3122_ = v___x_3111_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3128_; 
v_reuseFailAlloc_3128_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3128_, 0, v_env_3102_);
lean_ctor_set(v_reuseFailAlloc_3128_, 1, v_nextMacroScope_3103_);
lean_ctor_set(v_reuseFailAlloc_3128_, 2, v_ngen_3104_);
lean_ctor_set(v_reuseFailAlloc_3128_, 3, v_auxDeclNGen_3105_);
lean_ctor_set(v_reuseFailAlloc_3128_, 4, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3128_, 5, v_cache_3106_);
lean_ctor_set(v_reuseFailAlloc_3128_, 6, v_messages_3107_);
lean_ctor_set(v_reuseFailAlloc_3128_, 7, v_infoState_3108_);
lean_ctor_set(v_reuseFailAlloc_3128_, 8, v_snapshotTasks_3109_);
v___x_3122_ = v_reuseFailAlloc_3128_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
lean_object* v___x_3123_; lean_object* v___x_3124_; lean_object* v___x_3126_; 
v___x_3123_ = lean_st_ref_put(v___y_3071_, v___x_3122_);
v___x_3124_ = lean_box(0);
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 0, v___x_3124_);
v___x_3126_ = v___x_3098_;
goto v_reusejp_3125_;
}
else
{
lean_object* v_reuseFailAlloc_3127_; 
v_reuseFailAlloc_3127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3127_, 0, v___x_3124_);
v___x_3126_ = v_reuseFailAlloc_3127_;
goto v_reusejp_3125_;
}
v_reusejp_3125_:
{
return v___x_3126_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3134_, lean_object* v_data_3135_, lean_object* v_ref_3136_, lean_object* v_msg_3137_, lean_object* v___y_3138_, lean_object* v___y_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3134_, v_data_3135_, v_ref_3136_, v_msg_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_);
lean_dec(v___y_3141_);
lean_dec_ref(v___y_3140_);
lean_dec(v___y_3139_);
lean_dec_ref(v___y_3138_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3144_){
_start:
{
if (lean_obj_tag(v_x_3144_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3153_; 
v_a_3146_ = lean_ctor_get(v_x_3144_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_x_3144_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_3148_ = v_x_3144_;
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v_x_3144_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3153_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v___x_3151_; 
if (v_isShared_3149_ == 0)
{
lean_ctor_set_tag(v___x_3148_, 1);
v___x_3151_ = v___x_3148_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_a_3146_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
else
{
lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
v_a_3154_ = lean_ctor_get(v_x_3144_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v_x_3144_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v_x_3144_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v_x_3144_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
lean_ctor_set_tag(v___x_3156_, 0);
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3162_);
return v_res_3164_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3165_; double v___x_3166_; 
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = lean_float_of_nat(v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3169_ = l_Lean_stringToMessageData(v___x_3168_);
return v___x_3169_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3170_; double v___x_3171_; 
v___x_3170_ = lean_unsigned_to_nat(1000u);
v___x_3171_ = lean_float_of_nat(v___x_3170_);
return v___x_3171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3172_, uint8_t v_collapsed_3173_, lean_object* v_tag_3174_, lean_object* v_opts_3175_, uint8_t v_clsEnabled_3176_, lean_object* v_oldTraces_3177_, lean_object* v_msg_3178_, lean_object* v_resStartStop_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_){
_start:
{
lean_object* v_fst_3185_; lean_object* v_snd_3186_; lean_object* v___y_3188_; lean_object* v___y_3189_; lean_object* v_data_3190_; lean_object* v_fst_3201_; lean_object* v_snd_3202_; lean_object* v___x_3203_; uint8_t v___x_3204_; lean_object* v___y_3206_; lean_object* v_a_3207_; uint8_t v___y_3222_; double v___y_3253_; 
v_fst_3185_ = lean_ctor_get(v_resStartStop_3179_, 0);
lean_inc(v_fst_3185_);
v_snd_3186_ = lean_ctor_get(v_resStartStop_3179_, 1);
lean_inc(v_snd_3186_);
lean_dec_ref(v_resStartStop_3179_);
v_fst_3201_ = lean_ctor_get(v_snd_3186_, 0);
lean_inc(v_fst_3201_);
v_snd_3202_ = lean_ctor_get(v_snd_3186_, 1);
lean_inc(v_snd_3202_);
lean_dec(v_snd_3186_);
v___x_3203_ = l_Lean_trace_profiler;
v___x_3204_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3175_, v___x_3203_);
if (v___x_3204_ == 0)
{
v___y_3222_ = v___x_3204_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3258_; uint8_t v___x_3259_; 
v___x_3258_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3259_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3175_, v___x_3258_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; double v___x_3262_; double v___x_3263_; double v___x_3264_; 
v___x_3260_ = l_Lean_trace_profiler_threshold;
v___x_3261_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3175_, v___x_3260_);
v___x_3262_ = lean_float_of_nat(v___x_3261_);
v___x_3263_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3264_ = lean_float_div(v___x_3262_, v___x_3263_);
v___y_3253_ = v___x_3264_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3265_; lean_object* v___x_3266_; double v___x_3267_; 
v___x_3265_ = l_Lean_trace_profiler_threshold;
v___x_3266_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3175_, v___x_3265_);
v___x_3267_ = lean_float_of_nat(v___x_3266_);
v___y_3253_ = v___x_3267_;
goto v___jp_3252_;
}
}
v___jp_3187_:
{
lean_object* v___x_3191_; 
lean_inc(v___y_3188_);
v___x_3191_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3177_, v_data_3190_, v___y_3188_, v___y_3189_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v___x_3192_; 
lean_dec_ref_known(v___x_3191_, 1);
v___x_3192_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3185_);
return v___x_3192_;
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_dec(v_fst_3185_);
v_a_3193_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3191_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3191_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
v___jp_3205_:
{
uint8_t v_result_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; double v___x_3211_; lean_object* v_data_3212_; 
v_result_3208_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3185_);
v___x_3209_ = lean_box(v_result_3208_);
v___x_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3210_, 0, v___x_3209_);
v___x_3211_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3174_);
lean_inc_ref(v___x_3210_);
lean_inc(v_cls_3172_);
v_data_3212_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3212_, 0, v_cls_3172_);
lean_ctor_set(v_data_3212_, 1, v___x_3210_);
lean_ctor_set(v_data_3212_, 2, v_tag_3174_);
lean_ctor_set_float(v_data_3212_, sizeof(void*)*3, v___x_3211_);
lean_ctor_set_float(v_data_3212_, sizeof(void*)*3 + 8, v___x_3211_);
lean_ctor_set_uint8(v_data_3212_, sizeof(void*)*3 + 16, v_collapsed_3173_);
if (v___x_3204_ == 0)
{
lean_dec_ref_known(v___x_3210_, 1);
lean_dec(v_snd_3202_);
lean_dec(v_fst_3201_);
lean_dec_ref(v_tag_3174_);
lean_dec(v_cls_3172_);
v___y_3188_ = v___y_3206_;
v___y_3189_ = v_a_3207_;
v_data_3190_ = v_data_3212_;
goto v___jp_3187_;
}
else
{
lean_object* v_data_3213_; double v___x_3214_; double v___x_3215_; 
lean_dec_ref_known(v_data_3212_, 3);
v_data_3213_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3213_, 0, v_cls_3172_);
lean_ctor_set(v_data_3213_, 1, v___x_3210_);
lean_ctor_set(v_data_3213_, 2, v_tag_3174_);
v___x_3214_ = lean_unbox_float(v_fst_3201_);
lean_dec(v_fst_3201_);
lean_ctor_set_float(v_data_3213_, sizeof(void*)*3, v___x_3214_);
v___x_3215_ = lean_unbox_float(v_snd_3202_);
lean_dec(v_snd_3202_);
lean_ctor_set_float(v_data_3213_, sizeof(void*)*3 + 8, v___x_3215_);
lean_ctor_set_uint8(v_data_3213_, sizeof(void*)*3 + 16, v_collapsed_3173_);
v___y_3188_ = v___y_3206_;
v___y_3189_ = v_a_3207_;
v_data_3190_ = v_data_3213_;
goto v___jp_3187_;
}
}
v___jp_3216_:
{
lean_object* v_ref_3217_; lean_object* v___x_3218_; 
v_ref_3217_ = lean_ctor_get(v___y_3182_, 4);
lean_inc(v___y_3183_);
lean_inc_ref(v___y_3182_);
lean_inc(v___y_3181_);
lean_inc_ref(v___y_3180_);
lean_inc(v_fst_3185_);
v___x_3218_ = lean_apply_6(v_msg_3178_, v_fst_3185_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_, lean_box(0));
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___y_3206_ = v_ref_3217_;
v_a_3207_ = v_a_3219_;
goto v___jp_3205_;
}
else
{
lean_object* v___x_3220_; 
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3206_ = v_ref_3217_;
v_a_3207_ = v___x_3220_;
goto v___jp_3205_;
}
}
v___jp_3221_:
{
if (v_clsEnabled_3176_ == 0)
{
if (v___y_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v_traceState_3224_; lean_object* v_env_3225_; lean_object* v_nextMacroScope_3226_; lean_object* v_ngen_3227_; lean_object* v_auxDeclNGen_3228_; lean_object* v_cache_3229_; lean_object* v_messages_3230_; lean_object* v_infoState_3231_; lean_object* v_snapshotTasks_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3251_; 
lean_dec(v_snd_3202_);
lean_dec(v_fst_3201_);
lean_dec_ref(v_msg_3178_);
lean_dec_ref(v_tag_3174_);
lean_dec(v_cls_3172_);
v___x_3223_ = lean_st_ref_take(v___y_3183_);
v_traceState_3224_ = lean_ctor_get(v___x_3223_, 4);
v_env_3225_ = lean_ctor_get(v___x_3223_, 0);
v_nextMacroScope_3226_ = lean_ctor_get(v___x_3223_, 1);
v_ngen_3227_ = lean_ctor_get(v___x_3223_, 2);
v_auxDeclNGen_3228_ = lean_ctor_get(v___x_3223_, 3);
v_cache_3229_ = lean_ctor_get(v___x_3223_, 5);
v_messages_3230_ = lean_ctor_get(v___x_3223_, 6);
v_infoState_3231_ = lean_ctor_get(v___x_3223_, 7);
v_snapshotTasks_3232_ = lean_ctor_get(v___x_3223_, 8);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3234_ = v___x_3223_;
v_isShared_3235_ = v_isSharedCheck_3251_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_snapshotTasks_3232_);
lean_inc(v_infoState_3231_);
lean_inc(v_messages_3230_);
lean_inc(v_cache_3229_);
lean_inc(v_traceState_3224_);
lean_inc(v_auxDeclNGen_3228_);
lean_inc(v_ngen_3227_);
lean_inc(v_nextMacroScope_3226_);
lean_inc(v_env_3225_);
lean_dec(v___x_3223_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3251_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
uint64_t v_tid_3236_; lean_object* v_traces_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3250_; 
v_tid_3236_ = lean_ctor_get_uint64(v_traceState_3224_, sizeof(void*)*1);
v_traces_3237_ = lean_ctor_get(v_traceState_3224_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v_traceState_3224_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3239_ = v_traceState_3224_;
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_traces_3237_);
lean_dec(v_traceState_3224_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3250_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3241_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3177_, v_traces_3237_);
lean_dec_ref(v_traces_3237_);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 0, v___x_3241_);
v___x_3243_ = v___x_3239_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3241_);
lean_ctor_set_uint64(v_reuseFailAlloc_3249_, sizeof(void*)*1, v_tid_3236_);
v___x_3243_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3245_; 
if (v_isShared_3235_ == 0)
{
lean_ctor_set(v___x_3234_, 4, v___x_3243_);
v___x_3245_ = v___x_3234_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_env_3225_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_nextMacroScope_3226_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_ngen_3227_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v_auxDeclNGen_3228_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3248_, 5, v_cache_3229_);
lean_ctor_set(v_reuseFailAlloc_3248_, 6, v_messages_3230_);
lean_ctor_set(v_reuseFailAlloc_3248_, 7, v_infoState_3231_);
lean_ctor_set(v_reuseFailAlloc_3248_, 8, v_snapshotTasks_3232_);
v___x_3245_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = lean_st_ref_put(v___y_3183_, v___x_3245_);
v___x_3247_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3185_);
return v___x_3247_;
}
}
}
}
}
else
{
goto v___jp_3216_;
}
}
else
{
goto v___jp_3216_;
}
}
v___jp_3252_:
{
double v___x_3254_; double v___x_3255_; double v___x_3256_; uint8_t v___x_3257_; 
v___x_3254_ = lean_unbox_float(v_snd_3202_);
v___x_3255_ = lean_unbox_float(v_fst_3201_);
v___x_3256_ = lean_float_sub(v___x_3254_, v___x_3255_);
v___x_3257_ = lean_float_decLt(v___y_3253_, v___x_3256_);
v___y_3222_ = v___x_3257_;
goto v___jp_3221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3268_, lean_object* v_collapsed_3269_, lean_object* v_tag_3270_, lean_object* v_opts_3271_, lean_object* v_clsEnabled_3272_, lean_object* v_oldTraces_3273_, lean_object* v_msg_3274_, lean_object* v_resStartStop_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
uint8_t v_collapsed_boxed_3281_; uint8_t v_clsEnabled_boxed_3282_; lean_object* v_res_3283_; 
v_collapsed_boxed_3281_ = lean_unbox(v_collapsed_3269_);
v_clsEnabled_boxed_3282_ = lean_unbox(v_clsEnabled_3272_);
v_res_3283_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3268_, v_collapsed_boxed_3281_, v_tag_3270_, v_opts_3271_, v_clsEnabled_boxed_3282_, v_oldTraces_3273_, v_msg_3274_, v_resStartStop_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
lean_dec(v___y_3277_);
lean_dec_ref(v___y_3276_);
lean_dec_ref(v_opts_3271_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3284_, lean_object* v_a_3285_){
_start:
{
if (lean_obj_tag(v_a_3284_) == 0)
{
lean_object* v___x_3286_; 
v___x_3286_ = l_List_reverse___redArg(v_a_3285_);
return v___x_3286_;
}
else
{
lean_object* v_head_3287_; lean_object* v_tail_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3297_; 
v_head_3287_ = lean_ctor_get(v_a_3284_, 0);
v_tail_3288_ = lean_ctor_get(v_a_3284_, 1);
v_isSharedCheck_3297_ = !lean_is_exclusive(v_a_3284_);
if (v_isSharedCheck_3297_ == 0)
{
v___x_3290_ = v_a_3284_;
v_isShared_3291_ = v_isSharedCheck_3297_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_tail_3288_);
lean_inc(v_head_3287_);
lean_dec(v_a_3284_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3297_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3292_; lean_object* v___x_3294_; 
v___x_3292_ = l_Lean_MessageData_ofExpr(v_head_3287_);
if (v_isShared_3291_ == 0)
{
lean_ctor_set(v___x_3290_, 1, v_a_3285_);
lean_ctor_set(v___x_3290_, 0, v___x_3292_);
v___x_3294_ = v___x_3290_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3292_);
lean_ctor_set(v_reuseFailAlloc_3296_, 1, v_a_3285_);
v___x_3294_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
v_a_3284_ = v_tail_3288_;
v_a_3285_ = v___x_3294_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3298_, lean_object* v_xs_3299_, lean_object* v_x_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
v___x_3306_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3307_ = l_Lean_MessageData_ofName(v_f_3298_);
v___x_3308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3306_);
lean_ctor_set(v___x_3308_, 1, v___x_3307_);
v___x_3309_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3308_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_array_to_list(v_xs_3299_);
v___x_3312_ = lean_box(0);
v___x_3313_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3311_, v___x_3312_);
v___x_3314_ = l_Lean_MessageData_ofList(v___x_3313_);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3310_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3317_, lean_object* v_xs_3318_, lean_object* v_x_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v_res_3325_; 
v_res_3325_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3317_, v_xs_3318_, v_x_3319_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
lean_dec(v___y_3323_);
lean_dec_ref(v___y_3322_);
lean_dec(v___y_3321_);
lean_dec_ref(v___y_3320_);
lean_dec_ref(v_x_3319_);
return v_res_3325_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3328_, lean_object* v_msg_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_){
_start:
{
lean_object* v_ref_3335_; lean_object* v___x_3336_; lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3381_; 
v_ref_3335_ = lean_ctor_get(v___y_3332_, 4);
v___x_3336_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3381_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3381_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v_traceState_3342_; lean_object* v_env_3343_; lean_object* v_nextMacroScope_3344_; lean_object* v_ngen_3345_; lean_object* v_auxDeclNGen_3346_; lean_object* v_cache_3347_; lean_object* v_messages_3348_; lean_object* v_infoState_3349_; lean_object* v_snapshotTasks_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3380_; 
v___x_3341_ = lean_st_ref_take(v___y_3333_);
v_traceState_3342_ = lean_ctor_get(v___x_3341_, 4);
v_env_3343_ = lean_ctor_get(v___x_3341_, 0);
v_nextMacroScope_3344_ = lean_ctor_get(v___x_3341_, 1);
v_ngen_3345_ = lean_ctor_get(v___x_3341_, 2);
v_auxDeclNGen_3346_ = lean_ctor_get(v___x_3341_, 3);
v_cache_3347_ = lean_ctor_get(v___x_3341_, 5);
v_messages_3348_ = lean_ctor_get(v___x_3341_, 6);
v_infoState_3349_ = lean_ctor_get(v___x_3341_, 7);
v_snapshotTasks_3350_ = lean_ctor_get(v___x_3341_, 8);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3341_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3352_ = v___x_3341_;
v_isShared_3353_ = v_isSharedCheck_3380_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_snapshotTasks_3350_);
lean_inc(v_infoState_3349_);
lean_inc(v_messages_3348_);
lean_inc(v_cache_3347_);
lean_inc(v_traceState_3342_);
lean_inc(v_auxDeclNGen_3346_);
lean_inc(v_ngen_3345_);
lean_inc(v_nextMacroScope_3344_);
lean_inc(v_env_3343_);
lean_dec(v___x_3341_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3380_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
uint64_t v_tid_3354_; lean_object* v_traces_3355_; lean_object* v___x_3357_; uint8_t v_isShared_3358_; uint8_t v_isSharedCheck_3379_; 
v_tid_3354_ = lean_ctor_get_uint64(v_traceState_3342_, sizeof(void*)*1);
v_traces_3355_ = lean_ctor_get(v_traceState_3342_, 0);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_traceState_3342_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3357_ = v_traceState_3342_;
v_isShared_3358_ = v_isSharedCheck_3379_;
goto v_resetjp_3356_;
}
else
{
lean_inc(v_traces_3355_);
lean_dec(v_traceState_3342_);
v___x_3357_ = lean_box(0);
v_isShared_3358_ = v_isSharedCheck_3379_;
goto v_resetjp_3356_;
}
v_resetjp_3356_:
{
lean_object* v___x_3359_; double v___x_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3359_ = lean_box(0);
v___x_3360_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3361_ = 0;
v___x_3362_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3363_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3363_, 0, v_cls_3328_);
lean_ctor_set(v___x_3363_, 1, v___x_3359_);
lean_ctor_set(v___x_3363_, 2, v___x_3362_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3, v___x_3360_);
lean_ctor_set_float(v___x_3363_, sizeof(void*)*3 + 8, v___x_3360_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*3 + 16, v___x_3361_);
v___x_3364_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3365_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3363_);
lean_ctor_set(v___x_3365_, 1, v_a_3337_);
lean_ctor_set(v___x_3365_, 2, v___x_3364_);
lean_inc(v_ref_3335_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_ref_3335_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = l_Lean_PersistentArray_push___redArg(v_traces_3355_, v___x_3366_);
if (v_isShared_3358_ == 0)
{
lean_ctor_set(v___x_3357_, 0, v___x_3367_);
v___x_3369_ = v___x_3357_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3367_);
lean_ctor_set_uint64(v_reuseFailAlloc_3378_, sizeof(void*)*1, v_tid_3354_);
v___x_3369_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3371_; 
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 4, v___x_3369_);
v___x_3371_ = v___x_3352_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v_env_3343_);
lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_nextMacroScope_3344_);
lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_ngen_3345_);
lean_ctor_set(v_reuseFailAlloc_3377_, 3, v_auxDeclNGen_3346_);
lean_ctor_set(v_reuseFailAlloc_3377_, 4, v___x_3369_);
lean_ctor_set(v_reuseFailAlloc_3377_, 5, v_cache_3347_);
lean_ctor_set(v_reuseFailAlloc_3377_, 6, v_messages_3348_);
lean_ctor_set(v_reuseFailAlloc_3377_, 7, v_infoState_3349_);
lean_ctor_set(v_reuseFailAlloc_3377_, 8, v_snapshotTasks_3350_);
v___x_3371_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3372_ = lean_st_ref_put(v___y_3333_, v___x_3371_);
v___x_3373_ = lean_box(0);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3373_);
v___x_3375_ = v___x_3339_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3382_, lean_object* v_msg_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3382_, v_msg_3383_, v___y_3384_, v___y_3385_, v___y_3386_, v___y_3387_);
lean_dec(v___y_3387_);
lean_dec_ref(v___y_3386_);
lean_dec(v___y_3385_);
lean_dec_ref(v___y_3384_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3390_, lean_object* v_xs_3391_, lean_object* v_k_3392_, lean_object* v_a_3393_, lean_object* v_a_3394_, lean_object* v_a_3395_, lean_object* v_a_3396_){
_start:
{
lean_object* v_options_3398_; uint8_t v_hasTrace_3399_; 
v_options_3398_ = lean_ctor_get(v_a_3395_, 1);
v_hasTrace_3399_ = lean_ctor_get_uint8(v_options_3398_, sizeof(void*)*1);
if (v_hasTrace_3399_ == 0)
{
lean_object* v___x_3400_; 
lean_dec_ref(v_xs_3391_);
lean_dec(v_f_3390_);
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc(v_a_3394_);
lean_inc_ref(v_a_3393_);
v___x_3400_ = lean_apply_5(v_k_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, lean_box(0));
return v___x_3400_;
}
else
{
lean_object* v_toCold_3401_; lean_object* v_inheritedTraceOptions_3402_; lean_object* v___f_3403_; lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3431_; lean_object* v_a_3432_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; uint8_t v___x_3438_; lean_object* v___y_3440_; lean_object* v___y_3441_; lean_object* v_a_3442_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v_a_3457_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; uint8_t v___y_3463_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v_a_3473_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v_a_3479_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v_a_3484_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v_a_3496_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; uint8_t v___y_3502_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v_a_3512_; lean_object* v___y_3516_; lean_object* v___y_3517_; lean_object* v_a_3518_; 
v_toCold_3401_ = lean_ctor_get(v_a_3395_, 0);
v_inheritedTraceOptions_3402_ = lean_ctor_get(v_toCold_3401_, 4);
v___f_3403_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3403_, 0, v_f_3390_);
lean_closure_set(v___f_3403_, 1, v_xs_3391_);
v___x_3435_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3436_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3437_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3438_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3402_, v_options_3398_, v___x_3437_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3545_; uint8_t v___x_3546_; 
v___x_3545_ = l_Lean_trace_profiler;
v___x_3546_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3398_, v___x_3545_);
if (v___x_3546_ == 0)
{
lean_object* v___x_3547_; 
lean_dec_ref(v___f_3403_);
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc(v_a_3394_);
lean_inc_ref(v_a_3393_);
v___x_3547_ = lean_apply_5(v_k_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, lean_box(0));
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_object* v_a_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3550_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3551_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3402_, v_options_3398_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_dec(v_a_3548_);
return v___x_3547_;
}
else
{
lean_object* v___x_3552_; lean_object* v___x_3553_; 
lean_dec_ref_known(v___x_3547_, 1);
lean_inc(v_a_3548_);
v___x_3552_ = l_Lean_MessageData_ofExpr(v_a_3548_);
v___x_3553_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3549_, v___x_3552_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3553_) == 0)
{
lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3560_; 
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3560_ == 0)
{
lean_object* v_unused_3561_; 
v_unused_3561_ = lean_ctor_get(v___x_3553_, 0);
lean_dec(v_unused_3561_);
v___x_3555_ = v___x_3553_;
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
else
{
lean_dec(v___x_3553_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3560_;
goto v_resetjp_3554_;
}
v_resetjp_3554_:
{
lean_object* v___x_3558_; 
if (v_isShared_3556_ == 0)
{
lean_ctor_set(v___x_3555_, 0, v_a_3548_);
v___x_3558_ = v___x_3555_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v_a_3548_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3562_; lean_object* v___x_3564_; uint8_t v_isShared_3565_; uint8_t v_isSharedCheck_3569_; 
lean_dec(v_a_3548_);
v_a_3562_ = lean_ctor_get(v___x_3553_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3553_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3564_ = v___x_3553_;
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
else
{
lean_inc(v_a_3562_);
lean_dec(v___x_3553_);
v___x_3564_ = lean_box(0);
v_isShared_3565_ = v_isSharedCheck_3569_;
goto v_resetjp_3563_;
}
v_resetjp_3563_:
{
lean_object* v___x_3567_; 
lean_inc(v_a_3562_);
if (v_isShared_3565_ == 0)
{
v___x_3567_ = v___x_3564_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_a_3562_);
v___x_3567_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
v___y_3431_ = v___x_3567_;
v_a_3432_ = v_a_3562_;
goto v___jp_3430_;
}
}
}
}
}
else
{
lean_object* v_a_3570_; 
v_a_3570_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3570_);
v___y_3431_ = v___x_3547_;
v_a_3432_ = v_a_3570_;
goto v___jp_3430_;
}
}
else
{
goto v___jp_3520_;
}
}
else
{
goto v___jp_3520_;
}
v___jp_3404_:
{
if (v___y_3407_ == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3409_; uint8_t v___x_3410_; 
lean_dec_ref(v___y_3406_);
v___x_3408_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3409_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3410_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3402_, v_options_3398_, v___x_3409_);
if (v___x_3410_ == 0)
{
lean_object* v___x_3411_; 
v___x_3411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3411_, 0, v___y_3405_);
return v___x_3411_;
}
else
{
lean_object* v___x_3412_; lean_object* v___x_3413_; 
lean_inc_ref(v___y_3405_);
v___x_3412_ = l_Lean_Exception_toMessageData(v___y_3405_);
v___x_3413_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3408_, v___x_3412_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
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
lean_ctor_set(v___x_3415_, 0, v___y_3405_);
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v___y_3405_);
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
lean_dec_ref(v___y_3405_);
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
lean_dec_ref(v___y_3405_);
return v___y_3406_;
}
}
v___jp_3430_:
{
uint8_t v___x_3433_; 
v___x_3433_ = l_Lean_Exception_isInterrupt(v_a_3432_);
if (v___x_3433_ == 0)
{
uint8_t v___x_3434_; 
lean_inc_ref(v_a_3432_);
v___x_3434_ = l_Lean_Exception_isRuntime(v_a_3432_);
v___y_3405_ = v_a_3432_;
v___y_3406_ = v___y_3431_;
v___y_3407_ = v___x_3434_;
goto v___jp_3404_;
}
else
{
v___y_3405_ = v_a_3432_;
v___y_3406_ = v___y_3431_;
v___y_3407_ = v___x_3433_;
goto v___jp_3404_;
}
}
v___jp_3439_:
{
lean_object* v___x_3443_; double v___x_3444_; double v___x_3445_; double v___x_3446_; double v___x_3447_; double v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3443_ = lean_io_mono_nanos_now();
v___x_3444_ = lean_float_of_nat(v___y_3441_);
v___x_3445_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3446_ = lean_float_div(v___x_3444_, v___x_3445_);
v___x_3447_ = lean_float_of_nat(v___x_3443_);
v___x_3448_ = lean_float_div(v___x_3447_, v___x_3445_);
v___x_3449_ = lean_box_float(v___x_3446_);
v___x_3450_ = lean_box_float(v___x_3448_);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v___x_3449_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
v___x_3452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3452_, 0, v_a_3442_);
lean_ctor_set(v___x_3452_, 1, v___x_3451_);
v___x_3453_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3435_, v_hasTrace_3399_, v___x_3436_, v_options_3398_, v___x_3438_, v___y_3440_, v___f_3403_, v___x_3452_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
return v___x_3453_;
}
v___jp_3454_:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3458_, 0, v_a_3457_);
v___y_3440_ = v___y_3455_;
v___y_3441_ = v___y_3456_;
v_a_3442_ = v___x_3458_;
goto v___jp_3439_;
}
v___jp_3459_:
{
if (v___y_3463_ == 0)
{
lean_object* v___x_3464_; lean_object* v___x_3465_; uint8_t v___x_3466_; 
v___x_3464_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3465_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3466_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3402_, v_options_3398_, v___x_3465_);
if (v___x_3466_ == 0)
{
v___y_3455_ = v___y_3461_;
v___y_3456_ = v___y_3462_;
v_a_3457_ = v___y_3460_;
goto v___jp_3454_;
}
else
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
lean_inc_ref(v___y_3460_);
v___x_3467_ = l_Lean_Exception_toMessageData(v___y_3460_);
v___x_3468_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3464_, v___x_3467_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_dec_ref_known(v___x_3468_, 1);
v___y_3455_ = v___y_3461_;
v___y_3456_ = v___y_3462_;
v_a_3457_ = v___y_3460_;
goto v___jp_3454_;
}
else
{
lean_object* v_a_3469_; 
lean_dec_ref(v___y_3460_);
v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
lean_inc(v_a_3469_);
lean_dec_ref_known(v___x_3468_, 1);
v___y_3455_ = v___y_3461_;
v___y_3456_ = v___y_3462_;
v_a_3457_ = v_a_3469_;
goto v___jp_3454_;
}
}
}
else
{
v___y_3455_ = v___y_3461_;
v___y_3456_ = v___y_3462_;
v_a_3457_ = v___y_3460_;
goto v___jp_3454_;
}
}
v___jp_3470_:
{
uint8_t v___x_3474_; 
v___x_3474_ = l_Lean_Exception_isInterrupt(v_a_3473_);
if (v___x_3474_ == 0)
{
uint8_t v___x_3475_; 
lean_inc_ref(v_a_3473_);
v___x_3475_ = l_Lean_Exception_isRuntime(v_a_3473_);
v___y_3460_ = v_a_3473_;
v___y_3461_ = v___y_3471_;
v___y_3462_ = v___y_3472_;
v___y_3463_ = v___x_3475_;
goto v___jp_3459_;
}
else
{
v___y_3460_ = v_a_3473_;
v___y_3461_ = v___y_3471_;
v___y_3462_ = v___y_3472_;
v___y_3463_ = v___x_3474_;
goto v___jp_3459_;
}
}
v___jp_3476_:
{
lean_object* v___x_3480_; 
v___x_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_a_3479_);
v___y_3440_ = v___y_3477_;
v___y_3441_ = v___y_3478_;
v_a_3442_ = v___x_3480_;
goto v___jp_3439_;
}
v___jp_3481_:
{
lean_object* v___x_3485_; double v___x_3486_; double v___x_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3485_ = lean_io_get_num_heartbeats();
v___x_3486_ = lean_float_of_nat(v___y_3482_);
v___x_3487_ = lean_float_of_nat(v___x_3485_);
v___x_3488_ = lean_box_float(v___x_3486_);
v___x_3489_ = lean_box_float(v___x_3487_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v___x_3488_);
lean_ctor_set(v___x_3490_, 1, v___x_3489_);
v___x_3491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3491_, 0, v_a_3484_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
v___x_3492_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3435_, v_hasTrace_3399_, v___x_3436_, v_options_3398_, v___x_3438_, v___y_3483_, v___f_3403_, v___x_3491_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
return v___x_3492_;
}
v___jp_3493_:
{
lean_object* v___x_3497_; 
v___x_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3497_, 0, v_a_3496_);
v___y_3482_ = v___y_3494_;
v___y_3483_ = v___y_3495_;
v_a_3484_ = v___x_3497_;
goto v___jp_3481_;
}
v___jp_3498_:
{
if (v___y_3502_ == 0)
{
lean_object* v___x_3503_; lean_object* v___x_3504_; uint8_t v___x_3505_; 
v___x_3503_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3504_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3505_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3402_, v_options_3398_, v___x_3504_);
if (v___x_3505_ == 0)
{
v___y_3494_ = v___y_3499_;
v___y_3495_ = v___y_3500_;
v_a_3496_ = v___y_3501_;
goto v___jp_3493_;
}
else
{
lean_object* v___x_3506_; lean_object* v___x_3507_; 
lean_inc_ref(v___y_3501_);
v___x_3506_ = l_Lean_Exception_toMessageData(v___y_3501_);
v___x_3507_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3503_, v___x_3506_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_dec_ref_known(v___x_3507_, 1);
v___y_3494_ = v___y_3499_;
v___y_3495_ = v___y_3500_;
v_a_3496_ = v___y_3501_;
goto v___jp_3493_;
}
else
{
lean_object* v_a_3508_; 
lean_dec_ref(v___y_3501_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___y_3494_ = v___y_3499_;
v___y_3495_ = v___y_3500_;
v_a_3496_ = v_a_3508_;
goto v___jp_3493_;
}
}
}
else
{
v___y_3494_ = v___y_3499_;
v___y_3495_ = v___y_3500_;
v_a_3496_ = v___y_3501_;
goto v___jp_3493_;
}
}
v___jp_3509_:
{
uint8_t v___x_3513_; 
v___x_3513_ = l_Lean_Exception_isInterrupt(v_a_3512_);
if (v___x_3513_ == 0)
{
uint8_t v___x_3514_; 
lean_inc_ref(v_a_3512_);
v___x_3514_ = l_Lean_Exception_isRuntime(v_a_3512_);
v___y_3499_ = v___y_3510_;
v___y_3500_ = v___y_3511_;
v___y_3501_ = v_a_3512_;
v___y_3502_ = v___x_3514_;
goto v___jp_3498_;
}
else
{
v___y_3499_ = v___y_3510_;
v___y_3500_ = v___y_3511_;
v___y_3501_ = v_a_3512_;
v___y_3502_ = v___x_3513_;
goto v___jp_3498_;
}
}
v___jp_3515_:
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_a_3518_);
v___y_3482_ = v___y_3516_;
v___y_3483_ = v___y_3517_;
v_a_3484_ = v___x_3519_;
goto v___jp_3481_;
}
v___jp_3520_:
{
lean_object* v___x_3521_; lean_object* v_a_3522_; lean_object* v___x_3523_; uint8_t v___x_3524_; 
v___x_3521_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3396_);
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3524_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3398_, v___x_3523_);
if (v___x_3524_ == 0)
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
v___x_3525_ = lean_io_mono_nanos_now();
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc(v_a_3394_);
lean_inc_ref(v_a_3393_);
v___x_3526_ = lean_apply_5(v_k_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, lean_box(0));
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; uint8_t v___x_3530_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3526_, 1);
v___x_3528_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3529_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3530_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3402_, v_options_3398_, v___x_3529_);
if (v___x_3530_ == 0)
{
v___y_3477_ = v_a_3522_;
v___y_3478_ = v___x_3525_;
v_a_3479_ = v_a_3527_;
goto v___jp_3476_;
}
else
{
lean_object* v___x_3531_; lean_object* v___x_3532_; 
lean_inc(v_a_3527_);
v___x_3531_ = l_Lean_MessageData_ofExpr(v_a_3527_);
v___x_3532_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3528_, v___x_3531_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_dec_ref_known(v___x_3532_, 1);
v___y_3477_ = v_a_3522_;
v___y_3478_ = v___x_3525_;
v_a_3479_ = v_a_3527_;
goto v___jp_3476_;
}
else
{
lean_object* v_a_3533_; 
lean_dec(v_a_3527_);
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
lean_inc(v_a_3533_);
lean_dec_ref_known(v___x_3532_, 1);
v___y_3471_ = v_a_3522_;
v___y_3472_ = v___x_3525_;
v_a_3473_ = v_a_3533_;
goto v___jp_3470_;
}
}
}
else
{
lean_object* v_a_3534_; 
v_a_3534_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3534_);
lean_dec_ref_known(v___x_3526_, 1);
v___y_3471_ = v_a_3522_;
v___y_3472_ = v___x_3525_;
v_a_3473_ = v_a_3534_;
goto v___jp_3470_;
}
}
else
{
lean_object* v___x_3535_; lean_object* v___x_3536_; 
v___x_3535_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3396_);
lean_inc_ref(v_a_3395_);
lean_inc(v_a_3394_);
lean_inc_ref(v_a_3393_);
v___x_3536_ = lean_apply_5(v_k_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, lean_box(0));
if (lean_obj_tag(v___x_3536_) == 0)
{
lean_object* v_a_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3536_, 1);
v___x_3538_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3539_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3402_, v_options_3398_, v___x_3539_);
if (v___x_3540_ == 0)
{
v___y_3516_ = v___x_3535_;
v___y_3517_ = v_a_3522_;
v_a_3518_ = v_a_3537_;
goto v___jp_3515_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
lean_inc(v_a_3537_);
v___x_3541_ = l_Lean_MessageData_ofExpr(v_a_3537_);
v___x_3542_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3538_, v___x_3541_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_dec_ref_known(v___x_3542_, 1);
v___y_3516_ = v___x_3535_;
v___y_3517_ = v_a_3522_;
v_a_3518_ = v_a_3537_;
goto v___jp_3515_;
}
else
{
lean_object* v_a_3543_; 
lean_dec(v_a_3537_);
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v___y_3510_ = v___x_3535_;
v___y_3511_ = v_a_3522_;
v_a_3512_ = v_a_3543_;
goto v___jp_3509_;
}
}
}
else
{
lean_object* v_a_3544_; 
v_a_3544_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3544_);
lean_dec_ref_known(v___x_3536_, 1);
v___y_3510_ = v___x_3535_;
v___y_3511_ = v_a_3522_;
v_a_3512_ = v_a_3544_;
goto v___jp_3509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3571_, lean_object* v_xs_3572_, lean_object* v_k_3573_, lean_object* v_a_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v_res_3579_; 
v_res_3579_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3571_, v_xs_3572_, v_k_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_);
lean_dec(v_a_3577_);
lean_dec_ref(v_a_3576_);
lean_dec(v_a_3575_);
lean_dec_ref(v_a_3574_);
return v_res_3579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3580_, lean_object* v_xs_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v___f_3587_; uint8_t v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
lean_inc_ref(v_xs_3581_);
lean_inc(v_constName_3580_);
v___f_3587_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3587_, 0, v_constName_3580_);
lean_closure_set(v___f_3587_, 1, v_xs_3581_);
v___x_3588_ = 0;
v___x_3589_ = lean_box(v___x_3588_);
v___x_3590_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3590_, 0, lean_box(0));
lean_closure_set(v___x_3590_, 1, v___f_3587_);
lean_closure_set(v___x_3590_, 2, v___x_3589_);
v___x_3591_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3580_, v_xs_3581_, v___x_3590_, v_a_3582_, v_a_3583_, v_a_3584_, v_a_3585_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3592_, lean_object* v_xs_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_){
_start:
{
lean_object* v_res_3599_; 
v_res_3599_ = l_Lean_Meta_mkAppM(v_constName_3592_, v_xs_3593_, v_a_3594_, v_a_3595_, v_a_3596_, v_a_3597_);
lean_dec(v_a_3597_);
lean_dec_ref(v_a_3596_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
return v_res_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v___x_3605_; 
v___x_3605_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3603_);
return v___x_3605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v_res_3611_; 
v_res_3611_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
lean_dec(v___y_3609_);
lean_dec_ref(v___y_3608_);
lean_dec(v___y_3607_);
lean_dec_ref(v___y_3606_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3612_, lean_object* v_x_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; 
v___x_3619_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3613_);
return v___x_3619_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3620_, lean_object* v_x_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_){
_start:
{
lean_object* v_res_3627_; 
v_res_3627_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3620_, v_x_3621_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_);
lean_dec(v___y_3625_);
lean_dec_ref(v___y_3624_);
lean_dec(v___y_3623_);
lean_dec_ref(v___y_3622_);
return v_res_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3628_, lean_object* v_xs_3629_, lean_object* v_x_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v___x_3636_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3637_ = l_Lean_MessageData_ofExpr(v_f_3628_);
v___x_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3636_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3640_, 0, v___x_3638_);
lean_ctor_set(v___x_3640_, 1, v___x_3639_);
v___x_3641_ = lean_array_to_list(v_xs_3629_);
v___x_3642_ = lean_box(0);
v___x_3643_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3641_, v___x_3642_);
v___x_3644_ = l_Lean_MessageData_ofList(v___x_3643_);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3640_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
return v___x_3646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3647_, lean_object* v_xs_3648_, lean_object* v_x_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
lean_object* v_res_3655_; 
v_res_3655_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3647_, v_xs_3648_, v_x_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
lean_dec(v___y_3653_);
lean_dec_ref(v___y_3652_);
lean_dec(v___y_3651_);
lean_dec_ref(v___y_3650_);
lean_dec_ref(v_x_3649_);
return v_res_3655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3656_, lean_object* v_xs_3657_, lean_object* v_k_3658_, lean_object* v_a_3659_, lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v_a_3662_){
_start:
{
lean_object* v_options_3664_; uint8_t v_hasTrace_3665_; 
v_options_3664_ = lean_ctor_get(v_a_3661_, 1);
v_hasTrace_3665_ = lean_ctor_get_uint8(v_options_3664_, sizeof(void*)*1);
if (v_hasTrace_3665_ == 0)
{
lean_object* v___x_3666_; 
lean_dec_ref(v_xs_3657_);
lean_dec_ref(v_f_3656_);
lean_inc(v_a_3662_);
lean_inc_ref(v_a_3661_);
lean_inc(v_a_3660_);
lean_inc_ref(v_a_3659_);
v___x_3666_ = lean_apply_5(v_k_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, lean_box(0));
return v___x_3666_;
}
else
{
lean_object* v_toCold_3667_; lean_object* v_inheritedTraceOptions_3668_; lean_object* v___f_3669_; lean_object* v___y_3671_; lean_object* v___y_3672_; uint8_t v___y_3673_; lean_object* v___y_3697_; lean_object* v_a_3698_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; uint8_t v___x_3704_; lean_object* v___y_3706_; lean_object* v___y_3707_; lean_object* v_a_3708_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v_a_3723_; lean_object* v___y_3726_; lean_object* v___y_3727_; lean_object* v___y_3728_; uint8_t v___y_3729_; lean_object* v___y_3737_; lean_object* v___y_3738_; lean_object* v_a_3739_; lean_object* v___y_3743_; lean_object* v___y_3744_; lean_object* v_a_3745_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v_a_3750_; lean_object* v___y_3760_; lean_object* v___y_3761_; lean_object* v_a_3762_; lean_object* v___y_3765_; lean_object* v___y_3766_; lean_object* v___y_3767_; uint8_t v___y_3768_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v_a_3778_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v_a_3784_; 
v_toCold_3667_ = lean_ctor_get(v_a_3661_, 0);
v_inheritedTraceOptions_3668_ = lean_ctor_get(v_toCold_3667_, 4);
v___f_3669_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3669_, 0, v_f_3656_);
lean_closure_set(v___f_3669_, 1, v_xs_3657_);
v___x_3701_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3702_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3703_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3704_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3811_; uint8_t v___x_3812_; 
v___x_3811_ = l_Lean_trace_profiler;
v___x_3812_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3664_, v___x_3811_);
if (v___x_3812_ == 0)
{
lean_object* v___x_3813_; 
lean_dec_ref(v___f_3669_);
lean_inc(v_a_3662_);
lean_inc_ref(v_a_3661_);
lean_inc(v_a_3660_);
lean_inc_ref(v_a_3659_);
v___x_3813_ = lean_apply_5(v_k_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, lean_box(0));
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
v___x_3815_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3816_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3817_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3816_);
if (v___x_3817_ == 0)
{
lean_dec(v_a_3814_);
return v___x_3813_;
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3819_; 
lean_dec_ref_known(v___x_3813_, 1);
lean_inc(v_a_3814_);
v___x_3818_ = l_Lean_MessageData_ofExpr(v_a_3814_);
v___x_3819_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3815_, v___x_3818_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3826_; 
v_isSharedCheck_3826_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3826_ == 0)
{
lean_object* v_unused_3827_; 
v_unused_3827_ = lean_ctor_get(v___x_3819_, 0);
lean_dec(v_unused_3827_);
v___x_3821_ = v___x_3819_;
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
else
{
lean_dec(v___x_3819_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3826_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v___x_3824_; 
if (v_isShared_3822_ == 0)
{
lean_ctor_set(v___x_3821_, 0, v_a_3814_);
v___x_3824_ = v___x_3821_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3825_; 
v_reuseFailAlloc_3825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_a_3814_);
v___x_3824_ = v_reuseFailAlloc_3825_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
return v___x_3824_;
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_dec(v_a_3814_);
v_a_3828_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3819_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3819_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
lean_inc(v_a_3828_);
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
v___y_3697_ = v___x_3833_;
v_a_3698_ = v_a_3828_;
goto v___jp_3696_;
}
}
}
}
}
else
{
lean_object* v_a_3836_; 
v_a_3836_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3836_);
v___y_3697_ = v___x_3813_;
v_a_3698_ = v_a_3836_;
goto v___jp_3696_;
}
}
else
{
goto v___jp_3786_;
}
}
else
{
goto v___jp_3786_;
}
v___jp_3670_:
{
if (v___y_3673_ == 0)
{
lean_object* v___x_3674_; lean_object* v___x_3675_; uint8_t v___x_3676_; 
lean_dec_ref(v___y_3672_);
v___x_3674_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3675_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3675_);
if (v___x_3676_ == 0)
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3677_, 0, v___y_3671_);
return v___x_3677_;
}
else
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
lean_inc_ref(v___y_3671_);
v___x_3678_ = l_Lean_Exception_toMessageData(v___y_3671_);
v___x_3679_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3674_, v___x_3678_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3686_ == 0)
{
lean_object* v_unused_3687_; 
v_unused_3687_ = lean_ctor_get(v___x_3679_, 0);
lean_dec(v_unused_3687_);
v___x_3681_ = v___x_3679_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_dec(v___x_3679_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
lean_ctor_set_tag(v___x_3681_, 1);
lean_ctor_set(v___x_3681_, 0, v___y_3671_);
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___y_3671_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v___y_3671_);
v_a_3688_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3679_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3679_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3671_);
return v___y_3672_;
}
}
v___jp_3696_:
{
uint8_t v___x_3699_; 
v___x_3699_ = l_Lean_Exception_isInterrupt(v_a_3698_);
if (v___x_3699_ == 0)
{
uint8_t v___x_3700_; 
lean_inc_ref(v_a_3698_);
v___x_3700_ = l_Lean_Exception_isRuntime(v_a_3698_);
v___y_3671_ = v_a_3698_;
v___y_3672_ = v___y_3697_;
v___y_3673_ = v___x_3700_;
goto v___jp_3670_;
}
else
{
v___y_3671_ = v_a_3698_;
v___y_3672_ = v___y_3697_;
v___y_3673_ = v___x_3699_;
goto v___jp_3670_;
}
}
v___jp_3705_:
{
lean_object* v___x_3709_; double v___x_3710_; double v___x_3711_; double v___x_3712_; double v___x_3713_; double v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v___x_3709_ = lean_io_mono_nanos_now();
v___x_3710_ = lean_float_of_nat(v___y_3707_);
v___x_3711_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3712_ = lean_float_div(v___x_3710_, v___x_3711_);
v___x_3713_ = lean_float_of_nat(v___x_3709_);
v___x_3714_ = lean_float_div(v___x_3713_, v___x_3711_);
v___x_3715_ = lean_box_float(v___x_3712_);
v___x_3716_ = lean_box_float(v___x_3714_);
v___x_3717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v_a_3708_);
lean_ctor_set(v___x_3718_, 1, v___x_3717_);
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3701_, v_hasTrace_3665_, v___x_3702_, v_options_3664_, v___x_3704_, v___y_3706_, v___f_3669_, v___x_3718_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
return v___x_3719_;
}
v___jp_3720_:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v_a_3723_);
v___y_3706_ = v___y_3721_;
v___y_3707_ = v___y_3722_;
v_a_3708_ = v___x_3724_;
goto v___jp_3705_;
}
v___jp_3725_:
{
if (v___y_3729_ == 0)
{
lean_object* v___x_3730_; lean_object* v___x_3731_; uint8_t v___x_3732_; 
v___x_3730_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3731_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3731_);
if (v___x_3732_ == 0)
{
v___y_3721_ = v___y_3727_;
v___y_3722_ = v___y_3728_;
v_a_3723_ = v___y_3726_;
goto v___jp_3720_;
}
else
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
lean_inc_ref(v___y_3726_);
v___x_3733_ = l_Lean_Exception_toMessageData(v___y_3726_);
v___x_3734_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3730_, v___x_3733_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_dec_ref_known(v___x_3734_, 1);
v___y_3721_ = v___y_3727_;
v___y_3722_ = v___y_3728_;
v_a_3723_ = v___y_3726_;
goto v___jp_3720_;
}
else
{
lean_object* v_a_3735_; 
lean_dec_ref(v___y_3726_);
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3734_, 1);
v___y_3721_ = v___y_3727_;
v___y_3722_ = v___y_3728_;
v_a_3723_ = v_a_3735_;
goto v___jp_3720_;
}
}
}
else
{
v___y_3721_ = v___y_3727_;
v___y_3722_ = v___y_3728_;
v_a_3723_ = v___y_3726_;
goto v___jp_3720_;
}
}
v___jp_3736_:
{
uint8_t v___x_3740_; 
v___x_3740_ = l_Lean_Exception_isInterrupt(v_a_3739_);
if (v___x_3740_ == 0)
{
uint8_t v___x_3741_; 
lean_inc_ref(v_a_3739_);
v___x_3741_ = l_Lean_Exception_isRuntime(v_a_3739_);
v___y_3726_ = v_a_3739_;
v___y_3727_ = v___y_3737_;
v___y_3728_ = v___y_3738_;
v___y_3729_ = v___x_3741_;
goto v___jp_3725_;
}
else
{
v___y_3726_ = v_a_3739_;
v___y_3727_ = v___y_3737_;
v___y_3728_ = v___y_3738_;
v___y_3729_ = v___x_3740_;
goto v___jp_3725_;
}
}
v___jp_3742_:
{
lean_object* v___x_3746_; 
v___x_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3746_, 0, v_a_3745_);
v___y_3706_ = v___y_3743_;
v___y_3707_ = v___y_3744_;
v_a_3708_ = v___x_3746_;
goto v___jp_3705_;
}
v___jp_3747_:
{
lean_object* v___x_3751_; double v___x_3752_; double v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3751_ = lean_io_get_num_heartbeats();
v___x_3752_ = lean_float_of_nat(v___y_3749_);
v___x_3753_ = lean_float_of_nat(v___x_3751_);
v___x_3754_ = lean_box_float(v___x_3752_);
v___x_3755_ = lean_box_float(v___x_3753_);
v___x_3756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3756_, 0, v___x_3754_);
lean_ctor_set(v___x_3756_, 1, v___x_3755_);
v___x_3757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3757_, 0, v_a_3750_);
lean_ctor_set(v___x_3757_, 1, v___x_3756_);
v___x_3758_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3701_, v_hasTrace_3665_, v___x_3702_, v_options_3664_, v___x_3704_, v___y_3748_, v___f_3669_, v___x_3757_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
return v___x_3758_;
}
v___jp_3759_:
{
lean_object* v___x_3763_; 
v___x_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3763_, 0, v_a_3762_);
v___y_3748_ = v___y_3760_;
v___y_3749_ = v___y_3761_;
v_a_3750_ = v___x_3763_;
goto v___jp_3747_;
}
v___jp_3764_:
{
if (v___y_3768_ == 0)
{
lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v___x_3769_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3770_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3770_);
if (v___x_3771_ == 0)
{
v___y_3760_ = v___y_3765_;
v___y_3761_ = v___y_3767_;
v_a_3762_ = v___y_3766_;
goto v___jp_3759_;
}
else
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
lean_inc_ref(v___y_3766_);
v___x_3772_ = l_Lean_Exception_toMessageData(v___y_3766_);
v___x_3773_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3769_, v___x_3772_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_dec_ref_known(v___x_3773_, 1);
v___y_3760_ = v___y_3765_;
v___y_3761_ = v___y_3767_;
v_a_3762_ = v___y_3766_;
goto v___jp_3759_;
}
else
{
lean_object* v_a_3774_; 
lean_dec_ref(v___y_3766_);
v_a_3774_ = lean_ctor_get(v___x_3773_, 0);
lean_inc(v_a_3774_);
lean_dec_ref_known(v___x_3773_, 1);
v___y_3760_ = v___y_3765_;
v___y_3761_ = v___y_3767_;
v_a_3762_ = v_a_3774_;
goto v___jp_3759_;
}
}
}
else
{
v___y_3760_ = v___y_3765_;
v___y_3761_ = v___y_3767_;
v_a_3762_ = v___y_3766_;
goto v___jp_3759_;
}
}
v___jp_3775_:
{
uint8_t v___x_3779_; 
v___x_3779_ = l_Lean_Exception_isInterrupt(v_a_3778_);
if (v___x_3779_ == 0)
{
uint8_t v___x_3780_; 
lean_inc_ref(v_a_3778_);
v___x_3780_ = l_Lean_Exception_isRuntime(v_a_3778_);
v___y_3765_ = v___y_3776_;
v___y_3766_ = v_a_3778_;
v___y_3767_ = v___y_3777_;
v___y_3768_ = v___x_3780_;
goto v___jp_3764_;
}
else
{
v___y_3765_ = v___y_3776_;
v___y_3766_ = v_a_3778_;
v___y_3767_ = v___y_3777_;
v___y_3768_ = v___x_3779_;
goto v___jp_3764_;
}
}
v___jp_3781_:
{
lean_object* v___x_3785_; 
v___x_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3785_, 0, v_a_3784_);
v___y_3748_ = v___y_3782_;
v___y_3749_ = v___y_3783_;
v_a_3750_ = v___x_3785_;
goto v___jp_3747_;
}
v___jp_3786_:
{
lean_object* v___x_3787_; lean_object* v_a_3788_; lean_object* v___x_3789_; uint8_t v___x_3790_; 
v___x_3787_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3662_);
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
v___x_3789_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3790_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3664_, v___x_3789_);
if (v___x_3790_ == 0)
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = lean_io_mono_nanos_now();
lean_inc(v_a_3662_);
lean_inc_ref(v_a_3661_);
lean_inc(v_a_3660_);
lean_inc_ref(v_a_3659_);
v___x_3792_ = lean_apply_5(v_k_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, lean_box(0));
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; uint8_t v___x_3796_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3792_, 1);
v___x_3794_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3795_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3795_);
if (v___x_3796_ == 0)
{
v___y_3743_ = v_a_3788_;
v___y_3744_ = v___x_3791_;
v_a_3745_ = v_a_3793_;
goto v___jp_3742_;
}
else
{
lean_object* v___x_3797_; lean_object* v___x_3798_; 
lean_inc(v_a_3793_);
v___x_3797_ = l_Lean_MessageData_ofExpr(v_a_3793_);
v___x_3798_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3794_, v___x_3797_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_dec_ref_known(v___x_3798_, 1);
v___y_3743_ = v_a_3788_;
v___y_3744_ = v___x_3791_;
v_a_3745_ = v_a_3793_;
goto v___jp_3742_;
}
else
{
lean_object* v_a_3799_; 
lean_dec(v_a_3793_);
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3799_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3737_ = v_a_3788_;
v___y_3738_ = v___x_3791_;
v_a_3739_ = v_a_3799_;
goto v___jp_3736_;
}
}
}
else
{
lean_object* v_a_3800_; 
v_a_3800_ = lean_ctor_get(v___x_3792_, 0);
lean_inc(v_a_3800_);
lean_dec_ref_known(v___x_3792_, 1);
v___y_3737_ = v_a_3788_;
v___y_3738_ = v___x_3791_;
v_a_3739_ = v_a_3800_;
goto v___jp_3736_;
}
}
else
{
lean_object* v___x_3801_; lean_object* v___x_3802_; 
v___x_3801_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3662_);
lean_inc_ref(v_a_3661_);
lean_inc(v_a_3660_);
lean_inc_ref(v_a_3659_);
v___x_3802_ = lean_apply_5(v_k_3658_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_, lean_box(0));
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; uint8_t v___x_3806_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
v___x_3804_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3805_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3806_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3668_, v_options_3664_, v___x_3805_);
if (v___x_3806_ == 0)
{
v___y_3782_ = v_a_3788_;
v___y_3783_ = v___x_3801_;
v_a_3784_ = v_a_3803_;
goto v___jp_3781_;
}
else
{
lean_object* v___x_3807_; lean_object* v___x_3808_; 
lean_inc(v_a_3803_);
v___x_3807_ = l_Lean_MessageData_ofExpr(v_a_3803_);
v___x_3808_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3804_, v___x_3807_, v_a_3659_, v_a_3660_, v_a_3661_, v_a_3662_);
if (lean_obj_tag(v___x_3808_) == 0)
{
lean_dec_ref_known(v___x_3808_, 1);
v___y_3782_ = v_a_3788_;
v___y_3783_ = v___x_3801_;
v_a_3784_ = v_a_3803_;
goto v___jp_3781_;
}
else
{
lean_object* v_a_3809_; 
lean_dec(v_a_3803_);
v_a_3809_ = lean_ctor_get(v___x_3808_, 0);
lean_inc(v_a_3809_);
lean_dec_ref_known(v___x_3808_, 1);
v___y_3776_ = v_a_3788_;
v___y_3777_ = v___x_3801_;
v_a_3778_ = v_a_3809_;
goto v___jp_3775_;
}
}
}
else
{
lean_object* v_a_3810_; 
v_a_3810_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3810_);
lean_dec_ref_known(v___x_3802_, 1);
v___y_3776_ = v_a_3788_;
v___y_3777_ = v___x_3801_;
v_a_3778_ = v_a_3810_;
goto v___jp_3775_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3837_, lean_object* v_xs_3838_, lean_object* v_k_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v_res_3845_; 
v_res_3845_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3837_, v_xs_3838_, v_k_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
lean_dec(v_a_3843_);
lean_dec_ref(v_a_3842_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3846_, lean_object* v_xs_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_){
_start:
{
lean_object* v___x_3853_; 
lean_inc(v_a_3851_);
lean_inc_ref(v_a_3850_);
lean_inc(v_a_3849_);
lean_inc_ref(v_a_3848_);
lean_inc_ref(v_f_3846_);
v___x_3853_ = lean_infer_type(v_f_3846_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; lean_object* v___x_3855_; uint8_t v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref_known(v___x_3853_, 1);
lean_inc_ref(v_xs_3847_);
lean_inc_ref(v_f_3846_);
v___x_3855_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3855_, 0, v_f_3846_);
lean_closure_set(v___x_3855_, 1, v_a_3854_);
lean_closure_set(v___x_3855_, 2, v_xs_3847_);
v___x_3856_ = 0;
v___x_3857_ = lean_box(v___x_3856_);
v___x_3858_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3858_, 0, lean_box(0));
lean_closure_set(v___x_3858_, 1, v___x_3855_);
lean_closure_set(v___x_3858_, 2, v___x_3857_);
v___x_3859_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3846_, v_xs_3847_, v___x_3858_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_);
return v___x_3859_;
}
else
{
lean_dec_ref(v_xs_3847_);
lean_dec_ref(v_f_3846_);
return v___x_3853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3860_, lean_object* v_xs_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v_res_3867_; 
v_res_3867_ = l_Lean_Meta_mkAppM_x27(v_f_3860_, v_xs_3861_, v_a_3862_, v_a_3863_, v_a_3864_, v_a_3865_);
lean_dec(v_a_3865_);
lean_dec_ref(v_a_3864_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
return v_res_3867_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3868_, size_t v_i_3869_, size_t v_stop_3870_, lean_object* v_b_3871_){
_start:
{
lean_object* v___y_3873_; uint8_t v___x_3877_; 
v___x_3877_ = lean_usize_dec_eq(v_i_3869_, v_stop_3870_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
v___x_3878_ = lean_array_uget_borrowed(v_as_3868_, v_i_3869_);
if (lean_obj_tag(v___x_3878_) == 0)
{
v___y_3873_ = v_b_3871_;
goto v___jp_3872_;
}
else
{
lean_object* v_val_3879_; lean_object* v___x_3880_; 
v_val_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc(v_val_3879_);
v___x_3880_ = lean_array_push(v_b_3871_, v_val_3879_);
v___y_3873_ = v___x_3880_;
goto v___jp_3872_;
}
}
else
{
return v_b_3871_;
}
v___jp_3872_:
{
size_t v___x_3874_; size_t v___x_3875_; 
v___x_3874_ = ((size_t)1ULL);
v___x_3875_ = lean_usize_add(v_i_3869_, v___x_3874_);
v_i_3869_ = v___x_3875_;
v_b_3871_ = v___y_3873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3881_, lean_object* v_i_3882_, lean_object* v_stop_3883_, lean_object* v_b_3884_){
_start:
{
size_t v_i_boxed_3885_; size_t v_stop_boxed_3886_; lean_object* v_res_3887_; 
v_i_boxed_3885_ = lean_unbox_usize(v_i_3882_);
lean_dec(v_i_3882_);
v_stop_boxed_3886_ = lean_unbox_usize(v_stop_3883_);
lean_dec(v_stop_3883_);
v_res_3887_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3881_, v_i_boxed_3885_, v_stop_boxed_3886_, v_b_3884_);
lean_dec_ref(v_as_3881_);
return v_res_3887_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3895_ = l_Lean_MessageData_ofFormat(v___x_3894_);
return v___x_3895_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3896_; lean_object* v___x_3897_; 
v___x_3896_ = lean_box(1);
v___x_3897_ = l_Lean_MessageData_ofFormat(v___x_3896_);
return v___x_3897_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3902_ = l_Lean_MessageData_ofFormat(v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3903_, lean_object* v_xs_3904_, lean_object* v_x_3905_, lean_object* v_x_3906_, lean_object* v_x_3907_, lean_object* v_x_3908_, lean_object* v_x_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_){
_start:
{
if (lean_obj_tag(v_x_3909_) == 7)
{
lean_object* v_binderName_3915_; lean_object* v_binderType_3916_; lean_object* v_body_3917_; uint8_t v_binderInfo_3918_; lean_object* v___x_3919_; uint8_t v___x_3920_; 
v_binderName_3915_ = lean_ctor_get(v_x_3909_, 0);
lean_inc(v_binderName_3915_);
v_binderType_3916_ = lean_ctor_get(v_x_3909_, 1);
lean_inc_ref(v_binderType_3916_);
v_body_3917_ = lean_ctor_get(v_x_3909_, 2);
lean_inc_ref(v_body_3917_);
v_binderInfo_3918_ = lean_ctor_get_uint8(v_x_3909_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3909_, 3);
v___x_3919_ = lean_array_get_size(v_xs_3904_);
v___x_3920_ = lean_nat_dec_lt(v_x_3905_, v___x_3919_);
if (v___x_3920_ == 0)
{
lean_object* v___x_3921_; lean_object* v___x_3922_; 
lean_dec_ref(v_body_3917_);
lean_dec_ref(v_binderType_3916_);
lean_dec(v_binderName_3915_);
lean_dec(v_x_3907_);
lean_dec(v_x_3905_);
v___x_3921_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3922_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3921_, v_f_3903_, v_x_3906_, v_x_3908_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec_ref(v_x_3908_);
lean_dec_ref(v_x_3906_);
return v___x_3922_;
}
else
{
lean_object* v___x_3923_; lean_object* v_d_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_array_get_size(v_x_3906_);
v_d_3924_ = lean_expr_instantiate_rev_range(v_binderType_3916_, v_x_3907_, v___x_3923_, v_x_3906_);
lean_dec_ref(v_binderType_3916_);
v___x_3925_ = lean_array_fget_borrowed(v_xs_3904_, v_x_3905_);
if (lean_obj_tag(v___x_3925_) == 0)
{
if (v_binderInfo_3918_ == 3)
{
lean_object* v___x_3926_; uint8_t v___x_3927_; lean_object* v___x_3928_; 
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v_d_3924_);
v___x_3927_ = 1;
v___x_3928_ = l_Lean_Meta_mkFreshExprMVar(v___x_3926_, v___x_3927_, v_binderName_3915_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
if (lean_obj_tag(v___x_3928_) == 0)
{
lean_object* v_a_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_a_3929_ = lean_ctor_get(v___x_3928_, 0);
lean_inc_n(v_a_3929_, 2);
lean_dec_ref_known(v___x_3928_, 1);
v___x_3930_ = lean_unsigned_to_nat(1u);
v___x_3931_ = lean_nat_add(v_x_3905_, v___x_3930_);
lean_dec(v_x_3905_);
v___x_3932_ = lean_array_push(v_x_3906_, v_a_3929_);
v___x_3933_ = l_Lean_Expr_mvarId_x21(v_a_3929_);
lean_dec(v_a_3929_);
v___x_3934_ = lean_array_push(v_x_3908_, v___x_3933_);
v_x_3905_ = v___x_3931_;
v_x_3906_ = v___x_3932_;
v_x_3908_ = v___x_3934_;
v_x_3909_ = v_body_3917_;
goto _start;
}
else
{
lean_dec_ref(v_body_3917_);
lean_dec_ref(v_x_3908_);
lean_dec(v_x_3907_);
lean_dec_ref(v_x_3906_);
lean_dec(v_x_3905_);
lean_dec_ref(v_f_3903_);
return v___x_3928_;
}
}
else
{
lean_object* v___x_3936_; uint8_t v___x_3937_; lean_object* v___x_3938_; 
v___x_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3936_, 0, v_d_3924_);
v___x_3937_ = 0;
v___x_3938_ = l_Lean_Meta_mkFreshExprMVar(v___x_3936_, v___x_3937_, v_binderName_3915_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref_known(v___x_3938_, 1);
v___x_3940_ = lean_unsigned_to_nat(1u);
v___x_3941_ = lean_nat_add(v_x_3905_, v___x_3940_);
lean_dec(v_x_3905_);
v___x_3942_ = lean_array_push(v_x_3906_, v_a_3939_);
v_x_3905_ = v___x_3941_;
v_x_3906_ = v___x_3942_;
v_x_3909_ = v_body_3917_;
goto _start;
}
else
{
lean_dec_ref(v_body_3917_);
lean_dec_ref(v_x_3908_);
lean_dec(v_x_3907_);
lean_dec_ref(v_x_3906_);
lean_dec(v_x_3905_);
lean_dec_ref(v_f_3903_);
return v___x_3938_;
}
}
}
else
{
lean_object* v_val_3944_; lean_object* v___x_3945_; 
lean_dec(v_binderName_3915_);
v_val_3944_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3913_);
lean_inc_ref(v_a_3912_);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
lean_inc(v_val_3944_);
v___x_3945_ = lean_infer_type(v_val_3944_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
if (lean_obj_tag(v___x_3945_) == 0)
{
lean_object* v_a_3946_; lean_object* v___x_3947_; 
v_a_3946_ = lean_ctor_get(v___x_3945_, 0);
lean_inc(v_a_3946_);
lean_dec_ref_known(v___x_3945_, 1);
v___x_3947_ = l_Lean_Meta_isExprDefEq(v_d_3924_, v_a_3946_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; uint8_t v___x_3949_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc(v_a_3948_);
lean_dec_ref_known(v___x_3947_, 1);
v___x_3949_ = lean_unbox(v_a_3948_);
lean_dec(v_a_3948_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; lean_object* v___x_3951_; 
lean_dec_ref(v_body_3917_);
lean_dec_ref(v_x_3908_);
lean_dec(v_x_3907_);
lean_dec(v_x_3905_);
v___x_3950_ = l_Lean_mkAppN(v_f_3903_, v_x_3906_);
lean_dec_ref(v_x_3906_);
lean_inc(v_val_3944_);
v___x_3951_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3950_, v_val_3944_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
return v___x_3951_;
}
else
{
lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_nat_add(v_x_3905_, v___x_3952_);
lean_dec(v_x_3905_);
lean_inc(v_val_3944_);
v___x_3954_ = lean_array_push(v_x_3906_, v_val_3944_);
v_x_3905_ = v___x_3953_;
v_x_3906_ = v___x_3954_;
v_x_3909_ = v_body_3917_;
goto _start;
}
}
else
{
lean_object* v_a_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
lean_dec_ref(v_body_3917_);
lean_dec_ref(v_x_3908_);
lean_dec(v_x_3907_);
lean_dec_ref(v_x_3906_);
lean_dec(v_x_3905_);
lean_dec_ref(v_f_3903_);
v_a_3956_ = lean_ctor_get(v___x_3947_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3947_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3958_ = v___x_3947_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_a_3956_);
lean_dec(v___x_3947_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3956_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
}
else
{
lean_dec_ref(v_d_3924_);
lean_dec_ref(v_body_3917_);
lean_dec_ref(v_x_3908_);
lean_dec(v_x_3907_);
lean_dec_ref(v_x_3906_);
lean_dec(v_x_3905_);
lean_dec_ref(v_f_3903_);
return v___x_3945_;
}
}
}
}
else
{
lean_object* v___x_3964_; lean_object* v_type_3965_; lean_object* v___x_3966_; 
v___x_3964_ = lean_array_get_size(v_x_3906_);
v_type_3965_ = lean_expr_instantiate_rev_range(v_x_3909_, v_x_3907_, v___x_3964_, v_x_3906_);
lean_dec(v_x_3907_);
lean_dec_ref(v_x_3909_);
v___x_3966_ = l_Lean_Meta_whnfD(v_type_3965_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; uint8_t v___x_3968_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref_known(v___x_3966_, 1);
v___x_3968_ = l_Lean_Expr_isForall(v_a_3967_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; uint8_t v___x_3970_; 
lean_dec(v_a_3967_);
v___x_3969_ = lean_array_get_size(v_xs_3904_);
v___x_3970_ = lean_nat_dec_eq(v_x_3905_, v___x_3969_);
lean_dec(v_x_3905_);
if (v___x_3970_ == 0)
{
lean_object* v___x_3971_; lean_object* v___y_3973_; lean_object* v___x_3986_; uint8_t v___x_3987_; 
lean_dec_ref(v_x_3908_);
lean_dec_ref(v_x_3906_);
v___x_3971_ = lean_unsigned_to_nat(0u);
v___x_3986_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3987_ = lean_nat_dec_lt(v___x_3971_, v___x_3969_);
if (v___x_3987_ == 0)
{
v___y_3973_ = v___x_3986_;
goto v___jp_3972_;
}
else
{
uint8_t v___x_3988_; 
v___x_3988_ = lean_nat_dec_le(v___x_3969_, v___x_3969_);
if (v___x_3988_ == 0)
{
if (v___x_3987_ == 0)
{
v___y_3973_ = v___x_3986_;
goto v___jp_3972_;
}
else
{
size_t v___x_3989_; size_t v___x_3990_; lean_object* v___x_3991_; 
v___x_3989_ = ((size_t)0ULL);
v___x_3990_ = lean_usize_of_nat(v___x_3969_);
v___x_3991_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3904_, v___x_3989_, v___x_3990_, v___x_3986_);
v___y_3973_ = v___x_3991_;
goto v___jp_3972_;
}
}
else
{
size_t v___x_3992_; size_t v___x_3993_; lean_object* v___x_3994_; 
v___x_3992_ = ((size_t)0ULL);
v___x_3993_ = lean_usize_of_nat(v___x_3969_);
v___x_3994_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3904_, v___x_3992_, v___x_3993_, v___x_3986_);
v___y_3973_ = v___x_3994_;
goto v___jp_3972_;
}
}
v___jp_3972_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3981_; lean_object* v___x_3982_; lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3974_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3975_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3976_ = l_Lean_indentExpr(v_f_3903_);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3975_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3977_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3981_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3981_, 0, v___x_3979_);
lean_ctor_set(v___x_3981_, 1, v___x_3980_);
v___x_3982_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3983_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3973_, v___x_3971_, v___x_3982_);
lean_dec_ref(v___y_3973_);
v___x_3984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3981_);
lean_ctor_set(v___x_3984_, 1, v___x_3983_);
v___x_3985_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3974_, v___x_3984_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
return v___x_3985_;
}
}
else
{
lean_object* v___x_3995_; lean_object* v___x_3996_; 
v___x_3995_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3996_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3995_, v_f_3903_, v_x_3906_, v_x_3908_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec_ref(v_x_3908_);
lean_dec_ref(v_x_3906_);
return v___x_3996_;
}
}
else
{
v_x_3907_ = v___x_3964_;
v_x_3909_ = v_a_3967_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3908_);
lean_dec_ref(v_x_3906_);
lean_dec(v_x_3905_);
lean_dec_ref(v_f_3903_);
return v___x_3966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_3998_, lean_object* v_xs_3999_, lean_object* v_x_4000_, lean_object* v_x_4001_, lean_object* v_x_4002_, lean_object* v_x_4003_, lean_object* v_x_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_3998_, v_xs_3999_, v_x_4000_, v_x_4001_, v_x_4002_, v_x_4003_, v_x_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec_ref(v_xs_3999_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_4011_, lean_object* v_xs_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v___x_4018_; 
v___x_4018_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_4011_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v_fst_4020_; lean_object* v_snd_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref_known(v___x_4018_, 1);
v_fst_4020_ = lean_ctor_get(v_a_4019_, 0);
lean_inc(v_fst_4020_);
v_snd_4021_ = lean_ctor_get(v_a_4019_, 1);
lean_inc(v_snd_4021_);
lean_dec(v_a_4019_);
v___x_4022_ = lean_unsigned_to_nat(0u);
v___x_4023_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4024_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4020_, v_xs_4012_, v___x_4022_, v___x_4023_, v___x_4022_, v___x_4023_, v_snd_4021_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
return v___x_4024_;
}
else
{
lean_object* v_a_4025_; lean_object* v___x_4027_; uint8_t v_isShared_4028_; uint8_t v_isSharedCheck_4032_; 
v_a_4025_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4032_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4032_ == 0)
{
v___x_4027_ = v___x_4018_;
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
else
{
lean_inc(v_a_4025_);
lean_dec(v___x_4018_);
v___x_4027_ = lean_box(0);
v_isShared_4028_ = v_isSharedCheck_4032_;
goto v_resetjp_4026_;
}
v_resetjp_4026_:
{
lean_object* v___x_4030_; 
if (v_isShared_4028_ == 0)
{
v___x_4030_ = v___x_4027_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v_a_4025_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4033_, lean_object* v_xs_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4033_, v_xs_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec_ref(v_xs_4034_);
return v_res_4040_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4045_ = l_Lean_MessageData_ofFormat(v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4046_, lean_object* v_a_4047_){
_start:
{
if (lean_obj_tag(v_a_4046_) == 0)
{
lean_object* v___x_4048_; 
v___x_4048_ = l_List_reverse___redArg(v_a_4047_);
return v___x_4048_;
}
else
{
lean_object* v_head_4049_; lean_object* v_tail_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4063_; 
v_head_4049_ = lean_ctor_get(v_a_4046_, 0);
v_tail_4050_ = lean_ctor_get(v_a_4046_, 1);
v_isSharedCheck_4063_ = !lean_is_exclusive(v_a_4046_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4052_ = v_a_4046_;
v_isShared_4053_ = v_isSharedCheck_4063_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_tail_4050_);
lean_inc(v_head_4049_);
lean_dec(v_a_4046_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4063_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___y_4055_; 
if (lean_obj_tag(v_head_4049_) == 0)
{
lean_object* v___x_4060_; 
v___x_4060_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4055_ = v___x_4060_;
goto v___jp_4054_;
}
else
{
lean_object* v_val_4061_; lean_object* v___x_4062_; 
v_val_4061_ = lean_ctor_get(v_head_4049_, 0);
lean_inc(v_val_4061_);
lean_dec_ref_known(v_head_4049_, 1);
v___x_4062_ = l_Lean_MessageData_ofExpr(v_val_4061_);
v___y_4055_ = v___x_4062_;
goto v___jp_4054_;
}
v___jp_4054_:
{
lean_object* v___x_4057_; 
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 1, v_a_4047_);
lean_ctor_set(v___x_4052_, 0, v___y_4055_);
v___x_4057_ = v___x_4052_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v___y_4055_);
lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_a_4047_);
v___x_4057_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
v_a_4046_ = v_tail_4050_;
v_a_4047_ = v___x_4057_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4064_, lean_object* v_xs_4065_, lean_object* v_x_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4072_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4073_ = l_Lean_MessageData_ofName(v_f_4064_);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4072_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4074_);
lean_ctor_set(v___x_4076_, 1, v___x_4075_);
v___x_4077_ = lean_array_to_list(v_xs_4065_);
v___x_4078_ = lean_box(0);
v___x_4079_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4077_, v___x_4078_);
v___x_4080_ = l_Lean_MessageData_ofList(v___x_4079_);
v___x_4081_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4076_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
v___x_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4081_);
return v___x_4082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4083_, lean_object* v_xs_4084_, lean_object* v_x_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4083_, v_xs_4084_, v_x_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec_ref(v_x_4085_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4092_, lean_object* v_xs_4093_, lean_object* v_k_4094_, lean_object* v_a_4095_, lean_object* v_a_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_){
_start:
{
lean_object* v_options_4100_; uint8_t v_hasTrace_4101_; 
v_options_4100_ = lean_ctor_get(v_a_4097_, 1);
v_hasTrace_4101_ = lean_ctor_get_uint8(v_options_4100_, sizeof(void*)*1);
if (v_hasTrace_4101_ == 0)
{
lean_object* v___x_4102_; 
lean_dec_ref(v_xs_4093_);
lean_dec(v_f_4092_);
lean_inc(v_a_4098_);
lean_inc_ref(v_a_4097_);
lean_inc(v_a_4096_);
lean_inc_ref(v_a_4095_);
v___x_4102_ = lean_apply_5(v_k_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, lean_box(0));
return v___x_4102_;
}
else
{
lean_object* v_toCold_4103_; lean_object* v_inheritedTraceOptions_4104_; lean_object* v___f_4105_; lean_object* v___y_4107_; lean_object* v___y_4108_; uint8_t v___y_4109_; lean_object* v___y_4133_; lean_object* v_a_4134_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; uint8_t v___x_4140_; lean_object* v___y_4142_; lean_object* v___y_4143_; lean_object* v_a_4144_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v_a_4159_; lean_object* v___y_4162_; lean_object* v___y_4163_; lean_object* v___y_4164_; uint8_t v___y_4165_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v_a_4175_; lean_object* v___y_4179_; lean_object* v___y_4180_; lean_object* v_a_4181_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v_a_4186_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v_a_4198_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; uint8_t v___y_4204_; lean_object* v___y_4212_; lean_object* v___y_4213_; lean_object* v_a_4214_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v_a_4220_; 
v_toCold_4103_ = lean_ctor_get(v_a_4097_, 0);
v_inheritedTraceOptions_4104_ = lean_ctor_get(v_toCold_4103_, 4);
v___f_4105_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4105_, 0, v_f_4092_);
lean_closure_set(v___f_4105_, 1, v_xs_4093_);
v___x_4137_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4138_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4139_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4100_, v___x_4139_);
if (v___x_4140_ == 0)
{
lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4247_ = l_Lean_trace_profiler;
v___x_4248_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4100_, v___x_4247_);
if (v___x_4248_ == 0)
{
lean_object* v___x_4249_; 
lean_dec_ref(v___f_4105_);
lean_inc(v_a_4098_);
lean_inc_ref(v_a_4097_);
lean_inc(v_a_4096_);
lean_inc_ref(v_a_4095_);
v___x_4249_ = lean_apply_5(v_k_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, lean_box(0));
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v_a_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; uint8_t v___x_4253_; 
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
v___x_4251_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4252_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4253_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4100_, v___x_4252_);
if (v___x_4253_ == 0)
{
lean_dec(v_a_4250_);
return v___x_4249_;
}
else
{
lean_object* v___x_4254_; lean_object* v___x_4255_; 
lean_dec_ref_known(v___x_4249_, 1);
lean_inc(v_a_4250_);
v___x_4254_ = l_Lean_MessageData_ofExpr(v_a_4250_);
v___x_4255_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4251_, v___x_4254_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v___x_4257_; uint8_t v_isShared_4258_; uint8_t v_isSharedCheck_4262_; 
v_isSharedCheck_4262_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4262_ == 0)
{
lean_object* v_unused_4263_; 
v_unused_4263_ = lean_ctor_get(v___x_4255_, 0);
lean_dec(v_unused_4263_);
v___x_4257_ = v___x_4255_;
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
else
{
lean_dec(v___x_4255_);
v___x_4257_ = lean_box(0);
v_isShared_4258_ = v_isSharedCheck_4262_;
goto v_resetjp_4256_;
}
v_resetjp_4256_:
{
lean_object* v___x_4260_; 
if (v_isShared_4258_ == 0)
{
lean_ctor_set(v___x_4257_, 0, v_a_4250_);
v___x_4260_ = v___x_4257_;
goto v_reusejp_4259_;
}
else
{
lean_object* v_reuseFailAlloc_4261_; 
v_reuseFailAlloc_4261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4261_, 0, v_a_4250_);
v___x_4260_ = v_reuseFailAlloc_4261_;
goto v_reusejp_4259_;
}
v_reusejp_4259_:
{
return v___x_4260_;
}
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_a_4250_);
v_a_4264_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4255_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4255_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
lean_inc(v_a_4264_);
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
v___y_4133_ = v___x_4269_;
v_a_4134_ = v_a_4264_;
goto v___jp_4132_;
}
}
}
}
}
else
{
lean_object* v_a_4272_; 
v_a_4272_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4272_);
v___y_4133_ = v___x_4249_;
v_a_4134_ = v_a_4272_;
goto v___jp_4132_;
}
}
else
{
goto v___jp_4222_;
}
}
else
{
goto v___jp_4222_;
}
v___jp_4106_:
{
if (v___y_4109_ == 0)
{
lean_object* v___x_4110_; lean_object* v___x_4111_; uint8_t v___x_4112_; 
lean_dec_ref(v___y_4108_);
v___x_4110_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4111_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4112_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4100_, v___x_4111_);
if (v___x_4112_ == 0)
{
lean_object* v___x_4113_; 
v___x_4113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___y_4107_);
return v___x_4113_;
}
else
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_inc_ref(v___y_4107_);
v___x_4114_ = l_Lean_Exception_toMessageData(v___y_4107_);
v___x_4115_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4110_, v___x_4114_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4122_ == 0)
{
lean_object* v_unused_4123_; 
v_unused_4123_ = lean_ctor_get(v___x_4115_, 0);
lean_dec(v_unused_4123_);
v___x_4117_ = v___x_4115_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_dec(v___x_4115_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
lean_ctor_set_tag(v___x_4117_, 1);
lean_ctor_set(v___x_4117_, 0, v___y_4107_);
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v___y_4107_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec_ref(v___y_4107_);
v_a_4124_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4115_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4115_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4129_; 
if (v_isShared_4127_ == 0)
{
v___x_4129_ = v___x_4126_;
goto v_reusejp_4128_;
}
else
{
lean_object* v_reuseFailAlloc_4130_; 
v_reuseFailAlloc_4130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
v___x_4129_ = v_reuseFailAlloc_4130_;
goto v_reusejp_4128_;
}
v_reusejp_4128_:
{
return v___x_4129_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4107_);
return v___y_4108_;
}
}
v___jp_4132_:
{
uint8_t v___x_4135_; 
v___x_4135_ = l_Lean_Exception_isInterrupt(v_a_4134_);
if (v___x_4135_ == 0)
{
uint8_t v___x_4136_; 
lean_inc_ref(v_a_4134_);
v___x_4136_ = l_Lean_Exception_isRuntime(v_a_4134_);
v___y_4107_ = v_a_4134_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___x_4136_;
goto v___jp_4106_;
}
else
{
v___y_4107_ = v_a_4134_;
v___y_4108_ = v___y_4133_;
v___y_4109_ = v___x_4135_;
goto v___jp_4106_;
}
}
v___jp_4141_:
{
lean_object* v___x_4145_; double v___x_4146_; double v___x_4147_; double v___x_4148_; double v___x_4149_; double v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v___x_4145_ = lean_io_mono_nanos_now();
v___x_4146_ = lean_float_of_nat(v___y_4142_);
v___x_4147_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4148_ = lean_float_div(v___x_4146_, v___x_4147_);
v___x_4149_ = lean_float_of_nat(v___x_4145_);
v___x_4150_ = lean_float_div(v___x_4149_, v___x_4147_);
v___x_4151_ = lean_box_float(v___x_4148_);
v___x_4152_ = lean_box_float(v___x_4150_);
v___x_4153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4151_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4154_, 0, v_a_4144_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4137_, v_hasTrace_4101_, v___x_4138_, v_options_4100_, v___x_4140_, v___y_4143_, v___f_4105_, v___x_4154_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
return v___x_4155_;
}
v___jp_4156_:
{
lean_object* v___x_4160_; 
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v_a_4159_);
v___y_4142_ = v___y_4157_;
v___y_4143_ = v___y_4158_;
v_a_4144_ = v___x_4160_;
goto v___jp_4141_;
}
v___jp_4161_:
{
if (v___y_4165_ == 0)
{
lean_object* v___x_4166_; lean_object* v___x_4167_; uint8_t v___x_4168_; 
v___x_4166_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4167_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4100_, v___x_4167_);
if (v___x_4168_ == 0)
{
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v___y_4164_;
goto v___jp_4156_;
}
else
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
lean_inc_ref(v___y_4164_);
v___x_4169_ = l_Lean_Exception_toMessageData(v___y_4164_);
v___x_4170_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4166_, v___x_4169_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4170_) == 0)
{
lean_dec_ref_known(v___x_4170_, 1);
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v___y_4164_;
goto v___jp_4156_;
}
else
{
lean_object* v_a_4171_; 
lean_dec_ref(v___y_4164_);
v_a_4171_ = lean_ctor_get(v___x_4170_, 0);
lean_inc(v_a_4171_);
lean_dec_ref_known(v___x_4170_, 1);
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v_a_4171_;
goto v___jp_4156_;
}
}
}
else
{
v___y_4157_ = v___y_4162_;
v___y_4158_ = v___y_4163_;
v_a_4159_ = v___y_4164_;
goto v___jp_4156_;
}
}
v___jp_4172_:
{
uint8_t v___x_4176_; 
v___x_4176_ = l_Lean_Exception_isInterrupt(v_a_4175_);
if (v___x_4176_ == 0)
{
uint8_t v___x_4177_; 
lean_inc_ref(v_a_4175_);
v___x_4177_ = l_Lean_Exception_isRuntime(v_a_4175_);
v___y_4162_ = v___y_4173_;
v___y_4163_ = v___y_4174_;
v___y_4164_ = v_a_4175_;
v___y_4165_ = v___x_4177_;
goto v___jp_4161_;
}
else
{
v___y_4162_ = v___y_4173_;
v___y_4163_ = v___y_4174_;
v___y_4164_ = v_a_4175_;
v___y_4165_ = v___x_4176_;
goto v___jp_4161_;
}
}
v___jp_4178_:
{
lean_object* v___x_4182_; 
v___x_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4182_, 0, v_a_4181_);
v___y_4142_ = v___y_4179_;
v___y_4143_ = v___y_4180_;
v_a_4144_ = v___x_4182_;
goto v___jp_4141_;
}
v___jp_4183_:
{
lean_object* v___x_4187_; double v___x_4188_; double v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4187_ = lean_io_get_num_heartbeats();
v___x_4188_ = lean_float_of_nat(v___y_4185_);
v___x_4189_ = lean_float_of_nat(v___x_4187_);
v___x_4190_ = lean_box_float(v___x_4188_);
v___x_4191_ = lean_box_float(v___x_4189_);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4193_, 0, v_a_4186_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4137_, v_hasTrace_4101_, v___x_4138_, v_options_4100_, v___x_4140_, v___y_4184_, v___f_4105_, v___x_4193_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
return v___x_4194_;
}
v___jp_4195_:
{
lean_object* v___x_4199_; 
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v_a_4198_);
v___y_4184_ = v___y_4196_;
v___y_4185_ = v___y_4197_;
v_a_4186_ = v___x_4199_;
goto v___jp_4183_;
}
v___jp_4200_:
{
if (v___y_4204_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v___x_4205_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4206_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4207_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4100_, v___x_4206_);
if (v___x_4207_ == 0)
{
v___y_4196_ = v___y_4201_;
v___y_4197_ = v___y_4203_;
v_a_4198_ = v___y_4202_;
goto v___jp_4195_;
}
else
{
lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_inc_ref(v___y_4202_);
v___x_4208_ = l_Lean_Exception_toMessageData(v___y_4202_);
v___x_4209_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4205_, v___x_4208_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_dec_ref_known(v___x_4209_, 1);
v___y_4196_ = v___y_4201_;
v___y_4197_ = v___y_4203_;
v_a_4198_ = v___y_4202_;
goto v___jp_4195_;
}
else
{
lean_object* v_a_4210_; 
lean_dec_ref(v___y_4202_);
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
v___y_4196_ = v___y_4201_;
v___y_4197_ = v___y_4203_;
v_a_4198_ = v_a_4210_;
goto v___jp_4195_;
}
}
}
else
{
v___y_4196_ = v___y_4201_;
v___y_4197_ = v___y_4203_;
v_a_4198_ = v___y_4202_;
goto v___jp_4195_;
}
}
v___jp_4211_:
{
uint8_t v___x_4215_; 
v___x_4215_ = l_Lean_Exception_isInterrupt(v_a_4214_);
if (v___x_4215_ == 0)
{
uint8_t v___x_4216_; 
lean_inc_ref(v_a_4214_);
v___x_4216_ = l_Lean_Exception_isRuntime(v_a_4214_);
v___y_4201_ = v___y_4212_;
v___y_4202_ = v_a_4214_;
v___y_4203_ = v___y_4213_;
v___y_4204_ = v___x_4216_;
goto v___jp_4200_;
}
else
{
v___y_4201_ = v___y_4212_;
v___y_4202_ = v_a_4214_;
v___y_4203_ = v___y_4213_;
v___y_4204_ = v___x_4215_;
goto v___jp_4200_;
}
}
v___jp_4217_:
{
lean_object* v___x_4221_; 
v___x_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_a_4220_);
v___y_4184_ = v___y_4218_;
v___y_4185_ = v___y_4219_;
v_a_4186_ = v___x_4221_;
goto v___jp_4183_;
}
v___jp_4222_:
{
lean_object* v___x_4223_; lean_object* v_a_4224_; lean_object* v___x_4225_; uint8_t v___x_4226_; 
v___x_4223_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4098_);
v_a_4224_ = lean_ctor_get(v___x_4223_, 0);
lean_inc(v_a_4224_);
lean_dec_ref(v___x_4223_);
v___x_4225_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4226_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4100_, v___x_4225_);
if (v___x_4226_ == 0)
{
lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4227_ = lean_io_mono_nanos_now();
lean_inc(v_a_4098_);
lean_inc_ref(v_a_4097_);
lean_inc(v_a_4096_);
lean_inc_ref(v_a_4095_);
v___x_4228_ = lean_apply_5(v_k_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, lean_box(0));
if (lean_obj_tag(v___x_4228_) == 0)
{
lean_object* v_a_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; uint8_t v___x_4232_; 
v_a_4229_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4228_, 1);
v___x_4230_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4231_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4232_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4100_, v___x_4231_);
if (v___x_4232_ == 0)
{
v___y_4179_ = v___x_4227_;
v___y_4180_ = v_a_4224_;
v_a_4181_ = v_a_4229_;
goto v___jp_4178_;
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4234_; 
lean_inc(v_a_4229_);
v___x_4233_ = l_Lean_MessageData_ofExpr(v_a_4229_);
v___x_4234_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4230_, v___x_4233_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4234_) == 0)
{
lean_dec_ref_known(v___x_4234_, 1);
v___y_4179_ = v___x_4227_;
v___y_4180_ = v_a_4224_;
v_a_4181_ = v_a_4229_;
goto v___jp_4178_;
}
else
{
lean_object* v_a_4235_; 
lean_dec(v_a_4229_);
v_a_4235_ = lean_ctor_get(v___x_4234_, 0);
lean_inc(v_a_4235_);
lean_dec_ref_known(v___x_4234_, 1);
v___y_4173_ = v___x_4227_;
v___y_4174_ = v_a_4224_;
v_a_4175_ = v_a_4235_;
goto v___jp_4172_;
}
}
}
else
{
lean_object* v_a_4236_; 
v_a_4236_ = lean_ctor_get(v___x_4228_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4228_, 1);
v___y_4173_ = v___x_4227_;
v___y_4174_ = v_a_4224_;
v_a_4175_ = v_a_4236_;
goto v___jp_4172_;
}
}
else
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4098_);
lean_inc_ref(v_a_4097_);
lean_inc(v_a_4096_);
lean_inc_ref(v_a_4095_);
v___x_4238_ = lean_apply_5(v_k_4094_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_, lean_box(0));
if (lean_obj_tag(v___x_4238_) == 0)
{
lean_object* v_a_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; uint8_t v___x_4242_; 
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref_known(v___x_4238_, 1);
v___x_4240_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4241_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4242_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4104_, v_options_4100_, v___x_4241_);
if (v___x_4242_ == 0)
{
v___y_4218_ = v_a_4224_;
v___y_4219_ = v___x_4237_;
v_a_4220_ = v_a_4239_;
goto v___jp_4217_;
}
else
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
lean_inc(v_a_4239_);
v___x_4243_ = l_Lean_MessageData_ofExpr(v_a_4239_);
v___x_4244_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4240_, v___x_4243_, v_a_4095_, v_a_4096_, v_a_4097_, v_a_4098_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_dec_ref_known(v___x_4244_, 1);
v___y_4218_ = v_a_4224_;
v___y_4219_ = v___x_4237_;
v_a_4220_ = v_a_4239_;
goto v___jp_4217_;
}
else
{
lean_object* v_a_4245_; 
lean_dec(v_a_4239_);
v_a_4245_ = lean_ctor_get(v___x_4244_, 0);
lean_inc(v_a_4245_);
lean_dec_ref_known(v___x_4244_, 1);
v___y_4212_ = v_a_4224_;
v___y_4213_ = v___x_4237_;
v_a_4214_ = v_a_4245_;
goto v___jp_4211_;
}
}
}
else
{
lean_object* v_a_4246_; 
v_a_4246_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4238_, 1);
v___y_4212_ = v_a_4224_;
v___y_4213_ = v___x_4237_;
v_a_4214_ = v_a_4246_;
goto v___jp_4211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4273_, lean_object* v_xs_4274_, lean_object* v_k_4275_, lean_object* v_a_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v_res_4281_; 
v_res_4281_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4273_, v_xs_4274_, v_k_4275_, v_a_4276_, v_a_4277_, v_a_4278_, v_a_4279_);
lean_dec(v_a_4279_);
lean_dec_ref(v_a_4278_);
lean_dec(v_a_4277_);
lean_dec_ref(v_a_4276_);
return v_res_4281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4282_, lean_object* v_xs_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v___f_4289_; uint8_t v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; 
lean_inc_ref(v_xs_4283_);
lean_inc(v_constName_4282_);
v___f_4289_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4289_, 0, v_constName_4282_);
lean_closure_set(v___f_4289_, 1, v_xs_4283_);
v___x_4290_ = 0;
v___x_4291_ = lean_box(v___x_4290_);
v___x_4292_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4292_, 0, lean_box(0));
lean_closure_set(v___x_4292_, 1, v___f_4289_);
lean_closure_set(v___x_4292_, 2, v___x_4291_);
v___x_4293_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4282_, v_xs_4283_, v___x_4292_, v_a_4284_, v_a_4285_, v_a_4286_, v_a_4287_);
return v___x_4293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4294_, lean_object* v_xs_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_){
_start:
{
lean_object* v_res_4301_; 
v_res_4301_ = l_Lean_Meta_mkAppOptM(v_constName_4294_, v_xs_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_);
lean_dec(v_a_4299_);
lean_dec_ref(v_a_4298_);
lean_dec(v_a_4297_);
lean_dec_ref(v_a_4296_);
return v_res_4301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4302_, lean_object* v_xs_4303_, lean_object* v_x_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4310_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4311_ = l_Lean_MessageData_ofExpr(v_f_4302_);
v___x_4312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4310_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = lean_array_to_list(v_xs_4303_);
v___x_4316_ = lean_box(0);
v___x_4317_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4315_, v___x_4316_);
v___x_4318_ = l_Lean_MessageData_ofList(v___x_4317_);
v___x_4319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4319_, 0, v___x_4314_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4320_, 0, v___x_4319_);
return v___x_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4321_, lean_object* v_xs_4322_, lean_object* v_x_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v_res_4329_; 
v_res_4329_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4321_, v_xs_4322_, v_x_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
lean_dec(v___y_4327_);
lean_dec_ref(v___y_4326_);
lean_dec(v___y_4325_);
lean_dec_ref(v___y_4324_);
lean_dec_ref(v_x_4323_);
return v_res_4329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4330_, lean_object* v_xs_4331_, lean_object* v_k_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_){
_start:
{
lean_object* v_options_4338_; uint8_t v_hasTrace_4339_; 
v_options_4338_ = lean_ctor_get(v_a_4335_, 1);
v_hasTrace_4339_ = lean_ctor_get_uint8(v_options_4338_, sizeof(void*)*1);
if (v_hasTrace_4339_ == 0)
{
lean_object* v___x_4340_; 
lean_dec_ref(v_xs_4331_);
lean_dec_ref(v_f_4330_);
lean_inc(v_a_4336_);
lean_inc_ref(v_a_4335_);
lean_inc(v_a_4334_);
lean_inc_ref(v_a_4333_);
v___x_4340_ = lean_apply_5(v_k_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, lean_box(0));
return v___x_4340_;
}
else
{
lean_object* v_toCold_4341_; lean_object* v_inheritedTraceOptions_4342_; lean_object* v___f_4343_; lean_object* v___y_4345_; lean_object* v___y_4346_; uint8_t v___y_4347_; lean_object* v___y_4371_; lean_object* v_a_4372_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; uint8_t v___x_4378_; lean_object* v___y_4380_; lean_object* v___y_4381_; lean_object* v_a_4382_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v_a_4397_; lean_object* v___y_4400_; lean_object* v___y_4401_; lean_object* v___y_4402_; uint8_t v___y_4403_; lean_object* v___y_4411_; lean_object* v___y_4412_; lean_object* v_a_4413_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v_a_4419_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v_a_4424_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v_a_4436_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; uint8_t v___y_4442_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v_a_4452_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v_a_4458_; 
v_toCold_4341_ = lean_ctor_get(v_a_4335_, 0);
v_inheritedTraceOptions_4342_ = lean_ctor_get(v_toCold_4341_, 4);
v___f_4343_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4343_, 0, v_f_4330_);
lean_closure_set(v___f_4343_, 1, v_xs_4331_);
v___x_4375_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4376_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4377_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4378_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4377_);
if (v___x_4378_ == 0)
{
lean_object* v___x_4485_; uint8_t v___x_4486_; 
v___x_4485_ = l_Lean_trace_profiler;
v___x_4486_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4338_, v___x_4485_);
if (v___x_4486_ == 0)
{
lean_object* v___x_4487_; 
lean_dec_ref(v___f_4343_);
lean_inc(v_a_4336_);
lean_inc_ref(v_a_4335_);
lean_inc(v_a_4334_);
lean_inc_ref(v_a_4333_);
v___x_4487_ = lean_apply_5(v_k_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, lean_box(0));
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_object* v_a_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; uint8_t v___x_4491_; 
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
v___x_4489_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4490_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4491_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4490_);
if (v___x_4491_ == 0)
{
lean_dec(v_a_4488_);
return v___x_4487_;
}
else
{
lean_object* v___x_4492_; lean_object* v___x_4493_; 
lean_dec_ref_known(v___x_4487_, 1);
lean_inc(v_a_4488_);
v___x_4492_ = l_Lean_MessageData_ofExpr(v_a_4488_);
v___x_4493_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4489_, v___x_4492_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4500_ == 0)
{
lean_object* v_unused_4501_; 
v_unused_4501_ = lean_ctor_get(v___x_4493_, 0);
lean_dec(v_unused_4501_);
v___x_4495_ = v___x_4493_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_dec(v___x_4493_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
lean_ctor_set(v___x_4495_, 0, v_a_4488_);
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4488_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v_a_4488_);
v_a_4502_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4493_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4493_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
lean_inc(v_a_4502_);
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
v___y_4371_ = v___x_4507_;
v_a_4372_ = v_a_4502_;
goto v___jp_4370_;
}
}
}
}
}
else
{
lean_object* v_a_4510_; 
v_a_4510_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4510_);
v___y_4371_ = v___x_4487_;
v_a_4372_ = v_a_4510_;
goto v___jp_4370_;
}
}
else
{
goto v___jp_4460_;
}
}
else
{
goto v___jp_4460_;
}
v___jp_4344_:
{
if (v___y_4347_ == 0)
{
lean_object* v___x_4348_; lean_object* v___x_4349_; uint8_t v___x_4350_; 
lean_dec_ref(v___y_4346_);
v___x_4348_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4349_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4350_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4349_);
if (v___x_4350_ == 0)
{
lean_object* v___x_4351_; 
v___x_4351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4351_, 0, v___y_4345_);
return v___x_4351_;
}
else
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
lean_inc_ref(v___y_4345_);
v___x_4352_ = l_Lean_Exception_toMessageData(v___y_4345_);
v___x_4353_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4348_, v___x_4352_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4360_ == 0)
{
lean_object* v_unused_4361_; 
v_unused_4361_ = lean_ctor_get(v___x_4353_, 0);
lean_dec(v_unused_4361_);
v___x_4355_ = v___x_4353_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_dec(v___x_4353_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
lean_ctor_set_tag(v___x_4355_, 1);
lean_ctor_set(v___x_4355_, 0, v___y_4345_);
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___y_4345_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec_ref(v___y_4345_);
v_a_4362_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4353_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4353_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4345_);
return v___y_4346_;
}
}
v___jp_4370_:
{
uint8_t v___x_4373_; 
v___x_4373_ = l_Lean_Exception_isInterrupt(v_a_4372_);
if (v___x_4373_ == 0)
{
uint8_t v___x_4374_; 
lean_inc_ref(v_a_4372_);
v___x_4374_ = l_Lean_Exception_isRuntime(v_a_4372_);
v___y_4345_ = v_a_4372_;
v___y_4346_ = v___y_4371_;
v___y_4347_ = v___x_4374_;
goto v___jp_4344_;
}
else
{
v___y_4345_ = v_a_4372_;
v___y_4346_ = v___y_4371_;
v___y_4347_ = v___x_4373_;
goto v___jp_4344_;
}
}
v___jp_4379_:
{
lean_object* v___x_4383_; double v___x_4384_; double v___x_4385_; double v___x_4386_; double v___x_4387_; double v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; 
v___x_4383_ = lean_io_mono_nanos_now();
v___x_4384_ = lean_float_of_nat(v___y_4381_);
v___x_4385_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4386_ = lean_float_div(v___x_4384_, v___x_4385_);
v___x_4387_ = lean_float_of_nat(v___x_4383_);
v___x_4388_ = lean_float_div(v___x_4387_, v___x_4385_);
v___x_4389_ = lean_box_float(v___x_4386_);
v___x_4390_ = lean_box_float(v___x_4388_);
v___x_4391_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4392_, 0, v_a_4382_);
lean_ctor_set(v___x_4392_, 1, v___x_4391_);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4375_, v_hasTrace_4339_, v___x_4376_, v_options_4338_, v___x_4378_, v___y_4380_, v___f_4343_, v___x_4392_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4393_;
}
v___jp_4394_:
{
lean_object* v___x_4398_; 
v___x_4398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4398_, 0, v_a_4397_);
v___y_4380_ = v___y_4395_;
v___y_4381_ = v___y_4396_;
v_a_4382_ = v___x_4398_;
goto v___jp_4379_;
}
v___jp_4399_:
{
if (v___y_4403_ == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4405_; uint8_t v___x_4406_; 
v___x_4404_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4405_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4406_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4405_);
if (v___x_4406_ == 0)
{
v___y_4395_ = v___y_4400_;
v___y_4396_ = v___y_4402_;
v_a_4397_ = v___y_4401_;
goto v___jp_4394_;
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4408_; 
lean_inc_ref(v___y_4401_);
v___x_4407_ = l_Lean_Exception_toMessageData(v___y_4401_);
v___x_4408_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4404_, v___x_4407_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4408_) == 0)
{
lean_dec_ref_known(v___x_4408_, 1);
v___y_4395_ = v___y_4400_;
v___y_4396_ = v___y_4402_;
v_a_4397_ = v___y_4401_;
goto v___jp_4394_;
}
else
{
lean_object* v_a_4409_; 
lean_dec_ref(v___y_4401_);
v_a_4409_ = lean_ctor_get(v___x_4408_, 0);
lean_inc(v_a_4409_);
lean_dec_ref_known(v___x_4408_, 1);
v___y_4395_ = v___y_4400_;
v___y_4396_ = v___y_4402_;
v_a_4397_ = v_a_4409_;
goto v___jp_4394_;
}
}
}
else
{
v___y_4395_ = v___y_4400_;
v___y_4396_ = v___y_4402_;
v_a_4397_ = v___y_4401_;
goto v___jp_4394_;
}
}
v___jp_4410_:
{
uint8_t v___x_4414_; 
v___x_4414_ = l_Lean_Exception_isInterrupt(v_a_4413_);
if (v___x_4414_ == 0)
{
uint8_t v___x_4415_; 
lean_inc_ref(v_a_4413_);
v___x_4415_ = l_Lean_Exception_isRuntime(v_a_4413_);
v___y_4400_ = v___y_4411_;
v___y_4401_ = v_a_4413_;
v___y_4402_ = v___y_4412_;
v___y_4403_ = v___x_4415_;
goto v___jp_4399_;
}
else
{
v___y_4400_ = v___y_4411_;
v___y_4401_ = v_a_4413_;
v___y_4402_ = v___y_4412_;
v___y_4403_ = v___x_4414_;
goto v___jp_4399_;
}
}
v___jp_4416_:
{
lean_object* v___x_4420_; 
v___x_4420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4420_, 0, v_a_4419_);
v___y_4380_ = v___y_4417_;
v___y_4381_ = v___y_4418_;
v_a_4382_ = v___x_4420_;
goto v___jp_4379_;
}
v___jp_4421_:
{
lean_object* v___x_4425_; double v___x_4426_; double v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; 
v___x_4425_ = lean_io_get_num_heartbeats();
v___x_4426_ = lean_float_of_nat(v___y_4423_);
v___x_4427_ = lean_float_of_nat(v___x_4425_);
v___x_4428_ = lean_box_float(v___x_4426_);
v___x_4429_ = lean_box_float(v___x_4427_);
v___x_4430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4428_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4431_, 0, v_a_4424_);
lean_ctor_set(v___x_4431_, 1, v___x_4430_);
v___x_4432_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4375_, v_hasTrace_4339_, v___x_4376_, v_options_4338_, v___x_4378_, v___y_4422_, v___f_4343_, v___x_4431_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
return v___x_4432_;
}
v___jp_4433_:
{
lean_object* v___x_4437_; 
v___x_4437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4437_, 0, v_a_4436_);
v___y_4422_ = v___y_4434_;
v___y_4423_ = v___y_4435_;
v_a_4424_ = v___x_4437_;
goto v___jp_4421_;
}
v___jp_4438_:
{
if (v___y_4442_ == 0)
{
lean_object* v___x_4443_; lean_object* v___x_4444_; uint8_t v___x_4445_; 
v___x_4443_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4444_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4445_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4444_);
if (v___x_4445_ == 0)
{
v___y_4434_ = v___y_4439_;
v___y_4435_ = v___y_4441_;
v_a_4436_ = v___y_4440_;
goto v___jp_4433_;
}
else
{
lean_object* v___x_4446_; lean_object* v___x_4447_; 
lean_inc_ref(v___y_4440_);
v___x_4446_ = l_Lean_Exception_toMessageData(v___y_4440_);
v___x_4447_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4443_, v___x_4446_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_dec_ref_known(v___x_4447_, 1);
v___y_4434_ = v___y_4439_;
v___y_4435_ = v___y_4441_;
v_a_4436_ = v___y_4440_;
goto v___jp_4433_;
}
else
{
lean_object* v_a_4448_; 
lean_dec_ref(v___y_4440_);
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4447_, 1);
v___y_4434_ = v___y_4439_;
v___y_4435_ = v___y_4441_;
v_a_4436_ = v_a_4448_;
goto v___jp_4433_;
}
}
}
else
{
v___y_4434_ = v___y_4439_;
v___y_4435_ = v___y_4441_;
v_a_4436_ = v___y_4440_;
goto v___jp_4433_;
}
}
v___jp_4449_:
{
uint8_t v___x_4453_; 
v___x_4453_ = l_Lean_Exception_isInterrupt(v_a_4452_);
if (v___x_4453_ == 0)
{
uint8_t v___x_4454_; 
lean_inc_ref(v_a_4452_);
v___x_4454_ = l_Lean_Exception_isRuntime(v_a_4452_);
v___y_4439_ = v___y_4450_;
v___y_4440_ = v_a_4452_;
v___y_4441_ = v___y_4451_;
v___y_4442_ = v___x_4454_;
goto v___jp_4438_;
}
else
{
v___y_4439_ = v___y_4450_;
v___y_4440_ = v_a_4452_;
v___y_4441_ = v___y_4451_;
v___y_4442_ = v___x_4453_;
goto v___jp_4438_;
}
}
v___jp_4455_:
{
lean_object* v___x_4459_; 
v___x_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4459_, 0, v_a_4458_);
v___y_4422_ = v___y_4456_;
v___y_4423_ = v___y_4457_;
v_a_4424_ = v___x_4459_;
goto v___jp_4421_;
}
v___jp_4460_:
{
lean_object* v___x_4461_; lean_object* v_a_4462_; lean_object* v___x_4463_; uint8_t v___x_4464_; 
v___x_4461_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4336_);
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref(v___x_4461_);
v___x_4463_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4464_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4338_, v___x_4463_);
if (v___x_4464_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = lean_io_mono_nanos_now();
lean_inc(v_a_4336_);
lean_inc_ref(v_a_4335_);
lean_inc(v_a_4334_);
lean_inc_ref(v_a_4333_);
v___x_4466_ = lean_apply_5(v_k_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, lean_box(0));
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; uint8_t v___x_4470_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4466_, 1);
v___x_4468_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4469_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4470_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4469_);
if (v___x_4470_ == 0)
{
v___y_4417_ = v_a_4462_;
v___y_4418_ = v___x_4465_;
v_a_4419_ = v_a_4467_;
goto v___jp_4416_;
}
else
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
lean_inc(v_a_4467_);
v___x_4471_ = l_Lean_MessageData_ofExpr(v_a_4467_);
v___x_4472_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4468_, v___x_4471_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4472_) == 0)
{
lean_dec_ref_known(v___x_4472_, 1);
v___y_4417_ = v_a_4462_;
v___y_4418_ = v___x_4465_;
v_a_4419_ = v_a_4467_;
goto v___jp_4416_;
}
else
{
lean_object* v_a_4473_; 
lean_dec(v_a_4467_);
v_a_4473_ = lean_ctor_get(v___x_4472_, 0);
lean_inc(v_a_4473_);
lean_dec_ref_known(v___x_4472_, 1);
v___y_4411_ = v_a_4462_;
v___y_4412_ = v___x_4465_;
v_a_4413_ = v_a_4473_;
goto v___jp_4410_;
}
}
}
else
{
lean_object* v_a_4474_; 
v_a_4474_ = lean_ctor_get(v___x_4466_, 0);
lean_inc(v_a_4474_);
lean_dec_ref_known(v___x_4466_, 1);
v___y_4411_ = v_a_4462_;
v___y_4412_ = v___x_4465_;
v_a_4413_ = v_a_4474_;
goto v___jp_4410_;
}
}
else
{
lean_object* v___x_4475_; lean_object* v___x_4476_; 
v___x_4475_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4336_);
lean_inc_ref(v_a_4335_);
lean_inc(v_a_4334_);
lean_inc_ref(v_a_4333_);
v___x_4476_ = lean_apply_5(v_k_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, lean_box(0));
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; uint8_t v___x_4480_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4476_, 1);
v___x_4478_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4479_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4480_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4342_, v_options_4338_, v___x_4479_);
if (v___x_4480_ == 0)
{
v___y_4456_ = v_a_4462_;
v___y_4457_ = v___x_4475_;
v_a_4458_ = v_a_4477_;
goto v___jp_4455_;
}
else
{
lean_object* v___x_4481_; lean_object* v___x_4482_; 
lean_inc(v_a_4477_);
v___x_4481_ = l_Lean_MessageData_ofExpr(v_a_4477_);
v___x_4482_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4478_, v___x_4481_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_);
if (lean_obj_tag(v___x_4482_) == 0)
{
lean_dec_ref_known(v___x_4482_, 1);
v___y_4456_ = v_a_4462_;
v___y_4457_ = v___x_4475_;
v_a_4458_ = v_a_4477_;
goto v___jp_4455_;
}
else
{
lean_object* v_a_4483_; 
lean_dec(v_a_4477_);
v_a_4483_ = lean_ctor_get(v___x_4482_, 0);
lean_inc(v_a_4483_);
lean_dec_ref_known(v___x_4482_, 1);
v___y_4450_ = v_a_4462_;
v___y_4451_ = v___x_4475_;
v_a_4452_ = v_a_4483_;
goto v___jp_4449_;
}
}
}
else
{
lean_object* v_a_4484_; 
v_a_4484_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4476_, 1);
v___y_4450_ = v_a_4462_;
v___y_4451_ = v___x_4475_;
v_a_4452_ = v_a_4484_;
goto v___jp_4449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4511_, lean_object* v_xs_4512_, lean_object* v_k_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v_res_4519_; 
v_res_4519_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4511_, v_xs_4512_, v_k_4513_, v_a_4514_, v_a_4515_, v_a_4516_, v_a_4517_);
lean_dec(v_a_4517_);
lean_dec_ref(v_a_4516_);
lean_dec(v_a_4515_);
lean_dec_ref(v_a_4514_);
return v_res_4519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4520_, lean_object* v_xs_4521_, lean_object* v_a_4522_, lean_object* v_a_4523_, lean_object* v_a_4524_, lean_object* v_a_4525_){
_start:
{
lean_object* v___x_4527_; 
lean_inc(v_a_4525_);
lean_inc_ref(v_a_4524_);
lean_inc(v_a_4523_);
lean_inc_ref(v_a_4522_);
lean_inc_ref(v_f_4520_);
v___x_4527_ = lean_infer_type(v_f_4520_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; uint8_t v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; lean_object* v___x_4535_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
lean_inc(v_a_4528_);
lean_dec_ref_known(v___x_4527_, 1);
v___x_4529_ = lean_unsigned_to_nat(0u);
v___x_4530_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4521_);
lean_inc_ref(v_f_4520_);
v___x_4531_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4531_, 0, v_f_4520_);
lean_closure_set(v___x_4531_, 1, v_xs_4521_);
lean_closure_set(v___x_4531_, 2, v___x_4529_);
lean_closure_set(v___x_4531_, 3, v___x_4530_);
lean_closure_set(v___x_4531_, 4, v___x_4529_);
lean_closure_set(v___x_4531_, 5, v___x_4530_);
lean_closure_set(v___x_4531_, 6, v_a_4528_);
v___x_4532_ = 0;
v___x_4533_ = lean_box(v___x_4532_);
v___x_4534_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4534_, 0, lean_box(0));
lean_closure_set(v___x_4534_, 1, v___x_4531_);
lean_closure_set(v___x_4534_, 2, v___x_4533_);
v___x_4535_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4520_, v_xs_4521_, v___x_4534_, v_a_4522_, v_a_4523_, v_a_4524_, v_a_4525_);
return v___x_4535_;
}
else
{
lean_dec_ref(v_xs_4521_);
lean_dec_ref(v_f_4520_);
return v___x_4527_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4536_, lean_object* v_xs_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_, lean_object* v_a_4541_, lean_object* v_a_4542_){
_start:
{
lean_object* v_res_4543_; 
v_res_4543_ = l_Lean_Meta_mkAppOptM_x27(v_f_4536_, v_xs_4537_, v_a_4538_, v_a_4539_, v_a_4540_, v_a_4541_);
lean_dec(v_a_4541_);
lean_dec_ref(v_a_4540_);
lean_dec(v_a_4539_);
lean_dec_ref(v_a_4538_);
return v_res_4543_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
v___x_4551_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4552_ = l_Lean_MessageData_ofFormat(v___x_4551_);
return v___x_4552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4553_, lean_object* v_h1_4554_, lean_object* v_h2_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_, lean_object* v_a_4558_, lean_object* v_a_4559_){
_start:
{
lean_object* v___x_4561_; uint8_t v___x_4562_; 
v___x_4561_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4562_ = l_Lean_Expr_isAppOf(v_h2_4555_, v___x_4561_);
if (v___x_4562_ == 0)
{
lean_object* v___x_4563_; 
lean_inc_ref(v_h2_4555_);
v___x_4563_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4555_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; uint8_t v___x_4567_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
v___x_4565_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4566_ = lean_unsigned_to_nat(3u);
v___x_4567_ = l_Lean_Expr_isAppOfArity(v_a_4564_, v___x_4565_, v___x_4566_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; 
lean_dec_ref(v_h1_4554_);
lean_dec_ref(v_motive_4553_);
v___x_4568_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4569_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4570_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4555_, v_a_4564_);
v___x_4571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4571_, 0, v___x_4569_);
lean_ctor_set(v___x_4571_, 1, v___x_4570_);
v___x_4572_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4568_, v___x_4571_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
return v___x_4572_;
}
else
{
lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; 
v___x_4573_ = l_Lean_Expr_appFn_x21(v_a_4564_);
v___x_4574_ = l_Lean_Expr_appFn_x21(v___x_4573_);
v___x_4575_ = l_Lean_Expr_appArg_x21(v___x_4574_);
lean_dec_ref(v___x_4574_);
lean_inc_ref(v___x_4575_);
v___x_4576_ = l_Lean_Meta_getLevel(v___x_4575_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
if (lean_obj_tag(v___x_4576_) == 0)
{
lean_object* v_a_4577_; lean_object* v___x_4578_; 
v_a_4577_ = lean_ctor_get(v___x_4576_, 0);
lean_inc(v_a_4577_);
lean_dec_ref_known(v___x_4576_, 1);
lean_inc_ref(v_motive_4553_);
v___x_4578_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4553_, v_a_4556_, v_a_4557_, v_a_4558_, v_a_4559_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4614_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4614_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4614_ == 0)
{
v___x_4581_ = v___x_4578_;
v_isShared_4582_ = v_isSharedCheck_4614_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4578_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4614_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; 
if (lean_obj_tag(v_a_4579_) == 7)
{
lean_object* v_body_4593_; 
v_body_4593_ = lean_ctor_get(v_a_4579_, 2);
lean_inc_ref(v_body_4593_);
lean_dec_ref_known(v_a_4579_, 3);
if (lean_obj_tag(v_body_4593_) == 3)
{
lean_object* v_u_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
v_u_4594_ = lean_ctor_get(v_body_4593_, 0);
lean_inc(v_u_4594_);
lean_dec_ref_known(v_body_4593_, 1);
v___x_4595_ = l_Lean_Expr_appArg_x21(v___x_4573_);
lean_dec_ref(v___x_4573_);
v___x_4596_ = l_Lean_Expr_appArg_x21(v_a_4564_);
lean_dec(v_a_4564_);
v___x_4597_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4598_ = lean_box(0);
v___x_4599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4599_, 0, v_a_4577_);
lean_ctor_set(v___x_4599_, 1, v___x_4598_);
v___x_4600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4600_, 0, v_u_4594_);
lean_ctor_set(v___x_4600_, 1, v___x_4599_);
v___x_4601_ = l_Lean_mkConst(v___x_4597_, v___x_4600_);
v___x_4602_ = lean_unsigned_to_nat(6u);
v___x_4603_ = lean_mk_empty_array_with_capacity(v___x_4602_);
v___x_4604_ = lean_array_push(v___x_4603_, v___x_4575_);
v___x_4605_ = lean_array_push(v___x_4604_, v___x_4595_);
v___x_4606_ = lean_array_push(v___x_4605_, v_motive_4553_);
v___x_4607_ = lean_array_push(v___x_4606_, v_h1_4554_);
v___x_4608_ = lean_array_push(v___x_4607_, v___x_4596_);
v___x_4609_ = lean_array_push(v___x_4608_, v_h2_4555_);
v___x_4610_ = l_Lean_mkAppN(v___x_4601_, v___x_4609_);
lean_dec_ref(v___x_4609_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 0, v___x_4610_);
v___x_4612_ = v___x_4581_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v___x_4610_);
v___x_4612_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
return v___x_4612_;
}
}
else
{
lean_dec_ref(v_body_4593_);
lean_del_object(v___x_4581_);
lean_dec(v_a_4577_);
lean_dec_ref(v___x_4575_);
lean_dec_ref(v___x_4573_);
lean_dec(v_a_4564_);
lean_dec_ref(v_h2_4555_);
lean_dec_ref(v_h1_4554_);
v___y_4584_ = v_a_4556_;
v___y_4585_ = v_a_4557_;
v___y_4586_ = v_a_4558_;
v___y_4587_ = v_a_4559_;
goto v___jp_4583_;
}
}
else
{
lean_del_object(v___x_4581_);
lean_dec(v_a_4579_);
lean_dec(v_a_4577_);
lean_dec_ref(v___x_4575_);
lean_dec_ref(v___x_4573_);
lean_dec(v_a_4564_);
lean_dec_ref(v_h2_4555_);
lean_dec_ref(v_h1_4554_);
v___y_4584_ = v_a_4556_;
v___y_4585_ = v_a_4557_;
v___y_4586_ = v_a_4558_;
v___y_4587_ = v_a_4559_;
goto v___jp_4583_;
}
v___jp_4583_:
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; 
v___x_4588_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4589_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4590_ = l_Lean_indentExpr(v_motive_4553_);
v___x_4591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4591_, 0, v___x_4589_);
lean_ctor_set(v___x_4591_, 1, v___x_4590_);
v___x_4592_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4588_, v___x_4591_, v___y_4584_, v___y_4585_, v___y_4586_, v___y_4587_);
return v___x_4592_;
}
}
}
else
{
lean_dec(v_a_4577_);
lean_dec_ref(v___x_4575_);
lean_dec_ref(v___x_4573_);
lean_dec(v_a_4564_);
lean_dec_ref(v_h2_4555_);
lean_dec_ref(v_h1_4554_);
lean_dec_ref(v_motive_4553_);
return v___x_4578_;
}
}
else
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4622_; 
lean_dec_ref(v___x_4575_);
lean_dec_ref(v___x_4573_);
lean_dec(v_a_4564_);
lean_dec_ref(v_h2_4555_);
lean_dec_ref(v_h1_4554_);
lean_dec_ref(v_motive_4553_);
v_a_4615_ = lean_ctor_get(v___x_4576_, 0);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4622_ == 0)
{
v___x_4617_ = v___x_4576_;
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4576_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4622_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4620_; 
if (v_isShared_4618_ == 0)
{
v___x_4620_ = v___x_4617_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v_a_4615_);
v___x_4620_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4619_;
}
v_reusejp_4619_:
{
return v___x_4620_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4555_);
lean_dec_ref(v_h1_4554_);
lean_dec_ref(v_motive_4553_);
return v___x_4563_;
}
}
else
{
lean_object* v___x_4623_; 
lean_dec_ref(v_h2_4555_);
lean_dec_ref(v_motive_4553_);
v___x_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4623_, 0, v_h1_4554_);
return v___x_4623_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4624_, lean_object* v_h1_4625_, lean_object* v_h2_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_){
_start:
{
lean_object* v_res_4632_; 
v_res_4632_ = l_Lean_Meta_mkEqNDRec(v_motive_4624_, v_h1_4625_, v_h2_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
lean_dec(v_a_4630_);
lean_dec_ref(v_a_4629_);
lean_dec(v_a_4628_);
lean_dec_ref(v_a_4627_);
return v_res_4632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4637_, lean_object* v_h1_4638_, lean_object* v_h2_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_){
_start:
{
lean_object* v___x_4645_; uint8_t v___x_4646_; 
v___x_4645_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4646_ = l_Lean_Expr_isAppOf(v_h2_4639_, v___x_4645_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4647_; 
lean_inc_ref(v_h2_4639_);
v___x_4647_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4649_; lean_object* v___x_4650_; uint8_t v___x_4651_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
lean_dec_ref_known(v___x_4647_, 1);
v___x_4649_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4650_ = lean_unsigned_to_nat(3u);
v___x_4651_ = l_Lean_Expr_isAppOfArity(v_a_4648_, v___x_4649_, v___x_4650_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4656_; 
lean_dec(v_a_4648_);
lean_dec_ref(v_h1_4638_);
lean_dec_ref(v_motive_4637_);
v___x_4652_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4653_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4654_ = l_Lean_indentExpr(v_h2_4639_);
v___x_4655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4655_, 0, v___x_4653_);
lean_ctor_set(v___x_4655_, 1, v___x_4654_);
v___x_4656_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4652_, v___x_4655_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
return v___x_4656_;
}
else
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4657_ = l_Lean_Expr_appFn_x21(v_a_4648_);
v___x_4658_ = l_Lean_Expr_appFn_x21(v___x_4657_);
v___x_4659_ = l_Lean_Expr_appArg_x21(v___x_4658_);
lean_dec_ref(v___x_4658_);
lean_inc_ref(v___x_4659_);
v___x_4660_ = l_Lean_Meta_getLevel(v___x_4659_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
if (lean_obj_tag(v___x_4660_) == 0)
{
lean_object* v_a_4661_; lean_object* v___x_4662_; 
v_a_4661_ = lean_ctor_get(v___x_4660_, 0);
lean_inc(v_a_4661_);
lean_dec_ref_known(v___x_4660_, 1);
lean_inc_ref(v_motive_4637_);
v___x_4662_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4637_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
if (lean_obj_tag(v___x_4662_) == 0)
{
lean_object* v_a_4663_; lean_object* v___x_4665_; uint8_t v_isShared_4666_; uint8_t v_isSharedCheck_4699_; 
v_a_4663_ = lean_ctor_get(v___x_4662_, 0);
v_isSharedCheck_4699_ = !lean_is_exclusive(v___x_4662_);
if (v_isSharedCheck_4699_ == 0)
{
v___x_4665_ = v___x_4662_;
v_isShared_4666_ = v_isSharedCheck_4699_;
goto v_resetjp_4664_;
}
else
{
lean_inc(v_a_4663_);
lean_dec(v___x_4662_);
v___x_4665_ = lean_box(0);
v_isShared_4666_ = v_isSharedCheck_4699_;
goto v_resetjp_4664_;
}
v_resetjp_4664_:
{
lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; 
if (lean_obj_tag(v_a_4663_) == 7)
{
lean_object* v_body_4677_; 
v_body_4677_ = lean_ctor_get(v_a_4663_, 2);
lean_inc_ref(v_body_4677_);
lean_dec_ref_known(v_a_4663_, 3);
if (lean_obj_tag(v_body_4677_) == 7)
{
lean_object* v_body_4678_; 
v_body_4678_ = lean_ctor_get(v_body_4677_, 2);
lean_inc_ref(v_body_4678_);
lean_dec_ref_known(v_body_4677_, 3);
if (lean_obj_tag(v_body_4678_) == 3)
{
lean_object* v_u_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4697_; 
v_u_4679_ = lean_ctor_get(v_body_4678_, 0);
lean_inc(v_u_4679_);
lean_dec_ref_known(v_body_4678_, 1);
v___x_4680_ = l_Lean_Expr_appArg_x21(v___x_4657_);
lean_dec_ref(v___x_4657_);
v___x_4681_ = l_Lean_Expr_appArg_x21(v_a_4648_);
lean_dec(v_a_4648_);
v___x_4682_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4683_ = lean_box(0);
v___x_4684_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4684_, 0, v_a_4661_);
lean_ctor_set(v___x_4684_, 1, v___x_4683_);
v___x_4685_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4685_, 0, v_u_4679_);
lean_ctor_set(v___x_4685_, 1, v___x_4684_);
v___x_4686_ = l_Lean_mkConst(v___x_4682_, v___x_4685_);
v___x_4687_ = lean_unsigned_to_nat(6u);
v___x_4688_ = lean_mk_empty_array_with_capacity(v___x_4687_);
v___x_4689_ = lean_array_push(v___x_4688_, v___x_4659_);
v___x_4690_ = lean_array_push(v___x_4689_, v___x_4680_);
v___x_4691_ = lean_array_push(v___x_4690_, v_motive_4637_);
v___x_4692_ = lean_array_push(v___x_4691_, v_h1_4638_);
v___x_4693_ = lean_array_push(v___x_4692_, v___x_4681_);
v___x_4694_ = lean_array_push(v___x_4693_, v_h2_4639_);
v___x_4695_ = l_Lean_mkAppN(v___x_4686_, v___x_4694_);
lean_dec_ref(v___x_4694_);
if (v_isShared_4666_ == 0)
{
lean_ctor_set(v___x_4665_, 0, v___x_4695_);
v___x_4697_ = v___x_4665_;
goto v_reusejp_4696_;
}
else
{
lean_object* v_reuseFailAlloc_4698_; 
v_reuseFailAlloc_4698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4698_, 0, v___x_4695_);
v___x_4697_ = v_reuseFailAlloc_4698_;
goto v_reusejp_4696_;
}
v_reusejp_4696_:
{
return v___x_4697_;
}
}
else
{
lean_dec_ref(v_body_4678_);
lean_del_object(v___x_4665_);
lean_dec(v_a_4661_);
lean_dec_ref(v___x_4659_);
lean_dec_ref(v___x_4657_);
lean_dec(v_a_4648_);
lean_dec_ref(v_h2_4639_);
lean_dec_ref(v_h1_4638_);
v___y_4668_ = v_a_4640_;
v___y_4669_ = v_a_4641_;
v___y_4670_ = v_a_4642_;
v___y_4671_ = v_a_4643_;
goto v___jp_4667_;
}
}
else
{
lean_dec_ref(v_body_4677_);
lean_del_object(v___x_4665_);
lean_dec(v_a_4661_);
lean_dec_ref(v___x_4659_);
lean_dec_ref(v___x_4657_);
lean_dec(v_a_4648_);
lean_dec_ref(v_h2_4639_);
lean_dec_ref(v_h1_4638_);
v___y_4668_ = v_a_4640_;
v___y_4669_ = v_a_4641_;
v___y_4670_ = v_a_4642_;
v___y_4671_ = v_a_4643_;
goto v___jp_4667_;
}
}
else
{
lean_del_object(v___x_4665_);
lean_dec(v_a_4663_);
lean_dec(v_a_4661_);
lean_dec_ref(v___x_4659_);
lean_dec_ref(v___x_4657_);
lean_dec(v_a_4648_);
lean_dec_ref(v_h2_4639_);
lean_dec_ref(v_h1_4638_);
v___y_4668_ = v_a_4640_;
v___y_4669_ = v_a_4641_;
v___y_4670_ = v_a_4642_;
v___y_4671_ = v_a_4643_;
goto v___jp_4667_;
}
v___jp_4667_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4672_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4673_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4674_ = l_Lean_indentExpr(v_motive_4637_);
v___x_4675_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4673_);
lean_ctor_set(v___x_4675_, 1, v___x_4674_);
v___x_4676_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4672_, v___x_4675_, v___y_4668_, v___y_4669_, v___y_4670_, v___y_4671_);
return v___x_4676_;
}
}
}
else
{
lean_dec(v_a_4661_);
lean_dec_ref(v___x_4659_);
lean_dec_ref(v___x_4657_);
lean_dec(v_a_4648_);
lean_dec_ref(v_h2_4639_);
lean_dec_ref(v_h1_4638_);
lean_dec_ref(v_motive_4637_);
return v___x_4662_;
}
}
else
{
lean_object* v_a_4700_; lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
lean_dec_ref(v___x_4659_);
lean_dec_ref(v___x_4657_);
lean_dec(v_a_4648_);
lean_dec_ref(v_h2_4639_);
lean_dec_ref(v_h1_4638_);
lean_dec_ref(v_motive_4637_);
v_a_4700_ = lean_ctor_get(v___x_4660_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4660_);
if (v_isSharedCheck_4707_ == 0)
{
v___x_4702_ = v___x_4660_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_inc(v_a_4700_);
lean_dec(v___x_4660_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4700_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4639_);
lean_dec_ref(v_h1_4638_);
lean_dec_ref(v_motive_4637_);
return v___x_4647_;
}
}
else
{
lean_object* v___x_4708_; 
lean_dec_ref(v_h2_4639_);
lean_dec_ref(v_motive_4637_);
v___x_4708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4708_, 0, v_h1_4638_);
return v___x_4708_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4709_, lean_object* v_h1_4710_, lean_object* v_h2_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_, lean_object* v_a_4715_, lean_object* v_a_4716_){
_start:
{
lean_object* v_res_4717_; 
v_res_4717_ = l_Lean_Meta_mkEqRec(v_motive_4709_, v_h1_4710_, v_h2_4711_, v_a_4712_, v_a_4713_, v_a_4714_, v_a_4715_);
lean_dec(v_a_4715_);
lean_dec_ref(v_a_4714_);
lean_dec(v_a_4713_);
lean_dec_ref(v_a_4712_);
return v_res_4717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4722_, lean_object* v_pr_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_){
_start:
{
lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
v___x_4729_ = ((lean_object*)(l_Lean_Meta_mkEqMP___closed__1));
v___x_4730_ = lean_unsigned_to_nat(2u);
v___x_4731_ = lean_mk_empty_array_with_capacity(v___x_4730_);
v___x_4732_ = lean_array_push(v___x_4731_, v_eqProof_4722_);
v___x_4733_ = lean_array_push(v___x_4732_, v_pr_4723_);
v___x_4734_ = l_Lean_Meta_mkAppM(v___x_4729_, v___x_4733_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
return v___x_4734_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4735_, lean_object* v_pr_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_){
_start:
{
lean_object* v_res_4742_; 
v_res_4742_ = l_Lean_Meta_mkEqMP(v_eqProof_4735_, v_pr_4736_, v_a_4737_, v_a_4738_, v_a_4739_, v_a_4740_);
lean_dec(v_a_4740_);
lean_dec_ref(v_a_4739_);
lean_dec(v_a_4738_);
lean_dec_ref(v_a_4737_);
return v_res_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4747_, lean_object* v_pr_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_){
_start:
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4754_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4755_ = lean_unsigned_to_nat(2u);
v___x_4756_ = lean_mk_empty_array_with_capacity(v___x_4755_);
v___x_4757_ = lean_array_push(v___x_4756_, v_eqProof_4747_);
v___x_4758_ = lean_array_push(v___x_4757_, v_pr_4748_);
v___x_4759_ = l_Lean_Meta_mkAppM(v___x_4754_, v___x_4758_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4760_, lean_object* v_pr_4761_, lean_object* v_a_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l_Lean_Meta_mkEqMPR(v_eqProof_4760_, v_pr_4761_, v_a_4762_, v_a_4763_, v_a_4764_, v_a_4765_);
lean_dec(v_a_4765_);
lean_dec_ref(v_a_4764_);
lean_dec(v_a_4763_);
lean_dec_ref(v_a_4762_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v___f_4774_; lean_object* v___x_12328__overap_4775_; lean_object* v___x_4776_; 
v___f_4774_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12328__overap_4775_ = lean_panic_fn_borrowed(v___f_4774_, v_msg_4768_);
lean_inc(v___y_4772_);
lean_inc_ref(v___y_4771_);
lean_inc(v___y_4770_);
lean_inc_ref(v___y_4769_);
v___x_4776_ = lean_apply_5(v___x_12328__overap_4775_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, lean_box(0));
return v___x_4776_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4784_, uint8_t v_skipRealize_4785_, lean_object* v___y_4786_){
_start:
{
lean_object* v___x_4788_; lean_object* v_env_4789_; uint8_t v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4788_ = lean_st_ref_get(v___y_4786_);
v_env_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc_ref(v_env_4789_);
lean_dec(v___x_4788_);
v___x_4790_ = l_Lean_Environment_contains(v_env_4789_, v_constName_4784_, v_skipRealize_4785_);
v___x_4791_ = lean_box(v___x_4790_);
v___x_4792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4792_, 0, v___x_4791_);
return v___x_4792_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4793_, lean_object* v_skipRealize_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
uint8_t v_skipRealize_boxed_4797_; lean_object* v_res_4798_; 
v_skipRealize_boxed_4797_ = lean_unbox(v_skipRealize_4794_);
v_res_4798_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4793_, v_skipRealize_boxed_4797_, v___y_4795_);
lean_dec(v___y_4795_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4799_, uint8_t v_skipRealize_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4799_, v_skipRealize_4800_, v___y_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4807_, lean_object* v_skipRealize_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
uint8_t v_skipRealize_boxed_4814_; lean_object* v_res_4815_; 
v_skipRealize_boxed_4814_ = lean_unbox(v_skipRealize_4808_);
v_res_4815_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4807_, v_skipRealize_boxed_4814_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
return v_res_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___y_4816_, uint8_t v___x_4817_, lean_object* v_P_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4826_; uint8_t v___x_4827_; lean_object* v___x_4828_; 
v___x_4824_ = lean_unsigned_to_nat(1u);
v___x_4825_ = lean_mk_empty_array_with_capacity(v___x_4824_);
lean_inc_ref(v_P_4818_);
v___x_4826_ = lean_array_push(v___x_4825_, v_P_4818_);
v___x_4827_ = 1;
v___x_4828_ = l_Lean_Meta_mkLambdaFVars(v___x_4826_, v_P_4818_, v___y_4816_, v___x_4817_, v___y_4816_, v___x_4817_, v___x_4827_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
lean_dec_ref(v___x_4826_);
return v___x_4828_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___y_4829_, lean_object* v___x_4830_, lean_object* v_P_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
uint8_t v___y_13571__boxed_4837_; uint8_t v___x_13572__boxed_4838_; lean_object* v_res_4839_; 
v___y_13571__boxed_4837_ = lean_unbox(v___y_4829_);
v___x_13572__boxed_4838_ = lean_unbox(v___x_4830_);
v_res_4839_ = l_Lean_Meta_mkNoConfusion___lam__0(v___y_13571__boxed_4837_, v___x_13572__boxed_4838_, v_P_4831_, v___y_4832_, v___y_4833_, v___y_4834_, v___y_4835_);
lean_dec(v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec(v___y_4833_);
lean_dec_ref(v___y_4832_);
return v_res_4839_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4842_ = l_Lean_stringToMessageData(v___x_4841_);
return v___x_4842_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4845_ = l_Lean_stringToMessageData(v___x_4844_);
return v___x_4845_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4846_, lean_object* v_b_4847_, lean_object* v_i_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_){
_start:
{
lean_object* v_stop_4854_; lean_object* v_step_4855_; lean_object* v_a_4857_; uint8_t v___x_4860_; 
v_stop_4854_ = lean_ctor_get(v_range_4846_, 1);
v_step_4855_ = lean_ctor_get(v_range_4846_, 2);
v___x_4860_ = lean_nat_dec_lt(v_i_4848_, v_stop_4854_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; 
lean_dec(v_i_4848_);
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v_b_4847_);
return v___x_4861_;
}
else
{
lean_object* v___x_4862_; 
lean_inc(v___y_4852_);
lean_inc_ref(v___y_4851_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc_ref(v_b_4847_);
v___x_4862_ = lean_infer_type(v_b_4847_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4864_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v___x_4864_ = l_Lean_Meta_whnfForall(v_a_4863_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref_known(v___x_4864_, 1);
v___x_4866_ = l_Lean_Expr_bindingDomain_x21(v_a_4865_);
lean_dec(v_a_4865_);
lean_inc(v___y_4852_);
lean_inc_ref(v___y_4851_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
v___x_4867_ = lean_whnf(v___x_4866_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; uint8_t v___x_4871_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_a_4868_);
lean_dec_ref_known(v___x_4867_, 1);
v___x_4869_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4870_ = lean_unsigned_to_nat(4u);
v___x_4871_ = l_Lean_Expr_isAppOfArity(v_a_4868_, v___x_4869_, v___x_4870_);
if (v___x_4871_ == 0)
{
lean_object* v___x_4872_; lean_object* v___x_4873_; uint8_t v___x_4874_; 
v___x_4872_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4873_ = lean_unsigned_to_nat(3u);
v___x_4874_ = l_Lean_Expr_isAppOfArity(v_a_4868_, v___x_4872_, v___x_4873_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; 
lean_dec(v_i_4848_);
lean_inc(v___y_4852_);
lean_inc_ref(v___y_4851_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
v___x_4875_ = lean_infer_type(v_b_4847_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v_a_4886_; lean_object* v___x_4888_; uint8_t v_isShared_4889_; uint8_t v_isSharedCheck_4893_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___x_4875_, 1);
v___x_4877_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4878_ = l_Lean_MessageData_ofExpr(v_a_4868_);
v___x_4879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4877_);
lean_ctor_set(v___x_4879_, 1, v___x_4878_);
v___x_4880_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4879_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = lean_unsigned_to_nat(30u);
v___x_4883_ = l_Lean_inlineExpr(v_a_4876_, v___x_4882_);
v___x_4884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4881_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4884_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
v_a_4886_ = lean_ctor_get(v___x_4885_, 0);
v_isSharedCheck_4893_ = !lean_is_exclusive(v___x_4885_);
if (v_isSharedCheck_4893_ == 0)
{
v___x_4888_ = v___x_4885_;
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
else
{
lean_inc(v_a_4886_);
lean_dec(v___x_4885_);
v___x_4888_ = lean_box(0);
v_isShared_4889_ = v_isSharedCheck_4893_;
goto v_resetjp_4887_;
}
v_resetjp_4887_:
{
lean_object* v___x_4891_; 
if (v_isShared_4889_ == 0)
{
v___x_4891_ = v___x_4888_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4892_; 
v_reuseFailAlloc_4892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4892_, 0, v_a_4886_);
v___x_4891_ = v_reuseFailAlloc_4892_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
return v___x_4891_;
}
}
}
else
{
lean_dec(v_a_4868_);
return v___x_4875_;
}
}
else
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
v___x_4894_ = l_Lean_Expr_appFn_x21(v_a_4868_);
lean_dec(v_a_4868_);
v___x_4895_ = l_Lean_Expr_appArg_x21(v___x_4894_);
lean_dec_ref(v___x_4894_);
v___x_4896_ = l_Lean_Meta_mkEqRefl(v___x_4895_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v_a_4897_; lean_object* v___x_4898_; 
v_a_4897_ = lean_ctor_get(v___x_4896_, 0);
lean_inc(v_a_4897_);
lean_dec_ref_known(v___x_4896_, 1);
v___x_4898_ = l_Lean_Expr_app___override(v_b_4847_, v_a_4897_);
v_a_4857_ = v___x_4898_;
goto v___jp_4856_;
}
else
{
lean_dec(v_i_4848_);
lean_dec_ref(v_b_4847_);
return v___x_4896_;
}
}
}
else
{
lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; 
v___x_4899_ = l_Lean_Expr_appFn_x21(v_a_4868_);
lean_dec(v_a_4868_);
v___x_4900_ = l_Lean_Expr_appFn_x21(v___x_4899_);
lean_dec_ref(v___x_4899_);
v___x_4901_ = l_Lean_Expr_appArg_x21(v___x_4900_);
lean_dec_ref(v___x_4900_);
v___x_4902_ = l_Lean_Meta_mkHEqRefl(v___x_4901_, v___y_4849_, v___y_4850_, v___y_4851_, v___y_4852_);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v_a_4903_; lean_object* v___x_4904_; 
v_a_4903_ = lean_ctor_get(v___x_4902_, 0);
lean_inc(v_a_4903_);
lean_dec_ref_known(v___x_4902_, 1);
v___x_4904_ = l_Lean_Expr_app___override(v_b_4847_, v_a_4903_);
v_a_4857_ = v___x_4904_;
goto v___jp_4856_;
}
else
{
lean_dec(v_i_4848_);
lean_dec_ref(v_b_4847_);
return v___x_4902_;
}
}
}
else
{
lean_dec(v_i_4848_);
lean_dec_ref(v_b_4847_);
return v___x_4867_;
}
}
else
{
lean_dec(v_i_4848_);
lean_dec_ref(v_b_4847_);
return v___x_4864_;
}
}
else
{
lean_dec(v_i_4848_);
lean_dec_ref(v_b_4847_);
return v___x_4862_;
}
}
v___jp_4856_:
{
lean_object* v___x_4858_; 
v___x_4858_ = lean_nat_add(v_i_4848_, v_step_4855_);
lean_dec(v_i_4848_);
v_b_4847_ = v_a_4857_;
v_i_4848_ = v___x_4858_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4905_, lean_object* v_b_4906_, lean_object* v_i_4907_, lean_object* v___y_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v_res_4913_; 
v_res_4913_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4905_, v_b_4906_, v_i_4907_, v___y_4908_, v___y_4909_, v___y_4910_, v___y_4911_);
lean_dec(v___y_4911_);
lean_dec_ref(v___y_4910_);
lean_dec(v___y_4909_);
lean_dec_ref(v___y_4908_);
lean_dec_ref(v_range_4905_);
return v_res_4913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4914_, lean_object* v_b_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_){
_start:
{
lean_object* v___x_4921_; 
lean_inc(v___y_4919_);
lean_inc_ref(v___y_4918_);
lean_inc(v___y_4917_);
lean_inc_ref(v___y_4916_);
v___x_4921_ = lean_apply_6(v_k_4914_, v_b_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, lean_box(0));
return v___x_4921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4922_, lean_object* v_b_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4922_, v_b_4923_, v___y_4924_, v___y_4925_, v___y_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec_ref(v___y_4926_);
lean_dec(v___y_4925_);
lean_dec_ref(v___y_4924_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4930_, uint8_t v_bi_4931_, lean_object* v_type_4932_, lean_object* v_k_4933_, uint8_t v_kind_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_, lean_object* v___y_4937_, lean_object* v___y_4938_){
_start:
{
lean_object* v___f_4940_; lean_object* v___x_4941_; 
v___f_4940_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4940_, 0, v_k_4933_);
v___x_4941_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4930_, v_bi_4931_, v_type_4932_, v___f_4940_, v_kind_4934_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
if (lean_obj_tag(v___x_4941_) == 0)
{
lean_object* v_a_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4949_; 
v_a_4942_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4949_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4949_ == 0)
{
v___x_4944_ = v___x_4941_;
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
else
{
lean_inc(v_a_4942_);
lean_dec(v___x_4941_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4949_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
lean_object* v___x_4947_; 
if (v_isShared_4945_ == 0)
{
v___x_4947_ = v___x_4944_;
goto v_reusejp_4946_;
}
else
{
lean_object* v_reuseFailAlloc_4948_; 
v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4948_, 0, v_a_4942_);
v___x_4947_ = v_reuseFailAlloc_4948_;
goto v_reusejp_4946_;
}
v_reusejp_4946_:
{
return v___x_4947_;
}
}
}
else
{
lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_a_4950_ = lean_ctor_get(v___x_4941_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4941_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4941_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4941_);
v___x_4952_ = lean_box(0);
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
v_resetjp_4951_:
{
lean_object* v___x_4955_; 
if (v_isShared_4953_ == 0)
{
v___x_4955_ = v___x_4952_;
goto v_reusejp_4954_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
v___x_4955_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4954_;
}
v_reusejp_4954_:
{
return v___x_4955_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_4958_, lean_object* v_bi_4959_, lean_object* v_type_4960_, lean_object* v_k_4961_, lean_object* v_kind_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_){
_start:
{
uint8_t v_bi_boxed_4968_; uint8_t v_kind_boxed_4969_; lean_object* v_res_4970_; 
v_bi_boxed_4968_ = lean_unbox(v_bi_4959_);
v_kind_boxed_4969_ = lean_unbox(v_kind_4962_);
v_res_4970_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4958_, v_bi_boxed_4968_, v_type_4960_, v_k_4961_, v_kind_boxed_4969_, v___y_4963_, v___y_4964_, v___y_4965_, v___y_4966_);
lean_dec(v___y_4966_);
lean_dec_ref(v___y_4965_);
lean_dec(v___y_4964_);
lean_dec_ref(v___y_4963_);
return v_res_4970_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_4971_, lean_object* v_type_4972_, lean_object* v_k_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_){
_start:
{
uint8_t v___x_4979_; uint8_t v___x_4980_; lean_object* v___x_4981_; 
v___x_4979_ = 0;
v___x_4980_ = 0;
v___x_4981_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4971_, v___x_4979_, v_type_4972_, v_k_4973_, v___x_4980_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_4982_, lean_object* v_type_4983_, lean_object* v_k_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_4982_, v_type_4983_, v_k_4984_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
lean_dec(v___y_4986_);
lean_dec_ref(v___y_4985_);
return v_res_4990_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_4997_; lean_object* v___x_4998_; 
v___x_4997_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_4998_ = l_Lean_MessageData_ofFormat(v___x_4997_);
return v___x_4998_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__7(void){
_start:
{
lean_object* v___x_5002_; lean_object* v___x_5003_; 
v___x_5002_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__6));
v___x_5003_ = l_Lean_MessageData_ofFormat(v___x_5002_);
return v___x_5003_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__9(void){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_5005_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__8));
v___x_5006_ = l_Lean_stringToMessageData(v___x_5005_);
return v___x_5006_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_5008_; lean_object* v___x_5009_; 
v___x_5008_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_5009_ = l_Lean_stringToMessageData(v___x_5008_);
return v___x_5009_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__14(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5012_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__13));
v___x_5013_ = lean_unsigned_to_nat(10u);
v___x_5014_ = lean_unsigned_to_nat(490u);
v___x_5015_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5016_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5017_ = l_mkPanicMessageWithDecl(v___x_5016_, v___x_5015_, v___x_5014_, v___x_5013_, v___x_5012_);
return v___x_5017_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; 
v___x_5019_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5020_ = l_Lean_stringToMessageData(v___x_5019_);
return v___x_5020_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__23(void){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5029_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__22));
v___x_5030_ = l_Lean_stringToMessageData(v___x_5029_);
return v___x_5030_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__24(void){
_start:
{
lean_object* v___x_5031_; lean_object* v___x_5032_; 
v___x_5031_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5032_ = l_Lean_MessageData_ofName(v___x_5031_);
return v___x_5032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5033_, lean_object* v_h_5034_, lean_object* v_a_5035_, lean_object* v_a_5036_, lean_object* v_a_5037_, lean_object* v_a_5038_){
_start:
{
lean_object* v___x_5040_; 
lean_inc(v_a_5038_);
lean_inc_ref(v_a_5037_);
lean_inc(v_a_5036_);
lean_inc_ref(v_a_5035_);
lean_inc_ref(v_h_5034_);
v___x_5040_ = lean_infer_type(v_h_5034_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
if (lean_obj_tag(v___x_5040_) == 0)
{
lean_object* v_a_5041_; lean_object* v___x_5042_; 
v_a_5041_ = lean_ctor_get(v___x_5040_, 0);
lean_inc(v_a_5041_);
lean_dec_ref_known(v___x_5040_, 1);
lean_inc(v_a_5038_);
lean_inc_ref(v_a_5037_);
lean_inc(v_a_5036_);
lean_inc_ref(v_a_5035_);
v___x_5042_ = lean_whnf(v_a_5041_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; uint8_t v___x_5046_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v___x_5044_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5045_ = lean_unsigned_to_nat(3u);
v___x_5046_ = l_Lean_Expr_isAppOfArity(v_a_5043_, v___x_5044_, v___x_5045_);
if (v___x_5046_ == 0)
{
lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; 
lean_dec_ref(v_target_5033_);
v___x_5047_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5048_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5049_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5034_, v_a_5043_);
v___x_5050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5050_, 0, v___x_5048_);
lean_ctor_set(v___x_5050_, 1, v___x_5049_);
v___x_5051_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5047_, v___x_5050_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
return v___x_5051_;
}
else
{
lean_object* v___x_5052_; lean_object* v___x_5053_; lean_object* v___x_5054_; lean_object* v___x_5055_; 
v___x_5052_ = l_Lean_Expr_appFn_x21(v_a_5043_);
v___x_5053_ = l_Lean_Expr_appFn_x21(v___x_5052_);
v___x_5054_ = l_Lean_Expr_appArg_x21(v___x_5053_);
lean_dec_ref(v___x_5053_);
v___x_5055_ = l_Lean_Meta_whnfD(v___x_5054_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
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
v___x_5070_ = lean_st_ref_get(v_a_5038_);
v_env_5071_ = lean_ctor_get(v___x_5070_, 0);
lean_inc_ref(v_env_5071_);
lean_dec(v___x_5070_);
v___x_5072_ = 0;
v___x_5073_ = l_Lean_Environment_find_x3f(v_env_5071_, v_declName_5068_, v___x_5072_);
if (lean_obj_tag(v___x_5073_) == 0)
{
lean_dec(v_us_5069_);
lean_dec_ref(v___x_5052_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v___y_5058_ = v_a_5035_;
v___y_5059_ = v_a_5036_;
v___y_5060_ = v_a_5037_;
v___y_5061_ = v_a_5038_;
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
lean_inc_ref(v_target_5033_);
v___x_5076_ = l_Lean_Meta_getLevel(v_target_5033_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___x_5076_, 1);
v___x_5078_ = l_Lean_Expr_appArg_x21(v___x_5052_);
lean_dec_ref(v___x_5052_);
lean_inc_ref(v___x_5078_);
v___x_5079_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5078_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
if (lean_obj_tag(v___x_5079_) == 0)
{
lean_object* v_a_5080_; lean_object* v___x_5081_; lean_object* v___y_5083_; lean_object* v___y_5084_; lean_object* v___y_5085_; lean_object* v___y_5086_; 
v_a_5080_ = lean_ctor_get(v___x_5079_, 0);
lean_inc(v_a_5080_);
lean_dec_ref_known(v___x_5079_, 1);
v___x_5081_ = l_Lean_Expr_appArg_x21(v_a_5043_);
lean_dec(v_a_5043_);
if (lean_obj_tag(v_a_5080_) == 1)
{
lean_object* v_val_5095_; lean_object* v_fst_5096_; lean_object* v_snd_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5311_; 
v_val_5095_ = lean_ctor_get(v_a_5080_, 0);
lean_inc(v_val_5095_);
lean_dec_ref_known(v_a_5080_, 1);
v_fst_5096_ = lean_ctor_get(v_val_5095_, 0);
v_snd_5097_ = lean_ctor_get(v_val_5095_, 1);
v_isSharedCheck_5311_ = !lean_is_exclusive(v_val_5095_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5099_ = v_val_5095_;
v_isShared_5100_ = v_isSharedCheck_5311_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_snd_5097_);
lean_inc(v_fst_5096_);
lean_dec(v_val_5095_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5311_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
lean_object* v___x_5101_; 
lean_inc_ref(v___x_5081_);
v___x_5101_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5081_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc(v_a_5102_);
lean_dec_ref_known(v___x_5101_, 1);
if (lean_obj_tag(v_a_5102_) == 1)
{
lean_object* v_val_5103_; lean_object* v_fst_5104_; lean_object* v_snd_5105_; lean_object* v___x_5107_; uint8_t v_isShared_5108_; uint8_t v_isSharedCheck_5302_; 
v_val_5103_ = lean_ctor_get(v_a_5102_, 0);
lean_inc(v_val_5103_);
lean_dec_ref_known(v_a_5102_, 1);
v_fst_5104_ = lean_ctor_get(v_val_5103_, 0);
v_snd_5105_ = lean_ctor_get(v_val_5103_, 1);
v_isSharedCheck_5302_ = !lean_is_exclusive(v_val_5103_);
if (v_isSharedCheck_5302_ == 0)
{
v___x_5107_ = v_val_5103_;
v_isShared_5108_ = v_isSharedCheck_5302_;
goto v_resetjp_5106_;
}
else
{
lean_inc(v_snd_5105_);
lean_inc(v_fst_5104_);
lean_dec(v_val_5103_);
v___x_5107_ = lean_box(0);
v_isShared_5108_ = v_isSharedCheck_5302_;
goto v_resetjp_5106_;
}
v_resetjp_5106_:
{
lean_object* v_toConstantVal_5109_; lean_object* v_cidx_5110_; lean_object* v_numParams_5111_; lean_object* v_numFields_5112_; lean_object* v___y_5114_; lean_object* v___y_5115_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v___y_5118_; lean_object* v___y_5119_; uint8_t v___y_5204_; lean_object* v_cidx_5232_; uint8_t v___x_5233_; 
v_toConstantVal_5109_ = lean_ctor_get(v_fst_5096_, 0);
lean_inc_ref(v_toConstantVal_5109_);
v_cidx_5110_ = lean_ctor_get(v_fst_5096_, 2);
lean_inc(v_cidx_5110_);
v_numParams_5111_ = lean_ctor_get(v_fst_5096_, 3);
lean_inc(v_numParams_5111_);
v_numFields_5112_ = lean_ctor_get(v_fst_5096_, 4);
lean_inc(v_numFields_5112_);
lean_dec(v_fst_5096_);
v_cidx_5232_ = lean_ctor_get(v_fst_5104_, 2);
lean_inc(v_cidx_5232_);
lean_dec(v_fst_5104_);
v___x_5233_ = lean_nat_dec_eq(v_cidx_5110_, v_cidx_5232_);
lean_dec(v_cidx_5232_);
lean_dec(v_cidx_5110_);
if (v___x_5233_ == 0)
{
if (v___x_5046_ == 0)
{
lean_dec_ref(v___x_5081_);
lean_dec_ref(v___x_5078_);
lean_dec_ref(v_val_5075_);
v___y_5204_ = v___x_5046_;
goto v___jp_5203_;
}
else
{
lean_object* v_toConstantVal_5234_; lean_object* v_name_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v_a_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v_a_5242_; uint8_t v___x_5260_; 
lean_dec(v_numFields_5112_);
lean_dec(v_numParams_5111_);
lean_dec_ref(v_toConstantVal_5109_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_del_object(v___x_5099_);
lean_dec(v_snd_5097_);
v_toConstantVal_5234_ = lean_ctor_get(v_val_5075_, 0);
lean_inc_ref(v_toConstantVal_5234_);
lean_dec_ref(v_val_5075_);
v_name_5235_ = lean_ctor_get(v_toConstantVal_5234_, 0);
lean_inc(v_name_5235_);
lean_dec_ref(v_toConstantVal_5234_);
v___x_5236_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5237_ = l_Lean_Name_str___override(v_name_5235_, v___x_5236_);
lean_inc(v___x_5237_);
v___x_5238_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5237_, v___x_5046_, v_a_5038_);
v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
lean_inc(v_a_5239_);
lean_dec_ref(v___x_5238_);
v___x_5240_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5241_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5240_, v___x_5046_, v_a_5038_);
v_a_5242_ = lean_ctor_get(v___x_5241_, 0);
lean_inc(v_a_5242_);
lean_dec_ref(v___x_5241_);
v___x_5260_ = lean_unbox(v_a_5239_);
lean_dec(v_a_5239_);
if (v___x_5260_ == 0)
{
lean_dec(v_a_5242_);
lean_dec_ref(v___x_5081_);
lean_dec_ref(v___x_5078_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
goto v___jp_5243_;
}
else
{
uint8_t v___x_5261_; 
v___x_5261_ = lean_unbox(v_a_5242_);
lean_dec(v_a_5242_);
if (v___x_5261_ == 0)
{
lean_dec_ref(v___x_5081_);
lean_dec_ref(v___x_5078_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
goto v___jp_5243_;
}
else
{
lean_object* v_dummy_5262_; lean_object* v_nargs_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; 
v_dummy_5262_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5263_ = l_Lean_Expr_getAppNumArgs(v_a_5056_);
lean_inc(v_nargs_5263_);
v___x_5264_ = lean_mk_array(v_nargs_5263_, v_dummy_5262_);
v___x_5265_ = lean_unsigned_to_nat(1u);
v___x_5266_ = lean_nat_sub(v_nargs_5263_, v___x_5265_);
lean_dec(v_nargs_5263_);
lean_inc_n(v_a_5056_, 2);
v___x_5267_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5056_, v___x_5264_, v___x_5266_);
v___x_5268_ = l_Lean_Meta_getLevel(v_a_5056_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
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
v___x_5273_ = l_Lean_mkConst(v___x_5237_, v_us_5069_);
v___x_5274_ = l_Lean_mkAppN(v___x_5273_, v___x_5267_);
lean_dec_ref(v___x_5267_);
v___x_5275_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5276_ = lean_box(0);
v___x_5277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5277_, 0, v_a_5077_);
lean_ctor_set(v___x_5277_, 1, v___x_5276_);
v___x_5278_ = l_Lean_mkConst(v___x_5275_, v___x_5277_);
v___x_5279_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5279_, 0, v_a_5269_);
lean_ctor_set(v___x_5279_, 1, v___x_5276_);
v___x_5280_ = l_Lean_mkConst(v___x_5240_, v___x_5279_);
v___x_5281_ = lean_unsigned_to_nat(5u);
v___x_5282_ = lean_mk_empty_array_with_capacity(v___x_5281_);
v___x_5283_ = lean_array_push(v___x_5282_, v_a_5056_);
v___x_5284_ = lean_array_push(v___x_5283_, v___x_5274_);
v___x_5285_ = lean_array_push(v___x_5284_, v___x_5078_);
v___x_5286_ = lean_array_push(v___x_5285_, v___x_5081_);
v___x_5287_ = lean_array_push(v___x_5286_, v_h_5034_);
v___x_5288_ = l_Lean_mkAppN(v___x_5280_, v___x_5287_);
lean_dec_ref(v___x_5287_);
v___x_5289_ = l_Lean_mkAppB(v___x_5278_, v_target_5033_, v___x_5288_);
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
lean_dec_ref(v___x_5081_);
lean_dec_ref(v___x_5078_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
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
v___x_5251_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5250_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
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
lean_dec_ref(v___x_5081_);
lean_dec_ref(v___x_5078_);
lean_dec_ref(v_val_5075_);
v___y_5204_ = v___x_5072_;
goto v___jp_5203_;
}
v___jp_5113_:
{
lean_object* v___x_5120_; 
lean_inc(v___y_5115_);
v___x_5120_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5120_) == 0)
{
lean_object* v_a_5121_; lean_object* v_nargs_5122_; lean_object* v_type_5123_; lean_object* v___x_5125_; uint8_t v_isShared_5126_; uint8_t v_isSharedCheck_5192_; 
v_a_5121_ = lean_ctor_get(v___x_5120_, 0);
lean_inc(v_a_5121_);
lean_dec_ref_known(v___x_5120_, 1);
v_nargs_5122_ = l_Lean_Expr_getAppNumArgs(v_a_5056_);
v_type_5123_ = lean_ctor_get(v_a_5121_, 2);
v_isSharedCheck_5192_ = !lean_is_exclusive(v_a_5121_);
if (v_isSharedCheck_5192_ == 0)
{
lean_object* v_unused_5193_; lean_object* v_unused_5194_; 
v_unused_5193_ = lean_ctor_get(v_a_5121_, 1);
lean_dec(v_unused_5193_);
v_unused_5194_ = lean_ctor_get(v_a_5121_, 0);
lean_dec(v_unused_5194_);
v___x_5125_ = v_a_5121_;
v_isShared_5126_ = v_isSharedCheck_5192_;
goto v_resetjp_5124_;
}
else
{
lean_inc(v_type_5123_);
lean_dec(v_a_5121_);
v___x_5125_ = lean_box(0);
v_isShared_5126_ = v_isSharedCheck_5192_;
goto v_resetjp_5124_;
}
v_resetjp_5124_:
{
lean_object* v_dummy_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v_start_5133_; lean_object* v_stop_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; uint8_t v___x_5148_; 
v_dummy_5127_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
lean_inc(v_nargs_5122_);
v___x_5128_ = lean_mk_array(v_nargs_5122_, v_dummy_5127_);
v___x_5129_ = lean_unsigned_to_nat(1u);
v___x_5130_ = lean_nat_sub(v_nargs_5122_, v___x_5129_);
lean_dec(v_nargs_5122_);
v___x_5131_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5056_, v___x_5128_, v___x_5130_);
lean_inc_n(v_numParams_5111_, 2);
lean_inc(v___y_5114_);
v___x_5132_ = l_Array_toSubarray___redArg(v___x_5131_, v___y_5114_, v_numParams_5111_);
v_start_5133_ = lean_ctor_get(v___x_5132_, 1);
lean_inc(v_start_5133_);
v_stop_5134_ = lean_ctor_get(v___x_5132_, 2);
lean_inc(v_stop_5134_);
v___x_5135_ = lean_array_get_size(v_snd_5097_);
v___x_5136_ = l_Array_toSubarray___redArg(v_snd_5097_, v_numParams_5111_, v___x_5135_);
v___x_5137_ = lean_array_get_size(v_snd_5105_);
v___x_5138_ = l_Subarray_copy___redArg(v___x_5136_);
v___x_5139_ = l_Array_toSubarray___redArg(v_snd_5105_, v_numParams_5111_, v___x_5137_);
v___x_5140_ = l_Subarray_copy___redArg(v___x_5139_);
v___x_5141_ = l_Lean_Expr_getNumHeadForalls(v_type_5123_);
lean_dec_ref(v_type_5123_);
v___x_5142_ = lean_nat_sub(v_stop_5134_, v_start_5133_);
lean_dec(v_start_5133_);
lean_dec(v_stop_5134_);
v___x_5143_ = lean_array_get_size(v___x_5138_);
v___x_5144_ = lean_nat_add(v___x_5142_, v___x_5143_);
lean_dec(v___x_5142_);
v___x_5145_ = lean_array_get_size(v___x_5140_);
v___x_5146_ = lean_nat_add(v___x_5144_, v___x_5145_);
lean_dec(v___x_5144_);
v___x_5147_ = lean_nat_add(v___x_5146_, v___x_5045_);
lean_dec(v___x_5146_);
v___x_5148_ = lean_nat_dec_le(v___x_5147_, v___x_5141_);
if (v___x_5148_ == 0)
{
lean_object* v___x_5149_; lean_object* v___x_5150_; 
lean_dec(v___x_5147_);
lean_dec(v___x_5141_);
lean_dec_ref(v___x_5140_);
lean_dec_ref(v___x_5138_);
lean_dec_ref(v___x_5132_);
lean_del_object(v___x_5125_);
lean_dec(v___y_5115_);
lean_dec(v___y_5114_);
lean_del_object(v___x_5107_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v___x_5149_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__14, &l_Lean_Meta_mkNoConfusion___closed__14_once, _init_l_Lean_Meta_mkNoConfusion___closed__14);
v___x_5150_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5149_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
return v___x_5150_;
}
else
{
lean_object* v___x_5152_; 
if (v_isShared_5108_ == 0)
{
lean_ctor_set_tag(v___x_5107_, 1);
lean_ctor_set(v___x_5107_, 1, v_us_5069_);
lean_ctor_set(v___x_5107_, 0, v_a_5077_);
v___x_5152_ = v___x_5107_;
goto v_reusejp_5151_;
}
else
{
lean_object* v_reuseFailAlloc_5191_; 
v_reuseFailAlloc_5191_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5191_, 0, v_a_5077_);
lean_ctor_set(v_reuseFailAlloc_5191_, 1, v_us_5069_);
v___x_5152_ = v_reuseFailAlloc_5191_;
goto v_reusejp_5151_;
}
v_reusejp_5151_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; lean_object* v___x_5158_; lean_object* v___x_5159_; lean_object* v___x_5160_; lean_object* v___x_5161_; lean_object* v___x_5163_; 
v___x_5153_ = l_Lean_mkConst(v___y_5115_, v___x_5152_);
v___x_5154_ = l_Subarray_copy___redArg(v___x_5132_);
v___x_5155_ = l_Lean_mkAppN(v___x_5153_, v___x_5154_);
lean_dec_ref(v___x_5154_);
v___x_5156_ = lean_mk_empty_array_with_capacity(v___x_5129_);
v___x_5157_ = lean_array_push(v___x_5156_, v_target_5033_);
v___x_5158_ = l_Array_append___redArg(v___x_5157_, v___x_5138_);
lean_dec_ref(v___x_5138_);
v___x_5159_ = l_Array_append___redArg(v___x_5158_, v___x_5140_);
lean_dec_ref(v___x_5140_);
v___x_5160_ = l_Lean_mkAppN(v___x_5155_, v___x_5159_);
lean_dec_ref(v___x_5159_);
v___x_5161_ = lean_nat_sub(v___x_5141_, v___x_5147_);
lean_dec(v___x_5147_);
lean_dec(v___x_5141_);
lean_inc(v___y_5114_);
if (v_isShared_5126_ == 0)
{
lean_ctor_set(v___x_5125_, 2, v___x_5129_);
lean_ctor_set(v___x_5125_, 1, v___x_5161_);
lean_ctor_set(v___x_5125_, 0, v___y_5114_);
v___x_5163_ = v___x_5125_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5190_; 
v_reuseFailAlloc_5190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5190_, 0, v___y_5114_);
lean_ctor_set(v_reuseFailAlloc_5190_, 1, v___x_5161_);
lean_ctor_set(v_reuseFailAlloc_5190_, 2, v___x_5129_);
v___x_5163_ = v_reuseFailAlloc_5190_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
lean_object* v___x_5164_; 
v___x_5164_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5163_, v___x_5160_, v___y_5114_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
lean_dec_ref(v___x_5163_);
if (lean_obj_tag(v___x_5164_) == 0)
{
lean_object* v_a_5165_; lean_object* v___x_5166_; 
v_a_5165_ = lean_ctor_get(v___x_5164_, 0);
lean_inc_n(v_a_5165_, 2);
lean_dec_ref_known(v___x_5164_, 1);
lean_inc(v___y_5119_);
lean_inc_ref(v___y_5118_);
lean_inc(v___y_5117_);
lean_inc_ref(v___y_5116_);
v___x_5166_ = lean_infer_type(v_a_5165_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5168_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
lean_inc(v_a_5167_);
lean_dec_ref_known(v___x_5166_, 1);
v___x_5168_ = l_Lean_Meta_whnfForall(v_a_5167_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v_a_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5189_; 
v_a_5169_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5171_ = v___x_5168_;
v_isShared_5172_ = v_isSharedCheck_5189_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_a_5169_);
lean_dec(v___x_5168_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5189_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___x_5173_; uint8_t v___x_5174_; 
v___x_5173_ = l_Lean_Expr_bindingDomain_x21(v_a_5169_);
lean_dec(v_a_5169_);
v___x_5174_ = l_Lean_Expr_isHEq(v___x_5173_);
lean_dec_ref(v___x_5173_);
if (v___x_5174_ == 0)
{
lean_object* v___x_5175_; lean_object* v___x_5177_; 
v___x_5175_ = l_Lean_Expr_app___override(v_a_5165_, v_h_5034_);
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 0, v___x_5175_);
v___x_5177_ = v___x_5171_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v___x_5175_);
v___x_5177_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
return v___x_5177_;
}
}
else
{
lean_object* v___x_5179_; 
lean_del_object(v___x_5171_);
v___x_5179_ = l_Lean_Meta_mkHEqOfEq(v_h_5034_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_);
if (lean_obj_tag(v___x_5179_) == 0)
{
lean_object* v_a_5180_; lean_object* v___x_5182_; uint8_t v_isShared_5183_; uint8_t v_isSharedCheck_5188_; 
v_a_5180_ = lean_ctor_get(v___x_5179_, 0);
v_isSharedCheck_5188_ = !lean_is_exclusive(v___x_5179_);
if (v_isSharedCheck_5188_ == 0)
{
v___x_5182_ = v___x_5179_;
v_isShared_5183_ = v_isSharedCheck_5188_;
goto v_resetjp_5181_;
}
else
{
lean_inc(v_a_5180_);
lean_dec(v___x_5179_);
v___x_5182_ = lean_box(0);
v_isShared_5183_ = v_isSharedCheck_5188_;
goto v_resetjp_5181_;
}
v_resetjp_5181_:
{
lean_object* v___x_5184_; lean_object* v___x_5186_; 
v___x_5184_ = l_Lean_Expr_app___override(v_a_5165_, v_a_5180_);
if (v_isShared_5183_ == 0)
{
lean_ctor_set(v___x_5182_, 0, v___x_5184_);
v___x_5186_ = v___x_5182_;
goto v_reusejp_5185_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v___x_5184_);
v___x_5186_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5185_;
}
v_reusejp_5185_:
{
return v___x_5186_;
}
}
}
else
{
lean_dec(v_a_5165_);
return v___x_5179_;
}
}
}
}
else
{
lean_dec(v_a_5165_);
lean_dec_ref(v_h_5034_);
return v___x_5168_;
}
}
else
{
lean_dec(v_a_5165_);
lean_dec_ref(v_h_5034_);
return v___x_5166_;
}
}
else
{
lean_dec_ref(v_h_5034_);
return v___x_5164_;
}
}
}
}
}
}
else
{
lean_object* v_a_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5202_; 
lean_dec(v___y_5115_);
lean_dec(v___y_5114_);
lean_dec(v_numParams_5111_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_snd_5097_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v_a_5195_ = lean_ctor_get(v___x_5120_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5120_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5197_ = v___x_5120_;
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_a_5195_);
lean_dec(v___x_5120_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5202_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v___x_5200_; 
if (v_isShared_5198_ == 0)
{
v___x_5200_ = v___x_5197_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_a_5195_);
v___x_5200_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
return v___x_5200_;
}
}
}
}
v___jp_5203_:
{
lean_object* v___x_5205_; uint8_t v___x_5206_; 
v___x_5205_ = lean_unsigned_to_nat(0u);
v___x_5206_ = lean_nat_dec_eq(v_numFields_5112_, v___x_5205_);
lean_dec(v_numFields_5112_);
if (v___x_5206_ == 0)
{
lean_object* v_name_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v_a_5211_; uint8_t v___x_5212_; 
v_name_5207_ = lean_ctor_get(v_toConstantVal_5109_, 0);
lean_inc(v_name_5207_);
lean_dec_ref(v_toConstantVal_5109_);
v___x_5208_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5209_ = l_Lean_Name_str___override(v_name_5207_, v___x_5208_);
lean_inc(v___x_5209_);
v___x_5210_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5209_, v___x_5046_, v_a_5038_);
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
lean_inc(v_a_5211_);
lean_dec_ref(v___x_5210_);
v___x_5212_ = lean_unbox(v_a_5211_);
lean_dec(v_a_5211_);
if (v___x_5212_ == 0)
{
lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5216_; 
lean_dec(v_numParams_5111_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_dec(v_snd_5097_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v___x_5213_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5214_ = l_Lean_MessageData_ofName(v___x_5209_);
if (v_isShared_5100_ == 0)
{
lean_ctor_set_tag(v___x_5099_, 7);
lean_ctor_set(v___x_5099_, 1, v___x_5214_);
lean_ctor_set(v___x_5099_, 0, v___x_5213_);
v___x_5216_ = v___x_5099_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v___x_5214_);
v___x_5216_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
lean_object* v___x_5217_; lean_object* v_a_5218_; lean_object* v___x_5220_; uint8_t v_isShared_5221_; uint8_t v_isSharedCheck_5225_; 
v___x_5217_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5216_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
v_a_5218_ = lean_ctor_get(v___x_5217_, 0);
v_isSharedCheck_5225_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5225_ == 0)
{
v___x_5220_ = v___x_5217_;
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
else
{
lean_inc(v_a_5218_);
lean_dec(v___x_5217_);
v___x_5220_ = lean_box(0);
v_isShared_5221_ = v_isSharedCheck_5225_;
goto v_resetjp_5219_;
}
v_resetjp_5219_:
{
lean_object* v___x_5223_; 
if (v_isShared_5221_ == 0)
{
v___x_5223_ = v___x_5220_;
goto v_reusejp_5222_;
}
else
{
lean_object* v_reuseFailAlloc_5224_; 
v_reuseFailAlloc_5224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
v___x_5223_ = v_reuseFailAlloc_5224_;
goto v_reusejp_5222_;
}
v_reusejp_5222_:
{
return v___x_5223_;
}
}
}
}
else
{
lean_del_object(v___x_5099_);
v___y_5114_ = v___x_5205_;
v___y_5115_ = v___x_5209_;
v___y_5116_ = v_a_5035_;
v___y_5117_ = v_a_5036_;
v___y_5118_ = v_a_5037_;
v___y_5119_ = v_a_5038_;
goto v___jp_5113_;
}
}
else
{
lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v___f_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; 
lean_dec(v_numParams_5111_);
lean_dec_ref(v_toConstantVal_5109_);
lean_del_object(v___x_5107_);
lean_dec(v_snd_5105_);
lean_del_object(v___x_5099_);
lean_dec(v_snd_5097_);
lean_dec(v_a_5077_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
v___x_5227_ = lean_box(v___y_5204_);
v___x_5228_ = lean_box(v___x_5206_);
v___f_5229_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5229_, 0, v___x_5227_);
lean_closure_set(v___f_5229_, 1, v___x_5228_);
v___x_5230_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5231_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5230_, v_target_5033_, v___f_5229_, v_a_5035_, v_a_5036_, v_a_5037_, v_a_5038_);
return v___x_5231_;
}
}
}
}
else
{
lean_dec(v_a_5102_);
lean_del_object(v___x_5099_);
lean_dec(v_snd_5097_);
lean_dec(v_fst_5096_);
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v___y_5083_ = v_a_5035_;
v___y_5084_ = v_a_5036_;
v___y_5085_ = v_a_5037_;
v___y_5086_ = v_a_5038_;
goto v___jp_5082_;
}
}
else
{
lean_object* v_a_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5310_; 
lean_del_object(v___x_5099_);
lean_dec(v_snd_5097_);
lean_dec(v_fst_5096_);
lean_dec_ref(v___x_5081_);
lean_dec_ref(v___x_5078_);
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v_a_5303_ = lean_ctor_get(v___x_5101_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5101_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5305_ = v___x_5101_;
v_isShared_5306_ = v_isSharedCheck_5310_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_a_5303_);
lean_dec(v___x_5101_);
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
lean_dec(v_a_5080_);
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v___y_5083_ = v_a_5035_;
v___y_5084_ = v_a_5036_;
v___y_5085_ = v_a_5037_;
v___y_5086_ = v_a_5038_;
goto v___jp_5082_;
}
v___jp_5082_:
{
lean_object* v___x_5087_; lean_object* v___x_5088_; lean_object* v___x_5089_; lean_object* v___x_5090_; lean_object* v___x_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5087_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__9, &l_Lean_Meta_mkNoConfusion___closed__9_once, _init_l_Lean_Meta_mkNoConfusion___closed__9);
v___x_5088_ = l_Lean_MessageData_ofExpr(v___x_5078_);
v___x_5089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5089_, 0, v___x_5087_);
lean_ctor_set(v___x_5089_, 1, v___x_5088_);
v___x_5090_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5089_);
lean_ctor_set(v___x_5091_, 1, v___x_5090_);
v___x_5092_ = l_Lean_MessageData_ofExpr(v___x_5081_);
v___x_5093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5093_, 0, v___x_5091_);
lean_ctor_set(v___x_5093_, 1, v___x_5092_);
v___x_5094_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5093_, v___y_5083_, v___y_5084_, v___y_5085_, v___y_5086_);
return v___x_5094_;
}
}
else
{
lean_object* v_a_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5319_; 
lean_dec_ref(v___x_5078_);
lean_dec(v_a_5077_);
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v_a_5312_ = lean_ctor_get(v___x_5079_, 0);
v_isSharedCheck_5319_ = !lean_is_exclusive(v___x_5079_);
if (v_isSharedCheck_5319_ == 0)
{
v___x_5314_ = v___x_5079_;
v_isShared_5315_ = v_isSharedCheck_5319_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_a_5312_);
lean_dec(v___x_5079_);
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
lean_dec_ref(v_val_5075_);
lean_dec(v_us_5069_);
lean_dec(v_a_5056_);
lean_dec_ref(v___x_5052_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v_a_5320_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5327_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5327_ == 0)
{
v___x_5322_ = v___x_5076_;
v_isShared_5323_ = v_isSharedCheck_5327_;
goto v_resetjp_5321_;
}
else
{
lean_inc(v_a_5320_);
lean_dec(v___x_5076_);
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
lean_dec(v_val_5074_);
lean_dec(v_us_5069_);
lean_dec_ref(v___x_5052_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v___y_5058_ = v_a_5035_;
v___y_5059_ = v_a_5036_;
v___y_5060_ = v_a_5037_;
v___y_5061_ = v_a_5038_;
goto v___jp_5057_;
}
}
}
else
{
lean_dec_ref(v___x_5067_);
lean_dec_ref(v___x_5052_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
v___y_5058_ = v_a_5035_;
v___y_5059_ = v_a_5036_;
v___y_5060_ = v_a_5037_;
v___y_5061_ = v_a_5038_;
goto v___jp_5057_;
}
v___jp_5057_:
{
lean_object* v___x_5062_; lean_object* v___x_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v___x_5062_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5063_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__7, &l_Lean_Meta_mkNoConfusion___closed__7_once, _init_l_Lean_Meta_mkNoConfusion___closed__7);
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
lean_dec_ref(v___x_5052_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
return v___x_5055_;
}
}
}
else
{
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
return v___x_5042_;
}
}
else
{
lean_dec_ref(v_h_5034_);
lean_dec_ref(v_target_5033_);
return v___x_5040_;
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
v___y_5475_ = v___y_5500_;
v___y_5476_ = v___y_5501_;
v___y_5477_ = v___y_5499_;
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
v___y_5475_ = v___y_5500_;
v___y_5476_ = v___y_5501_;
v___y_5477_ = v___y_5499_;
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
v___x_5490_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5478_, v___x_5489_, v___y_5474_, v___y_5477_, v___y_5475_, v___y_5476_);
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
