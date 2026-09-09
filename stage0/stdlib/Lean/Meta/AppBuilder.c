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
lean_object* v___x_431_; lean_object* v_env_432_; lean_object* v___x_433_; lean_object* v_toCold_434_; lean_object* v_mctx_435_; lean_object* v_lctx_436_; lean_object* v_options_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_431_ = lean_st_ref_get(v___y_429_);
v_env_432_ = lean_ctor_get(v___x_431_, 0);
lean_inc_ref(v_env_432_);
lean_dec(v___x_431_);
v___x_433_ = lean_st_ref_get(v___y_427_);
v_toCold_434_ = lean_ctor_get(v___y_428_, 0);
v_mctx_435_ = lean_ctor_get(v___x_433_, 0);
lean_inc_ref(v_mctx_435_);
lean_dec(v___x_433_);
v_lctx_436_ = lean_ctor_get(v___y_426_, 2);
v_options_437_ = lean_ctor_get(v_toCold_434_, 2);
lean_inc_ref(v_options_437_);
lean_inc_ref(v_lctx_436_);
v___x_438_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_438_, 0, v_env_432_);
lean_ctor_set(v___x_438_, 1, v_mctx_435_);
lean_ctor_set(v___x_438_, 2, v_lctx_436_);
lean_ctor_set(v___x_438_, 3, v_options_437_);
v___x_439_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v_msgData_425_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0___boxed(lean_object* v_msgData_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msgData_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(lean_object* v_msg_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_ref_454_; lean_object* v___x_455_; lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_464_; 
v_ref_454_ = lean_ctor_get(v___y_451_, 2);
v___x_455_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_464_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_464_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; lean_object* v___x_462_; 
lean_inc(v_ref_454_);
v___x_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_460_, 0, v_ref_454_);
lean_ctor_set(v___x_460_, 1, v_a_456_);
if (v_isShared_459_ == 0)
{
lean_ctor_set_tag(v___x_458_, 1);
lean_ctor_set(v___x_458_, 0, v___x_460_);
v___x_462_ = v___x_458_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg___boxed(lean_object* v_msg_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
return v_res_471_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1(void){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__0));
v___x_474_ = l_Lean_stringToMessageData(v___x_473_);
return v___x_474_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3(void){
_start:
{
lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_476_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__2));
v___x_477_ = l_Lean_stringToMessageData(v___x_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(lean_object* v_op_478_, lean_object* v_msg_479_, lean_object* v_a_480_, lean_object* v_a_481_, lean_object* v_a_482_, lean_object* v_a_483_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_485_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__1);
v___x_486_ = l_Lean_MessageData_ofName(v_op_478_);
v___x_487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_487_, 0, v___x_485_);
lean_ctor_set(v___x_487_, 1, v___x_486_);
v___x_488_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___closed__3);
v___x_489_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_489_, 0, v___x_487_);
lean_ctor_set(v___x_489_, 1, v___x_488_);
v___x_490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_490_, 0, v___x_489_);
lean_ctor_set(v___x_490_, 1, v_msg_479_);
v___x_491_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_490_, v_a_480_, v_a_481_, v_a_482_, v_a_483_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg___boxed(lean_object* v_op_492_, lean_object* v_msg_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_a_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_op_492_, v_msg_493_, v_a_494_, v_a_495_, v_a_496_, v_a_497_);
lean_dec(v_a_497_);
lean_dec_ref(v_a_496_);
lean_dec(v_a_495_);
lean_dec_ref(v_a_494_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(lean_object* v_00_u03b1_500_, lean_object* v_op_501_, lean_object* v_msg_502_, lean_object* v_a_503_, lean_object* v_a_504_, lean_object* v_a_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; 
v___x_508_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_op_501_, v_msg_502_, v_a_503_, v_a_504_, v_a_505_, v_a_506_);
return v___x_508_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___boxed(lean_object* v_00_u03b1_509_, lean_object* v_op_510_, lean_object* v_msg_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_, lean_object* v_a_515_, lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException(v_00_u03b1_509_, v_op_510_, v_msg_511_, v_a_512_, v_a_513_, v_a_514_, v_a_515_);
lean_dec(v_a_515_);
lean_dec_ref(v_a_514_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0(lean_object* v_00_u03b1_518_, lean_object* v_msg_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_){
_start:
{
lean_object* v___x_525_; 
v___x_525_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___boxed(lean_object* v_00_u03b1_526_, lean_object* v_msg_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0(v_00_u03b1_526_, v_msg_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
return v_res_533_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqSymm___closed__4(void){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__3));
v___x_542_ = l_Lean_MessageData_ofFormat(v___x_541_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm(lean_object* v_h_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_, lean_object* v_a_547_){
_start:
{
lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_549_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_550_ = l_Lean_Expr_isAppOf(v_h_543_, v___x_549_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; 
lean_inc_ref(v_h_543_);
v___x_551_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_543_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_553_; lean_object* v___x_554_; uint8_t v___x_555_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_a_552_);
lean_dec_ref_known(v___x_551_, 1);
v___x_553_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_554_ = lean_unsigned_to_nat(3u);
v___x_555_ = l_Lean_Expr_isAppOfArity(v_a_552_, v___x_553_, v___x_554_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
v___x_556_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__1));
v___x_557_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_558_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_543_, v_a_552_);
v___x_559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_559_, 0, v___x_557_);
lean_ctor_set(v___x_559_, 1, v___x_558_);
v___x_560_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_556_, v___x_559_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
return v___x_560_;
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
v___x_561_ = l_Lean_Expr_appFn_x21(v_a_552_);
v___x_562_ = l_Lean_Expr_appFn_x21(v___x_561_);
v___x_563_ = l_Lean_Expr_appArg_x21(v___x_562_);
lean_dec_ref(v___x_562_);
lean_inc_ref(v___x_563_);
v___x_564_ = l_Lean_Meta_getLevel(v___x_563_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
if (lean_obj_tag(v___x_564_) == 0)
{
lean_object* v_a_565_; lean_object* v___x_567_; uint8_t v_isShared_568_; uint8_t v_isSharedCheck_579_; 
v_a_565_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_579_ == 0)
{
v___x_567_ = v___x_564_;
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
else
{
lean_inc(v_a_565_);
lean_dec(v___x_564_);
v___x_567_ = lean_box(0);
v_isShared_568_ = v_isSharedCheck_579_;
goto v_resetjp_566_;
}
v_resetjp_566_:
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_569_ = l_Lean_Expr_appArg_x21(v___x_561_);
lean_dec_ref(v___x_561_);
v___x_570_ = l_Lean_Expr_appArg_x21(v_a_552_);
lean_dec(v_a_552_);
v___x_571_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__1));
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v_a_565_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Lean_mkConst(v___x_571_, v___x_573_);
v___x_575_ = l_Lean_mkApp4(v___x_574_, v___x_563_, v___x_569_, v___x_570_, v_h_543_);
if (v_isShared_568_ == 0)
{
lean_ctor_set(v___x_567_, 0, v___x_575_);
v___x_577_ = v___x_567_;
goto v_reusejp_576_;
}
else
{
lean_object* v_reuseFailAlloc_578_; 
v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_578_, 0, v___x_575_);
v___x_577_ = v_reuseFailAlloc_578_;
goto v_reusejp_576_;
}
v_reusejp_576_:
{
return v___x_577_;
}
}
}
else
{
lean_object* v_a_580_; lean_object* v___x_582_; uint8_t v_isShared_583_; uint8_t v_isSharedCheck_587_; 
lean_dec_ref(v___x_563_);
lean_dec_ref(v___x_561_);
lean_dec(v_a_552_);
lean_dec_ref(v_h_543_);
v_a_580_ = lean_ctor_get(v___x_564_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_564_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_564_);
v___x_582_ = lean_box(0);
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
v_resetjp_581_:
{
lean_object* v___x_585_; 
if (v_isShared_583_ == 0)
{
v___x_585_ = v___x_582_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v_a_580_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_543_);
return v___x_551_;
}
}
else
{
lean_object* v___x_588_; 
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v_h_543_);
return v___x_588_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqSymm___boxed(lean_object* v_h_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l_Lean_Meta_mkEqSymm(v_h_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object* v_h_u2081_600_, lean_object* v_h_u2082_601_, lean_object* v_a_602_, lean_object* v_a_603_, lean_object* v_a_604_, lean_object* v_a_605_){
_start:
{
lean_object* v___x_607_; uint8_t v___x_608_; 
v___x_607_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_608_ = l_Lean_Expr_isAppOf(v_h_u2081_600_, v___x_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
v___x_609_ = l_Lean_Expr_isAppOf(v_h_u2082_601_, v___x_607_);
if (v___x_609_ == 0)
{
lean_object* v___x_610_; 
lean_inc_ref(v_h_u2081_600_);
v___x_610_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_600_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; lean_object* v___x_612_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
lean_inc_ref(v_h_u2082_601_);
v___x_612_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_601_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_a_613_; lean_object* v___x_614_; lean_object* v___x_615_; uint8_t v___x_616_; 
v_a_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_a_613_);
lean_dec_ref_known(v___x_612_, 1);
v___x_614_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_615_ = lean_unsigned_to_nat(3u);
v___x_616_ = l_Lean_Expr_isAppOfArity(v_a_611_, v___x_614_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; 
lean_dec(v_a_613_);
lean_dec_ref(v_h_u2082_601_);
v___x_617_ = ((lean_object*)(l_Lean_Meta_mkEqTrans___closed__1));
v___x_618_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_619_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_600_, v_a_611_);
v___x_620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
v___x_621_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_617_, v___x_620_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
return v___x_621_;
}
else
{
uint8_t v___x_622_; 
v___x_622_ = l_Lean_Expr_isAppOfArity(v_a_613_, v___x_614_, v___x_615_);
if (v___x_622_ == 0)
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_dec(v_a_611_);
lean_dec_ref(v_h_u2081_600_);
v___x_623_ = ((lean_object*)(l_Lean_Meta_mkEqTrans___closed__1));
v___x_624_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_625_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_601_, v_a_613_);
v___x_626_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_624_);
lean_ctor_set(v___x_626_, 1, v___x_625_);
v___x_627_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_623_, v___x_626_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
return v___x_627_;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; 
v___x_628_ = l_Lean_Expr_appFn_x21(v_a_611_);
v___x_629_ = l_Lean_Expr_appFn_x21(v___x_628_);
v___x_630_ = l_Lean_Expr_appArg_x21(v___x_629_);
lean_dec_ref(v___x_629_);
lean_inc_ref(v___x_630_);
v___x_631_ = l_Lean_Meta_getLevel(v___x_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_631_) == 0)
{
lean_object* v_a_632_; lean_object* v___x_634_; uint8_t v_isShared_635_; uint8_t v_isSharedCheck_647_; 
v_a_632_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_647_ == 0)
{
v___x_634_ = v___x_631_;
v_isShared_635_ = v_isSharedCheck_647_;
goto v_resetjp_633_;
}
else
{
lean_inc(v_a_632_);
lean_dec(v___x_631_);
v___x_634_ = lean_box(0);
v_isShared_635_ = v_isSharedCheck_647_;
goto v_resetjp_633_;
}
v_resetjp_633_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_636_ = l_Lean_Expr_appArg_x21(v___x_628_);
lean_dec_ref(v___x_628_);
v___x_637_ = l_Lean_Expr_appArg_x21(v_a_611_);
lean_dec(v_a_611_);
v___x_638_ = l_Lean_Expr_appArg_x21(v_a_613_);
lean_dec(v_a_613_);
v___x_639_ = ((lean_object*)(l_Lean_Meta_mkEqTrans___closed__1));
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v_a_632_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_mkConst(v___x_639_, v___x_641_);
v___x_643_ = l_Lean_mkApp6(v___x_642_, v___x_630_, v___x_636_, v___x_637_, v___x_638_, v_h_u2081_600_, v_h_u2082_601_);
if (v_isShared_635_ == 0)
{
lean_ctor_set(v___x_634_, 0, v___x_643_);
v___x_645_ = v___x_634_;
goto v_reusejp_644_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_643_);
v___x_645_ = v_reuseFailAlloc_646_;
goto v_reusejp_644_;
}
v_reusejp_644_:
{
return v___x_645_;
}
}
}
else
{
lean_object* v_a_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_655_; 
lean_dec_ref(v___x_630_);
lean_dec_ref(v___x_628_);
lean_dec(v_a_613_);
lean_dec(v_a_611_);
lean_dec_ref(v_h_u2082_601_);
lean_dec_ref(v_h_u2081_600_);
v_a_648_ = lean_ctor_get(v___x_631_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_631_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_631_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_631_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v___x_653_; 
if (v_isShared_651_ == 0)
{
v___x_653_ = v___x_650_;
goto v_reusejp_652_;
}
else
{
lean_object* v_reuseFailAlloc_654_; 
v_reuseFailAlloc_654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_654_, 0, v_a_648_);
v___x_653_ = v_reuseFailAlloc_654_;
goto v_reusejp_652_;
}
v_reusejp_652_:
{
return v___x_653_;
}
}
}
}
}
}
else
{
lean_dec(v_a_611_);
lean_dec_ref(v_h_u2082_601_);
lean_dec_ref(v_h_u2081_600_);
return v___x_612_;
}
}
else
{
lean_dec_ref(v_h_u2082_601_);
lean_dec_ref(v_h_u2081_600_);
return v___x_610_;
}
}
else
{
lean_object* v___x_656_; 
lean_dec_ref(v_h_u2082_601_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_h_u2081_600_);
return v___x_656_;
}
}
else
{
lean_object* v___x_657_; 
lean_dec_ref(v_h_u2081_600_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_h_u2082_601_);
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans___boxed(lean_object* v_h_u2081_658_, lean_object* v_h_u2082_659_, lean_object* v_a_660_, lean_object* v_a_661_, lean_object* v_a_662_, lean_object* v_a_663_, lean_object* v_a_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_Lean_Meta_mkEqTrans(v_h_u2081_658_, v_h_u2082_659_, v_a_660_, v_a_661_, v_a_662_, v_a_663_);
lean_dec(v_a_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_a_661_);
lean_dec_ref(v_a_660_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object* v_h_u2081_x3f_666_, lean_object* v_h_u2082_x3f_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v_h_674_; 
if (lean_obj_tag(v_h_u2081_x3f_666_) == 0)
{
if (lean_obj_tag(v_h_u2082_x3f_667_) == 0)
{
lean_object* v___x_677_; 
v___x_677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_677_, 0, v_h_u2082_x3f_667_);
return v___x_677_;
}
else
{
lean_object* v_val_678_; 
v_val_678_ = lean_ctor_get(v_h_u2082_x3f_667_, 0);
lean_inc(v_val_678_);
lean_dec_ref_known(v_h_u2082_x3f_667_, 1);
v_h_674_ = v_val_678_;
goto v___jp_673_;
}
}
else
{
if (lean_obj_tag(v_h_u2082_x3f_667_) == 0)
{
lean_object* v_val_679_; 
v_val_679_ = lean_ctor_get(v_h_u2081_x3f_666_, 0);
lean_inc(v_val_679_);
lean_dec_ref_known(v_h_u2081_x3f_666_, 1);
v_h_674_ = v_val_679_;
goto v___jp_673_;
}
else
{
lean_object* v_val_680_; lean_object* v_val_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_705_; 
v_val_680_ = lean_ctor_get(v_h_u2081_x3f_666_, 0);
lean_inc(v_val_680_);
lean_dec_ref_known(v_h_u2081_x3f_666_, 1);
v_val_681_ = lean_ctor_get(v_h_u2082_x3f_667_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_h_u2082_x3f_667_);
if (v_isSharedCheck_705_ == 0)
{
v___x_683_ = v_h_u2082_x3f_667_;
v_isShared_684_ = v_isSharedCheck_705_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_val_681_);
lean_dec(v_h_u2082_x3f_667_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_705_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_685_; 
v___x_685_ = l_Lean_Meta_mkEqTrans(v_val_680_, v_val_681_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_696_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_696_ == 0)
{
v___x_688_ = v___x_685_;
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_a_686_);
lean_dec(v___x_685_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_696_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_691_; 
if (v_isShared_684_ == 0)
{
lean_ctor_set(v___x_683_, 0, v_a_686_);
v___x_691_ = v___x_683_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v_a_686_);
v___x_691_ = v_reuseFailAlloc_695_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
lean_object* v___x_693_; 
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_691_);
v___x_693_ = v___x_688_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
return v___x_693_;
}
}
}
}
else
{
lean_object* v_a_697_; lean_object* v___x_699_; uint8_t v_isShared_700_; uint8_t v_isSharedCheck_704_; 
lean_del_object(v___x_683_);
v_a_697_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_704_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_704_ == 0)
{
v___x_699_ = v___x_685_;
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
else
{
lean_inc(v_a_697_);
lean_dec(v___x_685_);
v___x_699_ = lean_box(0);
v_isShared_700_ = v_isSharedCheck_704_;
goto v_resetjp_698_;
}
v_resetjp_698_:
{
lean_object* v___x_702_; 
if (v_isShared_700_ == 0)
{
v___x_702_ = v___x_699_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v_a_697_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_675_, 0, v_h_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f___boxed(lean_object* v_h_u2081_x3f_706_, lean_object* v_h_u2082_x3f_707_, lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v_res_713_; 
v_res_713_ = l_Lean_Meta_mkEqTrans_x3f(v_h_u2081_x3f_706_, v_h_u2082_x3f_707_, v_a_708_, v_a_709_, v_a_710_, v_a_711_);
lean_dec(v_a_711_);
lean_dec_ref(v_a_710_);
lean_dec(v_a_709_);
lean_dec_ref(v_a_708_);
return v_res_713_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__3(void){
_start:
{
lean_object* v___x_720_; lean_object* v___x_721_; 
v___x_720_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__2));
v___x_721_ = l_Lean_MessageData_ofFormat(v___x_720_);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object* v_h_722_, lean_object* v_a_723_, lean_object* v_a_724_, lean_object* v_a_725_, lean_object* v_a_726_){
_start:
{
lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_728_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_729_ = l_Lean_Expr_isAppOf(v_h_722_, v___x_728_);
if (v___x_729_ == 0)
{
lean_object* v___x_730_; 
lean_inc_ref(v_h_722_);
v___x_730_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_722_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_object* v_a_731_; lean_object* v___x_732_; lean_object* v___x_733_; uint8_t v___x_734_; 
v_a_731_ = lean_ctor_get(v___x_730_, 0);
lean_inc(v_a_731_);
lean_dec_ref_known(v___x_730_, 1);
v___x_732_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_733_ = lean_unsigned_to_nat(4u);
v___x_734_ = l_Lean_Expr_isAppOfArity(v_a_731_, v___x_732_, v___x_733_);
if (v___x_734_ == 0)
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_735_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_736_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_737_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_722_, v_a_731_);
v___x_738_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_738_, 0, v___x_736_);
lean_ctor_set(v___x_738_, 1, v___x_737_);
v___x_739_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_735_, v___x_738_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
return v___x_739_;
}
else
{
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_740_ = l_Lean_Expr_appFn_x21(v_a_731_);
v___x_741_ = l_Lean_Expr_appFn_x21(v___x_740_);
v___x_742_ = l_Lean_Expr_appFn_x21(v___x_741_);
v___x_743_ = l_Lean_Expr_appArg_x21(v___x_742_);
lean_dec_ref(v___x_742_);
lean_inc_ref(v___x_743_);
v___x_744_ = l_Lean_Meta_getLevel(v___x_743_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_760_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_760_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_760_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_760_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_749_ = l_Lean_Expr_appArg_x21(v___x_741_);
lean_dec_ref(v___x_741_);
v___x_750_ = l_Lean_Expr_appArg_x21(v___x_740_);
lean_dec_ref(v___x_740_);
v___x_751_ = l_Lean_Expr_appArg_x21(v_a_731_);
lean_dec(v_a_731_);
v___x_752_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v_a_745_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_mkConst(v___x_752_, v___x_754_);
v___x_756_ = l_Lean_mkApp5(v___x_755_, v___x_743_, v___x_750_, v___x_749_, v___x_751_, v_h_722_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_756_);
v___x_758_ = v___x_747_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
else
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___x_743_);
lean_dec_ref(v___x_741_);
lean_dec_ref(v___x_740_);
lean_dec(v_a_731_);
lean_dec_ref(v_h_722_);
v_a_761_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_744_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_744_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_722_);
return v___x_730_;
}
}
else
{
lean_object* v___x_769_; 
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v_h_722_);
return v___x_769_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm___boxed(lean_object* v_h_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_){
_start:
{
lean_object* v_res_776_; 
v_res_776_ = l_Lean_Meta_mkHEqSymm(v_h_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_);
lean_dec(v_a_774_);
lean_dec_ref(v_a_773_);
lean_dec(v_a_772_);
lean_dec_ref(v_a_771_);
return v_res_776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object* v_h_u2081_780_, lean_object* v_h_u2082_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_){
_start:
{
lean_object* v___x_787_; uint8_t v___x_788_; 
v___x_787_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_788_ = l_Lean_Expr_isAppOf(v_h_u2081_780_, v___x_787_);
if (v___x_788_ == 0)
{
uint8_t v___x_789_; 
v___x_789_ = l_Lean_Expr_isAppOf(v_h_u2082_781_, v___x_787_);
if (v___x_789_ == 0)
{
lean_object* v___x_790_; 
lean_inc_ref(v_h_u2081_780_);
v___x_790_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_780_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_790_) == 0)
{
lean_object* v_a_791_; lean_object* v___x_792_; 
v_a_791_ = lean_ctor_get(v___x_790_, 0);
lean_inc(v_a_791_);
lean_dec_ref_known(v___x_790_, 1);
lean_inc_ref(v_h_u2082_781_);
v___x_792_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_795_; uint8_t v___x_796_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc(v_a_793_);
lean_dec_ref_known(v___x_792_, 1);
v___x_794_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_795_ = lean_unsigned_to_nat(4u);
v___x_796_ = l_Lean_Expr_isAppOfArity(v_a_791_, v___x_794_, v___x_795_);
if (v___x_796_ == 0)
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; 
lean_dec(v_a_793_);
lean_dec_ref(v_h_u2082_781_);
v___x_797_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_798_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_799_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_780_, v_a_791_);
v___x_800_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_798_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_797_, v___x_800_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_801_;
}
else
{
uint8_t v___x_802_; 
v___x_802_ = l_Lean_Expr_isAppOfArity(v_a_793_, v___x_794_, v___x_795_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
lean_dec(v_a_791_);
lean_dec_ref(v_h_u2081_780_);
v___x_803_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_804_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_805_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_781_, v_a_793_);
v___x_806_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_804_);
lean_ctor_set(v___x_806_, 1, v___x_805_);
v___x_807_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_803_, v___x_806_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
return v___x_807_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_808_ = l_Lean_Expr_appFn_x21(v_a_791_);
v___x_809_ = l_Lean_Expr_appFn_x21(v___x_808_);
v___x_810_ = l_Lean_Expr_appFn_x21(v___x_809_);
v___x_811_ = l_Lean_Expr_appArg_x21(v___x_810_);
lean_dec_ref(v___x_810_);
lean_inc_ref(v___x_811_);
v___x_812_ = l_Lean_Meta_getLevel(v___x_811_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_815_; uint8_t v_isShared_816_; uint8_t v_isSharedCheck_831_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_831_ == 0)
{
v___x_815_ = v___x_812_;
v_isShared_816_ = v_isSharedCheck_831_;
goto v_resetjp_814_;
}
else
{
lean_inc(v_a_813_);
lean_dec(v___x_812_);
v___x_815_ = lean_box(0);
v_isShared_816_ = v_isSharedCheck_831_;
goto v_resetjp_814_;
}
v_resetjp_814_:
{
lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_817_ = l_Lean_Expr_appArg_x21(v___x_809_);
lean_dec_ref(v___x_809_);
v___x_818_ = l_Lean_Expr_appArg_x21(v___x_808_);
lean_dec_ref(v___x_808_);
v___x_819_ = l_Lean_Expr_appArg_x21(v_a_791_);
lean_dec(v_a_791_);
v___x_820_ = l_Lean_Expr_appFn_x21(v_a_793_);
v___x_821_ = l_Lean_Expr_appArg_x21(v___x_820_);
lean_dec_ref(v___x_820_);
v___x_822_ = l_Lean_Expr_appArg_x21(v_a_793_);
lean_dec(v_a_793_);
v___x_823_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_824_ = lean_box(0);
v___x_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_825_, 0, v_a_813_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_mkConst(v___x_823_, v___x_825_);
v___x_827_ = l_Lean_mkApp8(v___x_826_, v___x_811_, v___x_818_, v___x_821_, v___x_817_, v___x_819_, v___x_822_, v_h_u2081_780_, v_h_u2082_781_);
if (v_isShared_816_ == 0)
{
lean_ctor_set(v___x_815_, 0, v___x_827_);
v___x_829_ = v___x_815_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
}
else
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
lean_dec_ref(v___x_811_);
lean_dec_ref(v___x_809_);
lean_dec_ref(v___x_808_);
lean_dec(v_a_793_);
lean_dec(v_a_791_);
lean_dec_ref(v_h_u2082_781_);
lean_dec_ref(v_h_u2081_780_);
v_a_832_ = lean_ctor_get(v___x_812_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_812_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_812_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_812_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
}
}
}
else
{
lean_dec(v_a_791_);
lean_dec_ref(v_h_u2082_781_);
lean_dec_ref(v_h_u2081_780_);
return v___x_792_;
}
}
else
{
lean_dec_ref(v_h_u2082_781_);
lean_dec_ref(v_h_u2081_780_);
return v___x_790_;
}
}
else
{
lean_object* v___x_840_; 
lean_dec_ref(v_h_u2082_781_);
v___x_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_840_, 0, v_h_u2081_780_);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec_ref(v_h_u2081_780_);
v___x_841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_841_, 0, v_h_u2082_781_);
return v___x_841_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans___boxed(lean_object* v_h_u2081_842_, lean_object* v_h_u2082_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v_res_849_; 
v_res_849_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_842_, v_h_u2082_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec_ref(v_a_844_);
return v_res_849_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__2(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_853_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__1));
v___x_854_ = l_Lean_stringToMessageData(v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__4(void){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__3));
v___x_857_ = l_Lean_stringToMessageData(v___x_856_);
return v___x_857_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__6(void){
_start:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__5));
v___x_860_ = l_Lean_stringToMessageData(v___x_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* v_h_861_, uint8_t v_check_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_){
_start:
{
lean_object* v___x_868_; 
lean_inc_ref(v_h_861_);
v___x_868_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_861_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; lean_object* v___x_871_; uint8_t v___x_872_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
v___x_870_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_871_ = lean_unsigned_to_nat(4u);
v___x_872_ = l_Lean_Expr_isAppOfArity(v_a_869_, v___x_870_, v___x_871_);
if (v___x_872_ == 0)
{
lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
lean_dec(v_a_869_);
v___x_873_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_874_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__2, &l_Lean_Meta_mkEqOfHEq___closed__2_once, _init_l_Lean_Meta_mkEqOfHEq___closed__2);
v___x_875_ = l_Lean_indentExpr(v_h_861_);
v___x_876_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_876_, 0, v___x_874_);
lean_ctor_set(v___x_876_, 1, v___x_875_);
v___x_877_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_873_, v___x_876_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
return v___x_877_;
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; 
v___x_878_ = l_Lean_Expr_appFn_x21(v_a_869_);
v___x_879_ = l_Lean_Expr_appFn_x21(v___x_878_);
v___x_880_ = l_Lean_Expr_appFn_x21(v___x_879_);
v___x_881_ = l_Lean_Expr_appArg_x21(v___x_880_);
lean_dec_ref(v___x_880_);
v___x_882_ = l_Lean_Expr_appArg_x21(v___x_879_);
lean_dec_ref(v___x_879_);
v___x_883_ = l_Lean_Expr_appArg_x21(v_a_869_);
lean_dec(v_a_869_);
if (v_check_862_ == 0)
{
lean_dec_ref(v___x_878_);
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
v___y_888_ = v_a_866_;
goto v___jp_884_;
}
else
{
lean_object* v___x_911_; lean_object* v___x_912_; 
v___x_911_ = l_Lean_Expr_appArg_x21(v___x_878_);
lean_dec_ref(v___x_878_);
lean_inc_ref(v___x_911_);
lean_inc_ref(v___x_881_);
v___x_912_ = l_Lean_Meta_isExprDefEq(v___x_881_, v___x_911_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_unbox(v_a_913_);
lean_dec(v_a_913_);
if (v___x_914_ == 0)
{
lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
lean_dec_ref(v___x_883_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v_h_861_);
v___x_915_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_916_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__4, &l_Lean_Meta_mkEqOfHEq___closed__4_once, _init_l_Lean_Meta_mkEqOfHEq___closed__4);
v___x_917_ = l_Lean_indentExpr(v___x_881_);
v___x_918_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_916_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__6, &l_Lean_Meta_mkEqOfHEq___closed__6_once, _init_l_Lean_Meta_mkEqOfHEq___closed__6);
v___x_920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_918_);
lean_ctor_set(v___x_920_, 1, v___x_919_);
v___x_921_ = l_Lean_indentExpr(v___x_911_);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_920_);
lean_ctor_set(v___x_922_, 1, v___x_921_);
v___x_923_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_915_, v___x_922_, v_a_863_, v_a_864_, v_a_865_, v_a_866_);
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
else
{
lean_dec_ref(v___x_911_);
v___y_885_ = v_a_863_;
v___y_886_ = v_a_864_;
v___y_887_ = v_a_865_;
v___y_888_ = v_a_866_;
goto v___jp_884_;
}
}
else
{
lean_object* v_a_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_939_; 
lean_dec_ref(v___x_911_);
lean_dec_ref(v___x_883_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v_h_861_);
v_a_932_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_939_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_939_ == 0)
{
v___x_934_ = v___x_912_;
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_a_932_);
lean_dec(v___x_912_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_939_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_937_; 
if (v_isShared_935_ == 0)
{
v___x_937_ = v___x_934_;
goto v_reusejp_936_;
}
else
{
lean_object* v_reuseFailAlloc_938_; 
v_reuseFailAlloc_938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_938_, 0, v_a_932_);
v___x_937_ = v_reuseFailAlloc_938_;
goto v_reusejp_936_;
}
v_reusejp_936_:
{
return v___x_937_;
}
}
}
}
v___jp_884_:
{
lean_object* v___x_889_; 
lean_inc_ref(v___x_881_);
v___x_889_ = l_Lean_Meta_getLevel(v___x_881_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_902_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_902_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_902_ == 0)
{
v___x_892_ = v___x_889_;
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_889_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_902_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_900_; 
v___x_894_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_895_ = lean_box(0);
v___x_896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_896_, 0, v_a_890_);
lean_ctor_set(v___x_896_, 1, v___x_895_);
v___x_897_ = l_Lean_mkConst(v___x_894_, v___x_896_);
v___x_898_ = l_Lean_mkApp4(v___x_897_, v___x_881_, v___x_882_, v___x_883_, v_h_861_);
if (v_isShared_893_ == 0)
{
lean_ctor_set(v___x_892_, 0, v___x_898_);
v___x_900_ = v___x_892_;
goto v_reusejp_899_;
}
else
{
lean_object* v_reuseFailAlloc_901_; 
v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
v___x_900_ = v_reuseFailAlloc_901_;
goto v_reusejp_899_;
}
v_reusejp_899_:
{
return v___x_900_;
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v___x_883_);
lean_dec_ref(v___x_882_);
lean_dec_ref(v___x_881_);
lean_dec_ref(v_h_861_);
v_a_903_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_889_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_889_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_861_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___boxed(lean_object* v_h_940_, lean_object* v_check_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_){
_start:
{
uint8_t v_check_boxed_947_; lean_object* v_res_948_; 
v_check_boxed_947_ = lean_unbox(v_check_941_);
v_res_948_ = l_Lean_Meta_mkEqOfHEq(v_h_940_, v_check_boxed_947_, v_a_942_, v_a_943_, v_a_944_, v_a_945_);
lean_dec(v_a_945_);
lean_dec_ref(v_a_944_);
lean_dec(v_a_943_);
lean_dec_ref(v_a_942_);
return v_res_948_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqOfEq___closed__2(void){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__2));
v___x_953_ = l_Lean_stringToMessageData(v___x_952_);
return v___x_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq(lean_object* v_h_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v___x_960_; 
lean_inc_ref(v_h_954_);
v___x_960_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_954_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_962_; lean_object* v___x_963_; uint8_t v___x_964_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_a_961_);
lean_dec_ref_known(v___x_960_, 1);
v___x_962_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_963_ = lean_unsigned_to_nat(3u);
v___x_964_ = l_Lean_Expr_isAppOfArity(v_a_961_, v___x_962_, v___x_963_);
if (v___x_964_ == 0)
{
lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v_a_961_);
v___x_965_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_966_ = lean_obj_once(&l_Lean_Meta_mkHEqOfEq___closed__2, &l_Lean_Meta_mkHEqOfEq___closed__2_once, _init_l_Lean_Meta_mkHEqOfEq___closed__2);
v___x_967_ = l_Lean_indentExpr(v_h_954_);
v___x_968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_966_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_965_, v___x_968_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
return v___x_969_;
}
else
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v___x_970_ = l_Lean_Expr_appFn_x21(v_a_961_);
v___x_971_ = l_Lean_Expr_appFn_x21(v___x_970_);
v___x_972_ = l_Lean_Expr_appArg_x21(v___x_971_);
lean_dec_ref(v___x_971_);
lean_inc_ref(v___x_972_);
v___x_973_ = l_Lean_Meta_getLevel(v___x_972_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_988_; 
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_988_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_988_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_978_ = l_Lean_Expr_appArg_x21(v___x_970_);
lean_dec_ref(v___x_970_);
v___x_979_ = l_Lean_Expr_appArg_x21(v_a_961_);
lean_dec(v_a_961_);
v___x_980_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_974_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_mkConst(v___x_980_, v___x_982_);
v___x_984_ = l_Lean_mkApp4(v___x_983_, v___x_972_, v___x_978_, v___x_979_, v_h_954_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 0, v___x_984_);
v___x_986_ = v___x_976_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v___x_984_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
else
{
lean_object* v_a_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_996_; 
lean_dec_ref(v___x_972_);
lean_dec_ref(v___x_970_);
lean_dec(v_a_961_);
lean_dec_ref(v_h_954_);
v_a_989_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_973_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_973_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v_a_989_);
v___x_994_ = v_reuseFailAlloc_995_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
return v___x_994_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_954_);
return v___x_960_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq___boxed(lean_object* v_h_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v_res_1003_; 
v_res_1003_ = l_Lean_Meta_mkHEqOfEq(v_h_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f(lean_object* v_e_1004_){
_start:
{
lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1005_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1006_ = lean_unsigned_to_nat(2u);
v___x_1007_ = l_Lean_Expr_isAppOfArity(v_e_1004_, v___x_1005_, v___x_1006_);
if (v___x_1007_ == 0)
{
lean_object* v___x_1008_; 
v___x_1008_ = lean_box(0);
return v___x_1008_;
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; 
v___x_1009_ = l_Lean_Expr_appArg_x21(v_e_1004_);
v___x_1010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1010_, 0, v___x_1009_);
return v___x_1010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f___boxed(lean_object* v_e_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Lean_Meta_isRefl_x3f(v_e_1011_);
lean_dec_ref(v_e_1011_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(lean_object* v_msg_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v___f_1020_; lean_object* v___x_854__overap_1021_; lean_object* v___x_1022_; 
v___f_1020_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_854__overap_1021_ = lean_panic_fn_borrowed(v___f_1020_, v_msg_1014_);
lean_inc(v___y_1018_);
lean_inc_ref(v___y_1017_);
lean_inc(v___y_1016_);
lean_inc_ref(v___y_1015_);
v___x_1022_ = lean_apply_5(v___x_854__overap_1021_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, lean_box(0));
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___boxed(lean_object* v_msg_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v_msg_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
return v_res_1029_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__2(void){
_start:
{
lean_object* v___x_1033_; lean_object* v_dummy_1034_; 
v___x_1033_ = lean_box(0);
v_dummy_1034_ = l_Lean_Expr_sort___override(v___x_1033_);
return v_dummy_1034_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__6(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1038_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1039_ = lean_unsigned_to_nat(48u);
v___x_1040_ = lean_unsigned_to_nat(204u);
v___x_1041_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1042_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1043_ = l_mkPanicMessageWithDecl(v___x_1042_, v___x_1041_, v___x_1040_, v___x_1039_, v___x_1038_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__9(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = l_Lean_Expr_bvar___override(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__10(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1049_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1050_ = lean_unsigned_to_nat(1u);
v___x_1051_ = lean_mk_empty_array_with_capacity(v___x_1050_);
v___x_1052_ = lean_array_push(v___x_1051_, v___x_1049_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__15(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1059_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1060_ = lean_unsigned_to_nat(49u);
v___x_1061_ = lean_unsigned_to_nat(201u);
v___x_1062_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1063_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1064_ = l_mkPanicMessageWithDecl(v___x_1063_, v___x_1062_, v___x_1061_, v___x_1060_, v___x_1059_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f(lean_object* v_e_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___x_1120_; lean_object* v___x_1121_; uint8_t v___x_1122_; 
v___x_1120_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1121_ = lean_unsigned_to_nat(6u);
v___x_1122_ = l_Lean_Expr_isAppOfArity(v_e_1065_, v___x_1120_, v___x_1121_);
if (v___x_1122_ == 0)
{
v___y_1075_ = v_a_1066_;
v___y_1076_ = v_a_1067_;
v___y_1077_ = v_a_1068_;
v___y_1078_ = v_a_1069_;
goto v___jp_1074_;
}
else
{
lean_object* v_dummy_1123_; lean_object* v_nargs_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; uint8_t v___x_1130_; 
v_dummy_1123_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1124_ = l_Lean_Expr_getAppNumArgs(v_e_1065_);
lean_inc(v_nargs_1124_);
v___x_1125_ = lean_mk_array(v_nargs_1124_, v_dummy_1123_);
v___x_1126_ = lean_unsigned_to_nat(1u);
v___x_1127_ = lean_nat_sub(v_nargs_1124_, v___x_1126_);
lean_dec(v_nargs_1124_);
lean_inc_ref(v_e_1065_);
v___x_1128_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1065_, v___x_1125_, v___x_1127_);
v___x_1129_ = lean_array_get_size(v___x_1128_);
v___x_1130_ = lean_nat_dec_eq(v___x_1129_, v___x_1121_);
if (v___x_1130_ == 0)
{
lean_object* v___x_1131_; lean_object* v___x_1132_; 
lean_dec_ref(v___x_1128_);
v___x_1131_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__15, &l_Lean_Meta_congrArg_x3f___closed__15_once, _init_l_Lean_Meta_congrArg_x3f___closed__15);
v___x_1132_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1131_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_dec_ref_known(v___x_1132_, 1);
v___y_1075_ = v_a_1066_;
v___y_1076_ = v_a_1067_;
v___y_1077_ = v_a_1068_;
v___y_1078_ = v_a_1069_;
goto v___jp_1074_;
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec_ref(v_e_1065_);
v_a_1133_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1132_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1132_);
v___x_1135_ = lean_box(0);
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
v_resetjp_1134_:
{
lean_object* v___x_1138_; 
if (v_isShared_1136_ == 0)
{
v___x_1138_ = v___x_1135_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_a_1133_);
v___x_1138_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
return v___x_1138_;
}
}
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; 
lean_dec_ref(v_e_1065_);
v___x_1141_ = lean_unsigned_to_nat(0u);
v___x_1142_ = lean_array_fget(v___x_1128_, v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(4u);
v___x_1144_ = lean_array_fget(v___x_1128_, v___x_1143_);
v___x_1145_ = lean_unsigned_to_nat(5u);
v___x_1146_ = lean_array_fget(v___x_1128_, v___x_1145_);
lean_dec_ref(v___x_1128_);
v___x_1147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1144_);
lean_ctor_set(v___x_1147_, 1, v___x_1146_);
v___x_1148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1148_, 0, v___x_1142_);
lean_ctor_set(v___x_1148_, 1, v___x_1147_);
v___x_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1148_);
v___x_1150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1150_, 0, v___x_1149_);
return v___x_1150_;
}
}
v___jp_1071_:
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
return v___x_1073_;
}
v___jp_1074_:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; uint8_t v___x_1081_; 
v___x_1079_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1080_ = lean_unsigned_to_nat(6u);
v___x_1081_ = l_Lean_Expr_isAppOfArity(v_e_1065_, v___x_1079_, v___x_1080_);
if (v___x_1081_ == 0)
{
lean_dec_ref(v_e_1065_);
goto v___jp_1071_;
}
else
{
lean_object* v_dummy_1082_; lean_object* v_nargs_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; uint8_t v___x_1089_; 
v_dummy_1082_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1083_ = l_Lean_Expr_getAppNumArgs(v_e_1065_);
lean_inc(v_nargs_1083_);
v___x_1084_ = lean_mk_array(v_nargs_1083_, v_dummy_1082_);
v___x_1085_ = lean_unsigned_to_nat(1u);
v___x_1086_ = lean_nat_sub(v_nargs_1083_, v___x_1085_);
lean_dec(v_nargs_1083_);
v___x_1087_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1065_, v___x_1084_, v___x_1086_);
v___x_1088_ = lean_array_get_size(v___x_1087_);
v___x_1089_ = lean_nat_dec_eq(v___x_1088_, v___x_1080_);
if (v___x_1089_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec_ref(v___x_1087_);
v___x_1090_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__6, &l_Lean_Meta_congrArg_x3f___closed__6_once, _init_l_Lean_Meta_congrArg_x3f___closed__6);
v___x_1091_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1090_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_dec_ref_known(v___x_1091_, 1);
goto v___jp_1071_;
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_a_1092_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1094_ = v___x_1091_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_a_1092_);
lean_dec(v___x_1091_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; lean_object* v_00_u03b1_x27_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v_f_x27_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1100_ = lean_unsigned_to_nat(0u);
v___x_1101_ = lean_array_fget(v___x_1087_, v___x_1100_);
v___x_1102_ = lean_array_fget(v___x_1087_, v___x_1085_);
v___x_1103_ = lean_unsigned_to_nat(4u);
v___x_1104_ = lean_array_fget(v___x_1087_, v___x_1103_);
v___x_1105_ = lean_unsigned_to_nat(5u);
v___x_1106_ = lean_array_fget(v___x_1087_, v___x_1105_);
lean_dec_ref(v___x_1087_);
v___x_1107_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1108_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1109_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1110_ = l_Lean_Expr_beta(v___x_1102_, v___x_1109_);
v___x_1111_ = 0;
v_00_u03b1_x27_1112_ = l_Lean_Expr_forallE___override(v___x_1107_, v___x_1101_, v___x_1110_, v___x_1111_);
v___x_1113_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__12));
v___x_1114_ = l_Lean_Expr_app___override(v___x_1108_, v___x_1106_);
lean_inc_ref(v_00_u03b1_x27_1112_);
v_f_x27_1115_ = l_Lean_Expr_lam___override(v___x_1113_, v_00_u03b1_x27_1112_, v___x_1114_, v___x_1111_);
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_f_x27_1115_);
lean_ctor_set(v___x_1116_, 1, v___x_1104_);
v___x_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1117_, 0, v_00_u03b1_x27_1112_);
lean_ctor_set(v___x_1117_, 1, v___x_1116_);
v___x_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1118_, 0, v___x_1117_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
return v___x_1119_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___boxed(lean_object* v_e_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_){
_start:
{
lean_object* v_res_1157_; 
v_res_1157_ = l_Lean_Meta_congrArg_x3f(v_e_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_);
lean_dec(v_a_1155_);
lean_dec_ref(v_a_1154_);
lean_dec(v_a_1153_);
lean_dec_ref(v_a_1152_);
return v_res_1157_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__2(void){
_start:
{
lean_object* v___x_1161_; lean_object* v___x_1162_; 
v___x_1161_ = ((lean_object*)(l_Lean_Meta_mkCongrArg___closed__1));
v___x_1162_ = l_Lean_MessageData_ofFormat(v___x_1161_);
return v___x_1162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object* v_f_1163_, lean_object* v_h_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_Lean_Meta_isRefl_x3f(v_h_1164_);
if (lean_obj_tag(v___x_1170_) == 1)
{
lean_object* v_val_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; 
lean_dec_ref(v_h_1164_);
v_val_1171_ = lean_ctor_get(v___x_1170_, 0);
lean_inc(v_val_1171_);
lean_dec_ref_known(v___x_1170_, 1);
v___x_1172_ = l_Lean_Expr_app___override(v_f_1163_, v_val_1171_);
v___x_1173_ = l_Lean_Meta_mkEqRefl(v___x_1172_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
return v___x_1173_;
}
else
{
lean_object* v___x_1174_; 
lean_dec(v___x_1170_);
lean_inc_ref(v_h_1164_);
v___x_1174_ = l_Lean_Meta_congrArg_x3f(v_h_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_object* v_a_1175_; 
v_a_1175_ = lean_ctor_get(v___x_1174_, 0);
lean_inc(v_a_1175_);
lean_dec_ref_known(v___x_1174_, 1);
if (lean_obj_tag(v_a_1175_) == 1)
{
lean_object* v_val_1176_; lean_object* v_snd_1177_; lean_object* v_fst_1178_; lean_object* v_fst_1179_; lean_object* v_snd_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; 
lean_dec_ref(v_h_1164_);
v_val_1176_ = lean_ctor_get(v_a_1175_, 0);
lean_inc(v_val_1176_);
lean_dec_ref_known(v_a_1175_, 1);
v_snd_1177_ = lean_ctor_get(v_val_1176_, 1);
lean_inc(v_snd_1177_);
v_fst_1178_ = lean_ctor_get(v_val_1176_, 0);
lean_inc(v_fst_1178_);
lean_dec(v_val_1176_);
v_fst_1179_ = lean_ctor_get(v_snd_1177_, 0);
lean_inc(v_fst_1179_);
v_snd_1180_ = lean_ctor_get(v_snd_1177_, 1);
lean_inc(v_snd_1180_);
lean_dec(v_snd_1177_);
v___x_1181_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1182_ = lean_unsigned_to_nat(1u);
v___x_1183_ = lean_mk_empty_array_with_capacity(v___x_1182_);
v___x_1184_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1185_ = l_Lean_Expr_beta(v_fst_1179_, v___x_1184_);
v___x_1186_ = lean_array_push(v___x_1183_, v___x_1185_);
v___x_1187_ = l_Lean_Expr_beta(v_f_1163_, v___x_1186_);
v___x_1188_ = 0;
v___x_1189_ = l_Lean_Expr_lam___override(v___x_1181_, v_fst_1178_, v___x_1187_, v___x_1188_);
v_f_1163_ = v___x_1189_;
v_h_1164_ = v_snd_1180_;
goto _start;
}
else
{
lean_object* v___x_1191_; 
lean_dec(v_a_1175_);
lean_inc_ref(v_h_1164_);
v___x_1191_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1193_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
lean_inc(v_a_1192_);
lean_dec_ref_known(v___x_1191_, 1);
lean_inc_ref(v_f_1163_);
v___x_1193_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_f_1163_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1193_) == 0)
{
lean_object* v_a_1194_; 
v_a_1194_ = lean_ctor_get(v___x_1193_, 0);
lean_inc(v_a_1194_);
lean_dec_ref_known(v___x_1193_, 1);
if (lean_obj_tag(v_a_1194_) == 7)
{
lean_object* v_binderType_1201_; lean_object* v_body_1202_; uint8_t v___x_1203_; 
v_binderType_1201_ = lean_ctor_get(v_a_1194_, 1);
v_body_1202_ = lean_ctor_get(v_a_1194_, 2);
v___x_1203_ = l_Lean_Expr_hasLooseBVars(v_body_1202_);
if (v___x_1203_ == 0)
{
lean_object* v___x_1204_; lean_object* v___x_1205_; uint8_t v___x_1206_; 
lean_inc_ref(v_body_1202_);
lean_inc_ref(v_binderType_1201_);
lean_dec_ref_known(v_a_1194_, 3);
v___x_1204_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1205_ = lean_unsigned_to_nat(3u);
v___x_1206_ = l_Lean_Expr_isAppOfArity(v_a_1192_, v___x_1204_, v___x_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref(v_body_1202_);
lean_dec_ref(v_binderType_1201_);
lean_dec_ref(v_f_1163_);
v___x_1207_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1208_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1209_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1164_, v_a_1192_);
v___x_1210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1210_, 0, v___x_1208_);
lean_ctor_set(v___x_1210_, 1, v___x_1209_);
v___x_1211_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1207_, v___x_1210_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
return v___x_1211_;
}
else
{
lean_object* v___x_1212_; 
lean_inc_ref(v_binderType_1201_);
v___x_1212_ = l_Lean_Meta_getLevel(v_binderType_1201_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1214_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref_known(v___x_1212_, 1);
lean_inc_ref(v_body_1202_);
v___x_1214_ = l_Lean_Meta_getLevel(v_body_1202_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1231_; 
v_a_1215_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1217_ = v___x_1214_;
v_isShared_1218_ = v_isSharedCheck_1231_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1214_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1231_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1219_ = l_Lean_Expr_appFn_x21(v_a_1192_);
v___x_1220_ = l_Lean_Expr_appArg_x21(v___x_1219_);
lean_dec_ref(v___x_1219_);
v___x_1221_ = l_Lean_Expr_appArg_x21(v_a_1192_);
lean_dec(v_a_1192_);
v___x_1222_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1215_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_a_1213_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = l_Lean_mkConst(v___x_1222_, v___x_1225_);
v___x_1227_ = l_Lean_mkApp6(v___x_1226_, v_binderType_1201_, v_body_1202_, v___x_1220_, v___x_1221_, v_f_1163_, v_h_1164_);
if (v_isShared_1218_ == 0)
{
lean_ctor_set(v___x_1217_, 0, v___x_1227_);
v___x_1229_ = v___x_1217_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1230_; 
v_reuseFailAlloc_1230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1230_, 0, v___x_1227_);
v___x_1229_ = v_reuseFailAlloc_1230_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
return v___x_1229_;
}
}
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec(v_a_1213_);
lean_dec_ref(v_body_1202_);
lean_dec_ref(v_binderType_1201_);
lean_dec(v_a_1192_);
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_f_1163_);
v_a_1232_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1214_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1214_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
else
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1247_; 
lean_dec_ref(v_body_1202_);
lean_dec_ref(v_binderType_1201_);
lean_dec(v_a_1192_);
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_f_1163_);
v_a_1240_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1212_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1212_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1245_; 
if (v_isShared_1243_ == 0)
{
v___x_1245_ = v___x_1242_;
goto v_reusejp_1244_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v_a_1240_);
v___x_1245_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1244_;
}
v_reusejp_1244_:
{
return v___x_1245_;
}
}
}
}
}
else
{
lean_dec(v_a_1192_);
lean_dec_ref(v_h_1164_);
goto v___jp_1195_;
}
}
else
{
lean_dec(v_a_1192_);
lean_dec_ref(v_h_1164_);
goto v___jp_1195_;
}
v___jp_1195_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1196_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1197_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1198_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_f_1163_, v_a_1194_);
v___x_1199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1199_, 0, v___x_1197_);
lean_ctor_set(v___x_1199_, 1, v___x_1198_);
v___x_1200_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1196_, v___x_1199_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
return v___x_1200_;
}
}
else
{
lean_dec(v_a_1192_);
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_f_1163_);
return v___x_1193_;
}
}
else
{
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_f_1163_);
return v___x_1191_;
}
}
}
else
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1255_; 
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_f_1163_);
v_a_1248_ = lean_ctor_get(v___x_1174_, 0);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1174_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1250_ = v___x_1174_;
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1174_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1255_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
lean_object* v___x_1253_; 
if (v_isShared_1251_ == 0)
{
v___x_1253_ = v___x_1250_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1248_);
v___x_1253_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
return v___x_1253_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___boxed(lean_object* v_f_1256_, lean_object* v_h_1257_, lean_object* v_a_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_Lean_Meta_mkCongrArg(v_f_1256_, v_h_1257_, v_a_1258_, v_a_1259_, v_a_1260_, v_a_1261_);
lean_dec(v_a_1261_);
lean_dec_ref(v_a_1260_);
lean_dec(v_a_1259_);
lean_dec_ref(v_a_1258_);
return v_res_1263_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__0(void){
_start:
{
lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1264_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1265_ = lean_unsigned_to_nat(2u);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1265_);
v___x_1267_ = lean_array_push(v___x_1266_, v___x_1264_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__3(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_Meta_mkCongrFun___closed__2));
v___x_1272_ = l_Lean_MessageData_ofFormat(v___x_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object* v_h_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; 
v___x_1280_ = l_Lean_Meta_isRefl_x3f(v_h_1273_);
if (lean_obj_tag(v___x_1280_) == 1)
{
lean_object* v_val_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; 
lean_dec_ref(v_h_1273_);
v_val_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_val_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = l_Lean_Expr_app___override(v_val_1281_, v_a_1274_);
v___x_1283_ = l_Lean_Meta_mkEqRefl(v___x_1282_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1283_;
}
else
{
lean_object* v___x_1284_; 
lean_dec(v___x_1280_);
lean_inc_ref(v_h_1273_);
v___x_1284_ = l_Lean_Meta_congrArg_x3f(v_h_1273_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v_a_1285_; 
v_a_1285_ = lean_ctor_get(v___x_1284_, 0);
lean_inc(v_a_1285_);
lean_dec_ref_known(v___x_1284_, 1);
if (lean_obj_tag(v_a_1285_) == 1)
{
lean_object* v_val_1286_; lean_object* v_snd_1287_; lean_object* v_fst_1288_; lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; uint8_t v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v_h_1273_);
v_val_1286_ = lean_ctor_get(v_a_1285_, 0);
lean_inc(v_val_1286_);
lean_dec_ref_known(v_a_1285_, 1);
v_snd_1287_ = lean_ctor_get(v_val_1286_, 1);
lean_inc(v_snd_1287_);
v_fst_1288_ = lean_ctor_get(v_val_1286_, 0);
lean_inc(v_fst_1288_);
lean_dec(v_val_1286_);
v_fst_1289_ = lean_ctor_get(v_snd_1287_, 0);
lean_inc(v_fst_1289_);
v_snd_1290_ = lean_ctor_get(v_snd_1287_, 1);
lean_inc(v_snd_1290_);
lean_dec(v_snd_1287_);
v___x_1291_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1292_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__0, &l_Lean_Meta_mkCongrFun___closed__0_once, _init_l_Lean_Meta_mkCongrFun___closed__0);
v___x_1293_ = lean_array_push(v___x_1292_, v_a_1274_);
v___x_1294_ = l_Lean_Expr_beta(v_fst_1289_, v___x_1293_);
v___x_1295_ = 0;
v___x_1296_ = l_Lean_Expr_lam___override(v___x_1291_, v_fst_1288_, v___x_1294_, v___x_1295_);
v___x_1297_ = l_Lean_Meta_mkCongrArg(v___x_1296_, v_snd_1290_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1297_;
}
else
{
lean_object* v___x_1298_; 
lean_dec(v_a_1285_);
lean_inc_ref(v_h_1273_);
v___x_1298_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1273_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; uint8_t v___x_1302_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1301_ = lean_unsigned_to_nat(3u);
v___x_1302_ = l_Lean_Expr_isAppOfArity(v_a_1299_, v___x_1300_, v___x_1301_);
if (v___x_1302_ == 0)
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
lean_dec_ref(v_a_1274_);
v___x_1303_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1304_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1305_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1273_, v_a_1299_);
v___x_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1306_, 0, v___x_1304_);
lean_ctor_set(v___x_1306_, 1, v___x_1305_);
v___x_1307_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1303_, v___x_1306_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1308_ = l_Lean_Expr_appFn_x21(v_a_1299_);
v___x_1309_ = l_Lean_Expr_appFn_x21(v___x_1308_);
v___x_1310_ = l_Lean_Expr_appArg_x21(v___x_1309_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = l_Lean_Meta_whnfD(v___x_1310_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1311_) == 0)
{
lean_object* v_a_1312_; 
v_a_1312_ = lean_ctor_get(v___x_1311_, 0);
lean_inc(v_a_1312_);
lean_dec_ref_known(v___x_1311_, 1);
if (lean_obj_tag(v_a_1312_) == 7)
{
lean_object* v_binderName_1313_; lean_object* v_binderType_1314_; lean_object* v_body_1315_; uint8_t v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_binderName_1313_ = lean_ctor_get(v_a_1312_, 0);
lean_inc(v_binderName_1313_);
v_binderType_1314_ = lean_ctor_get(v_a_1312_, 1);
lean_inc_ref_n(v_binderType_1314_, 3);
v_body_1315_ = lean_ctor_get(v_a_1312_, 2);
lean_inc_ref(v_body_1315_);
lean_dec_ref_known(v_a_1312_, 3);
v___x_1316_ = 0;
v___x_1317_ = l_Lean_mkLambda(v_binderName_1313_, v___x_1316_, v_binderType_1314_, v_body_1315_);
v___x_1318_ = l_Lean_Meta_getLevel(v_binderType_1314_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v_a_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v_a_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc(v_a_1319_);
lean_dec_ref_known(v___x_1318_, 1);
lean_inc_ref(v_a_1274_);
lean_inc_ref(v___x_1317_);
v___x_1320_ = l_Lean_Expr_app___override(v___x_1317_, v_a_1274_);
v___x_1321_ = l_Lean_Meta_getLevel(v___x_1320_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1337_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1324_ = v___x_1321_;
v_isShared_1325_ = v_isSharedCheck_1337_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1321_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1337_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1326_ = l_Lean_Expr_appArg_x21(v___x_1308_);
lean_dec_ref(v___x_1308_);
v___x_1327_ = l_Lean_Expr_appArg_x21(v_a_1299_);
lean_dec(v_a_1299_);
v___x_1328_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1322_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1319_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_mkConst(v___x_1328_, v___x_1331_);
v___x_1333_ = l_Lean_mkApp6(v___x_1332_, v_binderType_1314_, v___x_1317_, v___x_1326_, v___x_1327_, v_h_1273_, v_a_1274_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 0, v___x_1333_);
v___x_1335_ = v___x_1324_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v___x_1333_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
lean_dec(v_a_1319_);
lean_dec_ref(v___x_1317_);
lean_dec_ref(v_binderType_1314_);
lean_dec_ref(v___x_1308_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
v_a_1338_ = lean_ctor_get(v___x_1321_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1321_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1321_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1321_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec_ref(v___x_1317_);
lean_dec_ref(v_binderType_1314_);
lean_dec_ref(v___x_1308_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
v_a_1346_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1318_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1318_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1351_; 
if (v_isShared_1349_ == 0)
{
v___x_1351_ = v___x_1348_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_a_1346_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_a_1312_);
lean_dec_ref(v___x_1308_);
lean_dec_ref(v_a_1274_);
v___x_1354_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1355_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__3, &l_Lean_Meta_mkCongrFun___closed__3_once, _init_l_Lean_Meta_mkCongrFun___closed__3);
v___x_1356_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1273_, v_a_1299_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1355_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
v___x_1358_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1354_, v___x_1357_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1358_;
}
}
else
{
lean_dec_ref(v___x_1308_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
return v___x_1311_;
}
}
}
else
{
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
return v___x_1298_;
}
}
}
else
{
lean_object* v_a_1359_; lean_object* v___x_1361_; uint8_t v_isShared_1362_; uint8_t v_isSharedCheck_1366_; 
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
v_a_1359_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1361_ = v___x_1284_;
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
else
{
lean_inc(v_a_1359_);
lean_dec(v___x_1284_);
v___x_1361_ = lean_box(0);
v_isShared_1362_ = v_isSharedCheck_1366_;
goto v_resetjp_1360_;
}
v_resetjp_1360_:
{
lean_object* v___x_1364_; 
if (v_isShared_1362_ == 0)
{
v___x_1364_ = v___x_1361_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v_a_1359_);
v___x_1364_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1363_;
}
v_reusejp_1363_:
{
return v___x_1364_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___boxed(lean_object* v_h_1367_, lean_object* v_a_1368_, lean_object* v_a_1369_, lean_object* v_a_1370_, lean_object* v_a_1371_, lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_Meta_mkCongrFun(v_h_1367_, v_a_1368_, v_a_1369_, v_a_1370_, v_a_1371_, v_a_1372_);
lean_dec(v_a_1372_);
lean_dec_ref(v_a_1371_);
lean_dec(v_a_1370_);
lean_dec_ref(v_a_1369_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object* v_h_u2081_1378_, lean_object* v_h_u2082_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_, lean_object* v_a_1382_, lean_object* v_a_1383_){
_start:
{
lean_object* v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1386_ = l_Lean_Expr_isAppOf(v_h_u2081_1378_, v___x_1385_);
if (v___x_1386_ == 0)
{
uint8_t v___x_1387_; 
v___x_1387_ = l_Lean_Expr_isAppOf(v_h_u2082_1379_, v___x_1385_);
if (v___x_1387_ == 0)
{
lean_object* v___x_1388_; 
lean_inc_ref(v_h_u2081_1378_);
v___x_1388_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_1378_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1388_) == 0)
{
lean_object* v_a_1389_; lean_object* v___x_1390_; 
v_a_1389_ = lean_ctor_get(v___x_1388_, 0);
lean_inc(v_a_1389_);
lean_dec_ref_known(v___x_1388_, 1);
lean_inc_ref(v_h_u2082_1379_);
v___x_1390_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1390_) == 0)
{
lean_object* v_a_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; uint8_t v___x_1394_; 
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref_known(v___x_1390_, 1);
v___x_1392_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1393_ = lean_unsigned_to_nat(3u);
v___x_1394_ = l_Lean_Expr_isAppOfArity(v_a_1389_, v___x_1392_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
lean_dec(v_a_1391_);
lean_dec_ref(v_h_u2082_1379_);
v___x_1395_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1396_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1397_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1378_, v_a_1389_);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1395_, v___x_1398_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1399_;
}
else
{
uint8_t v___x_1400_; 
v___x_1400_ = l_Lean_Expr_isAppOfArity(v_a_1391_, v___x_1392_, v___x_1393_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
lean_dec(v_a_1389_);
lean_dec_ref(v_h_u2081_1378_);
v___x_1401_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1402_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1403_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_1379_, v_a_1391_);
v___x_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1402_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1401_, v___x_1404_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1405_;
}
else
{
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1406_ = l_Lean_Expr_appFn_x21(v_a_1389_);
v___x_1407_ = l_Lean_Expr_appFn_x21(v___x_1406_);
v___x_1408_ = l_Lean_Expr_appArg_x21(v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = l_Lean_Meta_whnfD(v___x_1408_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
if (lean_obj_tag(v_a_1410_) == 7)
{
lean_object* v_body_1417_; uint8_t v___x_1418_; 
v_body_1417_ = lean_ctor_get(v_a_1410_, 2);
lean_inc_ref(v_body_1417_);
lean_dec_ref_known(v_a_1410_, 3);
v___x_1418_ = l_Lean_Expr_hasLooseBVars(v_body_1417_);
if (v___x_1418_ == 0)
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; 
v___x_1419_ = l_Lean_Expr_appFn_x21(v_a_1391_);
v___x_1420_ = l_Lean_Expr_appFn_x21(v___x_1419_);
v___x_1421_ = l_Lean_Expr_appArg_x21(v___x_1420_);
lean_dec_ref(v___x_1420_);
lean_inc_ref(v___x_1421_);
v___x_1422_ = l_Lean_Meta_getLevel(v___x_1421_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
lean_inc_ref(v_body_1417_);
v___x_1424_ = l_Lean_Meta_getLevel(v_body_1417_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v_a_1425_; lean_object* v___x_1427_; uint8_t v_isShared_1428_; uint8_t v_isSharedCheck_1442_; 
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1427_ = v___x_1424_;
v_isShared_1428_ = v_isSharedCheck_1442_;
goto v_resetjp_1426_;
}
else
{
lean_inc(v_a_1425_);
lean_dec(v___x_1424_);
v___x_1427_ = lean_box(0);
v_isShared_1428_ = v_isSharedCheck_1442_;
goto v_resetjp_1426_;
}
v_resetjp_1426_:
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1429_ = l_Lean_Expr_appArg_x21(v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1430_ = l_Lean_Expr_appArg_x21(v_a_1389_);
lean_dec(v_a_1389_);
v___x_1431_ = l_Lean_Expr_appArg_x21(v___x_1419_);
lean_dec_ref(v___x_1419_);
v___x_1432_ = l_Lean_Expr_appArg_x21(v_a_1391_);
lean_dec(v_a_1391_);
v___x_1433_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1425_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1423_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = l_Lean_mkConst(v___x_1433_, v___x_1436_);
v___x_1438_ = l_Lean_mkApp8(v___x_1437_, v___x_1421_, v_body_1417_, v___x_1429_, v___x_1430_, v___x_1431_, v___x_1432_, v_h_u2081_1378_, v_h_u2082_1379_);
if (v_isShared_1428_ == 0)
{
lean_ctor_set(v___x_1427_, 0, v___x_1438_);
v___x_1440_ = v___x_1427_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1438_);
v___x_1440_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
return v___x_1440_;
}
}
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_a_1423_);
lean_dec_ref(v___x_1421_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v_body_1417_);
lean_dec_ref(v___x_1406_);
lean_dec(v_a_1391_);
lean_dec(v_a_1389_);
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
v_a_1443_ = lean_ctor_get(v___x_1424_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1424_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1424_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1424_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
else
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1458_; 
lean_dec_ref(v___x_1421_);
lean_dec_ref(v___x_1419_);
lean_dec_ref(v_body_1417_);
lean_dec_ref(v___x_1406_);
lean_dec(v_a_1391_);
lean_dec(v_a_1389_);
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
v_a_1451_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1422_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1422_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1456_; 
if (v_isShared_1454_ == 0)
{
v___x_1456_ = v___x_1453_;
goto v_reusejp_1455_;
}
else
{
lean_object* v_reuseFailAlloc_1457_; 
v_reuseFailAlloc_1457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1457_, 0, v_a_1451_);
v___x_1456_ = v_reuseFailAlloc_1457_;
goto v_reusejp_1455_;
}
v_reusejp_1455_:
{
return v___x_1456_;
}
}
}
}
else
{
lean_dec_ref(v_body_1417_);
lean_dec_ref(v___x_1406_);
lean_dec(v_a_1391_);
lean_dec_ref(v_h_u2082_1379_);
goto v___jp_1411_;
}
}
else
{
lean_dec(v_a_1410_);
lean_dec_ref(v___x_1406_);
lean_dec(v_a_1391_);
lean_dec_ref(v_h_u2082_1379_);
goto v___jp_1411_;
}
v___jp_1411_:
{
lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1412_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1413_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1414_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1378_, v_a_1389_);
v___x_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1413_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1412_, v___x_1415_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1416_;
}
}
else
{
lean_dec_ref(v___x_1406_);
lean_dec(v_a_1391_);
lean_dec(v_a_1389_);
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
return v___x_1409_;
}
}
}
}
else
{
lean_dec(v_a_1389_);
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
return v___x_1390_;
}
}
else
{
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
return v___x_1388_;
}
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = l_Lean_Expr_appArg_x21(v_h_u2082_1379_);
lean_dec_ref(v_h_u2082_1379_);
v___x_1460_ = l_Lean_Meta_mkCongrFun(v_h_u2081_1378_, v___x_1459_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1460_;
}
}
else
{
lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___x_1461_ = l_Lean_Expr_appArg_x21(v_h_u2081_1378_);
lean_dec_ref(v_h_u2081_1378_);
v___x_1462_ = l_Lean_Meta_mkCongrArg(v___x_1461_, v_h_u2082_1379_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1462_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr___boxed(lean_object* v_h_u2081_1463_, lean_object* v_h_u2082_1464_, lean_object* v_a_1465_, lean_object* v_a_1466_, lean_object* v_a_1467_, lean_object* v_a_1468_, lean_object* v_a_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_Lean_Meta_mkCongr(v_h_u2081_1463_, v_h_u2082_1464_, v_a_1465_, v_a_1466_, v_a_1467_, v_a_1468_);
lean_dec(v_a_1468_);
lean_dec_ref(v_a_1467_);
lean_dec(v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(lean_object* v_e_1471_, lean_object* v___y_1472_){
_start:
{
uint8_t v___x_1474_; 
v___x_1474_ = l_Lean_Expr_hasMVar(v_e_1471_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_e_1471_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; lean_object* v_mctx_1477_; lean_object* v___x_1478_; lean_object* v_fst_1479_; lean_object* v_snd_1480_; lean_object* v___x_1481_; lean_object* v_cache_1482_; lean_object* v_zetaDeltaFVarIds_1483_; lean_object* v_postponed_1484_; lean_object* v_diag_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1494_; 
v___x_1476_ = lean_st_ref_get(v___y_1472_);
v_mctx_1477_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref(v_mctx_1477_);
lean_dec(v___x_1476_);
v___x_1478_ = l_Lean_instantiateMVarsCore(v_mctx_1477_, v_e_1471_);
v_fst_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_fst_1479_);
v_snd_1480_ = lean_ctor_get(v___x_1478_, 1);
lean_inc(v_snd_1480_);
lean_dec_ref(v___x_1478_);
v___x_1481_ = lean_st_ref_take(v___y_1472_);
v_cache_1482_ = lean_ctor_get(v___x_1481_, 1);
v_zetaDeltaFVarIds_1483_ = lean_ctor_get(v___x_1481_, 2);
v_postponed_1484_ = lean_ctor_get(v___x_1481_, 3);
v_diag_1485_ = lean_ctor_get(v___x_1481_, 4);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1494_ == 0)
{
lean_object* v_unused_1495_; 
v_unused_1495_ = lean_ctor_get(v___x_1481_, 0);
lean_dec(v_unused_1495_);
v___x_1487_ = v___x_1481_;
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
else
{
lean_inc(v_diag_1485_);
lean_inc(v_postponed_1484_);
lean_inc(v_zetaDeltaFVarIds_1483_);
lean_inc(v_cache_1482_);
lean_dec(v___x_1481_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1494_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1490_; 
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 0, v_snd_1480_);
v___x_1490_ = v___x_1487_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_snd_1480_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v_cache_1482_);
lean_ctor_set(v_reuseFailAlloc_1493_, 2, v_zetaDeltaFVarIds_1483_);
lean_ctor_set(v_reuseFailAlloc_1493_, 3, v_postponed_1484_);
lean_ctor_set(v_reuseFailAlloc_1493_, 4, v_diag_1485_);
v___x_1490_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_st_ref_put(v___y_1472_, v___x_1490_);
v___x_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1492_, 0, v_fst_1479_);
return v___x_1492_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg___boxed(lean_object* v_e_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1496_, v___y_1497_);
lean_dec(v___y_1497_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(lean_object* v_e_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1500_, v___y_1502_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___boxed(lean_object* v_e_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(v_e_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1514_, lean_object* v_x_1515_, lean_object* v_x_1516_, lean_object* v_x_1517_){
_start:
{
lean_object* v_ks_1518_; lean_object* v_vs_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1543_; 
v_ks_1518_ = lean_ctor_get(v_x_1514_, 0);
v_vs_1519_ = lean_ctor_get(v_x_1514_, 1);
v_isSharedCheck_1543_ = !lean_is_exclusive(v_x_1514_);
if (v_isSharedCheck_1543_ == 0)
{
v___x_1521_ = v_x_1514_;
v_isShared_1522_ = v_isSharedCheck_1543_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_vs_1519_);
lean_inc(v_ks_1518_);
lean_dec(v_x_1514_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1543_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1523_; uint8_t v___x_1524_; 
v___x_1523_ = lean_array_get_size(v_ks_1518_);
v___x_1524_ = lean_nat_dec_lt(v_x_1515_, v___x_1523_);
if (v___x_1524_ == 0)
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1528_; 
lean_dec(v_x_1515_);
v___x_1525_ = lean_array_push(v_ks_1518_, v_x_1516_);
v___x_1526_ = lean_array_push(v_vs_1519_, v_x_1517_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1526_);
lean_ctor_set(v___x_1521_, 0, v___x_1525_);
v___x_1528_ = v___x_1521_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v___x_1525_);
lean_ctor_set(v_reuseFailAlloc_1529_, 1, v___x_1526_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
else
{
lean_object* v_k_x27_1530_; uint8_t v___x_1531_; 
v_k_x27_1530_ = lean_array_fget_borrowed(v_ks_1518_, v_x_1515_);
v___x_1531_ = l_Lean_instBEqMVarId_beq(v_x_1516_, v_k_x27_1530_);
if (v___x_1531_ == 0)
{
lean_object* v___x_1533_; 
if (v_isShared_1522_ == 0)
{
v___x_1533_ = v___x_1521_;
goto v_reusejp_1532_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_ks_1518_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_vs_1519_);
v___x_1533_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1532_;
}
v_reusejp_1532_:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_unsigned_to_nat(1u);
v___x_1535_ = lean_nat_add(v_x_1515_, v___x_1534_);
lean_dec(v_x_1515_);
v_x_1514_ = v___x_1533_;
v_x_1515_ = v___x_1535_;
goto _start;
}
}
else
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1541_; 
v___x_1538_ = lean_array_fset(v_ks_1518_, v_x_1515_, v_x_1516_);
v___x_1539_ = lean_array_fset(v_vs_1519_, v_x_1515_, v_x_1517_);
lean_dec(v_x_1515_);
if (v_isShared_1522_ == 0)
{
lean_ctor_set(v___x_1521_, 1, v___x_1539_);
lean_ctor_set(v___x_1521_, 0, v___x_1538_);
v___x_1541_ = v___x_1521_;
goto v_reusejp_1540_;
}
else
{
lean_object* v_reuseFailAlloc_1542_; 
v_reuseFailAlloc_1542_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1542_, 0, v___x_1538_);
lean_ctor_set(v_reuseFailAlloc_1542_, 1, v___x_1539_);
v___x_1541_ = v_reuseFailAlloc_1542_;
goto v_reusejp_1540_;
}
v_reusejp_1540_:
{
return v___x_1541_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_1544_, lean_object* v_k_1545_, lean_object* v_v_1546_){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_1544_, v___x_1547_, v_k_1545_, v_v_1546_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1550_, size_t v_x_1551_, size_t v_x_1552_, lean_object* v_x_1553_, lean_object* v_x_1554_){
_start:
{
if (lean_obj_tag(v_x_1550_) == 0)
{
lean_object* v_es_1555_; size_t v___x_1556_; size_t v___x_1557_; lean_object* v_j_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_es_1555_ = lean_ctor_get(v_x_1550_, 0);
v___x_1556_ = ((size_t)31ULL);
v___x_1557_ = lean_usize_land(v_x_1551_, v___x_1556_);
v_j_1558_ = lean_usize_to_nat(v___x_1557_);
v___x_1559_ = lean_array_get_size(v_es_1555_);
v___x_1560_ = lean_nat_dec_lt(v_j_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_dec(v_j_1558_);
lean_dec(v_x_1554_);
lean_dec(v_x_1553_);
return v_x_1550_;
}
else
{
lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1599_; 
lean_inc_ref(v_es_1555_);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_x_1550_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v_x_1550_, 0);
lean_dec(v_unused_1600_);
v___x_1562_ = v_x_1550_;
v_isShared_1563_ = v_isSharedCheck_1599_;
goto v_resetjp_1561_;
}
else
{
lean_dec(v_x_1550_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1599_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v_v_1564_; lean_object* v___x_1565_; lean_object* v_xs_x27_1566_; lean_object* v___y_1568_; 
v_v_1564_ = lean_array_fget(v_es_1555_, v_j_1558_);
v___x_1565_ = lean_box(0);
v_xs_x27_1566_ = lean_array_fset(v_es_1555_, v_j_1558_, v___x_1565_);
switch(lean_obj_tag(v_v_1564_))
{
case 0:
{
lean_object* v_key_1573_; lean_object* v_val_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1584_; 
v_key_1573_ = lean_ctor_get(v_v_1564_, 0);
v_val_1574_ = lean_ctor_get(v_v_1564_, 1);
v_isSharedCheck_1584_ = !lean_is_exclusive(v_v_1564_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1576_ = v_v_1564_;
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
else
{
lean_inc(v_val_1574_);
lean_inc(v_key_1573_);
lean_dec(v_v_1564_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1584_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
uint8_t v___x_1578_; 
v___x_1578_ = l_Lean_instBEqMVarId_beq(v_x_1553_, v_key_1573_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
lean_del_object(v___x_1576_);
v___x_1579_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1573_, v_val_1574_, v_x_1553_, v_x_1554_);
v___x_1580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1580_, 0, v___x_1579_);
v___y_1568_ = v___x_1580_;
goto v___jp_1567_;
}
else
{
lean_object* v___x_1582_; 
lean_dec(v_val_1574_);
lean_dec(v_key_1573_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v_x_1554_);
lean_ctor_set(v___x_1576_, 0, v_x_1553_);
v___x_1582_ = v___x_1576_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_x_1553_);
lean_ctor_set(v_reuseFailAlloc_1583_, 1, v_x_1554_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
v___y_1568_ = v___x_1582_;
goto v___jp_1567_;
}
}
}
}
case 1:
{
lean_object* v_node_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1597_; 
v_node_1585_ = lean_ctor_get(v_v_1564_, 0);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_v_1564_);
if (v_isSharedCheck_1597_ == 0)
{
v___x_1587_ = v_v_1564_;
v_isShared_1588_ = v_isSharedCheck_1597_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_node_1585_);
lean_dec(v_v_1564_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1597_;
goto v_resetjp_1586_;
}
v_resetjp_1586_:
{
size_t v___x_1589_; size_t v___x_1590_; size_t v___x_1591_; size_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1595_; 
v___x_1589_ = ((size_t)5ULL);
v___x_1590_ = lean_usize_shift_right(v_x_1551_, v___x_1589_);
v___x_1591_ = ((size_t)1ULL);
v___x_1592_ = lean_usize_add(v_x_1552_, v___x_1591_);
v___x_1593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_node_1585_, v___x_1590_, v___x_1592_, v_x_1553_, v_x_1554_);
if (v_isShared_1588_ == 0)
{
lean_ctor_set(v___x_1587_, 0, v___x_1593_);
v___x_1595_ = v___x_1587_;
goto v_reusejp_1594_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1593_);
v___x_1595_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1594_;
}
v_reusejp_1594_:
{
v___y_1568_ = v___x_1595_;
goto v___jp_1567_;
}
}
}
default: 
{
lean_object* v___x_1598_; 
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_x_1553_);
lean_ctor_set(v___x_1598_, 1, v_x_1554_);
v___y_1568_ = v___x_1598_;
goto v___jp_1567_;
}
}
v___jp_1567_:
{
lean_object* v___x_1569_; lean_object* v___x_1571_; 
v___x_1569_ = lean_array_fset(v_xs_x27_1566_, v_j_1558_, v___y_1568_);
lean_dec(v_j_1558_);
if (v_isShared_1563_ == 0)
{
lean_ctor_set(v___x_1562_, 0, v___x_1569_);
v___x_1571_ = v___x_1562_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
}
}
}
else
{
lean_object* v_ks_1601_; lean_object* v_vs_1602_; lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1620_; 
v_ks_1601_ = lean_ctor_get(v_x_1550_, 0);
v_vs_1602_ = lean_ctor_get(v_x_1550_, 1);
v_isSharedCheck_1620_ = !lean_is_exclusive(v_x_1550_);
if (v_isSharedCheck_1620_ == 0)
{
v___x_1604_ = v_x_1550_;
v_isShared_1605_ = v_isSharedCheck_1620_;
goto v_resetjp_1603_;
}
else
{
lean_inc(v_vs_1602_);
lean_inc(v_ks_1601_);
lean_dec(v_x_1550_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1620_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v___x_1607_; 
if (v_isShared_1605_ == 0)
{
v___x_1607_ = v___x_1604_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1619_; 
v_reuseFailAlloc_1619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1619_, 0, v_ks_1601_);
lean_ctor_set(v_reuseFailAlloc_1619_, 1, v_vs_1602_);
v___x_1607_ = v_reuseFailAlloc_1619_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
lean_object* v_newNode_1608_; size_t v___x_1609_; uint8_t v___x_1610_; 
v_newNode_1608_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v___x_1607_, v_x_1553_, v_x_1554_);
v___x_1609_ = ((size_t)7ULL);
v___x_1610_ = lean_usize_dec_le(v___x_1609_, v_x_1552_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; 
v___x_1611_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1608_);
v___x_1612_ = lean_unsigned_to_nat(4u);
v___x_1613_ = lean_nat_dec_lt(v___x_1611_, v___x_1612_);
lean_dec(v___x_1611_);
if (v___x_1613_ == 0)
{
lean_object* v_ks_1614_; lean_object* v_vs_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; 
v_ks_1614_ = lean_ctor_get(v_newNode_1608_, 0);
lean_inc_ref(v_ks_1614_);
v_vs_1615_ = lean_ctor_get(v_newNode_1608_, 1);
lean_inc_ref(v_vs_1615_);
lean_dec_ref(v_newNode_1608_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1618_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1552_, v_ks_1614_, v_vs_1615_, v___x_1616_, v___x_1617_);
lean_dec_ref(v_vs_1615_);
lean_dec_ref(v_ks_1614_);
return v___x_1618_;
}
else
{
return v_newNode_1608_;
}
}
else
{
return v_newNode_1608_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_1621_, lean_object* v_keys_1622_, lean_object* v_vals_1623_, lean_object* v_i_1624_, lean_object* v_entries_1625_){
_start:
{
lean_object* v___x_1626_; uint8_t v___x_1627_; 
v___x_1626_ = lean_array_get_size(v_keys_1622_);
v___x_1627_ = lean_nat_dec_lt(v_i_1624_, v___x_1626_);
if (v___x_1627_ == 0)
{
lean_dec(v_i_1624_);
return v_entries_1625_;
}
else
{
lean_object* v_k_1628_; lean_object* v_v_1629_; uint64_t v___x_1630_; size_t v_h_1631_; size_t v___x_1632_; lean_object* v___x_1633_; size_t v___x_1634_; size_t v___x_1635_; size_t v___x_1636_; size_t v_h_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v_k_1628_ = lean_array_fget_borrowed(v_keys_1622_, v_i_1624_);
v_v_1629_ = lean_array_fget_borrowed(v_vals_1623_, v_i_1624_);
v___x_1630_ = l_Lean_instHashableMVarId_hash(v_k_1628_);
v_h_1631_ = lean_uint64_to_usize(v___x_1630_);
v___x_1632_ = ((size_t)5ULL);
v___x_1633_ = lean_unsigned_to_nat(1u);
v___x_1634_ = ((size_t)1ULL);
v___x_1635_ = lean_usize_sub(v_depth_1621_, v___x_1634_);
v___x_1636_ = lean_usize_mul(v___x_1632_, v___x_1635_);
v_h_1637_ = lean_usize_shift_right(v_h_1631_, v___x_1636_);
v___x_1638_ = lean_nat_add(v_i_1624_, v___x_1633_);
lean_dec(v_i_1624_);
lean_inc(v_v_1629_);
lean_inc(v_k_1628_);
v___x_1639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_entries_1625_, v_h_1637_, v_depth_1621_, v_k_1628_, v_v_1629_);
v_i_1624_ = v___x_1638_;
v_entries_1625_ = v___x_1639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1641_, lean_object* v_keys_1642_, lean_object* v_vals_1643_, lean_object* v_i_1644_, lean_object* v_entries_1645_){
_start:
{
size_t v_depth_boxed_1646_; lean_object* v_res_1647_; 
v_depth_boxed_1646_ = lean_unbox_usize(v_depth_1641_);
lean_dec(v_depth_1641_);
v_res_1647_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_1646_, v_keys_1642_, v_vals_1643_, v_i_1644_, v_entries_1645_);
lean_dec_ref(v_vals_1643_);
lean_dec_ref(v_keys_1642_);
return v_res_1647_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_, lean_object* v_x_1652_){
_start:
{
size_t v_x_1967__boxed_1653_; size_t v_x_1968__boxed_1654_; lean_object* v_res_1655_; 
v_x_1967__boxed_1653_ = lean_unbox_usize(v_x_1649_);
lean_dec(v_x_1649_);
v_x_1968__boxed_1654_ = lean_unbox_usize(v_x_1650_);
lean_dec(v_x_1650_);
v_res_1655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1648_, v_x_1967__boxed_1653_, v_x_1968__boxed_1654_, v_x_1651_, v_x_1652_);
return v_res_1655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object* v_x_1656_, lean_object* v_x_1657_, lean_object* v_x_1658_){
_start:
{
uint64_t v___x_1659_; size_t v___x_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1659_ = l_Lean_instHashableMVarId_hash(v_x_1657_);
v___x_1660_ = lean_uint64_to_usize(v___x_1659_);
v___x_1661_ = ((size_t)1ULL);
v___x_1662_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1656_, v___x_1660_, v___x_1661_, v_x_1657_, v_x_1658_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(lean_object* v_mvarId_1663_, lean_object* v_val_1664_, lean_object* v___y_1665_){
_start:
{
lean_object* v___x_1667_; lean_object* v_mctx_1668_; lean_object* v_cache_1669_; lean_object* v_zetaDeltaFVarIds_1670_; lean_object* v_postponed_1671_; lean_object* v_diag_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1701_; 
v___x_1667_ = lean_st_ref_take(v___y_1665_);
v_mctx_1668_ = lean_ctor_get(v___x_1667_, 0);
v_cache_1669_ = lean_ctor_get(v___x_1667_, 1);
v_zetaDeltaFVarIds_1670_ = lean_ctor_get(v___x_1667_, 2);
v_postponed_1671_ = lean_ctor_get(v___x_1667_, 3);
v_diag_1672_ = lean_ctor_get(v___x_1667_, 4);
v_isSharedCheck_1701_ = !lean_is_exclusive(v___x_1667_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1674_ = v___x_1667_;
v_isShared_1675_ = v_isSharedCheck_1701_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_diag_1672_);
lean_inc(v_postponed_1671_);
lean_inc(v_zetaDeltaFVarIds_1670_);
lean_inc(v_cache_1669_);
lean_inc(v_mctx_1668_);
lean_dec(v___x_1667_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1701_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v_depth_1676_; lean_object* v_levelAssignDepth_1677_; lean_object* v_lmvarCounter_1678_; lean_object* v_mvarCounter_1679_; lean_object* v_lDecls_1680_; lean_object* v_decls_1681_; lean_object* v_userNames_1682_; lean_object* v_lAssignment_1683_; lean_object* v_eAssignment_1684_; lean_object* v_dAssignment_1685_; lean_object* v_instanceTypedMVars_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1700_; 
v_depth_1676_ = lean_ctor_get(v_mctx_1668_, 0);
v_levelAssignDepth_1677_ = lean_ctor_get(v_mctx_1668_, 1);
v_lmvarCounter_1678_ = lean_ctor_get(v_mctx_1668_, 2);
v_mvarCounter_1679_ = lean_ctor_get(v_mctx_1668_, 3);
v_lDecls_1680_ = lean_ctor_get(v_mctx_1668_, 4);
v_decls_1681_ = lean_ctor_get(v_mctx_1668_, 5);
v_userNames_1682_ = lean_ctor_get(v_mctx_1668_, 6);
v_lAssignment_1683_ = lean_ctor_get(v_mctx_1668_, 7);
v_eAssignment_1684_ = lean_ctor_get(v_mctx_1668_, 8);
v_dAssignment_1685_ = lean_ctor_get(v_mctx_1668_, 9);
v_instanceTypedMVars_1686_ = lean_ctor_get(v_mctx_1668_, 10);
v_isSharedCheck_1700_ = !lean_is_exclusive(v_mctx_1668_);
if (v_isSharedCheck_1700_ == 0)
{
v___x_1688_ = v_mctx_1668_;
v_isShared_1689_ = v_isSharedCheck_1700_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_instanceTypedMVars_1686_);
lean_inc(v_dAssignment_1685_);
lean_inc(v_eAssignment_1684_);
lean_inc(v_lAssignment_1683_);
lean_inc(v_userNames_1682_);
lean_inc(v_decls_1681_);
lean_inc(v_lDecls_1680_);
lean_inc(v_mvarCounter_1679_);
lean_inc(v_lmvarCounter_1678_);
lean_inc(v_levelAssignDepth_1677_);
lean_inc(v_depth_1676_);
lean_dec(v_mctx_1668_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1700_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1690_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_eAssignment_1684_, v_mvarId_1663_, v_val_1664_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 8, v___x_1690_);
v___x_1692_ = v___x_1688_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v_depth_1676_);
lean_ctor_set(v_reuseFailAlloc_1699_, 1, v_levelAssignDepth_1677_);
lean_ctor_set(v_reuseFailAlloc_1699_, 2, v_lmvarCounter_1678_);
lean_ctor_set(v_reuseFailAlloc_1699_, 3, v_mvarCounter_1679_);
lean_ctor_set(v_reuseFailAlloc_1699_, 4, v_lDecls_1680_);
lean_ctor_set(v_reuseFailAlloc_1699_, 5, v_decls_1681_);
lean_ctor_set(v_reuseFailAlloc_1699_, 6, v_userNames_1682_);
lean_ctor_set(v_reuseFailAlloc_1699_, 7, v_lAssignment_1683_);
lean_ctor_set(v_reuseFailAlloc_1699_, 8, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1699_, 9, v_dAssignment_1685_);
lean_ctor_set(v_reuseFailAlloc_1699_, 10, v_instanceTypedMVars_1686_);
v___x_1692_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
lean_object* v___x_1694_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1692_);
v___x_1694_ = v___x_1674_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1692_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_cache_1669_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_zetaDeltaFVarIds_1670_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_postponed_1671_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_diag_1672_);
v___x_1694_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1695_ = lean_st_ref_put(v___y_1665_, v___x_1694_);
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
size_t v_x_2407__boxed_1871_; size_t v_x_2408__boxed_1872_; lean_object* v_res_1873_; 
v_x_2407__boxed_1871_ = lean_unbox_usize(v_x_1867_);
lean_dec(v_x_1867_);
v_x_2408__boxed_1872_ = lean_unbox_usize(v_x_1868_);
lean_dec(v_x_1868_);
v_res_1873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1865_, v_x_1866_, v_x_2407__boxed_1871_, v_x_2408__boxed_1872_, v_x_1869_, v_x_1870_);
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
lean_object* v_x_1955_; lean_object* v___y_1957_; lean_object* v___x_1974_; 
lean_dec(v_binderName_1930_);
v_x_1955_ = lean_array_fget_borrowed(v_xs_1917_, v_i_1919_);
lean_inc(v_a_1926_);
lean_inc_ref(v_a_1925_);
lean_inc(v_a_1924_);
lean_inc_ref(v_a_1923_);
lean_inc(v_x_1955_);
v___x_1974_ = lean_infer_type(v_x_1955_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1974_) == 0)
{
lean_object* v_a_1975_; lean_object* v___x_1976_; uint8_t v_transparency_1977_; uint8_t v___x_1978_; uint8_t v___x_1979_; 
v_a_1975_ = lean_ctor_get(v___x_1974_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1974_, 1);
v___x_1976_ = l_Lean_Meta_Context_config(v_a_1923_);
v_transparency_1977_ = lean_ctor_get_uint8(v___x_1976_, 9);
lean_dec_ref(v___x_1976_);
v___x_1978_ = 1;
v___x_1979_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1977_, v___x_1978_);
if (v___x_1979_ == 0)
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_Meta_isExprDefEq(v_d_1935_, v_a_1975_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
v___y_1957_ = v___x_1980_;
goto v___jp_1956_;
}
else
{
lean_object* v_keyedConfig_1981_; uint8_t v_trackZetaDelta_1982_; lean_object* v_zetaDeltaSet_1983_; lean_object* v_lctx_1984_; lean_object* v_localInstances_1985_; lean_object* v_defEqCtx_x3f_1986_; lean_object* v_synthPendingDepth_1987_; lean_object* v_customCanUnfoldPredicate_x3f_1988_; uint8_t v_univApprox_1989_; uint8_t v_inTypeClassResolution_1990_; uint8_t v_cacheInferType_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v_keyedConfig_1981_ = lean_ctor_get(v_a_1923_, 0);
v_trackZetaDelta_1982_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7);
v_zetaDeltaSet_1983_ = lean_ctor_get(v_a_1923_, 1);
v_lctx_1984_ = lean_ctor_get(v_a_1923_, 2);
v_localInstances_1985_ = lean_ctor_get(v_a_1923_, 3);
v_defEqCtx_x3f_1986_ = lean_ctor_get(v_a_1923_, 4);
v_synthPendingDepth_1987_ = lean_ctor_get(v_a_1923_, 5);
v_customCanUnfoldPredicate_x3f_1988_ = lean_ctor_get(v_a_1923_, 6);
v_univApprox_1989_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1990_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7 + 2);
v_cacheInferType_1991_ = lean_ctor_get_uint8(v_a_1923_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1981_);
v___x_1992_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1978_, v_keyedConfig_1981_);
lean_inc(v_customCanUnfoldPredicate_x3f_1988_);
lean_inc(v_synthPendingDepth_1987_);
lean_inc(v_defEqCtx_x3f_1986_);
lean_inc_ref(v_localInstances_1985_);
lean_inc_ref(v_lctx_1984_);
lean_inc(v_zetaDeltaSet_1983_);
v___x_1993_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1993_, 0, v___x_1992_);
lean_ctor_set(v___x_1993_, 1, v_zetaDeltaSet_1983_);
lean_ctor_set(v___x_1993_, 2, v_lctx_1984_);
lean_ctor_set(v___x_1993_, 3, v_localInstances_1985_);
lean_ctor_set(v___x_1993_, 4, v_defEqCtx_x3f_1986_);
lean_ctor_set(v___x_1993_, 5, v_synthPendingDepth_1987_);
lean_ctor_set(v___x_1993_, 6, v_customCanUnfoldPredicate_x3f_1988_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*7, v_trackZetaDelta_1982_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*7 + 1, v_univApprox_1989_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1990_);
lean_ctor_set_uint8(v___x_1993_, sizeof(void*)*7 + 3, v_cacheInferType_1991_);
v___x_1994_ = l_Lean_Meta_isExprDefEq(v_d_1935_, v_a_1975_, v___x_1993_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec_ref_known(v___x_1993_, 7);
v___y_1957_ = v___x_1994_;
goto v___jp_1956_;
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
return v___x_1974_;
}
v___jp_1956_:
{
if (lean_obj_tag(v___y_1957_) == 0)
{
lean_object* v_a_1958_; uint8_t v___x_1959_; 
v_a_1958_ = lean_ctor_get(v___y_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___y_1957_, 1);
v___x_1959_ = lean_unbox(v_a_1958_);
lean_dec(v_a_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
lean_dec_ref(v_body_1932_);
lean_dec_ref(v_instMVars_1922_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
v___x_1960_ = l_Lean_mkAppN(v_f_1916_, v_args_1921_);
lean_dec_ref(v_args_1921_);
lean_inc(v_x_1955_);
v___x_1961_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1960_, v_x_1955_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; 
v___x_1962_ = lean_unsigned_to_nat(1u);
v___x_1963_ = lean_nat_add(v_i_1919_, v___x_1962_);
lean_dec(v_i_1919_);
lean_inc(v_x_1955_);
v___x_1964_ = lean_array_push(v_args_1921_, v_x_1955_);
v_type_1918_ = v_body_1932_;
v_i_1919_ = v___x_1963_;
v_args_1921_ = v___x_1964_;
goto _start;
}
}
else
{
lean_object* v_a_1966_; lean_object* v___x_1968_; uint8_t v_isShared_1969_; uint8_t v_isSharedCheck_1973_; 
lean_dec_ref(v_body_1932_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_f_1916_);
v_a_1966_ = lean_ctor_get(v___y_1957_, 0);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___y_1957_);
if (v_isSharedCheck_1973_ == 0)
{
v___x_1968_ = v___y_1957_;
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
else
{
lean_inc(v_a_1966_);
lean_dec(v___y_1957_);
v___x_1968_ = lean_box(0);
v_isShared_1969_ = v_isSharedCheck_1973_;
goto v_resetjp_1967_;
}
v_resetjp_1967_:
{
lean_object* v___x_1971_; 
if (v_isShared_1969_ == 0)
{
v___x_1971_ = v___x_1968_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_a_1966_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
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
lean_object* v___x_1995_; lean_object* v_type_1996_; lean_object* v___x_1997_; 
v___x_1995_ = lean_array_get_size(v_args_1921_);
v_type_1996_ = lean_expr_instantiate_rev_range(v_type_1918_, v_j_1920_, v___x_1995_, v_args_1921_);
lean_dec(v_j_1920_);
lean_dec_ref(v_type_1918_);
v___x_1997_ = l_Lean_Meta_whnfD(v_type_1996_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
if (lean_obj_tag(v___x_1997_) == 0)
{
lean_object* v_a_1998_; uint8_t v___x_1999_; 
v_a_1998_ = lean_ctor_get(v___x_1997_, 0);
lean_inc(v_a_1998_);
lean_dec_ref_known(v___x_1997_, 1);
v___x_1999_ = l_Lean_Expr_isForall(v_a_1998_);
if (v___x_1999_ == 0)
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
lean_dec(v_a_1998_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_i_1919_);
v___x_2000_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2001_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2002_ = l_Lean_indentExpr(v_f_1916_);
v___x_2003_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_2001_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2005_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2003_);
lean_ctor_set(v___x_2005_, 1, v___x_2004_);
v___x_2006_ = lean_unsigned_to_nat(0u);
v___x_2007_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2008_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1917_, v___x_2006_, v___x_2007_);
v___x_2009_ = l_Lean_indentD(v___x_2008_);
v___x_2010_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2005_);
lean_ctor_set(v___x_2010_, 1, v___x_2009_);
v___x_2011_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_2000_, v___x_2010_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
return v___x_2011_;
}
else
{
v_type_1918_ = v_a_1998_;
v_j_1920_ = v___x_1995_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
lean_dec(v_i_1919_);
lean_dec_ref(v_f_1916_);
return v___x_1997_;
}
}
}
else
{
lean_object* v___x_2013_; lean_object* v___x_2014_; 
lean_dec(v_j_1920_);
lean_dec(v_i_1919_);
lean_dec_ref(v_type_1918_);
v___x_2013_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2014_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2013_, v_f_1916_, v_args_1921_, v_instMVars_1922_, v_a_1923_, v_a_1924_, v_a_1925_, v_a_1926_);
lean_dec_ref(v_instMVars_1922_);
lean_dec_ref(v_args_1921_);
return v___x_2014_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2015_, lean_object* v_xs_2016_, lean_object* v_type_2017_, lean_object* v_i_2018_, lean_object* v_j_2019_, lean_object* v_args_2020_, lean_object* v_instMVars_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2015_, v_xs_2016_, v_type_2017_, v_i_2018_, v_j_2019_, v_args_2020_, v_instMVars_2021_, v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_);
lean_dec(v_a_2025_);
lean_dec_ref(v_a_2024_);
lean_dec(v_a_2023_);
lean_dec_ref(v_a_2022_);
lean_dec_ref(v_xs_2016_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2030_, lean_object* v_fType_2031_, lean_object* v_xs_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2040_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2030_, v_xs_2032_, v_fType_2031_, v___x_2038_, v___x_2038_, v___x_2039_, v___x_2039_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
return v___x_2040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2041_, lean_object* v_fType_2042_, lean_object* v_xs_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2041_, v_fType_2042_, v_xs_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_xs_2043_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2050_, lean_object* v_x_2051_, lean_object* v___y_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_){
_start:
{
if (lean_obj_tag(v_x_2050_) == 0)
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2057_ = l_List_reverse___redArg(v_x_2051_);
v___x_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2058_, 0, v___x_2057_);
return v___x_2058_;
}
else
{
lean_object* v_tail_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2077_; 
v_tail_2059_ = lean_ctor_get(v_x_2050_, 1);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_x_2050_);
if (v_isSharedCheck_2077_ == 0)
{
lean_object* v_unused_2078_; 
v_unused_2078_ = lean_ctor_get(v_x_2050_, 0);
lean_dec(v_unused_2078_);
v___x_2061_ = v_x_2050_;
v_isShared_2062_ = v_isSharedCheck_2077_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_tail_2059_);
lean_dec(v_x_2050_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2077_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; 
v___x_2063_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_);
if (lean_obj_tag(v___x_2063_) == 0)
{
lean_object* v_a_2064_; lean_object* v___x_2066_; 
v_a_2064_ = lean_ctor_get(v___x_2063_, 0);
lean_inc(v_a_2064_);
lean_dec_ref_known(v___x_2063_, 1);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 1, v_x_2051_);
lean_ctor_set(v___x_2061_, 0, v_a_2064_);
v___x_2066_ = v___x_2061_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_a_2064_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v_x_2051_);
v___x_2066_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v_x_2050_ = v_tail_2059_;
v_x_2051_ = v___x_2066_;
goto _start;
}
}
else
{
lean_object* v_a_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2076_; 
lean_del_object(v___x_2061_);
lean_dec(v_tail_2059_);
lean_dec(v_x_2051_);
v_a_2069_ = lean_ctor_get(v___x_2063_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v___x_2063_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_2071_ = v___x_2063_;
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_a_2069_);
lean_dec(v___x_2063_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2076_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2074_; 
if (v_isShared_2072_ == 0)
{
v___x_2074_ = v___x_2071_;
goto v_reusejp_2073_;
}
else
{
lean_object* v_reuseFailAlloc_2075_; 
v_reuseFailAlloc_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2075_, 0, v_a_2069_);
v___x_2074_ = v_reuseFailAlloc_2075_;
goto v_reusejp_2073_;
}
v_reusejp_2073_:
{
return v___x_2074_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2079_, v_x_2080_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
lean_dec(v___y_2082_);
lean_dec_ref(v___y_2081_);
return v_res_2086_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_2087_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
v___x_2088_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2088_);
return v___x_2089_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; 
v___x_2090_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2091_ = lean_unsigned_to_nat(0u);
v___x_2092_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2091_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
lean_ctor_set(v___x_2092_, 2, v___x_2091_);
lean_ctor_set(v___x_2092_, 3, v___x_2091_);
lean_ctor_set(v___x_2092_, 4, v___x_2090_);
lean_ctor_set(v___x_2092_, 5, v___x_2090_);
lean_ctor_set(v___x_2092_, 6, v___x_2090_);
lean_ctor_set(v___x_2092_, 7, v___x_2090_);
lean_ctor_set(v___x_2092_, 8, v___x_2090_);
lean_ctor_set(v___x_2092_, 9, v___x_2090_);
lean_ctor_set(v___x_2092_, 10, v___x_2090_);
return v___x_2092_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(32u);
v___x_2094_ = lean_mk_empty_array_with_capacity(v___x_2093_);
v___x_2095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2095_, 0, v___x_2094_);
return v___x_2095_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2096_ = ((size_t)5ULL);
v___x_2097_ = lean_unsigned_to_nat(0u);
v___x_2098_ = lean_unsigned_to_nat(32u);
v___x_2099_ = lean_mk_empty_array_with_capacity(v___x_2098_);
v___x_2100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2101_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2101_, 0, v___x_2100_);
lean_ctor_set(v___x_2101_, 1, v___x_2099_);
lean_ctor_set(v___x_2101_, 2, v___x_2097_);
lean_ctor_set(v___x_2101_, 3, v___x_2097_);
lean_ctor_set_usize(v___x_2101_, 4, v___x_2096_);
return v___x_2101_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v___x_2102_ = lean_box(1);
v___x_2103_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2105_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2105_, 0, v___x_2104_);
lean_ctor_set(v___x_2105_, 1, v___x_2103_);
lean_ctor_set(v___x_2105_, 2, v___x_2102_);
return v___x_2105_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2107_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2108_ = l_Lean_stringToMessageData(v___x_2107_);
return v___x_2108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2111_ = l_Lean_stringToMessageData(v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2113_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2114_ = l_Lean_stringToMessageData(v___x_2113_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2116_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2117_ = l_Lean_stringToMessageData(v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2120_ = l_Lean_stringToMessageData(v___x_2119_);
return v___x_2120_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2127_, lean_object* v_declHint_2128_, lean_object* v___y_2129_){
_start:
{
lean_object* v___x_2131_; lean_object* v_env_2132_; uint8_t v___x_2133_; 
v___x_2131_ = lean_st_ref_get(v___y_2129_);
v_env_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc_ref(v_env_2132_);
lean_dec(v___x_2131_);
v___x_2133_ = l_Lean_Name_isAnonymous(v_declHint_2128_);
if (v___x_2133_ == 0)
{
uint8_t v_isExporting_2134_; 
v_isExporting_2134_ = lean_ctor_get_uint8(v_env_2132_, sizeof(void*)*8);
if (v_isExporting_2134_ == 0)
{
lean_object* v___x_2135_; 
lean_dec_ref(v_env_2132_);
lean_dec(v_declHint_2128_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v_msg_2127_);
return v___x_2135_;
}
else
{
lean_object* v___x_2136_; uint8_t v___x_2137_; 
lean_inc_ref(v_env_2132_);
v___x_2136_ = l_Lean_Environment_setExporting(v_env_2132_, v___x_2133_);
lean_inc(v_declHint_2128_);
lean_inc_ref(v___x_2136_);
v___x_2137_ = l_Lean_Environment_contains(v___x_2136_, v_declHint_2128_, v_isExporting_2134_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_dec_ref(v___x_2136_);
lean_dec_ref(v_env_2132_);
lean_dec(v_declHint_2128_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_msg_2127_);
return v___x_2138_;
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v_c_2144_; lean_object* v___x_2145_; 
v___x_2139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2141_ = l_Lean_Options_empty;
v___x_2142_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2136_);
lean_ctor_set(v___x_2142_, 1, v___x_2139_);
lean_ctor_set(v___x_2142_, 2, v___x_2140_);
lean_ctor_set(v___x_2142_, 3, v___x_2141_);
lean_inc(v_declHint_2128_);
v___x_2143_ = l_Lean_MessageData_ofConstName(v_declHint_2128_, v___x_2133_);
v_c_2144_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2144_, 0, v___x_2142_);
lean_ctor_set(v_c_2144_, 1, v___x_2143_);
v___x_2145_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2132_, v_declHint_2128_);
if (lean_obj_tag(v___x_2145_) == 0)
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
lean_dec_ref(v_env_2132_);
lean_dec(v_declHint_2128_);
v___x_2146_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2147_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
lean_ctor_set(v___x_2147_, 1, v_c_2144_);
v___x_2148_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2149_, 0, v___x_2147_);
lean_ctor_set(v___x_2149_, 1, v___x_2148_);
v___x_2150_ = l_Lean_MessageData_note(v___x_2149_);
v___x_2151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_msg_2127_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
return v___x_2152_;
}
else
{
lean_object* v_val_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2188_; 
v_val_2153_ = lean_ctor_get(v___x_2145_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2145_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2155_ = v___x_2145_;
v_isShared_2156_ = v_isSharedCheck_2188_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_val_2153_);
lean_dec(v___x_2145_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2188_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v_mod_2160_; uint8_t v___x_2161_; 
v___x_2157_ = lean_box(0);
v___x_2158_ = l_Lean_Environment_header(v_env_2132_);
lean_dec_ref(v_env_2132_);
v___x_2159_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2158_);
v_mod_2160_ = lean_array_get(v___x_2157_, v___x_2159_, v_val_2153_);
lean_dec(v_val_2153_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = l_Lean_isPrivateName(v_declHint_2128_);
lean_dec(v_declHint_2128_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v_c_2144_);
v___x_2164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2163_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l_Lean_MessageData_ofName(v_mod_2160_);
v___x_2167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2167_, 0, v___x_2165_);
lean_ctor_set(v___x_2167_, 1, v___x_2166_);
v___x_2168_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2167_);
lean_ctor_set(v___x_2169_, 1, v___x_2168_);
v___x_2170_ = l_Lean_MessageData_note(v___x_2169_);
v___x_2171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2171_, 0, v_msg_2127_);
lean_ctor_set(v___x_2171_, 1, v___x_2170_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2171_);
v___x_2173_ = v___x_2155_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2174_; 
v_reuseFailAlloc_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2174_, 0, v___x_2171_);
v___x_2173_ = v_reuseFailAlloc_2174_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
return v___x_2173_;
}
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2186_; 
v___x_2175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2176_, 0, v___x_2175_);
lean_ctor_set(v___x_2176_, 1, v_c_2144_);
v___x_2177_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2176_);
lean_ctor_set(v___x_2178_, 1, v___x_2177_);
v___x_2179_ = l_Lean_MessageData_ofName(v_mod_2160_);
v___x_2180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2178_);
lean_ctor_set(v___x_2180_, 1, v___x_2179_);
v___x_2181_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2182_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2180_);
lean_ctor_set(v___x_2182_, 1, v___x_2181_);
v___x_2183_ = l_Lean_MessageData_note(v___x_2182_);
v___x_2184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2184_, 0, v_msg_2127_);
lean_ctor_set(v___x_2184_, 1, v___x_2183_);
if (v_isShared_2156_ == 0)
{
lean_ctor_set_tag(v___x_2155_, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2184_);
v___x_2186_ = v___x_2155_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2184_);
v___x_2186_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
return v___x_2186_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2189_; 
lean_dec_ref(v_env_2132_);
lean_dec(v_declHint_2128_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_msg_2127_);
return v___x_2189_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2190_, lean_object* v_declHint_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v_res_2194_; 
v_res_2194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2190_, v_declHint_2191_, v___y_2192_);
lean_dec(v___y_2192_);
return v_res_2194_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2195_, lean_object* v_declHint_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v___x_2202_; lean_object* v_a_2203_; lean_object* v___x_2205_; uint8_t v_isShared_2206_; uint8_t v_isSharedCheck_2212_; 
v___x_2202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2195_, v_declHint_2196_, v___y_2200_);
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2202_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2205_ = v___x_2202_;
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
else
{
lean_inc(v_a_2203_);
lean_dec(v___x_2202_);
v___x_2205_ = lean_box(0);
v_isShared_2206_ = v_isSharedCheck_2212_;
goto v_resetjp_2204_;
}
v_resetjp_2204_:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2207_ = l_Lean_unknownIdentifierMessageTag;
v___x_2208_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v_a_2203_);
if (v_isShared_2206_ == 0)
{
lean_ctor_set(v___x_2205_, 0, v___x_2208_);
v___x_2210_ = v___x_2205_;
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2213_, lean_object* v_declHint_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
lean_object* v_res_2220_; 
v_res_2220_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2213_, v_declHint_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
return v_res_2220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2221_, lean_object* v_msg_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v_toCold_2228_; lean_object* v_currRecDepth_2229_; lean_object* v_ref_2230_; uint8_t v_diag_2231_; uint8_t v_suppressElabErrors_2232_; lean_object* v_ref_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v_toCold_2228_ = lean_ctor_get(v___y_2225_, 0);
v_currRecDepth_2229_ = lean_ctor_get(v___y_2225_, 1);
v_ref_2230_ = lean_ctor_get(v___y_2225_, 2);
v_diag_2231_ = lean_ctor_get_uint8(v___y_2225_, sizeof(void*)*3);
v_suppressElabErrors_2232_ = lean_ctor_get_uint8(v___y_2225_, sizeof(void*)*3 + 1);
v_ref_2233_ = l_Lean_replaceRef(v_ref_2221_, v_ref_2230_);
lean_inc(v_currRecDepth_2229_);
lean_inc_ref(v_toCold_2228_);
v___x_2234_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2234_, 0, v_toCold_2228_);
lean_ctor_set(v___x_2234_, 1, v_currRecDepth_2229_);
lean_ctor_set(v___x_2234_, 2, v_ref_2233_);
lean_ctor_set_uint8(v___x_2234_, sizeof(void*)*3, v_diag_2231_);
lean_ctor_set_uint8(v___x_2234_, sizeof(void*)*3 + 1, v_suppressElabErrors_2232_);
v___x_2235_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2222_, v___y_2223_, v___y_2224_, v___x_2234_, v___y_2226_);
lean_dec_ref_known(v___x_2234_, 3);
return v___x_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2236_, lean_object* v_msg_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2236_, v_msg_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v_ref_2236_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2244_, lean_object* v_msg_2245_, lean_object* v_declHint_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_){
_start:
{
lean_object* v___x_2252_; lean_object* v_a_2253_; lean_object* v___x_2254_; 
v___x_2252_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2245_, v_declHint_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_a_2253_);
lean_dec_ref(v___x_2252_);
v___x_2254_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2244_, v_a_2253_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2255_, lean_object* v_msg_2256_, lean_object* v_declHint_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2255_, v_msg_2256_, v_declHint_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_);
lean_dec(v___y_2261_);
lean_dec_ref(v___y_2260_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v_ref_2255_);
return v_res_2263_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2269_ = l_Lean_stringToMessageData(v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2270_, lean_object* v_constName_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2277_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2278_ = 0;
lean_inc(v_constName_2271_);
v___x_2279_ = l_Lean_MessageData_ofConstName(v_constName_2271_, v___x_2278_);
v___x_2280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2280_, 0, v___x_2277_);
lean_ctor_set(v___x_2280_, 1, v___x_2279_);
v___x_2281_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2280_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2270_, v___x_2282_, v_constName_2271_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
return v___x_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2284_, lean_object* v_constName_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_){
_start:
{
lean_object* v_res_2291_; 
v_res_2291_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2284_, v_constName_2285_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec(v_ref_2284_);
return v_res_2291_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_ref_2298_; lean_object* v___x_2299_; 
v_ref_2298_ = lean_ctor_get(v___y_2295_, 2);
v___x_2299_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2298_, v_constName_2292_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
return v___x_2299_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
lean_object* v___x_2313_; lean_object* v_env_2314_; uint8_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2313_ = lean_st_ref_get(v___y_2311_);
v_env_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc_ref(v_env_2314_);
lean_dec(v___x_2313_);
v___x_2315_ = 0;
lean_inc(v_constName_2307_);
v___x_2316_ = l_Lean_Environment_findConstVal_x3f(v_env_2314_, v_constName_2307_, v___x_2315_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v___x_2317_; 
v___x_2317_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2307_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
return v___x_2317_;
}
else
{
lean_object* v_val_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_constName_2307_);
v_val_2318_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2316_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_val_2318_);
lean_dec(v___x_2316_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
lean_ctor_set_tag(v___x_2320_, 0);
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_val_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_){
_start:
{
lean_object* v_res_2332_; 
v_res_2332_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2326_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
lean_dec(v___y_2330_);
lean_dec_ref(v___y_2329_);
lean_dec(v___y_2328_);
lean_dec_ref(v___y_2327_);
return v_res_2332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2339_; 
lean_inc(v_constName_2333_);
v___x_2339_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2333_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v_levelParams_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v_levelParams_2341_ = lean_ctor_get(v_a_2340_, 1);
v___x_2342_ = lean_box(0);
lean_inc(v_levelParams_2341_);
v___x_2343_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2341_, v___x_2342_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc_n(v_a_2344_, 2);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2345_ = l_Lean_mkConst(v_constName_2333_, v_a_2344_);
v___x_2346_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2340_, v_a_2344_, v_a_2337_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2355_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2349_ = v___x_2346_;
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2346_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2355_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
v___x_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2345_);
lean_ctor_set(v___x_2351_, 1, v_a_2347_);
if (v_isShared_2350_ == 0)
{
lean_ctor_set(v___x_2349_, 0, v___x_2351_);
v___x_2353_ = v___x_2349_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_dec_ref(v___x_2345_);
v_a_2356_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2346_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2346_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_dec(v_a_2340_);
lean_dec(v_constName_2333_);
v_a_2364_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2343_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2343_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_constName_2333_);
v_a_2372_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2339_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2339_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_){
_start:
{
lean_object* v_res_2386_; 
v_res_2386_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
return v_res_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2387_, lean_object* v_constName_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; 
v___x_2394_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2394_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2395_, lean_object* v_constName_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2395_, v_constName_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2403_, lean_object* v_ref_2404_, lean_object* v_constName_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2404_, v_constName_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2412_, lean_object* v_ref_2413_, lean_object* v_constName_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2412_, v_ref_2413_, v_constName_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
lean_dec(v___y_2418_);
lean_dec_ref(v___y_2417_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v_ref_2413_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2421_, lean_object* v_ref_2422_, lean_object* v_msg_2423_, lean_object* v_declHint_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; 
v___x_2430_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2422_, v_msg_2423_, v_declHint_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2431_, lean_object* v_ref_2432_, lean_object* v_msg_2433_, lean_object* v_declHint_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v_res_2440_; 
v_res_2440_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2431_, v_ref_2432_, v_msg_2433_, v_declHint_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec_ref(v___y_2435_);
lean_dec(v_ref_2432_);
return v_res_2440_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2441_, lean_object* v_declHint_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_){
_start:
{
lean_object* v___x_2448_; 
v___x_2448_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2441_, v_declHint_2442_, v___y_2446_);
return v___x_2448_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2449_, lean_object* v_declHint_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_){
_start:
{
lean_object* v_res_2456_; 
v_res_2456_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2449_, v_declHint_2450_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
return v_res_2456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2457_, lean_object* v_ref_2458_, lean_object* v_msg_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2458_, v_msg_2459_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2465_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2466_, lean_object* v_ref_2467_, lean_object* v_msg_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_){
_start:
{
lean_object* v_res_2474_; 
v_res_2474_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2466_, v_ref_2467_, v_msg_2468_, v___y_2469_, v___y_2470_, v___y_2471_, v___y_2472_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v_ref_2467_);
return v_res_2474_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2476_; lean_object* v___x_2477_; 
v___x_2476_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2477_ = l_Lean_stringToMessageData(v___x_2476_);
return v___x_2477_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2480_ = l_Lean_stringToMessageData(v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2481_, lean_object* v_f_2482_, lean_object* v_inst_2483_, lean_object* v_xs_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2491_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2492_ = lean_apply_1(v_inst_2481_, v_f_2482_);
v___x_2493_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2491_);
lean_ctor_set(v___x_2493_, 1, v___x_2492_);
v___x_2494_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = lean_apply_1(v_inst_2483_, v_xs_2484_);
v___x_2497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2497_);
return v___x_2498_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2499_, lean_object* v_f_2500_, lean_object* v_inst_2501_, lean_object* v_xs_2502_, lean_object* v_x_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2499_, v_f_2500_, v_inst_2501_, v_xs_2502_, v_x_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec_ref(v_x_2503_);
return v_res_2509_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2510_; 
v___x_2510_ = l_instMonadEIO(lean_box(0));
return v___x_2510_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
v___x_2511_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2512_ = l_StateRefT_x27_instMonad___redArg(v___x_2511_);
return v___x_2512_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2520_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2521_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2520_, v___x_2519_);
return v___x_2521_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___f_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2523_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2524_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2523_, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2527_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2528_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2529_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2530_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2529_, v___x_2528_, v___x_2527_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___f_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; 
v___x_2531_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2532_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2533_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2534_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2533_, v___f_2532_, v___x_2531_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2535_; 
v___x_2535_ = l_instMonadExceptOfEIO(lean_box(0));
return v___x_2535_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2537_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2539_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2538_);
return v___x_2539_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2540_; lean_object* v___x_2541_; 
v___x_2540_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2541_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2540_);
return v___x_2541_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2542_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2543_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2542_);
return v___x_2543_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2555_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2556_ = l_Lean_Name_append(v___x_2555_, v___x_2554_);
return v___x_2556_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2562_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2563_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2564_ = l_Lean_Name_append(v___x_2563_, v___x_2562_);
return v___x_2564_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2565_; double v___x_2566_; 
v___x_2565_ = lean_unsigned_to_nat(1000000000u);
v___x_2566_ = lean_float_of_nat(v___x_2565_);
return v___x_2566_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2572_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2573_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2574_ = l_Lean_Name_append(v___x_2573_, v___x_2572_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2575_, lean_object* v_inst_2576_, lean_object* v_f_2577_, lean_object* v_xs_2578_, lean_object* v_k_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v___x_2585_; lean_object* v_toApplicative_2586_; lean_object* v_toFunctor_2587_; lean_object* v_toSeq_2588_; lean_object* v_toSeqLeft_2589_; lean_object* v_toSeqRight_2590_; lean_object* v___f_2591_; lean_object* v___f_2592_; lean_object* v___f_2593_; lean_object* v___f_2594_; lean_object* v___x_2595_; lean_object* v___f_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_toApplicative_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2841_; 
v___x_2585_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2586_ = lean_ctor_get(v___x_2585_, 0);
v_toFunctor_2587_ = lean_ctor_get(v_toApplicative_2586_, 0);
v_toSeq_2588_ = lean_ctor_get(v_toApplicative_2586_, 2);
v_toSeqLeft_2589_ = lean_ctor_get(v_toApplicative_2586_, 3);
v_toSeqRight_2590_ = lean_ctor_get(v_toApplicative_2586_, 4);
v___f_2591_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2592_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2587_, 2);
v___f_2593_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2593_, 0, v_toFunctor_2587_);
v___f_2594_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2594_, 0, v_toFunctor_2587_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___f_2593_);
lean_ctor_set(v___x_2595_, 1, v___f_2594_);
lean_inc(v_toSeqRight_2590_);
v___f_2596_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2596_, 0, v_toSeqRight_2590_);
lean_inc(v_toSeqLeft_2589_);
v___f_2597_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2597_, 0, v_toSeqLeft_2589_);
lean_inc(v_toSeq_2588_);
v___f_2598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2598_, 0, v_toSeq_2588_);
v___x_2599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2595_);
lean_ctor_set(v___x_2599_, 1, v___f_2591_);
lean_ctor_set(v___x_2599_, 2, v___f_2598_);
lean_ctor_set(v___x_2599_, 3, v___f_2597_);
lean_ctor_set(v___x_2599_, 4, v___f_2596_);
v___x_2600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2599_);
lean_ctor_set(v___x_2600_, 1, v___f_2592_);
v___x_2601_ = l_StateRefT_x27_instMonad___redArg(v___x_2600_);
v_toApplicative_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; 
v_unused_2842_ = lean_ctor_get(v___x_2601_, 1);
lean_dec(v_unused_2842_);
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2841_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_toApplicative_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2841_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_toFunctor_2606_; lean_object* v_toSeq_2607_; lean_object* v_toSeqLeft_2608_; lean_object* v_toSeqRight_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2839_; 
v_toFunctor_2606_ = lean_ctor_get(v_toApplicative_2602_, 0);
v_toSeq_2607_ = lean_ctor_get(v_toApplicative_2602_, 2);
v_toSeqLeft_2608_ = lean_ctor_get(v_toApplicative_2602_, 3);
v_toSeqRight_2609_ = lean_ctor_get(v_toApplicative_2602_, 4);
v_isSharedCheck_2839_ = !lean_is_exclusive(v_toApplicative_2602_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v_toApplicative_2602_, 1);
lean_dec(v_unused_2840_);
v___x_2611_ = v_toApplicative_2602_;
v_isShared_2612_ = v_isSharedCheck_2839_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_toSeqRight_2609_);
lean_inc(v_toSeqLeft_2608_);
lean_inc(v_toSeq_2607_);
lean_inc(v_toFunctor_2606_);
lean_dec(v_toApplicative_2602_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2839_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___f_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___x_2617_; lean_object* v___f_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___x_2622_; 
v___f_2613_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2614_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2606_);
v___f_2615_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2615_, 0, v_toFunctor_2606_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toFunctor_2606_);
v___x_2617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2617_, 0, v___f_2615_);
lean_ctor_set(v___x_2617_, 1, v___f_2616_);
v___f_2618_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2618_, 0, v_toSeqRight_2609_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toSeqLeft_2608_);
v___f_2620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2620_, 0, v_toSeq_2607_);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 4, v___f_2618_);
lean_ctor_set(v___x_2611_, 3, v___f_2619_);
lean_ctor_set(v___x_2611_, 2, v___f_2620_);
lean_ctor_set(v___x_2611_, 1, v___f_2613_);
lean_ctor_set(v___x_2611_, 0, v___x_2617_);
v___x_2622_ = v___x_2611_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2617_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v___f_2613_);
lean_ctor_set(v_reuseFailAlloc_2838_, 2, v___f_2620_);
lean_ctor_set(v_reuseFailAlloc_2838_, 3, v___f_2619_);
lean_ctor_set(v_reuseFailAlloc_2838_, 4, v___f_2618_);
v___x_2622_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
lean_object* v___x_2624_; 
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 1, v___f_2614_);
lean_ctor_set(v___x_2604_, 0, v___x_2622_);
v___x_2624_ = v___x_2604_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v___x_2622_);
lean_ctor_set(v_reuseFailAlloc_2837_, 1, v___f_2614_);
v___x_2624_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v_toMonadRef_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v_toCold_2630_; lean_object* v_options_2631_; uint8_t v_hasTrace_2632_; 
v___x_2625_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2627_ = lean_ctor_get(v___x_2626_, 0);
v___x_2628_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2629_ = l_Lean_KVMap_instValueBool;
v_toCold_2630_ = lean_ctor_get(v_a_2582_, 0);
v_options_2631_ = lean_ctor_get(v_toCold_2630_, 2);
v_hasTrace_2632_ = lean_ctor_get_uint8(v_options_2631_, sizeof(void*)*1);
if (v_hasTrace_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec_ref(v___x_2624_);
lean_dec(v_xs_2578_);
lean_dec(v_f_2577_);
lean_dec_ref(v_inst_2576_);
lean_dec_ref(v_inst_2575_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2633_ = lean_apply_5(v_k_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2633_) == 0)
{
return v___x_2633_;
}
else
{
lean_object* v_a_2634_; uint8_t v___y_2636_; uint8_t v___x_2645_; 
v_a_2634_ = lean_ctor_get(v___x_2633_, 0);
lean_inc(v_a_2634_);
v___x_2645_ = l_Lean_Exception_isInterrupt(v_a_2634_);
if (v___x_2645_ == 0)
{
uint8_t v___x_2646_; 
lean_inc(v_a_2634_);
v___x_2646_ = l_Lean_Exception_isRuntime(v_a_2634_);
v___y_2636_ = v___x_2646_;
goto v___jp_2635_;
}
else
{
v___y_2636_ = v___x_2645_;
goto v___jp_2635_;
}
v___jp_2635_:
{
if (v___y_2636_ == 0)
{
lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2633_);
if (v_isSharedCheck_2643_ == 0)
{
lean_object* v_unused_2644_; 
v_unused_2644_ = lean_ctor_get(v___x_2633_, 0);
lean_dec(v_unused_2644_);
v___x_2638_ = v___x_2633_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_dec(v___x_2633_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2634_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
else
{
lean_dec(v_a_2634_);
return v___x_2633_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2647_; lean_object* v___x_2648_; lean_object* v___y_2650_; lean_object* v___y_2651_; uint8_t v___y_2652_; lean_object* v___y_2677_; lean_object* v_a_2678_; lean_object* v___f_2681_; lean_object* v___f_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; lean_object* v___y_2688_; lean_object* v___y_2689_; lean_object* v_a_2690_; lean_object* v___y_2704_; lean_object* v___y_2705_; lean_object* v_a_2706_; lean_object* v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; uint8_t v___y_2712_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v_a_2723_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v_a_2729_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v_a_2734_; lean_object* v___y_2745_; lean_object* v___y_2746_; lean_object* v_a_2747_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; uint8_t v___y_2753_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v_a_2764_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v_a_2770_; 
v_inheritedTraceOptions_2647_ = lean_ctor_get(v_toCold_2630_, 11);
v___x_2648_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2681_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2681_, 0, v_inst_2575_);
lean_closure_set(v___f_2681_, 1, v_f_2577_);
lean_closure_set(v___f_2681_, 2, v_inst_2576_);
lean_closure_set(v___f_2681_, 3, v_xs_2578_);
v___f_2682_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2685_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2686_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2631_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2809_; lean_object* v___x_2810_; uint8_t v___x_2811_; 
v___x_2809_ = l_Lean_trace_profiler;
v___x_2810_ = l_Lean_Option_get___redArg(v___x_2629_, v_options_2631_, v___x_2809_);
v___x_2811_ = lean_unbox(v___x_2810_);
lean_dec(v___x_2810_);
if (v___x_2811_ == 0)
{
lean_object* v___x_2812_; 
lean_dec_ref(v___f_2681_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2812_ = lean_apply_5(v_k_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
v___x_2814_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2815_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2816_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2631_, v___x_2815_);
if (v___x_2816_ == 0)
{
lean_dec(v_a_2813_);
lean_dec_ref(v___x_2624_);
return v___x_2812_;
}
else
{
lean_object* v___x_2817_; lean_object* v___x_8920__overap_2818_; lean_object* v___x_2819_; 
lean_dec_ref_known(v___x_2812_, 1);
lean_inc(v_a_2813_);
v___x_2817_ = l_Lean_MessageData_ofExpr(v_a_2813_);
lean_inc_ref(v_toMonadRef_2627_);
lean_inc_ref(v___x_2624_);
v___x_8920__overap_2818_ = l_Lean_addTrace___redArg(v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, v___x_2814_, v___x_2817_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2819_ = lean_apply_5(v___x_8920__overap_2818_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2819_) == 0)
{
lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_dec_ref(v___x_2624_);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2826_ == 0)
{
lean_object* v_unused_2827_; 
v_unused_2827_ = lean_ctor_get(v___x_2819_, 0);
lean_dec(v_unused_2827_);
v___x_2821_ = v___x_2819_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_dec(v___x_2819_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
lean_ctor_set(v___x_2821_, 0, v_a_2813_);
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2813_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
else
{
lean_object* v_a_2828_; lean_object* v___x_2830_; uint8_t v_isShared_2831_; uint8_t v_isSharedCheck_2835_; 
lean_dec(v_a_2813_);
v_a_2828_ = lean_ctor_get(v___x_2819_, 0);
v_isSharedCheck_2835_ = !lean_is_exclusive(v___x_2819_);
if (v_isSharedCheck_2835_ == 0)
{
v___x_2830_ = v___x_2819_;
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
else
{
lean_inc(v_a_2828_);
lean_dec(v___x_2819_);
v___x_2830_ = lean_box(0);
v_isShared_2831_ = v_isSharedCheck_2835_;
goto v_resetjp_2829_;
}
v_resetjp_2829_:
{
lean_object* v___x_2833_; 
lean_inc(v_a_2828_);
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
v___y_2677_ = v___x_2833_;
v_a_2678_ = v_a_2828_;
goto v___jp_2676_;
}
}
}
}
}
else
{
lean_object* v_a_2836_; 
v_a_2836_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2836_);
v___y_2677_ = v___x_2812_;
v_a_2678_ = v_a_2836_;
goto v___jp_2676_;
}
}
else
{
goto v___jp_2772_;
}
}
else
{
goto v___jp_2772_;
}
v___jp_2649_:
{
if (v___y_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
lean_dec_ref(v___y_2650_);
v___x_2653_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2654_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2631_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref(v___x_2624_);
v___x_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2656_, 0, v___y_2651_);
return v___x_2656_;
}
else
{
lean_object* v___x_2657_; lean_object* v___x_8699__overap_2658_; lean_object* v___x_2659_; 
lean_inc_ref(v___y_2651_);
v___x_2657_ = l_Lean_Exception_toMessageData(v___y_2651_);
lean_inc_ref(v_toMonadRef_2627_);
v___x_8699__overap_2658_ = l_Lean_addTrace___redArg(v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, v___x_2653_, v___x_2657_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2659_ = lean_apply_5(v___x_8699__overap_2658_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2659_, 0);
lean_dec(v_unused_2667_);
v___x_2661_ = v___x_2659_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2659_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
lean_ctor_set_tag(v___x_2661_, 1);
lean_ctor_set(v___x_2661_, 0, v___y_2651_);
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v___y_2651_);
v___x_2664_ = v_reuseFailAlloc_2665_;
goto v_reusejp_2663_;
}
v_reusejp_2663_:
{
return v___x_2664_;
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v___y_2651_);
v_a_2668_ = lean_ctor_get(v___x_2659_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2659_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2659_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2651_);
lean_dec_ref(v___x_2624_);
return v___y_2650_;
}
}
v___jp_2676_:
{
uint8_t v___x_2679_; 
v___x_2679_ = l_Lean_Exception_isInterrupt(v_a_2678_);
if (v___x_2679_ == 0)
{
uint8_t v___x_2680_; 
lean_inc_ref(v_a_2678_);
v___x_2680_ = l_Lean_Exception_isRuntime(v_a_2678_);
v___y_2650_ = v___y_2677_;
v___y_2651_ = v_a_2678_;
v___y_2652_ = v___x_2680_;
goto v___jp_2649_;
}
else
{
v___y_2650_ = v___y_2677_;
v___y_2651_ = v_a_2678_;
v___y_2652_ = v___x_2679_;
goto v___jp_2649_;
}
}
v___jp_2687_:
{
lean_object* v___x_2691_; double v___x_2692_; double v___x_2693_; double v___x_2694_; double v___x_2695_; double v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_8797__overap_2701_; lean_object* v___x_2702_; 
v___x_2691_ = lean_io_mono_nanos_now();
v___x_2692_ = lean_float_of_nat(v___y_2688_);
v___x_2693_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2694_ = lean_float_div(v___x_2692_, v___x_2693_);
v___x_2695_ = lean_float_of_nat(v___x_2691_);
v___x_2696_ = lean_float_div(v___x_2695_, v___x_2693_);
v___x_2697_ = lean_box_float(v___x_2694_);
v___x_2698_ = lean_box_float(v___x_2696_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_a_2690_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
lean_inc_ref(v_toMonadRef_2627_);
v___x_8797__overap_2701_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, lean_box(0), v___x_2628_, v___f_2682_, v___x_2683_, v_hasTrace_2632_, v___x_2684_, v_options_2631_, v___x_2686_, v___y_2689_, v___f_2681_, v___x_2700_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2702_ = lean_apply_5(v___x_8797__overap_2701_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
return v___x_2702_;
}
v___jp_2703_:
{
lean_object* v___x_2707_; 
v___x_2707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2707_, 0, v_a_2706_);
v___y_2688_ = v___y_2704_;
v___y_2689_ = v___y_2705_;
v_a_2690_ = v___x_2707_;
goto v___jp_2687_;
}
v___jp_2708_:
{
if (v___y_2712_ == 0)
{
lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2714_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2715_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2631_, v___x_2714_);
if (v___x_2715_ == 0)
{
v___y_2704_ = v___y_2709_;
v___y_2705_ = v___y_2711_;
v_a_2706_ = v___y_2710_;
goto v___jp_2703_;
}
else
{
lean_object* v___x_2716_; lean_object* v___x_8815__overap_2717_; lean_object* v___x_2718_; 
lean_inc_ref(v___y_2710_);
v___x_2716_ = l_Lean_Exception_toMessageData(v___y_2710_);
lean_inc_ref(v_toMonadRef_2627_);
lean_inc_ref(v___x_2624_);
v___x_8815__overap_2717_ = l_Lean_addTrace___redArg(v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, v___x_2713_, v___x_2716_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2718_ = lean_apply_5(v___x_8815__overap_2717_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2718_) == 0)
{
lean_dec_ref_known(v___x_2718_, 1);
v___y_2704_ = v___y_2709_;
v___y_2705_ = v___y_2711_;
v_a_2706_ = v___y_2710_;
goto v___jp_2703_;
}
else
{
lean_object* v_a_2719_; 
lean_dec_ref(v___y_2710_);
v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
lean_inc(v_a_2719_);
lean_dec_ref_known(v___x_2718_, 1);
v___y_2704_ = v___y_2709_;
v___y_2705_ = v___y_2711_;
v_a_2706_ = v_a_2719_;
goto v___jp_2703_;
}
}
}
else
{
v___y_2704_ = v___y_2709_;
v___y_2705_ = v___y_2711_;
v_a_2706_ = v___y_2710_;
goto v___jp_2703_;
}
}
v___jp_2720_:
{
uint8_t v___x_2724_; 
v___x_2724_ = l_Lean_Exception_isInterrupt(v_a_2723_);
if (v___x_2724_ == 0)
{
uint8_t v___x_2725_; 
lean_inc_ref(v_a_2723_);
v___x_2725_ = l_Lean_Exception_isRuntime(v_a_2723_);
v___y_2709_ = v___y_2721_;
v___y_2710_ = v_a_2723_;
v___y_2711_ = v___y_2722_;
v___y_2712_ = v___x_2725_;
goto v___jp_2708_;
}
else
{
v___y_2709_ = v___y_2721_;
v___y_2710_ = v_a_2723_;
v___y_2711_ = v___y_2722_;
v___y_2712_ = v___x_2724_;
goto v___jp_2708_;
}
}
v___jp_2726_:
{
lean_object* v___x_2730_; 
v___x_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2729_);
v___y_2688_ = v___y_2727_;
v___y_2689_ = v___y_2728_;
v_a_2690_ = v___x_2730_;
goto v___jp_2687_;
}
v___jp_2731_:
{
lean_object* v___x_2735_; double v___x_2736_; double v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_8857__overap_2742_; lean_object* v___x_2743_; 
v___x_2735_ = lean_io_get_num_heartbeats();
v___x_2736_ = lean_float_of_nat(v___y_2732_);
v___x_2737_ = lean_float_of_nat(v___x_2735_);
v___x_2738_ = lean_box_float(v___x_2736_);
v___x_2739_ = lean_box_float(v___x_2737_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2738_);
lean_ctor_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v_a_2734_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
lean_inc_ref(v_toMonadRef_2627_);
v___x_8857__overap_2742_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, lean_box(0), v___x_2628_, v___f_2682_, v___x_2683_, v_hasTrace_2632_, v___x_2684_, v_options_2631_, v___x_2686_, v___y_2733_, v___f_2681_, v___x_2741_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2743_ = lean_apply_5(v___x_8857__overap_2742_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
return v___x_2743_;
}
v___jp_2744_:
{
lean_object* v___x_2748_; 
v___x_2748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2748_, 0, v_a_2747_);
v___y_2732_ = v___y_2745_;
v___y_2733_ = v___y_2746_;
v_a_2734_ = v___x_2748_;
goto v___jp_2731_;
}
v___jp_2749_:
{
if (v___y_2753_ == 0)
{
lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2754_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2755_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2756_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2631_, v___x_2755_);
if (v___x_2756_ == 0)
{
v___y_2745_ = v___y_2750_;
v___y_2746_ = v___y_2752_;
v_a_2747_ = v___y_2751_;
goto v___jp_2744_;
}
else
{
lean_object* v___x_2757_; lean_object* v___x_8875__overap_2758_; lean_object* v___x_2759_; 
lean_inc_ref(v___y_2751_);
v___x_2757_ = l_Lean_Exception_toMessageData(v___y_2751_);
lean_inc_ref(v_toMonadRef_2627_);
lean_inc_ref(v___x_2624_);
v___x_8875__overap_2758_ = l_Lean_addTrace___redArg(v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, v___x_2754_, v___x_2757_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2759_ = lean_apply_5(v___x_8875__overap_2758_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_dec_ref_known(v___x_2759_, 1);
v___y_2745_ = v___y_2750_;
v___y_2746_ = v___y_2752_;
v_a_2747_ = v___y_2751_;
goto v___jp_2744_;
}
else
{
lean_object* v_a_2760_; 
lean_dec_ref(v___y_2751_);
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_a_2760_);
lean_dec_ref_known(v___x_2759_, 1);
v___y_2745_ = v___y_2750_;
v___y_2746_ = v___y_2752_;
v_a_2747_ = v_a_2760_;
goto v___jp_2744_;
}
}
}
else
{
v___y_2745_ = v___y_2750_;
v___y_2746_ = v___y_2752_;
v_a_2747_ = v___y_2751_;
goto v___jp_2744_;
}
}
v___jp_2761_:
{
uint8_t v___x_2765_; 
v___x_2765_ = l_Lean_Exception_isInterrupt(v_a_2764_);
if (v___x_2765_ == 0)
{
uint8_t v___x_2766_; 
lean_inc_ref(v_a_2764_);
v___x_2766_ = l_Lean_Exception_isRuntime(v_a_2764_);
v___y_2750_ = v___y_2762_;
v___y_2751_ = v_a_2764_;
v___y_2752_ = v___y_2763_;
v___y_2753_ = v___x_2766_;
goto v___jp_2749_;
}
else
{
v___y_2750_ = v___y_2762_;
v___y_2751_ = v_a_2764_;
v___y_2752_ = v___y_2763_;
v___y_2753_ = v___x_2765_;
goto v___jp_2749_;
}
}
v___jp_2767_:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2770_);
v___y_2732_ = v___y_2768_;
v___y_2733_ = v___y_2769_;
v_a_2734_ = v___x_2771_;
goto v___jp_2731_;
}
v___jp_2772_:
{
lean_object* v___x_8775__overap_2773_; lean_object* v___x_2774_; 
lean_inc_ref(v___x_2624_);
v___x_8775__overap_2773_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2624_, v___x_2625_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2774_ = lean_apply_5(v___x_8775__overap_2773_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2777_ = l_Lean_Option_get___redArg(v___x_2629_, v_options_2631_, v___x_2776_);
v___x_2778_ = lean_unbox(v___x_2777_);
lean_dec(v___x_2777_);
if (v___x_2778_ == 0)
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = lean_io_mono_nanos_now();
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2780_ = lean_apply_5(v_k_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; uint8_t v___x_2784_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2783_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2784_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2631_, v___x_2783_);
if (v___x_2784_ == 0)
{
v___y_2727_ = v___x_2779_;
v___y_2728_ = v_a_2775_;
v_a_2729_ = v_a_2781_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2785_; lean_object* v___x_8837__overap_2786_; lean_object* v___x_2787_; 
lean_inc(v_a_2781_);
v___x_2785_ = l_Lean_MessageData_ofExpr(v_a_2781_);
lean_inc_ref(v_toMonadRef_2627_);
lean_inc_ref(v___x_2624_);
v___x_8837__overap_2786_ = l_Lean_addTrace___redArg(v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, v___x_2782_, v___x_2785_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2787_ = lean_apply_5(v___x_8837__overap_2786_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_dec_ref_known(v___x_2787_, 1);
v___y_2727_ = v___x_2779_;
v___y_2728_ = v_a_2775_;
v_a_2729_ = v_a_2781_;
goto v___jp_2726_;
}
else
{
lean_object* v_a_2788_; 
lean_dec(v_a_2781_);
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v___y_2721_ = v___x_2779_;
v___y_2722_ = v_a_2775_;
v_a_2723_ = v_a_2788_;
goto v___jp_2720_;
}
}
}
else
{
lean_object* v_a_2789_; 
v_a_2789_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2780_, 1);
v___y_2721_ = v___x_2779_;
v___y_2722_ = v_a_2775_;
v_a_2723_ = v_a_2789_;
goto v___jp_2720_;
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2791_ = lean_apply_5(v_k_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; uint8_t v___x_2795_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v___x_2791_, 1);
v___x_2793_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2794_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2795_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2647_, v_options_2631_, v___x_2794_);
if (v___x_2795_ == 0)
{
v___y_2768_ = v___x_2790_;
v___y_2769_ = v_a_2775_;
v_a_2770_ = v_a_2792_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2796_; lean_object* v___x_8897__overap_2797_; lean_object* v___x_2798_; 
lean_inc(v_a_2792_);
v___x_2796_ = l_Lean_MessageData_ofExpr(v_a_2792_);
lean_inc_ref(v_toMonadRef_2627_);
lean_inc_ref(v___x_2624_);
v___x_8897__overap_2797_ = l_Lean_addTrace___redArg(v___x_2624_, v___x_2625_, v_toMonadRef_2627_, v___x_2648_, v___x_2793_, v___x_2796_);
lean_inc(v_a_2583_);
lean_inc_ref(v_a_2582_);
lean_inc(v_a_2581_);
lean_inc_ref(v_a_2580_);
v___x_2798_ = lean_apply_5(v___x_8897__overap_2797_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, lean_box(0));
if (lean_obj_tag(v___x_2798_) == 0)
{
lean_dec_ref_known(v___x_2798_, 1);
v___y_2768_ = v___x_2790_;
v___y_2769_ = v_a_2775_;
v_a_2770_ = v_a_2792_;
goto v___jp_2767_;
}
else
{
lean_object* v_a_2799_; 
lean_dec(v_a_2792_);
v_a_2799_ = lean_ctor_get(v___x_2798_, 0);
lean_inc(v_a_2799_);
lean_dec_ref_known(v___x_2798_, 1);
v___y_2762_ = v___x_2790_;
v___y_2763_ = v_a_2775_;
v_a_2764_ = v_a_2799_;
goto v___jp_2761_;
}
}
}
else
{
lean_object* v_a_2800_; 
v_a_2800_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2791_, 1);
v___y_2762_ = v___x_2790_;
v___y_2763_ = v_a_2775_;
v_a_2764_ = v_a_2800_;
goto v___jp_2761_;
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec_ref(v___f_2681_);
lean_dec_ref(v___x_2624_);
lean_dec_ref(v_k_2579_);
v_a_2801_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2774_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2774_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2843_, lean_object* v_inst_2844_, lean_object* v_f_2845_, lean_object* v_xs_2846_, lean_object* v_k_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2843_, v_inst_2844_, v_f_2845_, v_xs_2846_, v_k_2847_, v_a_2848_, v_a_2849_, v_a_2850_, v_a_2851_);
lean_dec(v_a_2851_);
lean_dec_ref(v_a_2850_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2854_, lean_object* v_00_u03b2_2855_, lean_object* v_inst_2856_, lean_object* v_inst_2857_, lean_object* v_f_2858_, lean_object* v_xs_2859_, lean_object* v_k_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_){
_start:
{
lean_object* v___x_2866_; 
v___x_2866_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2856_, v_inst_2857_, v_f_2858_, v_xs_2859_, v_k_2860_, v_a_2861_, v_a_2862_, v_a_2863_, v_a_2864_);
return v___x_2866_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2867_, lean_object* v_00_u03b2_2868_, lean_object* v_inst_2869_, lean_object* v_inst_2870_, lean_object* v_f_2871_, lean_object* v_xs_2872_, lean_object* v_k_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2867_, v_00_u03b2_2868_, v_inst_2869_, v_inst_2870_, v_f_2871_, v_xs_2872_, v_k_2873_, v_a_2874_, v_a_2875_, v_a_2876_, v_a_2877_);
lean_dec(v_a_2877_);
lean_dec_ref(v_a_2876_);
lean_dec(v_a_2875_);
lean_dec_ref(v_a_2874_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2880_, uint8_t v_allowLevelAssignments_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_){
_start:
{
lean_object* v___x_2887_; 
v___x_2887_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2881_, v_k_2880_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2887_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2887_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
v_a_2896_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2887_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2887_);
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
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2904_, lean_object* v_allowLevelAssignments_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2911_; lean_object* v_res_2912_; 
v_allowLevelAssignments_boxed_2911_ = lean_unbox(v_allowLevelAssignments_2905_);
v_res_2912_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2904_, v_allowLevelAssignments_boxed_2911_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec_ref(v___y_2906_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2913_, lean_object* v_k_2914_, uint8_t v_allowLevelAssignments_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v___x_2921_; 
v___x_2921_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2914_, v_allowLevelAssignments_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_);
return v___x_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2922_, lean_object* v_k_2923_, lean_object* v_allowLevelAssignments_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2930_; lean_object* v_res_2931_; 
v_allowLevelAssignments_boxed_2930_ = lean_unbox(v_allowLevelAssignments_2924_);
v_res_2931_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2922_, v_k_2923_, v_allowLevelAssignments_boxed_2930_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
lean_dec(v___y_2928_);
lean_dec_ref(v___y_2927_);
lean_dec(v___y_2926_);
lean_dec_ref(v___y_2925_);
return v_res_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2932_, lean_object* v_xs_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_){
_start:
{
lean_object* v___x_2939_; 
v___x_2939_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2932_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
if (lean_obj_tag(v___x_2939_) == 0)
{
lean_object* v_a_2940_; lean_object* v_fst_2941_; lean_object* v_snd_2942_; lean_object* v___x_2943_; 
v_a_2940_ = lean_ctor_get(v___x_2939_, 0);
lean_inc(v_a_2940_);
lean_dec_ref_known(v___x_2939_, 1);
v_fst_2941_ = lean_ctor_get(v_a_2940_, 0);
lean_inc(v_fst_2941_);
v_snd_2942_ = lean_ctor_get(v_a_2940_, 1);
lean_inc(v_snd_2942_);
lean_dec(v_a_2940_);
v___x_2943_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2941_, v_snd_2942_, v_xs_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
return v___x_2943_;
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
v_a_2944_ = lean_ctor_get(v___x_2939_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2939_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2939_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2939_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2952_, lean_object* v_xs_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2952_, v_xs_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
lean_dec(v___y_2957_);
lean_dec_ref(v___y_2956_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec_ref(v_xs_2953_);
return v_res_2959_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v___x_2960_ = lean_unsigned_to_nat(32u);
v___x_2961_ = lean_mk_empty_array_with_capacity(v___x_2960_);
v___x_2962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
return v___x_2962_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2963_ = ((size_t)5ULL);
v___x_2964_ = lean_unsigned_to_nat(0u);
v___x_2965_ = lean_unsigned_to_nat(32u);
v___x_2966_ = lean_mk_empty_array_with_capacity(v___x_2965_);
v___x_2967_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2968_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
lean_ctor_set(v___x_2968_, 1, v___x_2966_);
lean_ctor_set(v___x_2968_, 2, v___x_2964_);
lean_ctor_set(v___x_2968_, 3, v___x_2964_);
lean_ctor_set_usize(v___x_2968_, 4, v___x_2963_);
return v___x_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2969_){
_start:
{
lean_object* v___x_2971_; lean_object* v_traceState_2972_; lean_object* v_traces_2973_; lean_object* v___x_2974_; lean_object* v_traceState_2975_; lean_object* v_env_2976_; lean_object* v_nextMacroScope_2977_; lean_object* v_ngen_2978_; lean_object* v_auxDeclNGen_2979_; lean_object* v_cache_2980_; lean_object* v_messages_2981_; lean_object* v_infoState_2982_; lean_object* v_snapshotTasks_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_3002_; 
v___x_2971_ = lean_st_ref_get(v___y_2969_);
v_traceState_2972_ = lean_ctor_get(v___x_2971_, 4);
lean_inc_ref(v_traceState_2972_);
lean_dec(v___x_2971_);
v_traces_2973_ = lean_ctor_get(v_traceState_2972_, 0);
lean_inc_ref(v_traces_2973_);
lean_dec_ref(v_traceState_2972_);
v___x_2974_ = lean_st_ref_take(v___y_2969_);
v_traceState_2975_ = lean_ctor_get(v___x_2974_, 4);
v_env_2976_ = lean_ctor_get(v___x_2974_, 0);
v_nextMacroScope_2977_ = lean_ctor_get(v___x_2974_, 1);
v_ngen_2978_ = lean_ctor_get(v___x_2974_, 2);
v_auxDeclNGen_2979_ = lean_ctor_get(v___x_2974_, 3);
v_cache_2980_ = lean_ctor_get(v___x_2974_, 5);
v_messages_2981_ = lean_ctor_get(v___x_2974_, 6);
v_infoState_2982_ = lean_ctor_get(v___x_2974_, 7);
v_snapshotTasks_2983_ = lean_ctor_get(v___x_2974_, 8);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2985_ = v___x_2974_;
v_isShared_2986_ = v_isSharedCheck_3002_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_snapshotTasks_2983_);
lean_inc(v_infoState_2982_);
lean_inc(v_messages_2981_);
lean_inc(v_cache_2980_);
lean_inc(v_traceState_2975_);
lean_inc(v_auxDeclNGen_2979_);
lean_inc(v_ngen_2978_);
lean_inc(v_nextMacroScope_2977_);
lean_inc(v_env_2976_);
lean_dec(v___x_2974_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_3002_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
uint64_t v_tid_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_3000_; 
v_tid_2987_ = lean_ctor_get_uint64(v_traceState_2975_, sizeof(void*)*1);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_traceState_2975_);
if (v_isSharedCheck_3000_ == 0)
{
lean_object* v_unused_3001_; 
v_unused_3001_ = lean_ctor_get(v_traceState_2975_, 0);
lean_dec(v_unused_3001_);
v___x_2989_ = v_traceState_2975_;
v_isShared_2990_ = v_isSharedCheck_3000_;
goto v_resetjp_2988_;
}
else
{
lean_dec(v_traceState_2975_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_3000_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
v___x_2991_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_2990_ == 0)
{
lean_ctor_set(v___x_2989_, 0, v___x_2991_);
v___x_2993_ = v___x_2989_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v___x_2991_);
lean_ctor_set_uint64(v_reuseFailAlloc_2999_, sizeof(void*)*1, v_tid_2987_);
v___x_2993_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 4, v___x_2993_);
v___x_2995_ = v___x_2985_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_env_2976_);
lean_ctor_set(v_reuseFailAlloc_2998_, 1, v_nextMacroScope_2977_);
lean_ctor_set(v_reuseFailAlloc_2998_, 2, v_ngen_2978_);
lean_ctor_set(v_reuseFailAlloc_2998_, 3, v_auxDeclNGen_2979_);
lean_ctor_set(v_reuseFailAlloc_2998_, 4, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2998_, 5, v_cache_2980_);
lean_ctor_set(v_reuseFailAlloc_2998_, 6, v_messages_2981_);
lean_ctor_set(v_reuseFailAlloc_2998_, 7, v_infoState_2982_);
lean_ctor_set(v_reuseFailAlloc_2998_, 8, v_snapshotTasks_2983_);
v___x_2995_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2996_ = lean_st_ref_put(v___y_2969_, v___x_2995_);
v___x_2997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2997_, 0, v_traces_2973_);
return v___x_2997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3003_, lean_object* v___y_3004_){
_start:
{
lean_object* v_res_3005_; 
v_res_3005_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3003_);
lean_dec(v___y_3003_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3006_, lean_object* v_opt_3007_){
_start:
{
lean_object* v_name_3008_; lean_object* v_defValue_3009_; lean_object* v_map_3010_; lean_object* v___x_3011_; 
v_name_3008_ = lean_ctor_get(v_opt_3007_, 0);
v_defValue_3009_ = lean_ctor_get(v_opt_3007_, 1);
v_map_3010_ = lean_ctor_get(v_opts_3006_, 0);
v___x_3011_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3010_, v_name_3008_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_inc(v_defValue_3009_);
return v_defValue_3009_;
}
else
{
lean_object* v_val_3012_; 
v_val_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_val_3012_);
lean_dec_ref_known(v___x_3011_, 1);
if (lean_obj_tag(v_val_3012_) == 3)
{
lean_object* v_v_3013_; 
v_v_3013_ = lean_ctor_get(v_val_3012_, 0);
lean_inc(v_v_3013_);
lean_dec_ref_known(v_val_3012_, 1);
return v_v_3013_;
}
else
{
lean_dec(v_val_3012_);
lean_inc(v_defValue_3009_);
return v_defValue_3009_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3014_, lean_object* v_opt_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3014_, v_opt_3015_);
lean_dec_ref(v_opt_3015_);
lean_dec_ref(v_opts_3014_);
return v_res_3016_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3017_, lean_object* v_opt_3018_){
_start:
{
lean_object* v_name_3019_; lean_object* v_defValue_3020_; lean_object* v_map_3021_; lean_object* v___x_3022_; 
v_name_3019_ = lean_ctor_get(v_opt_3018_, 0);
v_defValue_3020_ = lean_ctor_get(v_opt_3018_, 1);
v_map_3021_ = lean_ctor_get(v_opts_3017_, 0);
v___x_3022_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3021_, v_name_3019_);
if (lean_obj_tag(v___x_3022_) == 0)
{
uint8_t v___x_3023_; 
v___x_3023_ = lean_unbox(v_defValue_3020_);
return v___x_3023_;
}
else
{
lean_object* v_val_3024_; 
v_val_3024_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_val_3024_);
lean_dec_ref_known(v___x_3022_, 1);
if (lean_obj_tag(v_val_3024_) == 1)
{
uint8_t v_v_3025_; 
v_v_3025_ = lean_ctor_get_uint8(v_val_3024_, 0);
lean_dec_ref_known(v_val_3024_, 0);
return v_v_3025_;
}
else
{
uint8_t v___x_3026_; 
lean_dec(v_val_3024_);
v___x_3026_ = lean_unbox(v_defValue_3020_);
return v___x_3026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3027_, lean_object* v_opt_3028_){
_start:
{
uint8_t v_res_3029_; lean_object* v_r_3030_; 
v_res_3029_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3027_, v_opt_3028_);
lean_dec_ref(v_opt_3028_);
lean_dec_ref(v_opts_3027_);
v_r_3030_ = lean_box(v_res_3029_);
return v_r_3030_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3031_){
_start:
{
if (lean_obj_tag(v_e_3031_) == 0)
{
uint8_t v___x_3032_; 
v___x_3032_ = 2;
return v___x_3032_;
}
else
{
lean_object* v_a_3033_; uint8_t v___x_3034_; 
v_a_3033_ = lean_ctor_get(v_e_3031_, 0);
v___x_3034_ = l_Lean_Expr_hasSyntheticSorry(v_a_3033_);
if (v___x_3034_ == 0)
{
uint8_t v___x_3035_; 
v___x_3035_ = 0;
return v___x_3035_;
}
else
{
uint8_t v___x_3036_; 
v___x_3036_ = 1;
return v___x_3036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3037_){
_start:
{
uint8_t v_res_3038_; lean_object* v_r_3039_; 
v_res_3038_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3037_);
lean_dec_ref(v_e_3037_);
v_r_3039_ = lean_box(v_res_3038_);
return v_r_3039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3040_, size_t v_i_3041_, lean_object* v_bs_3042_){
_start:
{
uint8_t v___x_3043_; 
v___x_3043_ = lean_usize_dec_lt(v_i_3041_, v_sz_3040_);
if (v___x_3043_ == 0)
{
return v_bs_3042_;
}
else
{
lean_object* v_v_3044_; lean_object* v_msg_3045_; lean_object* v___x_3046_; lean_object* v_bs_x27_3047_; size_t v___x_3048_; size_t v___x_3049_; lean_object* v___x_3050_; 
v_v_3044_ = lean_array_uget_borrowed(v_bs_3042_, v_i_3041_);
v_msg_3045_ = lean_ctor_get(v_v_3044_, 1);
lean_inc_ref(v_msg_3045_);
v___x_3046_ = lean_unsigned_to_nat(0u);
v_bs_x27_3047_ = lean_array_uset(v_bs_3042_, v_i_3041_, v___x_3046_);
v___x_3048_ = ((size_t)1ULL);
v___x_3049_ = lean_usize_add(v_i_3041_, v___x_3048_);
v___x_3050_ = lean_array_uset(v_bs_x27_3047_, v_i_3041_, v_msg_3045_);
v_i_3041_ = v___x_3049_;
v_bs_3042_ = v___x_3050_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3052_, lean_object* v_i_3053_, lean_object* v_bs_3054_){
_start:
{
size_t v_sz_boxed_3055_; size_t v_i_boxed_3056_; lean_object* v_res_3057_; 
v_sz_boxed_3055_ = lean_unbox_usize(v_sz_3052_);
lean_dec(v_sz_3052_);
v_i_boxed_3056_ = lean_unbox_usize(v_i_3053_);
lean_dec(v_i_3053_);
v_res_3057_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3055_, v_i_boxed_3056_, v_bs_3054_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3058_, lean_object* v_data_3059_, lean_object* v_ref_3060_, lean_object* v_msg_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v_toCold_3067_; lean_object* v_currRecDepth_3068_; lean_object* v_ref_3069_; uint8_t v_diag_3070_; uint8_t v_suppressElabErrors_3071_; lean_object* v___x_3072_; lean_object* v_traceState_3073_; lean_object* v_traces_3074_; lean_object* v_ref_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; size_t v_sz_3078_; size_t v___x_3079_; lean_object* v___x_3080_; lean_object* v_msg_3081_; lean_object* v___x_3082_; lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3120_; 
v_toCold_3067_ = lean_ctor_get(v___y_3064_, 0);
v_currRecDepth_3068_ = lean_ctor_get(v___y_3064_, 1);
v_ref_3069_ = lean_ctor_get(v___y_3064_, 2);
v_diag_3070_ = lean_ctor_get_uint8(v___y_3064_, sizeof(void*)*3);
v_suppressElabErrors_3071_ = lean_ctor_get_uint8(v___y_3064_, sizeof(void*)*3 + 1);
v___x_3072_ = lean_st_ref_get(v___y_3065_);
v_traceState_3073_ = lean_ctor_get(v___x_3072_, 4);
lean_inc_ref(v_traceState_3073_);
lean_dec(v___x_3072_);
v_traces_3074_ = lean_ctor_get(v_traceState_3073_, 0);
lean_inc_ref(v_traces_3074_);
lean_dec_ref(v_traceState_3073_);
v_ref_3075_ = l_Lean_replaceRef(v_ref_3060_, v_ref_3069_);
lean_inc(v_currRecDepth_3068_);
lean_inc_ref(v_toCold_3067_);
v___x_3076_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3076_, 0, v_toCold_3067_);
lean_ctor_set(v___x_3076_, 1, v_currRecDepth_3068_);
lean_ctor_set(v___x_3076_, 2, v_ref_3075_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*3, v_diag_3070_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*3 + 1, v_suppressElabErrors_3071_);
v___x_3077_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3074_);
lean_dec_ref(v_traces_3074_);
v_sz_3078_ = lean_array_size(v___x_3077_);
v___x_3079_ = ((size_t)0ULL);
v___x_3080_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3078_, v___x_3079_, v___x_3077_);
v_msg_3081_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3081_, 0, v_data_3059_);
lean_ctor_set(v_msg_3081_, 1, v_msg_3061_);
lean_ctor_set(v_msg_3081_, 2, v___x_3080_);
v___x_3082_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3081_, v___y_3062_, v___y_3063_, v___x_3076_, v___y_3065_);
lean_dec_ref_known(v___x_3076_, 3);
v_a_3083_ = lean_ctor_get(v___x_3082_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3082_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3085_ = v___x_3082_;
v_isShared_3086_ = v_isSharedCheck_3120_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3082_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3120_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v_traceState_3088_; lean_object* v_env_3089_; lean_object* v_nextMacroScope_3090_; lean_object* v_ngen_3091_; lean_object* v_auxDeclNGen_3092_; lean_object* v_cache_3093_; lean_object* v_messages_3094_; lean_object* v_infoState_3095_; lean_object* v_snapshotTasks_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3119_; 
v___x_3087_ = lean_st_ref_take(v___y_3065_);
v_traceState_3088_ = lean_ctor_get(v___x_3087_, 4);
v_env_3089_ = lean_ctor_get(v___x_3087_, 0);
v_nextMacroScope_3090_ = lean_ctor_get(v___x_3087_, 1);
v_ngen_3091_ = lean_ctor_get(v___x_3087_, 2);
v_auxDeclNGen_3092_ = lean_ctor_get(v___x_3087_, 3);
v_cache_3093_ = lean_ctor_get(v___x_3087_, 5);
v_messages_3094_ = lean_ctor_get(v___x_3087_, 6);
v_infoState_3095_ = lean_ctor_get(v___x_3087_, 7);
v_snapshotTasks_3096_ = lean_ctor_get(v___x_3087_, 8);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3087_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3098_ = v___x_3087_;
v_isShared_3099_ = v_isSharedCheck_3119_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_snapshotTasks_3096_);
lean_inc(v_infoState_3095_);
lean_inc(v_messages_3094_);
lean_inc(v_cache_3093_);
lean_inc(v_traceState_3088_);
lean_inc(v_auxDeclNGen_3092_);
lean_inc(v_ngen_3091_);
lean_inc(v_nextMacroScope_3090_);
lean_inc(v_env_3089_);
lean_dec(v___x_3087_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3119_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
uint64_t v_tid_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3117_; 
v_tid_3100_ = lean_ctor_get_uint64(v_traceState_3088_, sizeof(void*)*1);
v_isSharedCheck_3117_ = !lean_is_exclusive(v_traceState_3088_);
if (v_isSharedCheck_3117_ == 0)
{
lean_object* v_unused_3118_; 
v_unused_3118_ = lean_ctor_get(v_traceState_3088_, 0);
lean_dec(v_unused_3118_);
v___x_3102_ = v_traceState_3088_;
v_isShared_3103_ = v_isSharedCheck_3117_;
goto v_resetjp_3101_;
}
else
{
lean_dec(v_traceState_3088_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3117_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3107_; 
v___x_3104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3104_, 0, v_ref_3060_);
lean_ctor_set(v___x_3104_, 1, v_a_3083_);
v___x_3105_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3058_, v___x_3104_);
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 0, v___x_3105_);
v___x_3107_ = v___x_3102_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v___x_3105_);
lean_ctor_set_uint64(v_reuseFailAlloc_3116_, sizeof(void*)*1, v_tid_3100_);
v___x_3107_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
lean_object* v___x_3109_; 
if (v_isShared_3099_ == 0)
{
lean_ctor_set(v___x_3098_, 4, v___x_3107_);
v___x_3109_ = v___x_3098_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_env_3089_);
lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_nextMacroScope_3090_);
lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_ngen_3091_);
lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_auxDeclNGen_3092_);
lean_ctor_set(v_reuseFailAlloc_3115_, 4, v___x_3107_);
lean_ctor_set(v_reuseFailAlloc_3115_, 5, v_cache_3093_);
lean_ctor_set(v_reuseFailAlloc_3115_, 6, v_messages_3094_);
lean_ctor_set(v_reuseFailAlloc_3115_, 7, v_infoState_3095_);
lean_ctor_set(v_reuseFailAlloc_3115_, 8, v_snapshotTasks_3096_);
v___x_3109_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3110_ = lean_st_ref_put(v___y_3065_, v___x_3109_);
v___x_3111_ = lean_box(0);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3111_);
v___x_3113_ = v___x_3085_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3121_, lean_object* v_data_3122_, lean_object* v_ref_3123_, lean_object* v_msg_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3121_, v_data_3122_, v_ref_3123_, v_msg_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3131_){
_start:
{
if (lean_obj_tag(v_x_3131_) == 0)
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3133_ = lean_ctor_get(v_x_3131_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_x_3131_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v_x_3131_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v_x_3131_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 1);
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v_x_3131_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v_x_3131_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v_x_3131_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v_x_3131_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set_tag(v___x_3143_, 0);
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v_res_3151_; 
v_res_3151_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3149_);
return v_res_3151_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3152_; double v___x_3153_; 
v___x_3152_ = lean_unsigned_to_nat(0u);
v___x_3153_ = lean_float_of_nat(v___x_3152_);
return v___x_3153_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3155_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3156_ = l_Lean_stringToMessageData(v___x_3155_);
return v___x_3156_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3157_; double v___x_3158_; 
v___x_3157_ = lean_unsigned_to_nat(1000u);
v___x_3158_ = lean_float_of_nat(v___x_3157_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3159_, uint8_t v_collapsed_3160_, lean_object* v_tag_3161_, lean_object* v_opts_3162_, uint8_t v_clsEnabled_3163_, lean_object* v_oldTraces_3164_, lean_object* v_msg_3165_, lean_object* v_resStartStop_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_fst_3172_; lean_object* v_snd_3173_; lean_object* v___y_3175_; lean_object* v___y_3176_; lean_object* v_data_3177_; lean_object* v_fst_3188_; lean_object* v_snd_3189_; lean_object* v___x_3190_; uint8_t v___x_3191_; lean_object* v___y_3193_; lean_object* v_a_3194_; uint8_t v___y_3209_; double v___y_3240_; 
v_fst_3172_ = lean_ctor_get(v_resStartStop_3166_, 0);
lean_inc(v_fst_3172_);
v_snd_3173_ = lean_ctor_get(v_resStartStop_3166_, 1);
lean_inc(v_snd_3173_);
lean_dec_ref(v_resStartStop_3166_);
v_fst_3188_ = lean_ctor_get(v_snd_3173_, 0);
lean_inc(v_fst_3188_);
v_snd_3189_ = lean_ctor_get(v_snd_3173_, 1);
lean_inc(v_snd_3189_);
lean_dec(v_snd_3173_);
v___x_3190_ = l_Lean_trace_profiler;
v___x_3191_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3162_, v___x_3190_);
if (v___x_3191_ == 0)
{
v___y_3209_ = v___x_3191_;
goto v___jp_3208_;
}
else
{
lean_object* v___x_3245_; uint8_t v___x_3246_; 
v___x_3245_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3246_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3162_, v___x_3245_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3247_; lean_object* v___x_3248_; double v___x_3249_; double v___x_3250_; double v___x_3251_; 
v___x_3247_ = l_Lean_trace_profiler_threshold;
v___x_3248_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3162_, v___x_3247_);
v___x_3249_ = lean_float_of_nat(v___x_3248_);
v___x_3250_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3251_ = lean_float_div(v___x_3249_, v___x_3250_);
v___y_3240_ = v___x_3251_;
goto v___jp_3239_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; double v___x_3254_; 
v___x_3252_ = l_Lean_trace_profiler_threshold;
v___x_3253_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3162_, v___x_3252_);
v___x_3254_ = lean_float_of_nat(v___x_3253_);
v___y_3240_ = v___x_3254_;
goto v___jp_3239_;
}
}
v___jp_3174_:
{
lean_object* v___x_3178_; 
lean_inc(v___y_3175_);
v___x_3178_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3164_, v_data_3177_, v___y_3175_, v___y_3176_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_object* v___x_3179_; 
lean_dec_ref_known(v___x_3178_, 1);
v___x_3179_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3172_);
return v___x_3179_;
}
else
{
lean_object* v_a_3180_; lean_object* v___x_3182_; uint8_t v_isShared_3183_; uint8_t v_isSharedCheck_3187_; 
lean_dec(v_fst_3172_);
v_a_3180_ = lean_ctor_get(v___x_3178_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___x_3178_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3182_ = v___x_3178_;
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
else
{
lean_inc(v_a_3180_);
lean_dec(v___x_3178_);
v___x_3182_ = lean_box(0);
v_isShared_3183_ = v_isSharedCheck_3187_;
goto v_resetjp_3181_;
}
v_resetjp_3181_:
{
lean_object* v___x_3185_; 
if (v_isShared_3183_ == 0)
{
v___x_3185_ = v___x_3182_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3180_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
}
v___jp_3192_:
{
uint8_t v_result_3195_; lean_object* v___x_3196_; lean_object* v___x_3197_; double v___x_3198_; lean_object* v_data_3199_; 
v_result_3195_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3172_);
v___x_3196_ = lean_box(v_result_3195_);
v___x_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3197_, 0, v___x_3196_);
v___x_3198_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3161_);
lean_inc_ref(v___x_3197_);
lean_inc(v_cls_3159_);
v_data_3199_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3199_, 0, v_cls_3159_);
lean_ctor_set(v_data_3199_, 1, v___x_3197_);
lean_ctor_set(v_data_3199_, 2, v_tag_3161_);
lean_ctor_set_float(v_data_3199_, sizeof(void*)*3, v___x_3198_);
lean_ctor_set_float(v_data_3199_, sizeof(void*)*3 + 8, v___x_3198_);
lean_ctor_set_uint8(v_data_3199_, sizeof(void*)*3 + 16, v_collapsed_3160_);
if (v___x_3191_ == 0)
{
lean_dec_ref_known(v___x_3197_, 1);
lean_dec(v_snd_3189_);
lean_dec(v_fst_3188_);
lean_dec_ref(v_tag_3161_);
lean_dec(v_cls_3159_);
v___y_3175_ = v___y_3193_;
v___y_3176_ = v_a_3194_;
v_data_3177_ = v_data_3199_;
goto v___jp_3174_;
}
else
{
lean_object* v_data_3200_; double v___x_3201_; double v___x_3202_; 
lean_dec_ref_known(v_data_3199_, 3);
v_data_3200_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3200_, 0, v_cls_3159_);
lean_ctor_set(v_data_3200_, 1, v___x_3197_);
lean_ctor_set(v_data_3200_, 2, v_tag_3161_);
v___x_3201_ = lean_unbox_float(v_fst_3188_);
lean_dec(v_fst_3188_);
lean_ctor_set_float(v_data_3200_, sizeof(void*)*3, v___x_3201_);
v___x_3202_ = lean_unbox_float(v_snd_3189_);
lean_dec(v_snd_3189_);
lean_ctor_set_float(v_data_3200_, sizeof(void*)*3 + 8, v___x_3202_);
lean_ctor_set_uint8(v_data_3200_, sizeof(void*)*3 + 16, v_collapsed_3160_);
v___y_3175_ = v___y_3193_;
v___y_3176_ = v_a_3194_;
v_data_3177_ = v_data_3200_;
goto v___jp_3174_;
}
}
v___jp_3203_:
{
lean_object* v_ref_3204_; lean_object* v___x_3205_; 
v_ref_3204_ = lean_ctor_get(v___y_3169_, 2);
lean_inc(v___y_3170_);
lean_inc_ref(v___y_3169_);
lean_inc(v___y_3168_);
lean_inc_ref(v___y_3167_);
lean_inc(v_fst_3172_);
v___x_3205_ = lean_apply_6(v_msg_3165_, v_fst_3172_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_, lean_box(0));
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_object* v_a_3206_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref_known(v___x_3205_, 1);
v___y_3193_ = v_ref_3204_;
v_a_3194_ = v_a_3206_;
goto v___jp_3192_;
}
else
{
lean_object* v___x_3207_; 
lean_dec_ref_known(v___x_3205_, 1);
v___x_3207_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3193_ = v_ref_3204_;
v_a_3194_ = v___x_3207_;
goto v___jp_3192_;
}
}
v___jp_3208_:
{
if (v_clsEnabled_3163_ == 0)
{
if (v___y_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v_traceState_3211_; lean_object* v_env_3212_; lean_object* v_nextMacroScope_3213_; lean_object* v_ngen_3214_; lean_object* v_auxDeclNGen_3215_; lean_object* v_cache_3216_; lean_object* v_messages_3217_; lean_object* v_infoState_3218_; lean_object* v_snapshotTasks_3219_; lean_object* v___x_3221_; uint8_t v_isShared_3222_; uint8_t v_isSharedCheck_3238_; 
lean_dec(v_snd_3189_);
lean_dec(v_fst_3188_);
lean_dec_ref(v_msg_3165_);
lean_dec_ref(v_tag_3161_);
lean_dec(v_cls_3159_);
v___x_3210_ = lean_st_ref_take(v___y_3170_);
v_traceState_3211_ = lean_ctor_get(v___x_3210_, 4);
v_env_3212_ = lean_ctor_get(v___x_3210_, 0);
v_nextMacroScope_3213_ = lean_ctor_get(v___x_3210_, 1);
v_ngen_3214_ = lean_ctor_get(v___x_3210_, 2);
v_auxDeclNGen_3215_ = lean_ctor_get(v___x_3210_, 3);
v_cache_3216_ = lean_ctor_get(v___x_3210_, 5);
v_messages_3217_ = lean_ctor_get(v___x_3210_, 6);
v_infoState_3218_ = lean_ctor_get(v___x_3210_, 7);
v_snapshotTasks_3219_ = lean_ctor_get(v___x_3210_, 8);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3221_ = v___x_3210_;
v_isShared_3222_ = v_isSharedCheck_3238_;
goto v_resetjp_3220_;
}
else
{
lean_inc(v_snapshotTasks_3219_);
lean_inc(v_infoState_3218_);
lean_inc(v_messages_3217_);
lean_inc(v_cache_3216_);
lean_inc(v_traceState_3211_);
lean_inc(v_auxDeclNGen_3215_);
lean_inc(v_ngen_3214_);
lean_inc(v_nextMacroScope_3213_);
lean_inc(v_env_3212_);
lean_dec(v___x_3210_);
v___x_3221_ = lean_box(0);
v_isShared_3222_ = v_isSharedCheck_3238_;
goto v_resetjp_3220_;
}
v_resetjp_3220_:
{
uint64_t v_tid_3223_; lean_object* v_traces_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3237_; 
v_tid_3223_ = lean_ctor_get_uint64(v_traceState_3211_, sizeof(void*)*1);
v_traces_3224_ = lean_ctor_get(v_traceState_3211_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_traceState_3211_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3226_ = v_traceState_3211_;
v_isShared_3227_ = v_isSharedCheck_3237_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_traces_3224_);
lean_dec(v_traceState_3211_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3237_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3230_; 
v___x_3228_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3164_, v_traces_3224_);
lean_dec_ref(v_traces_3224_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3228_);
v___x_3230_ = v___x_3226_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v___x_3228_);
lean_ctor_set_uint64(v_reuseFailAlloc_3236_, sizeof(void*)*1, v_tid_3223_);
v___x_3230_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3232_; 
if (v_isShared_3222_ == 0)
{
lean_ctor_set(v___x_3221_, 4, v___x_3230_);
v___x_3232_ = v___x_3221_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v_env_3212_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_nextMacroScope_3213_);
lean_ctor_set(v_reuseFailAlloc_3235_, 2, v_ngen_3214_);
lean_ctor_set(v_reuseFailAlloc_3235_, 3, v_auxDeclNGen_3215_);
lean_ctor_set(v_reuseFailAlloc_3235_, 4, v___x_3230_);
lean_ctor_set(v_reuseFailAlloc_3235_, 5, v_cache_3216_);
lean_ctor_set(v_reuseFailAlloc_3235_, 6, v_messages_3217_);
lean_ctor_set(v_reuseFailAlloc_3235_, 7, v_infoState_3218_);
lean_ctor_set(v_reuseFailAlloc_3235_, 8, v_snapshotTasks_3219_);
v___x_3232_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3233_; lean_object* v___x_3234_; 
v___x_3233_ = lean_st_ref_put(v___y_3170_, v___x_3232_);
v___x_3234_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3172_);
return v___x_3234_;
}
}
}
}
}
else
{
goto v___jp_3203_;
}
}
else
{
goto v___jp_3203_;
}
}
v___jp_3239_:
{
double v___x_3241_; double v___x_3242_; double v___x_3243_; uint8_t v___x_3244_; 
v___x_3241_ = lean_unbox_float(v_snd_3189_);
v___x_3242_ = lean_unbox_float(v_fst_3188_);
v___x_3243_ = lean_float_sub(v___x_3241_, v___x_3242_);
v___x_3244_ = lean_float_decLt(v___y_3240_, v___x_3243_);
v___y_3209_ = v___x_3244_;
goto v___jp_3208_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3255_, lean_object* v_collapsed_3256_, lean_object* v_tag_3257_, lean_object* v_opts_3258_, lean_object* v_clsEnabled_3259_, lean_object* v_oldTraces_3260_, lean_object* v_msg_3261_, lean_object* v_resStartStop_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v_collapsed_boxed_3268_; uint8_t v_clsEnabled_boxed_3269_; lean_object* v_res_3270_; 
v_collapsed_boxed_3268_ = lean_unbox(v_collapsed_3256_);
v_clsEnabled_boxed_3269_ = lean_unbox(v_clsEnabled_3259_);
v_res_3270_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3255_, v_collapsed_boxed_3268_, v_tag_3257_, v_opts_3258_, v_clsEnabled_boxed_3269_, v_oldTraces_3260_, v_msg_3261_, v_resStartStop_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec_ref(v_opts_3258_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
if (lean_obj_tag(v_a_3271_) == 0)
{
lean_object* v___x_3273_; 
v___x_3273_ = l_List_reverse___redArg(v_a_3272_);
return v___x_3273_;
}
else
{
lean_object* v_head_3274_; lean_object* v_tail_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3284_; 
v_head_3274_ = lean_ctor_get(v_a_3271_, 0);
v_tail_3275_ = lean_ctor_get(v_a_3271_, 1);
v_isSharedCheck_3284_ = !lean_is_exclusive(v_a_3271_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3277_ = v_a_3271_;
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_tail_3275_);
lean_inc(v_head_3274_);
lean_dec(v_a_3271_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3284_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = l_Lean_MessageData_ofExpr(v_head_3274_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 1, v_a_3272_);
lean_ctor_set(v___x_3277_, 0, v___x_3279_);
v___x_3281_ = v___x_3277_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3279_);
lean_ctor_set(v_reuseFailAlloc_3283_, 1, v_a_3272_);
v___x_3281_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
v_a_3271_ = v_tail_3275_;
v_a_3272_ = v___x_3281_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3285_, lean_object* v_xs_3286_, lean_object* v_x_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; 
v___x_3293_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3294_ = l_Lean_MessageData_ofName(v_f_3285_);
v___x_3295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3293_);
lean_ctor_set(v___x_3295_, 1, v___x_3294_);
v___x_3296_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_array_to_list(v_xs_3286_);
v___x_3299_ = lean_box(0);
v___x_3300_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3298_, v___x_3299_);
v___x_3301_ = l_Lean_MessageData_ofList(v___x_3300_);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3297_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3304_, lean_object* v_xs_3305_, lean_object* v_x_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_, lean_object* v___y_3310_, lean_object* v___y_3311_){
_start:
{
lean_object* v_res_3312_; 
v_res_3312_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3304_, v_xs_3305_, v_x_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
lean_dec(v___y_3310_);
lean_dec_ref(v___y_3309_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec_ref(v_x_3306_);
return v_res_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3315_, lean_object* v_msg_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_ref_3322_; lean_object* v___x_3323_; lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3368_; 
v_ref_3322_ = lean_ctor_get(v___y_3319_, 2);
v___x_3323_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3368_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3368_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3368_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v_traceState_3329_; lean_object* v_env_3330_; lean_object* v_nextMacroScope_3331_; lean_object* v_ngen_3332_; lean_object* v_auxDeclNGen_3333_; lean_object* v_cache_3334_; lean_object* v_messages_3335_; lean_object* v_infoState_3336_; lean_object* v_snapshotTasks_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3367_; 
v___x_3328_ = lean_st_ref_take(v___y_3320_);
v_traceState_3329_ = lean_ctor_get(v___x_3328_, 4);
v_env_3330_ = lean_ctor_get(v___x_3328_, 0);
v_nextMacroScope_3331_ = lean_ctor_get(v___x_3328_, 1);
v_ngen_3332_ = lean_ctor_get(v___x_3328_, 2);
v_auxDeclNGen_3333_ = lean_ctor_get(v___x_3328_, 3);
v_cache_3334_ = lean_ctor_get(v___x_3328_, 5);
v_messages_3335_ = lean_ctor_get(v___x_3328_, 6);
v_infoState_3336_ = lean_ctor_get(v___x_3328_, 7);
v_snapshotTasks_3337_ = lean_ctor_get(v___x_3328_, 8);
v_isSharedCheck_3367_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3367_ == 0)
{
v___x_3339_ = v___x_3328_;
v_isShared_3340_ = v_isSharedCheck_3367_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_snapshotTasks_3337_);
lean_inc(v_infoState_3336_);
lean_inc(v_messages_3335_);
lean_inc(v_cache_3334_);
lean_inc(v_traceState_3329_);
lean_inc(v_auxDeclNGen_3333_);
lean_inc(v_ngen_3332_);
lean_inc(v_nextMacroScope_3331_);
lean_inc(v_env_3330_);
lean_dec(v___x_3328_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3367_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
uint64_t v_tid_3341_; lean_object* v_traces_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3366_; 
v_tid_3341_ = lean_ctor_get_uint64(v_traceState_3329_, sizeof(void*)*1);
v_traces_3342_ = lean_ctor_get(v_traceState_3329_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v_traceState_3329_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3344_ = v_traceState_3329_;
v_isShared_3345_ = v_isSharedCheck_3366_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_traces_3342_);
lean_dec(v_traceState_3329_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3366_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3346_; double v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3346_ = lean_box(0);
v___x_3347_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3348_ = 0;
v___x_3349_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3350_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3350_, 0, v_cls_3315_);
lean_ctor_set(v___x_3350_, 1, v___x_3346_);
lean_ctor_set(v___x_3350_, 2, v___x_3349_);
lean_ctor_set_float(v___x_3350_, sizeof(void*)*3, v___x_3347_);
lean_ctor_set_float(v___x_3350_, sizeof(void*)*3 + 8, v___x_3347_);
lean_ctor_set_uint8(v___x_3350_, sizeof(void*)*3 + 16, v___x_3348_);
v___x_3351_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3352_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3352_, 0, v___x_3350_);
lean_ctor_set(v___x_3352_, 1, v_a_3324_);
lean_ctor_set(v___x_3352_, 2, v___x_3351_);
lean_inc(v_ref_3322_);
v___x_3353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3353_, 0, v_ref_3322_);
lean_ctor_set(v___x_3353_, 1, v___x_3352_);
v___x_3354_ = l_Lean_PersistentArray_push___redArg(v_traces_3342_, v___x_3353_);
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 0, v___x_3354_);
v___x_3356_ = v___x_3344_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v___x_3354_);
lean_ctor_set_uint64(v_reuseFailAlloc_3365_, sizeof(void*)*1, v_tid_3341_);
v___x_3356_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3358_; 
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 4, v___x_3356_);
v___x_3358_ = v___x_3339_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_env_3330_);
lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_nextMacroScope_3331_);
lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_ngen_3332_);
lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_auxDeclNGen_3333_);
lean_ctor_set(v_reuseFailAlloc_3364_, 4, v___x_3356_);
lean_ctor_set(v_reuseFailAlloc_3364_, 5, v_cache_3334_);
lean_ctor_set(v_reuseFailAlloc_3364_, 6, v_messages_3335_);
lean_ctor_set(v_reuseFailAlloc_3364_, 7, v_infoState_3336_);
lean_ctor_set(v_reuseFailAlloc_3364_, 8, v_snapshotTasks_3337_);
v___x_3358_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3359_ = lean_st_ref_put(v___y_3320_, v___x_3358_);
v___x_3360_ = lean_box(0);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3360_);
v___x_3362_ = v___x_3326_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3369_, lean_object* v_msg_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_, lean_object* v___y_3375_){
_start:
{
lean_object* v_res_3376_; 
v_res_3376_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3369_, v_msg_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_);
lean_dec(v___y_3374_);
lean_dec_ref(v___y_3373_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
return v_res_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3377_, lean_object* v_xs_3378_, lean_object* v_k_3379_, lean_object* v_a_3380_, lean_object* v_a_3381_, lean_object* v_a_3382_, lean_object* v_a_3383_){
_start:
{
lean_object* v_toCold_3385_; lean_object* v_options_3386_; uint8_t v_hasTrace_3387_; 
v_toCold_3385_ = lean_ctor_get(v_a_3382_, 0);
v_options_3386_ = lean_ctor_get(v_toCold_3385_, 2);
v_hasTrace_3387_ = lean_ctor_get_uint8(v_options_3386_, sizeof(void*)*1);
if (v_hasTrace_3387_ == 0)
{
lean_object* v___x_3388_; 
lean_dec_ref(v_xs_3378_);
lean_dec(v_f_3377_);
lean_inc(v_a_3383_);
lean_inc_ref(v_a_3382_);
lean_inc(v_a_3381_);
lean_inc_ref(v_a_3380_);
v___x_3388_ = lean_apply_5(v_k_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, lean_box(0));
return v___x_3388_;
}
else
{
lean_object* v_inheritedTraceOptions_3389_; lean_object* v___f_3390_; lean_object* v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3418_; lean_object* v_a_3419_; lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v_a_3429_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v_a_3444_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v_a_3460_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v_a_3466_; lean_object* v___y_3469_; lean_object* v___y_3470_; lean_object* v_a_3471_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v_a_3483_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; uint8_t v___y_3489_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v_a_3499_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_a_3505_; 
v_inheritedTraceOptions_3389_ = lean_ctor_get(v_toCold_3385_, 11);
v___f_3390_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3390_, 0, v_f_3377_);
lean_closure_set(v___f_3390_, 1, v_xs_3378_);
v___x_3422_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3386_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3532_; uint8_t v___x_3533_; 
v___x_3532_ = l_Lean_trace_profiler;
v___x_3533_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3386_, v___x_3532_);
if (v___x_3533_ == 0)
{
lean_object* v___x_3534_; 
lean_dec_ref(v___f_3390_);
lean_inc(v_a_3383_);
lean_inc_ref(v_a_3382_);
lean_inc(v_a_3381_);
lean_inc_ref(v_a_3380_);
v___x_3534_ = lean_apply_5(v_k_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, lean_box(0));
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; uint8_t v___x_3538_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3535_);
v___x_3536_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3537_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3538_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3386_, v___x_3537_);
if (v___x_3538_ == 0)
{
lean_dec(v_a_3535_);
return v___x_3534_;
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_dec_ref_known(v___x_3534_, 1);
lean_inc(v_a_3535_);
v___x_3539_ = l_Lean_MessageData_ofExpr(v_a_3535_);
v___x_3540_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3536_, v___x_3539_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3547_ == 0)
{
lean_object* v_unused_3548_; 
v_unused_3548_ = lean_ctor_get(v___x_3540_, 0);
lean_dec(v_unused_3548_);
v___x_3542_ = v___x_3540_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_dec(v___x_3540_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v_a_3535_);
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3535_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_dec(v_a_3535_);
v_a_3549_ = lean_ctor_get(v___x_3540_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3540_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3540_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3540_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
lean_inc(v_a_3549_);
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
v___y_3418_ = v___x_3554_;
v_a_3419_ = v_a_3549_;
goto v___jp_3417_;
}
}
}
}
}
else
{
lean_object* v_a_3557_; 
v_a_3557_ = lean_ctor_get(v___x_3534_, 0);
lean_inc(v_a_3557_);
v___y_3418_ = v___x_3534_;
v_a_3419_ = v_a_3557_;
goto v___jp_3417_;
}
}
else
{
goto v___jp_3507_;
}
}
else
{
goto v___jp_3507_;
}
v___jp_3391_:
{
if (v___y_3394_ == 0)
{
lean_object* v___x_3395_; lean_object* v___x_3396_; uint8_t v___x_3397_; 
lean_dec_ref(v___y_3392_);
v___x_3395_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3396_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3397_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3386_, v___x_3396_);
if (v___x_3397_ == 0)
{
lean_object* v___x_3398_; 
v___x_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3398_, 0, v___y_3393_);
return v___x_3398_;
}
else
{
lean_object* v___x_3399_; lean_object* v___x_3400_; 
lean_inc_ref(v___y_3393_);
v___x_3399_ = l_Lean_Exception_toMessageData(v___y_3393_);
v___x_3400_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3395_, v___x_3399_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3400_) == 0)
{
lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v___x_3400_, 0);
lean_dec(v_unused_3408_);
v___x_3402_ = v___x_3400_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_dec(v___x_3400_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set_tag(v___x_3402_, 1);
lean_ctor_set(v___x_3402_, 0, v___y_3393_);
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___y_3393_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3411_; uint8_t v_isShared_3412_; uint8_t v_isSharedCheck_3416_; 
lean_dec_ref(v___y_3393_);
v_a_3409_ = lean_ctor_get(v___x_3400_, 0);
v_isSharedCheck_3416_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3416_ == 0)
{
v___x_3411_ = v___x_3400_;
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
else
{
lean_inc(v_a_3409_);
lean_dec(v___x_3400_);
v___x_3411_ = lean_box(0);
v_isShared_3412_ = v_isSharedCheck_3416_;
goto v_resetjp_3410_;
}
v_resetjp_3410_:
{
lean_object* v___x_3414_; 
if (v_isShared_3412_ == 0)
{
v___x_3414_ = v___x_3411_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3415_; 
v_reuseFailAlloc_3415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
v___x_3414_ = v_reuseFailAlloc_3415_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
return v___x_3414_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3393_);
return v___y_3392_;
}
}
v___jp_3417_:
{
uint8_t v___x_3420_; 
v___x_3420_ = l_Lean_Exception_isInterrupt(v_a_3419_);
if (v___x_3420_ == 0)
{
uint8_t v___x_3421_; 
lean_inc_ref(v_a_3419_);
v___x_3421_ = l_Lean_Exception_isRuntime(v_a_3419_);
v___y_3392_ = v___y_3418_;
v___y_3393_ = v_a_3419_;
v___y_3394_ = v___x_3421_;
goto v___jp_3391_;
}
else
{
v___y_3392_ = v___y_3418_;
v___y_3393_ = v_a_3419_;
v___y_3394_ = v___x_3420_;
goto v___jp_3391_;
}
}
v___jp_3426_:
{
lean_object* v___x_3430_; double v___x_3431_; double v___x_3432_; double v___x_3433_; double v___x_3434_; double v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v___x_3440_; 
v___x_3430_ = lean_io_mono_nanos_now();
v___x_3431_ = lean_float_of_nat(v___y_3428_);
v___x_3432_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3433_ = lean_float_div(v___x_3431_, v___x_3432_);
v___x_3434_ = lean_float_of_nat(v___x_3430_);
v___x_3435_ = lean_float_div(v___x_3434_, v___x_3432_);
v___x_3436_ = lean_box_float(v___x_3433_);
v___x_3437_ = lean_box_float(v___x_3435_);
v___x_3438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3436_);
lean_ctor_set(v___x_3438_, 1, v___x_3437_);
v___x_3439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3439_, 0, v_a_3429_);
lean_ctor_set(v___x_3439_, 1, v___x_3438_);
v___x_3440_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3422_, v_hasTrace_3387_, v___x_3423_, v_options_3386_, v___x_3425_, v___y_3427_, v___f_3390_, v___x_3439_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v___x_3440_;
}
v___jp_3441_:
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3445_, 0, v_a_3444_);
v___y_3427_ = v___y_3443_;
v___y_3428_ = v___y_3442_;
v_a_3429_ = v___x_3445_;
goto v___jp_3426_;
}
v___jp_3446_:
{
if (v___y_3450_ == 0)
{
lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; 
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3386_, v___x_3452_);
if (v___x_3453_ == 0)
{
v___y_3442_ = v___y_3449_;
v___y_3443_ = v___y_3448_;
v_a_3444_ = v___y_3447_;
goto v___jp_3441_;
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3455_; 
lean_inc_ref(v___y_3447_);
v___x_3454_ = l_Lean_Exception_toMessageData(v___y_3447_);
v___x_3455_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3451_, v___x_3454_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_dec_ref_known(v___x_3455_, 1);
v___y_3442_ = v___y_3449_;
v___y_3443_ = v___y_3448_;
v_a_3444_ = v___y_3447_;
goto v___jp_3441_;
}
else
{
lean_object* v_a_3456_; 
lean_dec_ref(v___y_3447_);
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___y_3442_ = v___y_3449_;
v___y_3443_ = v___y_3448_;
v_a_3444_ = v_a_3456_;
goto v___jp_3441_;
}
}
}
else
{
v___y_3442_ = v___y_3449_;
v___y_3443_ = v___y_3448_;
v_a_3444_ = v___y_3447_;
goto v___jp_3441_;
}
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
v___y_3447_ = v_a_3460_;
v___y_3448_ = v___y_3459_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___x_3462_;
goto v___jp_3446_;
}
else
{
v___y_3447_ = v_a_3460_;
v___y_3448_ = v___y_3459_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___x_3461_;
goto v___jp_3446_;
}
}
v___jp_3463_:
{
lean_object* v___x_3467_; 
v___x_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3467_, 0, v_a_3466_);
v___y_3427_ = v___y_3465_;
v___y_3428_ = v___y_3464_;
v_a_3429_ = v___x_3467_;
goto v___jp_3426_;
}
v___jp_3468_:
{
lean_object* v___x_3472_; double v___x_3473_; double v___x_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3472_ = lean_io_get_num_heartbeats();
v___x_3473_ = lean_float_of_nat(v___y_3469_);
v___x_3474_ = lean_float_of_nat(v___x_3472_);
v___x_3475_ = lean_box_float(v___x_3473_);
v___x_3476_ = lean_box_float(v___x_3474_);
v___x_3477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3475_);
lean_ctor_set(v___x_3477_, 1, v___x_3476_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_a_3471_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
v___x_3479_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3422_, v_hasTrace_3387_, v___x_3423_, v_options_3386_, v___x_3425_, v___y_3470_, v___f_3390_, v___x_3478_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
return v___x_3479_;
}
v___jp_3480_:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3484_, 0, v_a_3483_);
v___y_3469_ = v___y_3481_;
v___y_3470_ = v___y_3482_;
v_a_3471_ = v___x_3484_;
goto v___jp_3468_;
}
v___jp_3485_:
{
if (v___y_3489_ == 0)
{
lean_object* v___x_3490_; lean_object* v___x_3491_; uint8_t v___x_3492_; 
v___x_3490_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3491_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3492_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3386_, v___x_3491_);
if (v___x_3492_ == 0)
{
v___y_3481_ = v___y_3486_;
v___y_3482_ = v___y_3488_;
v_a_3483_ = v___y_3487_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3493_; lean_object* v___x_3494_; 
lean_inc_ref(v___y_3487_);
v___x_3493_ = l_Lean_Exception_toMessageData(v___y_3487_);
v___x_3494_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3490_, v___x_3493_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_dec_ref_known(v___x_3494_, 1);
v___y_3481_ = v___y_3486_;
v___y_3482_ = v___y_3488_;
v_a_3483_ = v___y_3487_;
goto v___jp_3480_;
}
else
{
lean_object* v_a_3495_; 
lean_dec_ref(v___y_3487_);
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
v___y_3481_ = v___y_3486_;
v___y_3482_ = v___y_3488_;
v_a_3483_ = v_a_3495_;
goto v___jp_3480_;
}
}
}
else
{
v___y_3481_ = v___y_3486_;
v___y_3482_ = v___y_3488_;
v_a_3483_ = v___y_3487_;
goto v___jp_3480_;
}
}
v___jp_3496_:
{
uint8_t v___x_3500_; 
v___x_3500_ = l_Lean_Exception_isInterrupt(v_a_3499_);
if (v___x_3500_ == 0)
{
uint8_t v___x_3501_; 
lean_inc_ref(v_a_3499_);
v___x_3501_ = l_Lean_Exception_isRuntime(v_a_3499_);
v___y_3486_ = v___y_3497_;
v___y_3487_ = v_a_3499_;
v___y_3488_ = v___y_3498_;
v___y_3489_ = v___x_3501_;
goto v___jp_3485_;
}
else
{
v___y_3486_ = v___y_3497_;
v___y_3487_ = v_a_3499_;
v___y_3488_ = v___y_3498_;
v___y_3489_ = v___x_3500_;
goto v___jp_3485_;
}
}
v___jp_3502_:
{
lean_object* v___x_3506_; 
v___x_3506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3506_, 0, v_a_3505_);
v___y_3469_ = v___y_3503_;
v___y_3470_ = v___y_3504_;
v_a_3471_ = v___x_3506_;
goto v___jp_3468_;
}
v___jp_3507_:
{
lean_object* v___x_3508_; lean_object* v_a_3509_; lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_3508_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3383_);
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref(v___x_3508_);
v___x_3510_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3511_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3386_, v___x_3510_);
if (v___x_3511_ == 0)
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = lean_io_mono_nanos_now();
lean_inc(v_a_3383_);
lean_inc_ref(v_a_3382_);
lean_inc(v_a_3381_);
lean_inc_ref(v_a_3380_);
v___x_3513_ = lean_apply_5(v_k_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, lean_box(0));
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3516_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3517_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3386_, v___x_3516_);
if (v___x_3517_ == 0)
{
v___y_3464_ = v___x_3512_;
v___y_3465_ = v_a_3509_;
v_a_3466_ = v_a_3514_;
goto v___jp_3463_;
}
else
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_inc(v_a_3514_);
v___x_3518_ = l_Lean_MessageData_ofExpr(v_a_3514_);
v___x_3519_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3515_, v___x_3518_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_dec_ref_known(v___x_3519_, 1);
v___y_3464_ = v___x_3512_;
v___y_3465_ = v_a_3509_;
v_a_3466_ = v_a_3514_;
goto v___jp_3463_;
}
else
{
lean_object* v_a_3520_; 
lean_dec(v_a_3514_);
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v___y_3458_ = v___x_3512_;
v___y_3459_ = v_a_3509_;
v_a_3460_ = v_a_3520_;
goto v___jp_3457_;
}
}
}
else
{
lean_object* v_a_3521_; 
v_a_3521_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3513_, 1);
v___y_3458_ = v___x_3512_;
v___y_3459_ = v_a_3509_;
v_a_3460_ = v_a_3521_;
goto v___jp_3457_;
}
}
else
{
lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3522_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3383_);
lean_inc_ref(v_a_3382_);
lean_inc(v_a_3381_);
lean_inc_ref(v_a_3380_);
v___x_3523_ = lean_apply_5(v_k_3379_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_, lean_box(0));
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; uint8_t v___x_3527_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3526_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3527_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3389_, v_options_3386_, v___x_3526_);
if (v___x_3527_ == 0)
{
v___y_3503_ = v___x_3522_;
v___y_3504_ = v_a_3509_;
v_a_3505_ = v_a_3524_;
goto v___jp_3502_;
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
lean_inc(v_a_3524_);
v___x_3528_ = l_Lean_MessageData_ofExpr(v_a_3524_);
v___x_3529_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3525_, v___x_3528_, v_a_3380_, v_a_3381_, v_a_3382_, v_a_3383_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_dec_ref_known(v___x_3529_, 1);
v___y_3503_ = v___x_3522_;
v___y_3504_ = v_a_3509_;
v_a_3505_ = v_a_3524_;
goto v___jp_3502_;
}
else
{
lean_object* v_a_3530_; 
lean_dec(v_a_3524_);
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v___y_3497_ = v___x_3522_;
v___y_3498_ = v_a_3509_;
v_a_3499_ = v_a_3530_;
goto v___jp_3496_;
}
}
}
else
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3523_, 1);
v___y_3497_ = v___x_3522_;
v___y_3498_ = v_a_3509_;
v_a_3499_ = v_a_3531_;
goto v___jp_3496_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3558_, lean_object* v_xs_3559_, lean_object* v_k_3560_, lean_object* v_a_3561_, lean_object* v_a_3562_, lean_object* v_a_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_){
_start:
{
lean_object* v_res_3566_; 
v_res_3566_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3558_, v_xs_3559_, v_k_3560_, v_a_3561_, v_a_3562_, v_a_3563_, v_a_3564_);
lean_dec(v_a_3564_);
lean_dec_ref(v_a_3563_);
lean_dec(v_a_3562_);
lean_dec_ref(v_a_3561_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3567_, lean_object* v_xs_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_){
_start:
{
lean_object* v___f_3574_; uint8_t v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_inc_ref(v_xs_3568_);
lean_inc(v_constName_3567_);
v___f_3574_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3574_, 0, v_constName_3567_);
lean_closure_set(v___f_3574_, 1, v_xs_3568_);
v___x_3575_ = 0;
v___x_3576_ = lean_box(v___x_3575_);
v___x_3577_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3577_, 0, lean_box(0));
lean_closure_set(v___x_3577_, 1, v___f_3574_);
lean_closure_set(v___x_3577_, 2, v___x_3576_);
v___x_3578_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3567_, v_xs_3568_, v___x_3577_, v_a_3569_, v_a_3570_, v_a_3571_, v_a_3572_);
return v___x_3578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3579_, lean_object* v_xs_3580_, lean_object* v_a_3581_, lean_object* v_a_3582_, lean_object* v_a_3583_, lean_object* v_a_3584_, lean_object* v_a_3585_){
_start:
{
lean_object* v_res_3586_; 
v_res_3586_ = l_Lean_Meta_mkAppM(v_constName_3579_, v_xs_3580_, v_a_3581_, v_a_3582_, v_a_3583_, v_a_3584_);
lean_dec(v_a_3584_);
lean_dec_ref(v_a_3583_);
lean_dec(v_a_3582_);
lean_dec_ref(v_a_3581_);
return v_res_3586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_){
_start:
{
lean_object* v___x_3592_; 
v___x_3592_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3590_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_){
_start:
{
lean_object* v_res_3598_; 
v_res_3598_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
lean_dec(v___y_3596_);
lean_dec_ref(v___y_3595_);
lean_dec(v___y_3594_);
lean_dec_ref(v___y_3593_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3599_, lean_object* v_x_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v___x_3606_; 
v___x_3606_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3600_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3607_, lean_object* v_x_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3607_, v_x_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3615_, lean_object* v_xs_3616_, lean_object* v_x_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_){
_start:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3623_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3624_ = l_Lean_MessageData_ofExpr(v_f_3615_);
v___x_3625_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3625_, 0, v___x_3623_);
lean_ctor_set(v___x_3625_, 1, v___x_3624_);
v___x_3626_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3627_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3627_, 0, v___x_3625_);
lean_ctor_set(v___x_3627_, 1, v___x_3626_);
v___x_3628_ = lean_array_to_list(v_xs_3616_);
v___x_3629_ = lean_box(0);
v___x_3630_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3628_, v___x_3629_);
v___x_3631_ = l_Lean_MessageData_ofList(v___x_3630_);
v___x_3632_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3632_, 0, v___x_3627_);
lean_ctor_set(v___x_3632_, 1, v___x_3631_);
v___x_3633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3632_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3634_, lean_object* v_xs_3635_, lean_object* v_x_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3634_, v_xs_3635_, v_x_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_x_3636_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3643_, lean_object* v_xs_3644_, lean_object* v_k_3645_, lean_object* v_a_3646_, lean_object* v_a_3647_, lean_object* v_a_3648_, lean_object* v_a_3649_){
_start:
{
lean_object* v_toCold_3651_; lean_object* v_options_3652_; uint8_t v_hasTrace_3653_; 
v_toCold_3651_ = lean_ctor_get(v_a_3648_, 0);
v_options_3652_ = lean_ctor_get(v_toCold_3651_, 2);
v_hasTrace_3653_ = lean_ctor_get_uint8(v_options_3652_, sizeof(void*)*1);
if (v_hasTrace_3653_ == 0)
{
lean_object* v___x_3654_; 
lean_dec_ref(v_xs_3644_);
lean_dec_ref(v_f_3643_);
lean_inc(v_a_3649_);
lean_inc_ref(v_a_3648_);
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
v___x_3654_ = lean_apply_5(v_k_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, lean_box(0));
return v___x_3654_;
}
else
{
lean_object* v_inheritedTraceOptions_3655_; lean_object* v___f_3656_; lean_object* v___y_3658_; lean_object* v___y_3659_; uint8_t v___y_3660_; lean_object* v___y_3684_; lean_object* v_a_3685_; lean_object* v___x_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; lean_object* v___y_3693_; lean_object* v___y_3694_; lean_object* v_a_3695_; lean_object* v___y_3708_; lean_object* v___y_3709_; lean_object* v_a_3710_; lean_object* v___y_3713_; lean_object* v___y_3714_; lean_object* v___y_3715_; uint8_t v___y_3716_; lean_object* v___y_3724_; lean_object* v___y_3725_; lean_object* v_a_3726_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_a_3732_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v_a_3737_; lean_object* v___y_3747_; lean_object* v___y_3748_; lean_object* v_a_3749_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v___y_3754_; uint8_t v___y_3755_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_a_3765_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_a_3771_; 
v_inheritedTraceOptions_3655_ = lean_ctor_get(v_toCold_3651_, 11);
v___f_3656_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3656_, 0, v_f_3643_);
lean_closure_set(v___f_3656_, 1, v_xs_3644_);
v___x_3688_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3689_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3690_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3691_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3655_, v_options_3652_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3798_; uint8_t v___x_3799_; 
v___x_3798_ = l_Lean_trace_profiler;
v___x_3799_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3652_, v___x_3798_);
if (v___x_3799_ == 0)
{
lean_object* v___x_3800_; 
lean_dec_ref(v___f_3656_);
lean_inc(v_a_3649_);
lean_inc_ref(v_a_3648_);
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
v___x_3800_ = lean_apply_5(v_k_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, lean_box(0));
if (lean_obj_tag(v___x_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; uint8_t v___x_3804_; 
v_a_3801_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3801_);
v___x_3802_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3803_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3655_, v_options_3652_, v___x_3803_);
if (v___x_3804_ == 0)
{
lean_dec(v_a_3801_);
return v___x_3800_;
}
else
{
lean_object* v___x_3805_; lean_object* v___x_3806_; 
lean_dec_ref_known(v___x_3800_, 1);
lean_inc(v_a_3801_);
v___x_3805_ = l_Lean_MessageData_ofExpr(v_a_3801_);
v___x_3806_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3802_, v___x_3805_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3813_ == 0)
{
lean_object* v_unused_3814_; 
v_unused_3814_ = lean_ctor_get(v___x_3806_, 0);
lean_dec(v_unused_3814_);
v___x_3808_ = v___x_3806_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_dec(v___x_3806_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v_a_3801_);
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3801_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
lean_dec(v_a_3801_);
v_a_3815_ = lean_ctor_get(v___x_3806_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3806_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3806_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3806_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
lean_inc(v_a_3815_);
if (v_isShared_3818_ == 0)
{
v___x_3820_ = v___x_3817_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_a_3815_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
v___y_3684_ = v___x_3820_;
v_a_3685_ = v_a_3815_;
goto v___jp_3683_;
}
}
}
}
}
else
{
lean_object* v_a_3823_; 
v_a_3823_ = lean_ctor_get(v___x_3800_, 0);
lean_inc(v_a_3823_);
v___y_3684_ = v___x_3800_;
v_a_3685_ = v_a_3823_;
goto v___jp_3683_;
}
}
else
{
goto v___jp_3773_;
}
}
else
{
goto v___jp_3773_;
}
v___jp_3657_:
{
if (v___y_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; uint8_t v___x_3663_; 
lean_dec_ref(v___y_3659_);
v___x_3661_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3662_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3655_, v_options_3652_, v___x_3662_);
if (v___x_3663_ == 0)
{
lean_object* v___x_3664_; 
v___x_3664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___y_3658_);
return v___x_3664_;
}
else
{
lean_object* v___x_3665_; lean_object* v___x_3666_; 
lean_inc_ref(v___y_3658_);
v___x_3665_ = l_Lean_Exception_toMessageData(v___y_3658_);
v___x_3666_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3661_, v___x_3665_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3673_; 
v_isSharedCheck_3673_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3673_ == 0)
{
lean_object* v_unused_3674_; 
v_unused_3674_ = lean_ctor_get(v___x_3666_, 0);
lean_dec(v_unused_3674_);
v___x_3668_ = v___x_3666_;
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
else
{
lean_dec(v___x_3666_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3673_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3671_; 
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 1);
lean_ctor_set(v___x_3668_, 0, v___y_3658_);
v___x_3671_ = v___x_3668_;
goto v_reusejp_3670_;
}
else
{
lean_object* v_reuseFailAlloc_3672_; 
v_reuseFailAlloc_3672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3672_, 0, v___y_3658_);
v___x_3671_ = v_reuseFailAlloc_3672_;
goto v_reusejp_3670_;
}
v_reusejp_3670_:
{
return v___x_3671_;
}
}
}
else
{
lean_object* v_a_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3682_; 
lean_dec_ref(v___y_3658_);
v_a_3675_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3677_ = v___x_3666_;
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_a_3675_);
lean_dec(v___x_3666_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3682_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3680_; 
if (v_isShared_3678_ == 0)
{
v___x_3680_ = v___x_3677_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3675_);
v___x_3680_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
return v___x_3680_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3658_);
return v___y_3659_;
}
}
v___jp_3683_:
{
uint8_t v___x_3686_; 
v___x_3686_ = l_Lean_Exception_isInterrupt(v_a_3685_);
if (v___x_3686_ == 0)
{
uint8_t v___x_3687_; 
lean_inc_ref(v_a_3685_);
v___x_3687_ = l_Lean_Exception_isRuntime(v_a_3685_);
v___y_3658_ = v_a_3685_;
v___y_3659_ = v___y_3684_;
v___y_3660_ = v___x_3687_;
goto v___jp_3657_;
}
else
{
v___y_3658_ = v_a_3685_;
v___y_3659_ = v___y_3684_;
v___y_3660_ = v___x_3686_;
goto v___jp_3657_;
}
}
v___jp_3692_:
{
lean_object* v___x_3696_; double v___x_3697_; double v___x_3698_; double v___x_3699_; double v___x_3700_; double v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3696_ = lean_io_mono_nanos_now();
v___x_3697_ = lean_float_of_nat(v___y_3693_);
v___x_3698_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3699_ = lean_float_div(v___x_3697_, v___x_3698_);
v___x_3700_ = lean_float_of_nat(v___x_3696_);
v___x_3701_ = lean_float_div(v___x_3700_, v___x_3698_);
v___x_3702_ = lean_box_float(v___x_3699_);
v___x_3703_ = lean_box_float(v___x_3701_);
v___x_3704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3702_);
lean_ctor_set(v___x_3704_, 1, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3705_, 0, v_a_3695_);
lean_ctor_set(v___x_3705_, 1, v___x_3704_);
v___x_3706_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3688_, v_hasTrace_3653_, v___x_3689_, v_options_3652_, v___x_3691_, v___y_3694_, v___f_3656_, v___x_3705_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
return v___x_3706_;
}
v___jp_3707_:
{
lean_object* v___x_3711_; 
v___x_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3711_, 0, v_a_3710_);
v___y_3693_ = v___y_3708_;
v___y_3694_ = v___y_3709_;
v_a_3695_ = v___x_3711_;
goto v___jp_3692_;
}
v___jp_3712_:
{
if (v___y_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3718_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3655_, v_options_3652_, v___x_3718_);
if (v___x_3719_ == 0)
{
v___y_3708_ = v___y_3713_;
v___y_3709_ = v___y_3714_;
v_a_3710_ = v___y_3715_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3721_; 
lean_inc_ref(v___y_3715_);
v___x_3720_ = l_Lean_Exception_toMessageData(v___y_3715_);
v___x_3721_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3717_, v___x_3720_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_dec_ref_known(v___x_3721_, 1);
v___y_3708_ = v___y_3713_;
v___y_3709_ = v___y_3714_;
v_a_3710_ = v___y_3715_;
goto v___jp_3707_;
}
else
{
lean_object* v_a_3722_; 
lean_dec_ref(v___y_3715_);
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref_known(v___x_3721_, 1);
v___y_3708_ = v___y_3713_;
v___y_3709_ = v___y_3714_;
v_a_3710_ = v_a_3722_;
goto v___jp_3707_;
}
}
}
else
{
v___y_3708_ = v___y_3713_;
v___y_3709_ = v___y_3714_;
v_a_3710_ = v___y_3715_;
goto v___jp_3707_;
}
}
v___jp_3723_:
{
uint8_t v___x_3727_; 
v___x_3727_ = l_Lean_Exception_isInterrupt(v_a_3726_);
if (v___x_3727_ == 0)
{
uint8_t v___x_3728_; 
lean_inc_ref(v_a_3726_);
v___x_3728_ = l_Lean_Exception_isRuntime(v_a_3726_);
v___y_3713_ = v___y_3724_;
v___y_3714_ = v___y_3725_;
v___y_3715_ = v_a_3726_;
v___y_3716_ = v___x_3728_;
goto v___jp_3712_;
}
else
{
v___y_3713_ = v___y_3724_;
v___y_3714_ = v___y_3725_;
v___y_3715_ = v_a_3726_;
v___y_3716_ = v___x_3727_;
goto v___jp_3712_;
}
}
v___jp_3729_:
{
lean_object* v___x_3733_; 
v___x_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3733_, 0, v_a_3732_);
v___y_3693_ = v___y_3730_;
v___y_3694_ = v___y_3731_;
v_a_3695_ = v___x_3733_;
goto v___jp_3692_;
}
v___jp_3734_:
{
lean_object* v___x_3738_; double v___x_3739_; double v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; 
v___x_3738_ = lean_io_get_num_heartbeats();
v___x_3739_ = lean_float_of_nat(v___y_3736_);
v___x_3740_ = lean_float_of_nat(v___x_3738_);
v___x_3741_ = lean_box_float(v___x_3739_);
v___x_3742_ = lean_box_float(v___x_3740_);
v___x_3743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3741_);
lean_ctor_set(v___x_3743_, 1, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v_a_3737_);
lean_ctor_set(v___x_3744_, 1, v___x_3743_);
v___x_3745_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3688_, v_hasTrace_3653_, v___x_3689_, v_options_3652_, v___x_3691_, v___y_3735_, v___f_3656_, v___x_3744_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
return v___x_3745_;
}
v___jp_3746_:
{
lean_object* v___x_3750_; 
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3749_);
v___y_3735_ = v___y_3747_;
v___y_3736_ = v___y_3748_;
v_a_3737_ = v___x_3750_;
goto v___jp_3734_;
}
v___jp_3751_:
{
if (v___y_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3757_; uint8_t v___x_3758_; 
v___x_3756_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3757_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3758_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3655_, v_options_3652_, v___x_3757_);
if (v___x_3758_ == 0)
{
v___y_3747_ = v___y_3752_;
v___y_3748_ = v___y_3754_;
v_a_3749_ = v___y_3753_;
goto v___jp_3746_;
}
else
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
lean_inc_ref(v___y_3753_);
v___x_3759_ = l_Lean_Exception_toMessageData(v___y_3753_);
v___x_3760_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3756_, v___x_3759_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
if (lean_obj_tag(v___x_3760_) == 0)
{
lean_dec_ref_known(v___x_3760_, 1);
v___y_3747_ = v___y_3752_;
v___y_3748_ = v___y_3754_;
v_a_3749_ = v___y_3753_;
goto v___jp_3746_;
}
else
{
lean_object* v_a_3761_; 
lean_dec_ref(v___y_3753_);
v_a_3761_ = lean_ctor_get(v___x_3760_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v___x_3760_, 1);
v___y_3747_ = v___y_3752_;
v___y_3748_ = v___y_3754_;
v_a_3749_ = v_a_3761_;
goto v___jp_3746_;
}
}
}
else
{
v___y_3747_ = v___y_3752_;
v___y_3748_ = v___y_3754_;
v_a_3749_ = v___y_3753_;
goto v___jp_3746_;
}
}
v___jp_3762_:
{
uint8_t v___x_3766_; 
v___x_3766_ = l_Lean_Exception_isInterrupt(v_a_3765_);
if (v___x_3766_ == 0)
{
uint8_t v___x_3767_; 
lean_inc_ref(v_a_3765_);
v___x_3767_ = l_Lean_Exception_isRuntime(v_a_3765_);
v___y_3752_ = v___y_3763_;
v___y_3753_ = v_a_3765_;
v___y_3754_ = v___y_3764_;
v___y_3755_ = v___x_3767_;
goto v___jp_3751_;
}
else
{
v___y_3752_ = v___y_3763_;
v___y_3753_ = v_a_3765_;
v___y_3754_ = v___y_3764_;
v___y_3755_ = v___x_3766_;
goto v___jp_3751_;
}
}
v___jp_3768_:
{
lean_object* v___x_3772_; 
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v_a_3771_);
v___y_3735_ = v___y_3769_;
v___y_3736_ = v___y_3770_;
v_a_3737_ = v___x_3772_;
goto v___jp_3734_;
}
v___jp_3773_:
{
lean_object* v___x_3774_; lean_object* v_a_3775_; lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3774_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3649_);
v_a_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc(v_a_3775_);
lean_dec_ref(v___x_3774_);
v___x_3776_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3777_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3652_, v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3778_ = lean_io_mono_nanos_now();
lean_inc(v_a_3649_);
lean_inc_ref(v_a_3648_);
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
v___x_3779_ = lean_apply_5(v_k_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, lean_box(0));
if (lean_obj_tag(v___x_3779_) == 0)
{
lean_object* v_a_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_a_3780_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3780_);
lean_dec_ref_known(v___x_3779_, 1);
v___x_3781_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3782_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3783_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3655_, v_options_3652_, v___x_3782_);
if (v___x_3783_ == 0)
{
v___y_3730_ = v___x_3778_;
v___y_3731_ = v_a_3775_;
v_a_3732_ = v_a_3780_;
goto v___jp_3729_;
}
else
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
lean_inc(v_a_3780_);
v___x_3784_ = l_Lean_MessageData_ofExpr(v_a_3780_);
v___x_3785_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3781_, v___x_3784_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_dec_ref_known(v___x_3785_, 1);
v___y_3730_ = v___x_3778_;
v___y_3731_ = v_a_3775_;
v_a_3732_ = v_a_3780_;
goto v___jp_3729_;
}
else
{
lean_object* v_a_3786_; 
lean_dec(v_a_3780_);
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3724_ = v___x_3778_;
v___y_3725_ = v_a_3775_;
v_a_3726_ = v_a_3786_;
goto v___jp_3723_;
}
}
}
else
{
lean_object* v_a_3787_; 
v_a_3787_ = lean_ctor_get(v___x_3779_, 0);
lean_inc(v_a_3787_);
lean_dec_ref_known(v___x_3779_, 1);
v___y_3724_ = v___x_3778_;
v___y_3725_ = v_a_3775_;
v_a_3726_ = v_a_3787_;
goto v___jp_3723_;
}
}
else
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3649_);
lean_inc_ref(v_a_3648_);
lean_inc(v_a_3647_);
lean_inc_ref(v_a_3646_);
v___x_3789_ = lean_apply_5(v_k_3645_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_, lean_box(0));
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; uint8_t v___x_3793_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
v___x_3791_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3792_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3793_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3655_, v_options_3652_, v___x_3792_);
if (v___x_3793_ == 0)
{
v___y_3769_ = v_a_3775_;
v___y_3770_ = v___x_3788_;
v_a_3771_ = v_a_3790_;
goto v___jp_3768_;
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
lean_inc(v_a_3790_);
v___x_3794_ = l_Lean_MessageData_ofExpr(v_a_3790_);
v___x_3795_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3791_, v___x_3794_, v_a_3646_, v_a_3647_, v_a_3648_, v_a_3649_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_dec_ref_known(v___x_3795_, 1);
v___y_3769_ = v_a_3775_;
v___y_3770_ = v___x_3788_;
v_a_3771_ = v_a_3790_;
goto v___jp_3768_;
}
else
{
lean_object* v_a_3796_; 
lean_dec(v_a_3790_);
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v___y_3763_ = v_a_3775_;
v___y_3764_ = v___x_3788_;
v_a_3765_ = v_a_3796_;
goto v___jp_3762_;
}
}
}
else
{
lean_object* v_a_3797_; 
v_a_3797_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3789_, 1);
v___y_3763_ = v_a_3775_;
v___y_3764_ = v___x_3788_;
v_a_3765_ = v_a_3797_;
goto v___jp_3762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3824_, lean_object* v_xs_3825_, lean_object* v_k_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_, lean_object* v_a_3830_, lean_object* v_a_3831_){
_start:
{
lean_object* v_res_3832_; 
v_res_3832_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3824_, v_xs_3825_, v_k_3826_, v_a_3827_, v_a_3828_, v_a_3829_, v_a_3830_);
lean_dec(v_a_3830_);
lean_dec_ref(v_a_3829_);
lean_dec(v_a_3828_);
lean_dec_ref(v_a_3827_);
return v_res_3832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3833_, lean_object* v_xs_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_){
_start:
{
lean_object* v___x_3840_; 
lean_inc(v_a_3838_);
lean_inc_ref(v_a_3837_);
lean_inc(v_a_3836_);
lean_inc_ref(v_a_3835_);
lean_inc_ref(v_f_3833_);
v___x_3840_ = lean_infer_type(v_f_3833_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v___x_3842_; uint8_t v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
lean_inc_ref(v_xs_3834_);
lean_inc_ref(v_f_3833_);
v___x_3842_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3842_, 0, v_f_3833_);
lean_closure_set(v___x_3842_, 1, v_a_3841_);
lean_closure_set(v___x_3842_, 2, v_xs_3834_);
v___x_3843_ = 0;
v___x_3844_ = lean_box(v___x_3843_);
v___x_3845_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3845_, 0, lean_box(0));
lean_closure_set(v___x_3845_, 1, v___x_3842_);
lean_closure_set(v___x_3845_, 2, v___x_3844_);
v___x_3846_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3833_, v_xs_3834_, v___x_3845_, v_a_3835_, v_a_3836_, v_a_3837_, v_a_3838_);
return v___x_3846_;
}
else
{
lean_dec_ref(v_xs_3834_);
lean_dec_ref(v_f_3833_);
return v___x_3840_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3847_, lean_object* v_xs_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_){
_start:
{
lean_object* v_res_3854_; 
v_res_3854_ = l_Lean_Meta_mkAppM_x27(v_f_3847_, v_xs_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_);
lean_dec(v_a_3852_);
lean_dec_ref(v_a_3851_);
lean_dec(v_a_3850_);
lean_dec_ref(v_a_3849_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3855_, size_t v_i_3856_, size_t v_stop_3857_, lean_object* v_b_3858_){
_start:
{
lean_object* v___y_3860_; uint8_t v___x_3864_; 
v___x_3864_ = lean_usize_dec_eq(v_i_3856_, v_stop_3857_);
if (v___x_3864_ == 0)
{
lean_object* v___x_3865_; 
v___x_3865_ = lean_array_uget_borrowed(v_as_3855_, v_i_3856_);
if (lean_obj_tag(v___x_3865_) == 0)
{
v___y_3860_ = v_b_3858_;
goto v___jp_3859_;
}
else
{
lean_object* v_val_3866_; lean_object* v___x_3867_; 
v_val_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_val_3866_);
v___x_3867_ = lean_array_push(v_b_3858_, v_val_3866_);
v___y_3860_ = v___x_3867_;
goto v___jp_3859_;
}
}
else
{
return v_b_3858_;
}
v___jp_3859_:
{
size_t v___x_3861_; size_t v___x_3862_; 
v___x_3861_ = ((size_t)1ULL);
v___x_3862_ = lean_usize_add(v_i_3856_, v___x_3861_);
v_i_3856_ = v___x_3862_;
v_b_3858_ = v___y_3860_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3868_, lean_object* v_i_3869_, lean_object* v_stop_3870_, lean_object* v_b_3871_){
_start:
{
size_t v_i_boxed_3872_; size_t v_stop_boxed_3873_; lean_object* v_res_3874_; 
v_i_boxed_3872_ = lean_unbox_usize(v_i_3869_);
lean_dec(v_i_3869_);
v_stop_boxed_3873_ = lean_unbox_usize(v_stop_3870_);
lean_dec(v_stop_3870_);
v_res_3874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3868_, v_i_boxed_3872_, v_stop_boxed_3873_, v_b_3871_);
lean_dec_ref(v_as_3868_);
return v_res_3874_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3882_ = l_Lean_MessageData_ofFormat(v___x_3881_);
return v___x_3882_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = lean_box(1);
v___x_3884_ = l_Lean_MessageData_ofFormat(v___x_3883_);
return v___x_3884_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3888_; lean_object* v___x_3889_; 
v___x_3888_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3889_ = l_Lean_MessageData_ofFormat(v___x_3888_);
return v___x_3889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3890_, lean_object* v_xs_3891_, lean_object* v_x_3892_, lean_object* v_x_3893_, lean_object* v_x_3894_, lean_object* v_x_3895_, lean_object* v_x_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_){
_start:
{
if (lean_obj_tag(v_x_3896_) == 7)
{
lean_object* v_binderName_3902_; lean_object* v_binderType_3903_; lean_object* v_body_3904_; uint8_t v_binderInfo_3905_; lean_object* v___x_3906_; uint8_t v___x_3907_; 
v_binderName_3902_ = lean_ctor_get(v_x_3896_, 0);
lean_inc(v_binderName_3902_);
v_binderType_3903_ = lean_ctor_get(v_x_3896_, 1);
lean_inc_ref(v_binderType_3903_);
v_body_3904_ = lean_ctor_get(v_x_3896_, 2);
lean_inc_ref(v_body_3904_);
v_binderInfo_3905_ = lean_ctor_get_uint8(v_x_3896_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3896_, 3);
v___x_3906_ = lean_array_get_size(v_xs_3891_);
v___x_3907_ = lean_nat_dec_lt(v_x_3892_, v___x_3906_);
if (v___x_3907_ == 0)
{
lean_object* v___x_3908_; lean_object* v___x_3909_; 
lean_dec_ref(v_body_3904_);
lean_dec_ref(v_binderType_3903_);
lean_dec(v_binderName_3902_);
lean_dec(v_x_3894_);
lean_dec(v_x_3892_);
v___x_3908_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3909_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3908_, v_f_3890_, v_x_3893_, v_x_3895_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
lean_dec_ref(v_x_3895_);
lean_dec_ref(v_x_3893_);
return v___x_3909_;
}
else
{
lean_object* v___x_3910_; lean_object* v_d_3911_; lean_object* v___x_3912_; 
v___x_3910_ = lean_array_get_size(v_x_3893_);
v_d_3911_ = lean_expr_instantiate_rev_range(v_binderType_3903_, v_x_3894_, v___x_3910_, v_x_3893_);
lean_dec_ref(v_binderType_3903_);
v___x_3912_ = lean_array_fget_borrowed(v_xs_3891_, v_x_3892_);
if (lean_obj_tag(v___x_3912_) == 0)
{
if (v_binderInfo_3905_ == 3)
{
lean_object* v___x_3913_; uint8_t v___x_3914_; lean_object* v___x_3915_; 
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v_d_3911_);
v___x_3914_ = 1;
v___x_3915_ = l_Lean_Meta_mkFreshExprMVar(v___x_3913_, v___x_3914_, v_binderName_3902_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
if (lean_obj_tag(v___x_3915_) == 0)
{
lean_object* v_a_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_a_3916_ = lean_ctor_get(v___x_3915_, 0);
lean_inc_n(v_a_3916_, 2);
lean_dec_ref_known(v___x_3915_, 1);
v___x_3917_ = lean_unsigned_to_nat(1u);
v___x_3918_ = lean_nat_add(v_x_3892_, v___x_3917_);
lean_dec(v_x_3892_);
v___x_3919_ = lean_array_push(v_x_3893_, v_a_3916_);
v___x_3920_ = l_Lean_Expr_mvarId_x21(v_a_3916_);
lean_dec(v_a_3916_);
v___x_3921_ = lean_array_push(v_x_3895_, v___x_3920_);
v_x_3892_ = v___x_3918_;
v_x_3893_ = v___x_3919_;
v_x_3895_ = v___x_3921_;
v_x_3896_ = v_body_3904_;
goto _start;
}
else
{
lean_dec_ref(v_body_3904_);
lean_dec_ref(v_x_3895_);
lean_dec(v_x_3894_);
lean_dec_ref(v_x_3893_);
lean_dec(v_x_3892_);
lean_dec_ref(v_f_3890_);
return v___x_3915_;
}
}
else
{
lean_object* v___x_3923_; uint8_t v___x_3924_; lean_object* v___x_3925_; 
v___x_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3923_, 0, v_d_3911_);
v___x_3924_ = 0;
v___x_3925_ = l_Lean_Meta_mkFreshExprMVar(v___x_3923_, v___x_3924_, v_binderName_3902_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
lean_inc(v_a_3926_);
lean_dec_ref_known(v___x_3925_, 1);
v___x_3927_ = lean_unsigned_to_nat(1u);
v___x_3928_ = lean_nat_add(v_x_3892_, v___x_3927_);
lean_dec(v_x_3892_);
v___x_3929_ = lean_array_push(v_x_3893_, v_a_3926_);
v_x_3892_ = v___x_3928_;
v_x_3893_ = v___x_3929_;
v_x_3896_ = v_body_3904_;
goto _start;
}
else
{
lean_dec_ref(v_body_3904_);
lean_dec_ref(v_x_3895_);
lean_dec(v_x_3894_);
lean_dec_ref(v_x_3893_);
lean_dec(v_x_3892_);
lean_dec_ref(v_f_3890_);
return v___x_3925_;
}
}
}
else
{
lean_object* v_val_3931_; lean_object* v___x_3932_; 
lean_dec(v_binderName_3902_);
v_val_3931_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3900_);
lean_inc_ref(v_a_3899_);
lean_inc(v_a_3898_);
lean_inc_ref(v_a_3897_);
lean_inc(v_val_3931_);
v___x_3932_ = lean_infer_type(v_val_3931_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3934_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
lean_inc(v_a_3933_);
lean_dec_ref_known(v___x_3932_, 1);
v___x_3934_ = l_Lean_Meta_isExprDefEq(v_d_3911_, v_a_3933_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; uint8_t v___x_3936_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v___x_3936_ = lean_unbox(v_a_3935_);
lean_dec(v_a_3935_);
if (v___x_3936_ == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_dec_ref(v_body_3904_);
lean_dec_ref(v_x_3895_);
lean_dec(v_x_3894_);
lean_dec(v_x_3892_);
v___x_3937_ = l_Lean_mkAppN(v_f_3890_, v_x_3893_);
lean_dec_ref(v_x_3893_);
lean_inc(v_val_3931_);
v___x_3938_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3937_, v_val_3931_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
return v___x_3938_;
}
else
{
lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; 
v___x_3939_ = lean_unsigned_to_nat(1u);
v___x_3940_ = lean_nat_add(v_x_3892_, v___x_3939_);
lean_dec(v_x_3892_);
lean_inc(v_val_3931_);
v___x_3941_ = lean_array_push(v_x_3893_, v_val_3931_);
v_x_3892_ = v___x_3940_;
v_x_3893_ = v___x_3941_;
v_x_3896_ = v_body_3904_;
goto _start;
}
}
else
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v_body_3904_);
lean_dec_ref(v_x_3895_);
lean_dec(v_x_3894_);
lean_dec_ref(v_x_3893_);
lean_dec(v_x_3892_);
lean_dec_ref(v_f_3890_);
v_a_3943_ = lean_ctor_get(v___x_3934_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3945_ = v___x_3934_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3934_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
else
{
lean_dec_ref(v_d_3911_);
lean_dec_ref(v_body_3904_);
lean_dec_ref(v_x_3895_);
lean_dec(v_x_3894_);
lean_dec_ref(v_x_3893_);
lean_dec(v_x_3892_);
lean_dec_ref(v_f_3890_);
return v___x_3932_;
}
}
}
}
else
{
lean_object* v___x_3951_; lean_object* v_type_3952_; lean_object* v___x_3953_; 
v___x_3951_ = lean_array_get_size(v_x_3893_);
v_type_3952_ = lean_expr_instantiate_rev_range(v_x_3896_, v_x_3894_, v___x_3951_, v_x_3893_);
lean_dec(v_x_3894_);
lean_dec_ref(v_x_3896_);
v___x_3953_ = l_Lean_Meta_whnfD(v_type_3952_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; uint8_t v___x_3955_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = l_Lean_Expr_isForall(v_a_3954_);
if (v___x_3955_ == 0)
{
lean_object* v___x_3956_; uint8_t v___x_3957_; 
lean_dec(v_a_3954_);
v___x_3956_ = lean_array_get_size(v_xs_3891_);
v___x_3957_ = lean_nat_dec_eq(v_x_3892_, v___x_3956_);
lean_dec(v_x_3892_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; lean_object* v___y_3960_; lean_object* v___x_3973_; uint8_t v___x_3974_; 
lean_dec_ref(v_x_3895_);
lean_dec_ref(v_x_3893_);
v___x_3958_ = lean_unsigned_to_nat(0u);
v___x_3973_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3974_ = lean_nat_dec_lt(v___x_3958_, v___x_3956_);
if (v___x_3974_ == 0)
{
v___y_3960_ = v___x_3973_;
goto v___jp_3959_;
}
else
{
uint8_t v___x_3975_; 
v___x_3975_ = lean_nat_dec_le(v___x_3956_, v___x_3956_);
if (v___x_3975_ == 0)
{
if (v___x_3974_ == 0)
{
v___y_3960_ = v___x_3973_;
goto v___jp_3959_;
}
else
{
size_t v___x_3976_; size_t v___x_3977_; lean_object* v___x_3978_; 
v___x_3976_ = ((size_t)0ULL);
v___x_3977_ = lean_usize_of_nat(v___x_3956_);
v___x_3978_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3891_, v___x_3976_, v___x_3977_, v___x_3973_);
v___y_3960_ = v___x_3978_;
goto v___jp_3959_;
}
}
else
{
size_t v___x_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = ((size_t)0ULL);
v___x_3980_ = lean_usize_of_nat(v___x_3956_);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3891_, v___x_3979_, v___x_3980_, v___x_3973_);
v___y_3960_ = v___x_3981_;
goto v___jp_3959_;
}
}
v___jp_3959_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3962_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3963_ = l_Lean_indentExpr(v_f_3890_);
v___x_3964_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3962_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3964_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
v___x_3967_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3966_);
lean_ctor_set(v___x_3968_, 1, v___x_3967_);
v___x_3969_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3970_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3960_, v___x_3958_, v___x_3969_);
lean_dec_ref(v___y_3960_);
v___x_3971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3971_, 0, v___x_3968_);
lean_ctor_set(v___x_3971_, 1, v___x_3970_);
v___x_3972_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3961_, v___x_3971_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
return v___x_3972_;
}
}
else
{
lean_object* v___x_3982_; lean_object* v___x_3983_; 
v___x_3982_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3983_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3982_, v_f_3890_, v_x_3893_, v_x_3895_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_);
lean_dec_ref(v_x_3895_);
lean_dec_ref(v_x_3893_);
return v___x_3983_;
}
}
else
{
v_x_3894_ = v___x_3951_;
v_x_3896_ = v_a_3954_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3895_);
lean_dec_ref(v_x_3893_);
lean_dec(v_x_3892_);
lean_dec_ref(v_f_3890_);
return v___x_3953_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_3985_, lean_object* v_xs_3986_, lean_object* v_x_3987_, lean_object* v_x_3988_, lean_object* v_x_3989_, lean_object* v_x_3990_, lean_object* v_x_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_3985_, v_xs_3986_, v_x_3987_, v_x_3988_, v_x_3989_, v_x_3990_, v_x_3991_, v_a_3992_, v_a_3993_, v_a_3994_, v_a_3995_);
lean_dec(v_a_3995_);
lean_dec_ref(v_a_3994_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec_ref(v_xs_3986_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_3998_, lean_object* v_xs_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_3998_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v_fst_4007_; lean_object* v_snd_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v_fst_4007_ = lean_ctor_get(v_a_4006_, 0);
lean_inc(v_fst_4007_);
v_snd_4008_ = lean_ctor_get(v_a_4006_, 1);
lean_inc(v_snd_4008_);
lean_dec(v_a_4006_);
v___x_4009_ = lean_unsigned_to_nat(0u);
v___x_4010_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4011_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4007_, v_xs_3999_, v___x_4009_, v___x_4010_, v___x_4009_, v___x_4010_, v_snd_4008_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
return v___x_4011_;
}
else
{
lean_object* v_a_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4019_; 
v_a_4012_ = lean_ctor_get(v___x_4005_, 0);
v_isSharedCheck_4019_ = !lean_is_exclusive(v___x_4005_);
if (v_isSharedCheck_4019_ == 0)
{
v___x_4014_ = v___x_4005_;
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_a_4012_);
lean_dec(v___x_4005_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4019_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v___x_4017_; 
if (v_isShared_4015_ == 0)
{
v___x_4017_ = v___x_4014_;
goto v_reusejp_4016_;
}
else
{
lean_object* v_reuseFailAlloc_4018_; 
v_reuseFailAlloc_4018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4018_, 0, v_a_4012_);
v___x_4017_ = v_reuseFailAlloc_4018_;
goto v_reusejp_4016_;
}
v_reusejp_4016_:
{
return v___x_4017_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4020_, lean_object* v_xs_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v_res_4027_; 
v_res_4027_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4020_, v_xs_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec_ref(v_xs_4021_);
return v_res_4027_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; 
v___x_4031_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4032_ = l_Lean_MessageData_ofFormat(v___x_4031_);
return v___x_4032_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4033_, lean_object* v_a_4034_){
_start:
{
if (lean_obj_tag(v_a_4033_) == 0)
{
lean_object* v___x_4035_; 
v___x_4035_ = l_List_reverse___redArg(v_a_4034_);
return v___x_4035_;
}
else
{
lean_object* v_head_4036_; lean_object* v_tail_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4050_; 
v_head_4036_ = lean_ctor_get(v_a_4033_, 0);
v_tail_4037_ = lean_ctor_get(v_a_4033_, 1);
v_isSharedCheck_4050_ = !lean_is_exclusive(v_a_4033_);
if (v_isSharedCheck_4050_ == 0)
{
v___x_4039_ = v_a_4033_;
v_isShared_4040_ = v_isSharedCheck_4050_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_tail_4037_);
lean_inc(v_head_4036_);
lean_dec(v_a_4033_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4050_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___y_4042_; 
if (lean_obj_tag(v_head_4036_) == 0)
{
lean_object* v___x_4047_; 
v___x_4047_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4042_ = v___x_4047_;
goto v___jp_4041_;
}
else
{
lean_object* v_val_4048_; lean_object* v___x_4049_; 
v_val_4048_ = lean_ctor_get(v_head_4036_, 0);
lean_inc(v_val_4048_);
lean_dec_ref_known(v_head_4036_, 1);
v___x_4049_ = l_Lean_MessageData_ofExpr(v_val_4048_);
v___y_4042_ = v___x_4049_;
goto v___jp_4041_;
}
v___jp_4041_:
{
lean_object* v___x_4044_; 
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 1, v_a_4034_);
lean_ctor_set(v___x_4039_, 0, v___y_4042_);
v___x_4044_ = v___x_4039_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___y_4042_);
lean_ctor_set(v_reuseFailAlloc_4046_, 1, v_a_4034_);
v___x_4044_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
v_a_4033_ = v_tail_4037_;
v_a_4034_ = v___x_4044_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4051_, lean_object* v_xs_4052_, lean_object* v_x_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4059_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4060_ = l_Lean_MessageData_ofName(v_f_4051_);
v___x_4061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4059_);
lean_ctor_set(v___x_4061_, 1, v___x_4060_);
v___x_4062_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4063_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4061_);
lean_ctor_set(v___x_4063_, 1, v___x_4062_);
v___x_4064_ = lean_array_to_list(v_xs_4052_);
v___x_4065_ = lean_box(0);
v___x_4066_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4064_, v___x_4065_);
v___x_4067_ = l_Lean_MessageData_ofList(v___x_4066_);
v___x_4068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4068_, 0, v___x_4063_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
v___x_4069_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4068_);
return v___x_4069_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4070_, lean_object* v_xs_4071_, lean_object* v_x_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_){
_start:
{
lean_object* v_res_4078_; 
v_res_4078_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4070_, v_xs_4071_, v_x_4072_, v___y_4073_, v___y_4074_, v___y_4075_, v___y_4076_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec(v___y_4074_);
lean_dec_ref(v___y_4073_);
lean_dec_ref(v_x_4072_);
return v_res_4078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4079_, lean_object* v_xs_4080_, lean_object* v_k_4081_, lean_object* v_a_4082_, lean_object* v_a_4083_, lean_object* v_a_4084_, lean_object* v_a_4085_){
_start:
{
lean_object* v_toCold_4087_; lean_object* v_options_4088_; uint8_t v_hasTrace_4089_; 
v_toCold_4087_ = lean_ctor_get(v_a_4084_, 0);
v_options_4088_ = lean_ctor_get(v_toCold_4087_, 2);
v_hasTrace_4089_ = lean_ctor_get_uint8(v_options_4088_, sizeof(void*)*1);
if (v_hasTrace_4089_ == 0)
{
lean_object* v___x_4090_; 
lean_dec_ref(v_xs_4080_);
lean_dec(v_f_4079_);
lean_inc(v_a_4085_);
lean_inc_ref(v_a_4084_);
lean_inc(v_a_4083_);
lean_inc_ref(v_a_4082_);
v___x_4090_ = lean_apply_5(v_k_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, lean_box(0));
return v___x_4090_;
}
else
{
lean_object* v_inheritedTraceOptions_4091_; lean_object* v___f_4092_; lean_object* v___y_4094_; lean_object* v___y_4095_; uint8_t v___y_4096_; lean_object* v___y_4120_; lean_object* v_a_4121_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; lean_object* v___y_4129_; lean_object* v___y_4130_; lean_object* v_a_4131_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v_a_4146_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; uint8_t v___y_4152_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v_a_4162_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v_a_4168_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v_a_4173_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v_a_4185_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4191_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v_a_4201_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v_a_4207_; 
v_inheritedTraceOptions_4091_ = lean_ctor_get(v_toCold_4087_, 11);
v___f_4092_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4092_, 0, v_f_4079_);
lean_closure_set(v___f_4092_, 1, v_xs_4080_);
v___x_4124_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4126_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4127_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4091_, v_options_4088_, v___x_4126_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4234_; uint8_t v___x_4235_; 
v___x_4234_ = l_Lean_trace_profiler;
v___x_4235_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4088_, v___x_4234_);
if (v___x_4235_ == 0)
{
lean_object* v___x_4236_; 
lean_dec_ref(v___f_4092_);
lean_inc(v_a_4085_);
lean_inc_ref(v_a_4084_);
lean_inc(v_a_4083_);
lean_inc_ref(v_a_4082_);
v___x_4236_ = lean_apply_5(v_k_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, lean_box(0));
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; uint8_t v___x_4240_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
v___x_4238_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4239_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4240_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4091_, v_options_4088_, v___x_4239_);
if (v___x_4240_ == 0)
{
lean_dec(v_a_4237_);
return v___x_4236_;
}
else
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
lean_dec_ref_known(v___x_4236_, 1);
lean_inc(v_a_4237_);
v___x_4241_ = l_Lean_MessageData_ofExpr(v_a_4237_);
v___x_4242_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4238_, v___x_4241_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4249_ == 0)
{
lean_object* v_unused_4250_; 
v_unused_4250_ = lean_ctor_get(v___x_4242_, 0);
lean_dec(v_unused_4250_);
v___x_4244_ = v___x_4242_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_dec(v___x_4242_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
lean_ctor_set(v___x_4244_, 0, v_a_4237_);
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4237_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
else
{
lean_object* v_a_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec(v_a_4237_);
v_a_4251_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4242_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_a_4251_);
lean_dec(v___x_4242_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
lean_inc(v_a_4251_);
if (v_isShared_4254_ == 0)
{
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_a_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
v___y_4120_ = v___x_4256_;
v_a_4121_ = v_a_4251_;
goto v___jp_4119_;
}
}
}
}
}
else
{
lean_object* v_a_4259_; 
v_a_4259_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4259_);
v___y_4120_ = v___x_4236_;
v_a_4121_ = v_a_4259_;
goto v___jp_4119_;
}
}
else
{
goto v___jp_4209_;
}
}
else
{
goto v___jp_4209_;
}
v___jp_4093_:
{
if (v___y_4096_ == 0)
{
lean_object* v___x_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
lean_dec_ref(v___y_4094_);
v___x_4097_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4098_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4099_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4091_, v_options_4088_, v___x_4098_);
if (v___x_4099_ == 0)
{
lean_object* v___x_4100_; 
v___x_4100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___y_4095_);
return v___x_4100_;
}
else
{
lean_object* v___x_4101_; lean_object* v___x_4102_; 
lean_inc_ref(v___y_4095_);
v___x_4101_ = l_Lean_Exception_toMessageData(v___y_4095_);
v___x_4102_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4097_, v___x_4101_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4109_ == 0)
{
lean_object* v_unused_4110_; 
v_unused_4110_ = lean_ctor_get(v___x_4102_, 0);
lean_dec(v_unused_4110_);
v___x_4104_ = v___x_4102_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_dec(v___x_4102_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set_tag(v___x_4104_, 1);
lean_ctor_set(v___x_4104_, 0, v___y_4095_);
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v___y_4095_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_dec_ref(v___y_4095_);
v_a_4111_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4102_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4102_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4095_);
return v___y_4094_;
}
}
v___jp_4119_:
{
uint8_t v___x_4122_; 
v___x_4122_ = l_Lean_Exception_isInterrupt(v_a_4121_);
if (v___x_4122_ == 0)
{
uint8_t v___x_4123_; 
lean_inc_ref(v_a_4121_);
v___x_4123_ = l_Lean_Exception_isRuntime(v_a_4121_);
v___y_4094_ = v___y_4120_;
v___y_4095_ = v_a_4121_;
v___y_4096_ = v___x_4123_;
goto v___jp_4093_;
}
else
{
v___y_4094_ = v___y_4120_;
v___y_4095_ = v_a_4121_;
v___y_4096_ = v___x_4122_;
goto v___jp_4093_;
}
}
v___jp_4128_:
{
lean_object* v___x_4132_; double v___x_4133_; double v___x_4134_; double v___x_4135_; double v___x_4136_; double v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v___x_4132_ = lean_io_mono_nanos_now();
v___x_4133_ = lean_float_of_nat(v___y_4129_);
v___x_4134_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4135_ = lean_float_div(v___x_4133_, v___x_4134_);
v___x_4136_ = lean_float_of_nat(v___x_4132_);
v___x_4137_ = lean_float_div(v___x_4136_, v___x_4134_);
v___x_4138_ = lean_box_float(v___x_4135_);
v___x_4139_ = lean_box_float(v___x_4137_);
v___x_4140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4141_, 0, v_a_4131_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4124_, v_hasTrace_4089_, v___x_4125_, v_options_4088_, v___x_4127_, v___y_4130_, v___f_4092_, v___x_4141_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
return v___x_4142_;
}
v___jp_4143_:
{
lean_object* v___x_4147_; 
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_a_4146_);
v___y_4129_ = v___y_4144_;
v___y_4130_ = v___y_4145_;
v_a_4131_ = v___x_4147_;
goto v___jp_4128_;
}
v___jp_4148_:
{
if (v___y_4152_ == 0)
{
lean_object* v___x_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; 
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4154_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4091_, v_options_4088_, v___x_4154_);
if (v___x_4155_ == 0)
{
v___y_4144_ = v___y_4149_;
v___y_4145_ = v___y_4151_;
v_a_4146_ = v___y_4150_;
goto v___jp_4143_;
}
else
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
lean_inc_ref(v___y_4150_);
v___x_4156_ = l_Lean_Exception_toMessageData(v___y_4150_);
v___x_4157_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4153_, v___x_4156_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_dec_ref_known(v___x_4157_, 1);
v___y_4144_ = v___y_4149_;
v___y_4145_ = v___y_4151_;
v_a_4146_ = v___y_4150_;
goto v___jp_4143_;
}
else
{
lean_object* v_a_4158_; 
lean_dec_ref(v___y_4150_);
v_a_4158_ = lean_ctor_get(v___x_4157_, 0);
lean_inc(v_a_4158_);
lean_dec_ref_known(v___x_4157_, 1);
v___y_4144_ = v___y_4149_;
v___y_4145_ = v___y_4151_;
v_a_4146_ = v_a_4158_;
goto v___jp_4143_;
}
}
}
else
{
v___y_4144_ = v___y_4149_;
v___y_4145_ = v___y_4151_;
v_a_4146_ = v___y_4150_;
goto v___jp_4143_;
}
}
v___jp_4159_:
{
uint8_t v___x_4163_; 
v___x_4163_ = l_Lean_Exception_isInterrupt(v_a_4162_);
if (v___x_4163_ == 0)
{
uint8_t v___x_4164_; 
lean_inc_ref(v_a_4162_);
v___x_4164_ = l_Lean_Exception_isRuntime(v_a_4162_);
v___y_4149_ = v___y_4160_;
v___y_4150_ = v_a_4162_;
v___y_4151_ = v___y_4161_;
v___y_4152_ = v___x_4164_;
goto v___jp_4148_;
}
else
{
v___y_4149_ = v___y_4160_;
v___y_4150_ = v_a_4162_;
v___y_4151_ = v___y_4161_;
v___y_4152_ = v___x_4163_;
goto v___jp_4148_;
}
}
v___jp_4165_:
{
lean_object* v___x_4169_; 
v___x_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4169_, 0, v_a_4168_);
v___y_4129_ = v___y_4166_;
v___y_4130_ = v___y_4167_;
v_a_4131_ = v___x_4169_;
goto v___jp_4128_;
}
v___jp_4170_:
{
lean_object* v___x_4174_; double v___x_4175_; double v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4174_ = lean_io_get_num_heartbeats();
v___x_4175_ = lean_float_of_nat(v___y_4172_);
v___x_4176_ = lean_float_of_nat(v___x_4174_);
v___x_4177_ = lean_box_float(v___x_4175_);
v___x_4178_ = lean_box_float(v___x_4176_);
v___x_4179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4180_, 0, v_a_4173_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4124_, v_hasTrace_4089_, v___x_4125_, v_options_4088_, v___x_4127_, v___y_4171_, v___f_4092_, v___x_4180_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
return v___x_4181_;
}
v___jp_4182_:
{
lean_object* v___x_4186_; 
v___x_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4186_, 0, v_a_4185_);
v___y_4171_ = v___y_4183_;
v___y_4172_ = v___y_4184_;
v_a_4173_ = v___x_4186_;
goto v___jp_4170_;
}
v___jp_4187_:
{
if (v___y_4191_ == 0)
{
lean_object* v___x_4192_; lean_object* v___x_4193_; uint8_t v___x_4194_; 
v___x_4192_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4193_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4091_, v_options_4088_, v___x_4193_);
if (v___x_4194_ == 0)
{
v___y_4183_ = v___y_4189_;
v___y_4184_ = v___y_4190_;
v_a_4185_ = v___y_4188_;
goto v___jp_4182_;
}
else
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
lean_inc_ref(v___y_4188_);
v___x_4195_ = l_Lean_Exception_toMessageData(v___y_4188_);
v___x_4196_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4192_, v___x_4195_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_dec_ref_known(v___x_4196_, 1);
v___y_4183_ = v___y_4189_;
v___y_4184_ = v___y_4190_;
v_a_4185_ = v___y_4188_;
goto v___jp_4182_;
}
else
{
lean_object* v_a_4197_; 
lean_dec_ref(v___y_4188_);
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___y_4183_ = v___y_4189_;
v___y_4184_ = v___y_4190_;
v_a_4185_ = v_a_4197_;
goto v___jp_4182_;
}
}
}
else
{
v___y_4183_ = v___y_4189_;
v___y_4184_ = v___y_4190_;
v_a_4185_ = v___y_4188_;
goto v___jp_4182_;
}
}
v___jp_4198_:
{
uint8_t v___x_4202_; 
v___x_4202_ = l_Lean_Exception_isInterrupt(v_a_4201_);
if (v___x_4202_ == 0)
{
uint8_t v___x_4203_; 
lean_inc_ref(v_a_4201_);
v___x_4203_ = l_Lean_Exception_isRuntime(v_a_4201_);
v___y_4188_ = v_a_4201_;
v___y_4189_ = v___y_4199_;
v___y_4190_ = v___y_4200_;
v___y_4191_ = v___x_4203_;
goto v___jp_4187_;
}
else
{
v___y_4188_ = v_a_4201_;
v___y_4189_ = v___y_4199_;
v___y_4190_ = v___y_4200_;
v___y_4191_ = v___x_4202_;
goto v___jp_4187_;
}
}
v___jp_4204_:
{
lean_object* v___x_4208_; 
v___x_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4208_, 0, v_a_4207_);
v___y_4171_ = v___y_4205_;
v___y_4172_ = v___y_4206_;
v_a_4173_ = v___x_4208_;
goto v___jp_4170_;
}
v___jp_4209_:
{
lean_object* v___x_4210_; lean_object* v_a_4211_; lean_object* v___x_4212_; uint8_t v___x_4213_; 
v___x_4210_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4085_);
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref(v___x_4210_);
v___x_4212_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4213_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4088_, v___x_4212_);
if (v___x_4213_ == 0)
{
lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4214_ = lean_io_mono_nanos_now();
lean_inc(v_a_4085_);
lean_inc_ref(v_a_4084_);
lean_inc(v_a_4083_);
lean_inc_ref(v_a_4082_);
v___x_4215_ = lean_apply_5(v_k_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, lean_box(0));
if (lean_obj_tag(v___x_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v_a_4216_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4216_);
lean_dec_ref_known(v___x_4215_, 1);
v___x_4217_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4218_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4219_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4091_, v_options_4088_, v___x_4218_);
if (v___x_4219_ == 0)
{
v___y_4166_ = v___x_4214_;
v___y_4167_ = v_a_4211_;
v_a_4168_ = v_a_4216_;
goto v___jp_4165_;
}
else
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
lean_inc(v_a_4216_);
v___x_4220_ = l_Lean_MessageData_ofExpr(v_a_4216_);
v___x_4221_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4217_, v___x_4220_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_dec_ref_known(v___x_4221_, 1);
v___y_4166_ = v___x_4214_;
v___y_4167_ = v_a_4211_;
v_a_4168_ = v_a_4216_;
goto v___jp_4165_;
}
else
{
lean_object* v_a_4222_; 
lean_dec(v_a_4216_);
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
v___y_4160_ = v___x_4214_;
v___y_4161_ = v_a_4211_;
v_a_4162_ = v_a_4222_;
goto v___jp_4159_;
}
}
}
else
{
lean_object* v_a_4223_; 
v_a_4223_ = lean_ctor_get(v___x_4215_, 0);
lean_inc(v_a_4223_);
lean_dec_ref_known(v___x_4215_, 1);
v___y_4160_ = v___x_4214_;
v___y_4161_ = v_a_4211_;
v_a_4162_ = v_a_4223_;
goto v___jp_4159_;
}
}
else
{
lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4224_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4085_);
lean_inc_ref(v_a_4084_);
lean_inc(v_a_4083_);
lean_inc_ref(v_a_4082_);
v___x_4225_ = lean_apply_5(v_k_4081_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_, lean_box(0));
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; uint8_t v___x_4229_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
v___x_4227_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4228_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4229_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4091_, v_options_4088_, v___x_4228_);
if (v___x_4229_ == 0)
{
v___y_4205_ = v_a_4211_;
v___y_4206_ = v___x_4224_;
v_a_4207_ = v_a_4226_;
goto v___jp_4204_;
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_inc(v_a_4226_);
v___x_4230_ = l_Lean_MessageData_ofExpr(v_a_4226_);
v___x_4231_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4227_, v___x_4230_, v_a_4082_, v_a_4083_, v_a_4084_, v_a_4085_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_dec_ref_known(v___x_4231_, 1);
v___y_4205_ = v_a_4211_;
v___y_4206_ = v___x_4224_;
v_a_4207_ = v_a_4226_;
goto v___jp_4204_;
}
else
{
lean_object* v_a_4232_; 
lean_dec(v_a_4226_);
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___y_4199_ = v_a_4211_;
v___y_4200_ = v___x_4224_;
v_a_4201_ = v_a_4232_;
goto v___jp_4198_;
}
}
}
else
{
lean_object* v_a_4233_; 
v_a_4233_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4233_);
lean_dec_ref_known(v___x_4225_, 1);
v___y_4199_ = v_a_4211_;
v___y_4200_ = v___x_4224_;
v_a_4201_ = v_a_4233_;
goto v___jp_4198_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4260_, lean_object* v_xs_4261_, lean_object* v_k_4262_, lean_object* v_a_4263_, lean_object* v_a_4264_, lean_object* v_a_4265_, lean_object* v_a_4266_, lean_object* v_a_4267_){
_start:
{
lean_object* v_res_4268_; 
v_res_4268_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4260_, v_xs_4261_, v_k_4262_, v_a_4263_, v_a_4264_, v_a_4265_, v_a_4266_);
lean_dec(v_a_4266_);
lean_dec_ref(v_a_4265_);
lean_dec(v_a_4264_);
lean_dec_ref(v_a_4263_);
return v_res_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4269_, lean_object* v_xs_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_, lean_object* v_a_4274_){
_start:
{
lean_object* v___f_4276_; uint8_t v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; 
lean_inc_ref(v_xs_4270_);
lean_inc(v_constName_4269_);
v___f_4276_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4276_, 0, v_constName_4269_);
lean_closure_set(v___f_4276_, 1, v_xs_4270_);
v___x_4277_ = 0;
v___x_4278_ = lean_box(v___x_4277_);
v___x_4279_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4279_, 0, lean_box(0));
lean_closure_set(v___x_4279_, 1, v___f_4276_);
lean_closure_set(v___x_4279_, 2, v___x_4278_);
v___x_4280_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4269_, v_xs_4270_, v___x_4279_, v_a_4271_, v_a_4272_, v_a_4273_, v_a_4274_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4281_, lean_object* v_xs_4282_, lean_object* v_a_4283_, lean_object* v_a_4284_, lean_object* v_a_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_){
_start:
{
lean_object* v_res_4288_; 
v_res_4288_ = l_Lean_Meta_mkAppOptM(v_constName_4281_, v_xs_4282_, v_a_4283_, v_a_4284_, v_a_4285_, v_a_4286_);
lean_dec(v_a_4286_);
lean_dec_ref(v_a_4285_);
lean_dec(v_a_4284_);
lean_dec_ref(v_a_4283_);
return v_res_4288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4289_, lean_object* v_xs_4290_, lean_object* v_x_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_, lean_object* v___y_4295_){
_start:
{
lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4297_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4298_ = l_Lean_MessageData_ofExpr(v_f_4289_);
v___x_4299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___x_4300_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = lean_array_to_list(v_xs_4290_);
v___x_4303_ = lean_box(0);
v___x_4304_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4302_, v___x_4303_);
v___x_4305_ = l_Lean_MessageData_ofList(v___x_4304_);
v___x_4306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4301_);
lean_ctor_set(v___x_4306_, 1, v___x_4305_);
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4308_, lean_object* v_xs_4309_, lean_object* v_x_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4308_, v_xs_4309_, v_x_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
lean_dec(v___y_4314_);
lean_dec_ref(v___y_4313_);
lean_dec(v___y_4312_);
lean_dec_ref(v___y_4311_);
lean_dec_ref(v_x_4310_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4317_, lean_object* v_xs_4318_, lean_object* v_k_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
lean_object* v_toCold_4325_; lean_object* v_options_4326_; uint8_t v_hasTrace_4327_; 
v_toCold_4325_ = lean_ctor_get(v_a_4322_, 0);
v_options_4326_ = lean_ctor_get(v_toCold_4325_, 2);
v_hasTrace_4327_ = lean_ctor_get_uint8(v_options_4326_, sizeof(void*)*1);
if (v_hasTrace_4327_ == 0)
{
lean_object* v___x_4328_; 
lean_dec_ref(v_xs_4318_);
lean_dec_ref(v_f_4317_);
lean_inc(v_a_4323_);
lean_inc_ref(v_a_4322_);
lean_inc(v_a_4321_);
lean_inc_ref(v_a_4320_);
v___x_4328_ = lean_apply_5(v_k_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, lean_box(0));
return v___x_4328_;
}
else
{
lean_object* v_inheritedTraceOptions_4329_; lean_object* v___f_4330_; lean_object* v___y_4332_; lean_object* v___y_4333_; uint8_t v___y_4334_; lean_object* v___y_4358_; lean_object* v_a_4359_; lean_object* v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v_a_4369_; lean_object* v___y_4382_; lean_object* v___y_4383_; lean_object* v_a_4384_; lean_object* v___y_4387_; lean_object* v___y_4388_; lean_object* v___y_4389_; uint8_t v___y_4390_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v_a_4400_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v_a_4406_; lean_object* v___y_4409_; lean_object* v___y_4410_; lean_object* v_a_4411_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v_a_4423_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; uint8_t v___y_4429_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v_a_4439_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v_a_4445_; 
v_inheritedTraceOptions_4329_ = lean_ctor_get(v_toCold_4325_, 11);
v___f_4330_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4330_, 0, v_f_4317_);
lean_closure_set(v___f_4330_, 1, v_xs_4318_);
v___x_4362_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4363_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4364_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4365_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4326_, v___x_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4472_; uint8_t v___x_4473_; 
v___x_4472_ = l_Lean_trace_profiler;
v___x_4473_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4326_, v___x_4472_);
if (v___x_4473_ == 0)
{
lean_object* v___x_4474_; 
lean_dec_ref(v___f_4330_);
lean_inc(v_a_4323_);
lean_inc_ref(v_a_4322_);
lean_inc(v_a_4321_);
lean_inc_ref(v_a_4320_);
v___x_4474_ = lean_apply_5(v_k_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, lean_box(0));
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; uint8_t v___x_4478_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
v___x_4476_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4477_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4478_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4326_, v___x_4477_);
if (v___x_4478_ == 0)
{
lean_dec(v_a_4475_);
return v___x_4474_;
}
else
{
lean_object* v___x_4479_; lean_object* v___x_4480_; 
lean_dec_ref_known(v___x_4474_, 1);
lean_inc(v_a_4475_);
v___x_4479_ = l_Lean_MessageData_ofExpr(v_a_4475_);
v___x_4480_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4476_, v___x_4479_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v___x_4482_; uint8_t v_isShared_4483_; uint8_t v_isSharedCheck_4487_; 
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4487_ == 0)
{
lean_object* v_unused_4488_; 
v_unused_4488_ = lean_ctor_get(v___x_4480_, 0);
lean_dec(v_unused_4488_);
v___x_4482_ = v___x_4480_;
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
else
{
lean_dec(v___x_4480_);
v___x_4482_ = lean_box(0);
v_isShared_4483_ = v_isSharedCheck_4487_;
goto v_resetjp_4481_;
}
v_resetjp_4481_:
{
lean_object* v___x_4485_; 
if (v_isShared_4483_ == 0)
{
lean_ctor_set(v___x_4482_, 0, v_a_4475_);
v___x_4485_ = v___x_4482_;
goto v_reusejp_4484_;
}
else
{
lean_object* v_reuseFailAlloc_4486_; 
v_reuseFailAlloc_4486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4475_);
v___x_4485_ = v_reuseFailAlloc_4486_;
goto v_reusejp_4484_;
}
v_reusejp_4484_:
{
return v___x_4485_;
}
}
}
else
{
lean_object* v_a_4489_; lean_object* v___x_4491_; uint8_t v_isShared_4492_; uint8_t v_isSharedCheck_4496_; 
lean_dec(v_a_4475_);
v_a_4489_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4496_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4491_ = v___x_4480_;
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
else
{
lean_inc(v_a_4489_);
lean_dec(v___x_4480_);
v___x_4491_ = lean_box(0);
v_isShared_4492_ = v_isSharedCheck_4496_;
goto v_resetjp_4490_;
}
v_resetjp_4490_:
{
lean_object* v___x_4494_; 
lean_inc(v_a_4489_);
if (v_isShared_4492_ == 0)
{
v___x_4494_ = v___x_4491_;
goto v_reusejp_4493_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v_a_4489_);
v___x_4494_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4493_;
}
v_reusejp_4493_:
{
v___y_4358_ = v___x_4494_;
v_a_4359_ = v_a_4489_;
goto v___jp_4357_;
}
}
}
}
}
else
{
lean_object* v_a_4497_; 
v_a_4497_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4497_);
v___y_4358_ = v___x_4474_;
v_a_4359_ = v_a_4497_;
goto v___jp_4357_;
}
}
else
{
goto v___jp_4447_;
}
}
else
{
goto v___jp_4447_;
}
v___jp_4331_:
{
if (v___y_4334_ == 0)
{
lean_object* v___x_4335_; lean_object* v___x_4336_; uint8_t v___x_4337_; 
lean_dec_ref(v___y_4332_);
v___x_4335_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4336_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4337_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4326_, v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
v___x_4338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4338_, 0, v___y_4333_);
return v___x_4338_;
}
else
{
lean_object* v___x_4339_; lean_object* v___x_4340_; 
lean_inc_ref(v___y_4333_);
v___x_4339_ = l_Lean_Exception_toMessageData(v___y_4333_);
v___x_4340_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4335_, v___x_4339_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
if (lean_obj_tag(v___x_4340_) == 0)
{
lean_object* v___x_4342_; uint8_t v_isShared_4343_; uint8_t v_isSharedCheck_4347_; 
v_isSharedCheck_4347_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4347_ == 0)
{
lean_object* v_unused_4348_; 
v_unused_4348_ = lean_ctor_get(v___x_4340_, 0);
lean_dec(v_unused_4348_);
v___x_4342_ = v___x_4340_;
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
else
{
lean_dec(v___x_4340_);
v___x_4342_ = lean_box(0);
v_isShared_4343_ = v_isSharedCheck_4347_;
goto v_resetjp_4341_;
}
v_resetjp_4341_:
{
lean_object* v___x_4345_; 
if (v_isShared_4343_ == 0)
{
lean_ctor_set_tag(v___x_4342_, 1);
lean_ctor_set(v___x_4342_, 0, v___y_4333_);
v___x_4345_ = v___x_4342_;
goto v_reusejp_4344_;
}
else
{
lean_object* v_reuseFailAlloc_4346_; 
v_reuseFailAlloc_4346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4346_, 0, v___y_4333_);
v___x_4345_ = v_reuseFailAlloc_4346_;
goto v_reusejp_4344_;
}
v_reusejp_4344_:
{
return v___x_4345_;
}
}
}
else
{
lean_object* v_a_4349_; lean_object* v___x_4351_; uint8_t v_isShared_4352_; uint8_t v_isSharedCheck_4356_; 
lean_dec_ref(v___y_4333_);
v_a_4349_ = lean_ctor_get(v___x_4340_, 0);
v_isSharedCheck_4356_ = !lean_is_exclusive(v___x_4340_);
if (v_isSharedCheck_4356_ == 0)
{
v___x_4351_ = v___x_4340_;
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
else
{
lean_inc(v_a_4349_);
lean_dec(v___x_4340_);
v___x_4351_ = lean_box(0);
v_isShared_4352_ = v_isSharedCheck_4356_;
goto v_resetjp_4350_;
}
v_resetjp_4350_:
{
lean_object* v___x_4354_; 
if (v_isShared_4352_ == 0)
{
v___x_4354_ = v___x_4351_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4355_; 
v_reuseFailAlloc_4355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4355_, 0, v_a_4349_);
v___x_4354_ = v_reuseFailAlloc_4355_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
return v___x_4354_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4333_);
return v___y_4332_;
}
}
v___jp_4357_:
{
uint8_t v___x_4360_; 
v___x_4360_ = l_Lean_Exception_isInterrupt(v_a_4359_);
if (v___x_4360_ == 0)
{
uint8_t v___x_4361_; 
lean_inc_ref(v_a_4359_);
v___x_4361_ = l_Lean_Exception_isRuntime(v_a_4359_);
v___y_4332_ = v___y_4358_;
v___y_4333_ = v_a_4359_;
v___y_4334_ = v___x_4361_;
goto v___jp_4331_;
}
else
{
v___y_4332_ = v___y_4358_;
v___y_4333_ = v_a_4359_;
v___y_4334_ = v___x_4360_;
goto v___jp_4331_;
}
}
v___jp_4366_:
{
lean_object* v___x_4370_; double v___x_4371_; double v___x_4372_; double v___x_4373_; double v___x_4374_; double v___x_4375_; lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4370_ = lean_io_mono_nanos_now();
v___x_4371_ = lean_float_of_nat(v___y_4368_);
v___x_4372_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4373_ = lean_float_div(v___x_4371_, v___x_4372_);
v___x_4374_ = lean_float_of_nat(v___x_4370_);
v___x_4375_ = lean_float_div(v___x_4374_, v___x_4372_);
v___x_4376_ = lean_box_float(v___x_4373_);
v___x_4377_ = lean_box_float(v___x_4375_);
v___x_4378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4376_);
lean_ctor_set(v___x_4378_, 1, v___x_4377_);
v___x_4379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4379_, 0, v_a_4369_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4362_, v_hasTrace_4327_, v___x_4363_, v_options_4326_, v___x_4365_, v___y_4367_, v___f_4330_, v___x_4379_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
return v___x_4380_;
}
v___jp_4381_:
{
lean_object* v___x_4385_; 
v___x_4385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4385_, 0, v_a_4384_);
v___y_4367_ = v___y_4383_;
v___y_4368_ = v___y_4382_;
v_a_4369_ = v___x_4385_;
goto v___jp_4366_;
}
v___jp_4386_:
{
if (v___y_4390_ == 0)
{
lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; 
v___x_4391_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4392_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4326_, v___x_4392_);
if (v___x_4393_ == 0)
{
v___y_4382_ = v___y_4388_;
v___y_4383_ = v___y_4387_;
v_a_4384_ = v___y_4389_;
goto v___jp_4381_;
}
else
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
lean_inc_ref(v___y_4389_);
v___x_4394_ = l_Lean_Exception_toMessageData(v___y_4389_);
v___x_4395_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4391_, v___x_4394_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_dec_ref_known(v___x_4395_, 1);
v___y_4382_ = v___y_4388_;
v___y_4383_ = v___y_4387_;
v_a_4384_ = v___y_4389_;
goto v___jp_4381_;
}
else
{
lean_object* v_a_4396_; 
lean_dec_ref(v___y_4389_);
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
v___y_4382_ = v___y_4388_;
v___y_4383_ = v___y_4387_;
v_a_4384_ = v_a_4396_;
goto v___jp_4381_;
}
}
}
else
{
v___y_4382_ = v___y_4388_;
v___y_4383_ = v___y_4387_;
v_a_4384_ = v___y_4389_;
goto v___jp_4381_;
}
}
v___jp_4397_:
{
uint8_t v___x_4401_; 
v___x_4401_ = l_Lean_Exception_isInterrupt(v_a_4400_);
if (v___x_4401_ == 0)
{
uint8_t v___x_4402_; 
lean_inc_ref(v_a_4400_);
v___x_4402_ = l_Lean_Exception_isRuntime(v_a_4400_);
v___y_4387_ = v___y_4399_;
v___y_4388_ = v___y_4398_;
v___y_4389_ = v_a_4400_;
v___y_4390_ = v___x_4402_;
goto v___jp_4386_;
}
else
{
v___y_4387_ = v___y_4399_;
v___y_4388_ = v___y_4398_;
v___y_4389_ = v_a_4400_;
v___y_4390_ = v___x_4401_;
goto v___jp_4386_;
}
}
v___jp_4403_:
{
lean_object* v___x_4407_; 
v___x_4407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4407_, 0, v_a_4406_);
v___y_4367_ = v___y_4405_;
v___y_4368_ = v___y_4404_;
v_a_4369_ = v___x_4407_;
goto v___jp_4366_;
}
v___jp_4408_:
{
lean_object* v___x_4412_; double v___x_4413_; double v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4412_ = lean_io_get_num_heartbeats();
v___x_4413_ = lean_float_of_nat(v___y_4410_);
v___x_4414_ = lean_float_of_nat(v___x_4412_);
v___x_4415_ = lean_box_float(v___x_4413_);
v___x_4416_ = lean_box_float(v___x_4414_);
v___x_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4415_);
lean_ctor_set(v___x_4417_, 1, v___x_4416_);
v___x_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4418_, 0, v_a_4411_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4362_, v_hasTrace_4327_, v___x_4363_, v_options_4326_, v___x_4365_, v___y_4409_, v___f_4330_, v___x_4418_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
return v___x_4419_;
}
v___jp_4420_:
{
lean_object* v___x_4424_; 
v___x_4424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4424_, 0, v_a_4423_);
v___y_4409_ = v___y_4421_;
v___y_4410_ = v___y_4422_;
v_a_4411_ = v___x_4424_;
goto v___jp_4408_;
}
v___jp_4425_:
{
if (v___y_4429_ == 0)
{
lean_object* v___x_4430_; lean_object* v___x_4431_; uint8_t v___x_4432_; 
v___x_4430_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4431_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4432_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4326_, v___x_4431_);
if (v___x_4432_ == 0)
{
v___y_4421_ = v___y_4426_;
v___y_4422_ = v___y_4428_;
v_a_4423_ = v___y_4427_;
goto v___jp_4420_;
}
else
{
lean_object* v___x_4433_; lean_object* v___x_4434_; 
lean_inc_ref(v___y_4427_);
v___x_4433_ = l_Lean_Exception_toMessageData(v___y_4427_);
v___x_4434_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4430_, v___x_4433_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
if (lean_obj_tag(v___x_4434_) == 0)
{
lean_dec_ref_known(v___x_4434_, 1);
v___y_4421_ = v___y_4426_;
v___y_4422_ = v___y_4428_;
v_a_4423_ = v___y_4427_;
goto v___jp_4420_;
}
else
{
lean_object* v_a_4435_; 
lean_dec_ref(v___y_4427_);
v_a_4435_ = lean_ctor_get(v___x_4434_, 0);
lean_inc(v_a_4435_);
lean_dec_ref_known(v___x_4434_, 1);
v___y_4421_ = v___y_4426_;
v___y_4422_ = v___y_4428_;
v_a_4423_ = v_a_4435_;
goto v___jp_4420_;
}
}
}
else
{
v___y_4421_ = v___y_4426_;
v___y_4422_ = v___y_4428_;
v_a_4423_ = v___y_4427_;
goto v___jp_4420_;
}
}
v___jp_4436_:
{
uint8_t v___x_4440_; 
v___x_4440_ = l_Lean_Exception_isInterrupt(v_a_4439_);
if (v___x_4440_ == 0)
{
uint8_t v___x_4441_; 
lean_inc_ref(v_a_4439_);
v___x_4441_ = l_Lean_Exception_isRuntime(v_a_4439_);
v___y_4426_ = v___y_4437_;
v___y_4427_ = v_a_4439_;
v___y_4428_ = v___y_4438_;
v___y_4429_ = v___x_4441_;
goto v___jp_4425_;
}
else
{
v___y_4426_ = v___y_4437_;
v___y_4427_ = v_a_4439_;
v___y_4428_ = v___y_4438_;
v___y_4429_ = v___x_4440_;
goto v___jp_4425_;
}
}
v___jp_4442_:
{
lean_object* v___x_4446_; 
v___x_4446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4446_, 0, v_a_4445_);
v___y_4409_ = v___y_4443_;
v___y_4410_ = v___y_4444_;
v_a_4411_ = v___x_4446_;
goto v___jp_4408_;
}
v___jp_4447_:
{
lean_object* v___x_4448_; lean_object* v_a_4449_; lean_object* v___x_4450_; uint8_t v___x_4451_; 
v___x_4448_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4323_);
v_a_4449_ = lean_ctor_get(v___x_4448_, 0);
lean_inc(v_a_4449_);
lean_dec_ref(v___x_4448_);
v___x_4450_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4451_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4326_, v___x_4450_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4452_; lean_object* v___x_4453_; 
v___x_4452_ = lean_io_mono_nanos_now();
lean_inc(v_a_4323_);
lean_inc_ref(v_a_4322_);
lean_inc(v_a_4321_);
lean_inc_ref(v_a_4320_);
v___x_4453_ = lean_apply_5(v_k_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, lean_box(0));
if (lean_obj_tag(v___x_4453_) == 0)
{
lean_object* v_a_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v_a_4454_ = lean_ctor_get(v___x_4453_, 0);
lean_inc(v_a_4454_);
lean_dec_ref_known(v___x_4453_, 1);
v___x_4455_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4456_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4457_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4326_, v___x_4456_);
if (v___x_4457_ == 0)
{
v___y_4404_ = v___x_4452_;
v___y_4405_ = v_a_4449_;
v_a_4406_ = v_a_4454_;
goto v___jp_4403_;
}
else
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
lean_inc(v_a_4454_);
v___x_4458_ = l_Lean_MessageData_ofExpr(v_a_4454_);
v___x_4459_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4455_, v___x_4458_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_dec_ref_known(v___x_4459_, 1);
v___y_4404_ = v___x_4452_;
v___y_4405_ = v_a_4449_;
v_a_4406_ = v_a_4454_;
goto v___jp_4403_;
}
else
{
lean_object* v_a_4460_; 
lean_dec(v_a_4454_);
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___y_4398_ = v___x_4452_;
v___y_4399_ = v_a_4449_;
v_a_4400_ = v_a_4460_;
goto v___jp_4397_;
}
}
}
else
{
lean_object* v_a_4461_; 
v_a_4461_ = lean_ctor_get(v___x_4453_, 0);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4453_, 1);
v___y_4398_ = v___x_4452_;
v___y_4399_ = v_a_4449_;
v_a_4400_ = v_a_4461_;
goto v___jp_4397_;
}
}
else
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4323_);
lean_inc_ref(v_a_4322_);
lean_inc(v_a_4321_);
lean_inc_ref(v_a_4320_);
v___x_4463_ = lean_apply_5(v_k_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, lean_box(0));
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v_a_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; uint8_t v___x_4467_; 
v_a_4464_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4464_);
lean_dec_ref_known(v___x_4463_, 1);
v___x_4465_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4466_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4467_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4329_, v_options_4326_, v___x_4466_);
if (v___x_4467_ == 0)
{
v___y_4443_ = v_a_4449_;
v___y_4444_ = v___x_4462_;
v_a_4445_ = v_a_4464_;
goto v___jp_4442_;
}
else
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
lean_inc(v_a_4464_);
v___x_4468_ = l_Lean_MessageData_ofExpr(v_a_4464_);
v___x_4469_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4465_, v___x_4468_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_dec_ref_known(v___x_4469_, 1);
v___y_4443_ = v_a_4449_;
v___y_4444_ = v___x_4462_;
v_a_4445_ = v_a_4464_;
goto v___jp_4442_;
}
else
{
lean_object* v_a_4470_; 
lean_dec(v_a_4464_);
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4470_);
lean_dec_ref_known(v___x_4469_, 1);
v___y_4437_ = v_a_4449_;
v___y_4438_ = v___x_4462_;
v_a_4439_ = v_a_4470_;
goto v___jp_4436_;
}
}
}
else
{
lean_object* v_a_4471_; 
v_a_4471_ = lean_ctor_get(v___x_4463_, 0);
lean_inc(v_a_4471_);
lean_dec_ref_known(v___x_4463_, 1);
v___y_4437_ = v_a_4449_;
v___y_4438_ = v___x_4462_;
v_a_4439_ = v_a_4471_;
goto v___jp_4436_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4498_, lean_object* v_xs_4499_, lean_object* v_k_4500_, lean_object* v_a_4501_, lean_object* v_a_4502_, lean_object* v_a_4503_, lean_object* v_a_4504_, lean_object* v_a_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4498_, v_xs_4499_, v_k_4500_, v_a_4501_, v_a_4502_, v_a_4503_, v_a_4504_);
lean_dec(v_a_4504_);
lean_dec_ref(v_a_4503_);
lean_dec(v_a_4502_);
lean_dec_ref(v_a_4501_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4507_, lean_object* v_xs_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_){
_start:
{
lean_object* v___x_4514_; 
lean_inc(v_a_4512_);
lean_inc_ref(v_a_4511_);
lean_inc(v_a_4510_);
lean_inc_ref(v_a_4509_);
lean_inc_ref(v_f_4507_);
v___x_4514_ = lean_infer_type(v_f_4507_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
if (lean_obj_tag(v___x_4514_) == 0)
{
lean_object* v_a_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; uint8_t v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; 
v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
lean_inc(v_a_4515_);
lean_dec_ref_known(v___x_4514_, 1);
v___x_4516_ = lean_unsigned_to_nat(0u);
v___x_4517_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4508_);
lean_inc_ref(v_f_4507_);
v___x_4518_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4518_, 0, v_f_4507_);
lean_closure_set(v___x_4518_, 1, v_xs_4508_);
lean_closure_set(v___x_4518_, 2, v___x_4516_);
lean_closure_set(v___x_4518_, 3, v___x_4517_);
lean_closure_set(v___x_4518_, 4, v___x_4516_);
lean_closure_set(v___x_4518_, 5, v___x_4517_);
lean_closure_set(v___x_4518_, 6, v_a_4515_);
v___x_4519_ = 0;
v___x_4520_ = lean_box(v___x_4519_);
v___x_4521_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4521_, 0, lean_box(0));
lean_closure_set(v___x_4521_, 1, v___x_4518_);
lean_closure_set(v___x_4521_, 2, v___x_4520_);
v___x_4522_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4507_, v_xs_4508_, v___x_4521_, v_a_4509_, v_a_4510_, v_a_4511_, v_a_4512_);
return v___x_4522_;
}
else
{
lean_dec_ref(v_xs_4508_);
lean_dec_ref(v_f_4507_);
return v___x_4514_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4523_, lean_object* v_xs_4524_, lean_object* v_a_4525_, lean_object* v_a_4526_, lean_object* v_a_4527_, lean_object* v_a_4528_, lean_object* v_a_4529_){
_start:
{
lean_object* v_res_4530_; 
v_res_4530_ = l_Lean_Meta_mkAppOptM_x27(v_f_4523_, v_xs_4524_, v_a_4525_, v_a_4526_, v_a_4527_, v_a_4528_);
lean_dec(v_a_4528_);
lean_dec_ref(v_a_4527_);
lean_dec(v_a_4526_);
lean_dec_ref(v_a_4525_);
return v_res_4530_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4538_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4539_ = l_Lean_MessageData_ofFormat(v___x_4538_);
return v___x_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4540_, lean_object* v_h1_4541_, lean_object* v_h2_4542_, lean_object* v_a_4543_, lean_object* v_a_4544_, lean_object* v_a_4545_, lean_object* v_a_4546_){
_start:
{
lean_object* v___x_4548_; uint8_t v___x_4549_; 
v___x_4548_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4549_ = l_Lean_Expr_isAppOf(v_h2_4542_, v___x_4548_);
if (v___x_4549_ == 0)
{
lean_object* v___x_4550_; 
lean_inc_ref(v_h2_4542_);
v___x_4550_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4542_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4550_) == 0)
{
lean_object* v_a_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; uint8_t v___x_4554_; 
v_a_4551_ = lean_ctor_get(v___x_4550_, 0);
lean_inc(v_a_4551_);
lean_dec_ref_known(v___x_4550_, 1);
v___x_4552_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4553_ = lean_unsigned_to_nat(3u);
v___x_4554_ = l_Lean_Expr_isAppOfArity(v_a_4551_, v___x_4552_, v___x_4553_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
lean_dec_ref(v_h1_4541_);
lean_dec_ref(v_motive_4540_);
v___x_4555_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4556_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4557_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4542_, v_a_4551_);
v___x_4558_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4556_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4555_, v___x_4558_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
return v___x_4559_;
}
else
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4560_ = l_Lean_Expr_appFn_x21(v_a_4551_);
v___x_4561_ = l_Lean_Expr_appFn_x21(v___x_4560_);
v___x_4562_ = l_Lean_Expr_appArg_x21(v___x_4561_);
lean_dec_ref(v___x_4561_);
lean_inc_ref(v___x_4562_);
v___x_4563_ = l_Lean_Meta_getLevel(v___x_4562_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4563_) == 0)
{
lean_object* v_a_4564_; lean_object* v___x_4565_; 
v_a_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc(v_a_4564_);
lean_dec_ref_known(v___x_4563_, 1);
lean_inc_ref(v_motive_4540_);
v___x_4565_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4540_, v_a_4543_, v_a_4544_, v_a_4545_, v_a_4546_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4601_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4568_ = v___x_4565_;
v_isShared_4569_ = v_isSharedCheck_4601_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4565_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4601_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; 
if (lean_obj_tag(v_a_4566_) == 7)
{
lean_object* v_body_4580_; 
v_body_4580_ = lean_ctor_get(v_a_4566_, 2);
lean_inc_ref(v_body_4580_);
lean_dec_ref_known(v_a_4566_, 3);
if (lean_obj_tag(v_body_4580_) == 3)
{
lean_object* v_u_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4599_; 
v_u_4581_ = lean_ctor_get(v_body_4580_, 0);
lean_inc(v_u_4581_);
lean_dec_ref_known(v_body_4580_, 1);
v___x_4582_ = l_Lean_Expr_appArg_x21(v___x_4560_);
lean_dec_ref(v___x_4560_);
v___x_4583_ = l_Lean_Expr_appArg_x21(v_a_4551_);
lean_dec(v_a_4551_);
v___x_4584_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4585_ = lean_box(0);
v___x_4586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4586_, 0, v_a_4564_);
lean_ctor_set(v___x_4586_, 1, v___x_4585_);
v___x_4587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4587_, 0, v_u_4581_);
lean_ctor_set(v___x_4587_, 1, v___x_4586_);
v___x_4588_ = l_Lean_mkConst(v___x_4584_, v___x_4587_);
v___x_4589_ = lean_unsigned_to_nat(6u);
v___x_4590_ = lean_mk_empty_array_with_capacity(v___x_4589_);
v___x_4591_ = lean_array_push(v___x_4590_, v___x_4562_);
v___x_4592_ = lean_array_push(v___x_4591_, v___x_4582_);
v___x_4593_ = lean_array_push(v___x_4592_, v_motive_4540_);
v___x_4594_ = lean_array_push(v___x_4593_, v_h1_4541_);
v___x_4595_ = lean_array_push(v___x_4594_, v___x_4583_);
v___x_4596_ = lean_array_push(v___x_4595_, v_h2_4542_);
v___x_4597_ = l_Lean_mkAppN(v___x_4588_, v___x_4596_);
lean_dec_ref(v___x_4596_);
if (v_isShared_4569_ == 0)
{
lean_ctor_set(v___x_4568_, 0, v___x_4597_);
v___x_4599_ = v___x_4568_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4597_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
else
{
lean_dec_ref(v_body_4580_);
lean_del_object(v___x_4568_);
lean_dec(v_a_4564_);
lean_dec_ref(v___x_4562_);
lean_dec_ref(v___x_4560_);
lean_dec(v_a_4551_);
lean_dec_ref(v_h2_4542_);
lean_dec_ref(v_h1_4541_);
v___y_4571_ = v_a_4543_;
v___y_4572_ = v_a_4544_;
v___y_4573_ = v_a_4545_;
v___y_4574_ = v_a_4546_;
goto v___jp_4570_;
}
}
else
{
lean_del_object(v___x_4568_);
lean_dec(v_a_4566_);
lean_dec(v_a_4564_);
lean_dec_ref(v___x_4562_);
lean_dec_ref(v___x_4560_);
lean_dec(v_a_4551_);
lean_dec_ref(v_h2_4542_);
lean_dec_ref(v_h1_4541_);
v___y_4571_ = v_a_4543_;
v___y_4572_ = v_a_4544_;
v___y_4573_ = v_a_4545_;
v___y_4574_ = v_a_4546_;
goto v___jp_4570_;
}
v___jp_4570_:
{
lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v___x_4575_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4576_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4577_ = l_Lean_indentExpr(v_motive_4540_);
v___x_4578_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4576_);
lean_ctor_set(v___x_4578_, 1, v___x_4577_);
v___x_4579_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4575_, v___x_4578_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4574_);
return v___x_4579_;
}
}
}
else
{
lean_dec(v_a_4564_);
lean_dec_ref(v___x_4562_);
lean_dec_ref(v___x_4560_);
lean_dec(v_a_4551_);
lean_dec_ref(v_h2_4542_);
lean_dec_ref(v_h1_4541_);
lean_dec_ref(v_motive_4540_);
return v___x_4565_;
}
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4609_; 
lean_dec_ref(v___x_4562_);
lean_dec_ref(v___x_4560_);
lean_dec(v_a_4551_);
lean_dec_ref(v_h2_4542_);
lean_dec_ref(v_h1_4541_);
lean_dec_ref(v_motive_4540_);
v_a_4602_ = lean_ctor_get(v___x_4563_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4604_ = v___x_4563_;
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4563_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4542_);
lean_dec_ref(v_h1_4541_);
lean_dec_ref(v_motive_4540_);
return v___x_4550_;
}
}
else
{
lean_object* v___x_4610_; 
lean_dec_ref(v_h2_4542_);
lean_dec_ref(v_motive_4540_);
v___x_4610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4610_, 0, v_h1_4541_);
return v___x_4610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4611_, lean_object* v_h1_4612_, lean_object* v_h2_4613_, lean_object* v_a_4614_, lean_object* v_a_4615_, lean_object* v_a_4616_, lean_object* v_a_4617_, lean_object* v_a_4618_){
_start:
{
lean_object* v_res_4619_; 
v_res_4619_ = l_Lean_Meta_mkEqNDRec(v_motive_4611_, v_h1_4612_, v_h2_4613_, v_a_4614_, v_a_4615_, v_a_4616_, v_a_4617_);
lean_dec(v_a_4617_);
lean_dec_ref(v_a_4616_);
lean_dec(v_a_4615_);
lean_dec_ref(v_a_4614_);
return v_res_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4624_, lean_object* v_h1_4625_, lean_object* v_h2_4626_, lean_object* v_a_4627_, lean_object* v_a_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_){
_start:
{
lean_object* v___x_4632_; uint8_t v___x_4633_; 
v___x_4632_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4633_ = l_Lean_Expr_isAppOf(v_h2_4626_, v___x_4632_);
if (v___x_4633_ == 0)
{
lean_object* v___x_4634_; 
lean_inc_ref(v_h2_4626_);
v___x_4634_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4626_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; uint8_t v___x_4638_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
lean_inc(v_a_4635_);
lean_dec_ref_known(v___x_4634_, 1);
v___x_4636_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4637_ = lean_unsigned_to_nat(3u);
v___x_4638_ = l_Lean_Expr_isAppOfArity(v_a_4635_, v___x_4636_, v___x_4637_);
if (v___x_4638_ == 0)
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
lean_dec(v_a_4635_);
lean_dec_ref(v_h1_4625_);
lean_dec_ref(v_motive_4624_);
v___x_4639_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4640_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4641_ = l_Lean_indentExpr(v_h2_4626_);
v___x_4642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4642_, 0, v___x_4640_);
lean_ctor_set(v___x_4642_, 1, v___x_4641_);
v___x_4643_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4639_, v___x_4642_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
return v___x_4643_;
}
else
{
lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4644_ = l_Lean_Expr_appFn_x21(v_a_4635_);
v___x_4645_ = l_Lean_Expr_appFn_x21(v___x_4644_);
v___x_4646_ = l_Lean_Expr_appArg_x21(v___x_4645_);
lean_dec_ref(v___x_4645_);
lean_inc_ref(v___x_4646_);
v___x_4647_ = l_Lean_Meta_getLevel(v___x_4646_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v_a_4648_; lean_object* v___x_4649_; 
v_a_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc(v_a_4648_);
lean_dec_ref_known(v___x_4647_, 1);
lean_inc_ref(v_motive_4624_);
v___x_4649_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4624_, v_a_4627_, v_a_4628_, v_a_4629_, v_a_4630_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4686_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4652_ = v___x_4649_;
v_isShared_4653_ = v_isSharedCheck_4686_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4649_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4686_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; 
if (lean_obj_tag(v_a_4650_) == 7)
{
lean_object* v_body_4664_; 
v_body_4664_ = lean_ctor_get(v_a_4650_, 2);
lean_inc_ref(v_body_4664_);
lean_dec_ref_known(v_a_4650_, 3);
if (lean_obj_tag(v_body_4664_) == 7)
{
lean_object* v_body_4665_; 
v_body_4665_ = lean_ctor_get(v_body_4664_, 2);
lean_inc_ref(v_body_4665_);
lean_dec_ref_known(v_body_4664_, 3);
if (lean_obj_tag(v_body_4665_) == 3)
{
lean_object* v_u_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4684_; 
v_u_4666_ = lean_ctor_get(v_body_4665_, 0);
lean_inc(v_u_4666_);
lean_dec_ref_known(v_body_4665_, 1);
v___x_4667_ = l_Lean_Expr_appArg_x21(v___x_4644_);
lean_dec_ref(v___x_4644_);
v___x_4668_ = l_Lean_Expr_appArg_x21(v_a_4635_);
lean_dec(v_a_4635_);
v___x_4669_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4670_ = lean_box(0);
v___x_4671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4671_, 0, v_a_4648_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
v___x_4672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4672_, 0, v_u_4666_);
lean_ctor_set(v___x_4672_, 1, v___x_4671_);
v___x_4673_ = l_Lean_mkConst(v___x_4669_, v___x_4672_);
v___x_4674_ = lean_unsigned_to_nat(6u);
v___x_4675_ = lean_mk_empty_array_with_capacity(v___x_4674_);
v___x_4676_ = lean_array_push(v___x_4675_, v___x_4646_);
v___x_4677_ = lean_array_push(v___x_4676_, v___x_4667_);
v___x_4678_ = lean_array_push(v___x_4677_, v_motive_4624_);
v___x_4679_ = lean_array_push(v___x_4678_, v_h1_4625_);
v___x_4680_ = lean_array_push(v___x_4679_, v___x_4668_);
v___x_4681_ = lean_array_push(v___x_4680_, v_h2_4626_);
v___x_4682_ = l_Lean_mkAppN(v___x_4673_, v___x_4681_);
lean_dec_ref(v___x_4681_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v___x_4682_);
v___x_4684_ = v___x_4652_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
else
{
lean_dec_ref(v_body_4665_);
lean_del_object(v___x_4652_);
lean_dec(v_a_4648_);
lean_dec_ref(v___x_4646_);
lean_dec_ref(v___x_4644_);
lean_dec(v_a_4635_);
lean_dec_ref(v_h2_4626_);
lean_dec_ref(v_h1_4625_);
v___y_4655_ = v_a_4627_;
v___y_4656_ = v_a_4628_;
v___y_4657_ = v_a_4629_;
v___y_4658_ = v_a_4630_;
goto v___jp_4654_;
}
}
else
{
lean_dec_ref(v_body_4664_);
lean_del_object(v___x_4652_);
lean_dec(v_a_4648_);
lean_dec_ref(v___x_4646_);
lean_dec_ref(v___x_4644_);
lean_dec(v_a_4635_);
lean_dec_ref(v_h2_4626_);
lean_dec_ref(v_h1_4625_);
v___y_4655_ = v_a_4627_;
v___y_4656_ = v_a_4628_;
v___y_4657_ = v_a_4629_;
v___y_4658_ = v_a_4630_;
goto v___jp_4654_;
}
}
else
{
lean_del_object(v___x_4652_);
lean_dec(v_a_4650_);
lean_dec(v_a_4648_);
lean_dec_ref(v___x_4646_);
lean_dec_ref(v___x_4644_);
lean_dec(v_a_4635_);
lean_dec_ref(v_h2_4626_);
lean_dec_ref(v_h1_4625_);
v___y_4655_ = v_a_4627_;
v___y_4656_ = v_a_4628_;
v___y_4657_ = v_a_4629_;
v___y_4658_ = v_a_4630_;
goto v___jp_4654_;
}
v___jp_4654_:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4659_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4660_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4661_ = l_Lean_indentExpr(v_motive_4624_);
v___x_4662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4660_);
lean_ctor_set(v___x_4662_, 1, v___x_4661_);
v___x_4663_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4659_, v___x_4662_, v___y_4655_, v___y_4656_, v___y_4657_, v___y_4658_);
return v___x_4663_;
}
}
}
else
{
lean_dec(v_a_4648_);
lean_dec_ref(v___x_4646_);
lean_dec_ref(v___x_4644_);
lean_dec(v_a_4635_);
lean_dec_ref(v_h2_4626_);
lean_dec_ref(v_h1_4625_);
lean_dec_ref(v_motive_4624_);
return v___x_4649_;
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v___x_4646_);
lean_dec_ref(v___x_4644_);
lean_dec(v_a_4635_);
lean_dec_ref(v_h2_4626_);
lean_dec_ref(v_h1_4625_);
lean_dec_ref(v_motive_4624_);
v_a_4687_ = lean_ctor_get(v___x_4647_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4647_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4647_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4647_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4626_);
lean_dec_ref(v_h1_4625_);
lean_dec_ref(v_motive_4624_);
return v___x_4634_;
}
}
else
{
lean_object* v___x_4695_; 
lean_dec_ref(v_h2_4626_);
lean_dec_ref(v_motive_4624_);
v___x_4695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4695_, 0, v_h1_4625_);
return v___x_4695_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4696_, lean_object* v_h1_4697_, lean_object* v_h2_4698_, lean_object* v_a_4699_, lean_object* v_a_4700_, lean_object* v_a_4701_, lean_object* v_a_4702_, lean_object* v_a_4703_){
_start:
{
lean_object* v_res_4704_; 
v_res_4704_ = l_Lean_Meta_mkEqRec(v_motive_4696_, v_h1_4697_, v_h2_4698_, v_a_4699_, v_a_4700_, v_a_4701_, v_a_4702_);
lean_dec(v_a_4702_);
lean_dec_ref(v_a_4701_);
lean_dec(v_a_4700_);
lean_dec_ref(v_a_4699_);
return v_res_4704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4709_, lean_object* v_pr_4710_, lean_object* v_a_4711_, lean_object* v_a_4712_, lean_object* v_a_4713_, lean_object* v_a_4714_){
_start:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v___x_4716_ = ((lean_object*)(l_Lean_Meta_mkEqMP___closed__1));
v___x_4717_ = lean_unsigned_to_nat(2u);
v___x_4718_ = lean_mk_empty_array_with_capacity(v___x_4717_);
v___x_4719_ = lean_array_push(v___x_4718_, v_eqProof_4709_);
v___x_4720_ = lean_array_push(v___x_4719_, v_pr_4710_);
v___x_4721_ = l_Lean_Meta_mkAppM(v___x_4716_, v___x_4720_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_);
return v___x_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4722_, lean_object* v_pr_4723_, lean_object* v_a_4724_, lean_object* v_a_4725_, lean_object* v_a_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_){
_start:
{
lean_object* v_res_4729_; 
v_res_4729_ = l_Lean_Meta_mkEqMP(v_eqProof_4722_, v_pr_4723_, v_a_4724_, v_a_4725_, v_a_4726_, v_a_4727_);
lean_dec(v_a_4727_);
lean_dec_ref(v_a_4726_);
lean_dec(v_a_4725_);
lean_dec_ref(v_a_4724_);
return v_res_4729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4734_, lean_object* v_pr_4735_, lean_object* v_a_4736_, lean_object* v_a_4737_, lean_object* v_a_4738_, lean_object* v_a_4739_){
_start:
{
lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; 
v___x_4741_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4742_ = lean_unsigned_to_nat(2u);
v___x_4743_ = lean_mk_empty_array_with_capacity(v___x_4742_);
v___x_4744_ = lean_array_push(v___x_4743_, v_eqProof_4734_);
v___x_4745_ = lean_array_push(v___x_4744_, v_pr_4735_);
v___x_4746_ = l_Lean_Meta_mkAppM(v___x_4741_, v___x_4745_, v_a_4736_, v_a_4737_, v_a_4738_, v_a_4739_);
return v___x_4746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4747_, lean_object* v_pr_4748_, lean_object* v_a_4749_, lean_object* v_a_4750_, lean_object* v_a_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_){
_start:
{
lean_object* v_res_4754_; 
v_res_4754_ = l_Lean_Meta_mkEqMPR(v_eqProof_4747_, v_pr_4748_, v_a_4749_, v_a_4750_, v_a_4751_, v_a_4752_);
lean_dec(v_a_4752_);
lean_dec_ref(v_a_4751_);
lean_dec(v_a_4750_);
lean_dec_ref(v_a_4749_);
return v_res_4754_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_){
_start:
{
lean_object* v___f_4761_; lean_object* v___x_12328__overap_4762_; lean_object* v___x_4763_; 
v___f_4761_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12328__overap_4762_ = lean_panic_fn_borrowed(v___f_4761_, v_msg_4755_);
lean_inc(v___y_4759_);
lean_inc_ref(v___y_4758_);
lean_inc(v___y_4757_);
lean_inc_ref(v___y_4756_);
v___x_4763_ = lean_apply_5(v___x_12328__overap_4762_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_, lean_box(0));
return v___x_4763_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v_res_4770_; 
v_res_4770_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4764_, v___y_4765_, v___y_4766_, v___y_4767_, v___y_4768_);
lean_dec(v___y_4768_);
lean_dec_ref(v___y_4767_);
lean_dec(v___y_4766_);
lean_dec_ref(v___y_4765_);
return v_res_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4771_, uint8_t v_skipRealize_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v___x_4775_; lean_object* v_env_4776_; uint8_t v___x_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; 
v___x_4775_ = lean_st_ref_get(v___y_4773_);
v_env_4776_ = lean_ctor_get(v___x_4775_, 0);
lean_inc_ref(v_env_4776_);
lean_dec(v___x_4775_);
v___x_4777_ = l_Lean_Environment_contains(v_env_4776_, v_constName_4771_, v_skipRealize_4772_);
v___x_4778_ = lean_box(v___x_4777_);
v___x_4779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4779_, 0, v___x_4778_);
return v___x_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4780_, lean_object* v_skipRealize_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
uint8_t v_skipRealize_boxed_4784_; lean_object* v_res_4785_; 
v_skipRealize_boxed_4784_ = lean_unbox(v_skipRealize_4781_);
v_res_4785_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4780_, v_skipRealize_boxed_4784_, v___y_4782_);
lean_dec(v___y_4782_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4786_, uint8_t v_skipRealize_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v___x_4793_; 
v___x_4793_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4786_, v_skipRealize_4787_, v___y_4791_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4794_, lean_object* v_skipRealize_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_){
_start:
{
uint8_t v_skipRealize_boxed_4801_; lean_object* v_res_4802_; 
v_skipRealize_boxed_4801_ = lean_unbox(v_skipRealize_4795_);
v_res_4802_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4794_, v_skipRealize_boxed_4801_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_);
lean_dec(v___y_4799_);
lean_dec_ref(v___y_4798_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___y_4803_, uint8_t v___x_4804_, lean_object* v_P_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v___x_4811_; lean_object* v___x_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; lean_object* v___x_4815_; 
v___x_4811_ = lean_unsigned_to_nat(1u);
v___x_4812_ = lean_mk_empty_array_with_capacity(v___x_4811_);
lean_inc_ref(v_P_4805_);
v___x_4813_ = lean_array_push(v___x_4812_, v_P_4805_);
v___x_4814_ = 1;
v___x_4815_ = l_Lean_Meta_mkLambdaFVars(v___x_4813_, v_P_4805_, v___y_4803_, v___x_4804_, v___y_4803_, v___x_4804_, v___x_4814_, v___y_4806_, v___y_4807_, v___y_4808_, v___y_4809_);
lean_dec_ref(v___x_4813_);
return v___x_4815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___y_4816_, lean_object* v___x_4817_, lean_object* v_P_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_, lean_object* v___y_4823_){
_start:
{
uint8_t v___y_13571__boxed_4824_; uint8_t v___x_13572__boxed_4825_; lean_object* v_res_4826_; 
v___y_13571__boxed_4824_ = lean_unbox(v___y_4816_);
v___x_13572__boxed_4825_ = lean_unbox(v___x_4817_);
v_res_4826_ = l_Lean_Meta_mkNoConfusion___lam__0(v___y_13571__boxed_4824_, v___x_13572__boxed_4825_, v_P_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_);
lean_dec(v___y_4822_);
lean_dec_ref(v___y_4821_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
return v_res_4826_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4828_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4829_ = l_Lean_stringToMessageData(v___x_4828_);
return v___x_4829_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4831_; lean_object* v___x_4832_; 
v___x_4831_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4832_ = l_Lean_stringToMessageData(v___x_4831_);
return v___x_4832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4833_, lean_object* v_b_4834_, lean_object* v_i_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v_stop_4841_; lean_object* v_step_4842_; lean_object* v_a_4844_; uint8_t v___x_4847_; 
v_stop_4841_ = lean_ctor_get(v_range_4833_, 1);
v_step_4842_ = lean_ctor_get(v_range_4833_, 2);
v___x_4847_ = lean_nat_dec_lt(v_i_4835_, v_stop_4841_);
if (v___x_4847_ == 0)
{
lean_object* v___x_4848_; 
lean_dec(v_i_4835_);
v___x_4848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4848_, 0, v_b_4834_);
return v___x_4848_;
}
else
{
lean_object* v___x_4849_; 
lean_inc(v___y_4839_);
lean_inc_ref(v___y_4838_);
lean_inc(v___y_4837_);
lean_inc_ref(v___y_4836_);
lean_inc_ref(v_b_4834_);
v___x_4849_ = lean_infer_type(v_b_4834_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4849_) == 0)
{
lean_object* v_a_4850_; lean_object* v___x_4851_; 
v_a_4850_ = lean_ctor_get(v___x_4849_, 0);
lean_inc(v_a_4850_);
lean_dec_ref_known(v___x_4849_, 1);
v___x_4851_ = l_Lean_Meta_whnfForall(v_a_4850_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4851_) == 0)
{
lean_object* v_a_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc(v_a_4852_);
lean_dec_ref_known(v___x_4851_, 1);
v___x_4853_ = l_Lean_Expr_bindingDomain_x21(v_a_4852_);
lean_dec(v_a_4852_);
lean_inc(v___y_4839_);
lean_inc_ref(v___y_4838_);
lean_inc(v___y_4837_);
lean_inc_ref(v___y_4836_);
v___x_4854_ = lean_whnf(v___x_4853_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4854_) == 0)
{
lean_object* v_a_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; uint8_t v___x_4858_; 
v_a_4855_ = lean_ctor_get(v___x_4854_, 0);
lean_inc(v_a_4855_);
lean_dec_ref_known(v___x_4854_, 1);
v___x_4856_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4857_ = lean_unsigned_to_nat(4u);
v___x_4858_ = l_Lean_Expr_isAppOfArity(v_a_4855_, v___x_4856_, v___x_4857_);
if (v___x_4858_ == 0)
{
lean_object* v___x_4859_; lean_object* v___x_4860_; uint8_t v___x_4861_; 
v___x_4859_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4860_ = lean_unsigned_to_nat(3u);
v___x_4861_ = l_Lean_Expr_isAppOfArity(v_a_4855_, v___x_4859_, v___x_4860_);
if (v___x_4861_ == 0)
{
lean_object* v___x_4862_; 
lean_dec(v_i_4835_);
lean_inc(v___y_4839_);
lean_inc_ref(v___y_4838_);
lean_inc(v___y_4837_);
lean_inc_ref(v___y_4836_);
v___x_4862_ = lean_infer_type(v_b_4834_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref_known(v___x_4862_, 1);
v___x_4864_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4865_ = l_Lean_MessageData_ofExpr(v_a_4855_);
v___x_4866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4864_);
lean_ctor_set(v___x_4866_, 1, v___x_4865_);
v___x_4867_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4868_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4867_);
v___x_4869_ = lean_unsigned_to_nat(30u);
v___x_4870_ = l_Lean_inlineExpr(v_a_4863_, v___x_4869_);
v___x_4871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4868_);
lean_ctor_set(v___x_4871_, 1, v___x_4870_);
v___x_4872_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4871_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4872_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4875_ = v___x_4872_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4872_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
else
{
lean_dec(v_a_4855_);
return v___x_4862_;
}
}
else
{
lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; 
v___x_4881_ = l_Lean_Expr_appFn_x21(v_a_4855_);
lean_dec(v_a_4855_);
v___x_4882_ = l_Lean_Expr_appArg_x21(v___x_4881_);
lean_dec_ref(v___x_4881_);
v___x_4883_ = l_Lean_Meta_mkEqRefl(v___x_4882_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4883_) == 0)
{
lean_object* v_a_4884_; lean_object* v___x_4885_; 
v_a_4884_ = lean_ctor_get(v___x_4883_, 0);
lean_inc(v_a_4884_);
lean_dec_ref_known(v___x_4883_, 1);
v___x_4885_ = l_Lean_Expr_app___override(v_b_4834_, v_a_4884_);
v_a_4844_ = v___x_4885_;
goto v___jp_4843_;
}
else
{
lean_dec(v_i_4835_);
lean_dec_ref(v_b_4834_);
return v___x_4883_;
}
}
}
else
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4886_ = l_Lean_Expr_appFn_x21(v_a_4855_);
lean_dec(v_a_4855_);
v___x_4887_ = l_Lean_Expr_appFn_x21(v___x_4886_);
lean_dec_ref(v___x_4886_);
v___x_4888_ = l_Lean_Expr_appArg_x21(v___x_4887_);
lean_dec_ref(v___x_4887_);
v___x_4889_ = l_Lean_Meta_mkHEqRefl(v___x_4888_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4891_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v___x_4891_ = l_Lean_Expr_app___override(v_b_4834_, v_a_4890_);
v_a_4844_ = v___x_4891_;
goto v___jp_4843_;
}
else
{
lean_dec(v_i_4835_);
lean_dec_ref(v_b_4834_);
return v___x_4889_;
}
}
}
else
{
lean_dec(v_i_4835_);
lean_dec_ref(v_b_4834_);
return v___x_4854_;
}
}
else
{
lean_dec(v_i_4835_);
lean_dec_ref(v_b_4834_);
return v___x_4851_;
}
}
else
{
lean_dec(v_i_4835_);
lean_dec_ref(v_b_4834_);
return v___x_4849_;
}
}
v___jp_4843_:
{
lean_object* v___x_4845_; 
v___x_4845_ = lean_nat_add(v_i_4835_, v_step_4842_);
lean_dec(v_i_4835_);
v_b_4834_ = v_a_4844_;
v_i_4835_ = v___x_4845_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4892_, lean_object* v_b_4893_, lean_object* v_i_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_){
_start:
{
lean_object* v_res_4900_; 
v_res_4900_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4892_, v_b_4893_, v_i_4894_, v___y_4895_, v___y_4896_, v___y_4897_, v___y_4898_);
lean_dec(v___y_4898_);
lean_dec_ref(v___y_4897_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
lean_dec_ref(v_range_4892_);
return v_res_4900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4901_, lean_object* v_b_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
lean_object* v___x_4908_; 
lean_inc(v___y_4906_);
lean_inc_ref(v___y_4905_);
lean_inc(v___y_4904_);
lean_inc_ref(v___y_4903_);
v___x_4908_ = lean_apply_6(v_k_4901_, v_b_4902_, v___y_4903_, v___y_4904_, v___y_4905_, v___y_4906_, lean_box(0));
return v___x_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4909_, lean_object* v_b_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_){
_start:
{
lean_object* v_res_4916_; 
v_res_4916_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4909_, v_b_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_);
lean_dec(v___y_4914_);
lean_dec_ref(v___y_4913_);
lean_dec(v___y_4912_);
lean_dec_ref(v___y_4911_);
return v_res_4916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4917_, uint8_t v_bi_4918_, lean_object* v_type_4919_, lean_object* v_k_4920_, uint8_t v_kind_4921_, lean_object* v___y_4922_, lean_object* v___y_4923_, lean_object* v___y_4924_, lean_object* v___y_4925_){
_start:
{
lean_object* v___f_4927_; lean_object* v___x_4928_; 
v___f_4927_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4927_, 0, v_k_4920_);
v___x_4928_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4917_, v_bi_4918_, v_type_4919_, v___f_4927_, v_kind_4921_, v___y_4922_, v___y_4923_, v___y_4924_, v___y_4925_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4936_ == 0)
{
v___x_4931_ = v___x_4928_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_a_4929_);
lean_dec(v___x_4928_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v_a_4929_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
else
{
lean_object* v_a_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4944_; 
v_a_4937_ = lean_ctor_get(v___x_4928_, 0);
v_isSharedCheck_4944_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4944_ == 0)
{
v___x_4939_ = v___x_4928_;
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_a_4937_);
lean_dec(v___x_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4944_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4942_; 
if (v_isShared_4940_ == 0)
{
v___x_4942_ = v___x_4939_;
goto v_reusejp_4941_;
}
else
{
lean_object* v_reuseFailAlloc_4943_; 
v_reuseFailAlloc_4943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4943_, 0, v_a_4937_);
v___x_4942_ = v_reuseFailAlloc_4943_;
goto v_reusejp_4941_;
}
v_reusejp_4941_:
{
return v___x_4942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_4945_, lean_object* v_bi_4946_, lean_object* v_type_4947_, lean_object* v_k_4948_, lean_object* v_kind_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_, lean_object* v___y_4954_){
_start:
{
uint8_t v_bi_boxed_4955_; uint8_t v_kind_boxed_4956_; lean_object* v_res_4957_; 
v_bi_boxed_4955_ = lean_unbox(v_bi_4946_);
v_kind_boxed_4956_ = lean_unbox(v_kind_4949_);
v_res_4957_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4945_, v_bi_boxed_4955_, v_type_4947_, v_k_4948_, v_kind_boxed_4956_, v___y_4950_, v___y_4951_, v___y_4952_, v___y_4953_);
lean_dec(v___y_4953_);
lean_dec_ref(v___y_4952_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_4958_, lean_object* v_type_4959_, lean_object* v_k_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_){
_start:
{
uint8_t v___x_4966_; uint8_t v___x_4967_; lean_object* v___x_4968_; 
v___x_4966_ = 0;
v___x_4967_ = 0;
v___x_4968_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4958_, v___x_4966_, v_type_4959_, v_k_4960_, v___x_4967_, v___y_4961_, v___y_4962_, v___y_4963_, v___y_4964_);
return v___x_4968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_4969_, lean_object* v_type_4970_, lean_object* v_k_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_4969_, v_type_4970_, v_k_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
return v_res_4977_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4984_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_4985_ = l_Lean_MessageData_ofFormat(v___x_4984_);
return v___x_4985_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__7(void){
_start:
{
lean_object* v___x_4989_; lean_object* v___x_4990_; 
v___x_4989_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__6));
v___x_4990_ = l_Lean_MessageData_ofFormat(v___x_4989_);
return v___x_4990_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__9(void){
_start:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; 
v___x_4992_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__8));
v___x_4993_ = l_Lean_stringToMessageData(v___x_4992_);
return v___x_4993_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_4995_; lean_object* v___x_4996_; 
v___x_4995_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_4996_ = l_Lean_stringToMessageData(v___x_4995_);
return v___x_4996_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__14(void){
_start:
{
lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; 
v___x_4999_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__13));
v___x_5000_ = lean_unsigned_to_nat(10u);
v___x_5001_ = lean_unsigned_to_nat(490u);
v___x_5002_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5003_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5004_ = l_mkPanicMessageWithDecl(v___x_5003_, v___x_5002_, v___x_5001_, v___x_5000_, v___x_4999_);
return v___x_5004_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5007_ = l_Lean_stringToMessageData(v___x_5006_);
return v___x_5007_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__23(void){
_start:
{
lean_object* v___x_5016_; lean_object* v___x_5017_; 
v___x_5016_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__22));
v___x_5017_ = l_Lean_stringToMessageData(v___x_5016_);
return v___x_5017_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__24(void){
_start:
{
lean_object* v___x_5018_; lean_object* v___x_5019_; 
v___x_5018_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5019_ = l_Lean_MessageData_ofName(v___x_5018_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5020_, lean_object* v_h_5021_, lean_object* v_a_5022_, lean_object* v_a_5023_, lean_object* v_a_5024_, lean_object* v_a_5025_){
_start:
{
lean_object* v___x_5027_; 
lean_inc(v_a_5025_);
lean_inc_ref(v_a_5024_);
lean_inc(v_a_5023_);
lean_inc_ref(v_a_5022_);
lean_inc_ref(v_h_5021_);
v___x_5027_ = lean_infer_type(v_h_5021_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5027_) == 0)
{
lean_object* v_a_5028_; lean_object* v___x_5029_; 
v_a_5028_ = lean_ctor_get(v___x_5027_, 0);
lean_inc(v_a_5028_);
lean_dec_ref_known(v___x_5027_, 1);
lean_inc(v_a_5025_);
lean_inc_ref(v_a_5024_);
lean_inc(v_a_5023_);
lean_inc_ref(v_a_5022_);
v___x_5029_ = lean_whnf(v_a_5028_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; lean_object* v___x_5031_; lean_object* v___x_5032_; uint8_t v___x_5033_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref_known(v___x_5029_, 1);
v___x_5031_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5032_ = lean_unsigned_to_nat(3u);
v___x_5033_ = l_Lean_Expr_isAppOfArity(v_a_5030_, v___x_5031_, v___x_5032_);
if (v___x_5033_ == 0)
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_dec_ref(v_target_5020_);
v___x_5034_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5035_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5036_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5021_, v_a_5030_);
v___x_5037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5037_, 0, v___x_5035_);
lean_ctor_set(v___x_5037_, 1, v___x_5036_);
v___x_5038_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5034_, v___x_5037_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
return v___x_5038_;
}
else
{
lean_object* v___x_5039_; lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; 
v___x_5039_ = l_Lean_Expr_appFn_x21(v_a_5030_);
v___x_5040_ = l_Lean_Expr_appFn_x21(v___x_5039_);
v___x_5041_ = l_Lean_Expr_appArg_x21(v___x_5040_);
lean_dec_ref(v___x_5040_);
v___x_5042_ = l_Lean_Meta_whnfD(v___x_5041_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5042_) == 0)
{
lean_object* v_a_5043_; lean_object* v___y_5045_; lean_object* v___y_5046_; lean_object* v___y_5047_; lean_object* v___y_5048_; lean_object* v___x_5054_; 
v_a_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc(v_a_5043_);
lean_dec_ref_known(v___x_5042_, 1);
v___x_5054_ = l_Lean_Expr_getAppFn(v_a_5043_);
if (lean_obj_tag(v___x_5054_) == 4)
{
lean_object* v_declName_5055_; lean_object* v_us_5056_; lean_object* v___x_5057_; lean_object* v_env_5058_; uint8_t v___x_5059_; lean_object* v___x_5060_; 
v_declName_5055_ = lean_ctor_get(v___x_5054_, 0);
lean_inc(v_declName_5055_);
v_us_5056_ = lean_ctor_get(v___x_5054_, 1);
lean_inc(v_us_5056_);
lean_dec_ref_known(v___x_5054_, 2);
v___x_5057_ = lean_st_ref_get(v_a_5025_);
v_env_5058_ = lean_ctor_get(v___x_5057_, 0);
lean_inc_ref(v_env_5058_);
lean_dec(v___x_5057_);
v___x_5059_ = 0;
v___x_5060_ = l_Lean_Environment_find_x3f(v_env_5058_, v_declName_5055_, v___x_5059_);
if (lean_obj_tag(v___x_5060_) == 0)
{
lean_dec(v_us_5056_);
lean_dec_ref(v___x_5039_);
lean_dec(v_a_5030_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v___y_5045_ = v_a_5022_;
v___y_5046_ = v_a_5023_;
v___y_5047_ = v_a_5024_;
v___y_5048_ = v_a_5025_;
goto v___jp_5044_;
}
else
{
lean_object* v_val_5061_; 
v_val_5061_ = lean_ctor_get(v___x_5060_, 0);
lean_inc(v_val_5061_);
lean_dec_ref_known(v___x_5060_, 1);
if (lean_obj_tag(v_val_5061_) == 5)
{
lean_object* v_val_5062_; lean_object* v___x_5063_; 
v_val_5062_ = lean_ctor_get(v_val_5061_, 0);
lean_inc_ref(v_val_5062_);
lean_dec_ref_known(v_val_5061_, 1);
lean_inc_ref(v_target_5020_);
v___x_5063_ = l_Lean_Meta_getLevel(v_target_5020_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; lean_object* v___x_5065_; lean_object* v___x_5066_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5063_, 1);
v___x_5065_ = l_Lean_Expr_appArg_x21(v___x_5039_);
lean_dec_ref(v___x_5039_);
lean_inc_ref(v___x_5065_);
v___x_5066_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5065_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5066_) == 0)
{
lean_object* v_a_5067_; lean_object* v___x_5068_; lean_object* v___y_5070_; lean_object* v___y_5071_; lean_object* v___y_5072_; lean_object* v___y_5073_; 
v_a_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc(v_a_5067_);
lean_dec_ref_known(v___x_5066_, 1);
v___x_5068_ = l_Lean_Expr_appArg_x21(v_a_5030_);
lean_dec(v_a_5030_);
if (lean_obj_tag(v_a_5067_) == 1)
{
lean_object* v_val_5082_; lean_object* v_fst_5083_; lean_object* v_snd_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5298_; 
v_val_5082_ = lean_ctor_get(v_a_5067_, 0);
lean_inc(v_val_5082_);
lean_dec_ref_known(v_a_5067_, 1);
v_fst_5083_ = lean_ctor_get(v_val_5082_, 0);
v_snd_5084_ = lean_ctor_get(v_val_5082_, 1);
v_isSharedCheck_5298_ = !lean_is_exclusive(v_val_5082_);
if (v_isSharedCheck_5298_ == 0)
{
v___x_5086_ = v_val_5082_;
v_isShared_5087_ = v_isSharedCheck_5298_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_snd_5084_);
lean_inc(v_fst_5083_);
lean_dec(v_val_5082_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5298_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
lean_object* v___x_5088_; 
lean_inc_ref(v___x_5068_);
v___x_5088_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5068_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5088_) == 0)
{
lean_object* v_a_5089_; 
v_a_5089_ = lean_ctor_get(v___x_5088_, 0);
lean_inc(v_a_5089_);
lean_dec_ref_known(v___x_5088_, 1);
if (lean_obj_tag(v_a_5089_) == 1)
{
lean_object* v_val_5090_; lean_object* v_fst_5091_; lean_object* v_snd_5092_; lean_object* v___x_5094_; uint8_t v_isShared_5095_; uint8_t v_isSharedCheck_5289_; 
v_val_5090_ = lean_ctor_get(v_a_5089_, 0);
lean_inc(v_val_5090_);
lean_dec_ref_known(v_a_5089_, 1);
v_fst_5091_ = lean_ctor_get(v_val_5090_, 0);
v_snd_5092_ = lean_ctor_get(v_val_5090_, 1);
v_isSharedCheck_5289_ = !lean_is_exclusive(v_val_5090_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5094_ = v_val_5090_;
v_isShared_5095_ = v_isSharedCheck_5289_;
goto v_resetjp_5093_;
}
else
{
lean_inc(v_snd_5092_);
lean_inc(v_fst_5091_);
lean_dec(v_val_5090_);
v___x_5094_ = lean_box(0);
v_isShared_5095_ = v_isSharedCheck_5289_;
goto v_resetjp_5093_;
}
v_resetjp_5093_:
{
lean_object* v_toConstantVal_5096_; lean_object* v_cidx_5097_; lean_object* v_numParams_5098_; lean_object* v_numFields_5099_; lean_object* v___y_5101_; lean_object* v___y_5102_; lean_object* v___y_5103_; lean_object* v___y_5104_; lean_object* v___y_5105_; lean_object* v___y_5106_; uint8_t v___y_5191_; lean_object* v_cidx_5219_; uint8_t v___x_5220_; 
v_toConstantVal_5096_ = lean_ctor_get(v_fst_5083_, 0);
lean_inc_ref(v_toConstantVal_5096_);
v_cidx_5097_ = lean_ctor_get(v_fst_5083_, 2);
lean_inc(v_cidx_5097_);
v_numParams_5098_ = lean_ctor_get(v_fst_5083_, 3);
lean_inc(v_numParams_5098_);
v_numFields_5099_ = lean_ctor_get(v_fst_5083_, 4);
lean_inc(v_numFields_5099_);
lean_dec(v_fst_5083_);
v_cidx_5219_ = lean_ctor_get(v_fst_5091_, 2);
lean_inc(v_cidx_5219_);
lean_dec(v_fst_5091_);
v___x_5220_ = lean_nat_dec_eq(v_cidx_5097_, v_cidx_5219_);
lean_dec(v_cidx_5219_);
lean_dec(v_cidx_5097_);
if (v___x_5220_ == 0)
{
if (v___x_5033_ == 0)
{
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5065_);
lean_dec_ref(v_val_5062_);
v___y_5191_ = v___x_5033_;
goto v___jp_5190_;
}
else
{
lean_object* v_toConstantVal_5221_; lean_object* v_name_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v_a_5226_; lean_object* v___x_5227_; lean_object* v___x_5228_; lean_object* v_a_5229_; uint8_t v___x_5247_; 
lean_dec(v_numFields_5099_);
lean_dec(v_numParams_5098_);
lean_dec_ref(v_toConstantVal_5096_);
lean_del_object(v___x_5094_);
lean_dec(v_snd_5092_);
lean_del_object(v___x_5086_);
lean_dec(v_snd_5084_);
v_toConstantVal_5221_ = lean_ctor_get(v_val_5062_, 0);
lean_inc_ref(v_toConstantVal_5221_);
lean_dec_ref(v_val_5062_);
v_name_5222_ = lean_ctor_get(v_toConstantVal_5221_, 0);
lean_inc(v_name_5222_);
lean_dec_ref(v_toConstantVal_5221_);
v___x_5223_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5224_ = l_Lean_Name_str___override(v_name_5222_, v___x_5223_);
lean_inc(v___x_5224_);
v___x_5225_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5224_, v___x_5033_, v_a_5025_);
v_a_5226_ = lean_ctor_get(v___x_5225_, 0);
lean_inc(v_a_5226_);
lean_dec_ref(v___x_5225_);
v___x_5227_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5228_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5227_, v___x_5033_, v_a_5025_);
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc(v_a_5229_);
lean_dec_ref(v___x_5228_);
v___x_5247_ = lean_unbox(v_a_5226_);
lean_dec(v_a_5226_);
if (v___x_5247_ == 0)
{
lean_dec(v_a_5229_);
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5065_);
lean_dec(v_a_5064_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
goto v___jp_5230_;
}
else
{
uint8_t v___x_5248_; 
v___x_5248_ = lean_unbox(v_a_5229_);
lean_dec(v_a_5229_);
if (v___x_5248_ == 0)
{
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5065_);
lean_dec(v_a_5064_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
goto v___jp_5230_;
}
else
{
lean_object* v_dummy_5249_; lean_object* v_nargs_5250_; lean_object* v___x_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; lean_object* v___x_5254_; lean_object* v___x_5255_; 
v_dummy_5249_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5250_ = l_Lean_Expr_getAppNumArgs(v_a_5043_);
lean_inc(v_nargs_5250_);
v___x_5251_ = lean_mk_array(v_nargs_5250_, v_dummy_5249_);
v___x_5252_ = lean_unsigned_to_nat(1u);
v___x_5253_ = lean_nat_sub(v_nargs_5250_, v___x_5252_);
lean_dec(v_nargs_5250_);
lean_inc_n(v_a_5043_, 2);
v___x_5254_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5043_, v___x_5251_, v___x_5253_);
v___x_5255_ = l_Lean_Meta_getLevel(v_a_5043_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
if (lean_obj_tag(v___x_5255_) == 0)
{
lean_object* v_a_5256_; lean_object* v___x_5258_; uint8_t v_isShared_5259_; uint8_t v_isSharedCheck_5280_; 
v_a_5256_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5280_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5258_ = v___x_5255_;
v_isShared_5259_ = v_isSharedCheck_5280_;
goto v_resetjp_5257_;
}
else
{
lean_inc(v_a_5256_);
lean_dec(v___x_5255_);
v___x_5258_ = lean_box(0);
v_isShared_5259_ = v_isSharedCheck_5280_;
goto v_resetjp_5257_;
}
v_resetjp_5257_:
{
lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5278_; 
v___x_5260_ = l_Lean_mkConst(v___x_5224_, v_us_5056_);
v___x_5261_ = l_Lean_mkAppN(v___x_5260_, v___x_5254_);
lean_dec_ref(v___x_5254_);
v___x_5262_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5263_ = lean_box(0);
v___x_5264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5264_, 0, v_a_5064_);
lean_ctor_set(v___x_5264_, 1, v___x_5263_);
v___x_5265_ = l_Lean_mkConst(v___x_5262_, v___x_5264_);
v___x_5266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5266_, 0, v_a_5256_);
lean_ctor_set(v___x_5266_, 1, v___x_5263_);
v___x_5267_ = l_Lean_mkConst(v___x_5227_, v___x_5266_);
v___x_5268_ = lean_unsigned_to_nat(5u);
v___x_5269_ = lean_mk_empty_array_with_capacity(v___x_5268_);
v___x_5270_ = lean_array_push(v___x_5269_, v_a_5043_);
v___x_5271_ = lean_array_push(v___x_5270_, v___x_5261_);
v___x_5272_ = lean_array_push(v___x_5271_, v___x_5065_);
v___x_5273_ = lean_array_push(v___x_5272_, v___x_5068_);
v___x_5274_ = lean_array_push(v___x_5273_, v_h_5021_);
v___x_5275_ = l_Lean_mkAppN(v___x_5267_, v___x_5274_);
lean_dec_ref(v___x_5274_);
v___x_5276_ = l_Lean_mkAppB(v___x_5265_, v_target_5020_, v___x_5275_);
if (v_isShared_5259_ == 0)
{
lean_ctor_set(v___x_5258_, 0, v___x_5276_);
v___x_5278_ = v___x_5258_;
goto v_reusejp_5277_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5276_);
v___x_5278_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5277_;
}
v_reusejp_5277_:
{
return v___x_5278_;
}
}
}
else
{
lean_object* v_a_5281_; lean_object* v___x_5283_; uint8_t v_isShared_5284_; uint8_t v_isSharedCheck_5288_; 
lean_dec_ref(v___x_5254_);
lean_dec(v___x_5224_);
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5065_);
lean_dec(v_a_5064_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v_a_5281_ = lean_ctor_get(v___x_5255_, 0);
v_isSharedCheck_5288_ = !lean_is_exclusive(v___x_5255_);
if (v_isSharedCheck_5288_ == 0)
{
v___x_5283_ = v___x_5255_;
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
else
{
lean_inc(v_a_5281_);
lean_dec(v___x_5255_);
v___x_5283_ = lean_box(0);
v_isShared_5284_ = v_isSharedCheck_5288_;
goto v_resetjp_5282_;
}
v_resetjp_5282_:
{
lean_object* v___x_5286_; 
if (v_isShared_5284_ == 0)
{
v___x_5286_ = v___x_5283_;
goto v_reusejp_5285_;
}
else
{
lean_object* v_reuseFailAlloc_5287_; 
v_reuseFailAlloc_5287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
v___x_5286_ = v_reuseFailAlloc_5287_;
goto v_reusejp_5285_;
}
v_reusejp_5285_:
{
return v___x_5286_;
}
}
}
}
}
v___jp_5230_:
{
lean_object* v___x_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v_a_5239_; lean_object* v___x_5241_; uint8_t v_isShared_5242_; uint8_t v_isSharedCheck_5246_; 
v___x_5231_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5232_ = l_Lean_MessageData_ofName(v___x_5224_);
v___x_5233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5233_, 0, v___x_5231_);
lean_ctor_set(v___x_5233_, 1, v___x_5232_);
v___x_5234_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__23, &l_Lean_Meta_mkNoConfusion___closed__23_once, _init_l_Lean_Meta_mkNoConfusion___closed__23);
v___x_5235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5233_);
lean_ctor_set(v___x_5235_, 1, v___x_5234_);
v___x_5236_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__24, &l_Lean_Meta_mkNoConfusion___closed__24_once, _init_l_Lean_Meta_mkNoConfusion___closed__24);
v___x_5237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5237_, 0, v___x_5235_);
lean_ctor_set(v___x_5237_, 1, v___x_5236_);
v___x_5238_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5237_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
v_a_5239_ = lean_ctor_get(v___x_5238_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___x_5238_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5241_ = v___x_5238_;
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
else
{
lean_inc(v_a_5239_);
lean_dec(v___x_5238_);
v___x_5241_ = lean_box(0);
v_isShared_5242_ = v_isSharedCheck_5246_;
goto v_resetjp_5240_;
}
v_resetjp_5240_:
{
lean_object* v___x_5244_; 
if (v_isShared_5242_ == 0)
{
v___x_5244_ = v___x_5241_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_a_5239_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5065_);
lean_dec_ref(v_val_5062_);
v___y_5191_ = v___x_5059_;
goto v___jp_5190_;
}
v___jp_5100_:
{
lean_object* v___x_5107_; 
lean_inc(v___y_5102_);
v___x_5107_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5102_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v_a_5108_; lean_object* v_nargs_5109_; lean_object* v_type_5110_; lean_object* v___x_5112_; uint8_t v_isShared_5113_; uint8_t v_isSharedCheck_5179_; 
v_a_5108_ = lean_ctor_get(v___x_5107_, 0);
lean_inc(v_a_5108_);
lean_dec_ref_known(v___x_5107_, 1);
v_nargs_5109_ = l_Lean_Expr_getAppNumArgs(v_a_5043_);
v_type_5110_ = lean_ctor_get(v_a_5108_, 2);
v_isSharedCheck_5179_ = !lean_is_exclusive(v_a_5108_);
if (v_isSharedCheck_5179_ == 0)
{
lean_object* v_unused_5180_; lean_object* v_unused_5181_; 
v_unused_5180_ = lean_ctor_get(v_a_5108_, 1);
lean_dec(v_unused_5180_);
v_unused_5181_ = lean_ctor_get(v_a_5108_, 0);
lean_dec(v_unused_5181_);
v___x_5112_ = v_a_5108_;
v_isShared_5113_ = v_isSharedCheck_5179_;
goto v_resetjp_5111_;
}
else
{
lean_inc(v_type_5110_);
lean_dec(v_a_5108_);
v___x_5112_ = lean_box(0);
v_isShared_5113_ = v_isSharedCheck_5179_;
goto v_resetjp_5111_;
}
v_resetjp_5111_:
{
lean_object* v_dummy_5114_; lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v_start_5120_; lean_object* v_stop_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; uint8_t v___x_5135_; 
v_dummy_5114_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
lean_inc(v_nargs_5109_);
v___x_5115_ = lean_mk_array(v_nargs_5109_, v_dummy_5114_);
v___x_5116_ = lean_unsigned_to_nat(1u);
v___x_5117_ = lean_nat_sub(v_nargs_5109_, v___x_5116_);
lean_dec(v_nargs_5109_);
v___x_5118_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5043_, v___x_5115_, v___x_5117_);
lean_inc_n(v_numParams_5098_, 2);
lean_inc(v___y_5101_);
v___x_5119_ = l_Array_toSubarray___redArg(v___x_5118_, v___y_5101_, v_numParams_5098_);
v_start_5120_ = lean_ctor_get(v___x_5119_, 1);
lean_inc(v_start_5120_);
v_stop_5121_ = lean_ctor_get(v___x_5119_, 2);
lean_inc(v_stop_5121_);
v___x_5122_ = lean_array_get_size(v_snd_5084_);
v___x_5123_ = l_Array_toSubarray___redArg(v_snd_5084_, v_numParams_5098_, v___x_5122_);
v___x_5124_ = lean_array_get_size(v_snd_5092_);
v___x_5125_ = l_Subarray_copy___redArg(v___x_5123_);
v___x_5126_ = l_Array_toSubarray___redArg(v_snd_5092_, v_numParams_5098_, v___x_5124_);
v___x_5127_ = l_Subarray_copy___redArg(v___x_5126_);
v___x_5128_ = l_Lean_Expr_getNumHeadForalls(v_type_5110_);
lean_dec_ref(v_type_5110_);
v___x_5129_ = lean_nat_sub(v_stop_5121_, v_start_5120_);
lean_dec(v_start_5120_);
lean_dec(v_stop_5121_);
v___x_5130_ = lean_array_get_size(v___x_5125_);
v___x_5131_ = lean_nat_add(v___x_5129_, v___x_5130_);
lean_dec(v___x_5129_);
v___x_5132_ = lean_array_get_size(v___x_5127_);
v___x_5133_ = lean_nat_add(v___x_5131_, v___x_5132_);
lean_dec(v___x_5131_);
v___x_5134_ = lean_nat_add(v___x_5133_, v___x_5032_);
lean_dec(v___x_5133_);
v___x_5135_ = lean_nat_dec_le(v___x_5134_, v___x_5128_);
if (v___x_5135_ == 0)
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
lean_dec(v___x_5134_);
lean_dec(v___x_5128_);
lean_dec_ref(v___x_5127_);
lean_dec_ref(v___x_5125_);
lean_dec_ref(v___x_5119_);
lean_del_object(v___x_5112_);
lean_dec(v___y_5102_);
lean_dec(v___y_5101_);
lean_del_object(v___x_5094_);
lean_dec(v_a_5064_);
lean_dec(v_us_5056_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v___x_5136_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__14, &l_Lean_Meta_mkNoConfusion___closed__14_once, _init_l_Lean_Meta_mkNoConfusion___closed__14);
v___x_5137_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5136_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
return v___x_5137_;
}
else
{
lean_object* v___x_5139_; 
if (v_isShared_5095_ == 0)
{
lean_ctor_set_tag(v___x_5094_, 1);
lean_ctor_set(v___x_5094_, 1, v_us_5056_);
lean_ctor_set(v___x_5094_, 0, v_a_5064_);
v___x_5139_ = v___x_5094_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5178_; 
v_reuseFailAlloc_5178_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5178_, 0, v_a_5064_);
lean_ctor_set(v_reuseFailAlloc_5178_, 1, v_us_5056_);
v___x_5139_ = v_reuseFailAlloc_5178_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5150_; 
v___x_5140_ = l_Lean_mkConst(v___y_5102_, v___x_5139_);
v___x_5141_ = l_Subarray_copy___redArg(v___x_5119_);
v___x_5142_ = l_Lean_mkAppN(v___x_5140_, v___x_5141_);
lean_dec_ref(v___x_5141_);
v___x_5143_ = lean_mk_empty_array_with_capacity(v___x_5116_);
v___x_5144_ = lean_array_push(v___x_5143_, v_target_5020_);
v___x_5145_ = l_Array_append___redArg(v___x_5144_, v___x_5125_);
lean_dec_ref(v___x_5125_);
v___x_5146_ = l_Array_append___redArg(v___x_5145_, v___x_5127_);
lean_dec_ref(v___x_5127_);
v___x_5147_ = l_Lean_mkAppN(v___x_5142_, v___x_5146_);
lean_dec_ref(v___x_5146_);
v___x_5148_ = lean_nat_sub(v___x_5128_, v___x_5134_);
lean_dec(v___x_5134_);
lean_dec(v___x_5128_);
lean_inc(v___y_5101_);
if (v_isShared_5113_ == 0)
{
lean_ctor_set(v___x_5112_, 2, v___x_5116_);
lean_ctor_set(v___x_5112_, 1, v___x_5148_);
lean_ctor_set(v___x_5112_, 0, v___y_5101_);
v___x_5150_ = v___x_5112_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___y_5101_);
lean_ctor_set(v_reuseFailAlloc_5177_, 1, v___x_5148_);
lean_ctor_set(v_reuseFailAlloc_5177_, 2, v___x_5116_);
v___x_5150_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5151_; 
v___x_5151_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5150_, v___x_5147_, v___y_5101_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
lean_dec_ref(v___x_5150_);
if (lean_obj_tag(v___x_5151_) == 0)
{
lean_object* v_a_5152_; lean_object* v___x_5153_; 
v_a_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc_n(v_a_5152_, 2);
lean_dec_ref_known(v___x_5151_, 1);
lean_inc(v___y_5106_);
lean_inc_ref(v___y_5105_);
lean_inc(v___y_5104_);
lean_inc_ref(v___y_5103_);
v___x_5153_ = lean_infer_type(v_a_5152_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
if (lean_obj_tag(v___x_5153_) == 0)
{
lean_object* v_a_5154_; lean_object* v___x_5155_; 
v_a_5154_ = lean_ctor_get(v___x_5153_, 0);
lean_inc(v_a_5154_);
lean_dec_ref_known(v___x_5153_, 1);
v___x_5155_ = l_Lean_Meta_whnfForall(v_a_5154_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5176_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5176_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5176_ == 0)
{
v___x_5158_ = v___x_5155_;
v_isShared_5159_ = v_isSharedCheck_5176_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_a_5156_);
lean_dec(v___x_5155_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5176_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
lean_object* v___x_5160_; uint8_t v___x_5161_; 
v___x_5160_ = l_Lean_Expr_bindingDomain_x21(v_a_5156_);
lean_dec(v_a_5156_);
v___x_5161_ = l_Lean_Expr_isHEq(v___x_5160_);
lean_dec_ref(v___x_5160_);
if (v___x_5161_ == 0)
{
lean_object* v___x_5162_; lean_object* v___x_5164_; 
v___x_5162_ = l_Lean_Expr_app___override(v_a_5152_, v_h_5021_);
if (v_isShared_5159_ == 0)
{
lean_ctor_set(v___x_5158_, 0, v___x_5162_);
v___x_5164_ = v___x_5158_;
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
else
{
lean_object* v___x_5166_; 
lean_del_object(v___x_5158_);
v___x_5166_ = l_Lean_Meta_mkHEqOfEq(v_h_5021_, v___y_5103_, v___y_5104_, v___y_5105_, v___y_5106_);
if (lean_obj_tag(v___x_5166_) == 0)
{
lean_object* v_a_5167_; lean_object* v___x_5169_; uint8_t v_isShared_5170_; uint8_t v_isSharedCheck_5175_; 
v_a_5167_ = lean_ctor_get(v___x_5166_, 0);
v_isSharedCheck_5175_ = !lean_is_exclusive(v___x_5166_);
if (v_isSharedCheck_5175_ == 0)
{
v___x_5169_ = v___x_5166_;
v_isShared_5170_ = v_isSharedCheck_5175_;
goto v_resetjp_5168_;
}
else
{
lean_inc(v_a_5167_);
lean_dec(v___x_5166_);
v___x_5169_ = lean_box(0);
v_isShared_5170_ = v_isSharedCheck_5175_;
goto v_resetjp_5168_;
}
v_resetjp_5168_:
{
lean_object* v___x_5171_; lean_object* v___x_5173_; 
v___x_5171_ = l_Lean_Expr_app___override(v_a_5152_, v_a_5167_);
if (v_isShared_5170_ == 0)
{
lean_ctor_set(v___x_5169_, 0, v___x_5171_);
v___x_5173_ = v___x_5169_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5174_; 
v_reuseFailAlloc_5174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5174_, 0, v___x_5171_);
v___x_5173_ = v_reuseFailAlloc_5174_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
return v___x_5173_;
}
}
}
else
{
lean_dec(v_a_5152_);
return v___x_5166_;
}
}
}
}
else
{
lean_dec(v_a_5152_);
lean_dec_ref(v_h_5021_);
return v___x_5155_;
}
}
else
{
lean_dec(v_a_5152_);
lean_dec_ref(v_h_5021_);
return v___x_5153_;
}
}
else
{
lean_dec_ref(v_h_5021_);
return v___x_5151_;
}
}
}
}
}
}
else
{
lean_object* v_a_5182_; lean_object* v___x_5184_; uint8_t v_isShared_5185_; uint8_t v_isSharedCheck_5189_; 
lean_dec(v___y_5102_);
lean_dec(v___y_5101_);
lean_dec(v_numParams_5098_);
lean_del_object(v___x_5094_);
lean_dec(v_snd_5092_);
lean_dec(v_snd_5084_);
lean_dec(v_a_5064_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v_a_5182_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5184_ = v___x_5107_;
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
else
{
lean_inc(v_a_5182_);
lean_dec(v___x_5107_);
v___x_5184_ = lean_box(0);
v_isShared_5185_ = v_isSharedCheck_5189_;
goto v_resetjp_5183_;
}
v_resetjp_5183_:
{
lean_object* v___x_5187_; 
if (v_isShared_5185_ == 0)
{
v___x_5187_ = v___x_5184_;
goto v_reusejp_5186_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v_a_5182_);
v___x_5187_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5186_;
}
v_reusejp_5186_:
{
return v___x_5187_;
}
}
}
}
v___jp_5190_:
{
lean_object* v___x_5192_; uint8_t v___x_5193_; 
v___x_5192_ = lean_unsigned_to_nat(0u);
v___x_5193_ = lean_nat_dec_eq(v_numFields_5099_, v___x_5192_);
lean_dec(v_numFields_5099_);
if (v___x_5193_ == 0)
{
lean_object* v_name_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v___x_5197_; lean_object* v_a_5198_; uint8_t v___x_5199_; 
v_name_5194_ = lean_ctor_get(v_toConstantVal_5096_, 0);
lean_inc(v_name_5194_);
lean_dec_ref(v_toConstantVal_5096_);
v___x_5195_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5196_ = l_Lean_Name_str___override(v_name_5194_, v___x_5195_);
lean_inc(v___x_5196_);
v___x_5197_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5196_, v___x_5033_, v_a_5025_);
v_a_5198_ = lean_ctor_get(v___x_5197_, 0);
lean_inc(v_a_5198_);
lean_dec_ref(v___x_5197_);
v___x_5199_ = lean_unbox(v_a_5198_);
lean_dec(v_a_5198_);
if (v___x_5199_ == 0)
{
lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5203_; 
lean_dec(v_numParams_5098_);
lean_del_object(v___x_5094_);
lean_dec(v_snd_5092_);
lean_dec(v_snd_5084_);
lean_dec(v_a_5064_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v___x_5200_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5201_ = l_Lean_MessageData_ofName(v___x_5196_);
if (v_isShared_5087_ == 0)
{
lean_ctor_set_tag(v___x_5086_, 7);
lean_ctor_set(v___x_5086_, 1, v___x_5201_);
lean_ctor_set(v___x_5086_, 0, v___x_5200_);
v___x_5203_ = v___x_5086_;
goto v_reusejp_5202_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v___x_5200_);
lean_ctor_set(v_reuseFailAlloc_5213_, 1, v___x_5201_);
v___x_5203_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5202_;
}
v_reusejp_5202_:
{
lean_object* v___x_5204_; lean_object* v_a_5205_; lean_object* v___x_5207_; uint8_t v_isShared_5208_; uint8_t v_isSharedCheck_5212_; 
v___x_5204_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5203_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
v_isSharedCheck_5212_ = !lean_is_exclusive(v___x_5204_);
if (v_isSharedCheck_5212_ == 0)
{
v___x_5207_ = v___x_5204_;
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
else
{
lean_inc(v_a_5205_);
lean_dec(v___x_5204_);
v___x_5207_ = lean_box(0);
v_isShared_5208_ = v_isSharedCheck_5212_;
goto v_resetjp_5206_;
}
v_resetjp_5206_:
{
lean_object* v___x_5210_; 
if (v_isShared_5208_ == 0)
{
v___x_5210_ = v___x_5207_;
goto v_reusejp_5209_;
}
else
{
lean_object* v_reuseFailAlloc_5211_; 
v_reuseFailAlloc_5211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5211_, 0, v_a_5205_);
v___x_5210_ = v_reuseFailAlloc_5211_;
goto v_reusejp_5209_;
}
v_reusejp_5209_:
{
return v___x_5210_;
}
}
}
}
else
{
lean_del_object(v___x_5086_);
v___y_5101_ = v___x_5192_;
v___y_5102_ = v___x_5196_;
v___y_5103_ = v_a_5022_;
v___y_5104_ = v_a_5023_;
v___y_5105_ = v_a_5024_;
v___y_5106_ = v_a_5025_;
goto v___jp_5100_;
}
}
else
{
lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___f_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
lean_dec(v_numParams_5098_);
lean_dec_ref(v_toConstantVal_5096_);
lean_del_object(v___x_5094_);
lean_dec(v_snd_5092_);
lean_del_object(v___x_5086_);
lean_dec(v_snd_5084_);
lean_dec(v_a_5064_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
v___x_5214_ = lean_box(v___y_5191_);
v___x_5215_ = lean_box(v___x_5193_);
v___f_5216_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5216_, 0, v___x_5214_);
lean_closure_set(v___f_5216_, 1, v___x_5215_);
v___x_5217_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5218_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5217_, v_target_5020_, v___f_5216_, v_a_5022_, v_a_5023_, v_a_5024_, v_a_5025_);
return v___x_5218_;
}
}
}
}
else
{
lean_dec(v_a_5089_);
lean_del_object(v___x_5086_);
lean_dec(v_snd_5084_);
lean_dec(v_fst_5083_);
lean_dec(v_a_5064_);
lean_dec_ref(v_val_5062_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v___y_5070_ = v_a_5022_;
v___y_5071_ = v_a_5023_;
v___y_5072_ = v_a_5024_;
v___y_5073_ = v_a_5025_;
goto v___jp_5069_;
}
}
else
{
lean_object* v_a_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5297_; 
lean_del_object(v___x_5086_);
lean_dec(v_snd_5084_);
lean_dec(v_fst_5083_);
lean_dec_ref(v___x_5068_);
lean_dec_ref(v___x_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_val_5062_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v_a_5290_ = lean_ctor_get(v___x_5088_, 0);
v_isSharedCheck_5297_ = !lean_is_exclusive(v___x_5088_);
if (v_isSharedCheck_5297_ == 0)
{
v___x_5292_ = v___x_5088_;
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
else
{
lean_inc(v_a_5290_);
lean_dec(v___x_5088_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5297_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5295_; 
if (v_isShared_5293_ == 0)
{
v___x_5295_ = v___x_5292_;
goto v_reusejp_5294_;
}
else
{
lean_object* v_reuseFailAlloc_5296_; 
v_reuseFailAlloc_5296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5296_, 0, v_a_5290_);
v___x_5295_ = v_reuseFailAlloc_5296_;
goto v_reusejp_5294_;
}
v_reusejp_5294_:
{
return v___x_5295_;
}
}
}
}
}
else
{
lean_dec(v_a_5067_);
lean_dec(v_a_5064_);
lean_dec_ref(v_val_5062_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v___y_5070_ = v_a_5022_;
v___y_5071_ = v_a_5023_;
v___y_5072_ = v_a_5024_;
v___y_5073_ = v_a_5025_;
goto v___jp_5069_;
}
v___jp_5069_:
{
lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5074_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__9, &l_Lean_Meta_mkNoConfusion___closed__9_once, _init_l_Lean_Meta_mkNoConfusion___closed__9);
v___x_5075_ = l_Lean_MessageData_ofExpr(v___x_5065_);
v___x_5076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5076_, 0, v___x_5074_);
lean_ctor_set(v___x_5076_, 1, v___x_5075_);
v___x_5077_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5078_, 0, v___x_5076_);
lean_ctor_set(v___x_5078_, 1, v___x_5077_);
v___x_5079_ = l_Lean_MessageData_ofExpr(v___x_5068_);
v___x_5080_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5080_, 0, v___x_5078_);
lean_ctor_set(v___x_5080_, 1, v___x_5079_);
v___x_5081_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5080_, v___y_5070_, v___y_5071_, v___y_5072_, v___y_5073_);
return v___x_5081_;
}
}
else
{
lean_object* v_a_5299_; lean_object* v___x_5301_; uint8_t v_isShared_5302_; uint8_t v_isSharedCheck_5306_; 
lean_dec_ref(v___x_5065_);
lean_dec(v_a_5064_);
lean_dec_ref(v_val_5062_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec(v_a_5030_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v_a_5299_ = lean_ctor_get(v___x_5066_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5066_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5301_ = v___x_5066_;
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
else
{
lean_inc(v_a_5299_);
lean_dec(v___x_5066_);
v___x_5301_ = lean_box(0);
v_isShared_5302_ = v_isSharedCheck_5306_;
goto v_resetjp_5300_;
}
v_resetjp_5300_:
{
lean_object* v___x_5304_; 
if (v_isShared_5302_ == 0)
{
v___x_5304_ = v___x_5301_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_a_5299_);
v___x_5304_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
return v___x_5304_;
}
}
}
}
else
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5314_; 
lean_dec_ref(v_val_5062_);
lean_dec(v_us_5056_);
lean_dec(v_a_5043_);
lean_dec_ref(v___x_5039_);
lean_dec(v_a_5030_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v_a_5307_ = lean_ctor_get(v___x_5063_, 0);
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5063_);
if (v_isSharedCheck_5314_ == 0)
{
v___x_5309_ = v___x_5063_;
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5063_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v___x_5312_; 
if (v_isShared_5310_ == 0)
{
v___x_5312_ = v___x_5309_;
goto v_reusejp_5311_;
}
else
{
lean_object* v_reuseFailAlloc_5313_; 
v_reuseFailAlloc_5313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5313_, 0, v_a_5307_);
v___x_5312_ = v_reuseFailAlloc_5313_;
goto v_reusejp_5311_;
}
v_reusejp_5311_:
{
return v___x_5312_;
}
}
}
}
else
{
lean_dec(v_val_5061_);
lean_dec(v_us_5056_);
lean_dec_ref(v___x_5039_);
lean_dec(v_a_5030_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v___y_5045_ = v_a_5022_;
v___y_5046_ = v_a_5023_;
v___y_5047_ = v_a_5024_;
v___y_5048_ = v_a_5025_;
goto v___jp_5044_;
}
}
}
else
{
lean_dec_ref(v___x_5054_);
lean_dec_ref(v___x_5039_);
lean_dec(v_a_5030_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
v___y_5045_ = v_a_5022_;
v___y_5046_ = v_a_5023_;
v___y_5047_ = v_a_5024_;
v___y_5048_ = v_a_5025_;
goto v___jp_5044_;
}
v___jp_5044_:
{
lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v___x_5053_; 
v___x_5049_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5050_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__7, &l_Lean_Meta_mkNoConfusion___closed__7_once, _init_l_Lean_Meta_mkNoConfusion___closed__7);
v___x_5051_ = l_Lean_indentExpr(v_a_5043_);
v___x_5052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5052_, 0, v___x_5050_);
lean_ctor_set(v___x_5052_, 1, v___x_5051_);
v___x_5053_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5049_, v___x_5052_, v___y_5045_, v___y_5046_, v___y_5047_, v___y_5048_);
return v___x_5053_;
}
}
else
{
lean_dec_ref(v___x_5039_);
lean_dec(v_a_5030_);
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
return v___x_5042_;
}
}
}
else
{
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
return v___x_5029_;
}
}
else
{
lean_dec_ref(v_h_5021_);
lean_dec_ref(v_target_5020_);
return v___x_5027_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5315_, lean_object* v_h_5316_, lean_object* v_a_5317_, lean_object* v_a_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Lean_Meta_mkNoConfusion(v_target_5315_, v_h_5316_, v_a_5317_, v_a_5318_, v_a_5319_, v_a_5320_);
lean_dec(v_a_5320_);
lean_dec_ref(v_a_5319_);
lean_dec(v_a_5318_);
lean_dec_ref(v_a_5317_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5323_, lean_object* v_b_5324_, lean_object* v_i_5325_, lean_object* v_hs_5326_, lean_object* v_hl_5327_, lean_object* v___y_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_){
_start:
{
lean_object* v___x_5333_; 
v___x_5333_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5323_, v_b_5324_, v_i_5325_, v___y_5328_, v___y_5329_, v___y_5330_, v___y_5331_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5334_, lean_object* v_b_5335_, lean_object* v_i_5336_, lean_object* v_hs_5337_, lean_object* v_hl_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
lean_object* v_res_5344_; 
v_res_5344_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5334_, v_b_5335_, v_i_5336_, v_hs_5337_, v_hl_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec_ref(v_range_5334_);
return v_res_5344_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5345_, lean_object* v_name_5346_, uint8_t v_bi_5347_, lean_object* v_type_5348_, lean_object* v_k_5349_, uint8_t v_kind_5350_, lean_object* v___y_5351_, lean_object* v___y_5352_, lean_object* v___y_5353_, lean_object* v___y_5354_){
_start:
{
lean_object* v___x_5356_; 
v___x_5356_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5346_, v_bi_5347_, v_type_5348_, v_k_5349_, v_kind_5350_, v___y_5351_, v___y_5352_, v___y_5353_, v___y_5354_);
return v___x_5356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5357_, lean_object* v_name_5358_, lean_object* v_bi_5359_, lean_object* v_type_5360_, lean_object* v_k_5361_, lean_object* v_kind_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_, lean_object* v___y_5367_){
_start:
{
uint8_t v_bi_boxed_5368_; uint8_t v_kind_boxed_5369_; lean_object* v_res_5370_; 
v_bi_boxed_5368_ = lean_unbox(v_bi_5359_);
v_kind_boxed_5369_ = lean_unbox(v_kind_5362_);
v_res_5370_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5357_, v_name_5358_, v_bi_boxed_5368_, v_type_5360_, v_k_5361_, v_kind_boxed_5369_, v___y_5363_, v___y_5364_, v___y_5365_, v___y_5366_);
lean_dec(v___y_5366_);
lean_dec_ref(v___y_5365_);
lean_dec(v___y_5364_);
lean_dec_ref(v___y_5363_);
return v_res_5370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5371_, lean_object* v_name_5372_, lean_object* v_type_5373_, lean_object* v_k_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_, lean_object* v___y_5377_, lean_object* v___y_5378_){
_start:
{
lean_object* v___x_5380_; 
v___x_5380_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5372_, v_type_5373_, v_k_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_);
return v___x_5380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5381_, lean_object* v_name_5382_, lean_object* v_type_5383_, lean_object* v_k_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_){
_start:
{
lean_object* v_res_5390_; 
v_res_5390_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5381_, v_name_5382_, v_type_5383_, v_k_5384_, v___y_5385_, v___y_5386_, v___y_5387_, v___y_5388_);
lean_dec(v___y_5388_);
lean_dec_ref(v___y_5387_);
lean_dec(v___y_5386_);
lean_dec_ref(v___y_5385_);
return v_res_5390_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5396_, lean_object* v_e_5397_, lean_object* v_a_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_){
_start:
{
lean_object* v___x_5403_; lean_object* v___x_5404_; lean_object* v___x_5405_; lean_object* v___x_5406_; lean_object* v___x_5407_; lean_object* v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; 
v___x_5403_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5404_, 0, v_monad_5396_);
v___x_5405_ = lean_box(0);
v___x_5406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5406_, 0, v_e_5397_);
v___x_5407_ = lean_unsigned_to_nat(4u);
v___x_5408_ = lean_mk_empty_array_with_capacity(v___x_5407_);
v___x_5409_ = lean_array_push(v___x_5408_, v___x_5404_);
v___x_5410_ = lean_array_push(v___x_5409_, v___x_5405_);
v___x_5411_ = lean_array_push(v___x_5410_, v___x_5405_);
v___x_5412_ = lean_array_push(v___x_5411_, v___x_5406_);
v___x_5413_ = l_Lean_Meta_mkAppOptM(v___x_5403_, v___x_5412_, v_a_5398_, v_a_5399_, v_a_5400_, v_a_5401_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5414_, lean_object* v_e_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_, lean_object* v_a_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Lean_Meta_mkPure(v_monad_5414_, v_e_5415_, v_a_5416_, v_a_5417_, v_a_5418_, v_a_5419_);
lean_dec(v_a_5419_);
lean_dec_ref(v_a_5418_);
lean_dec(v_a_5417_);
lean_dec_ref(v_a_5416_);
return v_res_5421_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5431_; lean_object* v___x_5432_; 
v___x_5431_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5432_ = l_Lean_MessageData_ofFormat(v___x_5431_);
return v___x_5432_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5436_; lean_object* v___x_5437_; 
v___x_5436_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5437_ = l_Lean_MessageData_ofFormat(v___x_5436_);
return v___x_5437_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5441_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5442_ = l_Lean_MessageData_ofFormat(v___x_5441_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5443_, lean_object* v_fieldName_5444_, lean_object* v_a_5445_, lean_object* v_a_5446_, lean_object* v_a_5447_, lean_object* v_a_5448_){
_start:
{
lean_object* v___x_5450_; 
lean_inc(v_a_5448_);
lean_inc_ref(v_a_5447_);
lean_inc(v_a_5446_);
lean_inc_ref(v_a_5445_);
lean_inc_ref(v_s_5443_);
v___x_5450_ = lean_infer_type(v_s_5443_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
if (lean_obj_tag(v___x_5450_) == 0)
{
lean_object* v_a_5451_; lean_object* v___x_5453_; uint8_t v_isShared_5454_; uint8_t v_isSharedCheck_5547_; 
v_a_5451_ = lean_ctor_get(v___x_5450_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5450_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5453_ = v___x_5450_;
v_isShared_5454_ = v_isSharedCheck_5547_;
goto v_resetjp_5452_;
}
else
{
lean_inc(v_a_5451_);
lean_dec(v___x_5450_);
v___x_5453_ = lean_box(0);
v_isShared_5454_ = v_isSharedCheck_5547_;
goto v_resetjp_5452_;
}
v_resetjp_5452_:
{
lean_object* v___x_5455_; 
lean_inc(v_a_5448_);
lean_inc_ref(v_a_5447_);
lean_inc(v_a_5446_);
lean_inc_ref(v_a_5445_);
v___x_5455_ = lean_whnf(v_a_5451_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
if (lean_obj_tag(v___x_5455_) == 0)
{
lean_object* v_a_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5546_; 
v_a_5456_ = lean_ctor_get(v___x_5455_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5455_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5458_ = v___x_5455_;
v_isShared_5459_ = v_isSharedCheck_5546_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_a_5456_);
lean_dec(v___x_5455_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5546_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___y_5461_; lean_object* v___y_5462_; lean_object* v___y_5463_; lean_object* v___y_5464_; lean_object* v___x_5479_; 
v___x_5479_ = l_Lean_Expr_getAppFn(v_a_5456_);
if (lean_obj_tag(v___x_5479_) == 4)
{
lean_object* v_declName_5480_; lean_object* v_us_5481_; lean_object* v___x_5482_; lean_object* v_env_5483_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___y_5487_; lean_object* v___y_5488_; uint8_t v___x_5527_; 
v_declName_5480_ = lean_ctor_get(v___x_5479_, 0);
lean_inc_n(v_declName_5480_, 2);
v_us_5481_ = lean_ctor_get(v___x_5479_, 1);
lean_inc(v_us_5481_);
lean_dec_ref_known(v___x_5479_, 2);
v___x_5482_ = lean_st_ref_get(v_a_5448_);
v_env_5483_ = lean_ctor_get(v___x_5482_, 0);
lean_inc_ref_n(v_env_5483_, 2);
lean_dec(v___x_5482_);
v___x_5527_ = l_Lean_isStructure(v_env_5483_, v_declName_5480_);
if (v___x_5527_ == 0)
{
lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v___x_5532_; 
v___x_5528_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5529_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5456_);
lean_inc_ref(v_s_5443_);
v___x_5530_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5443_, v_a_5456_);
v___x_5531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5531_, 0, v___x_5529_);
lean_ctor_set(v___x_5531_, 1, v___x_5530_);
v___x_5532_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5528_, v___x_5531_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_dec_ref_known(v___x_5532_, 1);
v___y_5485_ = v_a_5445_;
v___y_5486_ = v_a_5446_;
v___y_5487_ = v_a_5447_;
v___y_5488_ = v_a_5448_;
goto v___jp_5484_;
}
else
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5540_; 
lean_dec_ref(v_env_5483_);
lean_dec(v_us_5481_);
lean_dec(v_declName_5480_);
lean_del_object(v___x_5458_);
lean_dec(v_a_5456_);
lean_del_object(v___x_5453_);
lean_dec(v_fieldName_5444_);
lean_dec_ref(v_s_5443_);
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5540_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5540_ == 0)
{
v___x_5535_ = v___x_5532_;
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5532_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5540_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___x_5538_; 
if (v_isShared_5536_ == 0)
{
v___x_5538_ = v___x_5535_;
goto v_reusejp_5537_;
}
else
{
lean_object* v_reuseFailAlloc_5539_; 
v_reuseFailAlloc_5539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_a_5533_);
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
v___y_5485_ = v_a_5445_;
v___y_5486_ = v_a_5446_;
v___y_5487_ = v_a_5447_;
v___y_5488_ = v_a_5448_;
goto v___jp_5484_;
}
v___jp_5484_:
{
lean_object* v___x_5489_; 
lean_inc(v_fieldName_5444_);
lean_inc(v_declName_5480_);
lean_inc_ref(v_env_5483_);
v___x_5489_ = l_Lean_getProjFnForField_x3f(v_env_5483_, v_declName_5480_, v_fieldName_5444_);
if (lean_obj_tag(v___x_5489_) == 0)
{
lean_object* v___x_5490_; lean_object* v___x_5491_; size_t v_sz_5492_; size_t v___x_5493_; lean_object* v___x_5494_; 
lean_dec(v_us_5481_);
lean_del_object(v___x_5458_);
lean_inc(v_declName_5480_);
lean_inc_ref(v_env_5483_);
v___x_5490_ = l_Lean_getStructureFields(v_env_5483_, v_declName_5480_);
v___x_5491_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5492_ = lean_array_size(v___x_5490_);
v___x_5493_ = ((size_t)0ULL);
lean_inc(v_fieldName_5444_);
lean_inc_ref(v_s_5443_);
v___x_5494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5483_, v_declName_5480_, v_s_5443_, v_fieldName_5444_, v___x_5490_, v_sz_5492_, v___x_5493_, v___x_5491_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
lean_dec_ref(v___x_5490_);
if (lean_obj_tag(v___x_5494_) == 0)
{
lean_object* v_a_5495_; lean_object* v___x_5497_; uint8_t v_isShared_5498_; uint8_t v_isSharedCheck_5505_; 
v_a_5495_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5505_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5505_ == 0)
{
v___x_5497_ = v___x_5494_;
v_isShared_5498_ = v_isSharedCheck_5505_;
goto v_resetjp_5496_;
}
else
{
lean_inc(v_a_5495_);
lean_dec(v___x_5494_);
v___x_5497_ = lean_box(0);
v_isShared_5498_ = v_isSharedCheck_5505_;
goto v_resetjp_5496_;
}
v_resetjp_5496_:
{
lean_object* v_fst_5499_; 
v_fst_5499_ = lean_ctor_get(v_a_5495_, 0);
lean_inc(v_fst_5499_);
lean_dec(v_a_5495_);
if (lean_obj_tag(v_fst_5499_) == 0)
{
lean_del_object(v___x_5497_);
v___y_5461_ = v___y_5485_;
v___y_5462_ = v___y_5487_;
v___y_5463_ = v___y_5488_;
v___y_5464_ = v___y_5486_;
goto v___jp_5460_;
}
else
{
lean_object* v_val_5500_; 
v_val_5500_ = lean_ctor_get(v_fst_5499_, 0);
lean_inc(v_val_5500_);
lean_dec_ref_known(v_fst_5499_, 1);
if (lean_obj_tag(v_val_5500_) == 0)
{
lean_del_object(v___x_5497_);
v___y_5461_ = v___y_5485_;
v___y_5462_ = v___y_5487_;
v___y_5463_ = v___y_5488_;
v___y_5464_ = v___y_5486_;
goto v___jp_5460_;
}
else
{
lean_object* v_val_5501_; lean_object* v___x_5503_; 
lean_dec(v_a_5456_);
lean_del_object(v___x_5453_);
lean_dec(v_fieldName_5444_);
lean_dec_ref(v_s_5443_);
v_val_5501_ = lean_ctor_get(v_val_5500_, 0);
lean_inc(v_val_5501_);
lean_dec_ref_known(v_val_5500_, 1);
if (v_isShared_5498_ == 0)
{
lean_ctor_set(v___x_5497_, 0, v_val_5501_);
v___x_5503_ = v___x_5497_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5504_; 
v_reuseFailAlloc_5504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_val_5501_);
v___x_5503_ = v_reuseFailAlloc_5504_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
return v___x_5503_;
}
}
}
}
}
else
{
lean_object* v_a_5506_; lean_object* v___x_5508_; uint8_t v_isShared_5509_; uint8_t v_isSharedCheck_5513_; 
lean_dec(v_a_5456_);
lean_del_object(v___x_5453_);
lean_dec(v_fieldName_5444_);
lean_dec_ref(v_s_5443_);
v_a_5506_ = lean_ctor_get(v___x_5494_, 0);
v_isSharedCheck_5513_ = !lean_is_exclusive(v___x_5494_);
if (v_isSharedCheck_5513_ == 0)
{
v___x_5508_ = v___x_5494_;
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
else
{
lean_inc(v_a_5506_);
lean_dec(v___x_5494_);
v___x_5508_ = lean_box(0);
v_isShared_5509_ = v_isSharedCheck_5513_;
goto v_resetjp_5507_;
}
v_resetjp_5507_:
{
lean_object* v___x_5511_; 
if (v_isShared_5509_ == 0)
{
v___x_5511_ = v___x_5508_;
goto v_reusejp_5510_;
}
else
{
lean_object* v_reuseFailAlloc_5512_; 
v_reuseFailAlloc_5512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5512_, 0, v_a_5506_);
v___x_5511_ = v_reuseFailAlloc_5512_;
goto v_reusejp_5510_;
}
v_reusejp_5510_:
{
return v___x_5511_;
}
}
}
}
else
{
lean_object* v_val_5514_; lean_object* v_dummy_5515_; lean_object* v_nargs_5516_; lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; lean_object* v___x_5522_; lean_object* v___x_5523_; lean_object* v___x_5525_; 
lean_dec_ref(v_env_5483_);
lean_dec(v_declName_5480_);
lean_del_object(v___x_5453_);
lean_dec(v_fieldName_5444_);
v_val_5514_ = lean_ctor_get(v___x_5489_, 0);
lean_inc(v_val_5514_);
lean_dec_ref_known(v___x_5489_, 1);
v_dummy_5515_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5516_ = l_Lean_Expr_getAppNumArgs(v_a_5456_);
lean_inc(v_nargs_5516_);
v___x_5517_ = lean_mk_array(v_nargs_5516_, v_dummy_5515_);
v___x_5518_ = lean_unsigned_to_nat(1u);
v___x_5519_ = lean_nat_sub(v_nargs_5516_, v___x_5518_);
lean_dec(v_nargs_5516_);
v___x_5520_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5456_, v___x_5517_, v___x_5519_);
v___x_5521_ = l_Lean_mkConst(v_val_5514_, v_us_5481_);
v___x_5522_ = l_Lean_mkAppN(v___x_5521_, v___x_5520_);
lean_dec_ref(v___x_5520_);
v___x_5523_ = l_Lean_Expr_app___override(v___x_5522_, v_s_5443_);
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 0, v___x_5523_);
v___x_5525_ = v___x_5458_;
goto v_reusejp_5524_;
}
else
{
lean_object* v_reuseFailAlloc_5526_; 
v_reuseFailAlloc_5526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5526_, 0, v___x_5523_);
v___x_5525_ = v_reuseFailAlloc_5526_;
goto v_reusejp_5524_;
}
v_reusejp_5524_:
{
return v___x_5525_;
}
}
}
}
else
{
lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v___x_5545_; 
lean_dec_ref(v___x_5479_);
lean_del_object(v___x_5458_);
lean_del_object(v___x_5453_);
lean_dec(v_fieldName_5444_);
v___x_5541_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5542_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5543_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5443_, v_a_5456_);
v___x_5544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5544_, 0, v___x_5542_);
lean_ctor_set(v___x_5544_, 1, v___x_5543_);
v___x_5545_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5541_, v___x_5544_, v_a_5445_, v_a_5446_, v_a_5447_, v_a_5448_);
return v___x_5545_;
}
v___jp_5460_:
{
lean_object* v___x_5465_; lean_object* v___x_5466_; uint8_t v___x_5467_; lean_object* v___x_5468_; lean_object* v___x_5470_; 
v___x_5465_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5466_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5467_ = 1;
v___x_5468_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5444_, v___x_5467_);
if (v_isShared_5454_ == 0)
{
lean_ctor_set_tag(v___x_5453_, 3);
lean_ctor_set(v___x_5453_, 0, v___x_5468_);
v___x_5470_ = v___x_5453_;
goto v_reusejp_5469_;
}
else
{
lean_object* v_reuseFailAlloc_5478_; 
v_reuseFailAlloc_5478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5478_, 0, v___x_5468_);
v___x_5470_ = v_reuseFailAlloc_5478_;
goto v_reusejp_5469_;
}
v_reusejp_5469_:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; lean_object* v___x_5477_; 
v___x_5471_ = l_Lean_MessageData_ofFormat(v___x_5470_);
v___x_5472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5472_, 0, v___x_5466_);
lean_ctor_set(v___x_5472_, 1, v___x_5471_);
v___x_5473_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5474_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5474_, 0, v___x_5472_);
lean_ctor_set(v___x_5474_, 1, v___x_5473_);
v___x_5475_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5443_, v_a_5456_);
v___x_5476_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5476_, 0, v___x_5474_);
lean_ctor_set(v___x_5476_, 1, v___x_5475_);
v___x_5477_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5465_, v___x_5476_, v___y_5461_, v___y_5464_, v___y_5462_, v___y_5463_);
return v___x_5477_;
}
}
}
}
else
{
lean_del_object(v___x_5453_);
lean_dec(v_fieldName_5444_);
lean_dec_ref(v_s_5443_);
return v___x_5455_;
}
}
}
else
{
lean_dec(v_fieldName_5444_);
lean_dec_ref(v_s_5443_);
return v___x_5450_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5548_, lean_object* v_declName_5549_, lean_object* v_s_5550_, lean_object* v_fieldName_5551_, lean_object* v_as_5552_, size_t v_sz_5553_, size_t v_i_5554_, lean_object* v_b_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_){
_start:
{
lean_object* v_a_5562_; uint8_t v___x_5566_; 
v___x_5566_ = lean_usize_dec_lt(v_i_5554_, v_sz_5553_);
if (v___x_5566_ == 0)
{
lean_object* v___x_5567_; 
lean_dec(v_fieldName_5551_);
lean_dec_ref(v_s_5550_);
lean_dec(v_declName_5549_);
lean_dec_ref(v___x_5548_);
v___x_5567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5567_, 0, v_b_5555_);
return v___x_5567_;
}
else
{
lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v_a_5570_; lean_object* v___x_5571_; 
lean_dec_ref(v_b_5555_);
v___x_5568_ = lean_box(0);
v___x_5569_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5570_ = lean_array_uget_borrowed(v_as_5552_, v_i_5554_);
lean_inc(v_a_5570_);
lean_inc(v_declName_5549_);
lean_inc_ref(v___x_5548_);
v___x_5571_ = l_Lean_isSubobjectField_x3f(v___x_5548_, v_declName_5549_, v_a_5570_);
if (lean_obj_tag(v___x_5571_) == 0)
{
v_a_5562_ = v___x_5569_;
goto v___jp_5561_;
}
else
{
lean_object* v___x_5573_; uint8_t v_isShared_5574_; uint8_t v_isSharedCheck_5630_; 
v_isSharedCheck_5630_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5630_ == 0)
{
lean_object* v_unused_5631_; 
v_unused_5631_ = lean_ctor_get(v___x_5571_, 0);
lean_dec(v_unused_5631_);
v___x_5573_ = v___x_5571_;
v_isShared_5574_ = v_isSharedCheck_5630_;
goto v_resetjp_5572_;
}
else
{
lean_dec(v___x_5571_);
v___x_5573_ = lean_box(0);
v_isShared_5574_ = v_isSharedCheck_5630_;
goto v_resetjp_5572_;
}
v_resetjp_5572_:
{
lean_object* v___x_5575_; 
lean_inc(v_a_5570_);
lean_inc_ref(v_s_5550_);
v___x_5575_ = l_Lean_Meta_mkProjection(v_s_5550_, v_a_5570_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_);
if (lean_obj_tag(v___x_5575_) == 0)
{
lean_object* v_a_5576_; lean_object* v___x_5577_; 
v_a_5576_ = lean_ctor_get(v___x_5575_, 0);
lean_inc(v_a_5576_);
lean_dec_ref_known(v___x_5575_, 1);
v___x_5577_ = l_Lean_Meta_saveState___redArg(v___y_5557_, v___y_5559_);
if (lean_obj_tag(v___x_5577_) == 0)
{
lean_object* v_a_5578_; lean_object* v___x_5579_; 
v_a_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_a_5578_);
lean_dec_ref_known(v___x_5577_, 1);
lean_inc(v_fieldName_5551_);
v___x_5579_ = l_Lean_Meta_mkProjection(v_a_5576_, v_fieldName_5551_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_);
if (lean_obj_tag(v___x_5579_) == 0)
{
lean_object* v_a_5580_; lean_object* v___x_5582_; uint8_t v_isShared_5583_; uint8_t v_isSharedCheck_5592_; 
lean_dec(v_a_5578_);
lean_dec(v_fieldName_5551_);
lean_dec_ref(v_s_5550_);
lean_dec(v_declName_5549_);
lean_dec_ref(v___x_5548_);
v_a_5580_ = lean_ctor_get(v___x_5579_, 0);
v_isSharedCheck_5592_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5592_ == 0)
{
v___x_5582_ = v___x_5579_;
v_isShared_5583_ = v_isSharedCheck_5592_;
goto v_resetjp_5581_;
}
else
{
lean_inc(v_a_5580_);
lean_dec(v___x_5579_);
v___x_5582_ = lean_box(0);
v_isShared_5583_ = v_isSharedCheck_5592_;
goto v_resetjp_5581_;
}
v_resetjp_5581_:
{
lean_object* v___x_5585_; 
if (v_isShared_5574_ == 0)
{
lean_ctor_set(v___x_5573_, 0, v_a_5580_);
v___x_5585_ = v___x_5573_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v_a_5580_);
v___x_5585_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
lean_object* v___x_5586_; lean_object* v___x_5587_; lean_object* v___x_5589_; 
v___x_5586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5585_);
v___x_5587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
lean_ctor_set(v___x_5587_, 1, v___x_5568_);
if (v_isShared_5583_ == 0)
{
lean_ctor_set(v___x_5582_, 0, v___x_5587_);
v___x_5589_ = v___x_5582_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5590_; 
v_reuseFailAlloc_5590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5590_, 0, v___x_5587_);
v___x_5589_ = v_reuseFailAlloc_5590_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
return v___x_5589_;
}
}
}
}
else
{
lean_object* v_a_5593_; lean_object* v___x_5595_; uint8_t v_isShared_5596_; uint8_t v_isSharedCheck_5613_; 
lean_del_object(v___x_5573_);
v_a_5593_ = lean_ctor_get(v___x_5579_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5579_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5595_ = v___x_5579_;
v_isShared_5596_ = v_isSharedCheck_5613_;
goto v_resetjp_5594_;
}
else
{
lean_inc(v_a_5593_);
lean_dec(v___x_5579_);
v___x_5595_ = lean_box(0);
v_isShared_5596_ = v_isSharedCheck_5613_;
goto v_resetjp_5594_;
}
v_resetjp_5594_:
{
uint8_t v___y_5598_; uint8_t v___x_5611_; 
v___x_5611_ = l_Lean_Exception_isInterrupt(v_a_5593_);
if (v___x_5611_ == 0)
{
uint8_t v___x_5612_; 
lean_inc(v_a_5593_);
v___x_5612_ = l_Lean_Exception_isRuntime(v_a_5593_);
v___y_5598_ = v___x_5612_;
goto v___jp_5597_;
}
else
{
v___y_5598_ = v___x_5611_;
goto v___jp_5597_;
}
v___jp_5597_:
{
if (v___y_5598_ == 0)
{
lean_object* v___x_5599_; 
lean_del_object(v___x_5595_);
lean_dec(v_a_5593_);
v___x_5599_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5578_, v___y_5557_, v___y_5559_);
lean_dec(v_a_5578_);
if (lean_obj_tag(v___x_5599_) == 0)
{
lean_dec_ref_known(v___x_5599_, 1);
v_a_5562_ = v___x_5569_;
goto v___jp_5561_;
}
else
{
lean_object* v_a_5600_; lean_object* v___x_5602_; uint8_t v_isShared_5603_; uint8_t v_isSharedCheck_5607_; 
lean_dec(v_fieldName_5551_);
lean_dec_ref(v_s_5550_);
lean_dec(v_declName_5549_);
lean_dec_ref(v___x_5548_);
v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
v_isSharedCheck_5607_ = !lean_is_exclusive(v___x_5599_);
if (v_isSharedCheck_5607_ == 0)
{
v___x_5602_ = v___x_5599_;
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
else
{
lean_inc(v_a_5600_);
lean_dec(v___x_5599_);
v___x_5602_ = lean_box(0);
v_isShared_5603_ = v_isSharedCheck_5607_;
goto v_resetjp_5601_;
}
v_resetjp_5601_:
{
lean_object* v___x_5605_; 
if (v_isShared_5603_ == 0)
{
v___x_5605_ = v___x_5602_;
goto v_reusejp_5604_;
}
else
{
lean_object* v_reuseFailAlloc_5606_; 
v_reuseFailAlloc_5606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5606_, 0, v_a_5600_);
v___x_5605_ = v_reuseFailAlloc_5606_;
goto v_reusejp_5604_;
}
v_reusejp_5604_:
{
return v___x_5605_;
}
}
}
}
else
{
lean_object* v___x_5609_; 
lean_dec(v_a_5578_);
lean_dec(v_fieldName_5551_);
lean_dec_ref(v_s_5550_);
lean_dec(v_declName_5549_);
lean_dec_ref(v___x_5548_);
if (v_isShared_5596_ == 0)
{
v___x_5609_ = v___x_5595_;
goto v_reusejp_5608_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_a_5593_);
v___x_5609_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5608_;
}
v_reusejp_5608_:
{
return v___x_5609_;
}
}
}
}
}
}
else
{
lean_object* v_a_5614_; lean_object* v___x_5616_; uint8_t v_isShared_5617_; uint8_t v_isSharedCheck_5621_; 
lean_dec(v_a_5576_);
lean_del_object(v___x_5573_);
lean_dec(v_fieldName_5551_);
lean_dec_ref(v_s_5550_);
lean_dec(v_declName_5549_);
lean_dec_ref(v___x_5548_);
v_a_5614_ = lean_ctor_get(v___x_5577_, 0);
v_isSharedCheck_5621_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5621_ == 0)
{
v___x_5616_ = v___x_5577_;
v_isShared_5617_ = v_isSharedCheck_5621_;
goto v_resetjp_5615_;
}
else
{
lean_inc(v_a_5614_);
lean_dec(v___x_5577_);
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
lean_del_object(v___x_5573_);
lean_dec(v_fieldName_5551_);
lean_dec_ref(v_s_5550_);
lean_dec(v_declName_5549_);
lean_dec_ref(v___x_5548_);
v_a_5622_ = lean_ctor_get(v___x_5575_, 0);
v_isSharedCheck_5629_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5629_ == 0)
{
v___x_5624_ = v___x_5575_;
v_isShared_5625_ = v_isSharedCheck_5629_;
goto v_resetjp_5623_;
}
else
{
lean_inc(v_a_5622_);
lean_dec(v___x_5575_);
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
v___jp_5561_:
{
size_t v___x_5563_; size_t v___x_5564_; 
v___x_5563_ = ((size_t)1ULL);
v___x_5564_ = lean_usize_add(v_i_5554_, v___x_5563_);
lean_inc_ref(v_a_5562_);
v_i_5554_ = v___x_5564_;
v_b_5555_ = v_a_5562_;
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
lean_object* v___x_6155_; 
lean_inc_ref(v_h_6149_);
v___x_6155_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6149_, v_a_6151_);
if (lean_obj_tag(v___x_6155_) == 0)
{
lean_object* v_a_6156_; lean_object* v___x_6158_; uint8_t v_isShared_6159_; uint8_t v_isSharedCheck_6181_; 
v_a_6156_ = lean_ctor_get(v___x_6155_, 0);
v_isSharedCheck_6181_ = !lean_is_exclusive(v___x_6155_);
if (v_isSharedCheck_6181_ == 0)
{
v___x_6158_ = v___x_6155_;
v_isShared_6159_ = v_isSharedCheck_6181_;
goto v_resetjp_6157_;
}
else
{
lean_inc(v_a_6156_);
lean_dec(v___x_6155_);
v___x_6158_ = lean_box(0);
v_isShared_6159_ = v_isSharedCheck_6181_;
goto v_resetjp_6157_;
}
v_resetjp_6157_:
{
lean_object* v___y_6161_; lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6164_; lean_object* v___x_6170_; uint8_t v___x_6171_; 
v___x_6170_ = l_Lean_Expr_cleanupAnnotations(v_a_6156_);
v___x_6171_ = l_Lean_Expr_isApp(v___x_6170_);
if (v___x_6171_ == 0)
{
lean_dec_ref(v___x_6170_);
lean_del_object(v___x_6158_);
v___y_6161_ = v_a_6150_;
v___y_6162_ = v_a_6151_;
v___y_6163_ = v_a_6152_;
v___y_6164_ = v_a_6153_;
goto v___jp_6160_;
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
lean_del_object(v___x_6158_);
v___y_6161_ = v_a_6150_;
v___y_6162_ = v_a_6151_;
v___y_6163_ = v_a_6152_;
v___y_6164_ = v_a_6153_;
goto v___jp_6160_;
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
lean_del_object(v___x_6158_);
v___y_6161_ = v_a_6150_;
v___y_6162_ = v_a_6151_;
v___y_6163_ = v_a_6152_;
v___y_6164_ = v_a_6153_;
goto v___jp_6160_;
}
else
{
lean_object* v___x_6179_; 
lean_dec_ref(v_h_6149_);
if (v_isShared_6159_ == 0)
{
lean_ctor_set(v___x_6158_, 0, v_arg_6172_);
v___x_6179_ = v___x_6158_;
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
v___jp_6160_:
{
lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; 
v___x_6165_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6166_ = lean_unsigned_to_nat(1u);
v___x_6167_ = lean_mk_empty_array_with_capacity(v___x_6166_);
v___x_6168_ = lean_array_push(v___x_6167_, v_h_6149_);
v___x_6169_ = l_Lean_Meta_mkAppM(v___x_6165_, v___x_6168_, v___y_6161_, v___y_6162_, v___y_6163_, v___y_6164_);
return v___x_6169_;
}
}
}
else
{
lean_dec_ref(v_h_6149_);
return v___x_6155_;
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
lean_object* v___x_6217_; 
lean_inc_ref(v_h_6211_);
v___x_6217_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6211_, v_a_6213_);
if (lean_obj_tag(v___x_6217_) == 0)
{
lean_object* v_a_6218_; lean_object* v___x_6220_; uint8_t v_isShared_6221_; uint8_t v_isSharedCheck_6243_; 
v_a_6218_ = lean_ctor_get(v___x_6217_, 0);
v_isSharedCheck_6243_ = !lean_is_exclusive(v___x_6217_);
if (v_isSharedCheck_6243_ == 0)
{
v___x_6220_ = v___x_6217_;
v_isShared_6221_ = v_isSharedCheck_6243_;
goto v_resetjp_6219_;
}
else
{
lean_inc(v_a_6218_);
lean_dec(v___x_6217_);
v___x_6220_ = lean_box(0);
v_isShared_6221_ = v_isSharedCheck_6243_;
goto v_resetjp_6219_;
}
v_resetjp_6219_:
{
lean_object* v___y_6223_; lean_object* v___y_6224_; lean_object* v___y_6225_; lean_object* v___y_6226_; lean_object* v___x_6232_; uint8_t v___x_6233_; 
v___x_6232_ = l_Lean_Expr_cleanupAnnotations(v_a_6218_);
v___x_6233_ = l_Lean_Expr_isApp(v___x_6232_);
if (v___x_6233_ == 0)
{
lean_dec_ref(v___x_6232_);
lean_del_object(v___x_6220_);
v___y_6223_ = v_a_6212_;
v___y_6224_ = v_a_6213_;
v___y_6225_ = v_a_6214_;
v___y_6226_ = v_a_6215_;
goto v___jp_6222_;
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
lean_del_object(v___x_6220_);
v___y_6223_ = v_a_6212_;
v___y_6224_ = v_a_6213_;
v___y_6225_ = v_a_6214_;
v___y_6226_ = v_a_6215_;
goto v___jp_6222_;
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
lean_del_object(v___x_6220_);
v___y_6223_ = v_a_6212_;
v___y_6224_ = v_a_6213_;
v___y_6225_ = v_a_6214_;
v___y_6226_ = v_a_6215_;
goto v___jp_6222_;
}
else
{
lean_object* v___x_6241_; 
lean_dec_ref(v_h_6211_);
if (v_isShared_6221_ == 0)
{
lean_ctor_set(v___x_6220_, 0, v_arg_6234_);
v___x_6241_ = v___x_6220_;
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
v___jp_6222_:
{
lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; 
v___x_6227_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6228_ = lean_unsigned_to_nat(1u);
v___x_6229_ = lean_mk_empty_array_with_capacity(v___x_6228_);
v___x_6230_ = lean_array_push(v___x_6229_, v_h_6211_);
v___x_6231_ = l_Lean_Meta_mkAppM(v___x_6227_, v___x_6230_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_);
return v___x_6231_;
}
}
}
else
{
lean_dec_ref(v_h_6211_);
return v___x_6217_;
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
lean_object* v___x_6273_; 
lean_inc_ref(v_h_6267_);
v___x_6273_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6267_, v_a_6269_);
if (lean_obj_tag(v___x_6273_) == 0)
{
lean_object* v_a_6274_; lean_object* v___x_6276_; uint8_t v_isShared_6277_; uint8_t v_isSharedCheck_6305_; 
v_a_6274_ = lean_ctor_get(v___x_6273_, 0);
v_isSharedCheck_6305_ = !lean_is_exclusive(v___x_6273_);
if (v_isSharedCheck_6305_ == 0)
{
v___x_6276_ = v___x_6273_;
v_isShared_6277_ = v_isSharedCheck_6305_;
goto v_resetjp_6275_;
}
else
{
lean_inc(v_a_6274_);
lean_dec(v___x_6273_);
v___x_6276_ = lean_box(0);
v_isShared_6277_ = v_isSharedCheck_6305_;
goto v_resetjp_6275_;
}
v_resetjp_6275_:
{
lean_object* v___y_6279_; lean_object* v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___x_6294_; uint8_t v___x_6295_; 
v___x_6294_ = l_Lean_Expr_cleanupAnnotations(v_a_6274_);
v___x_6295_ = l_Lean_Expr_isApp(v___x_6294_);
if (v___x_6295_ == 0)
{
lean_dec_ref(v___x_6294_);
lean_del_object(v___x_6276_);
v___y_6279_ = v_a_6268_;
v___y_6280_ = v_a_6269_;
v___y_6281_ = v_a_6270_;
v___y_6282_ = v_a_6271_;
goto v___jp_6278_;
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
lean_del_object(v___x_6276_);
v___y_6279_ = v_a_6268_;
v___y_6280_ = v_a_6269_;
v___y_6281_ = v_a_6270_;
v___y_6282_ = v_a_6271_;
goto v___jp_6278_;
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
lean_del_object(v___x_6276_);
v___y_6279_ = v_a_6268_;
v___y_6280_ = v_a_6269_;
v___y_6281_ = v_a_6270_;
v___y_6282_ = v_a_6271_;
goto v___jp_6278_;
}
else
{
lean_object* v___x_6303_; 
lean_dec_ref(v_h_6267_);
if (v_isShared_6277_ == 0)
{
lean_ctor_set(v___x_6276_, 0, v_arg_6296_);
v___x_6303_ = v___x_6276_;
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
v___jp_6278_:
{
lean_object* v___x_6283_; 
lean_inc(v___y_6282_);
lean_inc_ref(v___y_6281_);
lean_inc(v___y_6280_);
lean_inc_ref(v___y_6279_);
lean_inc_ref(v_h_6267_);
v___x_6283_ = lean_infer_type(v_h_6267_, v___y_6279_, v___y_6280_, v___y_6281_, v___y_6282_);
if (lean_obj_tag(v___x_6283_) == 0)
{
lean_object* v_a_6284_; lean_object* v___x_6286_; uint8_t v_isShared_6287_; uint8_t v_isSharedCheck_6293_; 
v_a_6284_ = lean_ctor_get(v___x_6283_, 0);
v_isSharedCheck_6293_ = !lean_is_exclusive(v___x_6283_);
if (v_isSharedCheck_6293_ == 0)
{
v___x_6286_ = v___x_6283_;
v_isShared_6287_ = v_isSharedCheck_6293_;
goto v_resetjp_6285_;
}
else
{
lean_inc(v_a_6284_);
lean_dec(v___x_6283_);
v___x_6286_ = lean_box(0);
v_isShared_6287_ = v_isSharedCheck_6293_;
goto v_resetjp_6285_;
}
v_resetjp_6285_:
{
lean_object* v___x_6288_; lean_object* v___x_6289_; lean_object* v___x_6291_; 
v___x_6288_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6289_ = l_Lean_mkAppB(v___x_6288_, v_a_6284_, v_h_6267_);
if (v_isShared_6287_ == 0)
{
lean_ctor_set(v___x_6286_, 0, v___x_6289_);
v___x_6291_ = v___x_6286_;
goto v_reusejp_6290_;
}
else
{
lean_object* v_reuseFailAlloc_6292_; 
v_reuseFailAlloc_6292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6292_, 0, v___x_6289_);
v___x_6291_ = v_reuseFailAlloc_6292_;
goto v_reusejp_6290_;
}
v_reusejp_6290_:
{
return v___x_6291_;
}
}
}
else
{
lean_dec_ref(v_h_6267_);
return v___x_6283_;
}
}
}
}
else
{
lean_dec_ref(v_h_6267_);
return v___x_6273_;
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
lean_object* v___y_6469_; uint8_t v___y_6470_; lean_object* v___y_6474_; lean_object* v_a_6475_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; 
v___x_6478_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6479_ = lean_unsigned_to_nat(1u);
v___x_6480_ = lean_mk_empty_array_with_capacity(v___x_6479_);
v___x_6481_ = lean_array_push(v___x_6480_, v_m_6462_);
v___x_6482_ = l_Lean_Meta_mkAppM(v___x_6478_, v___x_6481_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_);
if (lean_obj_tag(v___x_6482_) == 0)
{
lean_object* v_a_6483_; lean_object* v___x_6484_; lean_object* v___x_6485_; 
v_a_6483_ = lean_ctor_get(v___x_6482_, 0);
lean_inc(v_a_6483_);
lean_dec_ref_known(v___x_6482_, 1);
v___x_6484_ = lean_box(0);
v___x_6485_ = l_Lean_Meta_trySynthInstance(v_a_6483_, v___x_6484_, v_a_6463_, v_a_6464_, v_a_6465_, v_a_6466_);
if (lean_obj_tag(v___x_6485_) == 0)
{
lean_object* v_a_6486_; lean_object* v___x_6488_; uint8_t v_isShared_6489_; uint8_t v_isSharedCheck_6504_; 
v_a_6486_ = lean_ctor_get(v___x_6485_, 0);
v_isSharedCheck_6504_ = !lean_is_exclusive(v___x_6485_);
if (v_isSharedCheck_6504_ == 0)
{
v___x_6488_ = v___x_6485_;
v_isShared_6489_ = v_isSharedCheck_6504_;
goto v_resetjp_6487_;
}
else
{
lean_inc(v_a_6486_);
lean_dec(v___x_6485_);
v___x_6488_ = lean_box(0);
v_isShared_6489_ = v_isSharedCheck_6504_;
goto v_resetjp_6487_;
}
v_resetjp_6487_:
{
if (lean_obj_tag(v_a_6486_) == 1)
{
lean_object* v_a_6490_; lean_object* v___x_6492_; uint8_t v_isShared_6493_; uint8_t v_isSharedCheck_6500_; 
v_a_6490_ = lean_ctor_get(v_a_6486_, 0);
v_isSharedCheck_6500_ = !lean_is_exclusive(v_a_6486_);
if (v_isSharedCheck_6500_ == 0)
{
v___x_6492_ = v_a_6486_;
v_isShared_6493_ = v_isSharedCheck_6500_;
goto v_resetjp_6491_;
}
else
{
lean_inc(v_a_6490_);
lean_dec(v_a_6486_);
v___x_6492_ = lean_box(0);
v_isShared_6493_ = v_isSharedCheck_6500_;
goto v_resetjp_6491_;
}
v_resetjp_6491_:
{
lean_object* v___x_6495_; 
if (v_isShared_6493_ == 0)
{
v___x_6495_ = v___x_6492_;
goto v_reusejp_6494_;
}
else
{
lean_object* v_reuseFailAlloc_6499_; 
v_reuseFailAlloc_6499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6499_, 0, v_a_6490_);
v___x_6495_ = v_reuseFailAlloc_6499_;
goto v_reusejp_6494_;
}
v_reusejp_6494_:
{
lean_object* v___x_6497_; 
if (v_isShared_6489_ == 0)
{
lean_ctor_set(v___x_6488_, 0, v___x_6495_);
v___x_6497_ = v___x_6488_;
goto v_reusejp_6496_;
}
else
{
lean_object* v_reuseFailAlloc_6498_; 
v_reuseFailAlloc_6498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6498_, 0, v___x_6495_);
v___x_6497_ = v_reuseFailAlloc_6498_;
goto v_reusejp_6496_;
}
v_reusejp_6496_:
{
return v___x_6497_;
}
}
}
}
else
{
lean_object* v___x_6502_; 
lean_dec(v_a_6486_);
if (v_isShared_6489_ == 0)
{
lean_ctor_set(v___x_6488_, 0, v___x_6484_);
v___x_6502_ = v___x_6488_;
goto v_reusejp_6501_;
}
else
{
lean_object* v_reuseFailAlloc_6503_; 
v_reuseFailAlloc_6503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6503_, 0, v___x_6484_);
v___x_6502_ = v_reuseFailAlloc_6503_;
goto v_reusejp_6501_;
}
v_reusejp_6501_:
{
return v___x_6502_;
}
}
}
}
else
{
lean_object* v_a_6505_; lean_object* v___x_6507_; uint8_t v_isShared_6508_; uint8_t v_isSharedCheck_6512_; 
v_a_6505_ = lean_ctor_get(v___x_6485_, 0);
v_isSharedCheck_6512_ = !lean_is_exclusive(v___x_6485_);
if (v_isSharedCheck_6512_ == 0)
{
v___x_6507_ = v___x_6485_;
v_isShared_6508_ = v_isSharedCheck_6512_;
goto v_resetjp_6506_;
}
else
{
lean_inc(v_a_6505_);
lean_dec(v___x_6485_);
v___x_6507_ = lean_box(0);
v_isShared_6508_ = v_isSharedCheck_6512_;
goto v_resetjp_6506_;
}
v_resetjp_6506_:
{
lean_object* v___x_6510_; 
lean_inc(v_a_6505_);
if (v_isShared_6508_ == 0)
{
v___x_6510_ = v___x_6507_;
goto v_reusejp_6509_;
}
else
{
lean_object* v_reuseFailAlloc_6511_; 
v_reuseFailAlloc_6511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6511_, 0, v_a_6505_);
v___x_6510_ = v_reuseFailAlloc_6511_;
goto v_reusejp_6509_;
}
v_reusejp_6509_:
{
v___y_6474_ = v___x_6510_;
v_a_6475_ = v_a_6505_;
goto v___jp_6473_;
}
}
}
}
else
{
lean_object* v_a_6513_; lean_object* v___x_6515_; uint8_t v_isShared_6516_; uint8_t v_isSharedCheck_6520_; 
v_a_6513_ = lean_ctor_get(v___x_6482_, 0);
v_isSharedCheck_6520_ = !lean_is_exclusive(v___x_6482_);
if (v_isSharedCheck_6520_ == 0)
{
v___x_6515_ = v___x_6482_;
v_isShared_6516_ = v_isSharedCheck_6520_;
goto v_resetjp_6514_;
}
else
{
lean_inc(v_a_6513_);
lean_dec(v___x_6482_);
v___x_6515_ = lean_box(0);
v_isShared_6516_ = v_isSharedCheck_6520_;
goto v_resetjp_6514_;
}
v_resetjp_6514_:
{
lean_object* v___x_6518_; 
lean_inc(v_a_6513_);
if (v_isShared_6516_ == 0)
{
v___x_6518_ = v___x_6515_;
goto v_reusejp_6517_;
}
else
{
lean_object* v_reuseFailAlloc_6519_; 
v_reuseFailAlloc_6519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6519_, 0, v_a_6513_);
v___x_6518_ = v_reuseFailAlloc_6519_;
goto v_reusejp_6517_;
}
v_reusejp_6517_:
{
v___y_6474_ = v___x_6518_;
v_a_6475_ = v_a_6513_;
goto v___jp_6473_;
}
}
}
v___jp_6468_:
{
if (v___y_6470_ == 0)
{
lean_object* v___x_6471_; lean_object* v___x_6472_; 
lean_dec_ref(v___y_6469_);
v___x_6471_ = lean_box(0);
v___x_6472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6472_, 0, v___x_6471_);
return v___x_6472_;
}
else
{
return v___y_6469_;
}
}
v___jp_6473_:
{
uint8_t v___x_6476_; 
v___x_6476_ = l_Lean_Exception_isInterrupt(v_a_6475_);
if (v___x_6476_ == 0)
{
uint8_t v___x_6477_; 
v___x_6477_ = l_Lean_Exception_isRuntime(v_a_6475_);
v___y_6469_ = v___y_6474_;
v___y_6470_ = v___x_6477_;
goto v___jp_6468_;
}
else
{
lean_dec_ref(v_a_6475_);
v___y_6469_ = v___y_6474_;
v___y_6470_ = v___x_6476_;
goto v___jp_6468_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6521_, lean_object* v_a_6522_, lean_object* v_a_6523_, lean_object* v_a_6524_, lean_object* v_a_6525_, lean_object* v_a_6526_){
_start:
{
lean_object* v_res_6527_; 
v_res_6527_ = l_Lean_Meta_isMonad_x3f(v_m_6521_, v_a_6522_, v_a_6523_, v_a_6524_, v_a_6525_);
lean_dec(v_a_6525_);
lean_dec_ref(v_a_6524_);
lean_dec(v_a_6523_);
lean_dec_ref(v_a_6522_);
return v_res_6527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6535_, lean_object* v_n_6536_, lean_object* v_a_6537_, lean_object* v_a_6538_, lean_object* v_a_6539_, lean_object* v_a_6540_){
_start:
{
lean_object* v___x_6542_; 
lean_inc_ref(v_type_6535_);
v___x_6542_ = l_Lean_Meta_getDecLevel(v_type_6535_, v_a_6537_, v_a_6538_, v_a_6539_, v_a_6540_);
if (lean_obj_tag(v___x_6542_) == 0)
{
lean_object* v_a_6543_; lean_object* v___x_6544_; lean_object* v___x_6545_; lean_object* v___x_6546_; lean_object* v___x_6547_; lean_object* v___x_6548_; lean_object* v___x_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; 
v_a_6543_ = lean_ctor_get(v___x_6542_, 0);
lean_inc(v_a_6543_);
lean_dec_ref_known(v___x_6542_, 1);
v___x_6544_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6545_ = lean_box(0);
v___x_6546_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6546_, 0, v_a_6543_);
lean_ctor_set(v___x_6546_, 1, v___x_6545_);
lean_inc_ref(v___x_6546_);
v___x_6547_ = l_Lean_mkConst(v___x_6544_, v___x_6546_);
v___x_6548_ = l_Lean_mkRawNatLit(v_n_6536_);
lean_inc_ref(v___x_6548_);
lean_inc_ref(v_type_6535_);
v___x_6549_ = l_Lean_mkAppB(v___x_6547_, v_type_6535_, v___x_6548_);
v___x_6550_ = lean_box(0);
v___x_6551_ = l_Lean_Meta_synthInstance(v___x_6549_, v___x_6550_, v_a_6537_, v_a_6538_, v_a_6539_, v_a_6540_);
if (lean_obj_tag(v___x_6551_) == 0)
{
lean_object* v_a_6552_; lean_object* v___x_6554_; uint8_t v_isShared_6555_; uint8_t v_isSharedCheck_6562_; 
v_a_6552_ = lean_ctor_get(v___x_6551_, 0);
v_isSharedCheck_6562_ = !lean_is_exclusive(v___x_6551_);
if (v_isSharedCheck_6562_ == 0)
{
v___x_6554_ = v___x_6551_;
v_isShared_6555_ = v_isSharedCheck_6562_;
goto v_resetjp_6553_;
}
else
{
lean_inc(v_a_6552_);
lean_dec(v___x_6551_);
v___x_6554_ = lean_box(0);
v_isShared_6555_ = v_isSharedCheck_6562_;
goto v_resetjp_6553_;
}
v_resetjp_6553_:
{
lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6560_; 
v___x_6556_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6557_ = l_Lean_mkConst(v___x_6556_, v___x_6546_);
v___x_6558_ = l_Lean_mkApp3(v___x_6557_, v_type_6535_, v___x_6548_, v_a_6552_);
if (v_isShared_6555_ == 0)
{
lean_ctor_set(v___x_6554_, 0, v___x_6558_);
v___x_6560_ = v___x_6554_;
goto v_reusejp_6559_;
}
else
{
lean_object* v_reuseFailAlloc_6561_; 
v_reuseFailAlloc_6561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6561_, 0, v___x_6558_);
v___x_6560_ = v_reuseFailAlloc_6561_;
goto v_reusejp_6559_;
}
v_reusejp_6559_:
{
return v___x_6560_;
}
}
}
else
{
lean_dec_ref(v___x_6548_);
lean_dec_ref_known(v___x_6546_, 2);
lean_dec_ref(v_type_6535_);
return v___x_6551_;
}
}
else
{
lean_object* v_a_6563_; lean_object* v___x_6565_; uint8_t v_isShared_6566_; uint8_t v_isSharedCheck_6570_; 
lean_dec(v_n_6536_);
lean_dec_ref(v_type_6535_);
v_a_6563_ = lean_ctor_get(v___x_6542_, 0);
v_isSharedCheck_6570_ = !lean_is_exclusive(v___x_6542_);
if (v_isSharedCheck_6570_ == 0)
{
v___x_6565_ = v___x_6542_;
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
else
{
lean_inc(v_a_6563_);
lean_dec(v___x_6542_);
v___x_6565_ = lean_box(0);
v_isShared_6566_ = v_isSharedCheck_6570_;
goto v_resetjp_6564_;
}
v_resetjp_6564_:
{
lean_object* v___x_6568_; 
if (v_isShared_6566_ == 0)
{
v___x_6568_ = v___x_6565_;
goto v_reusejp_6567_;
}
else
{
lean_object* v_reuseFailAlloc_6569_; 
v_reuseFailAlloc_6569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6569_, 0, v_a_6563_);
v___x_6568_ = v_reuseFailAlloc_6569_;
goto v_reusejp_6567_;
}
v_reusejp_6567_:
{
return v___x_6568_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6571_, lean_object* v_n_6572_, lean_object* v_a_6573_, lean_object* v_a_6574_, lean_object* v_a_6575_, lean_object* v_a_6576_, lean_object* v_a_6577_){
_start:
{
lean_object* v_res_6578_; 
v_res_6578_ = l_Lean_Meta_mkNumeral(v_type_6571_, v_n_6572_, v_a_6573_, v_a_6574_, v_a_6575_, v_a_6576_);
lean_dec(v_a_6576_);
lean_dec_ref(v_a_6575_);
lean_dec(v_a_6574_);
lean_dec_ref(v_a_6573_);
return v_res_6578_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6579_, lean_object* v_opName_6580_, lean_object* v_a_6581_, lean_object* v_b_6582_, lean_object* v_a_6583_, lean_object* v_a_6584_, lean_object* v_a_6585_, lean_object* v_a_6586_){
_start:
{
lean_object* v___x_6588_; 
lean_inc(v_a_6586_);
lean_inc_ref(v_a_6585_);
lean_inc(v_a_6584_);
lean_inc_ref(v_a_6583_);
lean_inc_ref(v_a_6581_);
v___x_6588_ = lean_infer_type(v_a_6581_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_);
if (lean_obj_tag(v___x_6588_) == 0)
{
lean_object* v_a_6589_; lean_object* v___x_6590_; 
v_a_6589_ = lean_ctor_get(v___x_6588_, 0);
lean_inc_n(v_a_6589_, 2);
lean_dec_ref_known(v___x_6588_, 1);
v___x_6590_ = l_Lean_Meta_getDecLevel(v_a_6589_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_);
if (lean_obj_tag(v___x_6590_) == 0)
{
lean_object* v_a_6591_; lean_object* v___x_6592_; lean_object* v___x_6593_; lean_object* v___x_6594_; lean_object* v___x_6595_; lean_object* v___x_6596_; lean_object* v___x_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; 
v_a_6591_ = lean_ctor_get(v___x_6590_, 0);
lean_inc_n(v_a_6591_, 3);
lean_dec_ref_known(v___x_6590_, 1);
v___x_6592_ = lean_box(0);
v___x_6593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6593_, 0, v_a_6591_);
lean_ctor_set(v___x_6593_, 1, v___x_6592_);
v___x_6594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6594_, 0, v_a_6591_);
lean_ctor_set(v___x_6594_, 1, v___x_6593_);
v___x_6595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6595_, 0, v_a_6591_);
lean_ctor_set(v___x_6595_, 1, v___x_6594_);
lean_inc_ref(v___x_6595_);
v___x_6596_ = l_Lean_mkConst(v_className_6579_, v___x_6595_);
lean_inc_n(v_a_6589_, 3);
v___x_6597_ = l_Lean_mkApp3(v___x_6596_, v_a_6589_, v_a_6589_, v_a_6589_);
v___x_6598_ = lean_box(0);
v___x_6599_ = l_Lean_Meta_synthInstance(v___x_6597_, v___x_6598_, v_a_6583_, v_a_6584_, v_a_6585_, v_a_6586_);
if (lean_obj_tag(v___x_6599_) == 0)
{
lean_object* v_a_6600_; lean_object* v___x_6602_; uint8_t v_isShared_6603_; uint8_t v_isSharedCheck_6609_; 
v_a_6600_ = lean_ctor_get(v___x_6599_, 0);
v_isSharedCheck_6609_ = !lean_is_exclusive(v___x_6599_);
if (v_isSharedCheck_6609_ == 0)
{
v___x_6602_ = v___x_6599_;
v_isShared_6603_ = v_isSharedCheck_6609_;
goto v_resetjp_6601_;
}
else
{
lean_inc(v_a_6600_);
lean_dec(v___x_6599_);
v___x_6602_ = lean_box(0);
v_isShared_6603_ = v_isSharedCheck_6609_;
goto v_resetjp_6601_;
}
v_resetjp_6601_:
{
lean_object* v___x_6604_; lean_object* v___x_6605_; lean_object* v___x_6607_; 
v___x_6604_ = l_Lean_mkConst(v_opName_6580_, v___x_6595_);
lean_inc_n(v_a_6589_, 2);
v___x_6605_ = l_Lean_mkApp6(v___x_6604_, v_a_6589_, v_a_6589_, v_a_6589_, v_a_6600_, v_a_6581_, v_b_6582_);
if (v_isShared_6603_ == 0)
{
lean_ctor_set(v___x_6602_, 0, v___x_6605_);
v___x_6607_ = v___x_6602_;
goto v_reusejp_6606_;
}
else
{
lean_object* v_reuseFailAlloc_6608_; 
v_reuseFailAlloc_6608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6608_, 0, v___x_6605_);
v___x_6607_ = v_reuseFailAlloc_6608_;
goto v_reusejp_6606_;
}
v_reusejp_6606_:
{
return v___x_6607_;
}
}
}
else
{
lean_dec_ref_known(v___x_6595_, 2);
lean_dec(v_a_6589_);
lean_dec_ref(v_b_6582_);
lean_dec_ref(v_a_6581_);
lean_dec(v_opName_6580_);
return v___x_6599_;
}
}
else
{
lean_object* v_a_6610_; lean_object* v___x_6612_; uint8_t v_isShared_6613_; uint8_t v_isSharedCheck_6617_; 
lean_dec(v_a_6589_);
lean_dec_ref(v_b_6582_);
lean_dec_ref(v_a_6581_);
lean_dec(v_opName_6580_);
lean_dec(v_className_6579_);
v_a_6610_ = lean_ctor_get(v___x_6590_, 0);
v_isSharedCheck_6617_ = !lean_is_exclusive(v___x_6590_);
if (v_isSharedCheck_6617_ == 0)
{
v___x_6612_ = v___x_6590_;
v_isShared_6613_ = v_isSharedCheck_6617_;
goto v_resetjp_6611_;
}
else
{
lean_inc(v_a_6610_);
lean_dec(v___x_6590_);
v___x_6612_ = lean_box(0);
v_isShared_6613_ = v_isSharedCheck_6617_;
goto v_resetjp_6611_;
}
v_resetjp_6611_:
{
lean_object* v___x_6615_; 
if (v_isShared_6613_ == 0)
{
v___x_6615_ = v___x_6612_;
goto v_reusejp_6614_;
}
else
{
lean_object* v_reuseFailAlloc_6616_; 
v_reuseFailAlloc_6616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6616_, 0, v_a_6610_);
v___x_6615_ = v_reuseFailAlloc_6616_;
goto v_reusejp_6614_;
}
v_reusejp_6614_:
{
return v___x_6615_;
}
}
}
}
else
{
lean_dec_ref(v_b_6582_);
lean_dec_ref(v_a_6581_);
lean_dec(v_opName_6580_);
lean_dec(v_className_6579_);
return v___x_6588_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6618_, lean_object* v_opName_6619_, lean_object* v_a_6620_, lean_object* v_b_6621_, lean_object* v_a_6622_, lean_object* v_a_6623_, lean_object* v_a_6624_, lean_object* v_a_6625_, lean_object* v_a_6626_){
_start:
{
lean_object* v_res_6627_; 
v_res_6627_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6618_, v_opName_6619_, v_a_6620_, v_b_6621_, v_a_6622_, v_a_6623_, v_a_6624_, v_a_6625_);
lean_dec(v_a_6625_);
lean_dec_ref(v_a_6624_);
lean_dec(v_a_6623_);
lean_dec_ref(v_a_6622_);
return v_res_6627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6635_, lean_object* v_b_6636_, lean_object* v_a_6637_, lean_object* v_a_6638_, lean_object* v_a_6639_, lean_object* v_a_6640_){
_start:
{
lean_object* v___x_6642_; lean_object* v___x_6643_; lean_object* v___x_6644_; 
v___x_6642_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6643_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6644_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6642_, v___x_6643_, v_a_6635_, v_b_6636_, v_a_6637_, v_a_6638_, v_a_6639_, v_a_6640_);
return v___x_6644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6645_, lean_object* v_b_6646_, lean_object* v_a_6647_, lean_object* v_a_6648_, lean_object* v_a_6649_, lean_object* v_a_6650_, lean_object* v_a_6651_){
_start:
{
lean_object* v_res_6652_; 
v_res_6652_ = l_Lean_Meta_mkAdd(v_a_6645_, v_b_6646_, v_a_6647_, v_a_6648_, v_a_6649_, v_a_6650_);
lean_dec(v_a_6650_);
lean_dec_ref(v_a_6649_);
lean_dec(v_a_6648_);
lean_dec_ref(v_a_6647_);
return v_res_6652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6660_, lean_object* v_b_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_, lean_object* v_a_6664_, lean_object* v_a_6665_){
_start:
{
lean_object* v___x_6667_; lean_object* v___x_6668_; lean_object* v___x_6669_; 
v___x_6667_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6668_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6669_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6667_, v___x_6668_, v_a_6660_, v_b_6661_, v_a_6662_, v_a_6663_, v_a_6664_, v_a_6665_);
return v___x_6669_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6670_, lean_object* v_b_6671_, lean_object* v_a_6672_, lean_object* v_a_6673_, lean_object* v_a_6674_, lean_object* v_a_6675_, lean_object* v_a_6676_){
_start:
{
lean_object* v_res_6677_; 
v_res_6677_ = l_Lean_Meta_mkSub(v_a_6670_, v_b_6671_, v_a_6672_, v_a_6673_, v_a_6674_, v_a_6675_);
lean_dec(v_a_6675_);
lean_dec_ref(v_a_6674_);
lean_dec(v_a_6673_);
lean_dec_ref(v_a_6672_);
return v_res_6677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6685_, lean_object* v_b_6686_, lean_object* v_a_6687_, lean_object* v_a_6688_, lean_object* v_a_6689_, lean_object* v_a_6690_){
_start:
{
lean_object* v___x_6692_; lean_object* v___x_6693_; lean_object* v___x_6694_; 
v___x_6692_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6693_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6694_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6692_, v___x_6693_, v_a_6685_, v_b_6686_, v_a_6687_, v_a_6688_, v_a_6689_, v_a_6690_);
return v___x_6694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6695_, lean_object* v_b_6696_, lean_object* v_a_6697_, lean_object* v_a_6698_, lean_object* v_a_6699_, lean_object* v_a_6700_, lean_object* v_a_6701_){
_start:
{
lean_object* v_res_6702_; 
v_res_6702_ = l_Lean_Meta_mkMul(v_a_6695_, v_b_6696_, v_a_6697_, v_a_6698_, v_a_6699_, v_a_6700_);
lean_dec(v_a_6700_);
lean_dec_ref(v_a_6699_);
lean_dec(v_a_6698_);
lean_dec_ref(v_a_6697_);
return v_res_6702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6703_, lean_object* v_rName_6704_, lean_object* v_a_6705_, lean_object* v_b_6706_, lean_object* v_a_6707_, lean_object* v_a_6708_, lean_object* v_a_6709_, lean_object* v_a_6710_){
_start:
{
lean_object* v___x_6712_; 
lean_inc(v_a_6710_);
lean_inc_ref(v_a_6709_);
lean_inc(v_a_6708_);
lean_inc_ref(v_a_6707_);
lean_inc_ref(v_a_6705_);
v___x_6712_ = lean_infer_type(v_a_6705_, v_a_6707_, v_a_6708_, v_a_6709_, v_a_6710_);
if (lean_obj_tag(v___x_6712_) == 0)
{
lean_object* v_a_6713_; lean_object* v___x_6714_; 
v_a_6713_ = lean_ctor_get(v___x_6712_, 0);
lean_inc_n(v_a_6713_, 2);
lean_dec_ref_known(v___x_6712_, 1);
v___x_6714_ = l_Lean_Meta_getDecLevel(v_a_6713_, v_a_6707_, v_a_6708_, v_a_6709_, v_a_6710_);
if (lean_obj_tag(v___x_6714_) == 0)
{
lean_object* v_a_6715_; lean_object* v___x_6716_; lean_object* v___x_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; 
v_a_6715_ = lean_ctor_get(v___x_6714_, 0);
lean_inc(v_a_6715_);
lean_dec_ref_known(v___x_6714_, 1);
v___x_6716_ = lean_box(0);
v___x_6717_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6717_, 0, v_a_6715_);
lean_ctor_set(v___x_6717_, 1, v___x_6716_);
lean_inc_ref(v___x_6717_);
v___x_6718_ = l_Lean_mkConst(v_className_6703_, v___x_6717_);
lean_inc(v_a_6713_);
v___x_6719_ = l_Lean_Expr_app___override(v___x_6718_, v_a_6713_);
v___x_6720_ = lean_box(0);
v___x_6721_ = l_Lean_Meta_synthInstance(v___x_6719_, v___x_6720_, v_a_6707_, v_a_6708_, v_a_6709_, v_a_6710_);
if (lean_obj_tag(v___x_6721_) == 0)
{
lean_object* v_a_6722_; lean_object* v___x_6724_; uint8_t v_isShared_6725_; uint8_t v_isSharedCheck_6731_; 
v_a_6722_ = lean_ctor_get(v___x_6721_, 0);
v_isSharedCheck_6731_ = !lean_is_exclusive(v___x_6721_);
if (v_isSharedCheck_6731_ == 0)
{
v___x_6724_ = v___x_6721_;
v_isShared_6725_ = v_isSharedCheck_6731_;
goto v_resetjp_6723_;
}
else
{
lean_inc(v_a_6722_);
lean_dec(v___x_6721_);
v___x_6724_ = lean_box(0);
v_isShared_6725_ = v_isSharedCheck_6731_;
goto v_resetjp_6723_;
}
v_resetjp_6723_:
{
lean_object* v___x_6726_; lean_object* v___x_6727_; lean_object* v___x_6729_; 
v___x_6726_ = l_Lean_mkConst(v_rName_6704_, v___x_6717_);
v___x_6727_ = l_Lean_mkApp4(v___x_6726_, v_a_6713_, v_a_6722_, v_a_6705_, v_b_6706_);
if (v_isShared_6725_ == 0)
{
lean_ctor_set(v___x_6724_, 0, v___x_6727_);
v___x_6729_ = v___x_6724_;
goto v_reusejp_6728_;
}
else
{
lean_object* v_reuseFailAlloc_6730_; 
v_reuseFailAlloc_6730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6730_, 0, v___x_6727_);
v___x_6729_ = v_reuseFailAlloc_6730_;
goto v_reusejp_6728_;
}
v_reusejp_6728_:
{
return v___x_6729_;
}
}
}
else
{
lean_dec_ref_known(v___x_6717_, 2);
lean_dec(v_a_6713_);
lean_dec_ref(v_b_6706_);
lean_dec_ref(v_a_6705_);
lean_dec(v_rName_6704_);
return v___x_6721_;
}
}
else
{
lean_object* v_a_6732_; lean_object* v___x_6734_; uint8_t v_isShared_6735_; uint8_t v_isSharedCheck_6739_; 
lean_dec(v_a_6713_);
lean_dec_ref(v_b_6706_);
lean_dec_ref(v_a_6705_);
lean_dec(v_rName_6704_);
lean_dec(v_className_6703_);
v_a_6732_ = lean_ctor_get(v___x_6714_, 0);
v_isSharedCheck_6739_ = !lean_is_exclusive(v___x_6714_);
if (v_isSharedCheck_6739_ == 0)
{
v___x_6734_ = v___x_6714_;
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
else
{
lean_inc(v_a_6732_);
lean_dec(v___x_6714_);
v___x_6734_ = lean_box(0);
v_isShared_6735_ = v_isSharedCheck_6739_;
goto v_resetjp_6733_;
}
v_resetjp_6733_:
{
lean_object* v___x_6737_; 
if (v_isShared_6735_ == 0)
{
v___x_6737_ = v___x_6734_;
goto v_reusejp_6736_;
}
else
{
lean_object* v_reuseFailAlloc_6738_; 
v_reuseFailAlloc_6738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6738_, 0, v_a_6732_);
v___x_6737_ = v_reuseFailAlloc_6738_;
goto v_reusejp_6736_;
}
v_reusejp_6736_:
{
return v___x_6737_;
}
}
}
}
else
{
lean_dec_ref(v_b_6706_);
lean_dec_ref(v_a_6705_);
lean_dec(v_rName_6704_);
lean_dec(v_className_6703_);
return v___x_6712_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6740_, lean_object* v_rName_6741_, lean_object* v_a_6742_, lean_object* v_b_6743_, lean_object* v_a_6744_, lean_object* v_a_6745_, lean_object* v_a_6746_, lean_object* v_a_6747_, lean_object* v_a_6748_){
_start:
{
lean_object* v_res_6749_; 
v_res_6749_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6740_, v_rName_6741_, v_a_6742_, v_b_6743_, v_a_6744_, v_a_6745_, v_a_6746_, v_a_6747_);
lean_dec(v_a_6747_);
lean_dec_ref(v_a_6746_);
lean_dec(v_a_6745_);
lean_dec_ref(v_a_6744_);
return v_res_6749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6752_, lean_object* v_b_6753_, lean_object* v_a_6754_, lean_object* v_a_6755_, lean_object* v_a_6756_, lean_object* v_a_6757_){
_start:
{
lean_object* v___x_6759_; lean_object* v___x_6760_; lean_object* v___x_6761_; 
v___x_6759_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6760_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6761_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6759_, v___x_6760_, v_a_6752_, v_b_6753_, v_a_6754_, v_a_6755_, v_a_6756_, v_a_6757_);
return v___x_6761_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6762_, lean_object* v_b_6763_, lean_object* v_a_6764_, lean_object* v_a_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_, lean_object* v_a_6768_){
_start:
{
lean_object* v_res_6769_; 
v_res_6769_ = l_Lean_Meta_mkLE(v_a_6762_, v_b_6763_, v_a_6764_, v_a_6765_, v_a_6766_, v_a_6767_);
lean_dec(v_a_6767_);
lean_dec_ref(v_a_6766_);
lean_dec(v_a_6765_);
lean_dec_ref(v_a_6764_);
return v_res_6769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6772_, lean_object* v_b_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_, lean_object* v_a_6776_, lean_object* v_a_6777_){
_start:
{
lean_object* v___x_6779_; lean_object* v___x_6780_; lean_object* v___x_6781_; 
v___x_6779_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6780_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6781_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6779_, v___x_6780_, v_a_6772_, v_b_6773_, v_a_6774_, v_a_6775_, v_a_6776_, v_a_6777_);
return v___x_6781_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6782_, lean_object* v_b_6783_, lean_object* v_a_6784_, lean_object* v_a_6785_, lean_object* v_a_6786_, lean_object* v_a_6787_, lean_object* v_a_6788_){
_start:
{
lean_object* v_res_6789_; 
v_res_6789_ = l_Lean_Meta_mkLT(v_a_6782_, v_b_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_);
lean_dec(v_a_6787_);
lean_dec_ref(v_a_6786_);
lean_dec(v_a_6785_);
lean_dec_ref(v_a_6784_);
return v_res_6789_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6795_, lean_object* v_a_6796_, lean_object* v_a_6797_, lean_object* v_a_6798_, lean_object* v_a_6799_){
_start:
{
lean_object* v___x_6801_; lean_object* v___x_6802_; uint8_t v___x_6803_; 
v___x_6801_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6802_ = lean_unsigned_to_nat(3u);
v___x_6803_ = l_Lean_Expr_isAppOfArity(v_h_6795_, v___x_6801_, v___x_6802_);
if (v___x_6803_ == 0)
{
lean_object* v___x_6804_; lean_object* v___x_6805_; lean_object* v___x_6806_; lean_object* v___x_6807_; lean_object* v___x_6808_; 
v___x_6804_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6805_ = lean_unsigned_to_nat(1u);
v___x_6806_ = lean_mk_empty_array_with_capacity(v___x_6805_);
v___x_6807_ = lean_array_push(v___x_6806_, v_h_6795_);
v___x_6808_ = l_Lean_Meta_mkAppM(v___x_6804_, v___x_6807_, v_a_6796_, v_a_6797_, v_a_6798_, v_a_6799_);
return v___x_6808_;
}
else
{
lean_object* v___x_6809_; lean_object* v___x_6810_; 
v___x_6809_ = l_Lean_Expr_appArg_x21(v_h_6795_);
lean_dec_ref(v_h_6795_);
v___x_6810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6810_, 0, v___x_6809_);
return v___x_6810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6811_, lean_object* v_a_6812_, lean_object* v_a_6813_, lean_object* v_a_6814_, lean_object* v_a_6815_, lean_object* v_a_6816_){
_start:
{
lean_object* v_res_6817_; 
v_res_6817_ = l_Lean_Meta_mkIffOfEq(v_h_6811_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_);
lean_dec(v_a_6815_);
lean_dec_ref(v_a_6814_);
lean_dec(v_a_6813_);
lean_dec_ref(v_a_6812_);
return v_res_6817_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6823_; lean_object* v___x_6824_; lean_object* v___x_6825_; 
v___x_6823_ = lean_box(0);
v___x_6824_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6825_ = l_Lean_mkConst(v___x_6824_, v___x_6823_);
return v___x_6825_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6828_; lean_object* v___x_6829_; lean_object* v___x_6830_; 
v___x_6828_ = lean_box(0);
v___x_6829_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6830_ = l_Lean_mkConst(v___x_6829_, v___x_6828_);
return v___x_6830_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6831_; lean_object* v___x_6832_; lean_object* v___x_6833_; 
v___x_6831_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6832_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6833_, 0, v___x_6832_);
lean_ctor_set(v___x_6833_, 1, v___x_6831_);
return v___x_6833_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6838_; lean_object* v___x_6839_; lean_object* v___x_6840_; 
v___x_6838_ = lean_box(0);
v___x_6839_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6840_ = l_Lean_mkConst(v___x_6839_, v___x_6838_);
return v___x_6840_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6843_; lean_object* v___x_6844_; lean_object* v___x_6845_; 
v___x_6843_ = lean_box(0);
v___x_6844_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6845_ = l_Lean_mkConst(v___x_6844_, v___x_6843_);
return v___x_6845_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6846_, lean_object* v_a_6847_, lean_object* v_a_6848_, lean_object* v_a_6849_, lean_object* v_a_6850_){
_start:
{
if (lean_obj_tag(v_a_6846_) == 0)
{
lean_object* v___x_6852_; lean_object* v___x_6853_; 
v___x_6852_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6853_, 0, v___x_6852_);
return v___x_6853_;
}
else
{
lean_object* v_tail_6854_; 
v_tail_6854_ = lean_ctor_get(v_a_6846_, 1);
if (lean_obj_tag(v_tail_6854_) == 0)
{
lean_object* v_head_6855_; lean_object* v___x_6857_; uint8_t v_isShared_6858_; uint8_t v_isSharedCheck_6879_; 
v_head_6855_ = lean_ctor_get(v_a_6846_, 0);
v_isSharedCheck_6879_ = !lean_is_exclusive(v_a_6846_);
if (v_isSharedCheck_6879_ == 0)
{
lean_object* v_unused_6880_; 
v_unused_6880_ = lean_ctor_get(v_a_6846_, 1);
lean_dec(v_unused_6880_);
v___x_6857_ = v_a_6846_;
v_isShared_6858_ = v_isSharedCheck_6879_;
goto v_resetjp_6856_;
}
else
{
lean_inc(v_head_6855_);
lean_dec(v_a_6846_);
v___x_6857_ = lean_box(0);
v_isShared_6858_ = v_isSharedCheck_6879_;
goto v_resetjp_6856_;
}
v_resetjp_6856_:
{
lean_object* v___x_6859_; 
lean_inc(v_a_6850_);
lean_inc_ref(v_a_6849_);
lean_inc(v_a_6848_);
lean_inc_ref(v_a_6847_);
lean_inc(v_head_6855_);
v___x_6859_ = lean_infer_type(v_head_6855_, v_a_6847_, v_a_6848_, v_a_6849_, v_a_6850_);
if (lean_obj_tag(v___x_6859_) == 0)
{
lean_object* v_a_6860_; lean_object* v___x_6862_; uint8_t v_isShared_6863_; uint8_t v_isSharedCheck_6870_; 
v_a_6860_ = lean_ctor_get(v___x_6859_, 0);
v_isSharedCheck_6870_ = !lean_is_exclusive(v___x_6859_);
if (v_isSharedCheck_6870_ == 0)
{
v___x_6862_ = v___x_6859_;
v_isShared_6863_ = v_isSharedCheck_6870_;
goto v_resetjp_6861_;
}
else
{
lean_inc(v_a_6860_);
lean_dec(v___x_6859_);
v___x_6862_ = lean_box(0);
v_isShared_6863_ = v_isSharedCheck_6870_;
goto v_resetjp_6861_;
}
v_resetjp_6861_:
{
lean_object* v___x_6865_; 
if (v_isShared_6858_ == 0)
{
lean_ctor_set_tag(v___x_6857_, 0);
lean_ctor_set(v___x_6857_, 1, v_a_6860_);
v___x_6865_ = v___x_6857_;
goto v_reusejp_6864_;
}
else
{
lean_object* v_reuseFailAlloc_6869_; 
v_reuseFailAlloc_6869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6869_, 0, v_head_6855_);
lean_ctor_set(v_reuseFailAlloc_6869_, 1, v_a_6860_);
v___x_6865_ = v_reuseFailAlloc_6869_;
goto v_reusejp_6864_;
}
v_reusejp_6864_:
{
lean_object* v___x_6867_; 
if (v_isShared_6863_ == 0)
{
lean_ctor_set(v___x_6862_, 0, v___x_6865_);
v___x_6867_ = v___x_6862_;
goto v_reusejp_6866_;
}
else
{
lean_object* v_reuseFailAlloc_6868_; 
v_reuseFailAlloc_6868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6868_, 0, v___x_6865_);
v___x_6867_ = v_reuseFailAlloc_6868_;
goto v_reusejp_6866_;
}
v_reusejp_6866_:
{
return v___x_6867_;
}
}
}
}
else
{
lean_object* v_a_6871_; lean_object* v___x_6873_; uint8_t v_isShared_6874_; uint8_t v_isSharedCheck_6878_; 
lean_del_object(v___x_6857_);
lean_dec(v_head_6855_);
v_a_6871_ = lean_ctor_get(v___x_6859_, 0);
v_isSharedCheck_6878_ = !lean_is_exclusive(v___x_6859_);
if (v_isSharedCheck_6878_ == 0)
{
v___x_6873_ = v___x_6859_;
v_isShared_6874_ = v_isSharedCheck_6878_;
goto v_resetjp_6872_;
}
else
{
lean_inc(v_a_6871_);
lean_dec(v___x_6859_);
v___x_6873_ = lean_box(0);
v_isShared_6874_ = v_isSharedCheck_6878_;
goto v_resetjp_6872_;
}
v_resetjp_6872_:
{
lean_object* v___x_6876_; 
if (v_isShared_6874_ == 0)
{
v___x_6876_ = v___x_6873_;
goto v_reusejp_6875_;
}
else
{
lean_object* v_reuseFailAlloc_6877_; 
v_reuseFailAlloc_6877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6877_, 0, v_a_6871_);
v___x_6876_ = v_reuseFailAlloc_6877_;
goto v_reusejp_6875_;
}
v_reusejp_6875_:
{
return v___x_6876_;
}
}
}
}
}
else
{
lean_object* v_head_6881_; lean_object* v___x_6882_; 
lean_inc(v_tail_6854_);
v_head_6881_ = lean_ctor_get(v_a_6846_, 0);
lean_inc(v_head_6881_);
lean_dec_ref_known(v_a_6846_, 2);
v___x_6882_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6854_, v_a_6847_, v_a_6848_, v_a_6849_, v_a_6850_);
if (lean_obj_tag(v___x_6882_) == 0)
{
lean_object* v_a_6883_; lean_object* v_fst_6884_; lean_object* v_snd_6885_; lean_object* v___x_6887_; uint8_t v_isShared_6888_; uint8_t v_isSharedCheck_6913_; 
v_a_6883_ = lean_ctor_get(v___x_6882_, 0);
lean_inc(v_a_6883_);
lean_dec_ref_known(v___x_6882_, 1);
v_fst_6884_ = lean_ctor_get(v_a_6883_, 0);
v_snd_6885_ = lean_ctor_get(v_a_6883_, 1);
v_isSharedCheck_6913_ = !lean_is_exclusive(v_a_6883_);
if (v_isSharedCheck_6913_ == 0)
{
v___x_6887_ = v_a_6883_;
v_isShared_6888_ = v_isSharedCheck_6913_;
goto v_resetjp_6886_;
}
else
{
lean_inc(v_snd_6885_);
lean_inc(v_fst_6884_);
lean_dec(v_a_6883_);
v___x_6887_ = lean_box(0);
v_isShared_6888_ = v_isSharedCheck_6913_;
goto v_resetjp_6886_;
}
v_resetjp_6886_:
{
lean_object* v___x_6889_; 
lean_inc(v_a_6850_);
lean_inc_ref(v_a_6849_);
lean_inc(v_a_6848_);
lean_inc_ref(v_a_6847_);
lean_inc(v_head_6881_);
v___x_6889_ = lean_infer_type(v_head_6881_, v_a_6847_, v_a_6848_, v_a_6849_, v_a_6850_);
if (lean_obj_tag(v___x_6889_) == 0)
{
lean_object* v_a_6890_; lean_object* v___x_6892_; uint8_t v_isShared_6893_; uint8_t v_isSharedCheck_6904_; 
v_a_6890_ = lean_ctor_get(v___x_6889_, 0);
v_isSharedCheck_6904_ = !lean_is_exclusive(v___x_6889_);
if (v_isSharedCheck_6904_ == 0)
{
v___x_6892_ = v___x_6889_;
v_isShared_6893_ = v_isSharedCheck_6904_;
goto v_resetjp_6891_;
}
else
{
lean_inc(v_a_6890_);
lean_dec(v___x_6889_);
v___x_6892_ = lean_box(0);
v_isShared_6893_ = v_isSharedCheck_6904_;
goto v_resetjp_6891_;
}
v_resetjp_6891_:
{
lean_object* v___x_6894_; lean_object* v___x_6895_; lean_object* v___x_6896_; lean_object* v___x_6897_; lean_object* v___x_6899_; 
v___x_6894_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6885_);
lean_inc(v_a_6890_);
v___x_6895_ = l_Lean_mkApp4(v___x_6894_, v_a_6890_, v_snd_6885_, v_head_6881_, v_fst_6884_);
v___x_6896_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6897_ = l_Lean_mkAppB(v___x_6896_, v_a_6890_, v_snd_6885_);
if (v_isShared_6888_ == 0)
{
lean_ctor_set(v___x_6887_, 1, v___x_6897_);
lean_ctor_set(v___x_6887_, 0, v___x_6895_);
v___x_6899_ = v___x_6887_;
goto v_reusejp_6898_;
}
else
{
lean_object* v_reuseFailAlloc_6903_; 
v_reuseFailAlloc_6903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6903_, 0, v___x_6895_);
lean_ctor_set(v_reuseFailAlloc_6903_, 1, v___x_6897_);
v___x_6899_ = v_reuseFailAlloc_6903_;
goto v_reusejp_6898_;
}
v_reusejp_6898_:
{
lean_object* v___x_6901_; 
if (v_isShared_6893_ == 0)
{
lean_ctor_set(v___x_6892_, 0, v___x_6899_);
v___x_6901_ = v___x_6892_;
goto v_reusejp_6900_;
}
else
{
lean_object* v_reuseFailAlloc_6902_; 
v_reuseFailAlloc_6902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6902_, 0, v___x_6899_);
v___x_6901_ = v_reuseFailAlloc_6902_;
goto v_reusejp_6900_;
}
v_reusejp_6900_:
{
return v___x_6901_;
}
}
}
}
else
{
lean_object* v_a_6905_; lean_object* v___x_6907_; uint8_t v_isShared_6908_; uint8_t v_isSharedCheck_6912_; 
lean_del_object(v___x_6887_);
lean_dec(v_snd_6885_);
lean_dec(v_fst_6884_);
lean_dec(v_head_6881_);
v_a_6905_ = lean_ctor_get(v___x_6889_, 0);
v_isSharedCheck_6912_ = !lean_is_exclusive(v___x_6889_);
if (v_isSharedCheck_6912_ == 0)
{
v___x_6907_ = v___x_6889_;
v_isShared_6908_ = v_isSharedCheck_6912_;
goto v_resetjp_6906_;
}
else
{
lean_inc(v_a_6905_);
lean_dec(v___x_6889_);
v___x_6907_ = lean_box(0);
v_isShared_6908_ = v_isSharedCheck_6912_;
goto v_resetjp_6906_;
}
v_resetjp_6906_:
{
lean_object* v___x_6910_; 
if (v_isShared_6908_ == 0)
{
v___x_6910_ = v___x_6907_;
goto v_reusejp_6909_;
}
else
{
lean_object* v_reuseFailAlloc_6911_; 
v_reuseFailAlloc_6911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6911_, 0, v_a_6905_);
v___x_6910_ = v_reuseFailAlloc_6911_;
goto v_reusejp_6909_;
}
v_reusejp_6909_:
{
return v___x_6910_;
}
}
}
}
}
else
{
lean_dec(v_head_6881_);
return v___x_6882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6914_, lean_object* v_a_6915_, lean_object* v_a_6916_, lean_object* v_a_6917_, lean_object* v_a_6918_, lean_object* v_a_6919_){
_start:
{
lean_object* v_res_6920_; 
v_res_6920_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6914_, v_a_6915_, v_a_6916_, v_a_6917_, v_a_6918_);
lean_dec(v_a_6918_);
lean_dec_ref(v_a_6917_);
lean_dec(v_a_6916_);
lean_dec_ref(v_a_6915_);
return v_res_6920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6921_, lean_object* v_a_6922_, lean_object* v_a_6923_, lean_object* v_a_6924_, lean_object* v_a_6925_){
_start:
{
lean_object* v___x_6927_; 
v___x_6927_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6921_, v_a_6922_, v_a_6923_, v_a_6924_, v_a_6925_);
if (lean_obj_tag(v___x_6927_) == 0)
{
lean_object* v_a_6928_; lean_object* v___x_6930_; uint8_t v_isShared_6931_; uint8_t v_isSharedCheck_6936_; 
v_a_6928_ = lean_ctor_get(v___x_6927_, 0);
v_isSharedCheck_6936_ = !lean_is_exclusive(v___x_6927_);
if (v_isSharedCheck_6936_ == 0)
{
v___x_6930_ = v___x_6927_;
v_isShared_6931_ = v_isSharedCheck_6936_;
goto v_resetjp_6929_;
}
else
{
lean_inc(v_a_6928_);
lean_dec(v___x_6927_);
v___x_6930_ = lean_box(0);
v_isShared_6931_ = v_isSharedCheck_6936_;
goto v_resetjp_6929_;
}
v_resetjp_6929_:
{
lean_object* v_fst_6932_; lean_object* v___x_6934_; 
v_fst_6932_ = lean_ctor_get(v_a_6928_, 0);
lean_inc(v_fst_6932_);
lean_dec(v_a_6928_);
if (v_isShared_6931_ == 0)
{
lean_ctor_set(v___x_6930_, 0, v_fst_6932_);
v___x_6934_ = v___x_6930_;
goto v_reusejp_6933_;
}
else
{
lean_object* v_reuseFailAlloc_6935_; 
v_reuseFailAlloc_6935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6935_, 0, v_fst_6932_);
v___x_6934_ = v_reuseFailAlloc_6935_;
goto v_reusejp_6933_;
}
v_reusejp_6933_:
{
return v___x_6934_;
}
}
}
else
{
lean_object* v_a_6937_; lean_object* v___x_6939_; uint8_t v_isShared_6940_; uint8_t v_isSharedCheck_6944_; 
v_a_6937_ = lean_ctor_get(v___x_6927_, 0);
v_isSharedCheck_6944_ = !lean_is_exclusive(v___x_6927_);
if (v_isSharedCheck_6944_ == 0)
{
v___x_6939_ = v___x_6927_;
v_isShared_6940_ = v_isSharedCheck_6944_;
goto v_resetjp_6938_;
}
else
{
lean_inc(v_a_6937_);
lean_dec(v___x_6927_);
v___x_6939_ = lean_box(0);
v_isShared_6940_ = v_isSharedCheck_6944_;
goto v_resetjp_6938_;
}
v_resetjp_6938_:
{
lean_object* v___x_6942_; 
if (v_isShared_6940_ == 0)
{
v___x_6942_ = v___x_6939_;
goto v_reusejp_6941_;
}
else
{
lean_object* v_reuseFailAlloc_6943_; 
v_reuseFailAlloc_6943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6943_, 0, v_a_6937_);
v___x_6942_ = v_reuseFailAlloc_6943_;
goto v_reusejp_6941_;
}
v_reusejp_6941_:
{
return v___x_6942_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_6945_, lean_object* v_a_6946_, lean_object* v_a_6947_, lean_object* v_a_6948_, lean_object* v_a_6949_, lean_object* v_a_6950_){
_start:
{
lean_object* v_res_6951_; 
v_res_6951_ = l_Lean_Meta_mkAndIntroN(v_hs_6945_, v_a_6946_, v_a_6947_, v_a_6948_, v_a_6949_);
lean_dec(v_a_6949_);
lean_dec_ref(v_a_6948_);
lean_dec(v_a_6947_);
lean_dec_ref(v_a_6946_);
return v_res_6951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7008_; uint8_t v___x_7009_; lean_object* v___x_7010_; lean_object* v___x_7011_; 
v___x_7008_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7009_ = 0;
v___x_7010_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7011_ = l_Lean_registerTraceClass(v___x_7008_, v___x_7009_, v___x_7010_);
if (lean_obj_tag(v___x_7011_) == 0)
{
lean_object* v___x_7012_; uint8_t v___x_7013_; lean_object* v___x_7014_; 
lean_dec_ref_known(v___x_7011_, 1);
v___x_7012_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7013_ = 1;
v___x_7014_ = l_Lean_registerTraceClass(v___x_7012_, v___x_7013_, v___x_7010_);
if (lean_obj_tag(v___x_7014_) == 0)
{
lean_object* v___x_7015_; lean_object* v___x_7016_; 
lean_dec_ref_known(v___x_7014_, 1);
v___x_7015_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7016_ = l_Lean_registerTraceClass(v___x_7015_, v___x_7013_, v___x_7010_);
return v___x_7016_;
}
else
{
return v___x_7014_;
}
}
else
{
return v___x_7011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7017_){
_start:
{
lean_object* v_res_7018_; 
v_res_7018_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7018_;
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
