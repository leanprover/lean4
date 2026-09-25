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
lean_object* l_Lean_Expr_bvar___override(lean_object*);
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
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_561_ = l_Lean_Expr_appFn_x21(v_a_552_);
v___x_562_ = l_Lean_Expr_appFn_x21(v___x_561_);
v___x_563_ = l_Lean_Expr_appArg_x21(v___x_562_);
lean_dec_ref(v___x_562_);
v___x_564_ = l_Lean_Expr_appArg_x21(v___x_561_);
lean_dec_ref(v___x_561_);
v___x_565_ = l_Lean_Expr_appArg_x21(v_a_552_);
lean_dec(v_a_552_);
lean_inc_ref(v___x_563_);
v___x_566_ = l_Lean_Meta_getLevel(v___x_563_, v_a_544_, v_a_545_, v_a_546_, v_a_547_);
if (lean_obj_tag(v___x_566_) == 0)
{
lean_object* v_a_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_579_; 
v_a_567_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_579_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_579_ == 0)
{
v___x_569_ = v___x_566_;
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_a_567_);
lean_dec(v___x_566_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_579_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_577_; 
v___x_571_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__1));
v___x_572_ = lean_box(0);
v___x_573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_573_, 0, v_a_567_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Lean_mkConst(v___x_571_, v___x_573_);
v___x_575_ = l_Lean_mkApp4(v___x_574_, v___x_563_, v___x_564_, v___x_565_, v_h_543_);
if (v_isShared_570_ == 0)
{
lean_ctor_set(v___x_569_, 0, v___x_575_);
v___x_577_ = v___x_569_;
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
lean_dec_ref(v___x_565_);
lean_dec_ref(v___x_564_);
lean_dec_ref(v___x_563_);
lean_dec_ref(v_h_543_);
v_a_580_ = lean_ctor_get(v___x_566_, 0);
v_isSharedCheck_587_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_587_ == 0)
{
v___x_582_ = v___x_566_;
v_isShared_583_ = v_isSharedCheck_587_;
goto v_resetjp_581_;
}
else
{
lean_inc(v_a_580_);
lean_dec(v___x_566_);
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
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_628_ = l_Lean_Expr_appFn_x21(v_a_611_);
v___x_629_ = l_Lean_Expr_appFn_x21(v___x_628_);
v___x_630_ = l_Lean_Expr_appArg_x21(v___x_629_);
lean_dec_ref(v___x_629_);
v___x_631_ = l_Lean_Expr_appArg_x21(v___x_628_);
lean_dec_ref(v___x_628_);
v___x_632_ = l_Lean_Expr_appArg_x21(v_a_611_);
lean_dec(v_a_611_);
v___x_633_ = l_Lean_Expr_appArg_x21(v_a_613_);
lean_dec(v_a_613_);
lean_inc_ref(v___x_630_);
v___x_634_ = l_Lean_Meta_getLevel(v___x_630_, v_a_602_, v_a_603_, v_a_604_, v_a_605_);
if (lean_obj_tag(v___x_634_) == 0)
{
lean_object* v_a_635_; lean_object* v___x_637_; uint8_t v_isShared_638_; uint8_t v_isSharedCheck_647_; 
v_a_635_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_647_ == 0)
{
v___x_637_ = v___x_634_;
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
else
{
lean_inc(v_a_635_);
lean_dec(v___x_634_);
v___x_637_ = lean_box(0);
v_isShared_638_ = v_isSharedCheck_647_;
goto v_resetjp_636_;
}
v_resetjp_636_:
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_645_; 
v___x_639_ = ((lean_object*)(l_Lean_Meta_mkEqTrans___closed__1));
v___x_640_ = lean_box(0);
v___x_641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_641_, 0, v_a_635_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = l_Lean_mkConst(v___x_639_, v___x_641_);
v___x_643_ = l_Lean_mkApp6(v___x_642_, v___x_630_, v___x_631_, v___x_632_, v___x_633_, v_h_u2081_600_, v_h_u2082_601_);
if (v_isShared_638_ == 0)
{
lean_ctor_set(v___x_637_, 0, v___x_643_);
v___x_645_ = v___x_637_;
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
lean_dec_ref(v___x_633_);
lean_dec_ref(v___x_632_);
lean_dec_ref(v___x_631_);
lean_dec_ref(v___x_630_);
lean_dec_ref(v_h_u2082_601_);
lean_dec_ref(v_h_u2081_600_);
v_a_648_ = lean_ctor_get(v___x_634_, 0);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_634_);
if (v_isSharedCheck_655_ == 0)
{
v___x_650_ = v___x_634_;
v_isShared_651_ = v_isSharedCheck_655_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_a_648_);
lean_dec(v___x_634_);
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
lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_740_ = l_Lean_Expr_appFn_x21(v_a_731_);
v___x_741_ = l_Lean_Expr_appFn_x21(v___x_740_);
v___x_742_ = l_Lean_Expr_appFn_x21(v___x_741_);
v___x_743_ = l_Lean_Expr_appArg_x21(v___x_742_);
lean_dec_ref(v___x_742_);
v___x_744_ = l_Lean_Expr_appArg_x21(v___x_741_);
lean_dec_ref(v___x_741_);
v___x_745_ = l_Lean_Expr_appArg_x21(v___x_740_);
lean_dec_ref(v___x_740_);
v___x_746_ = l_Lean_Expr_appArg_x21(v_a_731_);
lean_dec(v_a_731_);
lean_inc_ref(v___x_743_);
v___x_747_ = l_Lean_Meta_getLevel(v___x_743_, v_a_723_, v_a_724_, v_a_725_, v_a_726_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_760_; 
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_760_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_760_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_760_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_758_; 
v___x_752_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_753_ = lean_box(0);
v___x_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_754_, 0, v_a_748_);
lean_ctor_set(v___x_754_, 1, v___x_753_);
v___x_755_ = l_Lean_mkConst(v___x_752_, v___x_754_);
v___x_756_ = l_Lean_mkApp5(v___x_755_, v___x_743_, v___x_745_, v___x_744_, v___x_746_, v_h_722_);
if (v_isShared_751_ == 0)
{
lean_ctor_set(v___x_750_, 0, v___x_756_);
v___x_758_ = v___x_750_;
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
lean_dec_ref(v___x_746_);
lean_dec_ref(v___x_745_);
lean_dec_ref(v___x_744_);
lean_dec_ref(v___x_743_);
lean_dec_ref(v_h_722_);
v_a_761_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_747_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_747_);
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
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_808_ = l_Lean_Expr_appFn_x21(v_a_791_);
v___x_809_ = l_Lean_Expr_appFn_x21(v___x_808_);
v___x_810_ = l_Lean_Expr_appFn_x21(v___x_809_);
v___x_811_ = l_Lean_Expr_appArg_x21(v___x_810_);
lean_dec_ref(v___x_810_);
v___x_812_ = l_Lean_Expr_appArg_x21(v___x_809_);
lean_dec_ref(v___x_809_);
v___x_813_ = l_Lean_Expr_appArg_x21(v___x_808_);
lean_dec_ref(v___x_808_);
v___x_814_ = l_Lean_Expr_appArg_x21(v_a_791_);
lean_dec(v_a_791_);
v___x_815_ = l_Lean_Expr_appFn_x21(v_a_793_);
v___x_816_ = l_Lean_Expr_appArg_x21(v___x_815_);
lean_dec_ref(v___x_815_);
v___x_817_ = l_Lean_Expr_appArg_x21(v_a_793_);
lean_dec(v_a_793_);
lean_inc_ref(v___x_811_);
v___x_818_ = l_Lean_Meta_getLevel(v___x_811_, v_a_782_, v_a_783_, v_a_784_, v_a_785_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_831_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_831_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_831_ == 0)
{
v___x_821_ = v___x_818_;
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_818_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_831_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_829_; 
v___x_823_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_824_ = lean_box(0);
v___x_825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_825_, 0, v_a_819_);
lean_ctor_set(v___x_825_, 1, v___x_824_);
v___x_826_ = l_Lean_mkConst(v___x_823_, v___x_825_);
v___x_827_ = l_Lean_mkApp8(v___x_826_, v___x_811_, v___x_813_, v___x_816_, v___x_812_, v___x_814_, v___x_817_, v_h_u2081_780_, v_h_u2082_781_);
if (v_isShared_822_ == 0)
{
lean_ctor_set(v___x_821_, 0, v___x_827_);
v___x_829_ = v___x_821_;
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
lean_dec_ref(v___x_817_);
lean_dec_ref(v___x_816_);
lean_dec_ref(v___x_814_);
lean_dec_ref(v___x_813_);
lean_dec_ref(v___x_812_);
lean_dec_ref(v___x_811_);
lean_dec_ref(v_h_u2082_781_);
lean_dec_ref(v_h_u2081_780_);
v_a_832_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_818_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_818_);
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
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_970_ = l_Lean_Expr_appFn_x21(v_a_961_);
v___x_971_ = l_Lean_Expr_appFn_x21(v___x_970_);
v___x_972_ = l_Lean_Expr_appArg_x21(v___x_971_);
lean_dec_ref(v___x_971_);
v___x_973_ = l_Lean_Expr_appArg_x21(v___x_970_);
lean_dec_ref(v___x_970_);
v___x_974_ = l_Lean_Expr_appArg_x21(v_a_961_);
lean_dec(v_a_961_);
lean_inc_ref(v___x_972_);
v___x_975_ = l_Lean_Meta_getLevel(v___x_972_, v_a_955_, v_a_956_, v_a_957_, v_a_958_);
if (lean_obj_tag(v___x_975_) == 0)
{
lean_object* v_a_976_; lean_object* v___x_978_; uint8_t v_isShared_979_; uint8_t v_isSharedCheck_988_; 
v_a_976_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_988_ == 0)
{
v___x_978_ = v___x_975_;
v_isShared_979_ = v_isSharedCheck_988_;
goto v_resetjp_977_;
}
else
{
lean_inc(v_a_976_);
lean_dec(v___x_975_);
v___x_978_ = lean_box(0);
v_isShared_979_ = v_isSharedCheck_988_;
goto v_resetjp_977_;
}
v_resetjp_977_:
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_986_; 
v___x_980_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_981_ = lean_box(0);
v___x_982_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_982_, 0, v_a_976_);
lean_ctor_set(v___x_982_, 1, v___x_981_);
v___x_983_ = l_Lean_mkConst(v___x_980_, v___x_982_);
v___x_984_ = l_Lean_mkApp4(v___x_983_, v___x_972_, v___x_973_, v___x_974_, v_h_954_);
if (v_isShared_979_ == 0)
{
lean_ctor_set(v___x_978_, 0, v___x_984_);
v___x_986_ = v___x_978_;
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
lean_dec_ref(v___x_974_);
lean_dec_ref(v___x_973_);
lean_dec_ref(v___x_972_);
lean_dec_ref(v_h_954_);
v_a_989_ = lean_ctor_get(v___x_975_, 0);
v_isSharedCheck_996_ = !lean_is_exclusive(v___x_975_);
if (v_isSharedCheck_996_ == 0)
{
v___x_991_ = v___x_975_;
v_isShared_992_ = v_isSharedCheck_996_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_a_989_);
lean_dec(v___x_975_);
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
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = l_Lean_Expr_appFn_x21(v_a_1192_);
v___x_1213_ = l_Lean_Expr_appArg_x21(v___x_1212_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = l_Lean_Expr_appArg_x21(v_a_1192_);
lean_dec(v_a_1192_);
lean_inc_ref(v_binderType_1201_);
v___x_1215_ = l_Lean_Meta_getLevel(v_binderType_1201_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
lean_inc_ref(v_body_1202_);
v___x_1217_ = l_Lean_Meta_getLevel(v_body_1202_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
if (lean_obj_tag(v___x_1217_) == 0)
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1231_; 
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1231_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1231_ == 0)
{
v___x_1220_ = v___x_1217_;
v_isShared_1221_ = v_isSharedCheck_1231_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1217_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1231_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1229_; 
v___x_1222_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1223_ = lean_box(0);
v___x_1224_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1224_, 0, v_a_1218_);
lean_ctor_set(v___x_1224_, 1, v___x_1223_);
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v_a_1216_);
lean_ctor_set(v___x_1225_, 1, v___x_1224_);
v___x_1226_ = l_Lean_mkConst(v___x_1222_, v___x_1225_);
v___x_1227_ = l_Lean_mkApp6(v___x_1226_, v_binderType_1201_, v_body_1202_, v___x_1213_, v___x_1214_, v_f_1163_, v_h_1164_);
if (v_isShared_1221_ == 0)
{
lean_ctor_set(v___x_1220_, 0, v___x_1227_);
v___x_1229_ = v___x_1220_;
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
lean_dec(v_a_1216_);
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_body_1202_);
lean_dec_ref(v_binderType_1201_);
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_f_1163_);
v_a_1232_ = lean_ctor_get(v___x_1217_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1217_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1217_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1217_);
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
lean_dec_ref(v___x_1214_);
lean_dec_ref(v___x_1213_);
lean_dec_ref(v_body_1202_);
lean_dec_ref(v_binderType_1201_);
lean_dec_ref(v_h_1164_);
lean_dec_ref(v_f_1163_);
v_a_1240_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1242_ = v___x_1215_;
v_isShared_1243_ = v_isSharedCheck_1247_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1215_);
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
lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1308_ = l_Lean_Expr_appFn_x21(v_a_1299_);
v___x_1309_ = l_Lean_Expr_appFn_x21(v___x_1308_);
v___x_1310_ = l_Lean_Expr_appArg_x21(v___x_1309_);
lean_dec_ref(v___x_1309_);
v___x_1311_ = l_Lean_Expr_appArg_x21(v___x_1308_);
lean_dec_ref(v___x_1308_);
v___x_1312_ = l_Lean_Expr_appArg_x21(v_a_1299_);
v___x_1313_ = l_Lean_Meta_whnfD(v___x_1310_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1313_) == 0)
{
lean_object* v_a_1314_; 
v_a_1314_ = lean_ctor_get(v___x_1313_, 0);
lean_inc(v_a_1314_);
lean_dec_ref_known(v___x_1313_, 1);
if (lean_obj_tag(v_a_1314_) == 7)
{
lean_object* v_binderName_1315_; lean_object* v_binderType_1316_; lean_object* v_body_1317_; uint8_t v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
lean_dec(v_a_1299_);
v_binderName_1315_ = lean_ctor_get(v_a_1314_, 0);
lean_inc(v_binderName_1315_);
v_binderType_1316_ = lean_ctor_get(v_a_1314_, 1);
lean_inc_ref_n(v_binderType_1316_, 3);
v_body_1317_ = lean_ctor_get(v_a_1314_, 2);
lean_inc_ref(v_body_1317_);
lean_dec_ref_known(v_a_1314_, 3);
v___x_1318_ = 0;
v___x_1319_ = l_Lean_mkLambda(v_binderName_1315_, v___x_1318_, v_binderType_1316_, v_body_1317_);
v___x_1320_ = l_Lean_Meta_getLevel(v_binderType_1316_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
lean_inc_ref(v_a_1274_);
lean_inc_ref(v___x_1319_);
v___x_1322_ = l_Lean_Expr_app___override(v___x_1319_, v_a_1274_);
v___x_1323_ = l_Lean_Meta_getLevel(v___x_1322_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1337_; 
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1326_ = v___x_1323_;
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1323_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1337_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; 
v___x_1328_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1329_ = lean_box(0);
v___x_1330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1330_, 0, v_a_1324_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1331_, 0, v_a_1321_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
v___x_1332_ = l_Lean_mkConst(v___x_1328_, v___x_1331_);
v___x_1333_ = l_Lean_mkApp6(v___x_1332_, v_binderType_1316_, v___x_1319_, v___x_1311_, v___x_1312_, v_h_1273_, v_a_1274_);
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v___x_1333_);
v___x_1335_ = v___x_1326_;
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
lean_dec(v_a_1321_);
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_binderType_1316_);
lean_dec_ref(v___x_1312_);
lean_dec_ref(v___x_1311_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
v_a_1338_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1323_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1323_);
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
lean_dec_ref(v___x_1319_);
lean_dec_ref(v_binderType_1316_);
lean_dec_ref(v___x_1312_);
lean_dec_ref(v___x_1311_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
v_a_1346_ = lean_ctor_get(v___x_1320_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1320_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1320_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1320_);
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
lean_dec(v_a_1314_);
lean_dec_ref(v___x_1312_);
lean_dec_ref(v___x_1311_);
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
lean_dec_ref(v___x_1312_);
lean_dec_ref(v___x_1311_);
lean_dec(v_a_1299_);
lean_dec_ref(v_a_1274_);
lean_dec_ref(v_h_1273_);
return v___x_1313_;
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
lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v___x_1406_ = l_Lean_Expr_appFn_x21(v_a_1389_);
v___x_1407_ = l_Lean_Expr_appFn_x21(v___x_1406_);
v___x_1408_ = l_Lean_Expr_appArg_x21(v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = l_Lean_Expr_appArg_x21(v___x_1406_);
lean_dec_ref(v___x_1406_);
v___x_1410_ = l_Lean_Expr_appArg_x21(v_a_1389_);
v___x_1411_ = l_Lean_Expr_appFn_x21(v_a_1391_);
v___x_1412_ = l_Lean_Expr_appFn_x21(v___x_1411_);
v___x_1413_ = l_Lean_Expr_appArg_x21(v___x_1412_);
lean_dec_ref(v___x_1412_);
v___x_1414_ = l_Lean_Expr_appArg_x21(v___x_1411_);
lean_dec_ref(v___x_1411_);
v___x_1415_ = l_Lean_Expr_appArg_x21(v_a_1391_);
lean_dec(v_a_1391_);
v___x_1416_ = l_Lean_Meta_whnfD(v___x_1408_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_object* v_a_1417_; 
v_a_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_a_1417_);
lean_dec_ref_known(v___x_1416_, 1);
if (lean_obj_tag(v_a_1417_) == 7)
{
lean_object* v_body_1424_; uint8_t v___x_1425_; 
v_body_1424_ = lean_ctor_get(v_a_1417_, 2);
lean_inc_ref(v_body_1424_);
lean_dec_ref_known(v_a_1417_, 3);
v___x_1425_ = l_Lean_Expr_hasLooseBVars(v_body_1424_);
if (v___x_1425_ == 0)
{
lean_object* v___x_1426_; 
lean_dec(v_a_1389_);
lean_inc_ref(v___x_1413_);
v___x_1426_ = l_Lean_Meta_getLevel(v___x_1413_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1426_) == 0)
{
lean_object* v_a_1427_; lean_object* v___x_1428_; 
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref_known(v___x_1426_, 1);
lean_inc_ref(v_body_1424_);
v___x_1428_ = l_Lean_Meta_getLevel(v_body_1424_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1442_; 
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1442_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1442_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1442_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; 
v___x_1433_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1434_ = lean_box(0);
v___x_1435_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1435_, 0, v_a_1429_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1436_, 0, v_a_1427_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
v___x_1437_ = l_Lean_mkConst(v___x_1433_, v___x_1436_);
v___x_1438_ = l_Lean_mkApp8(v___x_1437_, v___x_1413_, v_body_1424_, v___x_1409_, v___x_1410_, v___x_1414_, v___x_1415_, v_h_u2081_1378_, v_h_u2082_1379_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1438_);
v___x_1440_ = v___x_1431_;
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
lean_dec(v_a_1427_);
lean_dec_ref(v_body_1424_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___x_1409_);
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
v_a_1443_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1428_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1428_);
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
lean_dec_ref(v_body_1424_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___x_1409_);
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
v_a_1451_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1453_ = v___x_1426_;
v_isShared_1454_ = v_isSharedCheck_1458_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1426_);
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
lean_dec_ref(v_body_1424_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___x_1409_);
lean_dec_ref(v_h_u2082_1379_);
goto v___jp_1418_;
}
}
else
{
lean_dec(v_a_1417_);
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___x_1409_);
lean_dec_ref(v_h_u2082_1379_);
goto v___jp_1418_;
}
v___jp_1418_:
{
lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1419_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1420_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1421_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1378_, v_a_1389_);
v___x_1422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1422_, 0, v___x_1420_);
lean_ctor_set(v___x_1422_, 1, v___x_1421_);
v___x_1423_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1419_, v___x_1422_, v_a_1380_, v_a_1381_, v_a_1382_, v_a_1383_);
return v___x_1423_;
}
}
else
{
lean_dec_ref(v___x_1415_);
lean_dec_ref(v___x_1414_);
lean_dec_ref(v___x_1413_);
lean_dec_ref(v___x_1410_);
lean_dec_ref(v___x_1409_);
lean_dec(v_a_1389_);
lean_dec_ref(v_h_u2082_1379_);
lean_dec_ref(v_h_u2081_1378_);
return v___x_1416_;
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
v___x_1549_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
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
size_t v_x_1971__boxed_1653_; size_t v_x_1972__boxed_1654_; lean_object* v_res_1655_; 
v_x_1971__boxed_1653_ = lean_unbox_usize(v_x_1649_);
lean_dec(v_x_1649_);
v_x_1972__boxed_1654_ = lean_unbox_usize(v_x_1650_);
lean_dec(v_x_1650_);
v_res_1655_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1648_, v_x_1971__boxed_1653_, v_x_1972__boxed_1654_, v_x_1651_, v_x_1652_);
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
lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1693_; 
v___x_1690_ = lean_box(0);
v___x_1691_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_eAssignment_1684_, v_mvarId_1663_, v_val_1664_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 8, v___x_1691_);
v___x_1693_ = v___x_1688_;
goto v_reusejp_1692_;
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
lean_ctor_set(v_reuseFailAlloc_1699_, 8, v___x_1691_);
lean_ctor_set(v_reuseFailAlloc_1699_, 9, v_dAssignment_1685_);
lean_ctor_set(v_reuseFailAlloc_1699_, 10, v_instanceTypedMVars_1686_);
v___x_1693_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
lean_object* v___x_1695_; 
if (v_isShared_1675_ == 0)
{
lean_ctor_set(v___x_1674_, 0, v___x_1693_);
v___x_1695_ = v___x_1674_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1693_);
lean_ctor_set(v_reuseFailAlloc_1698_, 1, v_cache_1669_);
lean_ctor_set(v_reuseFailAlloc_1698_, 2, v_zetaDeltaFVarIds_1670_);
lean_ctor_set(v_reuseFailAlloc_1698_, 3, v_postponed_1671_);
lean_ctor_set(v_reuseFailAlloc_1698_, 4, v_diag_1672_);
v___x_1695_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = lean_st_ref_put(v___y_1665_, v___x_1695_);
v___x_1697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1697_, 0, v___x_1690_);
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
size_t v_x_2411__boxed_1871_; size_t v_x_2412__boxed_1872_; lean_object* v_res_1873_; 
v_x_2411__boxed_1871_ = lean_unbox_usize(v_x_1867_);
lean_dec(v_x_1867_);
v_x_2412__boxed_1872_ = lean_unbox_usize(v_x_1868_);
lean_dec(v_x_1868_);
v_res_1873_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1865_, v_x_1866_, v_x_2411__boxed_1871_, v_x_2412__boxed_1872_, v_x_1869_, v_x_1870_);
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
v___x_2087_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v_env_2133_; uint8_t v___x_2134_; 
v___x_2131_ = lean_box(0);
v___x_2132_ = lean_st_ref_get(v___y_2129_);
v_env_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc_ref(v_env_2133_);
lean_dec(v___x_2132_);
v___x_2134_ = l_Lean_Name_isAnonymous(v_declHint_2128_);
if (v___x_2134_ == 0)
{
uint8_t v_isExporting_2135_; 
v_isExporting_2135_ = lean_ctor_get_uint8(v_env_2133_, sizeof(void*)*8);
if (v_isExporting_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec_ref(v_env_2133_);
lean_dec(v_declHint_2128_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v_msg_2127_);
return v___x_2136_;
}
else
{
lean_object* v___x_2137_; uint8_t v___x_2138_; 
lean_inc_ref(v_env_2133_);
v___x_2137_ = l_Lean_Environment_setExporting(v_env_2133_, v___x_2134_);
lean_inc(v_declHint_2128_);
lean_inc_ref(v___x_2137_);
v___x_2138_ = l_Lean_Environment_contains(v___x_2137_, v_declHint_2128_, v_isExporting_2135_);
if (v___x_2138_ == 0)
{
lean_object* v___x_2139_; 
lean_dec_ref(v___x_2137_);
lean_dec_ref(v_env_2133_);
lean_dec(v_declHint_2128_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v_msg_2127_);
return v___x_2139_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v_c_2145_; lean_object* v___x_2146_; 
v___x_2140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2142_ = l_Lean_Options_empty;
v___x_2143_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2143_, 0, v___x_2137_);
lean_ctor_set(v___x_2143_, 1, v___x_2140_);
lean_ctor_set(v___x_2143_, 2, v___x_2141_);
lean_ctor_set(v___x_2143_, 3, v___x_2142_);
lean_inc(v_declHint_2128_);
v___x_2144_ = l_Lean_MessageData_ofConstName(v_declHint_2128_, v___x_2134_);
v_c_2145_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2145_, 0, v___x_2143_);
lean_ctor_set(v_c_2145_, 1, v___x_2144_);
v___x_2146_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2133_, v_declHint_2128_);
if (lean_obj_tag(v___x_2146_) == 0)
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref(v_env_2133_);
lean_dec(v_declHint_2128_);
v___x_2147_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2148_, 0, v___x_2147_);
lean_ctor_set(v___x_2148_, 1, v_c_2145_);
v___x_2149_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2150_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2150_, 0, v___x_2148_);
lean_ctor_set(v___x_2150_, 1, v___x_2149_);
v___x_2151_ = l_Lean_MessageData_note(v___x_2150_);
v___x_2152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2152_, 0, v_msg_2127_);
lean_ctor_set(v___x_2152_, 1, v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
else
{
lean_object* v_val_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2188_; 
v_val_2154_ = lean_ctor_get(v___x_2146_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2146_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2156_ = v___x_2146_;
v_isShared_2157_ = v_isSharedCheck_2188_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_val_2154_);
lean_dec(v___x_2146_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2188_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v_mod_2160_; uint8_t v___x_2161_; 
v___x_2158_ = l_Lean_Environment_header(v_env_2133_);
lean_dec_ref(v_env_2133_);
v___x_2159_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2158_);
v_mod_2160_ = lean_array_get(v___x_2131_, v___x_2159_, v_val_2154_);
lean_dec(v_val_2154_);
lean_dec_ref(v___x_2159_);
v___x_2161_ = l_Lean_isPrivateName(v_declHint_2128_);
lean_dec(v_declHint_2128_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2173_; 
v___x_2162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v_c_2145_);
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
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2171_);
v___x_2173_ = v___x_2156_;
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
lean_ctor_set(v___x_2176_, 1, v_c_2145_);
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
if (v_isShared_2157_ == 0)
{
lean_ctor_set_tag(v___x_2156_, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2184_);
v___x_2186_ = v___x_2156_;
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
lean_dec_ref(v_env_2133_);
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
lean_object* v_toCold_2228_; lean_object* v_currRecDepth_2229_; lean_object* v_ref_2230_; uint16_t v_optionFlags_2231_; uint8_t v_suppressElabErrors_2232_; uint8_t v_isRecordingDeps_2233_; lean_object* v_ref_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_toCold_2228_ = lean_ctor_get(v___y_2225_, 0);
v_currRecDepth_2229_ = lean_ctor_get(v___y_2225_, 1);
v_ref_2230_ = lean_ctor_get(v___y_2225_, 2);
v_optionFlags_2231_ = lean_ctor_get_uint16(v___y_2225_, sizeof(void*)*3);
v_suppressElabErrors_2232_ = lean_ctor_get_uint8(v___y_2225_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2233_ = lean_ctor_get_uint8(v___y_2225_, sizeof(void*)*3 + 3);
v_ref_2234_ = l_Lean_replaceRef(v_ref_2221_, v_ref_2230_);
lean_inc(v_currRecDepth_2229_);
lean_inc_ref(v_toCold_2228_);
v___x_2235_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2235_, 0, v_toCold_2228_);
lean_ctor_set(v___x_2235_, 1, v_currRecDepth_2229_);
lean_ctor_set(v___x_2235_, 2, v_ref_2234_);
lean_ctor_set_uint16(v___x_2235_, sizeof(void*)*3, v_optionFlags_2231_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*3 + 2, v_suppressElabErrors_2232_);
lean_ctor_set_uint8(v___x_2235_, sizeof(void*)*3 + 3, v_isRecordingDeps_2233_);
v___x_2236_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2222_, v___y_2223_, v___y_2224_, v___x_2235_, v___y_2226_);
lean_dec_ref_known(v___x_2235_, 3);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2237_, lean_object* v_msg_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v_res_2244_; 
v_res_2244_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2237_, v_msg_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
lean_dec(v___y_2242_);
lean_dec_ref(v___y_2241_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v_ref_2237_);
return v_res_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2245_, lean_object* v_msg_2246_, lean_object* v_declHint_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v_a_2254_; lean_object* v___x_2255_; 
v___x_2253_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2246_, v_declHint_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref(v___x_2253_);
v___x_2255_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2245_, v_a_2254_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2255_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2256_, lean_object* v_msg_2257_, lean_object* v_declHint_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2256_, v_msg_2257_, v_declHint_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v_ref_2256_);
return v_res_2264_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2271_, lean_object* v_constName_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v___x_2278_; uint8_t v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2278_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2279_ = 0;
lean_inc(v_constName_2272_);
v___x_2280_ = l_Lean_MessageData_ofConstName(v_constName_2272_, v___x_2279_);
v___x_2281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___x_2278_);
lean_ctor_set(v___x_2281_, 1, v___x_2280_);
v___x_2282_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2283_, 0, v___x_2281_);
lean_ctor_set(v___x_2283_, 1, v___x_2282_);
v___x_2284_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2271_, v___x_2283_, v_constName_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
return v___x_2284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2285_, lean_object* v_constName_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_res_2292_; 
v_res_2292_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2285_, v_constName_2286_, v___y_2287_, v___y_2288_, v___y_2289_, v___y_2290_);
lean_dec(v___y_2290_);
lean_dec_ref(v___y_2289_);
lean_dec(v___y_2288_);
lean_dec_ref(v___y_2287_);
lean_dec(v_ref_2285_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_){
_start:
{
lean_object* v_ref_2299_; lean_object* v___x_2300_; 
v_ref_2299_ = lean_ctor_get(v___y_2296_, 2);
v___x_2300_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2299_, v_constName_2293_, v___y_2294_, v___y_2295_, v___y_2296_, v___y_2297_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_){
_start:
{
lean_object* v_res_2307_; 
v_res_2307_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_);
lean_dec(v___y_2305_);
lean_dec_ref(v___y_2304_);
lean_dec(v___y_2303_);
lean_dec_ref(v___y_2302_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_){
_start:
{
lean_object* v___x_2314_; lean_object* v_env_2315_; uint8_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_st_ref_get(v___y_2312_);
v_env_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc_ref(v_env_2315_);
lean_dec(v___x_2314_);
v___x_2316_ = 0;
lean_inc(v_constName_2308_);
v___x_2317_ = l_Lean_Environment_findConstVal_x3f(v_env_2315_, v_constName_2308_, v___x_2316_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v___x_2318_; 
v___x_2318_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
return v___x_2318_;
}
else
{
lean_object* v_val_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_constName_2308_);
v_val_2319_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2317_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_val_2319_);
lean_dec(v___x_2317_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set_tag(v___x_2321_, 0);
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_val_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_){
_start:
{
lean_object* v_res_2333_; 
v_res_2333_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2327_, v___y_2328_, v___y_2329_, v___y_2330_, v___y_2331_);
lean_dec(v___y_2331_);
lean_dec_ref(v___y_2330_);
lean_dec(v___y_2329_);
lean_dec_ref(v___y_2328_);
return v_res_2333_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v___x_2340_; 
lean_inc(v_constName_2334_);
v___x_2340_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2334_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v_levelParams_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v_levelParams_2342_ = lean_ctor_get(v_a_2341_, 1);
v___x_2343_ = lean_box(0);
lean_inc(v_levelParams_2342_);
v___x_2344_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2342_, v___x_2343_, v_a_2335_, v_a_2336_, v_a_2337_, v_a_2338_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc_n(v_a_2345_, 2);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = l_Lean_mkConst(v_constName_2334_, v_a_2345_);
v___x_2347_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2341_, v_a_2345_, v_a_2338_);
if (lean_obj_tag(v___x_2347_) == 0)
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2356_; 
v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2350_ = v___x_2347_;
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2347_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2356_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
v___x_2352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2346_);
lean_ctor_set(v___x_2352_, 1, v_a_2348_);
if (v_isShared_2351_ == 0)
{
lean_ctor_set(v___x_2350_, 0, v___x_2352_);
v___x_2354_ = v___x_2350_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_dec_ref(v___x_2346_);
v_a_2357_ = lean_ctor_get(v___x_2347_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2347_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2347_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2347_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_dec(v_a_2341_);
lean_dec(v_constName_2334_);
v_a_2365_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2344_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2344_);
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
lean_dec(v_constName_2334_);
v_a_2373_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2340_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2340_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2381_, v_a_2382_, v_a_2383_, v_a_2384_, v_a_2385_);
lean_dec(v_a_2385_);
lean_dec_ref(v_a_2384_);
lean_dec(v_a_2383_);
lean_dec_ref(v_a_2382_);
return v_res_2387_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2388_, lean_object* v_constName_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v___x_2395_; 
v___x_2395_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2396_, lean_object* v_constName_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_res_2403_; 
v_res_2403_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2396_, v_constName_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
return v_res_2403_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2404_, lean_object* v_ref_2405_, lean_object* v_constName_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2405_, v_constName_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2413_, lean_object* v_ref_2414_, lean_object* v_constName_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2413_, v_ref_2414_, v_constName_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v_ref_2414_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2422_, lean_object* v_ref_2423_, lean_object* v_msg_2424_, lean_object* v_declHint_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_){
_start:
{
lean_object* v___x_2431_; 
v___x_2431_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2423_, v_msg_2424_, v_declHint_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
return v___x_2431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2432_, lean_object* v_ref_2433_, lean_object* v_msg_2434_, lean_object* v_declHint_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2432_, v_ref_2433_, v_msg_2434_, v_declHint_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v_ref_2433_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2442_, lean_object* v_declHint_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2442_, v_declHint_2443_, v___y_2447_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2450_, lean_object* v_declHint_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2450_, v_declHint_2451_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v_res_2457_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2458_, lean_object* v_ref_2459_, lean_object* v_msg_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_){
_start:
{
lean_object* v___x_2466_; 
v___x_2466_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2459_, v_msg_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2467_, lean_object* v_ref_2468_, lean_object* v_msg_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2467_, v_ref_2468_, v_msg_2469_, v___y_2470_, v___y_2471_, v___y_2472_, v___y_2473_);
lean_dec(v___y_2473_);
lean_dec_ref(v___y_2472_);
lean_dec(v___y_2471_);
lean_dec_ref(v___y_2470_);
lean_dec(v_ref_2468_);
return v_res_2475_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2478_ = l_Lean_stringToMessageData(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2480_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2481_ = l_Lean_stringToMessageData(v___x_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2482_, lean_object* v_f_2483_, lean_object* v_inst_2484_, lean_object* v_xs_2485_, lean_object* v_x_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_){
_start:
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2492_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2493_ = lean_apply_1(v_inst_2482_, v_f_2483_);
v___x_2494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2492_);
lean_ctor_set(v___x_2494_, 1, v___x_2493_);
v___x_2495_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = lean_apply_1(v_inst_2484_, v_xs_2485_);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2500_, lean_object* v_f_2501_, lean_object* v_inst_2502_, lean_object* v_xs_2503_, lean_object* v_x_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
lean_object* v_res_2510_; 
v_res_2510_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2500_, v_f_2501_, v_inst_2502_, v_xs_2503_, v_x_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_);
lean_dec(v___y_2508_);
lean_dec_ref(v___y_2507_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec_ref(v_x_2504_);
return v_res_2510_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2511_; 
v___x_2511_ = l_instMonadEIO___redArg();
return v___x_2511_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; 
v___x_2512_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2513_ = l_StateRefT_x27_instMonad___redArg(v___x_2512_);
return v___x_2513_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2520_; lean_object* v___x_2521_; lean_object* v___x_2522_; 
v___x_2520_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2521_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2522_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2521_, v___x_2520_);
return v___x_2522_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2523_; lean_object* v___f_2524_; lean_object* v___x_2525_; 
v___x_2523_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2524_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2525_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2524_, v___x_2523_);
return v___x_2525_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2528_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2529_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2530_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2531_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2530_, v___x_2529_, v___x_2528_);
return v___x_2531_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___f_2533_; lean_object* v___f_2534_; lean_object* v___x_2535_; 
v___x_2532_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2533_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2534_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2535_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2534_, v___f_2533_, v___x_2532_);
return v___x_2535_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2536_; 
v___x_2536_ = l_instMonadExceptOfEIO___redArg();
return v___x_2536_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2538_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2537_);
return v___x_2538_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2540_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2539_);
return v___x_2540_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2542_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2541_);
return v___x_2542_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2544_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2543_);
return v___x_2544_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2555_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2556_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2557_ = l_Lean_Name_append(v___x_2556_, v___x_2555_);
return v___x_2557_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2563_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2564_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2565_ = l_Lean_Name_append(v___x_2564_, v___x_2563_);
return v___x_2565_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2566_; double v___x_2567_; 
v___x_2566_ = lean_unsigned_to_nat(1000000000u);
v___x_2567_ = lean_float_of_nat(v___x_2566_);
return v___x_2567_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2574_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2575_ = l_Lean_Name_append(v___x_2574_, v___x_2573_);
return v___x_2575_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2576_, lean_object* v_inst_2577_, lean_object* v_f_2578_, lean_object* v_xs_2579_, lean_object* v_k_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_){
_start:
{
lean_object* v___x_2586_; lean_object* v_toApplicative_2587_; lean_object* v_toFunctor_2588_; lean_object* v_toSeq_2589_; lean_object* v_toSeqLeft_2590_; lean_object* v_toSeqRight_2591_; lean_object* v___f_2592_; lean_object* v___f_2593_; lean_object* v___f_2594_; lean_object* v___f_2595_; lean_object* v___x_2596_; lean_object* v___f_2597_; lean_object* v___f_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v_toApplicative_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2842_; 
v___x_2586_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2587_ = lean_ctor_get(v___x_2586_, 0);
v_toFunctor_2588_ = lean_ctor_get(v_toApplicative_2587_, 0);
v_toSeq_2589_ = lean_ctor_get(v_toApplicative_2587_, 2);
v_toSeqLeft_2590_ = lean_ctor_get(v_toApplicative_2587_, 3);
v_toSeqRight_2591_ = lean_ctor_get(v_toApplicative_2587_, 4);
v___f_2592_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2593_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2588_, 2);
v___f_2594_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2594_, 0, v_toFunctor_2588_);
v___f_2595_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2595_, 0, v_toFunctor_2588_);
v___x_2596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___f_2594_);
lean_ctor_set(v___x_2596_, 1, v___f_2595_);
lean_inc(v_toSeqRight_2591_);
v___f_2597_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2597_, 0, v_toSeqRight_2591_);
lean_inc(v_toSeqLeft_2590_);
v___f_2598_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2598_, 0, v_toSeqLeft_2590_);
lean_inc(v_toSeq_2589_);
v___f_2599_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2599_, 0, v_toSeq_2589_);
v___x_2600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2596_);
lean_ctor_set(v___x_2600_, 1, v___f_2592_);
lean_ctor_set(v___x_2600_, 2, v___f_2599_);
lean_ctor_set(v___x_2600_, 3, v___f_2598_);
lean_ctor_set(v___x_2600_, 4, v___f_2597_);
v___x_2601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2601_, 0, v___x_2600_);
lean_ctor_set(v___x_2601_, 1, v___f_2593_);
v___x_2602_ = l_StateRefT_x27_instMonad___redArg(v___x_2601_);
v_toApplicative_2603_ = lean_ctor_get(v___x_2602_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2602_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v___x_2602_, 1);
lean_dec(v_unused_2843_);
v___x_2605_ = v___x_2602_;
v_isShared_2606_ = v_isSharedCheck_2842_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_toApplicative_2603_);
lean_dec(v___x_2602_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2842_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v_toFunctor_2607_; lean_object* v_toSeq_2608_; lean_object* v_toSeqLeft_2609_; lean_object* v_toSeqRight_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2840_; 
v_toFunctor_2607_ = lean_ctor_get(v_toApplicative_2603_, 0);
v_toSeq_2608_ = lean_ctor_get(v_toApplicative_2603_, 2);
v_toSeqLeft_2609_ = lean_ctor_get(v_toApplicative_2603_, 3);
v_toSeqRight_2610_ = lean_ctor_get(v_toApplicative_2603_, 4);
v_isSharedCheck_2840_ = !lean_is_exclusive(v_toApplicative_2603_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v_toApplicative_2603_, 1);
lean_dec(v_unused_2841_);
v___x_2612_ = v_toApplicative_2603_;
v_isShared_2613_ = v_isSharedCheck_2840_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_toSeqRight_2610_);
lean_inc(v_toSeqLeft_2609_);
lean_inc(v_toSeq_2608_);
lean_inc(v_toFunctor_2607_);
lean_dec(v_toApplicative_2603_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2840_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___x_2623_; 
v___f_2614_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2615_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2607_);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toFunctor_2607_);
v___f_2617_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2617_, 0, v_toFunctor_2607_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___f_2616_);
lean_ctor_set(v___x_2618_, 1, v___f_2617_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toSeqRight_2610_);
v___f_2620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2620_, 0, v_toSeqLeft_2609_);
v___f_2621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2621_, 0, v_toSeq_2608_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 4, v___f_2619_);
lean_ctor_set(v___x_2612_, 3, v___f_2620_);
lean_ctor_set(v___x_2612_, 2, v___f_2621_);
lean_ctor_set(v___x_2612_, 1, v___f_2614_);
lean_ctor_set(v___x_2612_, 0, v___x_2618_);
v___x_2623_ = v___x_2612_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2618_);
lean_ctor_set(v_reuseFailAlloc_2839_, 1, v___f_2614_);
lean_ctor_set(v_reuseFailAlloc_2839_, 2, v___f_2621_);
lean_ctor_set(v_reuseFailAlloc_2839_, 3, v___f_2620_);
lean_ctor_set(v_reuseFailAlloc_2839_, 4, v___f_2619_);
v___x_2623_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
lean_object* v___x_2625_; 
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 1, v___f_2615_);
lean_ctor_set(v___x_2605_, 0, v___x_2623_);
v___x_2625_ = v___x_2605_;
goto v_reusejp_2624_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v___x_2623_);
lean_ctor_set(v_reuseFailAlloc_2838_, 1, v___f_2615_);
v___x_2625_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2624_;
}
v_reusejp_2624_:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v_toMonadRef_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v_toCold_2631_; lean_object* v_options_2632_; uint8_t v_hasTrace_2633_; 
v___x_2626_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2627_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2628_ = lean_ctor_get(v___x_2627_, 0);
v___x_2629_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2630_ = l_Lean_KVMap_instValueBool;
v_toCold_2631_ = lean_ctor_get(v_a_2583_, 0);
v_options_2632_ = lean_ctor_get(v_toCold_2631_, 2);
v_hasTrace_2633_ = lean_ctor_get_uint8(v_options_2632_, sizeof(void*)*1);
if (v_hasTrace_2633_ == 0)
{
lean_object* v___x_2634_; 
lean_dec_ref(v___x_2625_);
lean_dec(v_xs_2579_);
lean_dec(v_f_2578_);
lean_dec_ref(v_inst_2577_);
lean_dec_ref(v_inst_2576_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2634_ = lean_apply_5(v_k_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2634_) == 0)
{
return v___x_2634_;
}
else
{
lean_object* v_a_2635_; uint8_t v___y_2637_; uint8_t v___x_2646_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
v___x_2646_ = l_Lean_Exception_isInterrupt(v_a_2635_);
if (v___x_2646_ == 0)
{
uint8_t v___x_2647_; 
lean_inc(v_a_2635_);
v___x_2647_ = l_Lean_Exception_isRuntime(v_a_2635_);
v___y_2637_ = v___x_2647_;
goto v___jp_2636_;
}
else
{
v___y_2637_ = v___x_2646_;
goto v___jp_2636_;
}
v___jp_2636_:
{
if (v___y_2637_ == 0)
{
lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2644_ == 0)
{
lean_object* v_unused_2645_; 
v_unused_2645_ = lean_ctor_get(v___x_2634_, 0);
lean_dec(v_unused_2645_);
v___x_2639_ = v___x_2634_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_dec(v___x_2634_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2635_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
else
{
lean_dec(v_a_2635_);
return v___x_2634_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2648_; lean_object* v___x_2649_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; lean_object* v___y_2678_; lean_object* v_a_2679_; lean_object* v___f_2682_; lean_object* v___f_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; lean_object* v___y_2689_; lean_object* v___y_2690_; lean_object* v_a_2691_; lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v_a_2707_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v_a_2724_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v_a_2730_; lean_object* v___y_2733_; lean_object* v___y_2734_; lean_object* v_a_2735_; lean_object* v___y_2746_; lean_object* v___y_2747_; lean_object* v_a_2748_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; uint8_t v___y_2754_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v_a_2765_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v_a_2771_; 
v_inheritedTraceOptions_2648_ = lean_ctor_get(v_toCold_2631_, 11);
v___x_2649_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2682_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2682_, 0, v_inst_2576_);
lean_closure_set(v___f_2682_, 1, v_f_2578_);
lean_closure_set(v___f_2682_, 2, v_inst_2577_);
lean_closure_set(v___f_2682_, 3, v_xs_2579_);
v___f_2683_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2685_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2686_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2687_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2632_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; 
v___x_2810_ = l_Lean_trace_profiler;
v___x_2811_ = l_Lean_Option_get___redArg(v___x_2630_, v_options_2632_, v___x_2810_);
v___x_2812_ = lean_unbox(v___x_2811_);
lean_dec(v___x_2811_);
if (v___x_2812_ == 0)
{
lean_object* v___x_2813_; 
lean_dec_ref(v___f_2682_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2813_ = lean_apply_5(v_k_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; uint8_t v___x_2817_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
v___x_2815_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2816_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2817_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2632_, v___x_2816_);
if (v___x_2817_ == 0)
{
lean_dec(v_a_2814_);
lean_dec_ref(v___x_2625_);
return v___x_2813_;
}
else
{
lean_object* v___x_2818_; lean_object* v___x_8995__overap_2819_; lean_object* v___x_2820_; 
lean_dec_ref_known(v___x_2813_, 1);
lean_inc(v_a_2814_);
v___x_2818_ = l_Lean_MessageData_ofExpr(v_a_2814_);
lean_inc_ref(v_toMonadRef_2628_);
lean_inc_ref(v___x_2625_);
v___x_8995__overap_2819_ = l_Lean_addTrace___redArg(v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, v___x_2815_, v___x_2818_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2820_ = lean_apply_5(v___x_8995__overap_2819_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v___x_2822_; uint8_t v_isShared_2823_; uint8_t v_isSharedCheck_2827_; 
lean_dec_ref(v___x_2625_);
v_isSharedCheck_2827_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2827_ == 0)
{
lean_object* v_unused_2828_; 
v_unused_2828_ = lean_ctor_get(v___x_2820_, 0);
lean_dec(v_unused_2828_);
v___x_2822_ = v___x_2820_;
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
else
{
lean_dec(v___x_2820_);
v___x_2822_ = lean_box(0);
v_isShared_2823_ = v_isSharedCheck_2827_;
goto v_resetjp_2821_;
}
v_resetjp_2821_:
{
lean_object* v___x_2825_; 
if (v_isShared_2823_ == 0)
{
lean_ctor_set(v___x_2822_, 0, v_a_2814_);
v___x_2825_ = v___x_2822_;
goto v_reusejp_2824_;
}
else
{
lean_object* v_reuseFailAlloc_2826_; 
v_reuseFailAlloc_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2826_, 0, v_a_2814_);
v___x_2825_ = v_reuseFailAlloc_2826_;
goto v_reusejp_2824_;
}
v_reusejp_2824_:
{
return v___x_2825_;
}
}
}
else
{
lean_object* v_a_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2836_; 
lean_dec(v_a_2814_);
v_a_2829_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2836_ == 0)
{
v___x_2831_ = v___x_2820_;
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
else
{
lean_inc(v_a_2829_);
lean_dec(v___x_2820_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2836_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2834_; 
lean_inc(v_a_2829_);
if (v_isShared_2832_ == 0)
{
v___x_2834_ = v___x_2831_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v_a_2829_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
v___y_2678_ = v___x_2834_;
v_a_2679_ = v_a_2829_;
goto v___jp_2677_;
}
}
}
}
}
else
{
lean_object* v_a_2837_; 
v_a_2837_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2837_);
v___y_2678_ = v___x_2813_;
v_a_2679_ = v_a_2837_;
goto v___jp_2677_;
}
}
else
{
goto v___jp_2773_;
}
}
else
{
goto v___jp_2773_;
}
v___jp_2650_:
{
if (v___y_2653_ == 0)
{
lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
lean_dec_ref(v___y_2652_);
v___x_2654_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2655_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2656_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2632_, v___x_2655_);
if (v___x_2656_ == 0)
{
lean_object* v___x_2657_; 
lean_dec_ref(v___x_2625_);
v___x_2657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2657_, 0, v___y_2651_);
return v___x_2657_;
}
else
{
lean_object* v___x_2658_; lean_object* v___x_8806__overap_2659_; lean_object* v___x_2660_; 
lean_inc_ref(v___y_2651_);
v___x_2658_ = l_Lean_Exception_toMessageData(v___y_2651_);
lean_inc_ref(v_toMonadRef_2628_);
v___x_8806__overap_2659_ = l_Lean_addTrace___redArg(v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, v___x_2654_, v___x_2658_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2660_ = lean_apply_5(v___x_8806__overap_2659_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2667_ == 0)
{
lean_object* v_unused_2668_; 
v_unused_2668_ = lean_ctor_get(v___x_2660_, 0);
lean_dec(v_unused_2668_);
v___x_2662_ = v___x_2660_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_dec(v___x_2660_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
lean_ctor_set_tag(v___x_2662_, 1);
lean_ctor_set(v___x_2662_, 0, v___y_2651_);
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v___y_2651_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec_ref(v___y_2651_);
v_a_2669_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2660_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2660_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2651_);
lean_dec_ref(v___x_2625_);
return v___y_2652_;
}
}
v___jp_2677_:
{
uint8_t v___x_2680_; 
v___x_2680_ = l_Lean_Exception_isInterrupt(v_a_2679_);
if (v___x_2680_ == 0)
{
uint8_t v___x_2681_; 
lean_inc_ref(v_a_2679_);
v___x_2681_ = l_Lean_Exception_isRuntime(v_a_2679_);
v___y_2651_ = v_a_2679_;
v___y_2652_ = v___y_2678_;
v___y_2653_ = v___x_2681_;
goto v___jp_2650_;
}
else
{
v___y_2651_ = v_a_2679_;
v___y_2652_ = v___y_2678_;
v___y_2653_ = v___x_2680_;
goto v___jp_2650_;
}
}
v___jp_2688_:
{
lean_object* v___x_2692_; double v___x_2693_; double v___x_2694_; double v___x_2695_; double v___x_2696_; double v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_8867__overap_2702_; lean_object* v___x_2703_; 
v___x_2692_ = lean_io_mono_nanos_now();
v___x_2693_ = lean_float_of_nat(v___y_2690_);
v___x_2694_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2695_ = lean_float_div(v___x_2693_, v___x_2694_);
v___x_2696_ = lean_float_of_nat(v___x_2692_);
v___x_2697_ = lean_float_div(v___x_2696_, v___x_2694_);
v___x_2698_ = lean_box_float(v___x_2695_);
v___x_2699_ = lean_box_float(v___x_2697_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2698_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2701_, 0, v_a_2691_);
lean_ctor_set(v___x_2701_, 1, v___x_2700_);
lean_inc_ref(v_toMonadRef_2628_);
v___x_8867__overap_2702_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, lean_box(0), v___x_2629_, v___f_2683_, v___x_2684_, v_hasTrace_2633_, v___x_2685_, v_options_2632_, v___x_2687_, v___y_2689_, v___f_2682_, v___x_2701_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2703_ = lean_apply_5(v___x_8867__overap_2702_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
return v___x_2703_;
}
v___jp_2704_:
{
lean_object* v___x_2708_; 
v___x_2708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2708_, 0, v_a_2707_);
v___y_2689_ = v___y_2705_;
v___y_2690_ = v___y_2706_;
v_a_2691_ = v___x_2708_;
goto v___jp_2688_;
}
v___jp_2709_:
{
if (v___y_2713_ == 0)
{
lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; 
v___x_2714_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2715_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2632_, v___x_2715_);
if (v___x_2716_ == 0)
{
v___y_2705_ = v___y_2711_;
v___y_2706_ = v___y_2712_;
v_a_2707_ = v___y_2710_;
goto v___jp_2704_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_8886__overap_2718_; lean_object* v___x_2719_; 
lean_inc_ref(v___y_2710_);
v___x_2717_ = l_Lean_Exception_toMessageData(v___y_2710_);
lean_inc_ref(v_toMonadRef_2628_);
lean_inc_ref(v___x_2625_);
v___x_8886__overap_2718_ = l_Lean_addTrace___redArg(v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, v___x_2714_, v___x_2717_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2719_ = lean_apply_5(v___x_8886__overap_2718_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_dec_ref_known(v___x_2719_, 1);
v___y_2705_ = v___y_2711_;
v___y_2706_ = v___y_2712_;
v_a_2707_ = v___y_2710_;
goto v___jp_2704_;
}
else
{
lean_object* v_a_2720_; 
lean_dec_ref(v___y_2710_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
lean_inc(v_a_2720_);
lean_dec_ref_known(v___x_2719_, 1);
v___y_2705_ = v___y_2711_;
v___y_2706_ = v___y_2712_;
v_a_2707_ = v_a_2720_;
goto v___jp_2704_;
}
}
}
else
{
v___y_2705_ = v___y_2711_;
v___y_2706_ = v___y_2712_;
v_a_2707_ = v___y_2710_;
goto v___jp_2704_;
}
}
v___jp_2721_:
{
uint8_t v___x_2725_; 
v___x_2725_ = l_Lean_Exception_isInterrupt(v_a_2724_);
if (v___x_2725_ == 0)
{
uint8_t v___x_2726_; 
lean_inc_ref(v_a_2724_);
v___x_2726_ = l_Lean_Exception_isRuntime(v_a_2724_);
v___y_2710_ = v_a_2724_;
v___y_2711_ = v___y_2722_;
v___y_2712_ = v___y_2723_;
v___y_2713_ = v___x_2726_;
goto v___jp_2709_;
}
else
{
v___y_2710_ = v_a_2724_;
v___y_2711_ = v___y_2722_;
v___y_2712_ = v___y_2723_;
v___y_2713_ = v___x_2725_;
goto v___jp_2709_;
}
}
v___jp_2727_:
{
lean_object* v___x_2731_; 
v___x_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2731_, 0, v_a_2730_);
v___y_2689_ = v___y_2728_;
v___y_2690_ = v___y_2729_;
v_a_2691_ = v___x_2731_;
goto v___jp_2688_;
}
v___jp_2732_:
{
lean_object* v___x_2736_; double v___x_2737_; double v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; lean_object* v___x_8929__overap_2743_; lean_object* v___x_2744_; 
v___x_2736_ = lean_io_get_num_heartbeats();
v___x_2737_ = lean_float_of_nat(v___y_2734_);
v___x_2738_ = lean_float_of_nat(v___x_2736_);
v___x_2739_ = lean_box_float(v___x_2737_);
v___x_2740_ = lean_box_float(v___x_2738_);
v___x_2741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2741_, 0, v___x_2739_);
lean_ctor_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2742_, 0, v_a_2735_);
lean_ctor_set(v___x_2742_, 1, v___x_2741_);
lean_inc_ref(v_toMonadRef_2628_);
v___x_8929__overap_2743_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, lean_box(0), v___x_2629_, v___f_2683_, v___x_2684_, v_hasTrace_2633_, v___x_2685_, v_options_2632_, v___x_2687_, v___y_2733_, v___f_2682_, v___x_2742_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2744_ = lean_apply_5(v___x_8929__overap_2743_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
return v___x_2744_;
}
v___jp_2745_:
{
lean_object* v___x_2749_; 
v___x_2749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2749_, 0, v_a_2748_);
v___y_2733_ = v___y_2746_;
v___y_2734_ = v___y_2747_;
v_a_2735_ = v___x_2749_;
goto v___jp_2732_;
}
v___jp_2750_:
{
if (v___y_2754_ == 0)
{
lean_object* v___x_2755_; lean_object* v___x_2756_; uint8_t v___x_2757_; 
v___x_2755_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2756_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2757_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2632_, v___x_2756_);
if (v___x_2757_ == 0)
{
v___y_2746_ = v___y_2751_;
v___y_2747_ = v___y_2753_;
v_a_2748_ = v___y_2752_;
goto v___jp_2745_;
}
else
{
lean_object* v___x_2758_; lean_object* v___x_8948__overap_2759_; lean_object* v___x_2760_; 
lean_inc_ref(v___y_2752_);
v___x_2758_ = l_Lean_Exception_toMessageData(v___y_2752_);
lean_inc_ref(v_toMonadRef_2628_);
lean_inc_ref(v___x_2625_);
v___x_8948__overap_2759_ = l_Lean_addTrace___redArg(v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, v___x_2755_, v___x_2758_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2760_ = lean_apply_5(v___x_8948__overap_2759_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2760_) == 0)
{
lean_dec_ref_known(v___x_2760_, 1);
v___y_2746_ = v___y_2751_;
v___y_2747_ = v___y_2753_;
v_a_2748_ = v___y_2752_;
goto v___jp_2745_;
}
else
{
lean_object* v_a_2761_; 
lean_dec_ref(v___y_2752_);
v_a_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc(v_a_2761_);
lean_dec_ref_known(v___x_2760_, 1);
v___y_2746_ = v___y_2751_;
v___y_2747_ = v___y_2753_;
v_a_2748_ = v_a_2761_;
goto v___jp_2745_;
}
}
}
else
{
v___y_2746_ = v___y_2751_;
v___y_2747_ = v___y_2753_;
v_a_2748_ = v___y_2752_;
goto v___jp_2745_;
}
}
v___jp_2762_:
{
uint8_t v___x_2766_; 
v___x_2766_ = l_Lean_Exception_isInterrupt(v_a_2765_);
if (v___x_2766_ == 0)
{
uint8_t v___x_2767_; 
lean_inc_ref(v_a_2765_);
v___x_2767_ = l_Lean_Exception_isRuntime(v_a_2765_);
v___y_2751_ = v___y_2763_;
v___y_2752_ = v_a_2765_;
v___y_2753_ = v___y_2764_;
v___y_2754_ = v___x_2767_;
goto v___jp_2750_;
}
else
{
v___y_2751_ = v___y_2763_;
v___y_2752_ = v_a_2765_;
v___y_2753_ = v___y_2764_;
v___y_2754_ = v___x_2766_;
goto v___jp_2750_;
}
}
v___jp_2768_:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2772_, 0, v_a_2771_);
v___y_2733_ = v___y_2769_;
v___y_2734_ = v___y_2770_;
v_a_2735_ = v___x_2772_;
goto v___jp_2732_;
}
v___jp_2773_:
{
lean_object* v___x_8845__overap_2774_; lean_object* v___x_2775_; 
lean_inc_ref(v___x_2625_);
v___x_8845__overap_2774_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2625_, v___x_2626_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2775_ = lean_apply_5(v___x_8845__overap_2774_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2778_ = l_Lean_Option_get___redArg(v___x_2630_, v_options_2632_, v___x_2777_);
v___x_2779_ = lean_unbox(v___x_2778_);
lean_dec(v___x_2778_);
if (v___x_2779_ == 0)
{
lean_object* v___x_2780_; lean_object* v___x_2781_; 
v___x_2780_ = lean_io_mono_nanos_now();
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2781_ = lean_apply_5(v_k_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; uint8_t v___x_2785_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2784_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2785_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2632_, v___x_2784_);
if (v___x_2785_ == 0)
{
v___y_2728_ = v_a_2776_;
v___y_2729_ = v___x_2780_;
v_a_2730_ = v_a_2782_;
goto v___jp_2727_;
}
else
{
lean_object* v___x_2786_; lean_object* v___x_8909__overap_2787_; lean_object* v___x_2788_; 
lean_inc(v_a_2782_);
v___x_2786_ = l_Lean_MessageData_ofExpr(v_a_2782_);
lean_inc_ref(v_toMonadRef_2628_);
lean_inc_ref(v___x_2625_);
v___x_8909__overap_2787_ = l_Lean_addTrace___redArg(v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, v___x_2783_, v___x_2786_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2788_ = lean_apply_5(v___x_8909__overap_2787_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_dec_ref_known(v___x_2788_, 1);
v___y_2728_ = v_a_2776_;
v___y_2729_ = v___x_2780_;
v_a_2730_ = v_a_2782_;
goto v___jp_2727_;
}
else
{
lean_object* v_a_2789_; 
lean_dec(v_a_2782_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
v___y_2722_ = v_a_2776_;
v___y_2723_ = v___x_2780_;
v_a_2724_ = v_a_2789_;
goto v___jp_2721_;
}
}
}
else
{
lean_object* v_a_2790_; 
v_a_2790_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v___x_2781_, 1);
v___y_2722_ = v_a_2776_;
v___y_2723_ = v___x_2780_;
v_a_2724_ = v_a_2790_;
goto v___jp_2721_;
}
}
else
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2792_ = lean_apply_5(v_k_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; uint8_t v___x_2796_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
v___x_2794_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2795_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2796_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2648_, v_options_2632_, v___x_2795_);
if (v___x_2796_ == 0)
{
v___y_2769_ = v_a_2776_;
v___y_2770_ = v___x_2791_;
v_a_2771_ = v_a_2793_;
goto v___jp_2768_;
}
else
{
lean_object* v___x_2797_; lean_object* v___x_8971__overap_2798_; lean_object* v___x_2799_; 
lean_inc(v_a_2793_);
v___x_2797_ = l_Lean_MessageData_ofExpr(v_a_2793_);
lean_inc_ref(v_toMonadRef_2628_);
lean_inc_ref(v___x_2625_);
v___x_8971__overap_2798_ = l_Lean_addTrace___redArg(v___x_2625_, v___x_2626_, v_toMonadRef_2628_, v___x_2649_, v___x_2794_, v___x_2797_);
lean_inc(v_a_2584_);
lean_inc_ref(v_a_2583_);
lean_inc(v_a_2582_);
lean_inc_ref(v_a_2581_);
v___x_2799_ = lean_apply_5(v___x_8971__overap_2798_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, lean_box(0));
if (lean_obj_tag(v___x_2799_) == 0)
{
lean_dec_ref_known(v___x_2799_, 1);
v___y_2769_ = v_a_2776_;
v___y_2770_ = v___x_2791_;
v_a_2771_ = v_a_2793_;
goto v___jp_2768_;
}
else
{
lean_object* v_a_2800_; 
lean_dec(v_a_2793_);
v_a_2800_ = lean_ctor_get(v___x_2799_, 0);
lean_inc(v_a_2800_);
lean_dec_ref_known(v___x_2799_, 1);
v___y_2763_ = v_a_2776_;
v___y_2764_ = v___x_2791_;
v_a_2765_ = v_a_2800_;
goto v___jp_2762_;
}
}
}
else
{
lean_object* v_a_2801_; 
v_a_2801_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2801_);
lean_dec_ref_known(v___x_2792_, 1);
v___y_2763_ = v_a_2776_;
v___y_2764_ = v___x_2791_;
v_a_2765_ = v_a_2801_;
goto v___jp_2762_;
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v___f_2682_);
lean_dec_ref(v___x_2625_);
lean_dec_ref(v_k_2580_);
v_a_2802_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2775_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2775_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2844_, lean_object* v_inst_2845_, lean_object* v_f_2846_, lean_object* v_xs_2847_, lean_object* v_k_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_, lean_object* v_a_2851_, lean_object* v_a_2852_, lean_object* v_a_2853_){
_start:
{
lean_object* v_res_2854_; 
v_res_2854_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2844_, v_inst_2845_, v_f_2846_, v_xs_2847_, v_k_2848_, v_a_2849_, v_a_2850_, v_a_2851_, v_a_2852_);
lean_dec(v_a_2852_);
lean_dec_ref(v_a_2851_);
lean_dec(v_a_2850_);
lean_dec_ref(v_a_2849_);
return v_res_2854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2855_, lean_object* v_00_u03b2_2856_, lean_object* v_inst_2857_, lean_object* v_inst_2858_, lean_object* v_f_2859_, lean_object* v_xs_2860_, lean_object* v_k_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_, lean_object* v_a_2864_, lean_object* v_a_2865_){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2857_, v_inst_2858_, v_f_2859_, v_xs_2860_, v_k_2861_, v_a_2862_, v_a_2863_, v_a_2864_, v_a_2865_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2868_, lean_object* v_00_u03b2_2869_, lean_object* v_inst_2870_, lean_object* v_inst_2871_, lean_object* v_f_2872_, lean_object* v_xs_2873_, lean_object* v_k_2874_, lean_object* v_a_2875_, lean_object* v_a_2876_, lean_object* v_a_2877_, lean_object* v_a_2878_, lean_object* v_a_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2868_, v_00_u03b2_2869_, v_inst_2870_, v_inst_2871_, v_f_2872_, v_xs_2873_, v_k_2874_, v_a_2875_, v_a_2876_, v_a_2877_, v_a_2878_);
lean_dec(v_a_2878_);
lean_dec_ref(v_a_2877_);
lean_dec(v_a_2876_);
lean_dec_ref(v_a_2875_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2881_, uint8_t v_allowLevelAssignments_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_){
_start:
{
lean_object* v___x_2888_; 
v___x_2888_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2882_, v_k_2881_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; lean_object* v___x_2891_; uint8_t v_isShared_2892_; uint8_t v_isSharedCheck_2896_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2896_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2896_ == 0)
{
v___x_2891_ = v___x_2888_;
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
else
{
lean_inc(v_a_2889_);
lean_dec(v___x_2888_);
v___x_2891_ = lean_box(0);
v_isShared_2892_ = v_isSharedCheck_2896_;
goto v_resetjp_2890_;
}
v_resetjp_2890_:
{
lean_object* v___x_2894_; 
if (v_isShared_2892_ == 0)
{
v___x_2894_ = v___x_2891_;
goto v_reusejp_2893_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_a_2889_);
v___x_2894_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2893_;
}
v_reusejp_2893_:
{
return v___x_2894_;
}
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
v_a_2897_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2888_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2888_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2905_, lean_object* v_allowLevelAssignments_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2912_; lean_object* v_res_2913_; 
v_allowLevelAssignments_boxed_2912_ = lean_unbox(v_allowLevelAssignments_2906_);
v_res_2913_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2905_, v_allowLevelAssignments_boxed_2912_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v___y_2908_);
lean_dec_ref(v___y_2907_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2914_, lean_object* v_k_2915_, uint8_t v_allowLevelAssignments_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v___x_2922_; 
v___x_2922_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2915_, v_allowLevelAssignments_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
return v___x_2922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2923_, lean_object* v_k_2924_, lean_object* v_allowLevelAssignments_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2931_; lean_object* v_res_2932_; 
v_allowLevelAssignments_boxed_2931_ = lean_unbox(v_allowLevelAssignments_2925_);
v_res_2932_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2923_, v_k_2924_, v_allowLevelAssignments_boxed_2931_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
lean_dec(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec_ref(v___y_2926_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2933_, lean_object* v_xs_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2933_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_object* v_a_2941_; lean_object* v_fst_2942_; lean_object* v_snd_2943_; lean_object* v___x_2944_; 
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
lean_inc(v_a_2941_);
lean_dec_ref_known(v___x_2940_, 1);
v_fst_2942_ = lean_ctor_get(v_a_2941_, 0);
lean_inc(v_fst_2942_);
v_snd_2943_ = lean_ctor_get(v_a_2941_, 1);
lean_inc(v_snd_2943_);
lean_dec(v_a_2941_);
v___x_2944_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2942_, v_snd_2943_, v_xs_2934_, v___y_2935_, v___y_2936_, v___y_2937_, v___y_2938_);
return v___x_2944_;
}
else
{
lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
v_a_2945_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2940_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2940_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2953_, lean_object* v_xs_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_){
_start:
{
lean_object* v_res_2960_; 
v_res_2960_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2953_, v_xs_2954_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
lean_dec(v___y_2958_);
lean_dec_ref(v___y_2957_);
lean_dec(v___y_2956_);
lean_dec_ref(v___y_2955_);
lean_dec_ref(v_xs_2954_);
return v_res_2960_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2961_ = lean_unsigned_to_nat(32u);
v___x_2962_ = lean_mk_empty_array_with_capacity(v___x_2961_);
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2962_);
return v___x_2963_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2964_ = ((size_t)5ULL);
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = lean_unsigned_to_nat(32u);
v___x_2967_ = lean_mk_empty_array_with_capacity(v___x_2966_);
v___x_2968_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2969_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v___x_2967_);
lean_ctor_set(v___x_2969_, 2, v___x_2965_);
lean_ctor_set(v___x_2969_, 3, v___x_2965_);
lean_ctor_set_usize(v___x_2969_, 4, v___x_2964_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2970_){
_start:
{
lean_object* v___x_2972_; lean_object* v_traceState_2973_; lean_object* v_traces_2974_; lean_object* v___x_2975_; lean_object* v_traceState_2976_; lean_object* v_env_2977_; lean_object* v_nextMacroScope_2978_; lean_object* v_ngen_2979_; lean_object* v_auxDeclNGen_2980_; lean_object* v_cache_2981_; lean_object* v_recordedDeps_2982_; lean_object* v_messages_2983_; lean_object* v_infoState_2984_; lean_object* v_snapshotTasks_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3004_; 
v___x_2972_ = lean_st_ref_get(v___y_2970_);
v_traceState_2973_ = lean_ctor_get(v___x_2972_, 4);
lean_inc_ref(v_traceState_2973_);
lean_dec(v___x_2972_);
v_traces_2974_ = lean_ctor_get(v_traceState_2973_, 0);
lean_inc_ref(v_traces_2974_);
lean_dec_ref(v_traceState_2973_);
v___x_2975_ = lean_st_ref_take(v___y_2970_);
v_traceState_2976_ = lean_ctor_get(v___x_2975_, 4);
v_env_2977_ = lean_ctor_get(v___x_2975_, 0);
v_nextMacroScope_2978_ = lean_ctor_get(v___x_2975_, 1);
v_ngen_2979_ = lean_ctor_get(v___x_2975_, 2);
v_auxDeclNGen_2980_ = lean_ctor_get(v___x_2975_, 3);
v_cache_2981_ = lean_ctor_get(v___x_2975_, 5);
v_recordedDeps_2982_ = lean_ctor_get(v___x_2975_, 6);
v_messages_2983_ = lean_ctor_get(v___x_2975_, 7);
v_infoState_2984_ = lean_ctor_get(v___x_2975_, 8);
v_snapshotTasks_2985_ = lean_ctor_get(v___x_2975_, 9);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2987_ = v___x_2975_;
v_isShared_2988_ = v_isSharedCheck_3004_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_snapshotTasks_2985_);
lean_inc(v_infoState_2984_);
lean_inc(v_messages_2983_);
lean_inc(v_recordedDeps_2982_);
lean_inc(v_cache_2981_);
lean_inc(v_traceState_2976_);
lean_inc(v_auxDeclNGen_2980_);
lean_inc(v_ngen_2979_);
lean_inc(v_nextMacroScope_2978_);
lean_inc(v_env_2977_);
lean_dec(v___x_2975_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3004_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint64_t v_tid_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3002_; 
v_tid_2989_ = lean_ctor_get_uint64(v_traceState_2976_, sizeof(void*)*1);
v_isSharedCheck_3002_ = !lean_is_exclusive(v_traceState_2976_);
if (v_isSharedCheck_3002_ == 0)
{
lean_object* v_unused_3003_; 
v_unused_3003_ = lean_ctor_get(v_traceState_2976_, 0);
lean_dec(v_unused_3003_);
v___x_2991_ = v_traceState_2976_;
v_isShared_2992_ = v_isSharedCheck_3002_;
goto v_resetjp_2990_;
}
else
{
lean_dec(v_traceState_2976_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3002_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; lean_object* v___x_2995_; 
v___x_2993_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_2992_ == 0)
{
lean_ctor_set(v___x_2991_, 0, v___x_2993_);
v___x_2995_ = v___x_2991_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v___x_2993_);
lean_ctor_set_uint64(v_reuseFailAlloc_3001_, sizeof(void*)*1, v_tid_2989_);
v___x_2995_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
lean_object* v___x_2997_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 4, v___x_2995_);
v___x_2997_ = v___x_2987_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_env_2977_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_nextMacroScope_2978_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v_ngen_2979_);
lean_ctor_set(v_reuseFailAlloc_3000_, 3, v_auxDeclNGen_2980_);
lean_ctor_set(v_reuseFailAlloc_3000_, 4, v___x_2995_);
lean_ctor_set(v_reuseFailAlloc_3000_, 5, v_cache_2981_);
lean_ctor_set(v_reuseFailAlloc_3000_, 6, v_recordedDeps_2982_);
lean_ctor_set(v_reuseFailAlloc_3000_, 7, v_messages_2983_);
lean_ctor_set(v_reuseFailAlloc_3000_, 8, v_infoState_2984_);
lean_ctor_set(v_reuseFailAlloc_3000_, 9, v_snapshotTasks_2985_);
v___x_2997_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
lean_object* v___x_2998_; lean_object* v___x_2999_; 
v___x_2998_ = lean_st_ref_put(v___y_2970_, v___x_2997_);
v___x_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2999_, 0, v_traces_2974_);
return v___x_2999_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3005_, lean_object* v___y_3006_){
_start:
{
lean_object* v_res_3007_; 
v_res_3007_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3005_);
lean_dec(v___y_3005_);
return v_res_3007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3008_, lean_object* v_opt_3009_){
_start:
{
lean_object* v_name_3010_; lean_object* v_defValue_3011_; lean_object* v_map_3012_; lean_object* v___x_3013_; 
v_name_3010_ = lean_ctor_get(v_opt_3009_, 0);
v_defValue_3011_ = lean_ctor_get(v_opt_3009_, 1);
v_map_3012_ = lean_ctor_get(v_opts_3008_, 0);
v___x_3013_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3012_, v_name_3010_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_inc(v_defValue_3011_);
return v_defValue_3011_;
}
else
{
lean_object* v_val_3014_; 
v_val_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_val_3014_);
lean_dec_ref_known(v___x_3013_, 1);
if (lean_obj_tag(v_val_3014_) == 3)
{
lean_object* v_v_3015_; 
v_v_3015_ = lean_ctor_get(v_val_3014_, 0);
lean_inc(v_v_3015_);
lean_dec_ref_known(v_val_3014_, 1);
return v_v_3015_;
}
else
{
lean_dec(v_val_3014_);
lean_inc(v_defValue_3011_);
return v_defValue_3011_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3016_, lean_object* v_opt_3017_){
_start:
{
lean_object* v_res_3018_; 
v_res_3018_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3016_, v_opt_3017_);
lean_dec_ref(v_opt_3017_);
lean_dec_ref(v_opts_3016_);
return v_res_3018_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3019_, lean_object* v_opt_3020_){
_start:
{
lean_object* v_name_3021_; lean_object* v_defValue_3022_; lean_object* v_map_3023_; lean_object* v___x_3024_; 
v_name_3021_ = lean_ctor_get(v_opt_3020_, 0);
v_defValue_3022_ = lean_ctor_get(v_opt_3020_, 1);
v_map_3023_ = lean_ctor_get(v_opts_3019_, 0);
v___x_3024_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3023_, v_name_3021_);
if (lean_obj_tag(v___x_3024_) == 0)
{
uint8_t v___x_3025_; 
v___x_3025_ = lean_unbox(v_defValue_3022_);
return v___x_3025_;
}
else
{
lean_object* v_val_3026_; 
v_val_3026_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_val_3026_);
lean_dec_ref_known(v___x_3024_, 1);
if (lean_obj_tag(v_val_3026_) == 1)
{
uint8_t v_v_3027_; 
v_v_3027_ = lean_ctor_get_uint8(v_val_3026_, 0);
lean_dec_ref_known(v_val_3026_, 0);
return v_v_3027_;
}
else
{
uint8_t v___x_3028_; 
lean_dec(v_val_3026_);
v___x_3028_ = lean_unbox(v_defValue_3022_);
return v___x_3028_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3029_, lean_object* v_opt_3030_){
_start:
{
uint8_t v_res_3031_; lean_object* v_r_3032_; 
v_res_3031_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3029_, v_opt_3030_);
lean_dec_ref(v_opt_3030_);
lean_dec_ref(v_opts_3029_);
v_r_3032_ = lean_box(v_res_3031_);
return v_r_3032_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3033_){
_start:
{
if (lean_obj_tag(v_e_3033_) == 0)
{
uint8_t v___x_3034_; 
v___x_3034_ = 2;
return v___x_3034_;
}
else
{
lean_object* v_a_3035_; uint8_t v___x_3036_; 
v_a_3035_ = lean_ctor_get(v_e_3033_, 0);
v___x_3036_ = l_Lean_Expr_hasSyntheticSorry(v_a_3035_);
if (v___x_3036_ == 0)
{
uint8_t v___x_3037_; 
v___x_3037_ = 0;
return v___x_3037_;
}
else
{
uint8_t v___x_3038_; 
v___x_3038_ = 1;
return v___x_3038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3039_){
_start:
{
uint8_t v_res_3040_; lean_object* v_r_3041_; 
v_res_3040_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3039_);
lean_dec_ref(v_e_3039_);
v_r_3041_ = lean_box(v_res_3040_);
return v_r_3041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3042_, size_t v_i_3043_, lean_object* v_bs_3044_){
_start:
{
uint8_t v___x_3045_; 
v___x_3045_ = lean_usize_dec_lt(v_i_3043_, v_sz_3042_);
if (v___x_3045_ == 0)
{
return v_bs_3044_;
}
else
{
lean_object* v_v_3046_; lean_object* v_msg_3047_; lean_object* v___x_3048_; lean_object* v_bs_x27_3049_; size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v_v_3046_ = lean_array_uget_borrowed(v_bs_3044_, v_i_3043_);
v_msg_3047_ = lean_ctor_get(v_v_3046_, 1);
lean_inc_ref(v_msg_3047_);
v___x_3048_ = lean_unsigned_to_nat(0u);
v_bs_x27_3049_ = lean_array_uset(v_bs_3044_, v_i_3043_, v___x_3048_);
v___x_3050_ = ((size_t)1ULL);
v___x_3051_ = lean_usize_add(v_i_3043_, v___x_3050_);
v___x_3052_ = lean_array_uset(v_bs_x27_3049_, v_i_3043_, v_msg_3047_);
v_i_3043_ = v___x_3051_;
v_bs_3044_ = v___x_3052_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3054_, lean_object* v_i_3055_, lean_object* v_bs_3056_){
_start:
{
size_t v_sz_boxed_3057_; size_t v_i_boxed_3058_; lean_object* v_res_3059_; 
v_sz_boxed_3057_ = lean_unbox_usize(v_sz_3054_);
lean_dec(v_sz_3054_);
v_i_boxed_3058_ = lean_unbox_usize(v_i_3055_);
lean_dec(v_i_3055_);
v_res_3059_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3057_, v_i_boxed_3058_, v_bs_3056_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3060_, lean_object* v_data_3061_, lean_object* v_ref_3062_, lean_object* v_msg_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_){
_start:
{
lean_object* v_toCold_3069_; lean_object* v_currRecDepth_3070_; lean_object* v_ref_3071_; uint16_t v_optionFlags_3072_; uint8_t v_suppressElabErrors_3073_; uint8_t v_isRecordingDeps_3074_; lean_object* v_ref_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v_traceState_3078_; lean_object* v_traces_3079_; lean_object* v___x_3080_; size_t v_sz_3081_; size_t v___x_3082_; lean_object* v___x_3083_; lean_object* v_msg_3084_; lean_object* v___x_3085_; lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3124_; 
v_toCold_3069_ = lean_ctor_get(v___y_3066_, 0);
v_currRecDepth_3070_ = lean_ctor_get(v___y_3066_, 1);
v_ref_3071_ = lean_ctor_get(v___y_3066_, 2);
v_optionFlags_3072_ = lean_ctor_get_uint16(v___y_3066_, sizeof(void*)*3);
v_suppressElabErrors_3073_ = lean_ctor_get_uint8(v___y_3066_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3074_ = lean_ctor_get_uint8(v___y_3066_, sizeof(void*)*3 + 3);
v_ref_3075_ = l_Lean_replaceRef(v_ref_3062_, v_ref_3071_);
lean_inc(v_currRecDepth_3070_);
lean_inc_ref(v_toCold_3069_);
v___x_3076_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3076_, 0, v_toCold_3069_);
lean_ctor_set(v___x_3076_, 1, v_currRecDepth_3070_);
lean_ctor_set(v___x_3076_, 2, v_ref_3075_);
lean_ctor_set_uint16(v___x_3076_, sizeof(void*)*3, v_optionFlags_3072_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*3 + 2, v_suppressElabErrors_3073_);
lean_ctor_set_uint8(v___x_3076_, sizeof(void*)*3 + 3, v_isRecordingDeps_3074_);
v___x_3077_ = lean_st_ref_get(v___y_3067_);
v_traceState_3078_ = lean_ctor_get(v___x_3077_, 4);
lean_inc_ref(v_traceState_3078_);
lean_dec(v___x_3077_);
v_traces_3079_ = lean_ctor_get(v_traceState_3078_, 0);
lean_inc_ref(v_traces_3079_);
lean_dec_ref(v_traceState_3078_);
v___x_3080_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3079_);
lean_dec_ref(v_traces_3079_);
v_sz_3081_ = lean_array_size(v___x_3080_);
v___x_3082_ = ((size_t)0ULL);
v___x_3083_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3081_, v___x_3082_, v___x_3080_);
v_msg_3084_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3084_, 0, v_data_3061_);
lean_ctor_set(v_msg_3084_, 1, v_msg_3063_);
lean_ctor_set(v_msg_3084_, 2, v___x_3083_);
v___x_3085_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3084_, v___y_3064_, v___y_3065_, v___x_3076_, v___y_3067_);
lean_dec_ref_known(v___x_3076_, 3);
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3088_ = v___x_3085_;
v_isShared_3089_ = v_isSharedCheck_3124_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3085_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3124_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3090_; lean_object* v_traceState_3091_; lean_object* v_env_3092_; lean_object* v_nextMacroScope_3093_; lean_object* v_ngen_3094_; lean_object* v_auxDeclNGen_3095_; lean_object* v_cache_3096_; lean_object* v_recordedDeps_3097_; lean_object* v_messages_3098_; lean_object* v_infoState_3099_; lean_object* v_snapshotTasks_3100_; lean_object* v___x_3102_; uint8_t v_isShared_3103_; uint8_t v_isSharedCheck_3123_; 
v___x_3090_ = lean_st_ref_take(v___y_3067_);
v_traceState_3091_ = lean_ctor_get(v___x_3090_, 4);
v_env_3092_ = lean_ctor_get(v___x_3090_, 0);
v_nextMacroScope_3093_ = lean_ctor_get(v___x_3090_, 1);
v_ngen_3094_ = lean_ctor_get(v___x_3090_, 2);
v_auxDeclNGen_3095_ = lean_ctor_get(v___x_3090_, 3);
v_cache_3096_ = lean_ctor_get(v___x_3090_, 5);
v_recordedDeps_3097_ = lean_ctor_get(v___x_3090_, 6);
v_messages_3098_ = lean_ctor_get(v___x_3090_, 7);
v_infoState_3099_ = lean_ctor_get(v___x_3090_, 8);
v_snapshotTasks_3100_ = lean_ctor_get(v___x_3090_, 9);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3102_ = v___x_3090_;
v_isShared_3103_ = v_isSharedCheck_3123_;
goto v_resetjp_3101_;
}
else
{
lean_inc(v_snapshotTasks_3100_);
lean_inc(v_infoState_3099_);
lean_inc(v_messages_3098_);
lean_inc(v_recordedDeps_3097_);
lean_inc(v_cache_3096_);
lean_inc(v_traceState_3091_);
lean_inc(v_auxDeclNGen_3095_);
lean_inc(v_ngen_3094_);
lean_inc(v_nextMacroScope_3093_);
lean_inc(v_env_3092_);
lean_dec(v___x_3090_);
v___x_3102_ = lean_box(0);
v_isShared_3103_ = v_isSharedCheck_3123_;
goto v_resetjp_3101_;
}
v_resetjp_3101_:
{
uint64_t v_tid_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3121_; 
v_tid_3104_ = lean_ctor_get_uint64(v_traceState_3091_, sizeof(void*)*1);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_traceState_3091_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v_traceState_3091_, 0);
lean_dec(v_unused_3122_);
v___x_3106_ = v_traceState_3091_;
v_isShared_3107_ = v_isSharedCheck_3121_;
goto v_resetjp_3105_;
}
else
{
lean_dec(v_traceState_3091_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3121_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3112_; 
v___x_3108_ = lean_box(0);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v_ref_3062_);
lean_ctor_set(v___x_3109_, 1, v_a_3086_);
v___x_3110_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3060_, v___x_3109_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3110_);
v___x_3112_ = v___x_3106_;
goto v_reusejp_3111_;
}
else
{
lean_object* v_reuseFailAlloc_3120_; 
v_reuseFailAlloc_3120_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3120_, 0, v___x_3110_);
lean_ctor_set_uint64(v_reuseFailAlloc_3120_, sizeof(void*)*1, v_tid_3104_);
v___x_3112_ = v_reuseFailAlloc_3120_;
goto v_reusejp_3111_;
}
v_reusejp_3111_:
{
lean_object* v___x_3114_; 
if (v_isShared_3103_ == 0)
{
lean_ctor_set(v___x_3102_, 4, v___x_3112_);
v___x_3114_ = v___x_3102_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_env_3092_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v_nextMacroScope_3093_);
lean_ctor_set(v_reuseFailAlloc_3119_, 2, v_ngen_3094_);
lean_ctor_set(v_reuseFailAlloc_3119_, 3, v_auxDeclNGen_3095_);
lean_ctor_set(v_reuseFailAlloc_3119_, 4, v___x_3112_);
lean_ctor_set(v_reuseFailAlloc_3119_, 5, v_cache_3096_);
lean_ctor_set(v_reuseFailAlloc_3119_, 6, v_recordedDeps_3097_);
lean_ctor_set(v_reuseFailAlloc_3119_, 7, v_messages_3098_);
lean_ctor_set(v_reuseFailAlloc_3119_, 8, v_infoState_3099_);
lean_ctor_set(v_reuseFailAlloc_3119_, 9, v_snapshotTasks_3100_);
v___x_3114_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
lean_object* v___x_3115_; lean_object* v___x_3117_; 
v___x_3115_ = lean_st_ref_put(v___y_3067_, v___x_3114_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 0, v___x_3108_);
v___x_3117_ = v___x_3088_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3108_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3125_, lean_object* v_data_3126_, lean_object* v_ref_3127_, lean_object* v_msg_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v_res_3134_; 
v_res_3134_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3125_, v_data_3126_, v_ref_3127_, v_msg_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3135_){
_start:
{
if (lean_obj_tag(v_x_3135_) == 0)
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_a_3137_ = lean_ctor_get(v_x_3135_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v_x_3135_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v_x_3135_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v_x_3135_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
lean_ctor_set_tag(v___x_3139_, 1);
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_a_3145_ = lean_ctor_get(v_x_3135_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_x_3135_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v_x_3135_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v_x_3135_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
lean_ctor_set_tag(v___x_3147_, 0);
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v_res_3155_; 
v_res_3155_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3153_);
return v_res_3155_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3156_; double v___x_3157_; 
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = lean_float_of_nat(v___x_3156_);
return v___x_3157_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3160_ = l_Lean_stringToMessageData(v___x_3159_);
return v___x_3160_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3161_; double v___x_3162_; 
v___x_3161_ = lean_unsigned_to_nat(1000u);
v___x_3162_ = lean_float_of_nat(v___x_3161_);
return v___x_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3163_, uint8_t v_collapsed_3164_, lean_object* v_tag_3165_, lean_object* v_opts_3166_, uint8_t v_clsEnabled_3167_, lean_object* v_oldTraces_3168_, lean_object* v_msg_3169_, lean_object* v_resStartStop_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v_fst_3176_; lean_object* v_snd_3177_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v_data_3181_; lean_object* v_fst_3192_; lean_object* v_snd_3193_; lean_object* v___x_3194_; uint8_t v___x_3195_; lean_object* v___y_3197_; lean_object* v_a_3198_; uint8_t v___y_3213_; double v___y_3245_; 
v_fst_3176_ = lean_ctor_get(v_resStartStop_3170_, 0);
lean_inc(v_fst_3176_);
v_snd_3177_ = lean_ctor_get(v_resStartStop_3170_, 1);
lean_inc(v_snd_3177_);
lean_dec_ref(v_resStartStop_3170_);
v_fst_3192_ = lean_ctor_get(v_snd_3177_, 0);
lean_inc(v_fst_3192_);
v_snd_3193_ = lean_ctor_get(v_snd_3177_, 1);
lean_inc(v_snd_3193_);
lean_dec(v_snd_3177_);
v___x_3194_ = l_Lean_trace_profiler;
v___x_3195_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3166_, v___x_3194_);
if (v___x_3195_ == 0)
{
v___y_3213_ = v___x_3195_;
goto v___jp_3212_;
}
else
{
lean_object* v___x_3250_; uint8_t v___x_3251_; 
v___x_3250_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3251_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3166_, v___x_3250_);
if (v___x_3251_ == 0)
{
lean_object* v___x_3252_; lean_object* v___x_3253_; double v___x_3254_; double v___x_3255_; double v___x_3256_; 
v___x_3252_ = l_Lean_trace_profiler_threshold;
v___x_3253_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3166_, v___x_3252_);
v___x_3254_ = lean_float_of_nat(v___x_3253_);
v___x_3255_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3256_ = lean_float_div(v___x_3254_, v___x_3255_);
v___y_3245_ = v___x_3256_;
goto v___jp_3244_;
}
else
{
lean_object* v___x_3257_; lean_object* v___x_3258_; double v___x_3259_; 
v___x_3257_ = l_Lean_trace_profiler_threshold;
v___x_3258_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3166_, v___x_3257_);
v___x_3259_ = lean_float_of_nat(v___x_3258_);
v___y_3245_ = v___x_3259_;
goto v___jp_3244_;
}
}
v___jp_3178_:
{
lean_object* v___x_3182_; 
lean_inc(v___y_3180_);
v___x_3182_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3168_, v_data_3181_, v___y_3180_, v___y_3179_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v___x_3183_; 
lean_dec_ref_known(v___x_3182_, 1);
v___x_3183_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3176_);
return v___x_3183_;
}
else
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3191_; 
lean_dec(v_fst_3176_);
v_a_3184_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3191_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3186_ = v___x_3182_;
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___x_3182_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3191_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v___x_3189_; 
if (v_isShared_3187_ == 0)
{
v___x_3189_ = v___x_3186_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_a_3184_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
}
}
v___jp_3196_:
{
uint8_t v_result_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; double v___x_3202_; lean_object* v_data_3203_; 
v_result_3199_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3176_);
v___x_3200_ = lean_box(v_result_3199_);
v___x_3201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3201_, 0, v___x_3200_);
v___x_3202_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3165_);
lean_inc_ref(v___x_3201_);
lean_inc(v_cls_3163_);
v_data_3203_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3203_, 0, v_cls_3163_);
lean_ctor_set(v_data_3203_, 1, v___x_3201_);
lean_ctor_set(v_data_3203_, 2, v_tag_3165_);
lean_ctor_set_float(v_data_3203_, sizeof(void*)*3, v___x_3202_);
lean_ctor_set_float(v_data_3203_, sizeof(void*)*3 + 8, v___x_3202_);
lean_ctor_set_uint8(v_data_3203_, sizeof(void*)*3 + 16, v_collapsed_3164_);
if (v___x_3195_ == 0)
{
lean_dec_ref_known(v___x_3201_, 1);
lean_dec(v_snd_3193_);
lean_dec(v_fst_3192_);
lean_dec_ref(v_tag_3165_);
lean_dec(v_cls_3163_);
v___y_3179_ = v_a_3198_;
v___y_3180_ = v___y_3197_;
v_data_3181_ = v_data_3203_;
goto v___jp_3178_;
}
else
{
lean_object* v_data_3204_; double v___x_3205_; double v___x_3206_; 
lean_dec_ref_known(v_data_3203_, 3);
v_data_3204_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3204_, 0, v_cls_3163_);
lean_ctor_set(v_data_3204_, 1, v___x_3201_);
lean_ctor_set(v_data_3204_, 2, v_tag_3165_);
v___x_3205_ = lean_unbox_float(v_fst_3192_);
lean_dec(v_fst_3192_);
lean_ctor_set_float(v_data_3204_, sizeof(void*)*3, v___x_3205_);
v___x_3206_ = lean_unbox_float(v_snd_3193_);
lean_dec(v_snd_3193_);
lean_ctor_set_float(v_data_3204_, sizeof(void*)*3 + 8, v___x_3206_);
lean_ctor_set_uint8(v_data_3204_, sizeof(void*)*3 + 16, v_collapsed_3164_);
v___y_3179_ = v_a_3198_;
v___y_3180_ = v___y_3197_;
v_data_3181_ = v_data_3204_;
goto v___jp_3178_;
}
}
v___jp_3207_:
{
lean_object* v_ref_3208_; lean_object* v___x_3209_; 
v_ref_3208_ = lean_ctor_get(v___y_3173_, 2);
lean_inc(v___y_3174_);
lean_inc_ref(v___y_3173_);
lean_inc(v___y_3172_);
lean_inc_ref(v___y_3171_);
lean_inc(v_fst_3176_);
v___x_3209_ = lean_apply_6(v_msg_3169_, v_fst_3176_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, lean_box(0));
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref_known(v___x_3209_, 1);
v___y_3197_ = v_ref_3208_;
v_a_3198_ = v_a_3210_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3211_; 
lean_dec_ref_known(v___x_3209_, 1);
v___x_3211_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3197_ = v_ref_3208_;
v_a_3198_ = v___x_3211_;
goto v___jp_3196_;
}
}
v___jp_3212_:
{
if (v_clsEnabled_3167_ == 0)
{
if (v___y_3213_ == 0)
{
lean_object* v___x_3214_; lean_object* v_traceState_3215_; lean_object* v_env_3216_; lean_object* v_nextMacroScope_3217_; lean_object* v_ngen_3218_; lean_object* v_auxDeclNGen_3219_; lean_object* v_cache_3220_; lean_object* v_recordedDeps_3221_; lean_object* v_messages_3222_; lean_object* v_infoState_3223_; lean_object* v_snapshotTasks_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3243_; 
lean_dec(v_snd_3193_);
lean_dec(v_fst_3192_);
lean_dec_ref(v_msg_3169_);
lean_dec_ref(v_tag_3165_);
lean_dec(v_cls_3163_);
v___x_3214_ = lean_st_ref_take(v___y_3174_);
v_traceState_3215_ = lean_ctor_get(v___x_3214_, 4);
v_env_3216_ = lean_ctor_get(v___x_3214_, 0);
v_nextMacroScope_3217_ = lean_ctor_get(v___x_3214_, 1);
v_ngen_3218_ = lean_ctor_get(v___x_3214_, 2);
v_auxDeclNGen_3219_ = lean_ctor_get(v___x_3214_, 3);
v_cache_3220_ = lean_ctor_get(v___x_3214_, 5);
v_recordedDeps_3221_ = lean_ctor_get(v___x_3214_, 6);
v_messages_3222_ = lean_ctor_get(v___x_3214_, 7);
v_infoState_3223_ = lean_ctor_get(v___x_3214_, 8);
v_snapshotTasks_3224_ = lean_ctor_get(v___x_3214_, 9);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3226_ = v___x_3214_;
v_isShared_3227_ = v_isSharedCheck_3243_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_snapshotTasks_3224_);
lean_inc(v_infoState_3223_);
lean_inc(v_messages_3222_);
lean_inc(v_recordedDeps_3221_);
lean_inc(v_cache_3220_);
lean_inc(v_traceState_3215_);
lean_inc(v_auxDeclNGen_3219_);
lean_inc(v_ngen_3218_);
lean_inc(v_nextMacroScope_3217_);
lean_inc(v_env_3216_);
lean_dec(v___x_3214_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3243_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
uint64_t v_tid_3228_; lean_object* v_traces_3229_; lean_object* v___x_3231_; uint8_t v_isShared_3232_; uint8_t v_isSharedCheck_3242_; 
v_tid_3228_ = lean_ctor_get_uint64(v_traceState_3215_, sizeof(void*)*1);
v_traces_3229_ = lean_ctor_get(v_traceState_3215_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v_traceState_3215_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3231_ = v_traceState_3215_;
v_isShared_3232_ = v_isSharedCheck_3242_;
goto v_resetjp_3230_;
}
else
{
lean_inc(v_traces_3229_);
lean_dec(v_traceState_3215_);
v___x_3231_ = lean_box(0);
v_isShared_3232_ = v_isSharedCheck_3242_;
goto v_resetjp_3230_;
}
v_resetjp_3230_:
{
lean_object* v___x_3233_; lean_object* v___x_3235_; 
v___x_3233_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3168_, v_traces_3229_);
lean_dec_ref(v_traces_3229_);
if (v_isShared_3232_ == 0)
{
lean_ctor_set(v___x_3231_, 0, v___x_3233_);
v___x_3235_ = v___x_3231_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v___x_3233_);
lean_ctor_set_uint64(v_reuseFailAlloc_3241_, sizeof(void*)*1, v_tid_3228_);
v___x_3235_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3237_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 4, v___x_3235_);
v___x_3237_ = v___x_3226_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_env_3216_);
lean_ctor_set(v_reuseFailAlloc_3240_, 1, v_nextMacroScope_3217_);
lean_ctor_set(v_reuseFailAlloc_3240_, 2, v_ngen_3218_);
lean_ctor_set(v_reuseFailAlloc_3240_, 3, v_auxDeclNGen_3219_);
lean_ctor_set(v_reuseFailAlloc_3240_, 4, v___x_3235_);
lean_ctor_set(v_reuseFailAlloc_3240_, 5, v_cache_3220_);
lean_ctor_set(v_reuseFailAlloc_3240_, 6, v_recordedDeps_3221_);
lean_ctor_set(v_reuseFailAlloc_3240_, 7, v_messages_3222_);
lean_ctor_set(v_reuseFailAlloc_3240_, 8, v_infoState_3223_);
lean_ctor_set(v_reuseFailAlloc_3240_, 9, v_snapshotTasks_3224_);
v___x_3237_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; 
v___x_3238_ = lean_st_ref_put(v___y_3174_, v___x_3237_);
v___x_3239_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3176_);
return v___x_3239_;
}
}
}
}
}
else
{
goto v___jp_3207_;
}
}
else
{
goto v___jp_3207_;
}
}
v___jp_3244_:
{
double v___x_3246_; double v___x_3247_; double v___x_3248_; uint8_t v___x_3249_; 
v___x_3246_ = lean_unbox_float(v_snd_3193_);
v___x_3247_ = lean_unbox_float(v_fst_3192_);
v___x_3248_ = lean_float_sub(v___x_3246_, v___x_3247_);
v___x_3249_ = lean_float_decLt(v___y_3245_, v___x_3248_);
v___y_3213_ = v___x_3249_;
goto v___jp_3212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3260_, lean_object* v_collapsed_3261_, lean_object* v_tag_3262_, lean_object* v_opts_3263_, lean_object* v_clsEnabled_3264_, lean_object* v_oldTraces_3265_, lean_object* v_msg_3266_, lean_object* v_resStartStop_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v_collapsed_boxed_3273_; uint8_t v_clsEnabled_boxed_3274_; lean_object* v_res_3275_; 
v_collapsed_boxed_3273_ = lean_unbox(v_collapsed_3261_);
v_clsEnabled_boxed_3274_ = lean_unbox(v_clsEnabled_3264_);
v_res_3275_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3260_, v_collapsed_boxed_3273_, v_tag_3262_, v_opts_3263_, v_clsEnabled_boxed_3274_, v_oldTraces_3265_, v_msg_3266_, v_resStartStop_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec_ref(v_opts_3263_);
return v_res_3275_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3276_, lean_object* v_a_3277_){
_start:
{
if (lean_obj_tag(v_a_3276_) == 0)
{
lean_object* v___x_3278_; 
v___x_3278_ = l_List_reverse___redArg(v_a_3277_);
return v___x_3278_;
}
else
{
lean_object* v_head_3279_; lean_object* v_tail_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3289_; 
v_head_3279_ = lean_ctor_get(v_a_3276_, 0);
v_tail_3280_ = lean_ctor_get(v_a_3276_, 1);
v_isSharedCheck_3289_ = !lean_is_exclusive(v_a_3276_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3282_ = v_a_3276_;
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_tail_3280_);
lean_inc(v_head_3279_);
lean_dec(v_a_3276_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3289_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3284_; lean_object* v___x_3286_; 
v___x_3284_ = l_Lean_MessageData_ofExpr(v_head_3279_);
if (v_isShared_3283_ == 0)
{
lean_ctor_set(v___x_3282_, 1, v_a_3277_);
lean_ctor_set(v___x_3282_, 0, v___x_3284_);
v___x_3286_ = v___x_3282_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v___x_3284_);
lean_ctor_set(v_reuseFailAlloc_3288_, 1, v_a_3277_);
v___x_3286_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
v_a_3276_ = v_tail_3280_;
v_a_3277_ = v___x_3286_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3290_, lean_object* v_xs_3291_, lean_object* v_x_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_){
_start:
{
lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3298_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3299_ = l_Lean_MessageData_ofName(v_f_3290_);
v___x_3300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3298_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3300_);
lean_ctor_set(v___x_3302_, 1, v___x_3301_);
v___x_3303_ = lean_array_to_list(v_xs_3291_);
v___x_3304_ = lean_box(0);
v___x_3305_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3303_, v___x_3304_);
v___x_3306_ = l_Lean_MessageData_ofList(v___x_3305_);
v___x_3307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3302_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3309_, lean_object* v_xs_3310_, lean_object* v_x_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3309_, v_xs_3310_, v_x_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec_ref(v_x_3311_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3320_, lean_object* v_msg_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_){
_start:
{
lean_object* v_ref_3327_; lean_object* v___x_3328_; lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3374_; 
v_ref_3327_ = lean_ctor_get(v___y_3324_, 2);
v___x_3328_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3321_, v___y_3322_, v___y_3323_, v___y_3324_, v___y_3325_);
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
v_isSharedCheck_3374_ = !lean_is_exclusive(v___x_3328_);
if (v_isSharedCheck_3374_ == 0)
{
v___x_3331_ = v___x_3328_;
v_isShared_3332_ = v_isSharedCheck_3374_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3328_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3374_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v_traceState_3334_; lean_object* v_env_3335_; lean_object* v_nextMacroScope_3336_; lean_object* v_ngen_3337_; lean_object* v_auxDeclNGen_3338_; lean_object* v_cache_3339_; lean_object* v_recordedDeps_3340_; lean_object* v_messages_3341_; lean_object* v_infoState_3342_; lean_object* v_snapshotTasks_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3373_; 
v___x_3333_ = lean_st_ref_take(v___y_3325_);
v_traceState_3334_ = lean_ctor_get(v___x_3333_, 4);
v_env_3335_ = lean_ctor_get(v___x_3333_, 0);
v_nextMacroScope_3336_ = lean_ctor_get(v___x_3333_, 1);
v_ngen_3337_ = lean_ctor_get(v___x_3333_, 2);
v_auxDeclNGen_3338_ = lean_ctor_get(v___x_3333_, 3);
v_cache_3339_ = lean_ctor_get(v___x_3333_, 5);
v_recordedDeps_3340_ = lean_ctor_get(v___x_3333_, 6);
v_messages_3341_ = lean_ctor_get(v___x_3333_, 7);
v_infoState_3342_ = lean_ctor_get(v___x_3333_, 8);
v_snapshotTasks_3343_ = lean_ctor_get(v___x_3333_, 9);
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3373_ == 0)
{
v___x_3345_ = v___x_3333_;
v_isShared_3346_ = v_isSharedCheck_3373_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_snapshotTasks_3343_);
lean_inc(v_infoState_3342_);
lean_inc(v_messages_3341_);
lean_inc(v_recordedDeps_3340_);
lean_inc(v_cache_3339_);
lean_inc(v_traceState_3334_);
lean_inc(v_auxDeclNGen_3338_);
lean_inc(v_ngen_3337_);
lean_inc(v_nextMacroScope_3336_);
lean_inc(v_env_3335_);
lean_dec(v___x_3333_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3373_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
uint64_t v_tid_3347_; lean_object* v_traces_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3372_; 
v_tid_3347_ = lean_ctor_get_uint64(v_traceState_3334_, sizeof(void*)*1);
v_traces_3348_ = lean_ctor_get(v_traceState_3334_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v_traceState_3334_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3350_ = v_traceState_3334_;
v_isShared_3351_ = v_isSharedCheck_3372_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_traces_3348_);
lean_dec(v_traceState_3334_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3372_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3353_; double v___x_3354_; uint8_t v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3363_; 
v___x_3352_ = lean_box(0);
v___x_3353_ = lean_box(0);
v___x_3354_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3355_ = 0;
v___x_3356_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3357_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3357_, 0, v_cls_3320_);
lean_ctor_set(v___x_3357_, 1, v___x_3353_);
lean_ctor_set(v___x_3357_, 2, v___x_3356_);
lean_ctor_set_float(v___x_3357_, sizeof(void*)*3, v___x_3354_);
lean_ctor_set_float(v___x_3357_, sizeof(void*)*3 + 8, v___x_3354_);
lean_ctor_set_uint8(v___x_3357_, sizeof(void*)*3 + 16, v___x_3355_);
v___x_3358_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3359_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3359_, 0, v___x_3357_);
lean_ctor_set(v___x_3359_, 1, v_a_3329_);
lean_ctor_set(v___x_3359_, 2, v___x_3358_);
lean_inc(v_ref_3327_);
v___x_3360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3360_, 0, v_ref_3327_);
lean_ctor_set(v___x_3360_, 1, v___x_3359_);
v___x_3361_ = l_Lean_PersistentArray_push___redArg(v_traces_3348_, v___x_3360_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3361_);
v___x_3363_ = v___x_3350_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3371_; 
v_reuseFailAlloc_3371_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3371_, 0, v___x_3361_);
lean_ctor_set_uint64(v_reuseFailAlloc_3371_, sizeof(void*)*1, v_tid_3347_);
v___x_3363_ = v_reuseFailAlloc_3371_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
lean_object* v___x_3365_; 
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 4, v___x_3363_);
v___x_3365_ = v___x_3345_;
goto v_reusejp_3364_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v_env_3335_);
lean_ctor_set(v_reuseFailAlloc_3370_, 1, v_nextMacroScope_3336_);
lean_ctor_set(v_reuseFailAlloc_3370_, 2, v_ngen_3337_);
lean_ctor_set(v_reuseFailAlloc_3370_, 3, v_auxDeclNGen_3338_);
lean_ctor_set(v_reuseFailAlloc_3370_, 4, v___x_3363_);
lean_ctor_set(v_reuseFailAlloc_3370_, 5, v_cache_3339_);
lean_ctor_set(v_reuseFailAlloc_3370_, 6, v_recordedDeps_3340_);
lean_ctor_set(v_reuseFailAlloc_3370_, 7, v_messages_3341_);
lean_ctor_set(v_reuseFailAlloc_3370_, 8, v_infoState_3342_);
lean_ctor_set(v_reuseFailAlloc_3370_, 9, v_snapshotTasks_3343_);
v___x_3365_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3364_;
}
v_reusejp_3364_:
{
lean_object* v___x_3366_; lean_object* v___x_3368_; 
v___x_3366_ = lean_st_ref_put(v___y_3325_, v___x_3365_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3352_);
v___x_3368_ = v___x_3331_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v___x_3352_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3375_, lean_object* v_msg_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_res_3382_; 
v_res_3382_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3375_, v_msg_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
return v_res_3382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3383_, lean_object* v_xs_3384_, lean_object* v_k_3385_, lean_object* v_a_3386_, lean_object* v_a_3387_, lean_object* v_a_3388_, lean_object* v_a_3389_){
_start:
{
lean_object* v_toCold_3391_; lean_object* v_options_3392_; uint8_t v_hasTrace_3393_; 
v_toCold_3391_ = lean_ctor_get(v_a_3388_, 0);
v_options_3392_ = lean_ctor_get(v_toCold_3391_, 2);
v_hasTrace_3393_ = lean_ctor_get_uint8(v_options_3392_, sizeof(void*)*1);
if (v_hasTrace_3393_ == 0)
{
lean_object* v___x_3394_; 
lean_dec_ref(v_xs_3384_);
lean_dec(v_f_3383_);
lean_inc(v_a_3389_);
lean_inc_ref(v_a_3388_);
lean_inc(v_a_3387_);
lean_inc_ref(v_a_3386_);
v___x_3394_ = lean_apply_5(v_k_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, lean_box(0));
return v___x_3394_;
}
else
{
lean_object* v_inheritedTraceOptions_3395_; lean_object* v___f_3396_; lean_object* v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3424_; lean_object* v_a_3425_; lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; uint8_t v___x_3431_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v_a_3435_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v_a_3450_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v_a_3466_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v_a_3472_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v_a_3477_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v_a_3489_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; uint8_t v___y_3495_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v_a_3505_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v_a_3511_; 
v_inheritedTraceOptions_3395_ = lean_ctor_get(v_toCold_3391_, 11);
v___f_3396_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3396_, 0, v_f_3383_);
lean_closure_set(v___f_3396_, 1, v_xs_3384_);
v___x_3428_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3429_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3430_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3431_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3395_, v_options_3392_, v___x_3430_);
if (v___x_3431_ == 0)
{
lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3538_ = l_Lean_trace_profiler;
v___x_3539_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3392_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; 
lean_dec_ref(v___f_3396_);
lean_inc(v_a_3389_);
lean_inc_ref(v_a_3388_);
lean_inc(v_a_3387_);
lean_inc_ref(v_a_3386_);
v___x_3540_ = lean_apply_5(v_k_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, lean_box(0));
if (lean_obj_tag(v___x_3540_) == 0)
{
lean_object* v_a_3541_; lean_object* v___x_3542_; lean_object* v___x_3543_; uint8_t v___x_3544_; 
v_a_3541_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3541_);
v___x_3542_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3543_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3544_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3395_, v_options_3392_, v___x_3543_);
if (v___x_3544_ == 0)
{
lean_dec(v_a_3541_);
return v___x_3540_;
}
else
{
lean_object* v___x_3545_; lean_object* v___x_3546_; 
lean_dec_ref_known(v___x_3540_, 1);
lean_inc(v_a_3541_);
v___x_3545_ = l_Lean_MessageData_ofExpr(v_a_3541_);
v___x_3546_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3542_, v___x_3545_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3553_ == 0)
{
lean_object* v_unused_3554_; 
v_unused_3554_ = lean_ctor_get(v___x_3546_, 0);
lean_dec(v_unused_3554_);
v___x_3548_ = v___x_3546_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_dec(v___x_3546_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v_a_3541_);
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3541_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
else
{
lean_object* v_a_3555_; lean_object* v___x_3557_; uint8_t v_isShared_3558_; uint8_t v_isSharedCheck_3562_; 
lean_dec(v_a_3541_);
v_a_3555_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3557_ = v___x_3546_;
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
else
{
lean_inc(v_a_3555_);
lean_dec(v___x_3546_);
v___x_3557_ = lean_box(0);
v_isShared_3558_ = v_isSharedCheck_3562_;
goto v_resetjp_3556_;
}
v_resetjp_3556_:
{
lean_object* v___x_3560_; 
lean_inc(v_a_3555_);
if (v_isShared_3558_ == 0)
{
v___x_3560_ = v___x_3557_;
goto v_reusejp_3559_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_a_3555_);
v___x_3560_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3559_;
}
v_reusejp_3559_:
{
v___y_3424_ = v___x_3560_;
v_a_3425_ = v_a_3555_;
goto v___jp_3423_;
}
}
}
}
}
else
{
lean_object* v_a_3563_; 
v_a_3563_ = lean_ctor_get(v___x_3540_, 0);
lean_inc(v_a_3563_);
v___y_3424_ = v___x_3540_;
v_a_3425_ = v_a_3563_;
goto v___jp_3423_;
}
}
else
{
goto v___jp_3513_;
}
}
else
{
goto v___jp_3513_;
}
v___jp_3397_:
{
if (v___y_3400_ == 0)
{
lean_object* v___x_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
lean_dec_ref(v___y_3398_);
v___x_3401_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3402_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3403_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3395_, v_options_3392_, v___x_3402_);
if (v___x_3403_ == 0)
{
lean_object* v___x_3404_; 
v___x_3404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3404_, 0, v___y_3399_);
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; lean_object* v___x_3406_; 
lean_inc_ref(v___y_3399_);
v___x_3405_ = l_Lean_Exception_toMessageData(v___y_3399_);
v___x_3406_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3401_, v___x_3405_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3413_; 
v_isSharedCheck_3413_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3413_ == 0)
{
lean_object* v_unused_3414_; 
v_unused_3414_ = lean_ctor_get(v___x_3406_, 0);
lean_dec(v_unused_3414_);
v___x_3408_ = v___x_3406_;
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
else
{
lean_dec(v___x_3406_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3413_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3411_; 
if (v_isShared_3409_ == 0)
{
lean_ctor_set_tag(v___x_3408_, 1);
lean_ctor_set(v___x_3408_, 0, v___y_3399_);
v___x_3411_ = v___x_3408_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3412_; 
v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3412_, 0, v___y_3399_);
v___x_3411_ = v_reuseFailAlloc_3412_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
return v___x_3411_;
}
}
}
else
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
lean_dec_ref(v___y_3399_);
v_a_3415_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3406_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3406_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3399_);
return v___y_3398_;
}
}
v___jp_3423_:
{
uint8_t v___x_3426_; 
v___x_3426_ = l_Lean_Exception_isInterrupt(v_a_3425_);
if (v___x_3426_ == 0)
{
uint8_t v___x_3427_; 
lean_inc_ref(v_a_3425_);
v___x_3427_ = l_Lean_Exception_isRuntime(v_a_3425_);
v___y_3398_ = v___y_3424_;
v___y_3399_ = v_a_3425_;
v___y_3400_ = v___x_3427_;
goto v___jp_3397_;
}
else
{
v___y_3398_ = v___y_3424_;
v___y_3399_ = v_a_3425_;
v___y_3400_ = v___x_3426_;
goto v___jp_3397_;
}
}
v___jp_3432_:
{
lean_object* v___x_3436_; double v___x_3437_; double v___x_3438_; double v___x_3439_; double v___x_3440_; double v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; 
v___x_3436_ = lean_io_mono_nanos_now();
v___x_3437_ = lean_float_of_nat(v___y_3434_);
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
v___x_3446_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3428_, v_hasTrace_3393_, v___x_3429_, v_options_3392_, v___x_3431_, v___y_3433_, v___f_3396_, v___x_3445_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
return v___x_3446_;
}
v___jp_3447_:
{
lean_object* v___x_3451_; 
v___x_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3451_, 0, v_a_3450_);
v___y_3433_ = v___y_3449_;
v___y_3434_ = v___y_3448_;
v_a_3435_ = v___x_3451_;
goto v___jp_3432_;
}
v___jp_3452_:
{
if (v___y_3456_ == 0)
{
lean_object* v___x_3457_; lean_object* v___x_3458_; uint8_t v___x_3459_; 
v___x_3457_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3458_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3459_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3395_, v_options_3392_, v___x_3458_);
if (v___x_3459_ == 0)
{
v___y_3448_ = v___y_3455_;
v___y_3449_ = v___y_3454_;
v_a_3450_ = v___y_3453_;
goto v___jp_3447_;
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
lean_inc_ref(v___y_3453_);
v___x_3460_ = l_Lean_Exception_toMessageData(v___y_3453_);
v___x_3461_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3457_, v___x_3460_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_dec_ref_known(v___x_3461_, 1);
v___y_3448_ = v___y_3455_;
v___y_3449_ = v___y_3454_;
v_a_3450_ = v___y_3453_;
goto v___jp_3447_;
}
else
{
lean_object* v_a_3462_; 
lean_dec_ref(v___y_3453_);
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___y_3448_ = v___y_3455_;
v___y_3449_ = v___y_3454_;
v_a_3450_ = v_a_3462_;
goto v___jp_3447_;
}
}
}
else
{
v___y_3448_ = v___y_3455_;
v___y_3449_ = v___y_3454_;
v_a_3450_ = v___y_3453_;
goto v___jp_3447_;
}
}
v___jp_3463_:
{
uint8_t v___x_3467_; 
v___x_3467_ = l_Lean_Exception_isInterrupt(v_a_3466_);
if (v___x_3467_ == 0)
{
uint8_t v___x_3468_; 
lean_inc_ref(v_a_3466_);
v___x_3468_ = l_Lean_Exception_isRuntime(v_a_3466_);
v___y_3453_ = v_a_3466_;
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3464_;
v___y_3456_ = v___x_3468_;
goto v___jp_3452_;
}
else
{
v___y_3453_ = v_a_3466_;
v___y_3454_ = v___y_3465_;
v___y_3455_ = v___y_3464_;
v___y_3456_ = v___x_3467_;
goto v___jp_3452_;
}
}
v___jp_3469_:
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_a_3472_);
v___y_3433_ = v___y_3471_;
v___y_3434_ = v___y_3470_;
v_a_3435_ = v___x_3473_;
goto v___jp_3432_;
}
v___jp_3474_:
{
lean_object* v___x_3478_; double v___x_3479_; double v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3478_ = lean_io_get_num_heartbeats();
v___x_3479_ = lean_float_of_nat(v___y_3475_);
v___x_3480_ = lean_float_of_nat(v___x_3478_);
v___x_3481_ = lean_box_float(v___x_3479_);
v___x_3482_ = lean_box_float(v___x_3480_);
v___x_3483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3481_);
lean_ctor_set(v___x_3483_, 1, v___x_3482_);
v___x_3484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3484_, 0, v_a_3477_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3428_, v_hasTrace_3393_, v___x_3429_, v_options_3392_, v___x_3431_, v___y_3476_, v___f_3396_, v___x_3484_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
return v___x_3485_;
}
v___jp_3486_:
{
lean_object* v___x_3490_; 
v___x_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3490_, 0, v_a_3489_);
v___y_3475_ = v___y_3487_;
v___y_3476_ = v___y_3488_;
v_a_3477_ = v___x_3490_;
goto v___jp_3474_;
}
v___jp_3491_:
{
if (v___y_3495_ == 0)
{
lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3496_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3497_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3498_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3395_, v_options_3392_, v___x_3497_);
if (v___x_3498_ == 0)
{
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3494_;
v_a_3489_ = v___y_3493_;
goto v___jp_3486_;
}
else
{
lean_object* v___x_3499_; lean_object* v___x_3500_; 
lean_inc_ref(v___y_3493_);
v___x_3499_ = l_Lean_Exception_toMessageData(v___y_3493_);
v___x_3500_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3496_, v___x_3499_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_dec_ref_known(v___x_3500_, 1);
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3494_;
v_a_3489_ = v___y_3493_;
goto v___jp_3486_;
}
else
{
lean_object* v_a_3501_; 
lean_dec_ref(v___y_3493_);
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3494_;
v_a_3489_ = v_a_3501_;
goto v___jp_3486_;
}
}
}
else
{
v___y_3487_ = v___y_3492_;
v___y_3488_ = v___y_3494_;
v_a_3489_ = v___y_3493_;
goto v___jp_3486_;
}
}
v___jp_3502_:
{
uint8_t v___x_3506_; 
v___x_3506_ = l_Lean_Exception_isInterrupt(v_a_3505_);
if (v___x_3506_ == 0)
{
uint8_t v___x_3507_; 
lean_inc_ref(v_a_3505_);
v___x_3507_ = l_Lean_Exception_isRuntime(v_a_3505_);
v___y_3492_ = v___y_3503_;
v___y_3493_ = v_a_3505_;
v___y_3494_ = v___y_3504_;
v___y_3495_ = v___x_3507_;
goto v___jp_3491_;
}
else
{
v___y_3492_ = v___y_3503_;
v___y_3493_ = v_a_3505_;
v___y_3494_ = v___y_3504_;
v___y_3495_ = v___x_3506_;
goto v___jp_3491_;
}
}
v___jp_3508_:
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3512_, 0, v_a_3511_);
v___y_3475_ = v___y_3509_;
v___y_3476_ = v___y_3510_;
v_a_3477_ = v___x_3512_;
goto v___jp_3474_;
}
v___jp_3513_:
{
lean_object* v___x_3514_; lean_object* v_a_3515_; lean_object* v___x_3516_; uint8_t v___x_3517_; 
v___x_3514_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3389_);
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref(v___x_3514_);
v___x_3516_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3517_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3392_, v___x_3516_);
if (v___x_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; 
v___x_3518_ = lean_io_mono_nanos_now();
lean_inc(v_a_3389_);
lean_inc_ref(v_a_3388_);
lean_inc(v_a_3387_);
lean_inc_ref(v_a_3386_);
v___x_3519_ = lean_apply_5(v_k_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, lean_box(0));
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
v___x_3521_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3522_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3523_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3395_, v_options_3392_, v___x_3522_);
if (v___x_3523_ == 0)
{
v___y_3470_ = v___x_3518_;
v___y_3471_ = v_a_3515_;
v_a_3472_ = v_a_3520_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3524_; lean_object* v___x_3525_; 
lean_inc(v_a_3520_);
v___x_3524_ = l_Lean_MessageData_ofExpr(v_a_3520_);
v___x_3525_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3521_, v___x_3524_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_dec_ref_known(v___x_3525_, 1);
v___y_3470_ = v___x_3518_;
v___y_3471_ = v_a_3515_;
v_a_3472_ = v_a_3520_;
goto v___jp_3469_;
}
else
{
lean_object* v_a_3526_; 
lean_dec(v_a_3520_);
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref_known(v___x_3525_, 1);
v___y_3464_ = v___x_3518_;
v___y_3465_ = v_a_3515_;
v_a_3466_ = v_a_3526_;
goto v___jp_3463_;
}
}
}
else
{
lean_object* v_a_3527_; 
v_a_3527_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3527_);
lean_dec_ref_known(v___x_3519_, 1);
v___y_3464_ = v___x_3518_;
v___y_3465_ = v_a_3515_;
v_a_3466_ = v_a_3527_;
goto v___jp_3463_;
}
}
else
{
lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3528_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3389_);
lean_inc_ref(v_a_3388_);
lean_inc(v_a_3387_);
lean_inc_ref(v_a_3386_);
v___x_3529_ = lean_apply_5(v_k_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, lean_box(0));
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; uint8_t v___x_3533_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref_known(v___x_3529_, 1);
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3532_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3533_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3395_, v_options_3392_, v___x_3532_);
if (v___x_3533_ == 0)
{
v___y_3509_ = v___x_3528_;
v___y_3510_ = v_a_3515_;
v_a_3511_ = v_a_3530_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_inc(v_a_3530_);
v___x_3534_ = l_Lean_MessageData_ofExpr(v_a_3530_);
v___x_3535_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3531_, v___x_3534_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_dec_ref_known(v___x_3535_, 1);
v___y_3509_ = v___x_3528_;
v___y_3510_ = v_a_3515_;
v_a_3511_ = v_a_3530_;
goto v___jp_3508_;
}
else
{
lean_object* v_a_3536_; 
lean_dec(v_a_3530_);
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_a_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v___y_3503_ = v___x_3528_;
v___y_3504_ = v_a_3515_;
v_a_3505_ = v_a_3536_;
goto v___jp_3502_;
}
}
}
else
{
lean_object* v_a_3537_; 
v_a_3537_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3537_);
lean_dec_ref_known(v___x_3529_, 1);
v___y_3503_ = v___x_3528_;
v___y_3504_ = v_a_3515_;
v_a_3505_ = v_a_3537_;
goto v___jp_3502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3564_, lean_object* v_xs_3565_, lean_object* v_k_3566_, lean_object* v_a_3567_, lean_object* v_a_3568_, lean_object* v_a_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_){
_start:
{
lean_object* v_res_3572_; 
v_res_3572_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3564_, v_xs_3565_, v_k_3566_, v_a_3567_, v_a_3568_, v_a_3569_, v_a_3570_);
lean_dec(v_a_3570_);
lean_dec_ref(v_a_3569_);
lean_dec(v_a_3568_);
lean_dec_ref(v_a_3567_);
return v_res_3572_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3573_, lean_object* v_xs_3574_, lean_object* v_a_3575_, lean_object* v_a_3576_, lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v___f_3580_; uint8_t v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; 
lean_inc_ref(v_xs_3574_);
lean_inc(v_constName_3573_);
v___f_3580_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3580_, 0, v_constName_3573_);
lean_closure_set(v___f_3580_, 1, v_xs_3574_);
v___x_3581_ = 0;
v___x_3582_ = lean_box(v___x_3581_);
v___x_3583_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3583_, 0, lean_box(0));
lean_closure_set(v___x_3583_, 1, v___f_3580_);
lean_closure_set(v___x_3583_, 2, v___x_3582_);
v___x_3584_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3573_, v_xs_3574_, v___x_3583_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_);
return v___x_3584_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3585_, lean_object* v_xs_3586_, lean_object* v_a_3587_, lean_object* v_a_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Meta_mkAppM(v_constName_3585_, v_xs_3586_, v_a_3587_, v_a_3588_, v_a_3589_, v_a_3590_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
lean_dec(v_a_3588_);
lean_dec_ref(v_a_3587_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v___x_3598_; 
v___x_3598_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3596_);
return v___x_3598_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3605_, lean_object* v_x_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_){
_start:
{
lean_object* v___x_3612_; 
v___x_3612_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3606_);
return v___x_3612_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3613_, lean_object* v_x_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_res_3620_; 
v_res_3620_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3613_, v_x_3614_, v___y_3615_, v___y_3616_, v___y_3617_, v___y_3618_);
lean_dec(v___y_3618_);
lean_dec_ref(v___y_3617_);
lean_dec(v___y_3616_);
lean_dec_ref(v___y_3615_);
return v_res_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3621_, lean_object* v_xs_3622_, lean_object* v_x_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3629_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3630_ = l_Lean_MessageData_ofExpr(v_f_3621_);
v___x_3631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3629_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
v___x_3632_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3633_, 0, v___x_3631_);
lean_ctor_set(v___x_3633_, 1, v___x_3632_);
v___x_3634_ = lean_array_to_list(v_xs_3622_);
v___x_3635_ = lean_box(0);
v___x_3636_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3634_, v___x_3635_);
v___x_3637_ = l_Lean_MessageData_ofList(v___x_3636_);
v___x_3638_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3633_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3640_, lean_object* v_xs_3641_, lean_object* v_x_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v_res_3648_; 
v_res_3648_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3640_, v_xs_3641_, v_x_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
lean_dec(v___y_3646_);
lean_dec_ref(v___y_3645_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec_ref(v_x_3642_);
return v_res_3648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3649_, lean_object* v_xs_3650_, lean_object* v_k_3651_, lean_object* v_a_3652_, lean_object* v_a_3653_, lean_object* v_a_3654_, lean_object* v_a_3655_){
_start:
{
lean_object* v_toCold_3657_; lean_object* v_options_3658_; uint8_t v_hasTrace_3659_; 
v_toCold_3657_ = lean_ctor_get(v_a_3654_, 0);
v_options_3658_ = lean_ctor_get(v_toCold_3657_, 2);
v_hasTrace_3659_ = lean_ctor_get_uint8(v_options_3658_, sizeof(void*)*1);
if (v_hasTrace_3659_ == 0)
{
lean_object* v___x_3660_; 
lean_dec_ref(v_xs_3650_);
lean_dec_ref(v_f_3649_);
lean_inc(v_a_3655_);
lean_inc_ref(v_a_3654_);
lean_inc(v_a_3653_);
lean_inc_ref(v_a_3652_);
v___x_3660_ = lean_apply_5(v_k_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, lean_box(0));
return v___x_3660_;
}
else
{
lean_object* v_inheritedTraceOptions_3661_; lean_object* v___f_3662_; lean_object* v___y_3664_; lean_object* v___y_3665_; uint8_t v___y_3666_; lean_object* v___y_3690_; lean_object* v_a_3691_; lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; uint8_t v___x_3697_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_a_3701_; lean_object* v___y_3714_; lean_object* v___y_3715_; lean_object* v_a_3716_; lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v___y_3721_; uint8_t v___y_3722_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v_a_3732_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v_a_3738_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v_a_3743_; lean_object* v___y_3753_; lean_object* v___y_3754_; lean_object* v_a_3755_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v___y_3760_; uint8_t v___y_3761_; lean_object* v___y_3769_; lean_object* v___y_3770_; lean_object* v_a_3771_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v_a_3777_; 
v_inheritedTraceOptions_3661_ = lean_ctor_get(v_toCold_3657_, 11);
v___f_3662_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3662_, 0, v_f_3649_);
lean_closure_set(v___f_3662_, 1, v_xs_3650_);
v___x_3694_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3695_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3696_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3697_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3661_, v_options_3658_, v___x_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3804_; uint8_t v___x_3805_; 
v___x_3804_ = l_Lean_trace_profiler;
v___x_3805_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3658_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; 
lean_dec_ref(v___f_3662_);
lean_inc(v_a_3655_);
lean_inc_ref(v_a_3654_);
lean_inc(v_a_3653_);
lean_inc_ref(v_a_3652_);
v___x_3806_ = lean_apply_5(v_k_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, lean_box(0));
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; uint8_t v___x_3810_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
v___x_3808_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3809_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3810_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3661_, v_options_3658_, v___x_3809_);
if (v___x_3810_ == 0)
{
lean_dec(v_a_3807_);
return v___x_3806_;
}
else
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
lean_dec_ref_known(v___x_3806_, 1);
lean_inc(v_a_3807_);
v___x_3811_ = l_Lean_MessageData_ofExpr(v_a_3807_);
v___x_3812_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3808_, v___x_3811_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3819_ == 0)
{
lean_object* v_unused_3820_; 
v_unused_3820_ = lean_ctor_get(v___x_3812_, 0);
lean_dec(v_unused_3820_);
v___x_3814_ = v___x_3812_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_dec(v___x_3812_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 0, v_a_3807_);
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3807_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec(v_a_3807_);
v_a_3821_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3812_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3812_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
lean_inc(v_a_3821_);
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
v___y_3690_ = v___x_3826_;
v_a_3691_ = v_a_3821_;
goto v___jp_3689_;
}
}
}
}
}
else
{
lean_object* v_a_3829_; 
v_a_3829_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3829_);
v___y_3690_ = v___x_3806_;
v_a_3691_ = v_a_3829_;
goto v___jp_3689_;
}
}
else
{
goto v___jp_3779_;
}
}
else
{
goto v___jp_3779_;
}
v___jp_3663_:
{
if (v___y_3666_ == 0)
{
lean_object* v___x_3667_; lean_object* v___x_3668_; uint8_t v___x_3669_; 
lean_dec_ref(v___y_3665_);
v___x_3667_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3668_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3669_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3661_, v_options_3658_, v___x_3668_);
if (v___x_3669_ == 0)
{
lean_object* v___x_3670_; 
v___x_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3670_, 0, v___y_3664_);
return v___x_3670_;
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3672_; 
lean_inc_ref(v___y_3664_);
v___x_3671_ = l_Lean_Exception_toMessageData(v___y_3664_);
v___x_3672_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3667_, v___x_3671_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3679_ == 0)
{
lean_object* v_unused_3680_; 
v_unused_3680_ = lean_ctor_get(v___x_3672_, 0);
lean_dec(v_unused_3680_);
v___x_3674_ = v___x_3672_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_dec(v___x_3672_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
lean_ctor_set_tag(v___x_3674_, 1);
lean_ctor_set(v___x_3674_, 0, v___y_3664_);
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___y_3664_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_dec_ref(v___y_3664_);
v_a_3681_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3672_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3672_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3664_);
return v___y_3665_;
}
}
v___jp_3689_:
{
uint8_t v___x_3692_; 
v___x_3692_ = l_Lean_Exception_isInterrupt(v_a_3691_);
if (v___x_3692_ == 0)
{
uint8_t v___x_3693_; 
lean_inc_ref(v_a_3691_);
v___x_3693_ = l_Lean_Exception_isRuntime(v_a_3691_);
v___y_3664_ = v_a_3691_;
v___y_3665_ = v___y_3690_;
v___y_3666_ = v___x_3693_;
goto v___jp_3663_;
}
else
{
v___y_3664_ = v_a_3691_;
v___y_3665_ = v___y_3690_;
v___y_3666_ = v___x_3692_;
goto v___jp_3663_;
}
}
v___jp_3698_:
{
lean_object* v___x_3702_; double v___x_3703_; double v___x_3704_; double v___x_3705_; double v___x_3706_; double v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3702_ = lean_io_mono_nanos_now();
v___x_3703_ = lean_float_of_nat(v___y_3699_);
v___x_3704_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3705_ = lean_float_div(v___x_3703_, v___x_3704_);
v___x_3706_ = lean_float_of_nat(v___x_3702_);
v___x_3707_ = lean_float_div(v___x_3706_, v___x_3704_);
v___x_3708_ = lean_box_float(v___x_3705_);
v___x_3709_ = lean_box_float(v___x_3707_);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3708_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3711_, 0, v_a_3701_);
lean_ctor_set(v___x_3711_, 1, v___x_3710_);
v___x_3712_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3694_, v_hasTrace_3659_, v___x_3695_, v_options_3658_, v___x_3697_, v___y_3700_, v___f_3662_, v___x_3711_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
return v___x_3712_;
}
v___jp_3713_:
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v_a_3716_);
v___y_3699_ = v___y_3714_;
v___y_3700_ = v___y_3715_;
v_a_3701_ = v___x_3717_;
goto v___jp_3698_;
}
v___jp_3718_:
{
if (v___y_3722_ == 0)
{
lean_object* v___x_3723_; lean_object* v___x_3724_; uint8_t v___x_3725_; 
v___x_3723_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3724_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3661_, v_options_3658_, v___x_3724_);
if (v___x_3725_ == 0)
{
v___y_3714_ = v___y_3719_;
v___y_3715_ = v___y_3720_;
v_a_3716_ = v___y_3721_;
goto v___jp_3713_;
}
else
{
lean_object* v___x_3726_; lean_object* v___x_3727_; 
lean_inc_ref(v___y_3721_);
v___x_3726_ = l_Lean_Exception_toMessageData(v___y_3721_);
v___x_3727_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3723_, v___x_3726_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3727_) == 0)
{
lean_dec_ref_known(v___x_3727_, 1);
v___y_3714_ = v___y_3719_;
v___y_3715_ = v___y_3720_;
v_a_3716_ = v___y_3721_;
goto v___jp_3713_;
}
else
{
lean_object* v_a_3728_; 
lean_dec_ref(v___y_3721_);
v_a_3728_ = lean_ctor_get(v___x_3727_, 0);
lean_inc(v_a_3728_);
lean_dec_ref_known(v___x_3727_, 1);
v___y_3714_ = v___y_3719_;
v___y_3715_ = v___y_3720_;
v_a_3716_ = v_a_3728_;
goto v___jp_3713_;
}
}
}
else
{
v___y_3714_ = v___y_3719_;
v___y_3715_ = v___y_3720_;
v_a_3716_ = v___y_3721_;
goto v___jp_3713_;
}
}
v___jp_3729_:
{
uint8_t v___x_3733_; 
v___x_3733_ = l_Lean_Exception_isInterrupt(v_a_3732_);
if (v___x_3733_ == 0)
{
uint8_t v___x_3734_; 
lean_inc_ref(v_a_3732_);
v___x_3734_ = l_Lean_Exception_isRuntime(v_a_3732_);
v___y_3719_ = v___y_3730_;
v___y_3720_ = v___y_3731_;
v___y_3721_ = v_a_3732_;
v___y_3722_ = v___x_3734_;
goto v___jp_3718_;
}
else
{
v___y_3719_ = v___y_3730_;
v___y_3720_ = v___y_3731_;
v___y_3721_ = v_a_3732_;
v___y_3722_ = v___x_3733_;
goto v___jp_3718_;
}
}
v___jp_3735_:
{
lean_object* v___x_3739_; 
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v_a_3738_);
v___y_3699_ = v___y_3736_;
v___y_3700_ = v___y_3737_;
v_a_3701_ = v___x_3739_;
goto v___jp_3698_;
}
v___jp_3740_:
{
lean_object* v___x_3744_; double v___x_3745_; double v___x_3746_; lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
v___x_3744_ = lean_io_get_num_heartbeats();
v___x_3745_ = lean_float_of_nat(v___y_3742_);
v___x_3746_ = lean_float_of_nat(v___x_3744_);
v___x_3747_ = lean_box_float(v___x_3745_);
v___x_3748_ = lean_box_float(v___x_3746_);
v___x_3749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3747_);
lean_ctor_set(v___x_3749_, 1, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v_a_3743_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3694_, v_hasTrace_3659_, v___x_3695_, v_options_3658_, v___x_3697_, v___y_3741_, v___f_3662_, v___x_3750_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
return v___x_3751_;
}
v___jp_3752_:
{
lean_object* v___x_3756_; 
v___x_3756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3756_, 0, v_a_3755_);
v___y_3741_ = v___y_3753_;
v___y_3742_ = v___y_3754_;
v_a_3743_ = v___x_3756_;
goto v___jp_3740_;
}
v___jp_3757_:
{
if (v___y_3761_ == 0)
{
lean_object* v___x_3762_; lean_object* v___x_3763_; uint8_t v___x_3764_; 
v___x_3762_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3763_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3764_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3661_, v_options_3658_, v___x_3763_);
if (v___x_3764_ == 0)
{
v___y_3753_ = v___y_3758_;
v___y_3754_ = v___y_3760_;
v_a_3755_ = v___y_3759_;
goto v___jp_3752_;
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3766_; 
lean_inc_ref(v___y_3759_);
v___x_3765_ = l_Lean_Exception_toMessageData(v___y_3759_);
v___x_3766_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3762_, v___x_3765_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_dec_ref_known(v___x_3766_, 1);
v___y_3753_ = v___y_3758_;
v___y_3754_ = v___y_3760_;
v_a_3755_ = v___y_3759_;
goto v___jp_3752_;
}
else
{
lean_object* v_a_3767_; 
lean_dec_ref(v___y_3759_);
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
lean_inc(v_a_3767_);
lean_dec_ref_known(v___x_3766_, 1);
v___y_3753_ = v___y_3758_;
v___y_3754_ = v___y_3760_;
v_a_3755_ = v_a_3767_;
goto v___jp_3752_;
}
}
}
else
{
v___y_3753_ = v___y_3758_;
v___y_3754_ = v___y_3760_;
v_a_3755_ = v___y_3759_;
goto v___jp_3752_;
}
}
v___jp_3768_:
{
uint8_t v___x_3772_; 
v___x_3772_ = l_Lean_Exception_isInterrupt(v_a_3771_);
if (v___x_3772_ == 0)
{
uint8_t v___x_3773_; 
lean_inc_ref(v_a_3771_);
v___x_3773_ = l_Lean_Exception_isRuntime(v_a_3771_);
v___y_3758_ = v___y_3769_;
v___y_3759_ = v_a_3771_;
v___y_3760_ = v___y_3770_;
v___y_3761_ = v___x_3773_;
goto v___jp_3757_;
}
else
{
v___y_3758_ = v___y_3769_;
v___y_3759_ = v_a_3771_;
v___y_3760_ = v___y_3770_;
v___y_3761_ = v___x_3772_;
goto v___jp_3757_;
}
}
v___jp_3774_:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3778_, 0, v_a_3777_);
v___y_3741_ = v___y_3775_;
v___y_3742_ = v___y_3776_;
v_a_3743_ = v___x_3778_;
goto v___jp_3740_;
}
v___jp_3779_:
{
lean_object* v___x_3780_; lean_object* v_a_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3780_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3655_);
v_a_3781_ = lean_ctor_get(v___x_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref(v___x_3780_);
v___x_3782_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3783_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3658_, v___x_3782_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3785_; 
v___x_3784_ = lean_io_mono_nanos_now();
lean_inc(v_a_3655_);
lean_inc_ref(v_a_3654_);
lean_inc(v_a_3653_);
lean_inc_ref(v_a_3652_);
v___x_3785_ = lean_apply_5(v_k_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, lean_box(0));
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3787_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3788_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3661_, v_options_3658_, v___x_3788_);
if (v___x_3789_ == 0)
{
v___y_3736_ = v___x_3784_;
v___y_3737_ = v_a_3781_;
v_a_3738_ = v_a_3786_;
goto v___jp_3735_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
lean_inc(v_a_3786_);
v___x_3790_ = l_Lean_MessageData_ofExpr(v_a_3786_);
v___x_3791_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3787_, v___x_3790_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_dec_ref_known(v___x_3791_, 1);
v___y_3736_ = v___x_3784_;
v___y_3737_ = v_a_3781_;
v_a_3738_ = v_a_3786_;
goto v___jp_3735_;
}
else
{
lean_object* v_a_3792_; 
lean_dec(v_a_3786_);
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___y_3730_ = v___x_3784_;
v___y_3731_ = v_a_3781_;
v_a_3732_ = v_a_3792_;
goto v___jp_3729_;
}
}
}
else
{
lean_object* v_a_3793_; 
v_a_3793_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3793_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3730_ = v___x_3784_;
v___y_3731_ = v_a_3781_;
v_a_3732_ = v_a_3793_;
goto v___jp_3729_;
}
}
else
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3655_);
lean_inc_ref(v_a_3654_);
lean_inc(v_a_3653_);
lean_inc_ref(v_a_3652_);
v___x_3795_ = lean_apply_5(v_k_3651_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_, lean_box(0));
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; uint8_t v___x_3799_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
v___x_3797_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3798_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3799_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3661_, v_options_3658_, v___x_3798_);
if (v___x_3799_ == 0)
{
v___y_3775_ = v_a_3781_;
v___y_3776_ = v___x_3794_;
v_a_3777_ = v_a_3796_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3800_; lean_object* v___x_3801_; 
lean_inc(v_a_3796_);
v___x_3800_ = l_Lean_MessageData_ofExpr(v_a_3796_);
v___x_3801_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3797_, v___x_3800_, v_a_3652_, v_a_3653_, v_a_3654_, v_a_3655_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_dec_ref_known(v___x_3801_, 1);
v___y_3775_ = v_a_3781_;
v___y_3776_ = v___x_3794_;
v_a_3777_ = v_a_3796_;
goto v___jp_3774_;
}
else
{
lean_object* v_a_3802_; 
lean_dec(v_a_3796_);
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___y_3769_ = v_a_3781_;
v___y_3770_ = v___x_3794_;
v_a_3771_ = v_a_3802_;
goto v___jp_3768_;
}
}
}
else
{
lean_object* v_a_3803_; 
v_a_3803_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3795_, 1);
v___y_3769_ = v_a_3781_;
v___y_3770_ = v___x_3794_;
v_a_3771_ = v_a_3803_;
goto v___jp_3768_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3830_, lean_object* v_xs_3831_, lean_object* v_k_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3830_, v_xs_3831_, v_k_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_a_3836_);
lean_dec_ref(v_a_3835_);
lean_dec(v_a_3834_);
lean_dec_ref(v_a_3833_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3839_, lean_object* v_xs_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3846_; 
lean_inc(v_a_3844_);
lean_inc_ref(v_a_3843_);
lean_inc(v_a_3842_);
lean_inc_ref(v_a_3841_);
lean_inc_ref(v_f_3839_);
v___x_3846_ = lean_infer_type(v_f_3839_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
lean_inc_ref(v_xs_3840_);
lean_inc_ref(v_f_3839_);
v___x_3848_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3848_, 0, v_f_3839_);
lean_closure_set(v___x_3848_, 1, v_a_3847_);
lean_closure_set(v___x_3848_, 2, v_xs_3840_);
v___x_3849_ = 0;
v___x_3850_ = lean_box(v___x_3849_);
v___x_3851_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3851_, 0, lean_box(0));
lean_closure_set(v___x_3851_, 1, v___x_3848_);
lean_closure_set(v___x_3851_, 2, v___x_3850_);
v___x_3852_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3839_, v_xs_3840_, v___x_3851_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
return v___x_3852_;
}
else
{
lean_dec_ref(v_xs_3840_);
lean_dec_ref(v_f_3839_);
return v___x_3846_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3853_, lean_object* v_xs_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l_Lean_Meta_mkAppM_x27(v_f_3853_, v_xs_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3861_, size_t v_i_3862_, size_t v_stop_3863_, lean_object* v_b_3864_){
_start:
{
lean_object* v___y_3866_; uint8_t v___x_3870_; 
v___x_3870_ = lean_usize_dec_eq(v_i_3862_, v_stop_3863_);
if (v___x_3870_ == 0)
{
lean_object* v___x_3871_; 
v___x_3871_ = lean_array_uget_borrowed(v_as_3861_, v_i_3862_);
if (lean_obj_tag(v___x_3871_) == 0)
{
v___y_3866_ = v_b_3864_;
goto v___jp_3865_;
}
else
{
lean_object* v_val_3872_; lean_object* v___x_3873_; 
v_val_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_val_3872_);
v___x_3873_ = lean_array_push(v_b_3864_, v_val_3872_);
v___y_3866_ = v___x_3873_;
goto v___jp_3865_;
}
}
else
{
return v_b_3864_;
}
v___jp_3865_:
{
size_t v___x_3867_; size_t v___x_3868_; 
v___x_3867_ = ((size_t)1ULL);
v___x_3868_ = lean_usize_add(v_i_3862_, v___x_3867_);
v_i_3862_ = v___x_3868_;
v_b_3864_ = v___y_3866_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3874_, lean_object* v_i_3875_, lean_object* v_stop_3876_, lean_object* v_b_3877_){
_start:
{
size_t v_i_boxed_3878_; size_t v_stop_boxed_3879_; lean_object* v_res_3880_; 
v_i_boxed_3878_ = lean_unbox_usize(v_i_3875_);
lean_dec(v_i_3875_);
v_stop_boxed_3879_ = lean_unbox_usize(v_stop_3876_);
lean_dec(v_stop_3876_);
v_res_3880_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3874_, v_i_boxed_3878_, v_stop_boxed_3879_, v_b_3877_);
lean_dec_ref(v_as_3874_);
return v_res_3880_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3888_ = l_Lean_MessageData_ofFormat(v___x_3887_);
return v___x_3888_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = lean_box(1);
v___x_3890_ = l_Lean_MessageData_ofFormat(v___x_3889_);
return v___x_3890_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3894_; lean_object* v___x_3895_; 
v___x_3894_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3895_ = l_Lean_MessageData_ofFormat(v___x_3894_);
return v___x_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3896_, lean_object* v_xs_3897_, lean_object* v_x_3898_, lean_object* v_x_3899_, lean_object* v_x_3900_, lean_object* v_x_3901_, lean_object* v_x_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_){
_start:
{
if (lean_obj_tag(v_x_3902_) == 7)
{
lean_object* v_binderName_3908_; lean_object* v_binderType_3909_; lean_object* v_body_3910_; uint8_t v_binderInfo_3911_; lean_object* v___x_3912_; uint8_t v___x_3913_; 
v_binderName_3908_ = lean_ctor_get(v_x_3902_, 0);
lean_inc(v_binderName_3908_);
v_binderType_3909_ = lean_ctor_get(v_x_3902_, 1);
lean_inc_ref(v_binderType_3909_);
v_body_3910_ = lean_ctor_get(v_x_3902_, 2);
lean_inc_ref(v_body_3910_);
v_binderInfo_3911_ = lean_ctor_get_uint8(v_x_3902_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3902_, 3);
v___x_3912_ = lean_array_get_size(v_xs_3897_);
v___x_3913_ = lean_nat_dec_lt(v_x_3898_, v___x_3912_);
if (v___x_3913_ == 0)
{
lean_object* v___x_3914_; lean_object* v___x_3915_; 
lean_dec_ref(v_body_3910_);
lean_dec_ref(v_binderType_3909_);
lean_dec(v_binderName_3908_);
lean_dec(v_x_3900_);
lean_dec(v_x_3898_);
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3915_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3914_, v_f_3896_, v_x_3899_, v_x_3901_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
lean_dec_ref(v_x_3901_);
lean_dec_ref(v_x_3899_);
return v___x_3915_;
}
else
{
lean_object* v___x_3916_; lean_object* v_d_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_array_get_size(v_x_3899_);
v_d_3917_ = lean_expr_instantiate_rev_range(v_binderType_3909_, v_x_3900_, v___x_3916_, v_x_3899_);
lean_dec_ref(v_binderType_3909_);
v___x_3918_ = lean_array_fget_borrowed(v_xs_3897_, v_x_3898_);
if (lean_obj_tag(v___x_3918_) == 0)
{
if (v_binderInfo_3911_ == 3)
{
lean_object* v___x_3919_; uint8_t v___x_3920_; lean_object* v___x_3921_; 
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v_d_3917_);
v___x_3920_ = 1;
v___x_3921_ = l_Lean_Meta_mkFreshExprMVar(v___x_3919_, v___x_3920_, v_binderName_3908_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc_n(v_a_3922_, 2);
lean_dec_ref_known(v___x_3921_, 1);
v___x_3923_ = lean_unsigned_to_nat(1u);
v___x_3924_ = lean_nat_add(v_x_3898_, v___x_3923_);
lean_dec(v_x_3898_);
v___x_3925_ = lean_array_push(v_x_3899_, v_a_3922_);
v___x_3926_ = l_Lean_Expr_mvarId_x21(v_a_3922_);
lean_dec(v_a_3922_);
v___x_3927_ = lean_array_push(v_x_3901_, v___x_3926_);
v_x_3898_ = v___x_3924_;
v_x_3899_ = v___x_3925_;
v_x_3901_ = v___x_3927_;
v_x_3902_ = v_body_3910_;
goto _start;
}
else
{
lean_dec_ref(v_body_3910_);
lean_dec_ref(v_x_3901_);
lean_dec(v_x_3900_);
lean_dec_ref(v_x_3899_);
lean_dec(v_x_3898_);
lean_dec_ref(v_f_3896_);
return v___x_3921_;
}
}
else
{
lean_object* v___x_3929_; uint8_t v___x_3930_; lean_object* v___x_3931_; 
v___x_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3929_, 0, v_d_3917_);
v___x_3930_ = 0;
v___x_3931_ = l_Lean_Meta_mkFreshExprMVar(v___x_3929_, v___x_3930_, v_binderName_3908_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
if (lean_obj_tag(v___x_3931_) == 0)
{
lean_object* v_a_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; 
v_a_3932_ = lean_ctor_get(v___x_3931_, 0);
lean_inc(v_a_3932_);
lean_dec_ref_known(v___x_3931_, 1);
v___x_3933_ = lean_unsigned_to_nat(1u);
v___x_3934_ = lean_nat_add(v_x_3898_, v___x_3933_);
lean_dec(v_x_3898_);
v___x_3935_ = lean_array_push(v_x_3899_, v_a_3932_);
v_x_3898_ = v___x_3934_;
v_x_3899_ = v___x_3935_;
v_x_3902_ = v_body_3910_;
goto _start;
}
else
{
lean_dec_ref(v_body_3910_);
lean_dec_ref(v_x_3901_);
lean_dec(v_x_3900_);
lean_dec_ref(v_x_3899_);
lean_dec(v_x_3898_);
lean_dec_ref(v_f_3896_);
return v___x_3931_;
}
}
}
else
{
lean_object* v_val_3937_; lean_object* v___x_3938_; 
lean_dec(v_binderName_3908_);
v_val_3937_ = lean_ctor_get(v___x_3918_, 0);
lean_inc(v_a_3906_);
lean_inc_ref(v_a_3905_);
lean_inc(v_a_3904_);
lean_inc_ref(v_a_3903_);
lean_inc(v_val_3937_);
v___x_3938_ = lean_infer_type(v_val_3937_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3940_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc(v_a_3939_);
lean_dec_ref_known(v___x_3938_, 1);
v___x_3940_ = l_Lean_Meta_isExprDefEq(v_d_3917_, v_a_3939_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
if (lean_obj_tag(v___x_3940_) == 0)
{
lean_object* v_a_3941_; uint8_t v___x_3942_; 
v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3941_);
lean_dec_ref_known(v___x_3940_, 1);
v___x_3942_ = lean_unbox(v_a_3941_);
lean_dec(v_a_3941_);
if (v___x_3942_ == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; 
lean_dec_ref(v_body_3910_);
lean_dec_ref(v_x_3901_);
lean_dec(v_x_3900_);
lean_dec(v_x_3898_);
v___x_3943_ = l_Lean_mkAppN(v_f_3896_, v_x_3899_);
lean_dec_ref(v_x_3899_);
lean_inc(v_val_3937_);
v___x_3944_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3943_, v_val_3937_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
return v___x_3944_;
}
else
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3945_ = lean_unsigned_to_nat(1u);
v___x_3946_ = lean_nat_add(v_x_3898_, v___x_3945_);
lean_dec(v_x_3898_);
lean_inc(v_val_3937_);
v___x_3947_ = lean_array_push(v_x_3899_, v_val_3937_);
v_x_3898_ = v___x_3946_;
v_x_3899_ = v___x_3947_;
v_x_3902_ = v_body_3910_;
goto _start;
}
}
else
{
lean_object* v_a_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3956_; 
lean_dec_ref(v_body_3910_);
lean_dec_ref(v_x_3901_);
lean_dec(v_x_3900_);
lean_dec_ref(v_x_3899_);
lean_dec(v_x_3898_);
lean_dec_ref(v_f_3896_);
v_a_3949_ = lean_ctor_get(v___x_3940_, 0);
v_isSharedCheck_3956_ = !lean_is_exclusive(v___x_3940_);
if (v_isSharedCheck_3956_ == 0)
{
v___x_3951_ = v___x_3940_;
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_a_3949_);
lean_dec(v___x_3940_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3956_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3954_; 
if (v_isShared_3952_ == 0)
{
v___x_3954_ = v___x_3951_;
goto v_reusejp_3953_;
}
else
{
lean_object* v_reuseFailAlloc_3955_; 
v_reuseFailAlloc_3955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3955_, 0, v_a_3949_);
v___x_3954_ = v_reuseFailAlloc_3955_;
goto v_reusejp_3953_;
}
v_reusejp_3953_:
{
return v___x_3954_;
}
}
}
}
else
{
lean_dec_ref(v_d_3917_);
lean_dec_ref(v_body_3910_);
lean_dec_ref(v_x_3901_);
lean_dec(v_x_3900_);
lean_dec_ref(v_x_3899_);
lean_dec(v_x_3898_);
lean_dec_ref(v_f_3896_);
return v___x_3938_;
}
}
}
}
else
{
lean_object* v___x_3957_; lean_object* v_type_3958_; lean_object* v___x_3959_; 
v___x_3957_ = lean_array_get_size(v_x_3899_);
v_type_3958_ = lean_expr_instantiate_rev_range(v_x_3902_, v_x_3900_, v___x_3957_, v_x_3899_);
lean_dec(v_x_3900_);
lean_dec_ref(v_x_3902_);
v___x_3959_ = l_Lean_Meta_whnfD(v_type_3958_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
if (lean_obj_tag(v___x_3959_) == 0)
{
lean_object* v_a_3960_; uint8_t v___x_3961_; 
v_a_3960_ = lean_ctor_get(v___x_3959_, 0);
lean_inc(v_a_3960_);
lean_dec_ref_known(v___x_3959_, 1);
v___x_3961_ = l_Lean_Expr_isForall(v_a_3960_);
if (v___x_3961_ == 0)
{
lean_object* v___x_3962_; uint8_t v___x_3963_; 
lean_dec(v_a_3960_);
v___x_3962_ = lean_array_get_size(v_xs_3897_);
v___x_3963_ = lean_nat_dec_eq(v_x_3898_, v___x_3962_);
lean_dec(v_x_3898_);
if (v___x_3963_ == 0)
{
lean_object* v___x_3964_; lean_object* v___y_3966_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
lean_dec_ref(v_x_3901_);
lean_dec_ref(v_x_3899_);
v___x_3964_ = lean_unsigned_to_nat(0u);
v___x_3979_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_3980_ = lean_nat_dec_lt(v___x_3964_, v___x_3962_);
if (v___x_3980_ == 0)
{
v___y_3966_ = v___x_3979_;
goto v___jp_3965_;
}
else
{
uint8_t v___x_3981_; 
v___x_3981_ = lean_nat_dec_le(v___x_3962_, v___x_3962_);
if (v___x_3981_ == 0)
{
if (v___x_3980_ == 0)
{
v___y_3966_ = v___x_3979_;
goto v___jp_3965_;
}
else
{
size_t v___x_3982_; size_t v___x_3983_; lean_object* v___x_3984_; 
v___x_3982_ = ((size_t)0ULL);
v___x_3983_ = lean_usize_of_nat(v___x_3962_);
v___x_3984_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3897_, v___x_3982_, v___x_3983_, v___x_3979_);
v___y_3966_ = v___x_3984_;
goto v___jp_3965_;
}
}
else
{
size_t v___x_3985_; size_t v___x_3986_; lean_object* v___x_3987_; 
v___x_3985_ = ((size_t)0ULL);
v___x_3986_ = lean_usize_of_nat(v___x_3962_);
v___x_3987_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3897_, v___x_3985_, v___x_3986_, v___x_3979_);
v___y_3966_ = v___x_3987_;
goto v___jp_3965_;
}
}
v___jp_3965_:
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; 
v___x_3967_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3968_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3969_ = l_Lean_indentExpr(v_f_3896_);
v___x_3970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3968_);
lean_ctor_set(v___x_3970_, 1, v___x_3969_);
v___x_3971_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3972_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3970_);
lean_ctor_set(v___x_3972_, 1, v___x_3971_);
v___x_3973_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3972_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3976_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3966_, v___x_3964_, v___x_3975_);
lean_dec_ref(v___y_3966_);
v___x_3977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3974_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3967_, v___x_3977_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
return v___x_3978_;
}
}
else
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3989_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3988_, v_f_3896_, v_x_3899_, v_x_3901_, v_a_3903_, v_a_3904_, v_a_3905_, v_a_3906_);
lean_dec_ref(v_x_3901_);
lean_dec_ref(v_x_3899_);
return v___x_3989_;
}
}
else
{
v_x_3900_ = v___x_3957_;
v_x_3902_ = v_a_3960_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3901_);
lean_dec_ref(v_x_3899_);
lean_dec(v_x_3898_);
lean_dec_ref(v_f_3896_);
return v___x_3959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_3991_, lean_object* v_xs_3992_, lean_object* v_x_3993_, lean_object* v_x_3994_, lean_object* v_x_3995_, lean_object* v_x_3996_, lean_object* v_x_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_, lean_object* v_a_4002_){
_start:
{
lean_object* v_res_4003_; 
v_res_4003_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_3991_, v_xs_3992_, v_x_3993_, v_x_3994_, v_x_3995_, v_x_3996_, v_x_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_);
lean_dec(v_a_4001_);
lean_dec_ref(v_a_4000_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec_ref(v_xs_3992_);
return v_res_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_4004_, lean_object* v_xs_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v___x_4011_; 
v___x_4011_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_4004_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
if (lean_obj_tag(v___x_4011_) == 0)
{
lean_object* v_a_4012_; lean_object* v_fst_4013_; lean_object* v_snd_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v_a_4012_ = lean_ctor_get(v___x_4011_, 0);
lean_inc(v_a_4012_);
lean_dec_ref_known(v___x_4011_, 1);
v_fst_4013_ = lean_ctor_get(v_a_4012_, 0);
lean_inc(v_fst_4013_);
v_snd_4014_ = lean_ctor_get(v_a_4012_, 1);
lean_inc(v_snd_4014_);
lean_dec(v_a_4012_);
v___x_4015_ = lean_unsigned_to_nat(0u);
v___x_4016_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4017_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4013_, v_xs_4005_, v___x_4015_, v___x_4016_, v___x_4015_, v___x_4016_, v_snd_4014_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
return v___x_4017_;
}
else
{
lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4025_; 
v_a_4018_ = lean_ctor_get(v___x_4011_, 0);
v_isSharedCheck_4025_ = !lean_is_exclusive(v___x_4011_);
if (v_isSharedCheck_4025_ == 0)
{
v___x_4020_ = v___x_4011_;
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_dec(v___x_4011_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4025_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
lean_object* v___x_4023_; 
if (v_isShared_4021_ == 0)
{
v___x_4023_ = v___x_4020_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4024_; 
v_reuseFailAlloc_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4024_, 0, v_a_4018_);
v___x_4023_ = v_reuseFailAlloc_4024_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
return v___x_4023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4026_, lean_object* v_xs_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4026_, v_xs_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec_ref(v_xs_4027_);
return v_res_4033_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4037_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4038_ = l_Lean_MessageData_ofFormat(v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4039_, lean_object* v_a_4040_){
_start:
{
if (lean_obj_tag(v_a_4039_) == 0)
{
lean_object* v___x_4041_; 
v___x_4041_ = l_List_reverse___redArg(v_a_4040_);
return v___x_4041_;
}
else
{
lean_object* v_head_4042_; lean_object* v_tail_4043_; lean_object* v___x_4045_; uint8_t v_isShared_4046_; uint8_t v_isSharedCheck_4056_; 
v_head_4042_ = lean_ctor_get(v_a_4039_, 0);
v_tail_4043_ = lean_ctor_get(v_a_4039_, 1);
v_isSharedCheck_4056_ = !lean_is_exclusive(v_a_4039_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4045_ = v_a_4039_;
v_isShared_4046_ = v_isSharedCheck_4056_;
goto v_resetjp_4044_;
}
else
{
lean_inc(v_tail_4043_);
lean_inc(v_head_4042_);
lean_dec(v_a_4039_);
v___x_4045_ = lean_box(0);
v_isShared_4046_ = v_isSharedCheck_4056_;
goto v_resetjp_4044_;
}
v_resetjp_4044_:
{
lean_object* v___y_4048_; 
if (lean_obj_tag(v_head_4042_) == 0)
{
lean_object* v___x_4053_; 
v___x_4053_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4048_ = v___x_4053_;
goto v___jp_4047_;
}
else
{
lean_object* v_val_4054_; lean_object* v___x_4055_; 
v_val_4054_ = lean_ctor_get(v_head_4042_, 0);
lean_inc(v_val_4054_);
lean_dec_ref_known(v_head_4042_, 1);
v___x_4055_ = l_Lean_MessageData_ofExpr(v_val_4054_);
v___y_4048_ = v___x_4055_;
goto v___jp_4047_;
}
v___jp_4047_:
{
lean_object* v___x_4050_; 
if (v_isShared_4046_ == 0)
{
lean_ctor_set(v___x_4045_, 1, v_a_4040_);
lean_ctor_set(v___x_4045_, 0, v___y_4048_);
v___x_4050_ = v___x_4045_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___y_4048_);
lean_ctor_set(v_reuseFailAlloc_4052_, 1, v_a_4040_);
v___x_4050_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
v_a_4039_ = v_tail_4043_;
v_a_4040_ = v___x_4050_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4057_, lean_object* v_xs_4058_, lean_object* v_x_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4065_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4066_ = l_Lean_MessageData_ofName(v_f_4057_);
v___x_4067_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4065_);
lean_ctor_set(v___x_4067_, 1, v___x_4066_);
v___x_4068_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4069_, 0, v___x_4067_);
lean_ctor_set(v___x_4069_, 1, v___x_4068_);
v___x_4070_ = lean_array_to_list(v_xs_4058_);
v___x_4071_ = lean_box(0);
v___x_4072_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4070_, v___x_4071_);
v___x_4073_ = l_Lean_MessageData_ofList(v___x_4072_);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4069_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4075_, 0, v___x_4074_);
return v___x_4075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4076_, lean_object* v_xs_4077_, lean_object* v_x_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_){
_start:
{
lean_object* v_res_4084_; 
v_res_4084_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4076_, v_xs_4077_, v_x_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
lean_dec(v___y_4082_);
lean_dec_ref(v___y_4081_);
lean_dec(v___y_4080_);
lean_dec_ref(v___y_4079_);
lean_dec_ref(v_x_4078_);
return v_res_4084_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4085_, lean_object* v_xs_4086_, lean_object* v_k_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_){
_start:
{
lean_object* v_toCold_4093_; lean_object* v_options_4094_; uint8_t v_hasTrace_4095_; 
v_toCold_4093_ = lean_ctor_get(v_a_4090_, 0);
v_options_4094_ = lean_ctor_get(v_toCold_4093_, 2);
v_hasTrace_4095_ = lean_ctor_get_uint8(v_options_4094_, sizeof(void*)*1);
if (v_hasTrace_4095_ == 0)
{
lean_object* v___x_4096_; 
lean_dec_ref(v_xs_4086_);
lean_dec(v_f_4085_);
lean_inc(v_a_4091_);
lean_inc_ref(v_a_4090_);
lean_inc(v_a_4089_);
lean_inc_ref(v_a_4088_);
v___x_4096_ = lean_apply_5(v_k_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, lean_box(0));
return v___x_4096_;
}
else
{
lean_object* v_inheritedTraceOptions_4097_; lean_object* v___f_4098_; lean_object* v___y_4100_; lean_object* v___y_4101_; uint8_t v___y_4102_; lean_object* v___y_4126_; lean_object* v_a_4127_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v_a_4137_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v_a_4152_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; uint8_t v___y_4158_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v_a_4168_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v_a_4174_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v_a_4179_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v_a_4191_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; uint8_t v___y_4197_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v_a_4207_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v_a_4213_; 
v_inheritedTraceOptions_4097_ = lean_ctor_get(v_toCold_4093_, 11);
v___f_4098_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4098_, 0, v_f_4085_);
lean_closure_set(v___f_4098_, 1, v_xs_4086_);
v___x_4130_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4131_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4132_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4133_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4132_);
if (v___x_4133_ == 0)
{
lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4240_ = l_Lean_trace_profiler;
v___x_4241_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4094_, v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; 
lean_dec_ref(v___f_4098_);
lean_inc(v_a_4091_);
lean_inc_ref(v_a_4090_);
lean_inc(v_a_4089_);
lean_inc_ref(v_a_4088_);
v___x_4242_ = lean_apply_5(v_k_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, lean_box(0));
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; uint8_t v___x_4246_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
v___x_4244_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4245_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4246_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4245_);
if (v___x_4246_ == 0)
{
lean_dec(v_a_4243_);
return v___x_4242_;
}
else
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
lean_dec_ref_known(v___x_4242_, 1);
lean_inc(v_a_4243_);
v___x_4247_ = l_Lean_MessageData_ofExpr(v_a_4243_);
v___x_4248_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4244_, v___x_4247_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v___x_4250_; uint8_t v_isShared_4251_; uint8_t v_isSharedCheck_4255_; 
v_isSharedCheck_4255_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4255_ == 0)
{
lean_object* v_unused_4256_; 
v_unused_4256_ = lean_ctor_get(v___x_4248_, 0);
lean_dec(v_unused_4256_);
v___x_4250_ = v___x_4248_;
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
else
{
lean_dec(v___x_4248_);
v___x_4250_ = lean_box(0);
v_isShared_4251_ = v_isSharedCheck_4255_;
goto v_resetjp_4249_;
}
v_resetjp_4249_:
{
lean_object* v___x_4253_; 
if (v_isShared_4251_ == 0)
{
lean_ctor_set(v___x_4250_, 0, v_a_4243_);
v___x_4253_ = v___x_4250_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4243_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
}
else
{
lean_object* v_a_4257_; lean_object* v___x_4259_; uint8_t v_isShared_4260_; uint8_t v_isSharedCheck_4264_; 
lean_dec(v_a_4243_);
v_a_4257_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4264_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4264_ == 0)
{
v___x_4259_ = v___x_4248_;
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
else
{
lean_inc(v_a_4257_);
lean_dec(v___x_4248_);
v___x_4259_ = lean_box(0);
v_isShared_4260_ = v_isSharedCheck_4264_;
goto v_resetjp_4258_;
}
v_resetjp_4258_:
{
lean_object* v___x_4262_; 
lean_inc(v_a_4257_);
if (v_isShared_4260_ == 0)
{
v___x_4262_ = v___x_4259_;
goto v_reusejp_4261_;
}
else
{
lean_object* v_reuseFailAlloc_4263_; 
v_reuseFailAlloc_4263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_a_4257_);
v___x_4262_ = v_reuseFailAlloc_4263_;
goto v_reusejp_4261_;
}
v_reusejp_4261_:
{
v___y_4126_ = v___x_4262_;
v_a_4127_ = v_a_4257_;
goto v___jp_4125_;
}
}
}
}
}
else
{
lean_object* v_a_4265_; 
v_a_4265_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4265_);
v___y_4126_ = v___x_4242_;
v_a_4127_ = v_a_4265_;
goto v___jp_4125_;
}
}
else
{
goto v___jp_4215_;
}
}
else
{
goto v___jp_4215_;
}
v___jp_4099_:
{
if (v___y_4102_ == 0)
{
lean_object* v___x_4103_; lean_object* v___x_4104_; uint8_t v___x_4105_; 
lean_dec_ref(v___y_4100_);
v___x_4103_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4104_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4105_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4104_);
if (v___x_4105_ == 0)
{
lean_object* v___x_4106_; 
v___x_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4106_, 0, v___y_4101_);
return v___x_4106_;
}
else
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
lean_inc_ref(v___y_4101_);
v___x_4107_ = l_Lean_Exception_toMessageData(v___y_4101_);
v___x_4108_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4103_, v___x_4107_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4115_ == 0)
{
lean_object* v_unused_4116_; 
v_unused_4116_ = lean_ctor_get(v___x_4108_, 0);
lean_dec(v_unused_4116_);
v___x_4110_ = v___x_4108_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_dec(v___x_4108_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
lean_ctor_set_tag(v___x_4110_, 1);
lean_ctor_set(v___x_4110_, 0, v___y_4101_);
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v___y_4101_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v___y_4101_);
v_a_4117_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4108_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4108_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4101_);
return v___y_4100_;
}
}
v___jp_4125_:
{
uint8_t v___x_4128_; 
v___x_4128_ = l_Lean_Exception_isInterrupt(v_a_4127_);
if (v___x_4128_ == 0)
{
uint8_t v___x_4129_; 
lean_inc_ref(v_a_4127_);
v___x_4129_ = l_Lean_Exception_isRuntime(v_a_4127_);
v___y_4100_ = v___y_4126_;
v___y_4101_ = v_a_4127_;
v___y_4102_ = v___x_4129_;
goto v___jp_4099_;
}
else
{
v___y_4100_ = v___y_4126_;
v___y_4101_ = v_a_4127_;
v___y_4102_ = v___x_4128_;
goto v___jp_4099_;
}
}
v___jp_4134_:
{
lean_object* v___x_4138_; double v___x_4139_; double v___x_4140_; double v___x_4141_; double v___x_4142_; double v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4138_ = lean_io_mono_nanos_now();
v___x_4139_ = lean_float_of_nat(v___y_4135_);
v___x_4140_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4141_ = lean_float_div(v___x_4139_, v___x_4140_);
v___x_4142_ = lean_float_of_nat(v___x_4138_);
v___x_4143_ = lean_float_div(v___x_4142_, v___x_4140_);
v___x_4144_ = lean_box_float(v___x_4141_);
v___x_4145_ = lean_box_float(v___x_4143_);
v___x_4146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v_a_4137_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4130_, v_hasTrace_4095_, v___x_4131_, v_options_4094_, v___x_4133_, v___y_4136_, v___f_4098_, v___x_4147_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
return v___x_4148_;
}
v___jp_4149_:
{
lean_object* v___x_4153_; 
v___x_4153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4153_, 0, v_a_4152_);
v___y_4135_ = v___y_4150_;
v___y_4136_ = v___y_4151_;
v_a_4137_ = v___x_4153_;
goto v___jp_4134_;
}
v___jp_4154_:
{
if (v___y_4158_ == 0)
{
lean_object* v___x_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v___x_4159_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4160_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4161_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4160_);
if (v___x_4161_ == 0)
{
v___y_4150_ = v___y_4155_;
v___y_4151_ = v___y_4157_;
v_a_4152_ = v___y_4156_;
goto v___jp_4149_;
}
else
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
lean_inc_ref(v___y_4156_);
v___x_4162_ = l_Lean_Exception_toMessageData(v___y_4156_);
v___x_4163_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4159_, v___x_4162_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4163_) == 0)
{
lean_dec_ref_known(v___x_4163_, 1);
v___y_4150_ = v___y_4155_;
v___y_4151_ = v___y_4157_;
v_a_4152_ = v___y_4156_;
goto v___jp_4149_;
}
else
{
lean_object* v_a_4164_; 
lean_dec_ref(v___y_4156_);
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
lean_inc(v_a_4164_);
lean_dec_ref_known(v___x_4163_, 1);
v___y_4150_ = v___y_4155_;
v___y_4151_ = v___y_4157_;
v_a_4152_ = v_a_4164_;
goto v___jp_4149_;
}
}
}
else
{
v___y_4150_ = v___y_4155_;
v___y_4151_ = v___y_4157_;
v_a_4152_ = v___y_4156_;
goto v___jp_4149_;
}
}
v___jp_4165_:
{
uint8_t v___x_4169_; 
v___x_4169_ = l_Lean_Exception_isInterrupt(v_a_4168_);
if (v___x_4169_ == 0)
{
uint8_t v___x_4170_; 
lean_inc_ref(v_a_4168_);
v___x_4170_ = l_Lean_Exception_isRuntime(v_a_4168_);
v___y_4155_ = v___y_4166_;
v___y_4156_ = v_a_4168_;
v___y_4157_ = v___y_4167_;
v___y_4158_ = v___x_4170_;
goto v___jp_4154_;
}
else
{
v___y_4155_ = v___y_4166_;
v___y_4156_ = v_a_4168_;
v___y_4157_ = v___y_4167_;
v___y_4158_ = v___x_4169_;
goto v___jp_4154_;
}
}
v___jp_4171_:
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v_a_4174_);
v___y_4135_ = v___y_4172_;
v___y_4136_ = v___y_4173_;
v_a_4137_ = v___x_4175_;
goto v___jp_4134_;
}
v___jp_4176_:
{
lean_object* v___x_4180_; double v___x_4181_; double v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v___x_4180_ = lean_io_get_num_heartbeats();
v___x_4181_ = lean_float_of_nat(v___y_4178_);
v___x_4182_ = lean_float_of_nat(v___x_4180_);
v___x_4183_ = lean_box_float(v___x_4181_);
v___x_4184_ = lean_box_float(v___x_4182_);
v___x_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4183_);
lean_ctor_set(v___x_4185_, 1, v___x_4184_);
v___x_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4186_, 0, v_a_4179_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
v___x_4187_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4130_, v_hasTrace_4095_, v___x_4131_, v_options_4094_, v___x_4133_, v___y_4177_, v___f_4098_, v___x_4186_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
return v___x_4187_;
}
v___jp_4188_:
{
lean_object* v___x_4192_; 
v___x_4192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4192_, 0, v_a_4191_);
v___y_4177_ = v___y_4189_;
v___y_4178_ = v___y_4190_;
v_a_4179_ = v___x_4192_;
goto v___jp_4176_;
}
v___jp_4193_:
{
if (v___y_4197_ == 0)
{
lean_object* v___x_4198_; lean_object* v___x_4199_; uint8_t v___x_4200_; 
v___x_4198_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4199_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4200_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4199_);
if (v___x_4200_ == 0)
{
v___y_4189_ = v___y_4195_;
v___y_4190_ = v___y_4196_;
v_a_4191_ = v___y_4194_;
goto v___jp_4188_;
}
else
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
lean_inc_ref(v___y_4194_);
v___x_4201_ = l_Lean_Exception_toMessageData(v___y_4194_);
v___x_4202_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4198_, v___x_4201_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_dec_ref_known(v___x_4202_, 1);
v___y_4189_ = v___y_4195_;
v___y_4190_ = v___y_4196_;
v_a_4191_ = v___y_4194_;
goto v___jp_4188_;
}
else
{
lean_object* v_a_4203_; 
lean_dec_ref(v___y_4194_);
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___y_4189_ = v___y_4195_;
v___y_4190_ = v___y_4196_;
v_a_4191_ = v_a_4203_;
goto v___jp_4188_;
}
}
}
else
{
v___y_4189_ = v___y_4195_;
v___y_4190_ = v___y_4196_;
v_a_4191_ = v___y_4194_;
goto v___jp_4188_;
}
}
v___jp_4204_:
{
uint8_t v___x_4208_; 
v___x_4208_ = l_Lean_Exception_isInterrupt(v_a_4207_);
if (v___x_4208_ == 0)
{
uint8_t v___x_4209_; 
lean_inc_ref(v_a_4207_);
v___x_4209_ = l_Lean_Exception_isRuntime(v_a_4207_);
v___y_4194_ = v_a_4207_;
v___y_4195_ = v___y_4205_;
v___y_4196_ = v___y_4206_;
v___y_4197_ = v___x_4209_;
goto v___jp_4193_;
}
else
{
v___y_4194_ = v_a_4207_;
v___y_4195_ = v___y_4205_;
v___y_4196_ = v___y_4206_;
v___y_4197_ = v___x_4208_;
goto v___jp_4193_;
}
}
v___jp_4210_:
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4214_, 0, v_a_4213_);
v___y_4177_ = v___y_4211_;
v___y_4178_ = v___y_4212_;
v_a_4179_ = v___x_4214_;
goto v___jp_4176_;
}
v___jp_4215_:
{
lean_object* v___x_4216_; lean_object* v_a_4217_; lean_object* v___x_4218_; uint8_t v___x_4219_; 
v___x_4216_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4091_);
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4216_);
v___x_4218_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4219_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4094_, v___x_4218_);
if (v___x_4219_ == 0)
{
lean_object* v___x_4220_; lean_object* v___x_4221_; 
v___x_4220_ = lean_io_mono_nanos_now();
lean_inc(v_a_4091_);
lean_inc_ref(v_a_4090_);
lean_inc(v_a_4089_);
lean_inc_ref(v_a_4088_);
v___x_4221_ = lean_apply_5(v_k_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, lean_box(0));
if (lean_obj_tag(v___x_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; 
v_a_4222_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4222_);
lean_dec_ref_known(v___x_4221_, 1);
v___x_4223_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4224_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4225_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4224_);
if (v___x_4225_ == 0)
{
v___y_4172_ = v___x_4220_;
v___y_4173_ = v_a_4217_;
v_a_4174_ = v_a_4222_;
goto v___jp_4171_;
}
else
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_inc(v_a_4222_);
v___x_4226_ = l_Lean_MessageData_ofExpr(v_a_4222_);
v___x_4227_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4223_, v___x_4226_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4227_) == 0)
{
lean_dec_ref_known(v___x_4227_, 1);
v___y_4172_ = v___x_4220_;
v___y_4173_ = v_a_4217_;
v_a_4174_ = v_a_4222_;
goto v___jp_4171_;
}
else
{
lean_object* v_a_4228_; 
lean_dec(v_a_4222_);
v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc(v_a_4228_);
lean_dec_ref_known(v___x_4227_, 1);
v___y_4166_ = v___x_4220_;
v___y_4167_ = v_a_4217_;
v_a_4168_ = v_a_4228_;
goto v___jp_4165_;
}
}
}
else
{
lean_object* v_a_4229_; 
v_a_4229_ = lean_ctor_get(v___x_4221_, 0);
lean_inc(v_a_4229_);
lean_dec_ref_known(v___x_4221_, 1);
v___y_4166_ = v___x_4220_;
v___y_4167_ = v_a_4217_;
v_a_4168_ = v_a_4229_;
goto v___jp_4165_;
}
}
else
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4091_);
lean_inc_ref(v_a_4090_);
lean_inc(v_a_4089_);
lean_inc_ref(v_a_4088_);
v___x_4231_ = lean_apply_5(v_k_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, lean_box(0));
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; uint8_t v___x_4235_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
v___x_4233_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4234_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4097_, v_options_4094_, v___x_4234_);
if (v___x_4235_ == 0)
{
v___y_4211_ = v_a_4217_;
v___y_4212_ = v___x_4230_;
v_a_4213_ = v_a_4232_;
goto v___jp_4210_;
}
else
{
lean_object* v___x_4236_; lean_object* v___x_4237_; 
lean_inc(v_a_4232_);
v___x_4236_ = l_Lean_MessageData_ofExpr(v_a_4232_);
v___x_4237_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4233_, v___x_4236_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_dec_ref_known(v___x_4237_, 1);
v___y_4211_ = v_a_4217_;
v___y_4212_ = v___x_4230_;
v_a_4213_ = v_a_4232_;
goto v___jp_4210_;
}
else
{
lean_object* v_a_4238_; 
lean_dec(v_a_4232_);
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v___y_4205_ = v_a_4217_;
v___y_4206_ = v___x_4230_;
v_a_4207_ = v_a_4238_;
goto v___jp_4204_;
}
}
}
else
{
lean_object* v_a_4239_; 
v_a_4239_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4239_);
lean_dec_ref_known(v___x_4231_, 1);
v___y_4205_ = v_a_4217_;
v___y_4206_ = v___x_4230_;
v_a_4207_ = v_a_4239_;
goto v___jp_4204_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4266_, lean_object* v_xs_4267_, lean_object* v_k_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_, lean_object* v_a_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4266_, v_xs_4267_, v_k_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec(v_a_4272_);
lean_dec_ref(v_a_4271_);
lean_dec(v_a_4270_);
lean_dec_ref(v_a_4269_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4275_, lean_object* v_xs_4276_, lean_object* v_a_4277_, lean_object* v_a_4278_, lean_object* v_a_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v___f_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
lean_inc_ref(v_xs_4276_);
lean_inc(v_constName_4275_);
v___f_4282_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4282_, 0, v_constName_4275_);
lean_closure_set(v___f_4282_, 1, v_xs_4276_);
v___x_4283_ = 0;
v___x_4284_ = lean_box(v___x_4283_);
v___x_4285_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4285_, 0, lean_box(0));
lean_closure_set(v___x_4285_, 1, v___f_4282_);
lean_closure_set(v___x_4285_, 2, v___x_4284_);
v___x_4286_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4275_, v_xs_4276_, v___x_4285_, v_a_4277_, v_a_4278_, v_a_4279_, v_a_4280_);
return v___x_4286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4287_, lean_object* v_xs_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_Meta_mkAppOptM(v_constName_4287_, v_xs_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
lean_dec(v_a_4290_);
lean_dec_ref(v_a_4289_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4295_, lean_object* v_xs_4296_, lean_object* v_x_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_){
_start:
{
lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4303_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4304_ = l_Lean_MessageData_ofExpr(v_f_4295_);
v___x_4305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4305_, 0, v___x_4303_);
lean_ctor_set(v___x_4305_, 1, v___x_4304_);
v___x_4306_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4305_);
lean_ctor_set(v___x_4307_, 1, v___x_4306_);
v___x_4308_ = lean_array_to_list(v_xs_4296_);
v___x_4309_ = lean_box(0);
v___x_4310_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4308_, v___x_4309_);
v___x_4311_ = l_Lean_MessageData_ofList(v___x_4310_);
v___x_4312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4312_, 0, v___x_4307_);
lean_ctor_set(v___x_4312_, 1, v___x_4311_);
v___x_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4312_);
return v___x_4313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4314_, lean_object* v_xs_4315_, lean_object* v_x_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_){
_start:
{
lean_object* v_res_4322_; 
v_res_4322_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4314_, v_xs_4315_, v_x_4316_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
lean_dec(v___y_4320_);
lean_dec_ref(v___y_4319_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec_ref(v_x_4316_);
return v_res_4322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4323_, lean_object* v_xs_4324_, lean_object* v_k_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_){
_start:
{
lean_object* v_toCold_4331_; lean_object* v_options_4332_; uint8_t v_hasTrace_4333_; 
v_toCold_4331_ = lean_ctor_get(v_a_4328_, 0);
v_options_4332_ = lean_ctor_get(v_toCold_4331_, 2);
v_hasTrace_4333_ = lean_ctor_get_uint8(v_options_4332_, sizeof(void*)*1);
if (v_hasTrace_4333_ == 0)
{
lean_object* v___x_4334_; 
lean_dec_ref(v_xs_4324_);
lean_dec_ref(v_f_4323_);
lean_inc(v_a_4329_);
lean_inc_ref(v_a_4328_);
lean_inc(v_a_4327_);
lean_inc_ref(v_a_4326_);
v___x_4334_ = lean_apply_5(v_k_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, lean_box(0));
return v___x_4334_;
}
else
{
lean_object* v_inheritedTraceOptions_4335_; lean_object* v___f_4336_; lean_object* v___y_4338_; lean_object* v___y_4339_; uint8_t v___y_4340_; lean_object* v___y_4364_; lean_object* v_a_4365_; lean_object* v___x_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; uint8_t v___x_4371_; lean_object* v___y_4373_; lean_object* v___y_4374_; lean_object* v_a_4375_; lean_object* v___y_4388_; lean_object* v___y_4389_; lean_object* v_a_4390_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; uint8_t v___y_4396_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v_a_4406_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v_a_4412_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v_a_4417_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v_a_4429_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4434_; uint8_t v___y_4435_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v_a_4445_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v_a_4451_; 
v_inheritedTraceOptions_4335_ = lean_ctor_get(v_toCold_4331_, 11);
v___f_4336_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4336_, 0, v_f_4323_);
lean_closure_set(v___f_4336_, 1, v_xs_4324_);
v___x_4368_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4369_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4370_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4371_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4335_, v_options_4332_, v___x_4370_);
if (v___x_4371_ == 0)
{
lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4478_ = l_Lean_trace_profiler;
v___x_4479_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4332_, v___x_4478_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; 
lean_dec_ref(v___f_4336_);
lean_inc(v_a_4329_);
lean_inc_ref(v_a_4328_);
lean_inc(v_a_4327_);
lean_inc_ref(v_a_4326_);
v___x_4480_ = lean_apply_5(v_k_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, lean_box(0));
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; uint8_t v___x_4484_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
v___x_4482_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4483_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4484_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4335_, v_options_4332_, v___x_4483_);
if (v___x_4484_ == 0)
{
lean_dec(v_a_4481_);
return v___x_4480_;
}
else
{
lean_object* v___x_4485_; lean_object* v___x_4486_; 
lean_dec_ref_known(v___x_4480_, 1);
lean_inc(v_a_4481_);
v___x_4485_ = l_Lean_MessageData_ofExpr(v_a_4481_);
v___x_4486_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4482_, v___x_4485_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4493_ == 0)
{
lean_object* v_unused_4494_; 
v_unused_4494_ = lean_ctor_get(v___x_4486_, 0);
lean_dec(v_unused_4494_);
v___x_4488_ = v___x_4486_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_dec(v___x_4486_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v_a_4481_);
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4481_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
lean_dec(v_a_4481_);
v_a_4495_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4486_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4486_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
lean_inc(v_a_4495_);
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
v___y_4364_ = v___x_4500_;
v_a_4365_ = v_a_4495_;
goto v___jp_4363_;
}
}
}
}
}
else
{
lean_object* v_a_4503_; 
v_a_4503_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4503_);
v___y_4364_ = v___x_4480_;
v_a_4365_ = v_a_4503_;
goto v___jp_4363_;
}
}
else
{
goto v___jp_4453_;
}
}
else
{
goto v___jp_4453_;
}
v___jp_4337_:
{
if (v___y_4340_ == 0)
{
lean_object* v___x_4341_; lean_object* v___x_4342_; uint8_t v___x_4343_; 
lean_dec_ref(v___y_4338_);
v___x_4341_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4342_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4343_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4335_, v_options_4332_, v___x_4342_);
if (v___x_4343_ == 0)
{
lean_object* v___x_4344_; 
v___x_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4344_, 0, v___y_4339_);
return v___x_4344_;
}
else
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
lean_inc_ref(v___y_4339_);
v___x_4345_ = l_Lean_Exception_toMessageData(v___y_4339_);
v___x_4346_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4341_, v___x_4345_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v___x_4348_; uint8_t v_isShared_4349_; uint8_t v_isSharedCheck_4353_; 
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v___x_4346_, 0);
lean_dec(v_unused_4354_);
v___x_4348_ = v___x_4346_;
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
else
{
lean_dec(v___x_4346_);
v___x_4348_ = lean_box(0);
v_isShared_4349_ = v_isSharedCheck_4353_;
goto v_resetjp_4347_;
}
v_resetjp_4347_:
{
lean_object* v___x_4351_; 
if (v_isShared_4349_ == 0)
{
lean_ctor_set_tag(v___x_4348_, 1);
lean_ctor_set(v___x_4348_, 0, v___y_4339_);
v___x_4351_ = v___x_4348_;
goto v_reusejp_4350_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___y_4339_);
v___x_4351_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4350_;
}
v_reusejp_4350_:
{
return v___x_4351_;
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec_ref(v___y_4339_);
v_a_4355_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4346_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4346_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4339_);
return v___y_4338_;
}
}
v___jp_4363_:
{
uint8_t v___x_4366_; 
v___x_4366_ = l_Lean_Exception_isInterrupt(v_a_4365_);
if (v___x_4366_ == 0)
{
uint8_t v___x_4367_; 
lean_inc_ref(v_a_4365_);
v___x_4367_ = l_Lean_Exception_isRuntime(v_a_4365_);
v___y_4338_ = v___y_4364_;
v___y_4339_ = v_a_4365_;
v___y_4340_ = v___x_4367_;
goto v___jp_4337_;
}
else
{
v___y_4338_ = v___y_4364_;
v___y_4339_ = v_a_4365_;
v___y_4340_ = v___x_4366_;
goto v___jp_4337_;
}
}
v___jp_4372_:
{
lean_object* v___x_4376_; double v___x_4377_; double v___x_4378_; double v___x_4379_; double v___x_4380_; double v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
v___x_4376_ = lean_io_mono_nanos_now();
v___x_4377_ = lean_float_of_nat(v___y_4374_);
v___x_4378_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4379_ = lean_float_div(v___x_4377_, v___x_4378_);
v___x_4380_ = lean_float_of_nat(v___x_4376_);
v___x_4381_ = lean_float_div(v___x_4380_, v___x_4378_);
v___x_4382_ = lean_box_float(v___x_4379_);
v___x_4383_ = lean_box_float(v___x_4381_);
v___x_4384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4382_);
lean_ctor_set(v___x_4384_, 1, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4385_, 0, v_a_4375_);
lean_ctor_set(v___x_4385_, 1, v___x_4384_);
v___x_4386_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4368_, v_hasTrace_4333_, v___x_4369_, v_options_4332_, v___x_4371_, v___y_4373_, v___f_4336_, v___x_4385_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
return v___x_4386_;
}
v___jp_4387_:
{
lean_object* v___x_4391_; 
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v_a_4390_);
v___y_4373_ = v___y_4389_;
v___y_4374_ = v___y_4388_;
v_a_4375_ = v___x_4391_;
goto v___jp_4372_;
}
v___jp_4392_:
{
if (v___y_4396_ == 0)
{
lean_object* v___x_4397_; lean_object* v___x_4398_; uint8_t v___x_4399_; 
v___x_4397_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4398_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4335_, v_options_4332_, v___x_4398_);
if (v___x_4399_ == 0)
{
v___y_4388_ = v___y_4394_;
v___y_4389_ = v___y_4393_;
v_a_4390_ = v___y_4395_;
goto v___jp_4387_;
}
else
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
lean_inc_ref(v___y_4395_);
v___x_4400_ = l_Lean_Exception_toMessageData(v___y_4395_);
v___x_4401_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4397_, v___x_4400_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_dec_ref_known(v___x_4401_, 1);
v___y_4388_ = v___y_4394_;
v___y_4389_ = v___y_4393_;
v_a_4390_ = v___y_4395_;
goto v___jp_4387_;
}
else
{
lean_object* v_a_4402_; 
lean_dec_ref(v___y_4395_);
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v___y_4388_ = v___y_4394_;
v___y_4389_ = v___y_4393_;
v_a_4390_ = v_a_4402_;
goto v___jp_4387_;
}
}
}
else
{
v___y_4388_ = v___y_4394_;
v___y_4389_ = v___y_4393_;
v_a_4390_ = v___y_4395_;
goto v___jp_4387_;
}
}
v___jp_4403_:
{
uint8_t v___x_4407_; 
v___x_4407_ = l_Lean_Exception_isInterrupt(v_a_4406_);
if (v___x_4407_ == 0)
{
uint8_t v___x_4408_; 
lean_inc_ref(v_a_4406_);
v___x_4408_ = l_Lean_Exception_isRuntime(v_a_4406_);
v___y_4393_ = v___y_4405_;
v___y_4394_ = v___y_4404_;
v___y_4395_ = v_a_4406_;
v___y_4396_ = v___x_4408_;
goto v___jp_4392_;
}
else
{
v___y_4393_ = v___y_4405_;
v___y_4394_ = v___y_4404_;
v___y_4395_ = v_a_4406_;
v___y_4396_ = v___x_4407_;
goto v___jp_4392_;
}
}
v___jp_4409_:
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4413_, 0, v_a_4412_);
v___y_4373_ = v___y_4411_;
v___y_4374_ = v___y_4410_;
v_a_4375_ = v___x_4413_;
goto v___jp_4372_;
}
v___jp_4414_:
{
lean_object* v___x_4418_; double v___x_4419_; double v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4418_ = lean_io_get_num_heartbeats();
v___x_4419_ = lean_float_of_nat(v___y_4416_);
v___x_4420_ = lean_float_of_nat(v___x_4418_);
v___x_4421_ = lean_box_float(v___x_4419_);
v___x_4422_ = lean_box_float(v___x_4420_);
v___x_4423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4424_, 0, v_a_4417_);
lean_ctor_set(v___x_4424_, 1, v___x_4423_);
v___x_4425_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4368_, v_hasTrace_4333_, v___x_4369_, v_options_4332_, v___x_4371_, v___y_4415_, v___f_4336_, v___x_4424_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
return v___x_4425_;
}
v___jp_4426_:
{
lean_object* v___x_4430_; 
v___x_4430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4430_, 0, v_a_4429_);
v___y_4415_ = v___y_4427_;
v___y_4416_ = v___y_4428_;
v_a_4417_ = v___x_4430_;
goto v___jp_4414_;
}
v___jp_4431_:
{
if (v___y_4435_ == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4437_; uint8_t v___x_4438_; 
v___x_4436_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4437_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4438_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4335_, v_options_4332_, v___x_4437_);
if (v___x_4438_ == 0)
{
v___y_4427_ = v___y_4432_;
v___y_4428_ = v___y_4434_;
v_a_4429_ = v___y_4433_;
goto v___jp_4426_;
}
else
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
lean_inc_ref(v___y_4433_);
v___x_4439_ = l_Lean_Exception_toMessageData(v___y_4433_);
v___x_4440_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4436_, v___x_4439_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_dec_ref_known(v___x_4440_, 1);
v___y_4427_ = v___y_4432_;
v___y_4428_ = v___y_4434_;
v_a_4429_ = v___y_4433_;
goto v___jp_4426_;
}
else
{
lean_object* v_a_4441_; 
lean_dec_ref(v___y_4433_);
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___y_4427_ = v___y_4432_;
v___y_4428_ = v___y_4434_;
v_a_4429_ = v_a_4441_;
goto v___jp_4426_;
}
}
}
else
{
v___y_4427_ = v___y_4432_;
v___y_4428_ = v___y_4434_;
v_a_4429_ = v___y_4433_;
goto v___jp_4426_;
}
}
v___jp_4442_:
{
uint8_t v___x_4446_; 
v___x_4446_ = l_Lean_Exception_isInterrupt(v_a_4445_);
if (v___x_4446_ == 0)
{
uint8_t v___x_4447_; 
lean_inc_ref(v_a_4445_);
v___x_4447_ = l_Lean_Exception_isRuntime(v_a_4445_);
v___y_4432_ = v___y_4443_;
v___y_4433_ = v_a_4445_;
v___y_4434_ = v___y_4444_;
v___y_4435_ = v___x_4447_;
goto v___jp_4431_;
}
else
{
v___y_4432_ = v___y_4443_;
v___y_4433_ = v_a_4445_;
v___y_4434_ = v___y_4444_;
v___y_4435_ = v___x_4446_;
goto v___jp_4431_;
}
}
v___jp_4448_:
{
lean_object* v___x_4452_; 
v___x_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4452_, 0, v_a_4451_);
v___y_4415_ = v___y_4449_;
v___y_4416_ = v___y_4450_;
v_a_4417_ = v___x_4452_;
goto v___jp_4414_;
}
v___jp_4453_:
{
lean_object* v___x_4454_; lean_object* v_a_4455_; lean_object* v___x_4456_; uint8_t v___x_4457_; 
v___x_4454_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4329_);
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref(v___x_4454_);
v___x_4456_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4457_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4332_, v___x_4456_);
if (v___x_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; 
v___x_4458_ = lean_io_mono_nanos_now();
lean_inc(v_a_4329_);
lean_inc_ref(v_a_4328_);
lean_inc(v_a_4327_);
lean_inc_ref(v_a_4326_);
v___x_4459_ = lean_apply_5(v_k_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, lean_box(0));
if (lean_obj_tag(v___x_4459_) == 0)
{
lean_object* v_a_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; uint8_t v___x_4463_; 
v_a_4460_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4460_);
lean_dec_ref_known(v___x_4459_, 1);
v___x_4461_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4462_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4463_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4335_, v_options_4332_, v___x_4462_);
if (v___x_4463_ == 0)
{
v___y_4410_ = v___x_4458_;
v___y_4411_ = v_a_4455_;
v_a_4412_ = v_a_4460_;
goto v___jp_4409_;
}
else
{
lean_object* v___x_4464_; lean_object* v___x_4465_; 
lean_inc(v_a_4460_);
v___x_4464_ = l_Lean_MessageData_ofExpr(v_a_4460_);
v___x_4465_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4461_, v___x_4464_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
if (lean_obj_tag(v___x_4465_) == 0)
{
lean_dec_ref_known(v___x_4465_, 1);
v___y_4410_ = v___x_4458_;
v___y_4411_ = v_a_4455_;
v_a_4412_ = v_a_4460_;
goto v___jp_4409_;
}
else
{
lean_object* v_a_4466_; 
lean_dec(v_a_4460_);
v_a_4466_ = lean_ctor_get(v___x_4465_, 0);
lean_inc(v_a_4466_);
lean_dec_ref_known(v___x_4465_, 1);
v___y_4404_ = v___x_4458_;
v___y_4405_ = v_a_4455_;
v_a_4406_ = v_a_4466_;
goto v___jp_4403_;
}
}
}
else
{
lean_object* v_a_4467_; 
v_a_4467_ = lean_ctor_get(v___x_4459_, 0);
lean_inc(v_a_4467_);
lean_dec_ref_known(v___x_4459_, 1);
v___y_4404_ = v___x_4458_;
v___y_4405_ = v_a_4455_;
v_a_4406_ = v_a_4467_;
goto v___jp_4403_;
}
}
else
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4329_);
lean_inc_ref(v_a_4328_);
lean_inc(v_a_4327_);
lean_inc_ref(v_a_4326_);
v___x_4469_ = lean_apply_5(v_k_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, lean_box(0));
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; uint8_t v___x_4473_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4470_);
lean_dec_ref_known(v___x_4469_, 1);
v___x_4471_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4472_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4473_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4335_, v_options_4332_, v___x_4472_);
if (v___x_4473_ == 0)
{
v___y_4449_ = v_a_4455_;
v___y_4450_ = v___x_4468_;
v_a_4451_ = v_a_4470_;
goto v___jp_4448_;
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; 
lean_inc(v_a_4470_);
v___x_4474_ = l_Lean_MessageData_ofExpr(v_a_4470_);
v___x_4475_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4471_, v___x_4474_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_dec_ref_known(v___x_4475_, 1);
v___y_4449_ = v_a_4455_;
v___y_4450_ = v___x_4468_;
v_a_4451_ = v_a_4470_;
goto v___jp_4448_;
}
else
{
lean_object* v_a_4476_; 
lean_dec(v_a_4470_);
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4475_, 1);
v___y_4443_ = v_a_4455_;
v___y_4444_ = v___x_4468_;
v_a_4445_ = v_a_4476_;
goto v___jp_4442_;
}
}
}
else
{
lean_object* v_a_4477_; 
v_a_4477_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4477_);
lean_dec_ref_known(v___x_4469_, 1);
v___y_4443_ = v_a_4455_;
v___y_4444_ = v___x_4468_;
v_a_4445_ = v_a_4477_;
goto v___jp_4442_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4504_, lean_object* v_xs_4505_, lean_object* v_k_4506_, lean_object* v_a_4507_, lean_object* v_a_4508_, lean_object* v_a_4509_, lean_object* v_a_4510_, lean_object* v_a_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4504_, v_xs_4505_, v_k_4506_, v_a_4507_, v_a_4508_, v_a_4509_, v_a_4510_);
lean_dec(v_a_4510_);
lean_dec_ref(v_a_4509_);
lean_dec(v_a_4508_);
lean_dec_ref(v_a_4507_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4513_, lean_object* v_xs_4514_, lean_object* v_a_4515_, lean_object* v_a_4516_, lean_object* v_a_4517_, lean_object* v_a_4518_){
_start:
{
lean_object* v___x_4520_; 
lean_inc(v_a_4518_);
lean_inc_ref(v_a_4517_);
lean_inc(v_a_4516_);
lean_inc_ref(v_a_4515_);
lean_inc_ref(v_f_4513_);
v___x_4520_ = lean_infer_type(v_f_4513_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_object* v_a_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; uint8_t v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v_a_4521_ = lean_ctor_get(v___x_4520_, 0);
lean_inc(v_a_4521_);
lean_dec_ref_known(v___x_4520_, 1);
v___x_4522_ = lean_unsigned_to_nat(0u);
v___x_4523_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4514_);
lean_inc_ref(v_f_4513_);
v___x_4524_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4524_, 0, v_f_4513_);
lean_closure_set(v___x_4524_, 1, v_xs_4514_);
lean_closure_set(v___x_4524_, 2, v___x_4522_);
lean_closure_set(v___x_4524_, 3, v___x_4523_);
lean_closure_set(v___x_4524_, 4, v___x_4522_);
lean_closure_set(v___x_4524_, 5, v___x_4523_);
lean_closure_set(v___x_4524_, 6, v_a_4521_);
v___x_4525_ = 0;
v___x_4526_ = lean_box(v___x_4525_);
v___x_4527_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4527_, 0, lean_box(0));
lean_closure_set(v___x_4527_, 1, v___x_4524_);
lean_closure_set(v___x_4527_, 2, v___x_4526_);
v___x_4528_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4513_, v_xs_4514_, v___x_4527_, v_a_4515_, v_a_4516_, v_a_4517_, v_a_4518_);
return v___x_4528_;
}
else
{
lean_dec_ref(v_xs_4514_);
lean_dec_ref(v_f_4513_);
return v___x_4520_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4529_, lean_object* v_xs_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_, lean_object* v_a_4534_, lean_object* v_a_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l_Lean_Meta_mkAppOptM_x27(v_f_4529_, v_xs_4530_, v_a_4531_, v_a_4532_, v_a_4533_, v_a_4534_);
lean_dec(v_a_4534_);
lean_dec_ref(v_a_4533_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
return v_res_4536_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4544_; lean_object* v___x_4545_; 
v___x_4544_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4545_ = l_Lean_MessageData_ofFormat(v___x_4544_);
return v___x_4545_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4546_, lean_object* v_h1_4547_, lean_object* v_h2_4548_, lean_object* v_a_4549_, lean_object* v_a_4550_, lean_object* v_a_4551_, lean_object* v_a_4552_){
_start:
{
lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___x_4564_; uint8_t v___x_4565_; 
v___x_4564_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4565_ = l_Lean_Expr_isAppOf(v_h2_4548_, v___x_4564_);
if (v___x_4565_ == 0)
{
lean_object* v___x_4566_; 
lean_inc_ref(v_h2_4548_);
v___x_4566_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4548_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
if (lean_obj_tag(v___x_4566_) == 0)
{
lean_object* v_a_4567_; lean_object* v___x_4568_; lean_object* v___x_4569_; uint8_t v___x_4570_; 
v_a_4567_ = lean_ctor_get(v___x_4566_, 0);
lean_inc(v_a_4567_);
lean_dec_ref_known(v___x_4566_, 1);
v___x_4568_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4569_ = lean_unsigned_to_nat(3u);
v___x_4570_ = l_Lean_Expr_isAppOfArity(v_a_4567_, v___x_4568_, v___x_4569_);
if (v___x_4570_ == 0)
{
lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
lean_dec_ref(v_h1_4547_);
lean_dec_ref(v_motive_4546_);
v___x_4571_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4572_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4573_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4548_, v_a_4567_);
v___x_4574_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4572_);
lean_ctor_set(v___x_4574_, 1, v___x_4573_);
v___x_4575_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4571_, v___x_4574_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
return v___x_4575_;
}
else
{
lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4576_ = l_Lean_Expr_appFn_x21(v_a_4567_);
v___x_4577_ = l_Lean_Expr_appFn_x21(v___x_4576_);
v___x_4578_ = l_Lean_Expr_appArg_x21(v___x_4577_);
lean_dec_ref(v___x_4577_);
v___x_4579_ = l_Lean_Expr_appArg_x21(v___x_4576_);
lean_dec_ref(v___x_4576_);
v___x_4580_ = l_Lean_Expr_appArg_x21(v_a_4567_);
lean_dec(v_a_4567_);
lean_inc_ref(v___x_4578_);
v___x_4581_ = l_Lean_Meta_getLevel(v___x_4578_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4583_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
lean_inc(v_a_4582_);
lean_dec_ref_known(v___x_4581_, 1);
lean_inc_ref(v_motive_4546_);
v___x_4583_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4546_, v_a_4549_, v_a_4550_, v_a_4551_, v_a_4552_);
if (lean_obj_tag(v___x_4583_) == 0)
{
lean_object* v_a_4584_; lean_object* v___x_4586_; uint8_t v_isShared_4587_; uint8_t v_isSharedCheck_4607_; 
v_a_4584_ = lean_ctor_get(v___x_4583_, 0);
v_isSharedCheck_4607_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4607_ == 0)
{
v___x_4586_ = v___x_4583_;
v_isShared_4587_ = v_isSharedCheck_4607_;
goto v_resetjp_4585_;
}
else
{
lean_inc(v_a_4584_);
lean_dec(v___x_4583_);
v___x_4586_ = lean_box(0);
v_isShared_4587_ = v_isSharedCheck_4607_;
goto v_resetjp_4585_;
}
v_resetjp_4585_:
{
if (lean_obj_tag(v_a_4584_) == 7)
{
lean_object* v_body_4588_; 
v_body_4588_ = lean_ctor_get(v_a_4584_, 2);
lean_inc_ref(v_body_4588_);
lean_dec_ref_known(v_a_4584_, 3);
if (lean_obj_tag(v_body_4588_) == 3)
{
lean_object* v_u_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v_u_4589_ = lean_ctor_get(v_body_4588_, 0);
lean_inc(v_u_4589_);
lean_dec_ref_known(v_body_4588_, 1);
v___x_4590_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4591_ = lean_box(0);
v___x_4592_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4592_, 0, v_a_4582_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
v___x_4593_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4593_, 0, v_u_4589_);
lean_ctor_set(v___x_4593_, 1, v___x_4592_);
v___x_4594_ = l_Lean_mkConst(v___x_4590_, v___x_4593_);
v___x_4595_ = lean_unsigned_to_nat(6u);
v___x_4596_ = lean_mk_empty_array_with_capacity(v___x_4595_);
v___x_4597_ = lean_array_push(v___x_4596_, v___x_4578_);
v___x_4598_ = lean_array_push(v___x_4597_, v___x_4579_);
v___x_4599_ = lean_array_push(v___x_4598_, v_motive_4546_);
v___x_4600_ = lean_array_push(v___x_4599_, v_h1_4547_);
v___x_4601_ = lean_array_push(v___x_4600_, v___x_4580_);
v___x_4602_ = lean_array_push(v___x_4601_, v_h2_4548_);
v___x_4603_ = l_Lean_mkAppN(v___x_4594_, v___x_4602_);
lean_dec_ref(v___x_4602_);
if (v_isShared_4587_ == 0)
{
lean_ctor_set(v___x_4586_, 0, v___x_4603_);
v___x_4605_ = v___x_4586_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4606_; 
v_reuseFailAlloc_4606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4606_, 0, v___x_4603_);
v___x_4605_ = v_reuseFailAlloc_4606_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
return v___x_4605_;
}
}
else
{
lean_dec_ref(v_body_4588_);
lean_del_object(v___x_4586_);
lean_dec(v_a_4582_);
lean_dec_ref(v___x_4580_);
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4578_);
lean_dec_ref(v_h2_4548_);
lean_dec_ref(v_h1_4547_);
v___y_4555_ = v_a_4549_;
v___y_4556_ = v_a_4550_;
v___y_4557_ = v_a_4551_;
v___y_4558_ = v_a_4552_;
goto v___jp_4554_;
}
}
else
{
lean_del_object(v___x_4586_);
lean_dec(v_a_4584_);
lean_dec(v_a_4582_);
lean_dec_ref(v___x_4580_);
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4578_);
lean_dec_ref(v_h2_4548_);
lean_dec_ref(v_h1_4547_);
v___y_4555_ = v_a_4549_;
v___y_4556_ = v_a_4550_;
v___y_4557_ = v_a_4551_;
v___y_4558_ = v_a_4552_;
goto v___jp_4554_;
}
}
}
else
{
lean_dec(v_a_4582_);
lean_dec_ref(v___x_4580_);
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4578_);
lean_dec_ref(v_h2_4548_);
lean_dec_ref(v_h1_4547_);
lean_dec_ref(v_motive_4546_);
return v___x_4583_;
}
}
else
{
lean_object* v_a_4608_; lean_object* v___x_4610_; uint8_t v_isShared_4611_; uint8_t v_isSharedCheck_4615_; 
lean_dec_ref(v___x_4580_);
lean_dec_ref(v___x_4579_);
lean_dec_ref(v___x_4578_);
lean_dec_ref(v_h2_4548_);
lean_dec_ref(v_h1_4547_);
lean_dec_ref(v_motive_4546_);
v_a_4608_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4610_ = v___x_4581_;
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
else
{
lean_inc(v_a_4608_);
lean_dec(v___x_4581_);
v___x_4610_ = lean_box(0);
v_isShared_4611_ = v_isSharedCheck_4615_;
goto v_resetjp_4609_;
}
v_resetjp_4609_:
{
lean_object* v___x_4613_; 
if (v_isShared_4611_ == 0)
{
v___x_4613_ = v___x_4610_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v_a_4608_);
v___x_4613_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
return v___x_4613_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4548_);
lean_dec_ref(v_h1_4547_);
lean_dec_ref(v_motive_4546_);
return v___x_4566_;
}
}
else
{
lean_object* v___x_4616_; 
lean_dec_ref(v_h2_4548_);
lean_dec_ref(v_motive_4546_);
v___x_4616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4616_, 0, v_h1_4547_);
return v___x_4616_;
}
v___jp_4554_:
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; 
v___x_4559_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4560_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4561_ = l_Lean_indentExpr(v_motive_4546_);
v___x_4562_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4562_, 0, v___x_4560_);
lean_ctor_set(v___x_4562_, 1, v___x_4561_);
v___x_4563_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4559_, v___x_4562_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4563_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4617_, lean_object* v_h1_4618_, lean_object* v_h2_4619_, lean_object* v_a_4620_, lean_object* v_a_4621_, lean_object* v_a_4622_, lean_object* v_a_4623_, lean_object* v_a_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_Meta_mkEqNDRec(v_motive_4617_, v_h1_4618_, v_h2_4619_, v_a_4620_, v_a_4621_, v_a_4622_, v_a_4623_);
lean_dec(v_a_4623_);
lean_dec_ref(v_a_4622_);
lean_dec(v_a_4621_);
lean_dec_ref(v_a_4620_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4630_, lean_object* v_h1_4631_, lean_object* v_h2_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_){
_start:
{
lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___x_4648_; uint8_t v___x_4649_; 
v___x_4648_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4649_ = l_Lean_Expr_isAppOf(v_h2_4632_, v___x_4648_);
if (v___x_4649_ == 0)
{
lean_object* v___x_4650_; 
lean_inc_ref(v_h2_4632_);
v___x_4650_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4632_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
if (lean_obj_tag(v___x_4650_) == 0)
{
lean_object* v_a_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; uint8_t v___x_4654_; 
v_a_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc(v_a_4651_);
lean_dec_ref_known(v___x_4650_, 1);
v___x_4652_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4653_ = lean_unsigned_to_nat(3u);
v___x_4654_ = l_Lean_Expr_isAppOfArity(v_a_4651_, v___x_4652_, v___x_4653_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4655_; lean_object* v___x_4656_; lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; 
lean_dec(v_a_4651_);
lean_dec_ref(v_h1_4631_);
lean_dec_ref(v_motive_4630_);
v___x_4655_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4656_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4657_ = l_Lean_indentExpr(v_h2_4632_);
v___x_4658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4656_);
lean_ctor_set(v___x_4658_, 1, v___x_4657_);
v___x_4659_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4655_, v___x_4658_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
return v___x_4659_;
}
else
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4660_ = l_Lean_Expr_appFn_x21(v_a_4651_);
v___x_4661_ = l_Lean_Expr_appFn_x21(v___x_4660_);
v___x_4662_ = l_Lean_Expr_appArg_x21(v___x_4661_);
lean_dec_ref(v___x_4661_);
v___x_4663_ = l_Lean_Expr_appArg_x21(v___x_4660_);
lean_dec_ref(v___x_4660_);
v___x_4664_ = l_Lean_Expr_appArg_x21(v_a_4651_);
lean_dec(v_a_4651_);
lean_inc_ref(v___x_4662_);
v___x_4665_ = l_Lean_Meta_getLevel(v___x_4662_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4667_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4666_);
lean_dec_ref_known(v___x_4665_, 1);
lean_inc_ref(v_motive_4630_);
v___x_4667_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4630_, v_a_4633_, v_a_4634_, v_a_4635_, v_a_4636_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4692_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4692_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4692_ == 0)
{
v___x_4670_ = v___x_4667_;
v_isShared_4671_ = v_isSharedCheck_4692_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4667_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4692_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
if (lean_obj_tag(v_a_4668_) == 7)
{
lean_object* v_body_4672_; 
v_body_4672_ = lean_ctor_get(v_a_4668_, 2);
lean_inc_ref(v_body_4672_);
lean_dec_ref_known(v_a_4668_, 3);
if (lean_obj_tag(v_body_4672_) == 7)
{
lean_object* v_body_4673_; 
v_body_4673_ = lean_ctor_get(v_body_4672_, 2);
lean_inc_ref(v_body_4673_);
lean_dec_ref_known(v_body_4672_, 3);
if (lean_obj_tag(v_body_4673_) == 3)
{
lean_object* v_u_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4690_; 
v_u_4674_ = lean_ctor_get(v_body_4673_, 0);
lean_inc(v_u_4674_);
lean_dec_ref_known(v_body_4673_, 1);
v___x_4675_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4676_ = lean_box(0);
v___x_4677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4677_, 0, v_a_4666_);
lean_ctor_set(v___x_4677_, 1, v___x_4676_);
v___x_4678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4678_, 0, v_u_4674_);
lean_ctor_set(v___x_4678_, 1, v___x_4677_);
v___x_4679_ = l_Lean_mkConst(v___x_4675_, v___x_4678_);
v___x_4680_ = lean_unsigned_to_nat(6u);
v___x_4681_ = lean_mk_empty_array_with_capacity(v___x_4680_);
v___x_4682_ = lean_array_push(v___x_4681_, v___x_4662_);
v___x_4683_ = lean_array_push(v___x_4682_, v___x_4663_);
v___x_4684_ = lean_array_push(v___x_4683_, v_motive_4630_);
v___x_4685_ = lean_array_push(v___x_4684_, v_h1_4631_);
v___x_4686_ = lean_array_push(v___x_4685_, v___x_4664_);
v___x_4687_ = lean_array_push(v___x_4686_, v_h2_4632_);
v___x_4688_ = l_Lean_mkAppN(v___x_4679_, v___x_4687_);
lean_dec_ref(v___x_4687_);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v___x_4688_);
v___x_4690_ = v___x_4670_;
goto v_reusejp_4689_;
}
else
{
lean_object* v_reuseFailAlloc_4691_; 
v_reuseFailAlloc_4691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4691_, 0, v___x_4688_);
v___x_4690_ = v_reuseFailAlloc_4691_;
goto v_reusejp_4689_;
}
v_reusejp_4689_:
{
return v___x_4690_;
}
}
else
{
lean_dec_ref(v_body_4673_);
lean_del_object(v___x_4670_);
lean_dec(v_a_4666_);
lean_dec_ref(v___x_4664_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4662_);
lean_dec_ref(v_h2_4632_);
lean_dec_ref(v_h1_4631_);
v___y_4639_ = v_a_4633_;
v___y_4640_ = v_a_4634_;
v___y_4641_ = v_a_4635_;
v___y_4642_ = v_a_4636_;
goto v___jp_4638_;
}
}
else
{
lean_dec_ref(v_body_4672_);
lean_del_object(v___x_4670_);
lean_dec(v_a_4666_);
lean_dec_ref(v___x_4664_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4662_);
lean_dec_ref(v_h2_4632_);
lean_dec_ref(v_h1_4631_);
v___y_4639_ = v_a_4633_;
v___y_4640_ = v_a_4634_;
v___y_4641_ = v_a_4635_;
v___y_4642_ = v_a_4636_;
goto v___jp_4638_;
}
}
else
{
lean_del_object(v___x_4670_);
lean_dec(v_a_4668_);
lean_dec(v_a_4666_);
lean_dec_ref(v___x_4664_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4662_);
lean_dec_ref(v_h2_4632_);
lean_dec_ref(v_h1_4631_);
v___y_4639_ = v_a_4633_;
v___y_4640_ = v_a_4634_;
v___y_4641_ = v_a_4635_;
v___y_4642_ = v_a_4636_;
goto v___jp_4638_;
}
}
}
else
{
lean_dec(v_a_4666_);
lean_dec_ref(v___x_4664_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4662_);
lean_dec_ref(v_h2_4632_);
lean_dec_ref(v_h1_4631_);
lean_dec_ref(v_motive_4630_);
return v___x_4667_;
}
}
else
{
lean_object* v_a_4693_; lean_object* v___x_4695_; uint8_t v_isShared_4696_; uint8_t v_isSharedCheck_4700_; 
lean_dec_ref(v___x_4664_);
lean_dec_ref(v___x_4663_);
lean_dec_ref(v___x_4662_);
lean_dec_ref(v_h2_4632_);
lean_dec_ref(v_h1_4631_);
lean_dec_ref(v_motive_4630_);
v_a_4693_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4700_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4700_ == 0)
{
v___x_4695_ = v___x_4665_;
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
else
{
lean_inc(v_a_4693_);
lean_dec(v___x_4665_);
v___x_4695_ = lean_box(0);
v_isShared_4696_ = v_isSharedCheck_4700_;
goto v_resetjp_4694_;
}
v_resetjp_4694_:
{
lean_object* v___x_4698_; 
if (v_isShared_4696_ == 0)
{
v___x_4698_ = v___x_4695_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4699_; 
v_reuseFailAlloc_4699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
v___x_4698_ = v_reuseFailAlloc_4699_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
return v___x_4698_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4632_);
lean_dec_ref(v_h1_4631_);
lean_dec_ref(v_motive_4630_);
return v___x_4650_;
}
}
else
{
lean_object* v___x_4701_; 
lean_dec_ref(v_h2_4632_);
lean_dec_ref(v_motive_4630_);
v___x_4701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4701_, 0, v_h1_4631_);
return v___x_4701_;
}
v___jp_4638_:
{
lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4643_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4644_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4645_ = l_Lean_indentExpr(v_motive_4630_);
v___x_4646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4646_, 0, v___x_4644_);
lean_ctor_set(v___x_4646_, 1, v___x_4645_);
v___x_4647_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4643_, v___x_4646_, v___y_4639_, v___y_4640_, v___y_4641_, v___y_4642_);
return v___x_4647_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4702_, lean_object* v_h1_4703_, lean_object* v_h2_4704_, lean_object* v_a_4705_, lean_object* v_a_4706_, lean_object* v_a_4707_, lean_object* v_a_4708_, lean_object* v_a_4709_){
_start:
{
lean_object* v_res_4710_; 
v_res_4710_ = l_Lean_Meta_mkEqRec(v_motive_4702_, v_h1_4703_, v_h2_4704_, v_a_4705_, v_a_4706_, v_a_4707_, v_a_4708_);
lean_dec(v_a_4708_);
lean_dec_ref(v_a_4707_);
lean_dec(v_a_4706_);
lean_dec_ref(v_a_4705_);
return v_res_4710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4715_, lean_object* v_pr_4716_, lean_object* v_a_4717_, lean_object* v_a_4718_, lean_object* v_a_4719_, lean_object* v_a_4720_){
_start:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4722_ = ((lean_object*)(l_Lean_Meta_mkEqMP___closed__1));
v___x_4723_ = lean_unsigned_to_nat(2u);
v___x_4724_ = lean_mk_empty_array_with_capacity(v___x_4723_);
v___x_4725_ = lean_array_push(v___x_4724_, v_eqProof_4715_);
v___x_4726_ = lean_array_push(v___x_4725_, v_pr_4716_);
v___x_4727_ = l_Lean_Meta_mkAppM(v___x_4722_, v___x_4726_, v_a_4717_, v_a_4718_, v_a_4719_, v_a_4720_);
return v___x_4727_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4728_, lean_object* v_pr_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_, lean_object* v_a_4732_, lean_object* v_a_4733_, lean_object* v_a_4734_){
_start:
{
lean_object* v_res_4735_; 
v_res_4735_ = l_Lean_Meta_mkEqMP(v_eqProof_4728_, v_pr_4729_, v_a_4730_, v_a_4731_, v_a_4732_, v_a_4733_);
lean_dec(v_a_4733_);
lean_dec_ref(v_a_4732_);
lean_dec(v_a_4731_);
lean_dec_ref(v_a_4730_);
return v_res_4735_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4740_, lean_object* v_pr_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_, lean_object* v_a_4745_){
_start:
{
lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4747_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4748_ = lean_unsigned_to_nat(2u);
v___x_4749_ = lean_mk_empty_array_with_capacity(v___x_4748_);
v___x_4750_ = lean_array_push(v___x_4749_, v_eqProof_4740_);
v___x_4751_ = lean_array_push(v___x_4750_, v_pr_4741_);
v___x_4752_ = l_Lean_Meta_mkAppM(v___x_4747_, v___x_4751_, v_a_4742_, v_a_4743_, v_a_4744_, v_a_4745_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4753_, lean_object* v_pr_4754_, lean_object* v_a_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_){
_start:
{
lean_object* v_res_4760_; 
v_res_4760_ = l_Lean_Meta_mkEqMPR(v_eqProof_4753_, v_pr_4754_, v_a_4755_, v_a_4756_, v_a_4757_, v_a_4758_);
lean_dec(v_a_4758_);
lean_dec_ref(v_a_4757_);
lean_dec(v_a_4756_);
lean_dec_ref(v_a_4755_);
return v_res_4760_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_){
_start:
{
lean_object* v___f_4767_; lean_object* v___x_12329__overap_4768_; lean_object* v___x_4769_; 
v___f_4767_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12329__overap_4768_ = lean_panic_fn_borrowed(v___f_4767_, v_msg_4761_);
lean_inc(v___y_4765_);
lean_inc_ref(v___y_4764_);
lean_inc(v___y_4763_);
lean_inc_ref(v___y_4762_);
v___x_4769_ = lean_apply_5(v___x_12329__overap_4768_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_, lean_box(0));
return v___x_4769_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4777_, uint8_t v_skipRealize_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v___x_4781_; lean_object* v_env_4782_; uint8_t v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4781_ = lean_st_ref_get(v___y_4779_);
v_env_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc_ref(v_env_4782_);
lean_dec(v___x_4781_);
v___x_4783_ = l_Lean_Environment_contains(v_env_4782_, v_constName_4777_, v_skipRealize_4778_);
v___x_4784_ = lean_box(v___x_4783_);
v___x_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4786_, lean_object* v_skipRealize_4787_, lean_object* v___y_4788_, lean_object* v___y_4789_){
_start:
{
uint8_t v_skipRealize_boxed_4790_; lean_object* v_res_4791_; 
v_skipRealize_boxed_4790_ = lean_unbox(v_skipRealize_4787_);
v_res_4791_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4786_, v_skipRealize_boxed_4790_, v___y_4788_);
lean_dec(v___y_4788_);
return v_res_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4792_, uint8_t v_skipRealize_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_){
_start:
{
lean_object* v___x_4799_; 
v___x_4799_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4792_, v_skipRealize_4793_, v___y_4797_);
return v___x_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4800_, lean_object* v_skipRealize_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_){
_start:
{
uint8_t v_skipRealize_boxed_4807_; lean_object* v_res_4808_; 
v_skipRealize_boxed_4807_ = lean_unbox(v_skipRealize_4801_);
v_res_4808_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4800_, v_skipRealize_boxed_4807_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_);
lean_dec(v___y_4805_);
lean_dec_ref(v___y_4804_);
lean_dec(v___y_4803_);
lean_dec_ref(v___y_4802_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___y_4809_, uint8_t v___x_4810_, lean_object* v_P_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; uint8_t v___x_4820_; lean_object* v___x_4821_; 
v___x_4817_ = lean_unsigned_to_nat(1u);
v___x_4818_ = lean_mk_empty_array_with_capacity(v___x_4817_);
lean_inc_ref(v_P_4811_);
v___x_4819_ = lean_array_push(v___x_4818_, v_P_4811_);
v___x_4820_ = 1;
v___x_4821_ = l_Lean_Meta_mkLambdaFVars(v___x_4819_, v_P_4811_, v___y_4809_, v___x_4810_, v___y_4809_, v___x_4810_, v___x_4820_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec_ref(v___x_4819_);
return v___x_4821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___y_4822_, lean_object* v___x_4823_, lean_object* v_P_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
uint8_t v___y_13587__boxed_4830_; uint8_t v___x_13588__boxed_4831_; lean_object* v_res_4832_; 
v___y_13587__boxed_4830_ = lean_unbox(v___y_4822_);
v___x_13588__boxed_4831_ = lean_unbox(v___x_4823_);
v_res_4832_ = l_Lean_Meta_mkNoConfusion___lam__0(v___y_13587__boxed_4830_, v___x_13588__boxed_4831_, v_P_4824_, v___y_4825_, v___y_4826_, v___y_4827_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v___y_4826_);
lean_dec_ref(v___y_4825_);
return v_res_4832_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4835_ = l_Lean_stringToMessageData(v___x_4834_);
return v___x_4835_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4838_ = l_Lean_stringToMessageData(v___x_4837_);
return v___x_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4839_, lean_object* v_b_4840_, lean_object* v_i_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_){
_start:
{
lean_object* v_stop_4847_; lean_object* v_step_4848_; lean_object* v_a_4850_; uint8_t v___x_4853_; 
v_stop_4847_ = lean_ctor_get(v_range_4839_, 1);
v_step_4848_ = lean_ctor_get(v_range_4839_, 2);
v___x_4853_ = lean_nat_dec_lt(v_i_4841_, v_stop_4847_);
if (v___x_4853_ == 0)
{
lean_object* v___x_4854_; 
lean_dec(v_i_4841_);
v___x_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4854_, 0, v_b_4840_);
return v___x_4854_;
}
else
{
lean_object* v___x_4855_; 
lean_inc(v___y_4845_);
lean_inc_ref(v___y_4844_);
lean_inc(v___y_4843_);
lean_inc_ref(v___y_4842_);
lean_inc_ref(v_b_4840_);
v___x_4855_ = lean_infer_type(v_b_4840_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4855_) == 0)
{
lean_object* v_a_4856_; lean_object* v___x_4857_; 
v_a_4856_ = lean_ctor_get(v___x_4855_, 0);
lean_inc(v_a_4856_);
lean_dec_ref_known(v___x_4855_, 1);
v___x_4857_ = l_Lean_Meta_whnfForall(v_a_4856_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4857_) == 0)
{
lean_object* v_a_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v_a_4858_ = lean_ctor_get(v___x_4857_, 0);
lean_inc(v_a_4858_);
lean_dec_ref_known(v___x_4857_, 1);
v___x_4859_ = l_Lean_Expr_bindingDomain_x21(v_a_4858_);
lean_dec(v_a_4858_);
lean_inc(v___y_4845_);
lean_inc_ref(v___y_4844_);
lean_inc(v___y_4843_);
lean_inc_ref(v___y_4842_);
v___x_4860_ = lean_whnf(v___x_4859_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; uint8_t v___x_4864_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v___x_4862_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4863_ = lean_unsigned_to_nat(4u);
v___x_4864_ = l_Lean_Expr_isAppOfArity(v_a_4861_, v___x_4862_, v___x_4863_);
if (v___x_4864_ == 0)
{
lean_object* v___x_4865_; lean_object* v___x_4866_; uint8_t v___x_4867_; 
v___x_4865_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4866_ = lean_unsigned_to_nat(3u);
v___x_4867_ = l_Lean_Expr_isAppOfArity(v_a_4861_, v___x_4865_, v___x_4866_);
if (v___x_4867_ == 0)
{
lean_object* v___x_4868_; 
lean_dec(v_i_4841_);
lean_inc(v___y_4845_);
lean_inc_ref(v___y_4844_);
lean_inc(v___y_4843_);
lean_inc_ref(v___y_4842_);
v___x_4868_ = lean_infer_type(v_b_4840_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v_a_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref_known(v___x_4868_, 1);
v___x_4870_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4871_ = l_Lean_MessageData_ofExpr(v_a_4861_);
v___x_4872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4870_);
lean_ctor_set(v___x_4872_, 1, v___x_4871_);
v___x_4873_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4872_);
lean_ctor_set(v___x_4874_, 1, v___x_4873_);
v___x_4875_ = lean_unsigned_to_nat(30u);
v___x_4876_ = l_Lean_inlineExpr(v_a_4869_, v___x_4875_);
v___x_4877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4874_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
v___x_4878_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4877_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_4886_ == 0)
{
v___x_4881_ = v___x_4878_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_inc(v_a_4879_);
lean_dec(v___x_4878_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4879_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
else
{
lean_dec(v_a_4861_);
return v___x_4868_;
}
}
else
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4887_ = l_Lean_Expr_appFn_x21(v_a_4861_);
lean_dec(v_a_4861_);
v___x_4888_ = l_Lean_Expr_appArg_x21(v___x_4887_);
lean_dec_ref(v___x_4887_);
v___x_4889_ = l_Lean_Meta_mkEqRefl(v___x_4888_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4891_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v___x_4891_ = l_Lean_Expr_app___override(v_b_4840_, v_a_4890_);
v_a_4850_ = v___x_4891_;
goto v___jp_4849_;
}
else
{
lean_dec(v_i_4841_);
lean_dec_ref(v_b_4840_);
return v___x_4889_;
}
}
}
else
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4892_ = l_Lean_Expr_appFn_x21(v_a_4861_);
lean_dec(v_a_4861_);
v___x_4893_ = l_Lean_Expr_appFn_x21(v___x_4892_);
lean_dec_ref(v___x_4892_);
v___x_4894_ = l_Lean_Expr_appArg_x21(v___x_4893_);
lean_dec_ref(v___x_4893_);
v___x_4895_ = l_Lean_Meta_mkHEqRefl(v___x_4894_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
if (lean_obj_tag(v___x_4895_) == 0)
{
lean_object* v_a_4896_; lean_object* v___x_4897_; 
v_a_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc(v_a_4896_);
lean_dec_ref_known(v___x_4895_, 1);
v___x_4897_ = l_Lean_Expr_app___override(v_b_4840_, v_a_4896_);
v_a_4850_ = v___x_4897_;
goto v___jp_4849_;
}
else
{
lean_dec(v_i_4841_);
lean_dec_ref(v_b_4840_);
return v___x_4895_;
}
}
}
else
{
lean_dec(v_i_4841_);
lean_dec_ref(v_b_4840_);
return v___x_4860_;
}
}
else
{
lean_dec(v_i_4841_);
lean_dec_ref(v_b_4840_);
return v___x_4857_;
}
}
else
{
lean_dec(v_i_4841_);
lean_dec_ref(v_b_4840_);
return v___x_4855_;
}
}
v___jp_4849_:
{
lean_object* v___x_4851_; 
v___x_4851_ = lean_nat_add(v_i_4841_, v_step_4848_);
lean_dec(v_i_4841_);
v_b_4840_ = v_a_4850_;
v_i_4841_ = v___x_4851_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4898_, lean_object* v_b_4899_, lean_object* v_i_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4898_, v_b_4899_, v_i_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_);
lean_dec(v___y_4904_);
lean_dec_ref(v___y_4903_);
lean_dec(v___y_4902_);
lean_dec_ref(v___y_4901_);
lean_dec_ref(v_range_4898_);
return v_res_4906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4907_, lean_object* v_b_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; 
lean_inc(v___y_4912_);
lean_inc_ref(v___y_4911_);
lean_inc(v___y_4910_);
lean_inc_ref(v___y_4909_);
v___x_4914_ = lean_apply_6(v_k_4907_, v_b_4908_, v___y_4909_, v___y_4910_, v___y_4911_, v___y_4912_, lean_box(0));
return v___x_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4915_, lean_object* v_b_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_){
_start:
{
lean_object* v_res_4922_; 
v_res_4922_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4915_, v_b_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
lean_dec(v___y_4920_);
lean_dec_ref(v___y_4919_);
lean_dec(v___y_4918_);
lean_dec_ref(v___y_4917_);
return v_res_4922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4923_, uint8_t v_bi_4924_, lean_object* v_type_4925_, lean_object* v_k_4926_, uint8_t v_kind_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_){
_start:
{
lean_object* v___f_4933_; lean_object* v___x_4934_; 
v___f_4933_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_4933_, 0, v_k_4926_);
v___x_4934_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4923_, v_bi_4924_, v_type_4925_, v___f_4933_, v_kind_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
if (lean_obj_tag(v___x_4934_) == 0)
{
lean_object* v_a_4935_; lean_object* v___x_4937_; uint8_t v_isShared_4938_; uint8_t v_isSharedCheck_4942_; 
v_a_4935_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4942_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4942_ == 0)
{
v___x_4937_ = v___x_4934_;
v_isShared_4938_ = v_isSharedCheck_4942_;
goto v_resetjp_4936_;
}
else
{
lean_inc(v_a_4935_);
lean_dec(v___x_4934_);
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
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_4943_; lean_object* v___x_4945_; uint8_t v_isShared_4946_; uint8_t v_isSharedCheck_4950_; 
v_a_4943_ = lean_ctor_get(v___x_4934_, 0);
v_isSharedCheck_4950_ = !lean_is_exclusive(v___x_4934_);
if (v_isSharedCheck_4950_ == 0)
{
v___x_4945_ = v___x_4934_;
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
else
{
lean_inc(v_a_4943_);
lean_dec(v___x_4934_);
v___x_4945_ = lean_box(0);
v_isShared_4946_ = v_isSharedCheck_4950_;
goto v_resetjp_4944_;
}
v_resetjp_4944_:
{
lean_object* v___x_4948_; 
if (v_isShared_4946_ == 0)
{
v___x_4948_ = v___x_4945_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4943_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_4951_, lean_object* v_bi_4952_, lean_object* v_type_4953_, lean_object* v_k_4954_, lean_object* v_kind_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_, lean_object* v___y_4959_, lean_object* v___y_4960_){
_start:
{
uint8_t v_bi_boxed_4961_; uint8_t v_kind_boxed_4962_; lean_object* v_res_4963_; 
v_bi_boxed_4961_ = lean_unbox(v_bi_4952_);
v_kind_boxed_4962_ = lean_unbox(v_kind_4955_);
v_res_4963_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4951_, v_bi_boxed_4961_, v_type_4953_, v_k_4954_, v_kind_boxed_4962_, v___y_4956_, v___y_4957_, v___y_4958_, v___y_4959_);
lean_dec(v___y_4959_);
lean_dec_ref(v___y_4958_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_4964_, lean_object* v_type_4965_, lean_object* v_k_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_, lean_object* v___y_4969_, lean_object* v___y_4970_){
_start:
{
uint8_t v___x_4972_; uint8_t v___x_4973_; lean_object* v___x_4974_; 
v___x_4972_ = 0;
v___x_4973_ = 0;
v___x_4974_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_4964_, v___x_4972_, v_type_4965_, v_k_4966_, v___x_4973_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_4975_, lean_object* v_type_4976_, lean_object* v_k_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v_res_4983_; 
v_res_4983_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_4975_, v_type_4976_, v_k_4977_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
return v_res_4983_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_4990_; lean_object* v___x_4991_; 
v___x_4990_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_4991_ = l_Lean_MessageData_ofFormat(v___x_4990_);
return v___x_4991_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6(void){
_start:
{
lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4993_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__5));
v___x_4994_ = l_Lean_stringToMessageData(v___x_4993_);
return v___x_4994_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8(void){
_start:
{
lean_object* v___x_4996_; lean_object* v___x_4997_; 
v___x_4996_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__7));
v___x_4997_ = l_Lean_stringToMessageData(v___x_4996_);
return v___x_4997_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; 
v___x_5001_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_5002_ = l_Lean_MessageData_ofFormat(v___x_5001_);
return v___x_5002_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__14(void){
_start:
{
lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5005_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__13));
v___x_5006_ = lean_unsigned_to_nat(10u);
v___x_5007_ = lean_unsigned_to_nat(490u);
v___x_5008_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5009_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5010_ = l_mkPanicMessageWithDecl(v___x_5009_, v___x_5008_, v___x_5007_, v___x_5006_, v___x_5005_);
return v___x_5010_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5012_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5013_ = l_Lean_stringToMessageData(v___x_5012_);
return v___x_5013_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__23(void){
_start:
{
lean_object* v___x_5022_; lean_object* v___x_5023_; 
v___x_5022_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__22));
v___x_5023_ = l_Lean_stringToMessageData(v___x_5022_);
return v___x_5023_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__24(void){
_start:
{
lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5024_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5025_ = l_Lean_MessageData_ofName(v___x_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5026_, lean_object* v_h_5027_, lean_object* v_a_5028_, lean_object* v_a_5029_, lean_object* v_a_5030_, lean_object* v_a_5031_){
_start:
{
lean_object* v___x_5033_; 
lean_inc(v_a_5031_);
lean_inc_ref(v_a_5030_);
lean_inc(v_a_5029_);
lean_inc_ref(v_a_5028_);
lean_inc_ref(v_h_5027_);
v___x_5033_ = lean_infer_type(v_h_5027_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5033_) == 0)
{
lean_object* v_a_5034_; lean_object* v___x_5035_; 
v_a_5034_ = lean_ctor_get(v___x_5033_, 0);
lean_inc(v_a_5034_);
lean_dec_ref_known(v___x_5033_, 1);
lean_inc(v_a_5031_);
lean_inc_ref(v_a_5030_);
lean_inc(v_a_5029_);
lean_inc_ref(v_a_5028_);
v___x_5035_ = lean_whnf(v_a_5034_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5035_) == 0)
{
lean_object* v_a_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; uint8_t v___x_5039_; 
v_a_5036_ = lean_ctor_get(v___x_5035_, 0);
lean_inc(v_a_5036_);
lean_dec_ref_known(v___x_5035_, 1);
v___x_5037_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5038_ = lean_unsigned_to_nat(3u);
v___x_5039_ = l_Lean_Expr_isAppOfArity(v_a_5036_, v___x_5037_, v___x_5038_);
if (v___x_5039_ == 0)
{
lean_object* v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; 
lean_dec_ref(v_target_5026_);
v___x_5040_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5041_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5042_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5027_, v_a_5036_);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5041_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5040_, v___x_5043_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
return v___x_5044_;
}
else
{
lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v___y_5051_; lean_object* v___y_5052_; lean_object* v___y_5053_; lean_object* v___y_5054_; lean_object* v___x_5063_; 
v___x_5045_ = l_Lean_Expr_appFn_x21(v_a_5036_);
v___x_5046_ = l_Lean_Expr_appFn_x21(v___x_5045_);
v___x_5047_ = l_Lean_Expr_appArg_x21(v___x_5046_);
lean_dec_ref(v___x_5046_);
v___x_5048_ = l_Lean_Expr_appArg_x21(v___x_5045_);
lean_dec_ref(v___x_5045_);
v___x_5049_ = l_Lean_Expr_appArg_x21(v_a_5036_);
lean_dec(v_a_5036_);
v___x_5063_ = l_Lean_Meta_whnfD(v___x_5047_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5063_) == 0)
{
lean_object* v_a_5064_; lean_object* v___y_5066_; lean_object* v___y_5067_; lean_object* v___y_5068_; lean_object* v___y_5069_; lean_object* v___x_5075_; 
v_a_5064_ = lean_ctor_get(v___x_5063_, 0);
lean_inc(v_a_5064_);
lean_dec_ref_known(v___x_5063_, 1);
v___x_5075_ = l_Lean_Expr_getAppFn(v_a_5064_);
if (lean_obj_tag(v___x_5075_) == 4)
{
lean_object* v_declName_5076_; lean_object* v_us_5077_; lean_object* v___x_5078_; lean_object* v_env_5079_; uint8_t v___x_5080_; lean_object* v___x_5081_; 
v_declName_5076_ = lean_ctor_get(v___x_5075_, 0);
lean_inc(v_declName_5076_);
v_us_5077_ = lean_ctor_get(v___x_5075_, 1);
lean_inc(v_us_5077_);
lean_dec_ref_known(v___x_5075_, 2);
v___x_5078_ = lean_st_ref_get(v_a_5031_);
v_env_5079_ = lean_ctor_get(v___x_5078_, 0);
lean_inc_ref(v_env_5079_);
lean_dec(v___x_5078_);
v___x_5080_ = 0;
v___x_5081_ = l_Lean_Environment_find_x3f(v_env_5079_, v_declName_5076_, v___x_5080_);
if (lean_obj_tag(v___x_5081_) == 0)
{
lean_dec(v_us_5077_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v___y_5066_ = v_a_5028_;
v___y_5067_ = v_a_5029_;
v___y_5068_ = v_a_5030_;
v___y_5069_ = v_a_5031_;
goto v___jp_5065_;
}
else
{
lean_object* v_val_5082_; 
v_val_5082_ = lean_ctor_get(v___x_5081_, 0);
lean_inc(v_val_5082_);
lean_dec_ref_known(v___x_5081_, 1);
if (lean_obj_tag(v_val_5082_) == 5)
{
lean_object* v_val_5083_; lean_object* v___x_5084_; 
v_val_5083_ = lean_ctor_get(v_val_5082_, 0);
lean_inc_ref(v_val_5083_);
lean_dec_ref_known(v_val_5082_, 1);
lean_inc_ref(v_target_5026_);
v___x_5084_ = l_Lean_Meta_getLevel(v_target_5026_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5084_) == 0)
{
lean_object* v_a_5085_; lean_object* v___x_5086_; 
v_a_5085_ = lean_ctor_get(v___x_5084_, 0);
lean_inc(v_a_5085_);
lean_dec_ref_known(v___x_5084_, 1);
lean_inc_ref(v___x_5048_);
v___x_5086_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5048_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5086_) == 0)
{
lean_object* v_a_5087_; 
v_a_5087_ = lean_ctor_get(v___x_5086_, 0);
lean_inc(v_a_5087_);
lean_dec_ref_known(v___x_5086_, 1);
if (lean_obj_tag(v_a_5087_) == 1)
{
lean_object* v_val_5088_; lean_object* v_fst_5089_; lean_object* v_snd_5090_; lean_object* v___x_5092_; uint8_t v_isShared_5093_; uint8_t v_isSharedCheck_5304_; 
v_val_5088_ = lean_ctor_get(v_a_5087_, 0);
lean_inc(v_val_5088_);
lean_dec_ref_known(v_a_5087_, 1);
v_fst_5089_ = lean_ctor_get(v_val_5088_, 0);
v_snd_5090_ = lean_ctor_get(v_val_5088_, 1);
v_isSharedCheck_5304_ = !lean_is_exclusive(v_val_5088_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5092_ = v_val_5088_;
v_isShared_5093_ = v_isSharedCheck_5304_;
goto v_resetjp_5091_;
}
else
{
lean_inc(v_snd_5090_);
lean_inc(v_fst_5089_);
lean_dec(v_val_5088_);
v___x_5092_ = lean_box(0);
v_isShared_5093_ = v_isSharedCheck_5304_;
goto v_resetjp_5091_;
}
v_resetjp_5091_:
{
lean_object* v___x_5094_; 
lean_inc_ref(v___x_5049_);
v___x_5094_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5049_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5094_) == 0)
{
lean_object* v_a_5095_; 
v_a_5095_ = lean_ctor_get(v___x_5094_, 0);
lean_inc(v_a_5095_);
lean_dec_ref_known(v___x_5094_, 1);
if (lean_obj_tag(v_a_5095_) == 1)
{
lean_object* v_val_5096_; lean_object* v_fst_5097_; lean_object* v_snd_5098_; lean_object* v___x_5100_; uint8_t v_isShared_5101_; uint8_t v_isSharedCheck_5295_; 
v_val_5096_ = lean_ctor_get(v_a_5095_, 0);
lean_inc(v_val_5096_);
lean_dec_ref_known(v_a_5095_, 1);
v_fst_5097_ = lean_ctor_get(v_val_5096_, 0);
v_snd_5098_ = lean_ctor_get(v_val_5096_, 1);
v_isSharedCheck_5295_ = !lean_is_exclusive(v_val_5096_);
if (v_isSharedCheck_5295_ == 0)
{
v___x_5100_ = v_val_5096_;
v_isShared_5101_ = v_isSharedCheck_5295_;
goto v_resetjp_5099_;
}
else
{
lean_inc(v_snd_5098_);
lean_inc(v_fst_5097_);
lean_dec(v_val_5096_);
v___x_5100_ = lean_box(0);
v_isShared_5101_ = v_isSharedCheck_5295_;
goto v_resetjp_5099_;
}
v_resetjp_5099_:
{
lean_object* v_toConstantVal_5102_; lean_object* v_cidx_5103_; lean_object* v_numParams_5104_; lean_object* v_numFields_5105_; lean_object* v___y_5107_; lean_object* v___y_5108_; lean_object* v___y_5109_; lean_object* v___y_5110_; lean_object* v___y_5111_; lean_object* v___y_5112_; uint8_t v___y_5197_; lean_object* v_cidx_5225_; uint8_t v___x_5226_; 
v_toConstantVal_5102_ = lean_ctor_get(v_fst_5089_, 0);
lean_inc_ref(v_toConstantVal_5102_);
v_cidx_5103_ = lean_ctor_get(v_fst_5089_, 2);
lean_inc(v_cidx_5103_);
v_numParams_5104_ = lean_ctor_get(v_fst_5089_, 3);
lean_inc(v_numParams_5104_);
v_numFields_5105_ = lean_ctor_get(v_fst_5089_, 4);
lean_inc(v_numFields_5105_);
lean_dec(v_fst_5089_);
v_cidx_5225_ = lean_ctor_get(v_fst_5097_, 2);
lean_inc(v_cidx_5225_);
lean_dec(v_fst_5097_);
v___x_5226_ = lean_nat_dec_eq(v_cidx_5103_, v_cidx_5225_);
lean_dec(v_cidx_5225_);
lean_dec(v_cidx_5103_);
if (v___x_5226_ == 0)
{
if (v___x_5039_ == 0)
{
lean_dec_ref(v_val_5083_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
v___y_5197_ = v___x_5039_;
goto v___jp_5196_;
}
else
{
lean_object* v_toConstantVal_5227_; lean_object* v_name_5228_; lean_object* v___x_5229_; lean_object* v___x_5230_; lean_object* v___x_5231_; lean_object* v_a_5232_; lean_object* v___x_5233_; lean_object* v___x_5234_; lean_object* v_a_5235_; uint8_t v___x_5253_; 
lean_dec(v_numFields_5105_);
lean_dec(v_numParams_5104_);
lean_dec_ref(v_toConstantVal_5102_);
lean_del_object(v___x_5100_);
lean_dec(v_snd_5098_);
lean_del_object(v___x_5092_);
lean_dec(v_snd_5090_);
v_toConstantVal_5227_ = lean_ctor_get(v_val_5083_, 0);
lean_inc_ref(v_toConstantVal_5227_);
lean_dec_ref(v_val_5083_);
v_name_5228_ = lean_ctor_get(v_toConstantVal_5227_, 0);
lean_inc(v_name_5228_);
lean_dec_ref(v_toConstantVal_5227_);
v___x_5229_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5230_ = l_Lean_Name_str___override(v_name_5228_, v___x_5229_);
lean_inc(v___x_5230_);
v___x_5231_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5230_, v___x_5039_, v_a_5031_);
v_a_5232_ = lean_ctor_get(v___x_5231_, 0);
lean_inc(v_a_5232_);
lean_dec_ref(v___x_5231_);
v___x_5233_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5234_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5233_, v___x_5039_, v_a_5031_);
v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc(v_a_5235_);
lean_dec_ref(v___x_5234_);
v___x_5253_ = lean_unbox(v_a_5232_);
lean_dec(v_a_5232_);
if (v___x_5253_ == 0)
{
lean_dec(v_a_5235_);
lean_dec(v_a_5085_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
goto v___jp_5236_;
}
else
{
uint8_t v___x_5254_; 
v___x_5254_ = lean_unbox(v_a_5235_);
lean_dec(v_a_5235_);
if (v___x_5254_ == 0)
{
lean_dec(v_a_5085_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
goto v___jp_5236_;
}
else
{
lean_object* v___x_5255_; lean_object* v_dummy_5256_; lean_object* v_nargs_5257_; lean_object* v___x_5258_; lean_object* v___x_5259_; lean_object* v___x_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5255_ = l_Lean_mkConst(v___x_5230_, v_us_5077_);
v_dummy_5256_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5257_ = l_Lean_Expr_getAppNumArgs(v_a_5064_);
lean_inc(v_nargs_5257_);
v___x_5258_ = lean_mk_array(v_nargs_5257_, v_dummy_5256_);
v___x_5259_ = lean_unsigned_to_nat(1u);
v___x_5260_ = lean_nat_sub(v_nargs_5257_, v___x_5259_);
lean_dec(v_nargs_5257_);
lean_inc_n(v_a_5064_, 2);
v___x_5261_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5064_, v___x_5258_, v___x_5260_);
v___x_5262_ = l_Lean_mkAppN(v___x_5255_, v___x_5261_);
lean_dec_ref(v___x_5261_);
v___x_5263_ = l_Lean_Meta_getLevel(v_a_5064_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
if (lean_obj_tag(v___x_5263_) == 0)
{
lean_object* v_a_5264_; lean_object* v___x_5266_; uint8_t v_isShared_5267_; uint8_t v_isSharedCheck_5286_; 
v_a_5264_ = lean_ctor_get(v___x_5263_, 0);
v_isSharedCheck_5286_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5266_ = v___x_5263_;
v_isShared_5267_ = v_isSharedCheck_5286_;
goto v_resetjp_5265_;
}
else
{
lean_inc(v_a_5264_);
lean_dec(v___x_5263_);
v___x_5266_ = lean_box(0);
v_isShared_5267_ = v_isSharedCheck_5286_;
goto v_resetjp_5265_;
}
v_resetjp_5265_:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; lean_object* v___x_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; lean_object* v___x_5282_; lean_object* v___x_5284_; 
v___x_5268_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5269_ = lean_box(0);
v___x_5270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5270_, 0, v_a_5085_);
lean_ctor_set(v___x_5270_, 1, v___x_5269_);
v___x_5271_ = l_Lean_mkConst(v___x_5268_, v___x_5270_);
v___x_5272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5272_, 0, v_a_5264_);
lean_ctor_set(v___x_5272_, 1, v___x_5269_);
v___x_5273_ = l_Lean_mkConst(v___x_5233_, v___x_5272_);
v___x_5274_ = lean_unsigned_to_nat(5u);
v___x_5275_ = lean_mk_empty_array_with_capacity(v___x_5274_);
v___x_5276_ = lean_array_push(v___x_5275_, v_a_5064_);
v___x_5277_ = lean_array_push(v___x_5276_, v___x_5262_);
v___x_5278_ = lean_array_push(v___x_5277_, v___x_5048_);
v___x_5279_ = lean_array_push(v___x_5278_, v___x_5049_);
v___x_5280_ = lean_array_push(v___x_5279_, v_h_5027_);
v___x_5281_ = l_Lean_mkAppN(v___x_5273_, v___x_5280_);
lean_dec_ref(v___x_5280_);
v___x_5282_ = l_Lean_mkAppB(v___x_5271_, v_target_5026_, v___x_5281_);
if (v_isShared_5267_ == 0)
{
lean_ctor_set(v___x_5266_, 0, v___x_5282_);
v___x_5284_ = v___x_5266_;
goto v_reusejp_5283_;
}
else
{
lean_object* v_reuseFailAlloc_5285_; 
v_reuseFailAlloc_5285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5285_, 0, v___x_5282_);
v___x_5284_ = v_reuseFailAlloc_5285_;
goto v_reusejp_5283_;
}
v_reusejp_5283_:
{
return v___x_5284_;
}
}
}
else
{
lean_object* v_a_5287_; lean_object* v___x_5289_; uint8_t v_isShared_5290_; uint8_t v_isSharedCheck_5294_; 
lean_dec_ref(v___x_5262_);
lean_dec(v_a_5085_);
lean_dec(v_a_5064_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v_a_5287_ = lean_ctor_get(v___x_5263_, 0);
v_isSharedCheck_5294_ = !lean_is_exclusive(v___x_5263_);
if (v_isSharedCheck_5294_ == 0)
{
v___x_5289_ = v___x_5263_;
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
else
{
lean_inc(v_a_5287_);
lean_dec(v___x_5263_);
v___x_5289_ = lean_box(0);
v_isShared_5290_ = v_isSharedCheck_5294_;
goto v_resetjp_5288_;
}
v_resetjp_5288_:
{
lean_object* v___x_5292_; 
if (v_isShared_5290_ == 0)
{
v___x_5292_ = v___x_5289_;
goto v_reusejp_5291_;
}
else
{
lean_object* v_reuseFailAlloc_5293_; 
v_reuseFailAlloc_5293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5293_, 0, v_a_5287_);
v___x_5292_ = v_reuseFailAlloc_5293_;
goto v_reusejp_5291_;
}
v_reusejp_5291_:
{
return v___x_5292_;
}
}
}
}
}
v___jp_5236_:
{
lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v___x_5239_; lean_object* v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v_a_5245_; lean_object* v___x_5247_; uint8_t v_isShared_5248_; uint8_t v_isSharedCheck_5252_; 
v___x_5237_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5238_ = l_Lean_MessageData_ofName(v___x_5230_);
v___x_5239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5239_, 0, v___x_5237_);
lean_ctor_set(v___x_5239_, 1, v___x_5238_);
v___x_5240_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__23, &l_Lean_Meta_mkNoConfusion___closed__23_once, _init_l_Lean_Meta_mkNoConfusion___closed__23);
v___x_5241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5241_, 0, v___x_5239_);
lean_ctor_set(v___x_5241_, 1, v___x_5240_);
v___x_5242_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__24, &l_Lean_Meta_mkNoConfusion___closed__24_once, _init_l_Lean_Meta_mkNoConfusion___closed__24);
v___x_5243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5241_);
lean_ctor_set(v___x_5243_, 1, v___x_5242_);
v___x_5244_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5243_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
v_a_5245_ = lean_ctor_get(v___x_5244_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5244_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5247_ = v___x_5244_;
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
else
{
lean_inc(v_a_5245_);
lean_dec(v___x_5244_);
v___x_5247_ = lean_box(0);
v_isShared_5248_ = v_isSharedCheck_5252_;
goto v_resetjp_5246_;
}
v_resetjp_5246_:
{
lean_object* v___x_5250_; 
if (v_isShared_5248_ == 0)
{
v___x_5250_ = v___x_5247_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v_a_5245_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
}
}
else
{
lean_dec_ref(v_val_5083_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
v___y_5197_ = v___x_5080_;
goto v___jp_5196_;
}
v___jp_5106_:
{
lean_object* v___x_5113_; 
lean_inc(v___y_5107_);
v___x_5113_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5107_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
if (lean_obj_tag(v___x_5113_) == 0)
{
lean_object* v_a_5114_; lean_object* v_nargs_5115_; lean_object* v_type_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5185_; 
v_a_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc(v_a_5114_);
lean_dec_ref_known(v___x_5113_, 1);
v_nargs_5115_ = l_Lean_Expr_getAppNumArgs(v_a_5064_);
v_type_5116_ = lean_ctor_get(v_a_5114_, 2);
v_isSharedCheck_5185_ = !lean_is_exclusive(v_a_5114_);
if (v_isSharedCheck_5185_ == 0)
{
lean_object* v_unused_5186_; lean_object* v_unused_5187_; 
v_unused_5186_ = lean_ctor_get(v_a_5114_, 1);
lean_dec(v_unused_5186_);
v_unused_5187_ = lean_ctor_get(v_a_5114_, 0);
lean_dec(v_unused_5187_);
v___x_5118_ = v_a_5114_;
v_isShared_5119_ = v_isSharedCheck_5185_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_type_5116_);
lean_dec(v_a_5114_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5185_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v_dummy_5120_; lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v___x_5125_; lean_object* v_start_5126_; lean_object* v_stop_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; lean_object* v___x_5134_; lean_object* v___x_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; uint8_t v___x_5141_; 
v_dummy_5120_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
lean_inc(v_nargs_5115_);
v___x_5121_ = lean_mk_array(v_nargs_5115_, v_dummy_5120_);
v___x_5122_ = lean_unsigned_to_nat(1u);
v___x_5123_ = lean_nat_sub(v_nargs_5115_, v___x_5122_);
lean_dec(v_nargs_5115_);
v___x_5124_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5064_, v___x_5121_, v___x_5123_);
lean_inc_n(v_numParams_5104_, 2);
lean_inc(v___y_5108_);
v___x_5125_ = l_Array_toSubarray___redArg(v___x_5124_, v___y_5108_, v_numParams_5104_);
v_start_5126_ = lean_ctor_get(v___x_5125_, 1);
lean_inc(v_start_5126_);
v_stop_5127_ = lean_ctor_get(v___x_5125_, 2);
lean_inc(v_stop_5127_);
v___x_5128_ = lean_array_get_size(v_snd_5090_);
v___x_5129_ = l_Array_toSubarray___redArg(v_snd_5090_, v_numParams_5104_, v___x_5128_);
v___x_5130_ = lean_array_get_size(v_snd_5098_);
v___x_5131_ = l_Subarray_copy___redArg(v___x_5129_);
v___x_5132_ = l_Array_toSubarray___redArg(v_snd_5098_, v_numParams_5104_, v___x_5130_);
v___x_5133_ = l_Subarray_copy___redArg(v___x_5132_);
v___x_5134_ = l_Lean_Expr_getNumHeadForalls(v_type_5116_);
lean_dec_ref(v_type_5116_);
v___x_5135_ = lean_nat_sub(v_stop_5127_, v_start_5126_);
lean_dec(v_start_5126_);
lean_dec(v_stop_5127_);
v___x_5136_ = lean_array_get_size(v___x_5131_);
v___x_5137_ = lean_nat_add(v___x_5135_, v___x_5136_);
lean_dec(v___x_5135_);
v___x_5138_ = lean_array_get_size(v___x_5133_);
v___x_5139_ = lean_nat_add(v___x_5137_, v___x_5138_);
lean_dec(v___x_5137_);
v___x_5140_ = lean_nat_add(v___x_5139_, v___x_5038_);
lean_dec(v___x_5139_);
v___x_5141_ = lean_nat_dec_le(v___x_5140_, v___x_5134_);
if (v___x_5141_ == 0)
{
lean_object* v___x_5142_; lean_object* v___x_5143_; 
lean_dec(v___x_5140_);
lean_dec(v___x_5134_);
lean_dec_ref(v___x_5133_);
lean_dec_ref(v___x_5131_);
lean_dec_ref(v___x_5125_);
lean_del_object(v___x_5118_);
lean_dec(v___y_5108_);
lean_dec(v___y_5107_);
lean_del_object(v___x_5100_);
lean_dec(v_a_5085_);
lean_dec(v_us_5077_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v___x_5142_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__14, &l_Lean_Meta_mkNoConfusion___closed__14_once, _init_l_Lean_Meta_mkNoConfusion___closed__14);
v___x_5143_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5142_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
return v___x_5143_;
}
else
{
lean_object* v___x_5145_; 
if (v_isShared_5101_ == 0)
{
lean_ctor_set_tag(v___x_5100_, 1);
lean_ctor_set(v___x_5100_, 1, v_us_5077_);
lean_ctor_set(v___x_5100_, 0, v_a_5085_);
v___x_5145_ = v___x_5100_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5085_);
lean_ctor_set(v_reuseFailAlloc_5184_, 1, v_us_5077_);
v___x_5145_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5149_; lean_object* v___x_5150_; lean_object* v___x_5151_; lean_object* v___x_5152_; lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5156_; 
v___x_5146_ = l_Lean_mkConst(v___y_5107_, v___x_5145_);
v___x_5147_ = l_Subarray_copy___redArg(v___x_5125_);
v___x_5148_ = l_Lean_mkAppN(v___x_5146_, v___x_5147_);
lean_dec_ref(v___x_5147_);
v___x_5149_ = lean_mk_empty_array_with_capacity(v___x_5122_);
v___x_5150_ = lean_array_push(v___x_5149_, v_target_5026_);
v___x_5151_ = l_Array_append___redArg(v___x_5150_, v___x_5131_);
lean_dec_ref(v___x_5131_);
v___x_5152_ = l_Array_append___redArg(v___x_5151_, v___x_5133_);
lean_dec_ref(v___x_5133_);
v___x_5153_ = l_Lean_mkAppN(v___x_5148_, v___x_5152_);
lean_dec_ref(v___x_5152_);
v___x_5154_ = lean_nat_sub(v___x_5134_, v___x_5140_);
lean_dec(v___x_5140_);
lean_dec(v___x_5134_);
lean_inc(v___y_5108_);
if (v_isShared_5119_ == 0)
{
lean_ctor_set(v___x_5118_, 2, v___x_5122_);
lean_ctor_set(v___x_5118_, 1, v___x_5154_);
lean_ctor_set(v___x_5118_, 0, v___y_5108_);
v___x_5156_ = v___x_5118_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___y_5108_);
lean_ctor_set(v_reuseFailAlloc_5183_, 1, v___x_5154_);
lean_ctor_set(v_reuseFailAlloc_5183_, 2, v___x_5122_);
v___x_5156_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
lean_object* v___x_5157_; 
v___x_5157_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5156_, v___x_5153_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
lean_dec_ref(v___x_5156_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v_a_5158_; lean_object* v___x_5159_; 
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc_n(v_a_5158_, 2);
lean_dec_ref_known(v___x_5157_, 1);
lean_inc(v___y_5112_);
lean_inc_ref(v___y_5111_);
lean_inc(v___y_5110_);
lean_inc_ref(v___y_5109_);
v___x_5159_ = lean_infer_type(v_a_5158_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
if (lean_obj_tag(v___x_5159_) == 0)
{
lean_object* v_a_5160_; lean_object* v___x_5161_; 
v_a_5160_ = lean_ctor_get(v___x_5159_, 0);
lean_inc(v_a_5160_);
lean_dec_ref_known(v___x_5159_, 1);
v___x_5161_ = l_Lean_Meta_whnfForall(v_a_5160_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
if (lean_obj_tag(v___x_5161_) == 0)
{
lean_object* v_a_5162_; lean_object* v___x_5164_; uint8_t v_isShared_5165_; uint8_t v_isSharedCheck_5182_; 
v_a_5162_ = lean_ctor_get(v___x_5161_, 0);
v_isSharedCheck_5182_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5182_ == 0)
{
v___x_5164_ = v___x_5161_;
v_isShared_5165_ = v_isSharedCheck_5182_;
goto v_resetjp_5163_;
}
else
{
lean_inc(v_a_5162_);
lean_dec(v___x_5161_);
v___x_5164_ = lean_box(0);
v_isShared_5165_ = v_isSharedCheck_5182_;
goto v_resetjp_5163_;
}
v_resetjp_5163_:
{
lean_object* v___x_5166_; uint8_t v___x_5167_; 
v___x_5166_ = l_Lean_Expr_bindingDomain_x21(v_a_5162_);
lean_dec(v_a_5162_);
v___x_5167_ = l_Lean_Expr_isHEq(v___x_5166_);
lean_dec_ref(v___x_5166_);
if (v___x_5167_ == 0)
{
lean_object* v___x_5168_; lean_object* v___x_5170_; 
v___x_5168_ = l_Lean_Expr_app___override(v_a_5158_, v_h_5027_);
if (v_isShared_5165_ == 0)
{
lean_ctor_set(v___x_5164_, 0, v___x_5168_);
v___x_5170_ = v___x_5164_;
goto v_reusejp_5169_;
}
else
{
lean_object* v_reuseFailAlloc_5171_; 
v_reuseFailAlloc_5171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5171_, 0, v___x_5168_);
v___x_5170_ = v_reuseFailAlloc_5171_;
goto v_reusejp_5169_;
}
v_reusejp_5169_:
{
return v___x_5170_;
}
}
else
{
lean_object* v___x_5172_; 
lean_del_object(v___x_5164_);
v___x_5172_ = l_Lean_Meta_mkHEqOfEq(v_h_5027_, v___y_5109_, v___y_5110_, v___y_5111_, v___y_5112_);
if (lean_obj_tag(v___x_5172_) == 0)
{
lean_object* v_a_5173_; lean_object* v___x_5175_; uint8_t v_isShared_5176_; uint8_t v_isSharedCheck_5181_; 
v_a_5173_ = lean_ctor_get(v___x_5172_, 0);
v_isSharedCheck_5181_ = !lean_is_exclusive(v___x_5172_);
if (v_isSharedCheck_5181_ == 0)
{
v___x_5175_ = v___x_5172_;
v_isShared_5176_ = v_isSharedCheck_5181_;
goto v_resetjp_5174_;
}
else
{
lean_inc(v_a_5173_);
lean_dec(v___x_5172_);
v___x_5175_ = lean_box(0);
v_isShared_5176_ = v_isSharedCheck_5181_;
goto v_resetjp_5174_;
}
v_resetjp_5174_:
{
lean_object* v___x_5177_; lean_object* v___x_5179_; 
v___x_5177_ = l_Lean_Expr_app___override(v_a_5158_, v_a_5173_);
if (v_isShared_5176_ == 0)
{
lean_ctor_set(v___x_5175_, 0, v___x_5177_);
v___x_5179_ = v___x_5175_;
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
}
else
{
lean_dec(v_a_5158_);
return v___x_5172_;
}
}
}
}
else
{
lean_dec(v_a_5158_);
lean_dec_ref(v_h_5027_);
return v___x_5161_;
}
}
else
{
lean_dec(v_a_5158_);
lean_dec_ref(v_h_5027_);
return v___x_5159_;
}
}
else
{
lean_dec_ref(v_h_5027_);
return v___x_5157_;
}
}
}
}
}
}
else
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5195_; 
lean_dec(v___y_5108_);
lean_dec(v___y_5107_);
lean_dec(v_numParams_5104_);
lean_del_object(v___x_5100_);
lean_dec(v_snd_5098_);
lean_dec(v_snd_5090_);
lean_dec(v_a_5085_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v_a_5188_ = lean_ctor_get(v___x_5113_, 0);
v_isSharedCheck_5195_ = !lean_is_exclusive(v___x_5113_);
if (v_isSharedCheck_5195_ == 0)
{
v___x_5190_ = v___x_5113_;
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5113_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5195_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
lean_object* v___x_5193_; 
if (v_isShared_5191_ == 0)
{
v___x_5193_ = v___x_5190_;
goto v_reusejp_5192_;
}
else
{
lean_object* v_reuseFailAlloc_5194_; 
v_reuseFailAlloc_5194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5194_, 0, v_a_5188_);
v___x_5193_ = v_reuseFailAlloc_5194_;
goto v_reusejp_5192_;
}
v_reusejp_5192_:
{
return v___x_5193_;
}
}
}
}
v___jp_5196_:
{
lean_object* v___x_5198_; uint8_t v___x_5199_; 
v___x_5198_ = lean_unsigned_to_nat(0u);
v___x_5199_ = lean_nat_dec_eq(v_numFields_5105_, v___x_5198_);
lean_dec(v_numFields_5105_);
if (v___x_5199_ == 0)
{
lean_object* v_name_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v_a_5204_; uint8_t v___x_5205_; 
v_name_5200_ = lean_ctor_get(v_toConstantVal_5102_, 0);
lean_inc(v_name_5200_);
lean_dec_ref(v_toConstantVal_5102_);
v___x_5201_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5202_ = l_Lean_Name_str___override(v_name_5200_, v___x_5201_);
lean_inc(v___x_5202_);
v___x_5203_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5202_, v___x_5039_, v_a_5031_);
v_a_5204_ = lean_ctor_get(v___x_5203_, 0);
lean_inc(v_a_5204_);
lean_dec_ref(v___x_5203_);
v___x_5205_ = lean_unbox(v_a_5204_);
lean_dec(v_a_5204_);
if (v___x_5205_ == 0)
{
lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5209_; 
lean_dec(v_numParams_5104_);
lean_del_object(v___x_5100_);
lean_dec(v_snd_5098_);
lean_dec(v_snd_5090_);
lean_dec(v_a_5085_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v___x_5206_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5207_ = l_Lean_MessageData_ofName(v___x_5202_);
if (v_isShared_5093_ == 0)
{
lean_ctor_set_tag(v___x_5092_, 7);
lean_ctor_set(v___x_5092_, 1, v___x_5207_);
lean_ctor_set(v___x_5092_, 0, v___x_5206_);
v___x_5209_ = v___x_5092_;
goto v_reusejp_5208_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v___x_5206_);
lean_ctor_set(v_reuseFailAlloc_5219_, 1, v___x_5207_);
v___x_5209_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5208_;
}
v_reusejp_5208_:
{
lean_object* v___x_5210_; lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5218_; 
v___x_5210_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5209_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5218_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5218_ == 0)
{
v___x_5213_ = v___x_5210_;
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5210_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5218_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v___x_5216_; 
if (v_isShared_5214_ == 0)
{
v___x_5216_ = v___x_5213_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5217_; 
v_reuseFailAlloc_5217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5217_, 0, v_a_5211_);
v___x_5216_ = v_reuseFailAlloc_5217_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
return v___x_5216_;
}
}
}
}
else
{
lean_del_object(v___x_5092_);
v___y_5107_ = v___x_5202_;
v___y_5108_ = v___x_5198_;
v___y_5109_ = v_a_5028_;
v___y_5110_ = v_a_5029_;
v___y_5111_ = v_a_5030_;
v___y_5112_ = v_a_5031_;
goto v___jp_5106_;
}
}
else
{
lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___f_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; 
lean_dec(v_numParams_5104_);
lean_dec_ref(v_toConstantVal_5102_);
lean_del_object(v___x_5100_);
lean_dec(v_snd_5098_);
lean_del_object(v___x_5092_);
lean_dec(v_snd_5090_);
lean_dec(v_a_5085_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v_h_5027_);
v___x_5220_ = lean_box(v___y_5197_);
v___x_5221_ = lean_box(v___x_5199_);
v___f_5222_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5222_, 0, v___x_5220_);
lean_closure_set(v___f_5222_, 1, v___x_5221_);
v___x_5223_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5224_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5223_, v_target_5026_, v___f_5222_, v_a_5028_, v_a_5029_, v_a_5030_, v_a_5031_);
return v___x_5224_;
}
}
}
}
else
{
lean_dec(v_a_5095_);
lean_del_object(v___x_5092_);
lean_dec(v_snd_5090_);
lean_dec(v_fst_5089_);
lean_dec(v_a_5085_);
lean_dec_ref(v_val_5083_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v___y_5051_ = v_a_5028_;
v___y_5052_ = v_a_5029_;
v___y_5053_ = v_a_5030_;
v___y_5054_ = v_a_5031_;
goto v___jp_5050_;
}
}
else
{
lean_object* v_a_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5303_; 
lean_del_object(v___x_5092_);
lean_dec(v_snd_5090_);
lean_dec(v_fst_5089_);
lean_dec(v_a_5085_);
lean_dec_ref(v_val_5083_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v_a_5296_ = lean_ctor_get(v___x_5094_, 0);
v_isSharedCheck_5303_ = !lean_is_exclusive(v___x_5094_);
if (v_isSharedCheck_5303_ == 0)
{
v___x_5298_ = v___x_5094_;
v_isShared_5299_ = v_isSharedCheck_5303_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_a_5296_);
lean_dec(v___x_5094_);
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
else
{
lean_dec(v_a_5087_);
lean_dec(v_a_5085_);
lean_dec_ref(v_val_5083_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v___y_5051_ = v_a_5028_;
v___y_5052_ = v_a_5029_;
v___y_5053_ = v_a_5030_;
v___y_5054_ = v_a_5031_;
goto v___jp_5050_;
}
}
else
{
lean_object* v_a_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5312_; 
lean_dec(v_a_5085_);
lean_dec_ref(v_val_5083_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v_a_5305_ = lean_ctor_get(v___x_5086_, 0);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5086_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5307_ = v___x_5086_;
v_isShared_5308_ = v_isSharedCheck_5312_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_a_5305_);
lean_dec(v___x_5086_);
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
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5320_; 
lean_dec_ref(v_val_5083_);
lean_dec(v_us_5077_);
lean_dec(v_a_5064_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v_a_5313_ = lean_ctor_get(v___x_5084_, 0);
v_isSharedCheck_5320_ = !lean_is_exclusive(v___x_5084_);
if (v_isSharedCheck_5320_ == 0)
{
v___x_5315_ = v___x_5084_;
v_isShared_5316_ = v_isSharedCheck_5320_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___x_5084_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5320_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v___x_5318_; 
if (v_isShared_5316_ == 0)
{
v___x_5318_ = v___x_5315_;
goto v_reusejp_5317_;
}
else
{
lean_object* v_reuseFailAlloc_5319_; 
v_reuseFailAlloc_5319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5319_, 0, v_a_5313_);
v___x_5318_ = v_reuseFailAlloc_5319_;
goto v_reusejp_5317_;
}
v_reusejp_5317_:
{
return v___x_5318_;
}
}
}
}
else
{
lean_dec(v_val_5082_);
lean_dec(v_us_5077_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v___y_5066_ = v_a_5028_;
v___y_5067_ = v_a_5029_;
v___y_5068_ = v_a_5030_;
v___y_5069_ = v_a_5031_;
goto v___jp_5065_;
}
}
}
else
{
lean_dec_ref(v___x_5075_);
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
v___y_5066_ = v_a_5028_;
v___y_5067_ = v_a_5029_;
v___y_5068_ = v_a_5030_;
v___y_5069_ = v_a_5031_;
goto v___jp_5065_;
}
v___jp_5065_:
{
lean_object* v___x_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; 
v___x_5070_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5071_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5072_ = l_Lean_indentExpr(v_a_5064_);
v___x_5073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5073_, 0, v___x_5071_);
lean_ctor_set(v___x_5073_, 1, v___x_5072_);
v___x_5074_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5070_, v___x_5073_, v___y_5066_, v___y_5067_, v___y_5068_, v___y_5069_);
return v___x_5074_;
}
}
else
{
lean_dec_ref(v___x_5049_);
lean_dec_ref(v___x_5048_);
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
return v___x_5063_;
}
v___jp_5050_:
{
lean_object* v___x_5055_; lean_object* v___x_5056_; lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5055_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__6, &l_Lean_Meta_mkNoConfusion___closed__6_once, _init_l_Lean_Meta_mkNoConfusion___closed__6);
v___x_5056_ = l_Lean_MessageData_ofExpr(v___x_5048_);
v___x_5057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5057_, 0, v___x_5055_);
lean_ctor_set(v___x_5057_, 1, v___x_5056_);
v___x_5058_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__8, &l_Lean_Meta_mkNoConfusion___closed__8_once, _init_l_Lean_Meta_mkNoConfusion___closed__8);
v___x_5059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5059_, 0, v___x_5057_);
lean_ctor_set(v___x_5059_, 1, v___x_5058_);
v___x_5060_ = l_Lean_MessageData_ofExpr(v___x_5049_);
v___x_5061_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5061_, 0, v___x_5059_);
lean_ctor_set(v___x_5061_, 1, v___x_5060_);
v___x_5062_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5061_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_);
return v___x_5062_;
}
}
}
else
{
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
return v___x_5035_;
}
}
else
{
lean_dec_ref(v_h_5027_);
lean_dec_ref(v_target_5026_);
return v___x_5033_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5321_, lean_object* v_h_5322_, lean_object* v_a_5323_, lean_object* v_a_5324_, lean_object* v_a_5325_, lean_object* v_a_5326_, lean_object* v_a_5327_){
_start:
{
lean_object* v_res_5328_; 
v_res_5328_ = l_Lean_Meta_mkNoConfusion(v_target_5321_, v_h_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_);
lean_dec(v_a_5326_);
lean_dec_ref(v_a_5325_);
lean_dec(v_a_5324_);
lean_dec_ref(v_a_5323_);
return v_res_5328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5329_, lean_object* v_b_5330_, lean_object* v_i_5331_, lean_object* v_hs_5332_, lean_object* v_hl_5333_, lean_object* v___y_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_){
_start:
{
lean_object* v___x_5339_; 
v___x_5339_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5329_, v_b_5330_, v_i_5331_, v___y_5334_, v___y_5335_, v___y_5336_, v___y_5337_);
return v___x_5339_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5340_, lean_object* v_b_5341_, lean_object* v_i_5342_, lean_object* v_hs_5343_, lean_object* v_hl_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5340_, v_b_5341_, v_i_5342_, v_hs_5343_, v_hl_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec_ref(v_range_5340_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5351_, lean_object* v_name_5352_, uint8_t v_bi_5353_, lean_object* v_type_5354_, lean_object* v_k_5355_, uint8_t v_kind_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_, lean_object* v___y_5359_, lean_object* v___y_5360_){
_start:
{
lean_object* v___x_5362_; 
v___x_5362_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5352_, v_bi_5353_, v_type_5354_, v_k_5355_, v_kind_5356_, v___y_5357_, v___y_5358_, v___y_5359_, v___y_5360_);
return v___x_5362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5363_, lean_object* v_name_5364_, lean_object* v_bi_5365_, lean_object* v_type_5366_, lean_object* v_k_5367_, lean_object* v_kind_5368_, lean_object* v___y_5369_, lean_object* v___y_5370_, lean_object* v___y_5371_, lean_object* v___y_5372_, lean_object* v___y_5373_){
_start:
{
uint8_t v_bi_boxed_5374_; uint8_t v_kind_boxed_5375_; lean_object* v_res_5376_; 
v_bi_boxed_5374_ = lean_unbox(v_bi_5365_);
v_kind_boxed_5375_ = lean_unbox(v_kind_5368_);
v_res_5376_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5363_, v_name_5364_, v_bi_boxed_5374_, v_type_5366_, v_k_5367_, v_kind_boxed_5375_, v___y_5369_, v___y_5370_, v___y_5371_, v___y_5372_);
lean_dec(v___y_5372_);
lean_dec_ref(v___y_5371_);
lean_dec(v___y_5370_);
lean_dec_ref(v___y_5369_);
return v_res_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5377_, lean_object* v_name_5378_, lean_object* v_type_5379_, lean_object* v_k_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_, lean_object* v___y_5383_, lean_object* v___y_5384_){
_start:
{
lean_object* v___x_5386_; 
v___x_5386_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5378_, v_type_5379_, v_k_5380_, v___y_5381_, v___y_5382_, v___y_5383_, v___y_5384_);
return v___x_5386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5387_, lean_object* v_name_5388_, lean_object* v_type_5389_, lean_object* v_k_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5387_, v_name_5388_, v_type_5389_, v_k_5390_, v___y_5391_, v___y_5392_, v___y_5393_, v___y_5394_);
lean_dec(v___y_5394_);
lean_dec_ref(v___y_5393_);
lean_dec(v___y_5392_);
lean_dec_ref(v___y_5391_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5402_, lean_object* v_e_5403_, lean_object* v_a_5404_, lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_){
_start:
{
lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; lean_object* v___x_5413_; lean_object* v___x_5414_; lean_object* v___x_5415_; lean_object* v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5409_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5410_, 0, v_monad_5402_);
v___x_5411_ = lean_box(0);
v___x_5412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5412_, 0, v_e_5403_);
v___x_5413_ = lean_unsigned_to_nat(4u);
v___x_5414_ = lean_mk_empty_array_with_capacity(v___x_5413_);
v___x_5415_ = lean_array_push(v___x_5414_, v___x_5410_);
v___x_5416_ = lean_array_push(v___x_5415_, v___x_5411_);
v___x_5417_ = lean_array_push(v___x_5416_, v___x_5411_);
v___x_5418_ = lean_array_push(v___x_5417_, v___x_5412_);
v___x_5419_ = l_Lean_Meta_mkAppOptM(v___x_5409_, v___x_5418_, v_a_5404_, v_a_5405_, v_a_5406_, v_a_5407_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5420_, lean_object* v_e_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_, lean_object* v_a_5424_, lean_object* v_a_5425_, lean_object* v_a_5426_){
_start:
{
lean_object* v_res_5427_; 
v_res_5427_ = l_Lean_Meta_mkPure(v_monad_5420_, v_e_5421_, v_a_5422_, v_a_5423_, v_a_5424_, v_a_5425_);
lean_dec(v_a_5425_);
lean_dec_ref(v_a_5424_);
lean_dec(v_a_5423_);
lean_dec_ref(v_a_5422_);
return v_res_5427_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5437_; lean_object* v___x_5438_; 
v___x_5437_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5438_ = l_Lean_MessageData_ofFormat(v___x_5437_);
return v___x_5438_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5442_; lean_object* v___x_5443_; 
v___x_5442_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5443_ = l_Lean_MessageData_ofFormat(v___x_5442_);
return v___x_5443_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5447_; lean_object* v___x_5448_; 
v___x_5447_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5448_ = l_Lean_MessageData_ofFormat(v___x_5447_);
return v___x_5448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5449_, lean_object* v_fieldName_5450_, lean_object* v_a_5451_, lean_object* v_a_5452_, lean_object* v_a_5453_, lean_object* v_a_5454_){
_start:
{
lean_object* v___x_5456_; 
lean_inc(v_a_5454_);
lean_inc_ref(v_a_5453_);
lean_inc(v_a_5452_);
lean_inc_ref(v_a_5451_);
lean_inc_ref(v_s_5449_);
v___x_5456_ = lean_infer_type(v_s_5449_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_);
if (lean_obj_tag(v___x_5456_) == 0)
{
lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5553_; 
v_a_5457_ = lean_ctor_get(v___x_5456_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v___x_5456_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5459_ = v___x_5456_;
v_isShared_5460_ = v_isSharedCheck_5553_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_dec(v___x_5456_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5553_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5461_; 
lean_inc(v_a_5454_);
lean_inc_ref(v_a_5453_);
lean_inc(v_a_5452_);
lean_inc_ref(v_a_5451_);
v___x_5461_ = lean_whnf(v_a_5457_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_);
if (lean_obj_tag(v___x_5461_) == 0)
{
lean_object* v_a_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5552_; 
v_a_5462_ = lean_ctor_get(v___x_5461_, 0);
v_isSharedCheck_5552_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5552_ == 0)
{
v___x_5464_ = v___x_5461_;
v_isShared_5465_ = v_isSharedCheck_5552_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_a_5462_);
lean_dec(v___x_5461_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5552_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___y_5467_; lean_object* v___y_5468_; lean_object* v___y_5469_; lean_object* v___y_5470_; lean_object* v___x_5485_; 
v___x_5485_ = l_Lean_Expr_getAppFn(v_a_5462_);
if (lean_obj_tag(v___x_5485_) == 4)
{
lean_object* v_declName_5486_; lean_object* v_us_5487_; lean_object* v___x_5488_; lean_object* v_env_5489_; lean_object* v___y_5491_; lean_object* v___y_5492_; lean_object* v___y_5493_; lean_object* v___y_5494_; uint8_t v___x_5533_; 
v_declName_5486_ = lean_ctor_get(v___x_5485_, 0);
lean_inc_n(v_declName_5486_, 2);
v_us_5487_ = lean_ctor_get(v___x_5485_, 1);
lean_inc(v_us_5487_);
lean_dec_ref_known(v___x_5485_, 2);
v___x_5488_ = lean_st_ref_get(v_a_5454_);
v_env_5489_ = lean_ctor_get(v___x_5488_, 0);
lean_inc_ref_n(v_env_5489_, 2);
lean_dec(v___x_5488_);
v___x_5533_ = l_Lean_isStructure(v_env_5489_, v_declName_5486_);
if (v___x_5533_ == 0)
{
lean_object* v___x_5534_; lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v___x_5537_; lean_object* v___x_5538_; 
v___x_5534_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5535_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5462_);
lean_inc_ref(v_s_5449_);
v___x_5536_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5449_, v_a_5462_);
v___x_5537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5535_);
lean_ctor_set(v___x_5537_, 1, v___x_5536_);
v___x_5538_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5534_, v___x_5537_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_);
if (lean_obj_tag(v___x_5538_) == 0)
{
lean_dec_ref_known(v___x_5538_, 1);
v___y_5491_ = v_a_5451_;
v___y_5492_ = v_a_5452_;
v___y_5493_ = v_a_5453_;
v___y_5494_ = v_a_5454_;
goto v___jp_5490_;
}
else
{
lean_object* v_a_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5546_; 
lean_dec_ref(v_env_5489_);
lean_dec(v_us_5487_);
lean_dec(v_declName_5486_);
lean_del_object(v___x_5464_);
lean_dec(v_a_5462_);
lean_del_object(v___x_5459_);
lean_dec(v_fieldName_5450_);
lean_dec_ref(v_s_5449_);
v_a_5539_ = lean_ctor_get(v___x_5538_, 0);
v_isSharedCheck_5546_ = !lean_is_exclusive(v___x_5538_);
if (v_isSharedCheck_5546_ == 0)
{
v___x_5541_ = v___x_5538_;
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_a_5539_);
lean_dec(v___x_5538_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5546_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5544_; 
if (v_isShared_5542_ == 0)
{
v___x_5544_ = v___x_5541_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5545_; 
v_reuseFailAlloc_5545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5545_, 0, v_a_5539_);
v___x_5544_ = v_reuseFailAlloc_5545_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
return v___x_5544_;
}
}
}
}
else
{
v___y_5491_ = v_a_5451_;
v___y_5492_ = v_a_5452_;
v___y_5493_ = v_a_5453_;
v___y_5494_ = v_a_5454_;
goto v___jp_5490_;
}
v___jp_5490_:
{
lean_object* v___x_5495_; 
lean_inc(v_fieldName_5450_);
lean_inc(v_declName_5486_);
lean_inc_ref(v_env_5489_);
v___x_5495_ = l_Lean_getProjFnForField_x3f(v_env_5489_, v_declName_5486_, v_fieldName_5450_);
if (lean_obj_tag(v___x_5495_) == 0)
{
lean_object* v___x_5496_; lean_object* v___x_5497_; size_t v_sz_5498_; size_t v___x_5499_; lean_object* v___x_5500_; 
lean_dec(v_us_5487_);
lean_del_object(v___x_5464_);
lean_inc(v_declName_5486_);
lean_inc_ref(v_env_5489_);
v___x_5496_ = l_Lean_getStructureFields(v_env_5489_, v_declName_5486_);
v___x_5497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5498_ = lean_array_size(v___x_5496_);
v___x_5499_ = ((size_t)0ULL);
lean_inc(v_fieldName_5450_);
lean_inc_ref(v_s_5449_);
v___x_5500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5489_, v_declName_5486_, v_s_5449_, v_fieldName_5450_, v___x_5496_, v_sz_5498_, v___x_5499_, v___x_5497_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
lean_dec_ref(v___x_5496_);
if (lean_obj_tag(v___x_5500_) == 0)
{
lean_object* v_a_5501_; lean_object* v___x_5503_; uint8_t v_isShared_5504_; uint8_t v_isSharedCheck_5511_; 
v_a_5501_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5511_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5511_ == 0)
{
v___x_5503_ = v___x_5500_;
v_isShared_5504_ = v_isSharedCheck_5511_;
goto v_resetjp_5502_;
}
else
{
lean_inc(v_a_5501_);
lean_dec(v___x_5500_);
v___x_5503_ = lean_box(0);
v_isShared_5504_ = v_isSharedCheck_5511_;
goto v_resetjp_5502_;
}
v_resetjp_5502_:
{
lean_object* v_fst_5505_; 
v_fst_5505_ = lean_ctor_get(v_a_5501_, 0);
lean_inc(v_fst_5505_);
lean_dec(v_a_5501_);
if (lean_obj_tag(v_fst_5505_) == 0)
{
lean_del_object(v___x_5503_);
v___y_5467_ = v___y_5494_;
v___y_5468_ = v___y_5492_;
v___y_5469_ = v___y_5493_;
v___y_5470_ = v___y_5491_;
goto v___jp_5466_;
}
else
{
lean_object* v_val_5506_; 
v_val_5506_ = lean_ctor_get(v_fst_5505_, 0);
lean_inc(v_val_5506_);
lean_dec_ref_known(v_fst_5505_, 1);
if (lean_obj_tag(v_val_5506_) == 0)
{
lean_del_object(v___x_5503_);
v___y_5467_ = v___y_5494_;
v___y_5468_ = v___y_5492_;
v___y_5469_ = v___y_5493_;
v___y_5470_ = v___y_5491_;
goto v___jp_5466_;
}
else
{
lean_object* v_val_5507_; lean_object* v___x_5509_; 
lean_dec(v_a_5462_);
lean_del_object(v___x_5459_);
lean_dec(v_fieldName_5450_);
lean_dec_ref(v_s_5449_);
v_val_5507_ = lean_ctor_get(v_val_5506_, 0);
lean_inc(v_val_5507_);
lean_dec_ref_known(v_val_5506_, 1);
if (v_isShared_5504_ == 0)
{
lean_ctor_set(v___x_5503_, 0, v_val_5507_);
v___x_5509_ = v___x_5503_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_val_5507_);
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
}
else
{
lean_object* v_a_5512_; lean_object* v___x_5514_; uint8_t v_isShared_5515_; uint8_t v_isSharedCheck_5519_; 
lean_dec(v_a_5462_);
lean_del_object(v___x_5459_);
lean_dec(v_fieldName_5450_);
lean_dec_ref(v_s_5449_);
v_a_5512_ = lean_ctor_get(v___x_5500_, 0);
v_isSharedCheck_5519_ = !lean_is_exclusive(v___x_5500_);
if (v_isSharedCheck_5519_ == 0)
{
v___x_5514_ = v___x_5500_;
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
else
{
lean_inc(v_a_5512_);
lean_dec(v___x_5500_);
v___x_5514_ = lean_box(0);
v_isShared_5515_ = v_isSharedCheck_5519_;
goto v_resetjp_5513_;
}
v_resetjp_5513_:
{
lean_object* v___x_5517_; 
if (v_isShared_5515_ == 0)
{
v___x_5517_ = v___x_5514_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5518_; 
v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
v___x_5517_ = v_reuseFailAlloc_5518_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
return v___x_5517_;
}
}
}
}
else
{
lean_object* v_val_5520_; lean_object* v_dummy_5521_; lean_object* v_nargs_5522_; lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v___x_5525_; lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___x_5528_; lean_object* v___x_5529_; lean_object* v___x_5531_; 
lean_dec_ref(v_env_5489_);
lean_dec(v_declName_5486_);
lean_del_object(v___x_5459_);
lean_dec(v_fieldName_5450_);
v_val_5520_ = lean_ctor_get(v___x_5495_, 0);
lean_inc(v_val_5520_);
lean_dec_ref_known(v___x_5495_, 1);
v_dummy_5521_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5522_ = l_Lean_Expr_getAppNumArgs(v_a_5462_);
lean_inc(v_nargs_5522_);
v___x_5523_ = lean_mk_array(v_nargs_5522_, v_dummy_5521_);
v___x_5524_ = lean_unsigned_to_nat(1u);
v___x_5525_ = lean_nat_sub(v_nargs_5522_, v___x_5524_);
lean_dec(v_nargs_5522_);
v___x_5526_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5462_, v___x_5523_, v___x_5525_);
v___x_5527_ = l_Lean_mkConst(v_val_5520_, v_us_5487_);
v___x_5528_ = l_Lean_mkAppN(v___x_5527_, v___x_5526_);
lean_dec_ref(v___x_5526_);
v___x_5529_ = l_Lean_Expr_app___override(v___x_5528_, v_s_5449_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 0, v___x_5529_);
v___x_5531_ = v___x_5464_;
goto v_reusejp_5530_;
}
else
{
lean_object* v_reuseFailAlloc_5532_; 
v_reuseFailAlloc_5532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5532_, 0, v___x_5529_);
v___x_5531_ = v_reuseFailAlloc_5532_;
goto v_reusejp_5530_;
}
v_reusejp_5530_:
{
return v___x_5531_;
}
}
}
}
else
{
lean_object* v___x_5547_; lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; 
lean_dec_ref(v___x_5485_);
lean_del_object(v___x_5464_);
lean_del_object(v___x_5459_);
lean_dec(v_fieldName_5450_);
v___x_5547_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5548_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5549_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5449_, v_a_5462_);
v___x_5550_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5550_, 0, v___x_5548_);
lean_ctor_set(v___x_5550_, 1, v___x_5549_);
v___x_5551_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5547_, v___x_5550_, v_a_5451_, v_a_5452_, v_a_5453_, v_a_5454_);
return v___x_5551_;
}
v___jp_5466_:
{
lean_object* v___x_5471_; lean_object* v___x_5472_; uint8_t v___x_5473_; lean_object* v___x_5474_; lean_object* v___x_5476_; 
v___x_5471_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5472_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5473_ = 1;
v___x_5474_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5450_, v___x_5473_);
if (v_isShared_5460_ == 0)
{
lean_ctor_set_tag(v___x_5459_, 3);
lean_ctor_set(v___x_5459_, 0, v___x_5474_);
v___x_5476_ = v___x_5459_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5474_);
v___x_5476_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
lean_object* v___x_5477_; lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; 
v___x_5477_ = l_Lean_MessageData_ofFormat(v___x_5476_);
v___x_5478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5478_, 0, v___x_5472_);
lean_ctor_set(v___x_5478_, 1, v___x_5477_);
v___x_5479_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5480_, 0, v___x_5478_);
lean_ctor_set(v___x_5480_, 1, v___x_5479_);
v___x_5481_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5449_, v_a_5462_);
v___x_5482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5480_);
lean_ctor_set(v___x_5482_, 1, v___x_5481_);
v___x_5483_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5471_, v___x_5482_, v___y_5470_, v___y_5468_, v___y_5469_, v___y_5467_);
return v___x_5483_;
}
}
}
}
else
{
lean_del_object(v___x_5459_);
lean_dec(v_fieldName_5450_);
lean_dec_ref(v_s_5449_);
return v___x_5461_;
}
}
}
else
{
lean_dec(v_fieldName_5450_);
lean_dec_ref(v_s_5449_);
return v___x_5456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5554_, lean_object* v_declName_5555_, lean_object* v_s_5556_, lean_object* v_fieldName_5557_, lean_object* v_as_5558_, size_t v_sz_5559_, size_t v_i_5560_, lean_object* v_b_5561_, lean_object* v___y_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_){
_start:
{
lean_object* v_a_5568_; uint8_t v___x_5572_; 
v___x_5572_ = lean_usize_dec_lt(v_i_5560_, v_sz_5559_);
if (v___x_5572_ == 0)
{
lean_object* v___x_5573_; 
lean_dec(v_fieldName_5557_);
lean_dec_ref(v_s_5556_);
lean_dec(v_declName_5555_);
lean_dec_ref(v___x_5554_);
v___x_5573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5573_, 0, v_b_5561_);
return v___x_5573_;
}
else
{
lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v_a_5576_; lean_object* v___x_5577_; 
lean_dec_ref(v_b_5561_);
v___x_5574_ = lean_box(0);
v___x_5575_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5576_ = lean_array_uget_borrowed(v_as_5558_, v_i_5560_);
lean_inc(v_a_5576_);
lean_inc(v_declName_5555_);
lean_inc_ref(v___x_5554_);
v___x_5577_ = l_Lean_isSubobjectField_x3f(v___x_5554_, v_declName_5555_, v_a_5576_);
if (lean_obj_tag(v___x_5577_) == 0)
{
v_a_5568_ = v___x_5575_;
goto v___jp_5567_;
}
else
{
lean_object* v___x_5579_; uint8_t v_isShared_5580_; uint8_t v_isSharedCheck_5636_; 
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5636_ == 0)
{
lean_object* v_unused_5637_; 
v_unused_5637_ = lean_ctor_get(v___x_5577_, 0);
lean_dec(v_unused_5637_);
v___x_5579_ = v___x_5577_;
v_isShared_5580_ = v_isSharedCheck_5636_;
goto v_resetjp_5578_;
}
else
{
lean_dec(v___x_5577_);
v___x_5579_ = lean_box(0);
v_isShared_5580_ = v_isSharedCheck_5636_;
goto v_resetjp_5578_;
}
v_resetjp_5578_:
{
lean_object* v___x_5581_; 
lean_inc(v_a_5576_);
lean_inc_ref(v_s_5556_);
v___x_5581_ = l_Lean_Meta_mkProjection(v_s_5556_, v_a_5576_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5581_) == 0)
{
lean_object* v_a_5582_; lean_object* v___x_5583_; 
v_a_5582_ = lean_ctor_get(v___x_5581_, 0);
lean_inc(v_a_5582_);
lean_dec_ref_known(v___x_5581_, 1);
v___x_5583_ = l_Lean_Meta_saveState___redArg(v___y_5563_, v___y_5565_);
if (lean_obj_tag(v___x_5583_) == 0)
{
lean_object* v_a_5584_; lean_object* v___x_5585_; 
v_a_5584_ = lean_ctor_get(v___x_5583_, 0);
lean_inc(v_a_5584_);
lean_dec_ref_known(v___x_5583_, 1);
lean_inc(v_fieldName_5557_);
v___x_5585_ = l_Lean_Meta_mkProjection(v_a_5582_, v_fieldName_5557_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
if (lean_obj_tag(v___x_5585_) == 0)
{
lean_object* v_a_5586_; lean_object* v___x_5588_; uint8_t v_isShared_5589_; uint8_t v_isSharedCheck_5598_; 
lean_dec(v_a_5584_);
lean_dec(v_fieldName_5557_);
lean_dec_ref(v_s_5556_);
lean_dec(v_declName_5555_);
lean_dec_ref(v___x_5554_);
v_a_5586_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5598_ == 0)
{
v___x_5588_ = v___x_5585_;
v_isShared_5589_ = v_isSharedCheck_5598_;
goto v_resetjp_5587_;
}
else
{
lean_inc(v_a_5586_);
lean_dec(v___x_5585_);
v___x_5588_ = lean_box(0);
v_isShared_5589_ = v_isSharedCheck_5598_;
goto v_resetjp_5587_;
}
v_resetjp_5587_:
{
lean_object* v___x_5591_; 
if (v_isShared_5580_ == 0)
{
lean_ctor_set(v___x_5579_, 0, v_a_5586_);
v___x_5591_ = v___x_5579_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5586_);
v___x_5591_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5595_; 
v___x_5592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5592_, 0, v___x_5591_);
v___x_5593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5593_, 0, v___x_5592_);
lean_ctor_set(v___x_5593_, 1, v___x_5574_);
if (v_isShared_5589_ == 0)
{
lean_ctor_set(v___x_5588_, 0, v___x_5593_);
v___x_5595_ = v___x_5588_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5593_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
}
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5601_; uint8_t v_isShared_5602_; uint8_t v_isSharedCheck_5619_; 
lean_del_object(v___x_5579_);
v_a_5599_ = lean_ctor_get(v___x_5585_, 0);
v_isSharedCheck_5619_ = !lean_is_exclusive(v___x_5585_);
if (v_isSharedCheck_5619_ == 0)
{
v___x_5601_ = v___x_5585_;
v_isShared_5602_ = v_isSharedCheck_5619_;
goto v_resetjp_5600_;
}
else
{
lean_inc(v_a_5599_);
lean_dec(v___x_5585_);
v___x_5601_ = lean_box(0);
v_isShared_5602_ = v_isSharedCheck_5619_;
goto v_resetjp_5600_;
}
v_resetjp_5600_:
{
uint8_t v___y_5604_; uint8_t v___x_5617_; 
v___x_5617_ = l_Lean_Exception_isInterrupt(v_a_5599_);
if (v___x_5617_ == 0)
{
uint8_t v___x_5618_; 
lean_inc(v_a_5599_);
v___x_5618_ = l_Lean_Exception_isRuntime(v_a_5599_);
v___y_5604_ = v___x_5618_;
goto v___jp_5603_;
}
else
{
v___y_5604_ = v___x_5617_;
goto v___jp_5603_;
}
v___jp_5603_:
{
if (v___y_5604_ == 0)
{
lean_object* v___x_5605_; 
lean_del_object(v___x_5601_);
lean_dec(v_a_5599_);
v___x_5605_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5584_, v___y_5563_, v___y_5565_);
lean_dec(v_a_5584_);
if (lean_obj_tag(v___x_5605_) == 0)
{
lean_dec_ref_known(v___x_5605_, 1);
v_a_5568_ = v___x_5575_;
goto v___jp_5567_;
}
else
{
lean_object* v_a_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5613_; 
lean_dec(v_fieldName_5557_);
lean_dec_ref(v_s_5556_);
lean_dec(v_declName_5555_);
lean_dec_ref(v___x_5554_);
v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
v_isSharedCheck_5613_ = !lean_is_exclusive(v___x_5605_);
if (v_isSharedCheck_5613_ == 0)
{
v___x_5608_ = v___x_5605_;
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_a_5606_);
lean_dec(v___x_5605_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5613_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5611_; 
if (v_isShared_5609_ == 0)
{
v___x_5611_ = v___x_5608_;
goto v_reusejp_5610_;
}
else
{
lean_object* v_reuseFailAlloc_5612_; 
v_reuseFailAlloc_5612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
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
else
{
lean_object* v___x_5615_; 
lean_dec(v_a_5584_);
lean_dec(v_fieldName_5557_);
lean_dec_ref(v_s_5556_);
lean_dec(v_declName_5555_);
lean_dec_ref(v___x_5554_);
if (v_isShared_5602_ == 0)
{
v___x_5615_ = v___x_5601_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_a_5599_);
v___x_5615_ = v_reuseFailAlloc_5616_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
return v___x_5615_;
}
}
}
}
}
}
else
{
lean_object* v_a_5620_; lean_object* v___x_5622_; uint8_t v_isShared_5623_; uint8_t v_isSharedCheck_5627_; 
lean_dec(v_a_5582_);
lean_del_object(v___x_5579_);
lean_dec(v_fieldName_5557_);
lean_dec_ref(v_s_5556_);
lean_dec(v_declName_5555_);
lean_dec_ref(v___x_5554_);
v_a_5620_ = lean_ctor_get(v___x_5583_, 0);
v_isSharedCheck_5627_ = !lean_is_exclusive(v___x_5583_);
if (v_isSharedCheck_5627_ == 0)
{
v___x_5622_ = v___x_5583_;
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
else
{
lean_inc(v_a_5620_);
lean_dec(v___x_5583_);
v___x_5622_ = lean_box(0);
v_isShared_5623_ = v_isSharedCheck_5627_;
goto v_resetjp_5621_;
}
v_resetjp_5621_:
{
lean_object* v___x_5625_; 
if (v_isShared_5623_ == 0)
{
v___x_5625_ = v___x_5622_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5626_; 
v_reuseFailAlloc_5626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5626_, 0, v_a_5620_);
v___x_5625_ = v_reuseFailAlloc_5626_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
return v___x_5625_;
}
}
}
}
else
{
lean_object* v_a_5628_; lean_object* v___x_5630_; uint8_t v_isShared_5631_; uint8_t v_isSharedCheck_5635_; 
lean_del_object(v___x_5579_);
lean_dec(v_fieldName_5557_);
lean_dec_ref(v_s_5556_);
lean_dec(v_declName_5555_);
lean_dec_ref(v___x_5554_);
v_a_5628_ = lean_ctor_get(v___x_5581_, 0);
v_isSharedCheck_5635_ = !lean_is_exclusive(v___x_5581_);
if (v_isSharedCheck_5635_ == 0)
{
v___x_5630_ = v___x_5581_;
v_isShared_5631_ = v_isSharedCheck_5635_;
goto v_resetjp_5629_;
}
else
{
lean_inc(v_a_5628_);
lean_dec(v___x_5581_);
v___x_5630_ = lean_box(0);
v_isShared_5631_ = v_isSharedCheck_5635_;
goto v_resetjp_5629_;
}
v_resetjp_5629_:
{
lean_object* v___x_5633_; 
if (v_isShared_5631_ == 0)
{
v___x_5633_ = v___x_5630_;
goto v_reusejp_5632_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5628_);
v___x_5633_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5632_;
}
v_reusejp_5632_:
{
return v___x_5633_;
}
}
}
}
}
}
v___jp_5567_:
{
size_t v___x_5569_; size_t v___x_5570_; 
v___x_5569_ = ((size_t)1ULL);
v___x_5570_ = lean_usize_add(v_i_5560_, v___x_5569_);
lean_inc_ref(v_a_5568_);
v_i_5560_ = v___x_5570_;
v_b_5561_ = v_a_5568_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5638_, lean_object* v_declName_5639_, lean_object* v_s_5640_, lean_object* v_fieldName_5641_, lean_object* v_as_5642_, lean_object* v_sz_5643_, lean_object* v_i_5644_, lean_object* v_b_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_, lean_object* v___y_5649_, lean_object* v___y_5650_){
_start:
{
size_t v_sz_boxed_5651_; size_t v_i_boxed_5652_; lean_object* v_res_5653_; 
v_sz_boxed_5651_ = lean_unbox_usize(v_sz_5643_);
lean_dec(v_sz_5643_);
v_i_boxed_5652_ = lean_unbox_usize(v_i_5644_);
lean_dec(v_i_5644_);
v_res_5653_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5638_, v_declName_5639_, v_s_5640_, v_fieldName_5641_, v_as_5642_, v_sz_boxed_5651_, v_i_boxed_5652_, v_b_5645_, v___y_5646_, v___y_5647_, v___y_5648_, v___y_5649_);
lean_dec(v___y_5649_);
lean_dec_ref(v___y_5648_);
lean_dec(v___y_5647_);
lean_dec_ref(v___y_5646_);
lean_dec_ref(v_as_5642_);
return v_res_5653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5654_, lean_object* v_fieldName_5655_, lean_object* v_a_5656_, lean_object* v_a_5657_, lean_object* v_a_5658_, lean_object* v_a_5659_, lean_object* v_a_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l_Lean_Meta_mkProjection(v_s_5654_, v_fieldName_5655_, v_a_5656_, v_a_5657_, v_a_5658_, v_a_5659_);
lean_dec(v_a_5659_);
lean_dec_ref(v_a_5658_);
lean_dec(v_a_5657_);
lean_dec_ref(v_a_5656_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5662_, lean_object* v_cons_5663_, lean_object* v_x_5664_){
_start:
{
if (lean_obj_tag(v_x_5664_) == 0)
{
lean_dec_ref(v_cons_5663_);
lean_inc_ref(v_nil_5662_);
return v_nil_5662_;
}
else
{
lean_object* v_head_5665_; lean_object* v_tail_5666_; lean_object* v___x_5667_; lean_object* v___x_5668_; lean_object* v___x_5669_; 
v_head_5665_ = lean_ctor_get(v_x_5664_, 0);
lean_inc(v_head_5665_);
v_tail_5666_ = lean_ctor_get(v_x_5664_, 1);
lean_inc(v_tail_5666_);
lean_dec_ref_known(v_x_5664_, 2);
lean_inc_ref(v_cons_5663_);
v___x_5667_ = l_Lean_Expr_app___override(v_cons_5663_, v_head_5665_);
v___x_5668_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5662_, v_cons_5663_, v_tail_5666_);
v___x_5669_ = l_Lean_Expr_app___override(v___x_5667_, v___x_5668_);
return v___x_5669_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5670_, lean_object* v_cons_5671_, lean_object* v_x_5672_){
_start:
{
lean_object* v_res_5673_; 
v_res_5673_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5670_, v_cons_5671_, v_x_5672_);
lean_dec_ref(v_nil_5670_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5683_, lean_object* v_xs_5684_, lean_object* v_a_5685_, lean_object* v_a_5686_, lean_object* v_a_5687_, lean_object* v_a_5688_){
_start:
{
lean_object* v___x_5690_; 
lean_inc_ref(v_type_5683_);
v___x_5690_ = l_Lean_Meta_getDecLevel(v_type_5683_, v_a_5685_, v_a_5686_, v_a_5687_, v_a_5688_);
if (lean_obj_tag(v___x_5690_) == 0)
{
lean_object* v_a_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5710_; 
v_a_5691_ = lean_ctor_get(v___x_5690_, 0);
v_isSharedCheck_5710_ = !lean_is_exclusive(v___x_5690_);
if (v_isSharedCheck_5710_ == 0)
{
v___x_5693_ = v___x_5690_;
v_isShared_5694_ = v_isSharedCheck_5710_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_a_5691_);
lean_dec(v___x_5690_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5710_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5695_; lean_object* v___x_5696_; lean_object* v___x_5697_; lean_object* v___x_5698_; lean_object* v___x_5699_; 
v___x_5695_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5696_ = lean_box(0);
v___x_5697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5697_, 0, v_a_5691_);
lean_ctor_set(v___x_5697_, 1, v___x_5696_);
lean_inc_ref(v___x_5697_);
v___x_5698_ = l_Lean_mkConst(v___x_5695_, v___x_5697_);
lean_inc_ref(v_type_5683_);
v___x_5699_ = l_Lean_Expr_app___override(v___x_5698_, v_type_5683_);
if (lean_obj_tag(v_xs_5684_) == 0)
{
lean_object* v___x_5701_; 
lean_dec_ref_known(v___x_5697_, 2);
lean_dec_ref(v_type_5683_);
if (v_isShared_5694_ == 0)
{
lean_ctor_set(v___x_5693_, 0, v___x_5699_);
v___x_5701_ = v___x_5693_;
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
else
{
lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; lean_object* v___x_5706_; lean_object* v___x_5708_; 
v___x_5703_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5704_ = l_Lean_mkConst(v___x_5703_, v___x_5697_);
v___x_5705_ = l_Lean_Expr_app___override(v___x_5704_, v_type_5683_);
v___x_5706_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5699_, v___x_5705_, v_xs_5684_);
lean_dec_ref(v___x_5699_);
if (v_isShared_5694_ == 0)
{
lean_ctor_set(v___x_5693_, 0, v___x_5706_);
v___x_5708_ = v___x_5693_;
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
}
}
else
{
lean_object* v_a_5711_; lean_object* v___x_5713_; uint8_t v_isShared_5714_; uint8_t v_isSharedCheck_5718_; 
lean_dec(v_xs_5684_);
lean_dec_ref(v_type_5683_);
v_a_5711_ = lean_ctor_get(v___x_5690_, 0);
v_isSharedCheck_5718_ = !lean_is_exclusive(v___x_5690_);
if (v_isSharedCheck_5718_ == 0)
{
v___x_5713_ = v___x_5690_;
v_isShared_5714_ = v_isSharedCheck_5718_;
goto v_resetjp_5712_;
}
else
{
lean_inc(v_a_5711_);
lean_dec(v___x_5690_);
v___x_5713_ = lean_box(0);
v_isShared_5714_ = v_isSharedCheck_5718_;
goto v_resetjp_5712_;
}
v_resetjp_5712_:
{
lean_object* v___x_5716_; 
if (v_isShared_5714_ == 0)
{
v___x_5716_ = v___x_5713_;
goto v_reusejp_5715_;
}
else
{
lean_object* v_reuseFailAlloc_5717_; 
v_reuseFailAlloc_5717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5717_, 0, v_a_5711_);
v___x_5716_ = v_reuseFailAlloc_5717_;
goto v_reusejp_5715_;
}
v_reusejp_5715_:
{
return v___x_5716_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5719_, lean_object* v_xs_5720_, lean_object* v_a_5721_, lean_object* v_a_5722_, lean_object* v_a_5723_, lean_object* v_a_5724_, lean_object* v_a_5725_){
_start:
{
lean_object* v_res_5726_; 
v_res_5726_ = l_Lean_Meta_mkListLit(v_type_5719_, v_xs_5720_, v_a_5721_, v_a_5722_, v_a_5723_, v_a_5724_);
lean_dec(v_a_5724_);
lean_dec_ref(v_a_5723_);
lean_dec(v_a_5722_);
lean_dec_ref(v_a_5721_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5731_, lean_object* v_xs_5732_, lean_object* v_a_5733_, lean_object* v_a_5734_, lean_object* v_a_5735_, lean_object* v_a_5736_){
_start:
{
lean_object* v___x_5738_; 
lean_inc_ref(v_type_5731_);
v___x_5738_ = l_Lean_Meta_getDecLevel(v_type_5731_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_);
if (lean_obj_tag(v___x_5738_) == 0)
{
lean_object* v_a_5739_; lean_object* v___x_5740_; 
v_a_5739_ = lean_ctor_get(v___x_5738_, 0);
lean_inc(v_a_5739_);
lean_dec_ref_known(v___x_5738_, 1);
lean_inc_ref(v_type_5731_);
v___x_5740_ = l_Lean_Meta_mkListLit(v_type_5731_, v_xs_5732_, v_a_5733_, v_a_5734_, v_a_5735_, v_a_5736_);
if (lean_obj_tag(v___x_5740_) == 0)
{
lean_object* v_a_5741_; lean_object* v___x_5743_; uint8_t v_isShared_5744_; uint8_t v_isSharedCheck_5754_; 
v_a_5741_ = lean_ctor_get(v___x_5740_, 0);
v_isSharedCheck_5754_ = !lean_is_exclusive(v___x_5740_);
if (v_isSharedCheck_5754_ == 0)
{
v___x_5743_ = v___x_5740_;
v_isShared_5744_ = v_isSharedCheck_5754_;
goto v_resetjp_5742_;
}
else
{
lean_inc(v_a_5741_);
lean_dec(v___x_5740_);
v___x_5743_ = lean_box(0);
v_isShared_5744_ = v_isSharedCheck_5754_;
goto v_resetjp_5742_;
}
v_resetjp_5742_:
{
lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5752_; 
v___x_5745_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5746_ = lean_box(0);
v___x_5747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5747_, 0, v_a_5739_);
lean_ctor_set(v___x_5747_, 1, v___x_5746_);
v___x_5748_ = l_Lean_mkConst(v___x_5745_, v___x_5747_);
v___x_5749_ = l_Lean_Expr_app___override(v___x_5748_, v_type_5731_);
v___x_5750_ = l_Lean_Expr_app___override(v___x_5749_, v_a_5741_);
if (v_isShared_5744_ == 0)
{
lean_ctor_set(v___x_5743_, 0, v___x_5750_);
v___x_5752_ = v___x_5743_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v___x_5750_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
else
{
lean_dec(v_a_5739_);
lean_dec_ref(v_type_5731_);
return v___x_5740_;
}
}
else
{
lean_object* v_a_5755_; lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5762_; 
lean_dec(v_xs_5732_);
lean_dec_ref(v_type_5731_);
v_a_5755_ = lean_ctor_get(v___x_5738_, 0);
v_isSharedCheck_5762_ = !lean_is_exclusive(v___x_5738_);
if (v_isSharedCheck_5762_ == 0)
{
v___x_5757_ = v___x_5738_;
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
else
{
lean_inc(v_a_5755_);
lean_dec(v___x_5738_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5762_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5760_; 
if (v_isShared_5758_ == 0)
{
v___x_5760_ = v___x_5757_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_a_5755_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5763_, lean_object* v_xs_5764_, lean_object* v_a_5765_, lean_object* v_a_5766_, lean_object* v_a_5767_, lean_object* v_a_5768_, lean_object* v_a_5769_){
_start:
{
lean_object* v_res_5770_; 
v_res_5770_ = l_Lean_Meta_mkArrayLit(v_type_5763_, v_xs_5764_, v_a_5765_, v_a_5766_, v_a_5767_, v_a_5768_);
lean_dec(v_a_5768_);
lean_dec_ref(v_a_5767_);
lean_dec(v_a_5766_);
lean_dec_ref(v_a_5765_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5776_, lean_object* v_a_5777_, lean_object* v_a_5778_, lean_object* v_a_5779_, lean_object* v_a_5780_){
_start:
{
lean_object* v___x_5782_; 
lean_inc_ref(v_type_5776_);
v___x_5782_ = l_Lean_Meta_getDecLevel(v_type_5776_, v_a_5777_, v_a_5778_, v_a_5779_, v_a_5780_);
if (lean_obj_tag(v___x_5782_) == 0)
{
lean_object* v_a_5783_; lean_object* v___x_5785_; uint8_t v_isShared_5786_; uint8_t v_isSharedCheck_5795_; 
v_a_5783_ = lean_ctor_get(v___x_5782_, 0);
v_isSharedCheck_5795_ = !lean_is_exclusive(v___x_5782_);
if (v_isSharedCheck_5795_ == 0)
{
v___x_5785_ = v___x_5782_;
v_isShared_5786_ = v_isSharedCheck_5795_;
goto v_resetjp_5784_;
}
else
{
lean_inc(v_a_5783_);
lean_dec(v___x_5782_);
v___x_5785_ = lean_box(0);
v_isShared_5786_ = v_isSharedCheck_5795_;
goto v_resetjp_5784_;
}
v_resetjp_5784_:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; lean_object* v___x_5789_; lean_object* v___x_5790_; lean_object* v___x_5791_; lean_object* v___x_5793_; 
v___x_5787_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5788_ = lean_box(0);
v___x_5789_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5789_, 0, v_a_5783_);
lean_ctor_set(v___x_5789_, 1, v___x_5788_);
v___x_5790_ = l_Lean_mkConst(v___x_5787_, v___x_5789_);
v___x_5791_ = l_Lean_Expr_app___override(v___x_5790_, v_type_5776_);
if (v_isShared_5786_ == 0)
{
lean_ctor_set(v___x_5785_, 0, v___x_5791_);
v___x_5793_ = v___x_5785_;
goto v_reusejp_5792_;
}
else
{
lean_object* v_reuseFailAlloc_5794_; 
v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5794_, 0, v___x_5791_);
v___x_5793_ = v_reuseFailAlloc_5794_;
goto v_reusejp_5792_;
}
v_reusejp_5792_:
{
return v___x_5793_;
}
}
}
else
{
lean_object* v_a_5796_; lean_object* v___x_5798_; uint8_t v_isShared_5799_; uint8_t v_isSharedCheck_5803_; 
lean_dec_ref(v_type_5776_);
v_a_5796_ = lean_ctor_get(v___x_5782_, 0);
v_isSharedCheck_5803_ = !lean_is_exclusive(v___x_5782_);
if (v_isSharedCheck_5803_ == 0)
{
v___x_5798_ = v___x_5782_;
v_isShared_5799_ = v_isSharedCheck_5803_;
goto v_resetjp_5797_;
}
else
{
lean_inc(v_a_5796_);
lean_dec(v___x_5782_);
v___x_5798_ = lean_box(0);
v_isShared_5799_ = v_isSharedCheck_5803_;
goto v_resetjp_5797_;
}
v_resetjp_5797_:
{
lean_object* v___x_5801_; 
if (v_isShared_5799_ == 0)
{
v___x_5801_ = v___x_5798_;
goto v_reusejp_5800_;
}
else
{
lean_object* v_reuseFailAlloc_5802_; 
v_reuseFailAlloc_5802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5802_, 0, v_a_5796_);
v___x_5801_ = v_reuseFailAlloc_5802_;
goto v_reusejp_5800_;
}
v_reusejp_5800_:
{
return v___x_5801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_, lean_object* v_a_5808_, lean_object* v_a_5809_){
_start:
{
lean_object* v_res_5810_; 
v_res_5810_ = l_Lean_Meta_mkNone(v_type_5804_, v_a_5805_, v_a_5806_, v_a_5807_, v_a_5808_);
lean_dec(v_a_5808_);
lean_dec_ref(v_a_5807_);
lean_dec(v_a_5806_);
lean_dec_ref(v_a_5805_);
return v_res_5810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5815_, lean_object* v_value_5816_, lean_object* v_a_5817_, lean_object* v_a_5818_, lean_object* v_a_5819_, lean_object* v_a_5820_){
_start:
{
lean_object* v___x_5822_; 
lean_inc_ref(v_type_5815_);
v___x_5822_ = l_Lean_Meta_getDecLevel(v_type_5815_, v_a_5817_, v_a_5818_, v_a_5819_, v_a_5820_);
if (lean_obj_tag(v___x_5822_) == 0)
{
lean_object* v_a_5823_; lean_object* v___x_5825_; uint8_t v_isShared_5826_; uint8_t v_isSharedCheck_5835_; 
v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5835_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5835_ == 0)
{
v___x_5825_ = v___x_5822_;
v_isShared_5826_ = v_isSharedCheck_5835_;
goto v_resetjp_5824_;
}
else
{
lean_inc(v_a_5823_);
lean_dec(v___x_5822_);
v___x_5825_ = lean_box(0);
v_isShared_5826_ = v_isSharedCheck_5835_;
goto v_resetjp_5824_;
}
v_resetjp_5824_:
{
lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v___x_5831_; lean_object* v___x_5833_; 
v___x_5827_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5828_ = lean_box(0);
v___x_5829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5829_, 0, v_a_5823_);
lean_ctor_set(v___x_5829_, 1, v___x_5828_);
v___x_5830_ = l_Lean_mkConst(v___x_5827_, v___x_5829_);
v___x_5831_ = l_Lean_mkAppB(v___x_5830_, v_type_5815_, v_value_5816_);
if (v_isShared_5826_ == 0)
{
lean_ctor_set(v___x_5825_, 0, v___x_5831_);
v___x_5833_ = v___x_5825_;
goto v_reusejp_5832_;
}
else
{
lean_object* v_reuseFailAlloc_5834_; 
v_reuseFailAlloc_5834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5834_, 0, v___x_5831_);
v___x_5833_ = v_reuseFailAlloc_5834_;
goto v_reusejp_5832_;
}
v_reusejp_5832_:
{
return v___x_5833_;
}
}
}
else
{
lean_object* v_a_5836_; lean_object* v___x_5838_; uint8_t v_isShared_5839_; uint8_t v_isSharedCheck_5843_; 
lean_dec_ref(v_value_5816_);
lean_dec_ref(v_type_5815_);
v_a_5836_ = lean_ctor_get(v___x_5822_, 0);
v_isSharedCheck_5843_ = !lean_is_exclusive(v___x_5822_);
if (v_isSharedCheck_5843_ == 0)
{
v___x_5838_ = v___x_5822_;
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
else
{
lean_inc(v_a_5836_);
lean_dec(v___x_5822_);
v___x_5838_ = lean_box(0);
v_isShared_5839_ = v_isSharedCheck_5843_;
goto v_resetjp_5837_;
}
v_resetjp_5837_:
{
lean_object* v___x_5841_; 
if (v_isShared_5839_ == 0)
{
v___x_5841_ = v___x_5838_;
goto v_reusejp_5840_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v_a_5836_);
v___x_5841_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5840_;
}
v_reusejp_5840_:
{
return v___x_5841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5844_, lean_object* v_value_5845_, lean_object* v_a_5846_, lean_object* v_a_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_){
_start:
{
lean_object* v_res_5851_; 
v_res_5851_ = l_Lean_Meta_mkSome(v_type_5844_, v_value_5845_, v_a_5846_, v_a_5847_, v_a_5848_, v_a_5849_);
lean_dec(v_a_5849_);
lean_dec_ref(v_a_5848_);
lean_dec(v_a_5847_);
lean_dec_ref(v_a_5846_);
return v_res_5851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5857_, lean_object* v_a_5858_, lean_object* v_a_5859_, lean_object* v_a_5860_, lean_object* v_a_5861_){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; lean_object* v___x_5869_; lean_object* v___x_5870_; 
v___x_5863_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5864_, 0, v_p_5857_);
v___x_5865_ = lean_box(0);
v___x_5866_ = lean_unsigned_to_nat(2u);
v___x_5867_ = lean_mk_empty_array_with_capacity(v___x_5866_);
v___x_5868_ = lean_array_push(v___x_5867_, v___x_5864_);
v___x_5869_ = lean_array_push(v___x_5868_, v___x_5865_);
v___x_5870_ = l_Lean_Meta_mkAppOptM(v___x_5863_, v___x_5869_, v_a_5858_, v_a_5859_, v_a_5860_, v_a_5861_);
return v___x_5870_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5871_, lean_object* v_a_5872_, lean_object* v_a_5873_, lean_object* v_a_5874_, lean_object* v_a_5875_, lean_object* v_a_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l_Lean_Meta_mkDecide(v_p_5871_, v_a_5872_, v_a_5873_, v_a_5874_, v_a_5875_);
lean_dec(v_a_5875_);
lean_dec_ref(v_a_5874_);
lean_dec(v_a_5873_);
lean_dec_ref(v_a_5872_);
return v_res_5877_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; 
v___x_5883_ = lean_box(0);
v___x_5884_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5885_ = l_Lean_mkConst(v___x_5884_, v___x_5883_);
return v___x_5885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_, lean_object* v_a_5892_, lean_object* v_a_5893_){
_start:
{
lean_object* v___x_5895_; 
v___x_5895_ = l_Lean_Meta_mkDecide(v_p_5889_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
if (lean_obj_tag(v___x_5895_) == 0)
{
lean_object* v_a_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; 
v_a_5896_ = lean_ctor_get(v___x_5895_, 0);
lean_inc(v_a_5896_);
lean_dec_ref_known(v___x_5895_, 1);
v___x_5897_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5898_ = l_Lean_Meta_mkEq(v_a_5896_, v___x_5897_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
if (lean_obj_tag(v___x_5898_) == 0)
{
lean_object* v_a_5899_; lean_object* v___x_5900_; 
v_a_5899_ = lean_ctor_get(v___x_5898_, 0);
lean_inc(v_a_5899_);
lean_dec_ref_known(v___x_5898_, 1);
v___x_5900_ = l_Lean_Meta_mkEqRefl(v___x_5897_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
if (lean_obj_tag(v___x_5900_) == 0)
{
lean_object* v_a_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; 
v_a_5901_ = lean_ctor_get(v___x_5900_, 0);
lean_inc(v_a_5901_);
lean_dec_ref_known(v___x_5900_, 1);
v___x_5902_ = l_Lean_Meta_mkExpectedPropHint(v_a_5901_, v_a_5899_);
v___x_5903_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5904_ = lean_unsigned_to_nat(1u);
v___x_5905_ = lean_mk_empty_array_with_capacity(v___x_5904_);
v___x_5906_ = lean_array_push(v___x_5905_, v___x_5902_);
v___x_5907_ = l_Lean_Meta_mkAppM(v___x_5903_, v___x_5906_, v_a_5890_, v_a_5891_, v_a_5892_, v_a_5893_);
return v___x_5907_;
}
else
{
lean_dec(v_a_5899_);
return v___x_5900_;
}
}
else
{
return v___x_5898_;
}
}
else
{
return v___x_5895_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5908_, lean_object* v_a_5909_, lean_object* v_a_5910_, lean_object* v_a_5911_, lean_object* v_a_5912_, lean_object* v_a_5913_){
_start:
{
lean_object* v_res_5914_; 
v_res_5914_ = l_Lean_Meta_mkDecideProof(v_p_5908_, v_a_5909_, v_a_5910_, v_a_5911_, v_a_5912_);
lean_dec(v_a_5912_);
lean_dec_ref(v_a_5911_);
lean_dec(v_a_5910_);
lean_dec_ref(v_a_5909_);
return v_res_5914_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5920_, lean_object* v_b_5921_, lean_object* v_a_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_){
_start:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; 
v___x_5927_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_5928_ = lean_unsigned_to_nat(2u);
v___x_5929_ = lean_mk_empty_array_with_capacity(v___x_5928_);
v___x_5930_ = lean_array_push(v___x_5929_, v_a_5920_);
v___x_5931_ = lean_array_push(v___x_5930_, v_b_5921_);
v___x_5932_ = l_Lean_Meta_mkAppM(v___x_5927_, v___x_5931_, v_a_5922_, v_a_5923_, v_a_5924_, v_a_5925_);
return v___x_5932_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_5933_, lean_object* v_b_5934_, lean_object* v_a_5935_, lean_object* v_a_5936_, lean_object* v_a_5937_, lean_object* v_a_5938_, lean_object* v_a_5939_){
_start:
{
lean_object* v_res_5940_; 
v_res_5940_ = l_Lean_Meta_mkLt(v_a_5933_, v_b_5934_, v_a_5935_, v_a_5936_, v_a_5937_, v_a_5938_);
lean_dec(v_a_5938_);
lean_dec_ref(v_a_5937_);
lean_dec(v_a_5936_);
lean_dec_ref(v_a_5935_);
return v_res_5940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_5946_, lean_object* v_b_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5953_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_5954_ = lean_unsigned_to_nat(2u);
v___x_5955_ = lean_mk_empty_array_with_capacity(v___x_5954_);
v___x_5956_ = lean_array_push(v___x_5955_, v_a_5946_);
v___x_5957_ = lean_array_push(v___x_5956_, v_b_5947_);
v___x_5958_ = l_Lean_Meta_mkAppM(v___x_5953_, v___x_5957_, v_a_5948_, v_a_5949_, v_a_5950_, v_a_5951_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_5959_, lean_object* v_b_5960_, lean_object* v_a_5961_, lean_object* v_a_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_, lean_object* v_a_5965_){
_start:
{
lean_object* v_res_5966_; 
v_res_5966_ = l_Lean_Meta_mkLe(v_a_5959_, v_b_5960_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_);
lean_dec(v_a_5964_);
lean_dec_ref(v_a_5963_);
lean_dec(v_a_5962_);
lean_dec_ref(v_a_5961_);
return v_res_5966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_, lean_object* v_a_5975_, lean_object* v_a_5976_){
_start:
{
lean_object* v___x_5978_; lean_object* v___x_5979_; lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5978_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_5979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5979_, 0, v_00_u03b1_5972_);
v___x_5980_ = lean_box(0);
v___x_5981_ = lean_unsigned_to_nat(2u);
v___x_5982_ = lean_mk_empty_array_with_capacity(v___x_5981_);
v___x_5983_ = lean_array_push(v___x_5982_, v___x_5979_);
v___x_5984_ = lean_array_push(v___x_5983_, v___x_5980_);
v___x_5985_ = l_Lean_Meta_mkAppOptM(v___x_5978_, v___x_5984_, v_a_5973_, v_a_5974_, v_a_5975_, v_a_5976_);
return v___x_5985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_5986_, lean_object* v_a_5987_, lean_object* v_a_5988_, lean_object* v_a_5989_, lean_object* v_a_5990_, lean_object* v_a_5991_){
_start:
{
lean_object* v_res_5992_; 
v_res_5992_ = l_Lean_Meta_mkDefault(v_00_u03b1_5986_, v_a_5987_, v_a_5988_, v_a_5989_, v_a_5990_);
lean_dec(v_a_5990_);
lean_dec_ref(v_a_5989_);
lean_dec(v_a_5988_);
lean_dec_ref(v_a_5987_);
return v_res_5992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_5998_, lean_object* v_a_5999_, lean_object* v_a_6000_, lean_object* v_a_6001_, lean_object* v_a_6002_){
_start:
{
lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; 
v___x_6004_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_6005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6005_, 0, v_00_u03b1_5998_);
v___x_6006_ = lean_box(0);
v___x_6007_ = lean_unsigned_to_nat(2u);
v___x_6008_ = lean_mk_empty_array_with_capacity(v___x_6007_);
v___x_6009_ = lean_array_push(v___x_6008_, v___x_6005_);
v___x_6010_ = lean_array_push(v___x_6009_, v___x_6006_);
v___x_6011_ = l_Lean_Meta_mkAppOptM(v___x_6004_, v___x_6010_, v_a_5999_, v_a_6000_, v_a_6001_, v_a_6002_);
return v___x_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6012_, lean_object* v_a_6013_, lean_object* v_a_6014_, lean_object* v_a_6015_, lean_object* v_a_6016_, lean_object* v_a_6017_){
_start:
{
lean_object* v_res_6018_; 
v_res_6018_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6012_, v_a_6013_, v_a_6014_, v_a_6015_, v_a_6016_);
lean_dec(v_a_6016_);
lean_dec_ref(v_a_6015_);
lean_dec(v_a_6014_);
lean_dec_ref(v_a_6013_);
return v_res_6018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6022_, lean_object* v_a_6023_, lean_object* v_a_6024_, lean_object* v_a_6025_, lean_object* v_a_6026_){
_start:
{
lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
v___x_6028_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6029_ = lean_unsigned_to_nat(1u);
v___x_6030_ = lean_mk_empty_array_with_capacity(v___x_6029_);
v___x_6031_ = lean_array_push(v___x_6030_, v_h_6022_);
v___x_6032_ = l_Lean_Meta_mkAppM(v___x_6028_, v___x_6031_, v_a_6023_, v_a_6024_, v_a_6025_, v_a_6026_);
return v___x_6032_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_, lean_object* v_a_6037_, lean_object* v_a_6038_){
_start:
{
lean_object* v_res_6039_; 
v_res_6039_ = l_Lean_Meta_mkFunExt(v_h_6033_, v_a_6034_, v_a_6035_, v_a_6036_, v_a_6037_);
lean_dec(v_a_6037_);
lean_dec_ref(v_a_6036_);
lean_dec(v_a_6035_);
lean_dec_ref(v_a_6034_);
return v_res_6039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6043_, lean_object* v_a_6044_, lean_object* v_a_6045_, lean_object* v_a_6046_, lean_object* v_a_6047_){
_start:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; 
v___x_6049_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6050_ = lean_unsigned_to_nat(1u);
v___x_6051_ = lean_mk_empty_array_with_capacity(v___x_6050_);
v___x_6052_ = lean_array_push(v___x_6051_, v_h_6043_);
v___x_6053_ = l_Lean_Meta_mkAppM(v___x_6049_, v___x_6052_, v_a_6044_, v_a_6045_, v_a_6046_, v_a_6047_);
return v___x_6053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6054_, lean_object* v_a_6055_, lean_object* v_a_6056_, lean_object* v_a_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_){
_start:
{
lean_object* v_res_6060_; 
v_res_6060_ = l_Lean_Meta_mkPropExt(v_h_6054_, v_a_6055_, v_a_6056_, v_a_6057_, v_a_6058_);
lean_dec(v_a_6058_);
lean_dec_ref(v_a_6057_);
lean_dec(v_a_6056_);
lean_dec_ref(v_a_6055_);
return v_res_6060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6064_, lean_object* v_h_u2082_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_){
_start:
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
v___x_6071_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6072_ = lean_unsigned_to_nat(2u);
v___x_6073_ = lean_mk_empty_array_with_capacity(v___x_6072_);
v___x_6074_ = lean_array_push(v___x_6073_, v_h_u2081_6064_);
v___x_6075_ = lean_array_push(v___x_6074_, v_h_u2082_6065_);
v___x_6076_ = l_Lean_Meta_mkAppM(v___x_6071_, v___x_6075_, v_a_6066_, v_a_6067_, v_a_6068_, v_a_6069_);
return v___x_6076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6077_, lean_object* v_h_u2082_6078_, lean_object* v_a_6079_, lean_object* v_a_6080_, lean_object* v_a_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_){
_start:
{
lean_object* v_res_6084_; 
v_res_6084_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6077_, v_h_u2082_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_);
lean_dec(v_a_6082_);
lean_dec_ref(v_a_6081_);
lean_dec(v_a_6080_);
lean_dec_ref(v_a_6079_);
return v_res_6084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6088_, lean_object* v_h_6089_, lean_object* v_a_6090_, lean_object* v_a_6091_, lean_object* v_a_6092_, lean_object* v_a_6093_){
_start:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; lean_object* v___x_6099_; lean_object* v___x_6100_; 
v___x_6095_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6096_ = lean_unsigned_to_nat(2u);
v___x_6097_ = lean_mk_empty_array_with_capacity(v___x_6096_);
v___x_6098_ = lean_array_push(v___x_6097_, v_b_6088_);
v___x_6099_ = lean_array_push(v___x_6098_, v_h_6089_);
v___x_6100_ = l_Lean_Meta_mkAppM(v___x_6095_, v___x_6099_, v_a_6090_, v_a_6091_, v_a_6092_, v_a_6093_);
return v___x_6100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6101_, lean_object* v_h_6102_, lean_object* v_a_6103_, lean_object* v_a_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_, lean_object* v_a_6107_){
_start:
{
lean_object* v_res_6108_; 
v_res_6108_ = l_Lean_Meta_mkLetValCongr(v_b_6101_, v_h_6102_, v_a_6103_, v_a_6104_, v_a_6105_, v_a_6106_);
lean_dec(v_a_6106_);
lean_dec_ref(v_a_6105_);
lean_dec(v_a_6104_);
lean_dec_ref(v_a_6103_);
return v_res_6108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6112_, lean_object* v_h_6113_, lean_object* v_a_6114_, lean_object* v_a_6115_, lean_object* v_a_6116_, lean_object* v_a_6117_){
_start:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6119_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6120_ = lean_unsigned_to_nat(2u);
v___x_6121_ = lean_mk_empty_array_with_capacity(v___x_6120_);
v___x_6122_ = lean_array_push(v___x_6121_, v_a_6112_);
v___x_6123_ = lean_array_push(v___x_6122_, v_h_6113_);
v___x_6124_ = l_Lean_Meta_mkAppM(v___x_6119_, v___x_6123_, v_a_6114_, v_a_6115_, v_a_6116_, v_a_6117_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6125_, lean_object* v_h_6126_, lean_object* v_a_6127_, lean_object* v_a_6128_, lean_object* v_a_6129_, lean_object* v_a_6130_, lean_object* v_a_6131_){
_start:
{
lean_object* v_res_6132_; 
v_res_6132_ = l_Lean_Meta_mkLetBodyCongr(v_a_6125_, v_h_6126_, v_a_6127_, v_a_6128_, v_a_6129_, v_a_6130_);
lean_dec(v_a_6130_);
lean_dec_ref(v_a_6129_);
lean_dec(v_a_6128_);
lean_dec_ref(v_a_6127_);
return v_res_6132_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; 
v___x_6136_ = lean_box(0);
v___x_6137_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6138_ = l_Lean_mkConst(v___x_6137_, v___x_6136_);
return v___x_6138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6142_, lean_object* v_h_6143_){
_start:
{
lean_object* v___x_6147_; uint8_t v___x_6148_; 
lean_inc_ref(v_h_6143_);
v___x_6147_ = l_Lean_Expr_cleanupAnnotations(v_h_6143_);
v___x_6148_ = l_Lean_Expr_isApp(v___x_6147_);
if (v___x_6148_ == 0)
{
lean_dec_ref(v___x_6147_);
goto v___jp_6144_;
}
else
{
lean_object* v_arg_6149_; lean_object* v___x_6150_; uint8_t v___x_6151_; 
v_arg_6149_ = lean_ctor_get(v___x_6147_, 1);
lean_inc_ref(v_arg_6149_);
v___x_6150_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6147_);
v___x_6151_ = l_Lean_Expr_isApp(v___x_6150_);
if (v___x_6151_ == 0)
{
lean_dec_ref(v___x_6150_);
lean_dec_ref(v_arg_6149_);
goto v___jp_6144_;
}
else
{
lean_object* v___x_6152_; lean_object* v___x_6153_; uint8_t v___x_6154_; 
v___x_6152_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6150_);
v___x_6153_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6154_ = l_Lean_Expr_isConstOf(v___x_6152_, v___x_6153_);
lean_dec_ref(v___x_6152_);
if (v___x_6154_ == 0)
{
lean_dec_ref(v_arg_6149_);
goto v___jp_6144_;
}
else
{
lean_dec_ref(v_h_6143_);
lean_dec_ref(v_p_6142_);
return v_arg_6149_;
}
}
}
v___jp_6144_:
{
lean_object* v___x_6145_; lean_object* v___x_6146_; 
v___x_6145_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6146_ = l_Lean_mkAppB(v___x_6145_, v_p_6142_, v_h_6143_);
return v___x_6146_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6155_, lean_object* v_a_6156_, lean_object* v_a_6157_, lean_object* v_a_6158_, lean_object* v_a_6159_){
_start:
{
lean_object* v___y_6162_; lean_object* v___y_6163_; lean_object* v___y_6164_; lean_object* v___y_6165_; lean_object* v___x_6171_; 
lean_inc_ref(v_h_6155_);
v___x_6171_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6155_, v_a_6157_);
if (lean_obj_tag(v___x_6171_) == 0)
{
lean_object* v_a_6172_; lean_object* v___x_6174_; uint8_t v_isShared_6175_; uint8_t v_isSharedCheck_6187_; 
v_a_6172_ = lean_ctor_get(v___x_6171_, 0);
v_isSharedCheck_6187_ = !lean_is_exclusive(v___x_6171_);
if (v_isSharedCheck_6187_ == 0)
{
v___x_6174_ = v___x_6171_;
v_isShared_6175_ = v_isSharedCheck_6187_;
goto v_resetjp_6173_;
}
else
{
lean_inc(v_a_6172_);
lean_dec(v___x_6171_);
v___x_6174_ = lean_box(0);
v_isShared_6175_ = v_isSharedCheck_6187_;
goto v_resetjp_6173_;
}
v_resetjp_6173_:
{
lean_object* v___x_6176_; uint8_t v___x_6177_; 
v___x_6176_ = l_Lean_Expr_cleanupAnnotations(v_a_6172_);
v___x_6177_ = l_Lean_Expr_isApp(v___x_6176_);
if (v___x_6177_ == 0)
{
lean_dec_ref(v___x_6176_);
lean_del_object(v___x_6174_);
v___y_6162_ = v_a_6156_;
v___y_6163_ = v_a_6157_;
v___y_6164_ = v_a_6158_;
v___y_6165_ = v_a_6159_;
goto v___jp_6161_;
}
else
{
lean_object* v_arg_6178_; lean_object* v___x_6179_; uint8_t v___x_6180_; 
v_arg_6178_ = lean_ctor_get(v___x_6176_, 1);
lean_inc_ref(v_arg_6178_);
v___x_6179_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6176_);
v___x_6180_ = l_Lean_Expr_isApp(v___x_6179_);
if (v___x_6180_ == 0)
{
lean_dec_ref(v___x_6179_);
lean_dec_ref(v_arg_6178_);
lean_del_object(v___x_6174_);
v___y_6162_ = v_a_6156_;
v___y_6163_ = v_a_6157_;
v___y_6164_ = v_a_6158_;
v___y_6165_ = v_a_6159_;
goto v___jp_6161_;
}
else
{
lean_object* v___x_6181_; lean_object* v___x_6182_; uint8_t v___x_6183_; 
v___x_6181_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6179_);
v___x_6182_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6183_ = l_Lean_Expr_isConstOf(v___x_6181_, v___x_6182_);
lean_dec_ref(v___x_6181_);
if (v___x_6183_ == 0)
{
lean_dec_ref(v_arg_6178_);
lean_del_object(v___x_6174_);
v___y_6162_ = v_a_6156_;
v___y_6163_ = v_a_6157_;
v___y_6164_ = v_a_6158_;
v___y_6165_ = v_a_6159_;
goto v___jp_6161_;
}
else
{
lean_object* v___x_6185_; 
lean_dec_ref(v_h_6155_);
if (v_isShared_6175_ == 0)
{
lean_ctor_set(v___x_6174_, 0, v_arg_6178_);
v___x_6185_ = v___x_6174_;
goto v_reusejp_6184_;
}
else
{
lean_object* v_reuseFailAlloc_6186_; 
v_reuseFailAlloc_6186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6186_, 0, v_arg_6178_);
v___x_6185_ = v_reuseFailAlloc_6186_;
goto v_reusejp_6184_;
}
v_reusejp_6184_:
{
return v___x_6185_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6155_);
return v___x_6171_;
}
v___jp_6161_:
{
lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; 
v___x_6166_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6167_ = lean_unsigned_to_nat(1u);
v___x_6168_ = lean_mk_empty_array_with_capacity(v___x_6167_);
v___x_6169_ = lean_array_push(v___x_6168_, v_h_6155_);
v___x_6170_ = l_Lean_Meta_mkAppM(v___x_6166_, v___x_6169_, v___y_6162_, v___y_6163_, v___y_6164_, v___y_6165_);
return v___x_6170_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_, lean_object* v_a_6193_){
_start:
{
lean_object* v_res_6194_; 
v_res_6194_ = l_Lean_Meta_mkOfEqFalse(v_h_6188_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_);
lean_dec(v_a_6192_);
lean_dec_ref(v_a_6191_);
lean_dec(v_a_6190_);
lean_dec_ref(v_a_6189_);
return v_res_6194_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; lean_object* v___x_6200_; 
v___x_6198_ = lean_box(0);
v___x_6199_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6200_ = l_Lean_mkConst(v___x_6199_, v___x_6198_);
return v___x_6200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6204_, lean_object* v_h_6205_){
_start:
{
lean_object* v___x_6209_; uint8_t v___x_6210_; 
lean_inc_ref(v_h_6205_);
v___x_6209_ = l_Lean_Expr_cleanupAnnotations(v_h_6205_);
v___x_6210_ = l_Lean_Expr_isApp(v___x_6209_);
if (v___x_6210_ == 0)
{
lean_dec_ref(v___x_6209_);
goto v___jp_6206_;
}
else
{
lean_object* v_arg_6211_; lean_object* v___x_6212_; uint8_t v___x_6213_; 
v_arg_6211_ = lean_ctor_get(v___x_6209_, 1);
lean_inc_ref(v_arg_6211_);
v___x_6212_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6209_);
v___x_6213_ = l_Lean_Expr_isApp(v___x_6212_);
if (v___x_6213_ == 0)
{
lean_dec_ref(v___x_6212_);
lean_dec_ref(v_arg_6211_);
goto v___jp_6206_;
}
else
{
lean_object* v___x_6214_; lean_object* v___x_6215_; uint8_t v___x_6216_; 
v___x_6214_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6212_);
v___x_6215_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6216_ = l_Lean_Expr_isConstOf(v___x_6214_, v___x_6215_);
lean_dec_ref(v___x_6214_);
if (v___x_6216_ == 0)
{
lean_dec_ref(v_arg_6211_);
goto v___jp_6206_;
}
else
{
lean_dec_ref(v_h_6205_);
lean_dec_ref(v_p_6204_);
return v_arg_6211_;
}
}
}
v___jp_6206_:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; 
v___x_6207_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6208_ = l_Lean_mkAppB(v___x_6207_, v_p_6204_, v_h_6205_);
return v___x_6208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6217_, lean_object* v_a_6218_, lean_object* v_a_6219_, lean_object* v_a_6220_, lean_object* v_a_6221_){
_start:
{
lean_object* v___y_6224_; lean_object* v___y_6225_; lean_object* v___y_6226_; lean_object* v___y_6227_; lean_object* v___x_6233_; 
lean_inc_ref(v_h_6217_);
v___x_6233_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6217_, v_a_6219_);
if (lean_obj_tag(v___x_6233_) == 0)
{
lean_object* v_a_6234_; lean_object* v___x_6236_; uint8_t v_isShared_6237_; uint8_t v_isSharedCheck_6249_; 
v_a_6234_ = lean_ctor_get(v___x_6233_, 0);
v_isSharedCheck_6249_ = !lean_is_exclusive(v___x_6233_);
if (v_isSharedCheck_6249_ == 0)
{
v___x_6236_ = v___x_6233_;
v_isShared_6237_ = v_isSharedCheck_6249_;
goto v_resetjp_6235_;
}
else
{
lean_inc(v_a_6234_);
lean_dec(v___x_6233_);
v___x_6236_ = lean_box(0);
v_isShared_6237_ = v_isSharedCheck_6249_;
goto v_resetjp_6235_;
}
v_resetjp_6235_:
{
lean_object* v___x_6238_; uint8_t v___x_6239_; 
v___x_6238_ = l_Lean_Expr_cleanupAnnotations(v_a_6234_);
v___x_6239_ = l_Lean_Expr_isApp(v___x_6238_);
if (v___x_6239_ == 0)
{
lean_dec_ref(v___x_6238_);
lean_del_object(v___x_6236_);
v___y_6224_ = v_a_6218_;
v___y_6225_ = v_a_6219_;
v___y_6226_ = v_a_6220_;
v___y_6227_ = v_a_6221_;
goto v___jp_6223_;
}
else
{
lean_object* v_arg_6240_; lean_object* v___x_6241_; uint8_t v___x_6242_; 
v_arg_6240_ = lean_ctor_get(v___x_6238_, 1);
lean_inc_ref(v_arg_6240_);
v___x_6241_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6238_);
v___x_6242_ = l_Lean_Expr_isApp(v___x_6241_);
if (v___x_6242_ == 0)
{
lean_dec_ref(v___x_6241_);
lean_dec_ref(v_arg_6240_);
lean_del_object(v___x_6236_);
v___y_6224_ = v_a_6218_;
v___y_6225_ = v_a_6219_;
v___y_6226_ = v_a_6220_;
v___y_6227_ = v_a_6221_;
goto v___jp_6223_;
}
else
{
lean_object* v___x_6243_; lean_object* v___x_6244_; uint8_t v___x_6245_; 
v___x_6243_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6241_);
v___x_6244_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6245_ = l_Lean_Expr_isConstOf(v___x_6243_, v___x_6244_);
lean_dec_ref(v___x_6243_);
if (v___x_6245_ == 0)
{
lean_dec_ref(v_arg_6240_);
lean_del_object(v___x_6236_);
v___y_6224_ = v_a_6218_;
v___y_6225_ = v_a_6219_;
v___y_6226_ = v_a_6220_;
v___y_6227_ = v_a_6221_;
goto v___jp_6223_;
}
else
{
lean_object* v___x_6247_; 
lean_dec_ref(v_h_6217_);
if (v_isShared_6237_ == 0)
{
lean_ctor_set(v___x_6236_, 0, v_arg_6240_);
v___x_6247_ = v___x_6236_;
goto v_reusejp_6246_;
}
else
{
lean_object* v_reuseFailAlloc_6248_; 
v_reuseFailAlloc_6248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6248_, 0, v_arg_6240_);
v___x_6247_ = v_reuseFailAlloc_6248_;
goto v_reusejp_6246_;
}
v_reusejp_6246_:
{
return v___x_6247_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6217_);
return v___x_6233_;
}
v___jp_6223_:
{
lean_object* v___x_6228_; lean_object* v___x_6229_; lean_object* v___x_6230_; lean_object* v___x_6231_; lean_object* v___x_6232_; 
v___x_6228_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6229_ = lean_unsigned_to_nat(1u);
v___x_6230_ = lean_mk_empty_array_with_capacity(v___x_6229_);
v___x_6231_ = lean_array_push(v___x_6230_, v_h_6217_);
v___x_6232_ = l_Lean_Meta_mkAppM(v___x_6228_, v___x_6231_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_);
return v___x_6232_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6250_, lean_object* v_a_6251_, lean_object* v_a_6252_, lean_object* v_a_6253_, lean_object* v_a_6254_, lean_object* v_a_6255_){
_start:
{
lean_object* v_res_6256_; 
v_res_6256_ = l_Lean_Meta_mkOfEqTrue(v_h_6250_, v_a_6251_, v_a_6252_, v_a_6253_, v_a_6254_);
lean_dec(v_a_6254_);
lean_dec_ref(v_a_6253_);
lean_dec(v_a_6252_);
lean_dec_ref(v_a_6251_);
return v_res_6256_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6257_; lean_object* v___x_6258_; lean_object* v___x_6259_; 
v___x_6257_ = lean_box(0);
v___x_6258_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6259_ = l_Lean_mkConst(v___x_6258_, v___x_6257_);
return v___x_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6260_, lean_object* v_h_6261_){
_start:
{
lean_object* v___x_6265_; uint8_t v___x_6266_; 
lean_inc_ref(v_h_6261_);
v___x_6265_ = l_Lean_Expr_cleanupAnnotations(v_h_6261_);
v___x_6266_ = l_Lean_Expr_isApp(v___x_6265_);
if (v___x_6266_ == 0)
{
lean_dec_ref(v___x_6265_);
goto v___jp_6262_;
}
else
{
lean_object* v_arg_6267_; lean_object* v___x_6268_; uint8_t v___x_6269_; 
v_arg_6267_ = lean_ctor_get(v___x_6265_, 1);
lean_inc_ref(v_arg_6267_);
v___x_6268_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6265_);
v___x_6269_ = l_Lean_Expr_isApp(v___x_6268_);
if (v___x_6269_ == 0)
{
lean_dec_ref(v___x_6268_);
lean_dec_ref(v_arg_6267_);
goto v___jp_6262_;
}
else
{
lean_object* v___x_6270_; lean_object* v___x_6271_; uint8_t v___x_6272_; 
v___x_6270_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6268_);
v___x_6271_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6272_ = l_Lean_Expr_isConstOf(v___x_6270_, v___x_6271_);
lean_dec_ref(v___x_6270_);
if (v___x_6272_ == 0)
{
lean_dec_ref(v_arg_6267_);
goto v___jp_6262_;
}
else
{
lean_dec_ref(v_h_6261_);
lean_dec_ref(v_p_6260_);
return v_arg_6267_;
}
}
}
v___jp_6262_:
{
lean_object* v___x_6263_; lean_object* v___x_6264_; 
v___x_6263_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6264_ = l_Lean_mkAppB(v___x_6263_, v_p_6260_, v_h_6261_);
return v___x_6264_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6273_, lean_object* v_a_6274_, lean_object* v_a_6275_, lean_object* v_a_6276_, lean_object* v_a_6277_){
_start:
{
lean_object* v___y_6280_; lean_object* v___y_6281_; lean_object* v___y_6282_; lean_object* v___y_6283_; lean_object* v___x_6295_; 
lean_inc_ref(v_h_6273_);
v___x_6295_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6273_, v_a_6275_);
if (lean_obj_tag(v___x_6295_) == 0)
{
lean_object* v_a_6296_; lean_object* v___x_6298_; uint8_t v_isShared_6299_; uint8_t v_isSharedCheck_6311_; 
v_a_6296_ = lean_ctor_get(v___x_6295_, 0);
v_isSharedCheck_6311_ = !lean_is_exclusive(v___x_6295_);
if (v_isSharedCheck_6311_ == 0)
{
v___x_6298_ = v___x_6295_;
v_isShared_6299_ = v_isSharedCheck_6311_;
goto v_resetjp_6297_;
}
else
{
lean_inc(v_a_6296_);
lean_dec(v___x_6295_);
v___x_6298_ = lean_box(0);
v_isShared_6299_ = v_isSharedCheck_6311_;
goto v_resetjp_6297_;
}
v_resetjp_6297_:
{
lean_object* v___x_6300_; uint8_t v___x_6301_; 
v___x_6300_ = l_Lean_Expr_cleanupAnnotations(v_a_6296_);
v___x_6301_ = l_Lean_Expr_isApp(v___x_6300_);
if (v___x_6301_ == 0)
{
lean_dec_ref(v___x_6300_);
lean_del_object(v___x_6298_);
v___y_6280_ = v_a_6274_;
v___y_6281_ = v_a_6275_;
v___y_6282_ = v_a_6276_;
v___y_6283_ = v_a_6277_;
goto v___jp_6279_;
}
else
{
lean_object* v_arg_6302_; lean_object* v___x_6303_; uint8_t v___x_6304_; 
v_arg_6302_ = lean_ctor_get(v___x_6300_, 1);
lean_inc_ref(v_arg_6302_);
v___x_6303_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6300_);
v___x_6304_ = l_Lean_Expr_isApp(v___x_6303_);
if (v___x_6304_ == 0)
{
lean_dec_ref(v___x_6303_);
lean_dec_ref(v_arg_6302_);
lean_del_object(v___x_6298_);
v___y_6280_ = v_a_6274_;
v___y_6281_ = v_a_6275_;
v___y_6282_ = v_a_6276_;
v___y_6283_ = v_a_6277_;
goto v___jp_6279_;
}
else
{
lean_object* v___x_6305_; lean_object* v___x_6306_; uint8_t v___x_6307_; 
v___x_6305_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6303_);
v___x_6306_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6307_ = l_Lean_Expr_isConstOf(v___x_6305_, v___x_6306_);
lean_dec_ref(v___x_6305_);
if (v___x_6307_ == 0)
{
lean_dec_ref(v_arg_6302_);
lean_del_object(v___x_6298_);
v___y_6280_ = v_a_6274_;
v___y_6281_ = v_a_6275_;
v___y_6282_ = v_a_6276_;
v___y_6283_ = v_a_6277_;
goto v___jp_6279_;
}
else
{
lean_object* v___x_6309_; 
lean_dec_ref(v_h_6273_);
if (v_isShared_6299_ == 0)
{
lean_ctor_set(v___x_6298_, 0, v_arg_6302_);
v___x_6309_ = v___x_6298_;
goto v_reusejp_6308_;
}
else
{
lean_object* v_reuseFailAlloc_6310_; 
v_reuseFailAlloc_6310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6310_, 0, v_arg_6302_);
v___x_6309_ = v_reuseFailAlloc_6310_;
goto v_reusejp_6308_;
}
v_reusejp_6308_:
{
return v___x_6309_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6273_);
return v___x_6295_;
}
v___jp_6279_:
{
lean_object* v___x_6284_; 
lean_inc(v___y_6283_);
lean_inc_ref(v___y_6282_);
lean_inc(v___y_6281_);
lean_inc_ref(v___y_6280_);
lean_inc_ref(v_h_6273_);
v___x_6284_ = lean_infer_type(v_h_6273_, v___y_6280_, v___y_6281_, v___y_6282_, v___y_6283_);
if (lean_obj_tag(v___x_6284_) == 0)
{
lean_object* v_a_6285_; lean_object* v___x_6287_; uint8_t v_isShared_6288_; uint8_t v_isSharedCheck_6294_; 
v_a_6285_ = lean_ctor_get(v___x_6284_, 0);
v_isSharedCheck_6294_ = !lean_is_exclusive(v___x_6284_);
if (v_isSharedCheck_6294_ == 0)
{
v___x_6287_ = v___x_6284_;
v_isShared_6288_ = v_isSharedCheck_6294_;
goto v_resetjp_6286_;
}
else
{
lean_inc(v_a_6285_);
lean_dec(v___x_6284_);
v___x_6287_ = lean_box(0);
v_isShared_6288_ = v_isSharedCheck_6294_;
goto v_resetjp_6286_;
}
v_resetjp_6286_:
{
lean_object* v___x_6289_; lean_object* v___x_6290_; lean_object* v___x_6292_; 
v___x_6289_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6290_ = l_Lean_mkAppB(v___x_6289_, v_a_6285_, v_h_6273_);
if (v_isShared_6288_ == 0)
{
lean_ctor_set(v___x_6287_, 0, v___x_6290_);
v___x_6292_ = v___x_6287_;
goto v_reusejp_6291_;
}
else
{
lean_object* v_reuseFailAlloc_6293_; 
v_reuseFailAlloc_6293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6293_, 0, v___x_6290_);
v___x_6292_ = v_reuseFailAlloc_6293_;
goto v_reusejp_6291_;
}
v_reusejp_6291_:
{
return v___x_6292_;
}
}
}
else
{
lean_dec_ref(v_h_6273_);
return v___x_6284_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6312_, lean_object* v_a_6313_, lean_object* v_a_6314_, lean_object* v_a_6315_, lean_object* v_a_6316_, lean_object* v_a_6317_){
_start:
{
lean_object* v_res_6318_; 
v_res_6318_ = l_Lean_Meta_mkEqTrue(v_h_6312_, v_a_6313_, v_a_6314_, v_a_6315_, v_a_6316_);
lean_dec(v_a_6316_);
lean_dec_ref(v_a_6315_);
lean_dec(v_a_6314_);
lean_dec_ref(v_a_6313_);
return v_res_6318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6319_, lean_object* v_a_6320_, lean_object* v_a_6321_, lean_object* v_a_6322_, lean_object* v_a_6323_){
_start:
{
lean_object* v___y_6326_; lean_object* v___y_6327_; lean_object* v___y_6328_; lean_object* v___y_6329_; lean_object* v___x_6335_; uint8_t v___x_6336_; 
lean_inc_ref(v_h_6319_);
v___x_6335_ = l_Lean_Expr_cleanupAnnotations(v_h_6319_);
v___x_6336_ = l_Lean_Expr_isApp(v___x_6335_);
if (v___x_6336_ == 0)
{
lean_dec_ref(v___x_6335_);
v___y_6326_ = v_a_6320_;
v___y_6327_ = v_a_6321_;
v___y_6328_ = v_a_6322_;
v___y_6329_ = v_a_6323_;
goto v___jp_6325_;
}
else
{
lean_object* v_arg_6337_; lean_object* v___x_6338_; uint8_t v___x_6339_; 
v_arg_6337_ = lean_ctor_get(v___x_6335_, 1);
lean_inc_ref(v_arg_6337_);
v___x_6338_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6335_);
v___x_6339_ = l_Lean_Expr_isApp(v___x_6338_);
if (v___x_6339_ == 0)
{
lean_dec_ref(v___x_6338_);
lean_dec_ref(v_arg_6337_);
v___y_6326_ = v_a_6320_;
v___y_6327_ = v_a_6321_;
v___y_6328_ = v_a_6322_;
v___y_6329_ = v_a_6323_;
goto v___jp_6325_;
}
else
{
lean_object* v___x_6340_; lean_object* v___x_6341_; uint8_t v___x_6342_; 
v___x_6340_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6338_);
v___x_6341_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6342_ = l_Lean_Expr_isConstOf(v___x_6340_, v___x_6341_);
lean_dec_ref(v___x_6340_);
if (v___x_6342_ == 0)
{
lean_dec_ref(v_arg_6337_);
v___y_6326_ = v_a_6320_;
v___y_6327_ = v_a_6321_;
v___y_6328_ = v_a_6322_;
v___y_6329_ = v_a_6323_;
goto v___jp_6325_;
}
else
{
lean_object* v___x_6343_; 
lean_dec_ref(v_h_6319_);
v___x_6343_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6343_, 0, v_arg_6337_);
return v___x_6343_;
}
}
}
v___jp_6325_:
{
lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; lean_object* v___x_6333_; lean_object* v___x_6334_; 
v___x_6330_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6331_ = lean_unsigned_to_nat(1u);
v___x_6332_ = lean_mk_empty_array_with_capacity(v___x_6331_);
v___x_6333_ = lean_array_push(v___x_6332_, v_h_6319_);
v___x_6334_ = l_Lean_Meta_mkAppM(v___x_6330_, v___x_6333_, v___y_6326_, v___y_6327_, v___y_6328_, v___y_6329_);
return v___x_6334_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6344_, lean_object* v_a_6345_, lean_object* v_a_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_, lean_object* v_a_6349_){
_start:
{
lean_object* v_res_6350_; 
v_res_6350_ = l_Lean_Meta_mkEqFalse(v_h_6344_, v_a_6345_, v_a_6346_, v_a_6347_, v_a_6348_);
lean_dec(v_a_6348_);
lean_dec_ref(v_a_6347_);
lean_dec(v_a_6346_);
lean_dec_ref(v_a_6345_);
return v_res_6350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6354_, lean_object* v_a_6355_, lean_object* v_a_6356_, lean_object* v_a_6357_, lean_object* v_a_6358_){
_start:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6362_; lean_object* v___x_6363_; lean_object* v___x_6364_; 
v___x_6360_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6361_ = lean_unsigned_to_nat(1u);
v___x_6362_ = lean_mk_empty_array_with_capacity(v___x_6361_);
v___x_6363_ = lean_array_push(v___x_6362_, v_h_6354_);
v___x_6364_ = l_Lean_Meta_mkAppM(v___x_6360_, v___x_6363_, v_a_6355_, v_a_6356_, v_a_6357_, v_a_6358_);
return v___x_6364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6365_, lean_object* v_a_6366_, lean_object* v_a_6367_, lean_object* v_a_6368_, lean_object* v_a_6369_, lean_object* v_a_6370_){
_start:
{
lean_object* v_res_6371_; 
v_res_6371_ = l_Lean_Meta_mkEqFalse_x27(v_h_6365_, v_a_6366_, v_a_6367_, v_a_6368_, v_a_6369_);
lean_dec(v_a_6369_);
lean_dec_ref(v_a_6368_);
lean_dec(v_a_6367_);
lean_dec_ref(v_a_6366_);
return v_res_6371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6375_, lean_object* v_h_u2082_6376_, lean_object* v_a_6377_, lean_object* v_a_6378_, lean_object* v_a_6379_, lean_object* v_a_6380_){
_start:
{
lean_object* v___x_6382_; lean_object* v___x_6383_; lean_object* v___x_6384_; lean_object* v___x_6385_; lean_object* v___x_6386_; lean_object* v___x_6387_; 
v___x_6382_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6383_ = lean_unsigned_to_nat(2u);
v___x_6384_ = lean_mk_empty_array_with_capacity(v___x_6383_);
v___x_6385_ = lean_array_push(v___x_6384_, v_h_u2081_6375_);
v___x_6386_ = lean_array_push(v___x_6385_, v_h_u2082_6376_);
v___x_6387_ = l_Lean_Meta_mkAppM(v___x_6382_, v___x_6386_, v_a_6377_, v_a_6378_, v_a_6379_, v_a_6380_);
return v___x_6387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6388_, lean_object* v_h_u2082_6389_, lean_object* v_a_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_){
_start:
{
lean_object* v_res_6395_; 
v_res_6395_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6388_, v_h_u2082_6389_, v_a_6390_, v_a_6391_, v_a_6392_, v_a_6393_);
lean_dec(v_a_6393_);
lean_dec_ref(v_a_6392_);
lean_dec(v_a_6391_);
lean_dec_ref(v_a_6390_);
return v_res_6395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6399_, lean_object* v_h_u2082_6400_, lean_object* v_a_6401_, lean_object* v_a_6402_, lean_object* v_a_6403_, lean_object* v_a_6404_){
_start:
{
lean_object* v___x_6406_; lean_object* v___x_6407_; lean_object* v___x_6408_; lean_object* v___x_6409_; lean_object* v___x_6410_; lean_object* v___x_6411_; 
v___x_6406_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6407_ = lean_unsigned_to_nat(2u);
v___x_6408_ = lean_mk_empty_array_with_capacity(v___x_6407_);
v___x_6409_ = lean_array_push(v___x_6408_, v_h_u2081_6399_);
v___x_6410_ = lean_array_push(v___x_6409_, v_h_u2082_6400_);
v___x_6411_ = l_Lean_Meta_mkAppM(v___x_6406_, v___x_6410_, v_a_6401_, v_a_6402_, v_a_6403_, v_a_6404_);
return v___x_6411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6412_, lean_object* v_h_u2082_6413_, lean_object* v_a_6414_, lean_object* v_a_6415_, lean_object* v_a_6416_, lean_object* v_a_6417_, lean_object* v_a_6418_){
_start:
{
lean_object* v_res_6419_; 
v_res_6419_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6412_, v_h_u2082_6413_, v_a_6414_, v_a_6415_, v_a_6416_, v_a_6417_);
lean_dec(v_a_6417_);
lean_dec_ref(v_a_6416_);
lean_dec(v_a_6415_);
lean_dec_ref(v_a_6414_);
return v_res_6419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6423_, lean_object* v_h_u2082_6424_, lean_object* v_a_6425_, lean_object* v_a_6426_, lean_object* v_a_6427_, lean_object* v_a_6428_){
_start:
{
lean_object* v___x_6430_; lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; 
v___x_6430_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6431_ = lean_unsigned_to_nat(2u);
v___x_6432_ = lean_mk_empty_array_with_capacity(v___x_6431_);
v___x_6433_ = lean_array_push(v___x_6432_, v_h_u2081_6423_);
v___x_6434_ = lean_array_push(v___x_6433_, v_h_u2082_6424_);
v___x_6435_ = l_Lean_Meta_mkAppM(v___x_6430_, v___x_6434_, v_a_6425_, v_a_6426_, v_a_6427_, v_a_6428_);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6436_, lean_object* v_h_u2082_6437_, lean_object* v_a_6438_, lean_object* v_a_6439_, lean_object* v_a_6440_, lean_object* v_a_6441_, lean_object* v_a_6442_){
_start:
{
lean_object* v_res_6443_; 
v_res_6443_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6436_, v_h_u2082_6437_, v_a_6438_, v_a_6439_, v_a_6440_, v_a_6441_);
lean_dec(v_a_6441_);
lean_dec_ref(v_a_6440_);
lean_dec(v_a_6439_);
lean_dec_ref(v_a_6438_);
return v_res_6443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_, lean_object* v_a_6450_, lean_object* v_a_6451_){
_start:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; lean_object* v___x_6457_; 
v___x_6453_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6454_ = lean_unsigned_to_nat(1u);
v___x_6455_ = lean_mk_empty_array_with_capacity(v___x_6454_);
v___x_6456_ = lean_array_push(v___x_6455_, v_h_6447_);
v___x_6457_ = l_Lean_Meta_mkAppM(v___x_6453_, v___x_6456_, v_a_6448_, v_a_6449_, v_a_6450_, v_a_6451_);
return v___x_6457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6458_, lean_object* v_a_6459_, lean_object* v_a_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_){
_start:
{
lean_object* v_res_6464_; 
v_res_6464_ = l_Lean_Meta_mkForallCongr(v_h_6458_, v_a_6459_, v_a_6460_, v_a_6461_, v_a_6462_);
lean_dec(v_a_6462_);
lean_dec_ref(v_a_6461_);
lean_dec(v_a_6460_);
lean_dec_ref(v_a_6459_);
return v_res_6464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6468_, lean_object* v_a_6469_, lean_object* v_a_6470_, lean_object* v_a_6471_, lean_object* v_a_6472_){
_start:
{
lean_object* v___y_6475_; uint8_t v___y_6476_; lean_object* v___y_6480_; lean_object* v_a_6481_; lean_object* v___x_6484_; lean_object* v___x_6485_; lean_object* v___x_6486_; lean_object* v___x_6487_; lean_object* v___x_6488_; 
v___x_6484_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6485_ = lean_unsigned_to_nat(1u);
v___x_6486_ = lean_mk_empty_array_with_capacity(v___x_6485_);
v___x_6487_ = lean_array_push(v___x_6486_, v_m_6468_);
v___x_6488_ = l_Lean_Meta_mkAppM(v___x_6484_, v___x_6487_, v_a_6469_, v_a_6470_, v_a_6471_, v_a_6472_);
if (lean_obj_tag(v___x_6488_) == 0)
{
lean_object* v_a_6489_; lean_object* v___x_6490_; lean_object* v___x_6491_; 
v_a_6489_ = lean_ctor_get(v___x_6488_, 0);
lean_inc(v_a_6489_);
lean_dec_ref_known(v___x_6488_, 1);
v___x_6490_ = lean_box(0);
v___x_6491_ = l_Lean_Meta_trySynthInstance(v_a_6489_, v___x_6490_, v_a_6469_, v_a_6470_, v_a_6471_, v_a_6472_);
if (lean_obj_tag(v___x_6491_) == 0)
{
lean_object* v_a_6492_; lean_object* v___x_6494_; uint8_t v_isShared_6495_; uint8_t v_isSharedCheck_6510_; 
v_a_6492_ = lean_ctor_get(v___x_6491_, 0);
v_isSharedCheck_6510_ = !lean_is_exclusive(v___x_6491_);
if (v_isSharedCheck_6510_ == 0)
{
v___x_6494_ = v___x_6491_;
v_isShared_6495_ = v_isSharedCheck_6510_;
goto v_resetjp_6493_;
}
else
{
lean_inc(v_a_6492_);
lean_dec(v___x_6491_);
v___x_6494_ = lean_box(0);
v_isShared_6495_ = v_isSharedCheck_6510_;
goto v_resetjp_6493_;
}
v_resetjp_6493_:
{
if (lean_obj_tag(v_a_6492_) == 1)
{
lean_object* v_a_6496_; lean_object* v___x_6498_; uint8_t v_isShared_6499_; uint8_t v_isSharedCheck_6506_; 
v_a_6496_ = lean_ctor_get(v_a_6492_, 0);
v_isSharedCheck_6506_ = !lean_is_exclusive(v_a_6492_);
if (v_isSharedCheck_6506_ == 0)
{
v___x_6498_ = v_a_6492_;
v_isShared_6499_ = v_isSharedCheck_6506_;
goto v_resetjp_6497_;
}
else
{
lean_inc(v_a_6496_);
lean_dec(v_a_6492_);
v___x_6498_ = lean_box(0);
v_isShared_6499_ = v_isSharedCheck_6506_;
goto v_resetjp_6497_;
}
v_resetjp_6497_:
{
lean_object* v___x_6501_; 
if (v_isShared_6499_ == 0)
{
v___x_6501_ = v___x_6498_;
goto v_reusejp_6500_;
}
else
{
lean_object* v_reuseFailAlloc_6505_; 
v_reuseFailAlloc_6505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6505_, 0, v_a_6496_);
v___x_6501_ = v_reuseFailAlloc_6505_;
goto v_reusejp_6500_;
}
v_reusejp_6500_:
{
lean_object* v___x_6503_; 
if (v_isShared_6495_ == 0)
{
lean_ctor_set(v___x_6494_, 0, v___x_6501_);
v___x_6503_ = v___x_6494_;
goto v_reusejp_6502_;
}
else
{
lean_object* v_reuseFailAlloc_6504_; 
v_reuseFailAlloc_6504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6504_, 0, v___x_6501_);
v___x_6503_ = v_reuseFailAlloc_6504_;
goto v_reusejp_6502_;
}
v_reusejp_6502_:
{
return v___x_6503_;
}
}
}
}
else
{
lean_object* v___x_6508_; 
lean_dec(v_a_6492_);
if (v_isShared_6495_ == 0)
{
lean_ctor_set(v___x_6494_, 0, v___x_6490_);
v___x_6508_ = v___x_6494_;
goto v_reusejp_6507_;
}
else
{
lean_object* v_reuseFailAlloc_6509_; 
v_reuseFailAlloc_6509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6509_, 0, v___x_6490_);
v___x_6508_ = v_reuseFailAlloc_6509_;
goto v_reusejp_6507_;
}
v_reusejp_6507_:
{
return v___x_6508_;
}
}
}
}
else
{
lean_object* v_a_6511_; lean_object* v___x_6513_; uint8_t v_isShared_6514_; uint8_t v_isSharedCheck_6518_; 
v_a_6511_ = lean_ctor_get(v___x_6491_, 0);
v_isSharedCheck_6518_ = !lean_is_exclusive(v___x_6491_);
if (v_isSharedCheck_6518_ == 0)
{
v___x_6513_ = v___x_6491_;
v_isShared_6514_ = v_isSharedCheck_6518_;
goto v_resetjp_6512_;
}
else
{
lean_inc(v_a_6511_);
lean_dec(v___x_6491_);
v___x_6513_ = lean_box(0);
v_isShared_6514_ = v_isSharedCheck_6518_;
goto v_resetjp_6512_;
}
v_resetjp_6512_:
{
lean_object* v___x_6516_; 
lean_inc(v_a_6511_);
if (v_isShared_6514_ == 0)
{
v___x_6516_ = v___x_6513_;
goto v_reusejp_6515_;
}
else
{
lean_object* v_reuseFailAlloc_6517_; 
v_reuseFailAlloc_6517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6517_, 0, v_a_6511_);
v___x_6516_ = v_reuseFailAlloc_6517_;
goto v_reusejp_6515_;
}
v_reusejp_6515_:
{
v___y_6480_ = v___x_6516_;
v_a_6481_ = v_a_6511_;
goto v___jp_6479_;
}
}
}
}
else
{
lean_object* v_a_6519_; lean_object* v___x_6521_; uint8_t v_isShared_6522_; uint8_t v_isSharedCheck_6526_; 
v_a_6519_ = lean_ctor_get(v___x_6488_, 0);
v_isSharedCheck_6526_ = !lean_is_exclusive(v___x_6488_);
if (v_isSharedCheck_6526_ == 0)
{
v___x_6521_ = v___x_6488_;
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
else
{
lean_inc(v_a_6519_);
lean_dec(v___x_6488_);
v___x_6521_ = lean_box(0);
v_isShared_6522_ = v_isSharedCheck_6526_;
goto v_resetjp_6520_;
}
v_resetjp_6520_:
{
lean_object* v___x_6524_; 
lean_inc(v_a_6519_);
if (v_isShared_6522_ == 0)
{
v___x_6524_ = v___x_6521_;
goto v_reusejp_6523_;
}
else
{
lean_object* v_reuseFailAlloc_6525_; 
v_reuseFailAlloc_6525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6525_, 0, v_a_6519_);
v___x_6524_ = v_reuseFailAlloc_6525_;
goto v_reusejp_6523_;
}
v_reusejp_6523_:
{
v___y_6480_ = v___x_6524_;
v_a_6481_ = v_a_6519_;
goto v___jp_6479_;
}
}
}
v___jp_6474_:
{
if (v___y_6476_ == 0)
{
lean_object* v___x_6477_; lean_object* v___x_6478_; 
lean_dec_ref(v___y_6475_);
v___x_6477_ = lean_box(0);
v___x_6478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6478_, 0, v___x_6477_);
return v___x_6478_;
}
else
{
return v___y_6475_;
}
}
v___jp_6479_:
{
uint8_t v___x_6482_; 
v___x_6482_ = l_Lean_Exception_isInterrupt(v_a_6481_);
if (v___x_6482_ == 0)
{
uint8_t v___x_6483_; 
v___x_6483_ = l_Lean_Exception_isRuntime(v_a_6481_);
v___y_6475_ = v___y_6480_;
v___y_6476_ = v___x_6483_;
goto v___jp_6474_;
}
else
{
lean_dec_ref(v_a_6481_);
v___y_6475_ = v___y_6480_;
v___y_6476_ = v___x_6482_;
goto v___jp_6474_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6527_, lean_object* v_a_6528_, lean_object* v_a_6529_, lean_object* v_a_6530_, lean_object* v_a_6531_, lean_object* v_a_6532_){
_start:
{
lean_object* v_res_6533_; 
v_res_6533_ = l_Lean_Meta_isMonad_x3f(v_m_6527_, v_a_6528_, v_a_6529_, v_a_6530_, v_a_6531_);
lean_dec(v_a_6531_);
lean_dec_ref(v_a_6530_);
lean_dec(v_a_6529_);
lean_dec_ref(v_a_6528_);
return v_res_6533_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6541_, lean_object* v_n_6542_, lean_object* v_a_6543_, lean_object* v_a_6544_, lean_object* v_a_6545_, lean_object* v_a_6546_){
_start:
{
lean_object* v___x_6548_; 
lean_inc_ref(v_type_6541_);
v___x_6548_ = l_Lean_Meta_getDecLevel(v_type_6541_, v_a_6543_, v_a_6544_, v_a_6545_, v_a_6546_);
if (lean_obj_tag(v___x_6548_) == 0)
{
lean_object* v_a_6549_; lean_object* v___x_6550_; lean_object* v___x_6551_; lean_object* v___x_6552_; lean_object* v___x_6553_; lean_object* v___x_6554_; lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; 
v_a_6549_ = lean_ctor_get(v___x_6548_, 0);
lean_inc(v_a_6549_);
lean_dec_ref_known(v___x_6548_, 1);
v___x_6550_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6551_ = lean_box(0);
v___x_6552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6552_, 0, v_a_6549_);
lean_ctor_set(v___x_6552_, 1, v___x_6551_);
lean_inc_ref(v___x_6552_);
v___x_6553_ = l_Lean_mkConst(v___x_6550_, v___x_6552_);
v___x_6554_ = l_Lean_mkRawNatLit(v_n_6542_);
lean_inc_ref(v___x_6554_);
lean_inc_ref(v_type_6541_);
v___x_6555_ = l_Lean_mkAppB(v___x_6553_, v_type_6541_, v___x_6554_);
v___x_6556_ = lean_box(0);
v___x_6557_ = l_Lean_Meta_synthInstance(v___x_6555_, v___x_6556_, v_a_6543_, v_a_6544_, v_a_6545_, v_a_6546_);
if (lean_obj_tag(v___x_6557_) == 0)
{
lean_object* v_a_6558_; lean_object* v___x_6560_; uint8_t v_isShared_6561_; uint8_t v_isSharedCheck_6568_; 
v_a_6558_ = lean_ctor_get(v___x_6557_, 0);
v_isSharedCheck_6568_ = !lean_is_exclusive(v___x_6557_);
if (v_isSharedCheck_6568_ == 0)
{
v___x_6560_ = v___x_6557_;
v_isShared_6561_ = v_isSharedCheck_6568_;
goto v_resetjp_6559_;
}
else
{
lean_inc(v_a_6558_);
lean_dec(v___x_6557_);
v___x_6560_ = lean_box(0);
v_isShared_6561_ = v_isSharedCheck_6568_;
goto v_resetjp_6559_;
}
v_resetjp_6559_:
{
lean_object* v___x_6562_; lean_object* v___x_6563_; lean_object* v___x_6564_; lean_object* v___x_6566_; 
v___x_6562_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6563_ = l_Lean_mkConst(v___x_6562_, v___x_6552_);
v___x_6564_ = l_Lean_mkApp3(v___x_6563_, v_type_6541_, v___x_6554_, v_a_6558_);
if (v_isShared_6561_ == 0)
{
lean_ctor_set(v___x_6560_, 0, v___x_6564_);
v___x_6566_ = v___x_6560_;
goto v_reusejp_6565_;
}
else
{
lean_object* v_reuseFailAlloc_6567_; 
v_reuseFailAlloc_6567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6567_, 0, v___x_6564_);
v___x_6566_ = v_reuseFailAlloc_6567_;
goto v_reusejp_6565_;
}
v_reusejp_6565_:
{
return v___x_6566_;
}
}
}
else
{
lean_dec_ref(v___x_6554_);
lean_dec_ref_known(v___x_6552_, 2);
lean_dec_ref(v_type_6541_);
return v___x_6557_;
}
}
else
{
lean_object* v_a_6569_; lean_object* v___x_6571_; uint8_t v_isShared_6572_; uint8_t v_isSharedCheck_6576_; 
lean_dec(v_n_6542_);
lean_dec_ref(v_type_6541_);
v_a_6569_ = lean_ctor_get(v___x_6548_, 0);
v_isSharedCheck_6576_ = !lean_is_exclusive(v___x_6548_);
if (v_isSharedCheck_6576_ == 0)
{
v___x_6571_ = v___x_6548_;
v_isShared_6572_ = v_isSharedCheck_6576_;
goto v_resetjp_6570_;
}
else
{
lean_inc(v_a_6569_);
lean_dec(v___x_6548_);
v___x_6571_ = lean_box(0);
v_isShared_6572_ = v_isSharedCheck_6576_;
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
lean_object* v_reuseFailAlloc_6575_; 
v_reuseFailAlloc_6575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6575_, 0, v_a_6569_);
v___x_6574_ = v_reuseFailAlloc_6575_;
goto v_reusejp_6573_;
}
v_reusejp_6573_:
{
return v___x_6574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6577_, lean_object* v_n_6578_, lean_object* v_a_6579_, lean_object* v_a_6580_, lean_object* v_a_6581_, lean_object* v_a_6582_, lean_object* v_a_6583_){
_start:
{
lean_object* v_res_6584_; 
v_res_6584_ = l_Lean_Meta_mkNumeral(v_type_6577_, v_n_6578_, v_a_6579_, v_a_6580_, v_a_6581_, v_a_6582_);
lean_dec(v_a_6582_);
lean_dec_ref(v_a_6581_);
lean_dec(v_a_6580_);
lean_dec_ref(v_a_6579_);
return v_res_6584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6585_, lean_object* v_opName_6586_, lean_object* v_a_6587_, lean_object* v_b_6588_, lean_object* v_a_6589_, lean_object* v_a_6590_, lean_object* v_a_6591_, lean_object* v_a_6592_){
_start:
{
lean_object* v___x_6594_; 
lean_inc(v_a_6592_);
lean_inc_ref(v_a_6591_);
lean_inc(v_a_6590_);
lean_inc_ref(v_a_6589_);
lean_inc_ref(v_a_6587_);
v___x_6594_ = lean_infer_type(v_a_6587_, v_a_6589_, v_a_6590_, v_a_6591_, v_a_6592_);
if (lean_obj_tag(v___x_6594_) == 0)
{
lean_object* v_a_6595_; lean_object* v___x_6596_; 
v_a_6595_ = lean_ctor_get(v___x_6594_, 0);
lean_inc_n(v_a_6595_, 2);
lean_dec_ref_known(v___x_6594_, 1);
v___x_6596_ = l_Lean_Meta_getDecLevel(v_a_6595_, v_a_6589_, v_a_6590_, v_a_6591_, v_a_6592_);
if (lean_obj_tag(v___x_6596_) == 0)
{
lean_object* v_a_6597_; lean_object* v___x_6598_; lean_object* v___x_6599_; lean_object* v___x_6600_; lean_object* v___x_6601_; lean_object* v___x_6602_; lean_object* v___x_6603_; lean_object* v___x_6604_; lean_object* v___x_6605_; 
v_a_6597_ = lean_ctor_get(v___x_6596_, 0);
lean_inc_n(v_a_6597_, 3);
lean_dec_ref_known(v___x_6596_, 1);
v___x_6598_ = lean_box(0);
v___x_6599_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6599_, 0, v_a_6597_);
lean_ctor_set(v___x_6599_, 1, v___x_6598_);
v___x_6600_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6600_, 0, v_a_6597_);
lean_ctor_set(v___x_6600_, 1, v___x_6599_);
v___x_6601_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6601_, 0, v_a_6597_);
lean_ctor_set(v___x_6601_, 1, v___x_6600_);
lean_inc_ref(v___x_6601_);
v___x_6602_ = l_Lean_mkConst(v_className_6585_, v___x_6601_);
lean_inc_n(v_a_6595_, 3);
v___x_6603_ = l_Lean_mkApp3(v___x_6602_, v_a_6595_, v_a_6595_, v_a_6595_);
v___x_6604_ = lean_box(0);
v___x_6605_ = l_Lean_Meta_synthInstance(v___x_6603_, v___x_6604_, v_a_6589_, v_a_6590_, v_a_6591_, v_a_6592_);
if (lean_obj_tag(v___x_6605_) == 0)
{
lean_object* v_a_6606_; lean_object* v___x_6608_; uint8_t v_isShared_6609_; uint8_t v_isSharedCheck_6615_; 
v_a_6606_ = lean_ctor_get(v___x_6605_, 0);
v_isSharedCheck_6615_ = !lean_is_exclusive(v___x_6605_);
if (v_isSharedCheck_6615_ == 0)
{
v___x_6608_ = v___x_6605_;
v_isShared_6609_ = v_isSharedCheck_6615_;
goto v_resetjp_6607_;
}
else
{
lean_inc(v_a_6606_);
lean_dec(v___x_6605_);
v___x_6608_ = lean_box(0);
v_isShared_6609_ = v_isSharedCheck_6615_;
goto v_resetjp_6607_;
}
v_resetjp_6607_:
{
lean_object* v___x_6610_; lean_object* v___x_6611_; lean_object* v___x_6613_; 
v___x_6610_ = l_Lean_mkConst(v_opName_6586_, v___x_6601_);
lean_inc_n(v_a_6595_, 2);
v___x_6611_ = l_Lean_mkApp6(v___x_6610_, v_a_6595_, v_a_6595_, v_a_6595_, v_a_6606_, v_a_6587_, v_b_6588_);
if (v_isShared_6609_ == 0)
{
lean_ctor_set(v___x_6608_, 0, v___x_6611_);
v___x_6613_ = v___x_6608_;
goto v_reusejp_6612_;
}
else
{
lean_object* v_reuseFailAlloc_6614_; 
v_reuseFailAlloc_6614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6614_, 0, v___x_6611_);
v___x_6613_ = v_reuseFailAlloc_6614_;
goto v_reusejp_6612_;
}
v_reusejp_6612_:
{
return v___x_6613_;
}
}
}
else
{
lean_dec_ref_known(v___x_6601_, 2);
lean_dec(v_a_6595_);
lean_dec_ref(v_b_6588_);
lean_dec_ref(v_a_6587_);
lean_dec(v_opName_6586_);
return v___x_6605_;
}
}
else
{
lean_object* v_a_6616_; lean_object* v___x_6618_; uint8_t v_isShared_6619_; uint8_t v_isSharedCheck_6623_; 
lean_dec(v_a_6595_);
lean_dec_ref(v_b_6588_);
lean_dec_ref(v_a_6587_);
lean_dec(v_opName_6586_);
lean_dec(v_className_6585_);
v_a_6616_ = lean_ctor_get(v___x_6596_, 0);
v_isSharedCheck_6623_ = !lean_is_exclusive(v___x_6596_);
if (v_isSharedCheck_6623_ == 0)
{
v___x_6618_ = v___x_6596_;
v_isShared_6619_ = v_isSharedCheck_6623_;
goto v_resetjp_6617_;
}
else
{
lean_inc(v_a_6616_);
lean_dec(v___x_6596_);
v___x_6618_ = lean_box(0);
v_isShared_6619_ = v_isSharedCheck_6623_;
goto v_resetjp_6617_;
}
v_resetjp_6617_:
{
lean_object* v___x_6621_; 
if (v_isShared_6619_ == 0)
{
v___x_6621_ = v___x_6618_;
goto v_reusejp_6620_;
}
else
{
lean_object* v_reuseFailAlloc_6622_; 
v_reuseFailAlloc_6622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6622_, 0, v_a_6616_);
v___x_6621_ = v_reuseFailAlloc_6622_;
goto v_reusejp_6620_;
}
v_reusejp_6620_:
{
return v___x_6621_;
}
}
}
}
else
{
lean_dec_ref(v_b_6588_);
lean_dec_ref(v_a_6587_);
lean_dec(v_opName_6586_);
lean_dec(v_className_6585_);
return v___x_6594_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6624_, lean_object* v_opName_6625_, lean_object* v_a_6626_, lean_object* v_b_6627_, lean_object* v_a_6628_, lean_object* v_a_6629_, lean_object* v_a_6630_, lean_object* v_a_6631_, lean_object* v_a_6632_){
_start:
{
lean_object* v_res_6633_; 
v_res_6633_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6624_, v_opName_6625_, v_a_6626_, v_b_6627_, v_a_6628_, v_a_6629_, v_a_6630_, v_a_6631_);
lean_dec(v_a_6631_);
lean_dec_ref(v_a_6630_);
lean_dec(v_a_6629_);
lean_dec_ref(v_a_6628_);
return v_res_6633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6641_, lean_object* v_b_6642_, lean_object* v_a_6643_, lean_object* v_a_6644_, lean_object* v_a_6645_, lean_object* v_a_6646_){
_start:
{
lean_object* v___x_6648_; lean_object* v___x_6649_; lean_object* v___x_6650_; 
v___x_6648_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6649_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6650_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6648_, v___x_6649_, v_a_6641_, v_b_6642_, v_a_6643_, v_a_6644_, v_a_6645_, v_a_6646_);
return v___x_6650_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6651_, lean_object* v_b_6652_, lean_object* v_a_6653_, lean_object* v_a_6654_, lean_object* v_a_6655_, lean_object* v_a_6656_, lean_object* v_a_6657_){
_start:
{
lean_object* v_res_6658_; 
v_res_6658_ = l_Lean_Meta_mkAdd(v_a_6651_, v_b_6652_, v_a_6653_, v_a_6654_, v_a_6655_, v_a_6656_);
lean_dec(v_a_6656_);
lean_dec_ref(v_a_6655_);
lean_dec(v_a_6654_);
lean_dec_ref(v_a_6653_);
return v_res_6658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6666_, lean_object* v_b_6667_, lean_object* v_a_6668_, lean_object* v_a_6669_, lean_object* v_a_6670_, lean_object* v_a_6671_){
_start:
{
lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; 
v___x_6673_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6674_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6675_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6673_, v___x_6674_, v_a_6666_, v_b_6667_, v_a_6668_, v_a_6669_, v_a_6670_, v_a_6671_);
return v___x_6675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6676_, lean_object* v_b_6677_, lean_object* v_a_6678_, lean_object* v_a_6679_, lean_object* v_a_6680_, lean_object* v_a_6681_, lean_object* v_a_6682_){
_start:
{
lean_object* v_res_6683_; 
v_res_6683_ = l_Lean_Meta_mkSub(v_a_6676_, v_b_6677_, v_a_6678_, v_a_6679_, v_a_6680_, v_a_6681_);
lean_dec(v_a_6681_);
lean_dec_ref(v_a_6680_);
lean_dec(v_a_6679_);
lean_dec_ref(v_a_6678_);
return v_res_6683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6691_, lean_object* v_b_6692_, lean_object* v_a_6693_, lean_object* v_a_6694_, lean_object* v_a_6695_, lean_object* v_a_6696_){
_start:
{
lean_object* v___x_6698_; lean_object* v___x_6699_; lean_object* v___x_6700_; 
v___x_6698_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6699_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6700_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6698_, v___x_6699_, v_a_6691_, v_b_6692_, v_a_6693_, v_a_6694_, v_a_6695_, v_a_6696_);
return v___x_6700_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6701_, lean_object* v_b_6702_, lean_object* v_a_6703_, lean_object* v_a_6704_, lean_object* v_a_6705_, lean_object* v_a_6706_, lean_object* v_a_6707_){
_start:
{
lean_object* v_res_6708_; 
v_res_6708_ = l_Lean_Meta_mkMul(v_a_6701_, v_b_6702_, v_a_6703_, v_a_6704_, v_a_6705_, v_a_6706_);
lean_dec(v_a_6706_);
lean_dec_ref(v_a_6705_);
lean_dec(v_a_6704_);
lean_dec_ref(v_a_6703_);
return v_res_6708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6709_, lean_object* v_rName_6710_, lean_object* v_a_6711_, lean_object* v_b_6712_, lean_object* v_a_6713_, lean_object* v_a_6714_, lean_object* v_a_6715_, lean_object* v_a_6716_){
_start:
{
lean_object* v___x_6718_; 
lean_inc(v_a_6716_);
lean_inc_ref(v_a_6715_);
lean_inc(v_a_6714_);
lean_inc_ref(v_a_6713_);
lean_inc_ref(v_a_6711_);
v___x_6718_ = lean_infer_type(v_a_6711_, v_a_6713_, v_a_6714_, v_a_6715_, v_a_6716_);
if (lean_obj_tag(v___x_6718_) == 0)
{
lean_object* v_a_6719_; lean_object* v___x_6720_; 
v_a_6719_ = lean_ctor_get(v___x_6718_, 0);
lean_inc_n(v_a_6719_, 2);
lean_dec_ref_known(v___x_6718_, 1);
v___x_6720_ = l_Lean_Meta_getDecLevel(v_a_6719_, v_a_6713_, v_a_6714_, v_a_6715_, v_a_6716_);
if (lean_obj_tag(v___x_6720_) == 0)
{
lean_object* v_a_6721_; lean_object* v___x_6722_; lean_object* v___x_6723_; lean_object* v___x_6724_; lean_object* v___x_6725_; lean_object* v___x_6726_; lean_object* v___x_6727_; 
v_a_6721_ = lean_ctor_get(v___x_6720_, 0);
lean_inc(v_a_6721_);
lean_dec_ref_known(v___x_6720_, 1);
v___x_6722_ = lean_box(0);
v___x_6723_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6723_, 0, v_a_6721_);
lean_ctor_set(v___x_6723_, 1, v___x_6722_);
lean_inc_ref(v___x_6723_);
v___x_6724_ = l_Lean_mkConst(v_className_6709_, v___x_6723_);
lean_inc(v_a_6719_);
v___x_6725_ = l_Lean_Expr_app___override(v___x_6724_, v_a_6719_);
v___x_6726_ = lean_box(0);
v___x_6727_ = l_Lean_Meta_synthInstance(v___x_6725_, v___x_6726_, v_a_6713_, v_a_6714_, v_a_6715_, v_a_6716_);
if (lean_obj_tag(v___x_6727_) == 0)
{
lean_object* v_a_6728_; lean_object* v___x_6730_; uint8_t v_isShared_6731_; uint8_t v_isSharedCheck_6737_; 
v_a_6728_ = lean_ctor_get(v___x_6727_, 0);
v_isSharedCheck_6737_ = !lean_is_exclusive(v___x_6727_);
if (v_isSharedCheck_6737_ == 0)
{
v___x_6730_ = v___x_6727_;
v_isShared_6731_ = v_isSharedCheck_6737_;
goto v_resetjp_6729_;
}
else
{
lean_inc(v_a_6728_);
lean_dec(v___x_6727_);
v___x_6730_ = lean_box(0);
v_isShared_6731_ = v_isSharedCheck_6737_;
goto v_resetjp_6729_;
}
v_resetjp_6729_:
{
lean_object* v___x_6732_; lean_object* v___x_6733_; lean_object* v___x_6735_; 
v___x_6732_ = l_Lean_mkConst(v_rName_6710_, v___x_6723_);
v___x_6733_ = l_Lean_mkApp4(v___x_6732_, v_a_6719_, v_a_6728_, v_a_6711_, v_b_6712_);
if (v_isShared_6731_ == 0)
{
lean_ctor_set(v___x_6730_, 0, v___x_6733_);
v___x_6735_ = v___x_6730_;
goto v_reusejp_6734_;
}
else
{
lean_object* v_reuseFailAlloc_6736_; 
v_reuseFailAlloc_6736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6736_, 0, v___x_6733_);
v___x_6735_ = v_reuseFailAlloc_6736_;
goto v_reusejp_6734_;
}
v_reusejp_6734_:
{
return v___x_6735_;
}
}
}
else
{
lean_dec_ref_known(v___x_6723_, 2);
lean_dec(v_a_6719_);
lean_dec_ref(v_b_6712_);
lean_dec_ref(v_a_6711_);
lean_dec(v_rName_6710_);
return v___x_6727_;
}
}
else
{
lean_object* v_a_6738_; lean_object* v___x_6740_; uint8_t v_isShared_6741_; uint8_t v_isSharedCheck_6745_; 
lean_dec(v_a_6719_);
lean_dec_ref(v_b_6712_);
lean_dec_ref(v_a_6711_);
lean_dec(v_rName_6710_);
lean_dec(v_className_6709_);
v_a_6738_ = lean_ctor_get(v___x_6720_, 0);
v_isSharedCheck_6745_ = !lean_is_exclusive(v___x_6720_);
if (v_isSharedCheck_6745_ == 0)
{
v___x_6740_ = v___x_6720_;
v_isShared_6741_ = v_isSharedCheck_6745_;
goto v_resetjp_6739_;
}
else
{
lean_inc(v_a_6738_);
lean_dec(v___x_6720_);
v___x_6740_ = lean_box(0);
v_isShared_6741_ = v_isSharedCheck_6745_;
goto v_resetjp_6739_;
}
v_resetjp_6739_:
{
lean_object* v___x_6743_; 
if (v_isShared_6741_ == 0)
{
v___x_6743_ = v___x_6740_;
goto v_reusejp_6742_;
}
else
{
lean_object* v_reuseFailAlloc_6744_; 
v_reuseFailAlloc_6744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6744_, 0, v_a_6738_);
v___x_6743_ = v_reuseFailAlloc_6744_;
goto v_reusejp_6742_;
}
v_reusejp_6742_:
{
return v___x_6743_;
}
}
}
}
else
{
lean_dec_ref(v_b_6712_);
lean_dec_ref(v_a_6711_);
lean_dec(v_rName_6710_);
lean_dec(v_className_6709_);
return v___x_6718_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6746_, lean_object* v_rName_6747_, lean_object* v_a_6748_, lean_object* v_b_6749_, lean_object* v_a_6750_, lean_object* v_a_6751_, lean_object* v_a_6752_, lean_object* v_a_6753_, lean_object* v_a_6754_){
_start:
{
lean_object* v_res_6755_; 
v_res_6755_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6746_, v_rName_6747_, v_a_6748_, v_b_6749_, v_a_6750_, v_a_6751_, v_a_6752_, v_a_6753_);
lean_dec(v_a_6753_);
lean_dec_ref(v_a_6752_);
lean_dec(v_a_6751_);
lean_dec_ref(v_a_6750_);
return v_res_6755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6758_, lean_object* v_b_6759_, lean_object* v_a_6760_, lean_object* v_a_6761_, lean_object* v_a_6762_, lean_object* v_a_6763_){
_start:
{
lean_object* v___x_6765_; lean_object* v___x_6766_; lean_object* v___x_6767_; 
v___x_6765_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6766_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6767_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6765_, v___x_6766_, v_a_6758_, v_b_6759_, v_a_6760_, v_a_6761_, v_a_6762_, v_a_6763_);
return v___x_6767_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6768_, lean_object* v_b_6769_, lean_object* v_a_6770_, lean_object* v_a_6771_, lean_object* v_a_6772_, lean_object* v_a_6773_, lean_object* v_a_6774_){
_start:
{
lean_object* v_res_6775_; 
v_res_6775_ = l_Lean_Meta_mkLE(v_a_6768_, v_b_6769_, v_a_6770_, v_a_6771_, v_a_6772_, v_a_6773_);
lean_dec(v_a_6773_);
lean_dec_ref(v_a_6772_);
lean_dec(v_a_6771_);
lean_dec_ref(v_a_6770_);
return v_res_6775_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6778_, lean_object* v_b_6779_, lean_object* v_a_6780_, lean_object* v_a_6781_, lean_object* v_a_6782_, lean_object* v_a_6783_){
_start:
{
lean_object* v___x_6785_; lean_object* v___x_6786_; lean_object* v___x_6787_; 
v___x_6785_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6786_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6787_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6785_, v___x_6786_, v_a_6778_, v_b_6779_, v_a_6780_, v_a_6781_, v_a_6782_, v_a_6783_);
return v___x_6787_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6788_, lean_object* v_b_6789_, lean_object* v_a_6790_, lean_object* v_a_6791_, lean_object* v_a_6792_, lean_object* v_a_6793_, lean_object* v_a_6794_){
_start:
{
lean_object* v_res_6795_; 
v_res_6795_ = l_Lean_Meta_mkLT(v_a_6788_, v_b_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
lean_dec(v_a_6793_);
lean_dec_ref(v_a_6792_);
lean_dec(v_a_6791_);
lean_dec_ref(v_a_6790_);
return v_res_6795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6801_, lean_object* v_a_6802_, lean_object* v_a_6803_, lean_object* v_a_6804_, lean_object* v_a_6805_){
_start:
{
lean_object* v___x_6807_; lean_object* v___x_6808_; uint8_t v___x_6809_; 
v___x_6807_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6808_ = lean_unsigned_to_nat(3u);
v___x_6809_ = l_Lean_Expr_isAppOfArity(v_h_6801_, v___x_6807_, v___x_6808_);
if (v___x_6809_ == 0)
{
lean_object* v___x_6810_; lean_object* v___x_6811_; lean_object* v___x_6812_; lean_object* v___x_6813_; lean_object* v___x_6814_; 
v___x_6810_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6811_ = lean_unsigned_to_nat(1u);
v___x_6812_ = lean_mk_empty_array_with_capacity(v___x_6811_);
v___x_6813_ = lean_array_push(v___x_6812_, v_h_6801_);
v___x_6814_ = l_Lean_Meta_mkAppM(v___x_6810_, v___x_6813_, v_a_6802_, v_a_6803_, v_a_6804_, v_a_6805_);
return v___x_6814_;
}
else
{
lean_object* v___x_6815_; lean_object* v___x_6816_; 
v___x_6815_ = l_Lean_Expr_appArg_x21(v_h_6801_);
lean_dec_ref(v_h_6801_);
v___x_6816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6816_, 0, v___x_6815_);
return v___x_6816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6817_, lean_object* v_a_6818_, lean_object* v_a_6819_, lean_object* v_a_6820_, lean_object* v_a_6821_, lean_object* v_a_6822_){
_start:
{
lean_object* v_res_6823_; 
v_res_6823_ = l_Lean_Meta_mkIffOfEq(v_h_6817_, v_a_6818_, v_a_6819_, v_a_6820_, v_a_6821_);
lean_dec(v_a_6821_);
lean_dec_ref(v_a_6820_);
lean_dec(v_a_6819_);
lean_dec_ref(v_a_6818_);
return v_res_6823_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6829_; lean_object* v___x_6830_; lean_object* v___x_6831_; 
v___x_6829_ = lean_box(0);
v___x_6830_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6831_ = l_Lean_mkConst(v___x_6830_, v___x_6829_);
return v___x_6831_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6834_; lean_object* v___x_6835_; lean_object* v___x_6836_; 
v___x_6834_ = lean_box(0);
v___x_6835_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6836_ = l_Lean_mkConst(v___x_6835_, v___x_6834_);
return v___x_6836_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6837_; lean_object* v___x_6838_; lean_object* v___x_6839_; 
v___x_6837_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6838_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6839_, 0, v___x_6838_);
lean_ctor_set(v___x_6839_, 1, v___x_6837_);
return v___x_6839_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6844_; lean_object* v___x_6845_; lean_object* v___x_6846_; 
v___x_6844_ = lean_box(0);
v___x_6845_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6846_ = l_Lean_mkConst(v___x_6845_, v___x_6844_);
return v___x_6846_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6849_; lean_object* v___x_6850_; lean_object* v___x_6851_; 
v___x_6849_ = lean_box(0);
v___x_6850_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6851_ = l_Lean_mkConst(v___x_6850_, v___x_6849_);
return v___x_6851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6852_, lean_object* v_a_6853_, lean_object* v_a_6854_, lean_object* v_a_6855_, lean_object* v_a_6856_){
_start:
{
if (lean_obj_tag(v_a_6852_) == 0)
{
lean_object* v___x_6858_; lean_object* v___x_6859_; 
v___x_6858_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6859_, 0, v___x_6858_);
return v___x_6859_;
}
else
{
lean_object* v_tail_6860_; 
v_tail_6860_ = lean_ctor_get(v_a_6852_, 1);
if (lean_obj_tag(v_tail_6860_) == 0)
{
lean_object* v_head_6861_; lean_object* v___x_6863_; uint8_t v_isShared_6864_; uint8_t v_isSharedCheck_6885_; 
v_head_6861_ = lean_ctor_get(v_a_6852_, 0);
v_isSharedCheck_6885_ = !lean_is_exclusive(v_a_6852_);
if (v_isSharedCheck_6885_ == 0)
{
lean_object* v_unused_6886_; 
v_unused_6886_ = lean_ctor_get(v_a_6852_, 1);
lean_dec(v_unused_6886_);
v___x_6863_ = v_a_6852_;
v_isShared_6864_ = v_isSharedCheck_6885_;
goto v_resetjp_6862_;
}
else
{
lean_inc(v_head_6861_);
lean_dec(v_a_6852_);
v___x_6863_ = lean_box(0);
v_isShared_6864_ = v_isSharedCheck_6885_;
goto v_resetjp_6862_;
}
v_resetjp_6862_:
{
lean_object* v___x_6865_; 
lean_inc(v_a_6856_);
lean_inc_ref(v_a_6855_);
lean_inc(v_a_6854_);
lean_inc_ref(v_a_6853_);
lean_inc(v_head_6861_);
v___x_6865_ = lean_infer_type(v_head_6861_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
if (lean_obj_tag(v___x_6865_) == 0)
{
lean_object* v_a_6866_; lean_object* v___x_6868_; uint8_t v_isShared_6869_; uint8_t v_isSharedCheck_6876_; 
v_a_6866_ = lean_ctor_get(v___x_6865_, 0);
v_isSharedCheck_6876_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6876_ == 0)
{
v___x_6868_ = v___x_6865_;
v_isShared_6869_ = v_isSharedCheck_6876_;
goto v_resetjp_6867_;
}
else
{
lean_inc(v_a_6866_);
lean_dec(v___x_6865_);
v___x_6868_ = lean_box(0);
v_isShared_6869_ = v_isSharedCheck_6876_;
goto v_resetjp_6867_;
}
v_resetjp_6867_:
{
lean_object* v___x_6871_; 
if (v_isShared_6864_ == 0)
{
lean_ctor_set_tag(v___x_6863_, 0);
lean_ctor_set(v___x_6863_, 1, v_a_6866_);
v___x_6871_ = v___x_6863_;
goto v_reusejp_6870_;
}
else
{
lean_object* v_reuseFailAlloc_6875_; 
v_reuseFailAlloc_6875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6875_, 0, v_head_6861_);
lean_ctor_set(v_reuseFailAlloc_6875_, 1, v_a_6866_);
v___x_6871_ = v_reuseFailAlloc_6875_;
goto v_reusejp_6870_;
}
v_reusejp_6870_:
{
lean_object* v___x_6873_; 
if (v_isShared_6869_ == 0)
{
lean_ctor_set(v___x_6868_, 0, v___x_6871_);
v___x_6873_ = v___x_6868_;
goto v_reusejp_6872_;
}
else
{
lean_object* v_reuseFailAlloc_6874_; 
v_reuseFailAlloc_6874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6874_, 0, v___x_6871_);
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
else
{
lean_object* v_a_6877_; lean_object* v___x_6879_; uint8_t v_isShared_6880_; uint8_t v_isSharedCheck_6884_; 
lean_del_object(v___x_6863_);
lean_dec(v_head_6861_);
v_a_6877_ = lean_ctor_get(v___x_6865_, 0);
v_isSharedCheck_6884_ = !lean_is_exclusive(v___x_6865_);
if (v_isSharedCheck_6884_ == 0)
{
v___x_6879_ = v___x_6865_;
v_isShared_6880_ = v_isSharedCheck_6884_;
goto v_resetjp_6878_;
}
else
{
lean_inc(v_a_6877_);
lean_dec(v___x_6865_);
v___x_6879_ = lean_box(0);
v_isShared_6880_ = v_isSharedCheck_6884_;
goto v_resetjp_6878_;
}
v_resetjp_6878_:
{
lean_object* v___x_6882_; 
if (v_isShared_6880_ == 0)
{
v___x_6882_ = v___x_6879_;
goto v_reusejp_6881_;
}
else
{
lean_object* v_reuseFailAlloc_6883_; 
v_reuseFailAlloc_6883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6883_, 0, v_a_6877_);
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
}
else
{
lean_object* v_head_6887_; lean_object* v___x_6888_; 
lean_inc(v_tail_6860_);
v_head_6887_ = lean_ctor_get(v_a_6852_, 0);
lean_inc(v_head_6887_);
lean_dec_ref_known(v_a_6852_, 2);
v___x_6888_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6860_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
if (lean_obj_tag(v___x_6888_) == 0)
{
lean_object* v_a_6889_; lean_object* v_fst_6890_; lean_object* v_snd_6891_; lean_object* v___x_6893_; uint8_t v_isShared_6894_; uint8_t v_isSharedCheck_6919_; 
v_a_6889_ = lean_ctor_get(v___x_6888_, 0);
lean_inc(v_a_6889_);
lean_dec_ref_known(v___x_6888_, 1);
v_fst_6890_ = lean_ctor_get(v_a_6889_, 0);
v_snd_6891_ = lean_ctor_get(v_a_6889_, 1);
v_isSharedCheck_6919_ = !lean_is_exclusive(v_a_6889_);
if (v_isSharedCheck_6919_ == 0)
{
v___x_6893_ = v_a_6889_;
v_isShared_6894_ = v_isSharedCheck_6919_;
goto v_resetjp_6892_;
}
else
{
lean_inc(v_snd_6891_);
lean_inc(v_fst_6890_);
lean_dec(v_a_6889_);
v___x_6893_ = lean_box(0);
v_isShared_6894_ = v_isSharedCheck_6919_;
goto v_resetjp_6892_;
}
v_resetjp_6892_:
{
lean_object* v___x_6895_; 
lean_inc(v_a_6856_);
lean_inc_ref(v_a_6855_);
lean_inc(v_a_6854_);
lean_inc_ref(v_a_6853_);
lean_inc(v_head_6887_);
v___x_6895_ = lean_infer_type(v_head_6887_, v_a_6853_, v_a_6854_, v_a_6855_, v_a_6856_);
if (lean_obj_tag(v___x_6895_) == 0)
{
lean_object* v_a_6896_; lean_object* v___x_6898_; uint8_t v_isShared_6899_; uint8_t v_isSharedCheck_6910_; 
v_a_6896_ = lean_ctor_get(v___x_6895_, 0);
v_isSharedCheck_6910_ = !lean_is_exclusive(v___x_6895_);
if (v_isSharedCheck_6910_ == 0)
{
v___x_6898_ = v___x_6895_;
v_isShared_6899_ = v_isSharedCheck_6910_;
goto v_resetjp_6897_;
}
else
{
lean_inc(v_a_6896_);
lean_dec(v___x_6895_);
v___x_6898_ = lean_box(0);
v_isShared_6899_ = v_isSharedCheck_6910_;
goto v_resetjp_6897_;
}
v_resetjp_6897_:
{
lean_object* v___x_6900_; lean_object* v___x_6901_; lean_object* v___x_6902_; lean_object* v___x_6903_; lean_object* v___x_6905_; 
v___x_6900_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6891_);
lean_inc(v_a_6896_);
v___x_6901_ = l_Lean_mkApp4(v___x_6900_, v_a_6896_, v_snd_6891_, v_head_6887_, v_fst_6890_);
v___x_6902_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6903_ = l_Lean_mkAppB(v___x_6902_, v_a_6896_, v_snd_6891_);
if (v_isShared_6894_ == 0)
{
lean_ctor_set(v___x_6893_, 1, v___x_6903_);
lean_ctor_set(v___x_6893_, 0, v___x_6901_);
v___x_6905_ = v___x_6893_;
goto v_reusejp_6904_;
}
else
{
lean_object* v_reuseFailAlloc_6909_; 
v_reuseFailAlloc_6909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6909_, 0, v___x_6901_);
lean_ctor_set(v_reuseFailAlloc_6909_, 1, v___x_6903_);
v___x_6905_ = v_reuseFailAlloc_6909_;
goto v_reusejp_6904_;
}
v_reusejp_6904_:
{
lean_object* v___x_6907_; 
if (v_isShared_6899_ == 0)
{
lean_ctor_set(v___x_6898_, 0, v___x_6905_);
v___x_6907_ = v___x_6898_;
goto v_reusejp_6906_;
}
else
{
lean_object* v_reuseFailAlloc_6908_; 
v_reuseFailAlloc_6908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6908_, 0, v___x_6905_);
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
else
{
lean_object* v_a_6911_; lean_object* v___x_6913_; uint8_t v_isShared_6914_; uint8_t v_isSharedCheck_6918_; 
lean_del_object(v___x_6893_);
lean_dec(v_snd_6891_);
lean_dec(v_fst_6890_);
lean_dec(v_head_6887_);
v_a_6911_ = lean_ctor_get(v___x_6895_, 0);
v_isSharedCheck_6918_ = !lean_is_exclusive(v___x_6895_);
if (v_isSharedCheck_6918_ == 0)
{
v___x_6913_ = v___x_6895_;
v_isShared_6914_ = v_isSharedCheck_6918_;
goto v_resetjp_6912_;
}
else
{
lean_inc(v_a_6911_);
lean_dec(v___x_6895_);
v___x_6913_ = lean_box(0);
v_isShared_6914_ = v_isSharedCheck_6918_;
goto v_resetjp_6912_;
}
v_resetjp_6912_:
{
lean_object* v___x_6916_; 
if (v_isShared_6914_ == 0)
{
v___x_6916_ = v___x_6913_;
goto v_reusejp_6915_;
}
else
{
lean_object* v_reuseFailAlloc_6917_; 
v_reuseFailAlloc_6917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6917_, 0, v_a_6911_);
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
}
else
{
lean_dec(v_head_6887_);
return v___x_6888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6920_, lean_object* v_a_6921_, lean_object* v_a_6922_, lean_object* v_a_6923_, lean_object* v_a_6924_, lean_object* v_a_6925_){
_start:
{
lean_object* v_res_6926_; 
v_res_6926_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6920_, v_a_6921_, v_a_6922_, v_a_6923_, v_a_6924_);
lean_dec(v_a_6924_);
lean_dec_ref(v_a_6923_);
lean_dec(v_a_6922_);
lean_dec_ref(v_a_6921_);
return v_res_6926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6927_, lean_object* v_a_6928_, lean_object* v_a_6929_, lean_object* v_a_6930_, lean_object* v_a_6931_){
_start:
{
lean_object* v___x_6933_; 
v___x_6933_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6927_, v_a_6928_, v_a_6929_, v_a_6930_, v_a_6931_);
if (lean_obj_tag(v___x_6933_) == 0)
{
lean_object* v_a_6934_; lean_object* v___x_6936_; uint8_t v_isShared_6937_; uint8_t v_isSharedCheck_6942_; 
v_a_6934_ = lean_ctor_get(v___x_6933_, 0);
v_isSharedCheck_6942_ = !lean_is_exclusive(v___x_6933_);
if (v_isSharedCheck_6942_ == 0)
{
v___x_6936_ = v___x_6933_;
v_isShared_6937_ = v_isSharedCheck_6942_;
goto v_resetjp_6935_;
}
else
{
lean_inc(v_a_6934_);
lean_dec(v___x_6933_);
v___x_6936_ = lean_box(0);
v_isShared_6937_ = v_isSharedCheck_6942_;
goto v_resetjp_6935_;
}
v_resetjp_6935_:
{
lean_object* v_fst_6938_; lean_object* v___x_6940_; 
v_fst_6938_ = lean_ctor_get(v_a_6934_, 0);
lean_inc(v_fst_6938_);
lean_dec(v_a_6934_);
if (v_isShared_6937_ == 0)
{
lean_ctor_set(v___x_6936_, 0, v_fst_6938_);
v___x_6940_ = v___x_6936_;
goto v_reusejp_6939_;
}
else
{
lean_object* v_reuseFailAlloc_6941_; 
v_reuseFailAlloc_6941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6941_, 0, v_fst_6938_);
v___x_6940_ = v_reuseFailAlloc_6941_;
goto v_reusejp_6939_;
}
v_reusejp_6939_:
{
return v___x_6940_;
}
}
}
else
{
lean_object* v_a_6943_; lean_object* v___x_6945_; uint8_t v_isShared_6946_; uint8_t v_isSharedCheck_6950_; 
v_a_6943_ = lean_ctor_get(v___x_6933_, 0);
v_isSharedCheck_6950_ = !lean_is_exclusive(v___x_6933_);
if (v_isSharedCheck_6950_ == 0)
{
v___x_6945_ = v___x_6933_;
v_isShared_6946_ = v_isSharedCheck_6950_;
goto v_resetjp_6944_;
}
else
{
lean_inc(v_a_6943_);
lean_dec(v___x_6933_);
v___x_6945_ = lean_box(0);
v_isShared_6946_ = v_isSharedCheck_6950_;
goto v_resetjp_6944_;
}
v_resetjp_6944_:
{
lean_object* v___x_6948_; 
if (v_isShared_6946_ == 0)
{
v___x_6948_ = v___x_6945_;
goto v_reusejp_6947_;
}
else
{
lean_object* v_reuseFailAlloc_6949_; 
v_reuseFailAlloc_6949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6949_, 0, v_a_6943_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_6951_, lean_object* v_a_6952_, lean_object* v_a_6953_, lean_object* v_a_6954_, lean_object* v_a_6955_, lean_object* v_a_6956_){
_start:
{
lean_object* v_res_6957_; 
v_res_6957_ = l_Lean_Meta_mkAndIntroN(v_hs_6951_, v_a_6952_, v_a_6953_, v_a_6954_, v_a_6955_);
lean_dec(v_a_6955_);
lean_dec_ref(v_a_6954_);
lean_dec(v_a_6953_);
lean_dec_ref(v_a_6952_);
return v_res_6957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7014_; uint8_t v___x_7015_; lean_object* v___x_7016_; lean_object* v___x_7017_; 
v___x_7014_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7015_ = 0;
v___x_7016_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7017_ = l_Lean_registerTraceClass(v___x_7014_, v___x_7015_, v___x_7016_);
if (lean_obj_tag(v___x_7017_) == 0)
{
lean_object* v___x_7018_; uint8_t v___x_7019_; lean_object* v___x_7020_; 
lean_dec_ref_known(v___x_7017_, 1);
v___x_7018_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7019_ = 1;
v___x_7020_ = l_Lean_registerTraceClass(v___x_7018_, v___x_7019_, v___x_7016_);
if (lean_obj_tag(v___x_7020_) == 0)
{
lean_object* v___x_7021_; lean_object* v___x_7022_; 
lean_dec_ref_known(v___x_7020_, 1);
v___x_7021_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7022_ = l_Lean_registerTraceClass(v___x_7021_, v___x_7019_, v___x_7016_);
return v___x_7022_;
}
else
{
return v___x_7020_;
}
}
else
{
return v___x_7017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7023_){
_start:
{
lean_object* v_res_7024_; 
v_res_7024_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7024_;
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
