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
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTransCore(lean_object* v_u_600_, lean_object* v_00_u03b1_601_, lean_object* v_a_602_, lean_object* v_b_603_, lean_object* v_c_604_, lean_object* v_h_u2081_605_, lean_object* v_h_u2082_606_){
_start:
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; 
v___x_607_ = ((lean_object*)(l_Lean_Meta_mkEqTransCore___closed__1));
v___x_608_ = lean_box(0);
v___x_609_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_609_, 0, v_u_600_);
lean_ctor_set(v___x_609_, 1, v___x_608_);
v___x_610_ = l_Lean_mkConst(v___x_607_, v___x_609_);
v___x_611_ = l_Lean_mkApp6(v___x_610_, v_00_u03b1_601_, v_a_602_, v_b_603_, v_c_604_, v_h_u2081_605_, v_h_u2082_606_);
return v___x_611_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTransCoreProp___closed__0(void){
_start:
{
lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_612_ = lean_unsigned_to_nat(1u);
v___x_613_ = l_Lean_Level_ofNat(v___x_612_);
return v___x_613_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTransCoreProp___closed__1(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = lean_unsigned_to_nat(0u);
v___x_615_ = l_Lean_Level_ofNat(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTransCoreProp___closed__2(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Lean_Meta_mkEqTransCoreProp___closed__1, &l_Lean_Meta_mkEqTransCoreProp___closed__1_once, _init_l_Lean_Meta_mkEqTransCoreProp___closed__1);
v___x_617_ = l_Lean_mkSort(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTransCoreProp(lean_object* v_a_618_, lean_object* v_b_619_, lean_object* v_c_620_, lean_object* v_h_u2081_621_, lean_object* v_h_u2082_622_){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_623_ = lean_obj_once(&l_Lean_Meta_mkEqTransCoreProp___closed__0, &l_Lean_Meta_mkEqTransCoreProp___closed__0_once, _init_l_Lean_Meta_mkEqTransCoreProp___closed__0);
v___x_624_ = lean_obj_once(&l_Lean_Meta_mkEqTransCoreProp___closed__2, &l_Lean_Meta_mkEqTransCoreProp___closed__2_once, _init_l_Lean_Meta_mkEqTransCoreProp___closed__2);
v___x_625_ = l_Lean_Meta_mkEqTransCore(v___x_623_, v___x_624_, v_a_618_, v_b_619_, v_c_620_, v_h_u2081_621_, v_h_u2082_622_);
return v___x_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans(lean_object* v_h_u2081_626_, lean_object* v_h_u2082_627_, lean_object* v_a_628_, lean_object* v_a_629_, lean_object* v_a_630_, lean_object* v_a_631_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_634_ = l_Lean_Expr_isAppOf(v_h_u2081_626_, v___x_633_);
if (v___x_634_ == 0)
{
uint8_t v___x_635_; 
v___x_635_ = l_Lean_Expr_isAppOf(v_h_u2082_627_, v___x_633_);
if (v___x_635_ == 0)
{
lean_object* v___x_636_; 
lean_inc_ref(v_h_u2081_626_);
v___x_636_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_626_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_636_) == 0)
{
lean_object* v_a_637_; lean_object* v___x_638_; 
v_a_637_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_a_637_);
lean_dec_ref_known(v___x_636_, 1);
lean_inc_ref(v_h_u2082_627_);
v___x_638_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_638_) == 0)
{
lean_object* v_a_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_a_639_ = lean_ctor_get(v___x_638_, 0);
lean_inc(v_a_639_);
lean_dec_ref_known(v___x_638_, 1);
v___x_640_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_641_ = lean_unsigned_to_nat(3u);
v___x_642_ = l_Lean_Expr_isAppOfArity(v_a_637_, v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
lean_dec(v_a_639_);
lean_dec_ref(v_h_u2082_627_);
v___x_643_ = ((lean_object*)(l_Lean_Meta_mkEqTransCore___closed__1));
v___x_644_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_645_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_626_, v_a_637_);
v___x_646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_646_, 0, v___x_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
v___x_647_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_643_, v___x_646_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
return v___x_647_;
}
else
{
uint8_t v___x_648_; 
v___x_648_ = l_Lean_Expr_isAppOfArity(v_a_639_, v___x_640_, v___x_641_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_a_637_);
lean_dec_ref(v_h_u2081_626_);
v___x_649_ = ((lean_object*)(l_Lean_Meta_mkEqTransCore___closed__1));
v___x_650_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_651_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_627_, v_a_639_);
v___x_652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_650_);
lean_ctor_set(v___x_652_, 1, v___x_651_);
v___x_653_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_649_, v___x_652_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_654_ = l_Lean_Expr_appFn_x21(v_a_637_);
v___x_655_ = l_Lean_Expr_appFn_x21(v___x_654_);
v___x_656_ = l_Lean_Expr_appArg_x21(v___x_655_);
lean_dec_ref(v___x_655_);
v___x_657_ = l_Lean_Expr_appArg_x21(v___x_654_);
lean_dec_ref(v___x_654_);
v___x_658_ = l_Lean_Expr_appArg_x21(v_a_637_);
lean_dec(v_a_637_);
v___x_659_ = l_Lean_Expr_appArg_x21(v_a_639_);
lean_dec(v_a_639_);
lean_inc_ref(v___x_656_);
v___x_660_ = l_Lean_Meta_getLevel(v___x_656_, v_a_628_, v_a_629_, v_a_630_, v_a_631_);
if (lean_obj_tag(v___x_660_) == 0)
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_669_; 
v_a_661_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_669_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_669_ == 0)
{
v___x_663_ = v___x_660_;
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_660_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_669_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_665_; lean_object* v___x_667_; 
v___x_665_ = l_Lean_Meta_mkEqTransCore(v_a_661_, v___x_656_, v___x_657_, v___x_658_, v___x_659_, v_h_u2081_626_, v_h_u2082_627_);
if (v_isShared_664_ == 0)
{
lean_ctor_set(v___x_663_, 0, v___x_665_);
v___x_667_ = v___x_663_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_665_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
}
else
{
lean_object* v_a_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_677_; 
lean_dec_ref(v___x_659_);
lean_dec_ref(v___x_658_);
lean_dec_ref(v___x_657_);
lean_dec_ref(v___x_656_);
lean_dec_ref(v_h_u2082_627_);
lean_dec_ref(v_h_u2081_626_);
v_a_670_ = lean_ctor_get(v___x_660_, 0);
v_isSharedCheck_677_ = !lean_is_exclusive(v___x_660_);
if (v_isSharedCheck_677_ == 0)
{
v___x_672_ = v___x_660_;
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_a_670_);
lean_dec(v___x_660_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_677_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_676_; 
v_reuseFailAlloc_676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
v___x_675_ = v_reuseFailAlloc_676_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
return v___x_675_;
}
}
}
}
}
}
else
{
lean_dec(v_a_637_);
lean_dec_ref(v_h_u2082_627_);
lean_dec_ref(v_h_u2081_626_);
return v___x_638_;
}
}
else
{
lean_dec_ref(v_h_u2082_627_);
lean_dec_ref(v_h_u2081_626_);
return v___x_636_;
}
}
else
{
lean_object* v___x_678_; 
lean_dec_ref(v_h_u2082_627_);
v___x_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_678_, 0, v_h_u2081_626_);
return v___x_678_;
}
}
else
{
lean_object* v___x_679_; 
lean_dec_ref(v_h_u2081_626_);
v___x_679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_679_, 0, v_h_u2082_627_);
return v___x_679_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans___boxed(lean_object* v_h_u2081_680_, lean_object* v_h_u2082_681_, lean_object* v_a_682_, lean_object* v_a_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_Lean_Meta_mkEqTrans(v_h_u2081_680_, v_h_u2082_681_, v_a_682_, v_a_683_, v_a_684_, v_a_685_);
lean_dec(v_a_685_);
lean_dec_ref(v_a_684_);
lean_dec(v_a_683_);
lean_dec_ref(v_a_682_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object* v_h_u2081_x3f_688_, lean_object* v_h_u2082_x3f_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v_h_696_; 
if (lean_obj_tag(v_h_u2081_x3f_688_) == 0)
{
if (lean_obj_tag(v_h_u2082_x3f_689_) == 0)
{
lean_object* v___x_699_; 
v___x_699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_699_, 0, v_h_u2082_x3f_689_);
return v___x_699_;
}
else
{
lean_object* v_val_700_; 
v_val_700_ = lean_ctor_get(v_h_u2082_x3f_689_, 0);
lean_inc(v_val_700_);
lean_dec_ref_known(v_h_u2082_x3f_689_, 1);
v_h_696_ = v_val_700_;
goto v___jp_695_;
}
}
else
{
if (lean_obj_tag(v_h_u2082_x3f_689_) == 0)
{
lean_object* v_val_701_; 
v_val_701_ = lean_ctor_get(v_h_u2081_x3f_688_, 0);
lean_inc(v_val_701_);
lean_dec_ref_known(v_h_u2081_x3f_688_, 1);
v_h_696_ = v_val_701_;
goto v___jp_695_;
}
else
{
lean_object* v_val_702_; lean_object* v_val_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_727_; 
v_val_702_ = lean_ctor_get(v_h_u2081_x3f_688_, 0);
lean_inc(v_val_702_);
lean_dec_ref_known(v_h_u2081_x3f_688_, 1);
v_val_703_ = lean_ctor_get(v_h_u2082_x3f_689_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v_h_u2082_x3f_689_);
if (v_isSharedCheck_727_ == 0)
{
v___x_705_ = v_h_u2082_x3f_689_;
v_isShared_706_ = v_isSharedCheck_727_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_val_703_);
lean_dec(v_h_u2082_x3f_689_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_727_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_707_; 
v___x_707_ = l_Lean_Meta_mkEqTrans(v_val_702_, v_val_703_, v_a_690_, v_a_691_, v_a_692_, v_a_693_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_718_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_718_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_718_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
lean_object* v___x_713_; 
if (v_isShared_706_ == 0)
{
lean_ctor_set(v___x_705_, 0, v_a_708_);
v___x_713_ = v___x_705_;
goto v_reusejp_712_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_708_);
v___x_713_ = v_reuseFailAlloc_717_;
goto v_reusejp_712_;
}
v_reusejp_712_:
{
lean_object* v___x_715_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_713_);
v___x_715_ = v___x_710_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v___x_713_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_719_; lean_object* v___x_721_; uint8_t v_isShared_722_; uint8_t v_isSharedCheck_726_; 
lean_del_object(v___x_705_);
v_a_719_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_726_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_726_ == 0)
{
v___x_721_ = v___x_707_;
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
else
{
lean_inc(v_a_719_);
lean_dec(v___x_707_);
v___x_721_ = lean_box(0);
v_isShared_722_ = v_isSharedCheck_726_;
goto v_resetjp_720_;
}
v_resetjp_720_:
{
lean_object* v___x_724_; 
if (v_isShared_722_ == 0)
{
v___x_724_ = v___x_721_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
return v___x_724_;
}
}
}
}
}
}
v___jp_695_:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_697_, 0, v_h_696_);
v___x_698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
return v___x_698_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrans_x3f___boxed(lean_object* v_h_u2081_x3f_728_, lean_object* v_h_u2082_x3f_729_, lean_object* v_a_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_Lean_Meta_mkEqTrans_x3f(v_h_u2081_x3f_728_, v_h_u2082_x3f_729_, v_a_730_, v_a_731_, v_a_732_, v_a_733_);
lean_dec(v_a_733_);
lean_dec_ref(v_a_732_);
lean_dec(v_a_731_);
lean_dec_ref(v_a_730_);
return v_res_735_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqSymm___closed__3(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__2));
v___x_743_ = l_Lean_MessageData_ofFormat(v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm(lean_object* v_h_744_, lean_object* v_a_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_){
_start:
{
lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_751_ = l_Lean_Expr_isAppOf(v_h_744_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_inc_ref(v_h_744_);
v___x_752_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_744_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_752_) == 0)
{
lean_object* v_a_753_; lean_object* v___x_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v_a_753_ = lean_ctor_get(v___x_752_, 0);
lean_inc(v_a_753_);
lean_dec_ref_known(v___x_752_, 1);
v___x_754_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_755_ = lean_unsigned_to_nat(4u);
v___x_756_ = l_Lean_Expr_isAppOfArity(v_a_753_, v___x_754_, v___x_755_);
if (v___x_756_ == 0)
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_757_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_758_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_759_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_744_, v_a_753_);
v___x_760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_758_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_757_, v___x_760_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
return v___x_761_;
}
else
{
lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_762_ = l_Lean_Expr_appFn_x21(v_a_753_);
v___x_763_ = l_Lean_Expr_appFn_x21(v___x_762_);
v___x_764_ = l_Lean_Expr_appFn_x21(v___x_763_);
v___x_765_ = l_Lean_Expr_appArg_x21(v___x_764_);
lean_dec_ref(v___x_764_);
v___x_766_ = l_Lean_Expr_appArg_x21(v___x_763_);
lean_dec_ref(v___x_763_);
v___x_767_ = l_Lean_Expr_appArg_x21(v___x_762_);
lean_dec_ref(v___x_762_);
v___x_768_ = l_Lean_Expr_appArg_x21(v_a_753_);
lean_dec(v_a_753_);
lean_inc_ref(v___x_765_);
v___x_769_ = l_Lean_Meta_getLevel(v___x_765_, v_a_745_, v_a_746_, v_a_747_, v_a_748_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_782_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_782_ == 0)
{
v___x_772_ = v___x_769_;
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_a_770_);
lean_dec(v___x_769_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_782_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_780_; 
v___x_774_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__0));
v___x_775_ = lean_box(0);
v___x_776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_776_, 0, v_a_770_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = l_Lean_mkConst(v___x_774_, v___x_776_);
v___x_778_ = l_Lean_mkApp5(v___x_777_, v___x_765_, v___x_767_, v___x_766_, v___x_768_, v_h_744_);
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 0, v___x_778_);
v___x_780_ = v___x_772_;
goto v_reusejp_779_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_778_);
v___x_780_ = v_reuseFailAlloc_781_;
goto v_reusejp_779_;
}
v_reusejp_779_:
{
return v___x_780_;
}
}
}
else
{
lean_object* v_a_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_790_; 
lean_dec_ref(v___x_768_);
lean_dec_ref(v___x_767_);
lean_dec_ref(v___x_766_);
lean_dec_ref(v___x_765_);
lean_dec_ref(v_h_744_);
v_a_783_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_790_ == 0)
{
v___x_785_ = v___x_769_;
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_a_783_);
lean_dec(v___x_769_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_790_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_788_; 
if (v_isShared_786_ == 0)
{
v___x_788_ = v___x_785_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_744_);
return v___x_752_;
}
}
else
{
lean_object* v___x_791_; 
v___x_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_791_, 0, v_h_744_);
return v___x_791_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqSymm___boxed(lean_object* v_h_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_Lean_Meta_mkHEqSymm(v_h_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_);
lean_dec(v_a_796_);
lean_dec_ref(v_a_795_);
lean_dec(v_a_794_);
lean_dec_ref(v_a_793_);
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans(lean_object* v_h_u2081_802_, lean_object* v_h_u2082_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_809_; uint8_t v___x_810_; 
v___x_809_ = ((lean_object*)(l_Lean_Meta_mkHEqRefl___closed__0));
v___x_810_ = l_Lean_Expr_isAppOf(v_h_u2081_802_, v___x_809_);
if (v___x_810_ == 0)
{
uint8_t v___x_811_; 
v___x_811_ = l_Lean_Expr_isAppOf(v_h_u2082_803_, v___x_809_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_inc_ref(v_h_u2081_802_);
v___x_812_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_802_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v_a_813_; lean_object* v___x_814_; 
v_a_813_ = lean_ctor_get(v___x_812_, 0);
lean_inc(v_a_813_);
lean_dec_ref_known(v___x_812_, 1);
lean_inc_ref(v_h_u2082_803_);
v___x_814_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_object* v_a_815_; lean_object* v___x_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v_a_815_ = lean_ctor_get(v___x_814_, 0);
lean_inc(v_a_815_);
lean_dec_ref_known(v___x_814_, 1);
v___x_816_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_817_ = lean_unsigned_to_nat(4u);
v___x_818_ = l_Lean_Expr_isAppOfArity(v_a_813_, v___x_816_, v___x_817_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; 
lean_dec(v_a_815_);
lean_dec_ref(v_h_u2082_803_);
v___x_819_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_820_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_821_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_802_, v_a_813_);
v___x_822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_820_);
lean_ctor_set(v___x_822_, 1, v___x_821_);
v___x_823_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_819_, v___x_822_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
return v___x_823_;
}
else
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Expr_isAppOfArity(v_a_815_, v___x_816_, v___x_817_);
if (v___x_824_ == 0)
{
lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
lean_dec(v_a_813_);
lean_dec_ref(v_h_u2081_802_);
v___x_825_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_826_ = lean_obj_once(&l_Lean_Meta_mkHEqSymm___closed__3, &l_Lean_Meta_mkHEqSymm___closed__3_once, _init_l_Lean_Meta_mkHEqSymm___closed__3);
v___x_827_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_803_, v_a_815_);
v___x_828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_826_);
lean_ctor_set(v___x_828_, 1, v___x_827_);
v___x_829_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_825_, v___x_828_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; 
v___x_830_ = l_Lean_Expr_appFn_x21(v_a_813_);
v___x_831_ = l_Lean_Expr_appFn_x21(v___x_830_);
v___x_832_ = l_Lean_Expr_appFn_x21(v___x_831_);
v___x_833_ = l_Lean_Expr_appArg_x21(v___x_832_);
lean_dec_ref(v___x_832_);
v___x_834_ = l_Lean_Expr_appArg_x21(v___x_831_);
lean_dec_ref(v___x_831_);
v___x_835_ = l_Lean_Expr_appArg_x21(v___x_830_);
lean_dec_ref(v___x_830_);
v___x_836_ = l_Lean_Expr_appArg_x21(v_a_813_);
lean_dec(v_a_813_);
v___x_837_ = l_Lean_Expr_appFn_x21(v_a_815_);
v___x_838_ = l_Lean_Expr_appArg_x21(v___x_837_);
lean_dec_ref(v___x_837_);
v___x_839_ = l_Lean_Expr_appArg_x21(v_a_815_);
lean_dec(v_a_815_);
lean_inc_ref(v___x_833_);
v___x_840_ = l_Lean_Meta_getLevel(v___x_833_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v_a_841_; lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_853_; 
v_a_841_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_853_ == 0)
{
v___x_843_ = v___x_840_;
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
else
{
lean_inc(v_a_841_);
lean_dec(v___x_840_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_853_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_845_ = ((lean_object*)(l_Lean_Meta_mkHEqTrans___closed__0));
v___x_846_ = lean_box(0);
v___x_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_847_, 0, v_a_841_);
lean_ctor_set(v___x_847_, 1, v___x_846_);
v___x_848_ = l_Lean_mkConst(v___x_845_, v___x_847_);
v___x_849_ = l_Lean_mkApp8(v___x_848_, v___x_833_, v___x_835_, v___x_838_, v___x_834_, v___x_836_, v___x_839_, v_h_u2081_802_, v_h_u2082_803_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_849_);
v___x_851_ = v___x_843_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec_ref(v___x_839_);
lean_dec_ref(v___x_838_);
lean_dec_ref(v___x_836_);
lean_dec_ref(v___x_835_);
lean_dec_ref(v___x_834_);
lean_dec_ref(v___x_833_);
lean_dec_ref(v_h_u2082_803_);
lean_dec_ref(v_h_u2081_802_);
v_a_854_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_840_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_840_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
else
{
lean_dec(v_a_813_);
lean_dec_ref(v_h_u2082_803_);
lean_dec_ref(v_h_u2081_802_);
return v___x_814_;
}
}
else
{
lean_dec_ref(v_h_u2082_803_);
lean_dec_ref(v_h_u2081_802_);
return v___x_812_;
}
}
else
{
lean_object* v___x_862_; 
lean_dec_ref(v_h_u2082_803_);
v___x_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_862_, 0, v_h_u2081_802_);
return v___x_862_;
}
}
else
{
lean_object* v___x_863_; 
lean_dec_ref(v_h_u2081_802_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v_h_u2082_803_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqTrans___boxed(lean_object* v_h_u2081_864_, lean_object* v_h_u2082_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v_res_871_; 
v_res_871_ = l_Lean_Meta_mkHEqTrans(v_h_u2081_864_, v_h_u2082_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_);
lean_dec(v_a_869_);
lean_dec_ref(v_a_868_);
lean_dec(v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_871_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__2(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Meta_mkHEqSymm___closed__1));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__4(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__3));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqOfHEq___closed__6(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__5));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq(lean_object* v_h_883_, uint8_t v_check_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_890_; 
lean_inc_ref(v_h_883_);
v___x_890_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_883_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; uint8_t v___x_894_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref_known(v___x_890_, 1);
v___x_892_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_893_ = lean_unsigned_to_nat(4u);
v___x_894_ = l_Lean_Expr_isAppOfArity(v_a_891_, v___x_892_, v___x_893_);
if (v___x_894_ == 0)
{
lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
lean_dec(v_a_891_);
v___x_895_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_896_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__2, &l_Lean_Meta_mkEqOfHEq___closed__2_once, _init_l_Lean_Meta_mkEqOfHEq___closed__2);
v___x_897_ = l_Lean_indentExpr(v_h_883_);
v___x_898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_898_, 0, v___x_896_);
lean_ctor_set(v___x_898_, 1, v___x_897_);
v___x_899_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_895_, v___x_898_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v___x_899_;
}
else
{
lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___y_907_; lean_object* v___y_908_; lean_object* v___y_909_; lean_object* v___y_910_; 
v___x_900_ = l_Lean_Expr_appFn_x21(v_a_891_);
v___x_901_ = l_Lean_Expr_appFn_x21(v___x_900_);
v___x_902_ = l_Lean_Expr_appFn_x21(v___x_901_);
v___x_903_ = l_Lean_Expr_appArg_x21(v___x_902_);
lean_dec_ref(v___x_902_);
v___x_904_ = l_Lean_Expr_appArg_x21(v___x_901_);
lean_dec_ref(v___x_901_);
v___x_905_ = l_Lean_Expr_appArg_x21(v_a_891_);
lean_dec(v_a_891_);
if (v_check_884_ == 0)
{
lean_dec_ref(v___x_900_);
v___y_907_ = v_a_885_;
v___y_908_ = v_a_886_;
v___y_909_ = v_a_887_;
v___y_910_ = v_a_888_;
goto v___jp_906_;
}
else
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = l_Lean_Expr_appArg_x21(v___x_900_);
lean_dec_ref(v___x_900_);
lean_inc_ref(v___x_933_);
lean_inc_ref(v___x_903_);
v___x_934_ = l_Lean_Meta_isExprDefEq(v___x_903_, v___x_933_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_934_) == 0)
{
lean_object* v_a_935_; uint8_t v___x_936_; 
v_a_935_ = lean_ctor_get(v___x_934_, 0);
lean_inc(v_a_935_);
lean_dec_ref_known(v___x_934_, 1);
v___x_936_ = lean_unbox(v_a_935_);
lean_dec(v_a_935_);
if (v___x_936_ == 0)
{
lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v_h_883_);
v___x_937_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_938_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__4, &l_Lean_Meta_mkEqOfHEq___closed__4_once, _init_l_Lean_Meta_mkEqOfHEq___closed__4);
v___x_939_ = l_Lean_indentExpr(v___x_903_);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_obj_once(&l_Lean_Meta_mkEqOfHEq___closed__6, &l_Lean_Meta_mkEqOfHEq___closed__6_once, _init_l_Lean_Meta_mkEqOfHEq___closed__6);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_indentExpr(v___x_933_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v___x_942_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
v___x_945_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_937_, v___x_944_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
else
{
lean_dec_ref(v___x_933_);
v___y_907_ = v_a_885_;
v___y_908_ = v_a_886_;
v___y_909_ = v_a_887_;
v___y_910_ = v_a_888_;
goto v___jp_906_;
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___x_933_);
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v_h_883_);
v_a_954_ = lean_ctor_get(v___x_934_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_934_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_934_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_934_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
v___jp_906_:
{
lean_object* v___x_911_; 
lean_inc_ref(v___x_903_);
v___x_911_ = l_Lean_Meta_getLevel(v___x_903_, v___y_907_, v___y_908_, v___y_909_, v___y_910_);
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_924_; 
v_a_912_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_924_ == 0)
{
v___x_914_ = v___x_911_;
v_isShared_915_ = v_isSharedCheck_924_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_911_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_924_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_922_; 
v___x_916_ = ((lean_object*)(l_Lean_Meta_mkEqOfHEq___closed__1));
v___x_917_ = lean_box(0);
v___x_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_918_, 0, v_a_912_);
lean_ctor_set(v___x_918_, 1, v___x_917_);
v___x_919_ = l_Lean_mkConst(v___x_916_, v___x_918_);
v___x_920_ = l_Lean_mkApp4(v___x_919_, v___x_903_, v___x_904_, v___x_905_, v_h_883_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v___x_920_);
v___x_922_ = v___x_914_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v___x_920_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v___x_905_);
lean_dec_ref(v___x_904_);
lean_dec_ref(v___x_903_);
lean_dec_ref(v_h_883_);
v_a_925_ = lean_ctor_get(v___x_911_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_911_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_911_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_911_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_883_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqOfHEq___boxed(lean_object* v_h_962_, lean_object* v_check_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
uint8_t v_check_boxed_969_; lean_object* v_res_970_; 
v_check_boxed_969_ = lean_unbox(v_check_963_);
v_res_970_ = l_Lean_Meta_mkEqOfHEq(v_h_962_, v_check_boxed_969_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
return v_res_970_;
}
}
static lean_object* _init_l_Lean_Meta_mkHEqOfEq___closed__2(void){
_start:
{
lean_object* v___x_974_; lean_object* v___x_975_; 
v___x_974_ = ((lean_object*)(l_Lean_Meta_mkEqSymm___closed__2));
v___x_975_ = l_Lean_stringToMessageData(v___x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq(lean_object* v_h_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_){
_start:
{
lean_object* v___x_982_; 
lean_inc_ref(v_h_976_);
v___x_982_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v_a_983_; lean_object* v___x_984_; lean_object* v___x_985_; uint8_t v___x_986_; 
v_a_983_ = lean_ctor_get(v___x_982_, 0);
lean_inc(v_a_983_);
lean_dec_ref_known(v___x_982_, 1);
v___x_984_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_985_ = lean_unsigned_to_nat(3u);
v___x_986_ = l_Lean_Expr_isAppOfArity(v_a_983_, v___x_984_, v___x_985_);
if (v___x_986_ == 0)
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; 
lean_dec(v_a_983_);
v___x_987_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_988_ = lean_obj_once(&l_Lean_Meta_mkHEqOfEq___closed__2, &l_Lean_Meta_mkHEqOfEq___closed__2_once, _init_l_Lean_Meta_mkHEqOfEq___closed__2);
v___x_989_ = l_Lean_indentExpr(v_h_976_);
v___x_990_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
v___x_991_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_987_, v___x_990_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
return v___x_991_;
}
else
{
lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_992_ = l_Lean_Expr_appFn_x21(v_a_983_);
v___x_993_ = l_Lean_Expr_appFn_x21(v___x_992_);
v___x_994_ = l_Lean_Expr_appArg_x21(v___x_993_);
lean_dec_ref(v___x_993_);
v___x_995_ = l_Lean_Expr_appArg_x21(v___x_992_);
lean_dec_ref(v___x_992_);
v___x_996_ = l_Lean_Expr_appArg_x21(v_a_983_);
lean_dec(v_a_983_);
lean_inc_ref(v___x_994_);
v___x_997_ = l_Lean_Meta_getLevel(v___x_994_, v_a_977_, v_a_978_, v_a_979_, v_a_980_);
if (lean_obj_tag(v___x_997_) == 0)
{
lean_object* v_a_998_; lean_object* v___x_1000_; uint8_t v_isShared_1001_; uint8_t v_isSharedCheck_1010_; 
v_a_998_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1000_ = v___x_997_;
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
else
{
lean_inc(v_a_998_);
lean_dec(v___x_997_);
v___x_1000_ = lean_box(0);
v_isShared_1001_ = v_isSharedCheck_1010_;
goto v_resetjp_999_;
}
v_resetjp_999_:
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1002_ = ((lean_object*)(l_Lean_Meta_mkHEqOfEq___closed__1));
v___x_1003_ = lean_box(0);
v___x_1004_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1004_, 0, v_a_998_);
lean_ctor_set(v___x_1004_, 1, v___x_1003_);
v___x_1005_ = l_Lean_mkConst(v___x_1002_, v___x_1004_);
v___x_1006_ = l_Lean_mkApp4(v___x_1005_, v___x_994_, v___x_995_, v___x_996_, v_h_976_);
if (v_isShared_1001_ == 0)
{
lean_ctor_set(v___x_1000_, 0, v___x_1006_);
v___x_1008_ = v___x_1000_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
lean_dec_ref(v___x_996_);
lean_dec_ref(v___x_995_);
lean_dec_ref(v___x_994_);
lean_dec_ref(v_h_976_);
v_a_1011_ = lean_ctor_get(v___x_997_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_997_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_997_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_997_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
else
{
lean_dec_ref(v_h_976_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkHEqOfEq___boxed(lean_object* v_h_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_Meta_mkHEqOfEq(v_h_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec(v_a_1023_);
lean_dec_ref(v_a_1022_);
lean_dec(v_a_1021_);
lean_dec_ref(v_a_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f(lean_object* v_e_1026_){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; uint8_t v___x_1029_; 
v___x_1027_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1028_ = lean_unsigned_to_nat(2u);
v___x_1029_ = l_Lean_Expr_isAppOfArity(v_e_1026_, v___x_1027_, v___x_1028_);
if (v___x_1029_ == 0)
{
lean_object* v___x_1030_; 
v___x_1030_ = lean_box(0);
return v___x_1030_;
}
else
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = l_Lean_Expr_appArg_x21(v_e_1026_);
v___x_1032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1032_, 0, v___x_1031_);
return v___x_1032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRefl_x3f___boxed(lean_object* v_e_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Meta_isRefl_x3f(v_e_1033_);
lean_dec_ref(v_e_1033_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(lean_object* v_msg_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_){
_start:
{
lean_object* v___f_1042_; lean_object* v___x_854__overap_1043_; lean_object* v___x_1044_; 
v___f_1042_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_854__overap_1043_ = lean_panic_fn_borrowed(v___f_1042_, v_msg_1036_);
lean_inc(v___y_1040_);
lean_inc_ref(v___y_1039_);
lean_inc(v___y_1038_);
lean_inc_ref(v___y_1037_);
v___x_1044_ = lean_apply_5(v___x_854__overap_1043_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, lean_box(0));
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___boxed(lean_object* v_msg_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v_msg_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
return v_res_1051_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__2(void){
_start:
{
lean_object* v___x_1055_; lean_object* v_dummy_1056_; 
v___x_1055_ = lean_box(0);
v_dummy_1056_ = l_Lean_Expr_sort___override(v___x_1055_);
return v_dummy_1056_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__6(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1060_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1061_ = lean_unsigned_to_nat(48u);
v___x_1062_ = lean_unsigned_to_nat(212u);
v___x_1063_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1064_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1065_ = l_mkPanicMessageWithDecl(v___x_1064_, v___x_1063_, v___x_1062_, v___x_1061_, v___x_1060_);
return v___x_1065_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__9(void){
_start:
{
lean_object* v___x_1069_; lean_object* v___x_1070_; 
v___x_1069_ = lean_unsigned_to_nat(0u);
v___x_1070_ = l_Lean_Expr_bvar___override(v___x_1069_);
return v___x_1070_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__10(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; 
v___x_1071_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = lean_mk_empty_array_with_capacity(v___x_1072_);
v___x_1074_ = lean_array_push(v___x_1073_, v___x_1071_);
return v___x_1074_;
}
}
static lean_object* _init_l_Lean_Meta_congrArg_x3f___closed__15(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1081_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__5));
v___x_1082_ = lean_unsigned_to_nat(49u);
v___x_1083_ = lean_unsigned_to_nat(209u);
v___x_1084_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__4));
v___x_1085_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_1086_ = l_mkPanicMessageWithDecl(v___x_1085_, v___x_1084_, v___x_1083_, v___x_1082_, v___x_1081_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f(lean_object* v_e_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; 
v___x_1142_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1143_ = lean_unsigned_to_nat(6u);
v___x_1144_ = l_Lean_Expr_isAppOfArity(v_e_1087_, v___x_1142_, v___x_1143_);
if (v___x_1144_ == 0)
{
v___y_1097_ = v_a_1088_;
v___y_1098_ = v_a_1089_;
v___y_1099_ = v_a_1090_;
v___y_1100_ = v_a_1091_;
goto v___jp_1096_;
}
else
{
lean_object* v_dummy_1145_; lean_object* v_nargs_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; uint8_t v___x_1152_; 
v_dummy_1145_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1146_ = l_Lean_Expr_getAppNumArgs(v_e_1087_);
lean_inc(v_nargs_1146_);
v___x_1147_ = lean_mk_array(v_nargs_1146_, v_dummy_1145_);
v___x_1148_ = lean_unsigned_to_nat(1u);
v___x_1149_ = lean_nat_sub(v_nargs_1146_, v___x_1148_);
lean_dec(v_nargs_1146_);
lean_inc_ref(v_e_1087_);
v___x_1150_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1087_, v___x_1147_, v___x_1149_);
v___x_1151_ = lean_array_get_size(v___x_1150_);
v___x_1152_ = lean_nat_dec_eq(v___x_1151_, v___x_1143_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; 
lean_dec_ref(v___x_1150_);
v___x_1153_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__15, &l_Lean_Meta_congrArg_x3f___closed__15_once, _init_l_Lean_Meta_congrArg_x3f___closed__15);
v___x_1154_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1153_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
if (lean_obj_tag(v___x_1154_) == 0)
{
lean_dec_ref_known(v___x_1154_, 1);
v___y_1097_ = v_a_1088_;
v___y_1098_ = v_a_1089_;
v___y_1099_ = v_a_1090_;
v___y_1100_ = v_a_1091_;
goto v___jp_1096_;
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec_ref(v_e_1087_);
v_a_1155_ = lean_ctor_get(v___x_1154_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1154_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1154_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
else
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; 
lean_dec_ref(v_e_1087_);
v___x_1163_ = lean_unsigned_to_nat(0u);
v___x_1164_ = lean_array_fget(v___x_1150_, v___x_1163_);
v___x_1165_ = lean_unsigned_to_nat(4u);
v___x_1166_ = lean_array_fget(v___x_1150_, v___x_1165_);
v___x_1167_ = lean_unsigned_to_nat(5u);
v___x_1168_ = lean_array_fget(v___x_1150_, v___x_1167_);
lean_dec_ref(v___x_1150_);
v___x_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1166_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1164_);
lean_ctor_set(v___x_1170_, 1, v___x_1169_);
v___x_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
v___x_1172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1172_, 0, v___x_1171_);
return v___x_1172_;
}
}
v___jp_1093_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1094_ = lean_box(0);
v___x_1095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
return v___x_1095_;
}
v___jp_1096_:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; uint8_t v___x_1103_; 
v___x_1101_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1102_ = lean_unsigned_to_nat(6u);
v___x_1103_ = l_Lean_Expr_isAppOfArity(v_e_1087_, v___x_1101_, v___x_1102_);
if (v___x_1103_ == 0)
{
lean_dec_ref(v_e_1087_);
goto v___jp_1093_;
}
else
{
lean_object* v_dummy_1104_; lean_object* v_nargs_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; uint8_t v___x_1111_; 
v_dummy_1104_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_1105_ = l_Lean_Expr_getAppNumArgs(v_e_1087_);
lean_inc(v_nargs_1105_);
v___x_1106_ = lean_mk_array(v_nargs_1105_, v_dummy_1104_);
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_sub(v_nargs_1105_, v___x_1107_);
lean_dec(v_nargs_1105_);
v___x_1109_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_1087_, v___x_1106_, v___x_1108_);
v___x_1110_ = lean_array_get_size(v___x_1109_);
v___x_1111_ = lean_nat_dec_eq(v___x_1110_, v___x_1102_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_dec_ref(v___x_1109_);
v___x_1112_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__6, &l_Lean_Meta_congrArg_x3f___closed__6_once, _init_l_Lean_Meta_congrArg_x3f___closed__6);
v___x_1113_ = l_panic___at___00Lean_Meta_congrArg_x3f_spec__0(v___x_1112_, v___y_1097_, v___y_1098_, v___y_1099_, v___y_1100_);
if (lean_obj_tag(v___x_1113_) == 0)
{
lean_dec_ref_known(v___x_1113_, 1);
goto v___jp_1093_;
}
else
{
lean_object* v_a_1114_; lean_object* v___x_1116_; uint8_t v_isShared_1117_; uint8_t v_isSharedCheck_1121_; 
v_a_1114_ = lean_ctor_get(v___x_1113_, 0);
v_isSharedCheck_1121_ = !lean_is_exclusive(v___x_1113_);
if (v_isSharedCheck_1121_ == 0)
{
v___x_1116_ = v___x_1113_;
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
else
{
lean_inc(v_a_1114_);
lean_dec(v___x_1113_);
v___x_1116_ = lean_box(0);
v_isShared_1117_ = v_isSharedCheck_1121_;
goto v_resetjp_1115_;
}
v_resetjp_1115_:
{
lean_object* v___x_1119_; 
if (v_isShared_1117_ == 0)
{
v___x_1119_ = v___x_1116_;
goto v_reusejp_1118_;
}
else
{
lean_object* v_reuseFailAlloc_1120_; 
v_reuseFailAlloc_1120_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
v___x_1119_ = v_reuseFailAlloc_1120_;
goto v_reusejp_1118_;
}
v_reusejp_1118_:
{
return v___x_1119_;
}
}
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; lean_object* v_00_u03b1_x27_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v_f_x27_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1122_ = lean_unsigned_to_nat(0u);
v___x_1123_ = lean_array_fget(v___x_1109_, v___x_1122_);
v___x_1124_ = lean_array_fget(v___x_1109_, v___x_1107_);
v___x_1125_ = lean_unsigned_to_nat(4u);
v___x_1126_ = lean_array_fget(v___x_1109_, v___x_1125_);
v___x_1127_ = lean_unsigned_to_nat(5u);
v___x_1128_ = lean_array_fget(v___x_1109_, v___x_1127_);
lean_dec_ref(v___x_1109_);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1130_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1131_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1132_ = l_Lean_Expr_beta(v___x_1124_, v___x_1131_);
v___x_1133_ = 0;
v_00_u03b1_x27_1134_ = l_Lean_Expr_forallE___override(v___x_1129_, v___x_1123_, v___x_1132_, v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__12));
v___x_1136_ = l_Lean_Expr_app___override(v___x_1130_, v___x_1128_);
lean_inc_ref(v_00_u03b1_x27_1134_);
v_f_x27_1137_ = l_Lean_Expr_lam___override(v___x_1135_, v_00_u03b1_x27_1134_, v___x_1136_, v___x_1133_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v_f_x27_1137_);
lean_ctor_set(v___x_1138_, 1, v___x_1126_);
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_00_u03b1_x27_1134_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1140_, 0, v___x_1139_);
v___x_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1140_);
return v___x_1141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_congrArg_x3f___boxed(lean_object* v_e_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_, lean_object* v_a_1176_, lean_object* v_a_1177_, lean_object* v_a_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_Lean_Meta_congrArg_x3f(v_e_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
lean_dec(v_a_1177_);
lean_dec_ref(v_a_1176_);
lean_dec(v_a_1175_);
lean_dec_ref(v_a_1174_);
return v_res_1179_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrArg___closed__2(void){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___x_1183_ = ((lean_object*)(l_Lean_Meta_mkCongrArg___closed__1));
v___x_1184_ = l_Lean_MessageData_ofFormat(v___x_1183_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg(lean_object* v_f_1185_, lean_object* v_h_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_, lean_object* v_a_1189_, lean_object* v_a_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_Meta_isRefl_x3f(v_h_1186_);
if (lean_obj_tag(v___x_1192_) == 1)
{
lean_object* v_val_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
lean_dec_ref(v_h_1186_);
v_val_1193_ = lean_ctor_get(v___x_1192_, 0);
lean_inc(v_val_1193_);
lean_dec_ref_known(v___x_1192_, 1);
v___x_1194_ = l_Lean_Expr_app___override(v_f_1185_, v_val_1193_);
v___x_1195_ = l_Lean_Meta_mkEqRefl(v___x_1194_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v___x_1195_;
}
else
{
lean_object* v___x_1196_; 
lean_dec(v___x_1192_);
lean_inc_ref(v_h_1186_);
v___x_1196_ = l_Lean_Meta_congrArg_x3f(v_h_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1196_) == 0)
{
lean_object* v_a_1197_; 
v_a_1197_ = lean_ctor_get(v___x_1196_, 0);
lean_inc(v_a_1197_);
lean_dec_ref_known(v___x_1196_, 1);
if (lean_obj_tag(v_a_1197_) == 1)
{
lean_object* v_val_1198_; lean_object* v_snd_1199_; lean_object* v_fst_1200_; lean_object* v_fst_1201_; lean_object* v_snd_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; uint8_t v___x_1210_; lean_object* v___x_1211_; 
lean_dec_ref(v_h_1186_);
v_val_1198_ = lean_ctor_get(v_a_1197_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v_a_1197_, 1);
v_snd_1199_ = lean_ctor_get(v_val_1198_, 1);
lean_inc(v_snd_1199_);
v_fst_1200_ = lean_ctor_get(v_val_1198_, 0);
lean_inc(v_fst_1200_);
lean_dec(v_val_1198_);
v_fst_1201_ = lean_ctor_get(v_snd_1199_, 0);
lean_inc(v_fst_1201_);
v_snd_1202_ = lean_ctor_get(v_snd_1199_, 1);
lean_inc(v_snd_1202_);
lean_dec(v_snd_1199_);
v___x_1203_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1204_ = lean_unsigned_to_nat(1u);
v___x_1205_ = lean_mk_empty_array_with_capacity(v___x_1204_);
v___x_1206_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__10, &l_Lean_Meta_congrArg_x3f___closed__10_once, _init_l_Lean_Meta_congrArg_x3f___closed__10);
v___x_1207_ = l_Lean_Expr_beta(v_fst_1201_, v___x_1206_);
v___x_1208_ = lean_array_push(v___x_1205_, v___x_1207_);
v___x_1209_ = l_Lean_Expr_beta(v_f_1185_, v___x_1208_);
v___x_1210_ = 0;
v___x_1211_ = l_Lean_Expr_lam___override(v___x_1203_, v_fst_1200_, v___x_1209_, v___x_1210_);
v_f_1185_ = v___x_1211_;
v_h_1186_ = v_snd_1202_;
goto _start;
}
else
{
lean_object* v___x_1213_; 
lean_dec(v_a_1197_);
lean_inc_ref(v_h_1186_);
v___x_1213_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1186_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1215_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref_known(v___x_1213_, 1);
lean_inc_ref(v_f_1185_);
v___x_1215_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_f_1185_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref_known(v___x_1215_, 1);
if (lean_obj_tag(v_a_1216_) == 7)
{
lean_object* v_binderType_1223_; lean_object* v_body_1224_; uint8_t v___x_1225_; 
v_binderType_1223_ = lean_ctor_get(v_a_1216_, 1);
v_body_1224_ = lean_ctor_get(v_a_1216_, 2);
v___x_1225_ = l_Lean_Expr_hasLooseBVars(v_body_1224_);
if (v___x_1225_ == 0)
{
lean_object* v___x_1226_; lean_object* v___x_1227_; uint8_t v___x_1228_; 
lean_inc_ref(v_body_1224_);
lean_inc_ref(v_binderType_1223_);
lean_dec_ref_known(v_a_1216_, 3);
v___x_1226_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1227_ = lean_unsigned_to_nat(3u);
v___x_1228_ = l_Lean_Expr_isAppOfArity(v_a_1214_, v___x_1226_, v___x_1227_);
if (v___x_1228_ == 0)
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; 
lean_dec_ref(v_body_1224_);
lean_dec_ref(v_binderType_1223_);
lean_dec_ref(v_f_1185_);
v___x_1229_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1230_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1231_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1186_, v_a_1214_);
v___x_1232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1230_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1229_, v___x_1232_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v___x_1233_;
}
else
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1234_ = l_Lean_Expr_appFn_x21(v_a_1214_);
v___x_1235_ = l_Lean_Expr_appArg_x21(v___x_1234_);
lean_dec_ref(v___x_1234_);
v___x_1236_ = l_Lean_Expr_appArg_x21(v_a_1214_);
lean_dec(v_a_1214_);
lean_inc_ref(v_binderType_1223_);
v___x_1237_ = l_Lean_Meta_getLevel(v_binderType_1223_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; lean_object* v___x_1239_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
lean_inc_ref(v_body_1224_);
v___x_1239_ = l_Lean_Meta_getLevel(v_body_1224_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; lean_object* v___x_1242_; uint8_t v_isShared_1243_; uint8_t v_isSharedCheck_1253_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1253_ == 0)
{
v___x_1242_ = v___x_1239_;
v_isShared_1243_ = v_isSharedCheck_1253_;
goto v_resetjp_1241_;
}
else
{
lean_inc(v_a_1240_);
lean_dec(v___x_1239_);
v___x_1242_ = lean_box(0);
v_isShared_1243_ = v_isSharedCheck_1253_;
goto v_resetjp_1241_;
}
v_resetjp_1241_:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1244_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1246_, 0, v_a_1240_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1238_);
lean_ctor_set(v___x_1247_, 1, v___x_1246_);
v___x_1248_ = l_Lean_mkConst(v___x_1244_, v___x_1247_);
v___x_1249_ = l_Lean_mkApp6(v___x_1248_, v_binderType_1223_, v_body_1224_, v___x_1235_, v___x_1236_, v_f_1185_, v_h_1186_);
if (v_isShared_1243_ == 0)
{
lean_ctor_set(v___x_1242_, 0, v___x_1249_);
v___x_1251_ = v___x_1242_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1252_; 
v_reuseFailAlloc_1252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1252_, 0, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1252_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
return v___x_1251_;
}
}
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
lean_dec(v_a_1238_);
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_body_1224_);
lean_dec_ref(v_binderType_1223_);
lean_dec_ref(v_h_1186_);
lean_dec_ref(v_f_1185_);
v_a_1254_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1239_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1239_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
v___x_1259_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
return v___x_1259_;
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec_ref(v___x_1236_);
lean_dec_ref(v___x_1235_);
lean_dec_ref(v_body_1224_);
lean_dec_ref(v_binderType_1223_);
lean_dec_ref(v_h_1186_);
lean_dec_ref(v_f_1185_);
v_a_1262_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1237_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1237_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
else
{
lean_dec(v_a_1214_);
lean_dec_ref(v_h_1186_);
goto v___jp_1217_;
}
}
else
{
lean_dec(v_a_1214_);
lean_dec_ref(v_h_1186_);
goto v___jp_1217_;
}
v___jp_1217_:
{
lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v___x_1218_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__14));
v___x_1219_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1220_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_f_1185_, v_a_1216_);
v___x_1221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
v___x_1222_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1218_, v___x_1221_, v_a_1187_, v_a_1188_, v_a_1189_, v_a_1190_);
return v___x_1222_;
}
}
else
{
lean_dec(v_a_1214_);
lean_dec_ref(v_h_1186_);
lean_dec_ref(v_f_1185_);
return v___x_1215_;
}
}
else
{
lean_dec_ref(v_h_1186_);
lean_dec_ref(v_f_1185_);
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1270_; lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1277_; 
lean_dec_ref(v_h_1186_);
lean_dec_ref(v_f_1185_);
v_a_1270_ = lean_ctor_get(v___x_1196_, 0);
v_isSharedCheck_1277_ = !lean_is_exclusive(v___x_1196_);
if (v_isSharedCheck_1277_ == 0)
{
v___x_1272_ = v___x_1196_;
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
else
{
lean_inc(v_a_1270_);
lean_dec(v___x_1196_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1277_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1275_; 
if (v_isShared_1273_ == 0)
{
v___x_1275_ = v___x_1272_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1276_; 
v_reuseFailAlloc_1276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1276_, 0, v_a_1270_);
v___x_1275_ = v_reuseFailAlloc_1276_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
return v___x_1275_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrArg___boxed(lean_object* v_f_1278_, lean_object* v_h_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_, lean_object* v_a_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l_Lean_Meta_mkCongrArg(v_f_1278_, v_h_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
lean_dec(v_a_1283_);
lean_dec_ref(v_a_1282_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
return v_res_1285_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__0(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1286_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__9, &l_Lean_Meta_congrArg_x3f___closed__9_once, _init_l_Lean_Meta_congrArg_x3f___closed__9);
v___x_1287_ = lean_unsigned_to_nat(2u);
v___x_1288_ = lean_mk_empty_array_with_capacity(v___x_1287_);
v___x_1289_ = lean_array_push(v___x_1288_, v___x_1286_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_Meta_mkCongrFun___closed__3(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_Meta_mkCongrFun___closed__2));
v___x_1294_ = l_Lean_MessageData_ofFormat(v___x_1293_);
return v___x_1294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun(lean_object* v_h_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_){
_start:
{
lean_object* v___x_1302_; 
v___x_1302_ = l_Lean_Meta_isRefl_x3f(v_h_1295_);
if (lean_obj_tag(v___x_1302_) == 1)
{
lean_object* v_val_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
lean_dec_ref(v_h_1295_);
v_val_1303_ = lean_ctor_get(v___x_1302_, 0);
lean_inc(v_val_1303_);
lean_dec_ref_known(v___x_1302_, 1);
v___x_1304_ = l_Lean_Expr_app___override(v_val_1303_, v_a_1296_);
v___x_1305_ = l_Lean_Meta_mkEqRefl(v___x_1304_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1305_;
}
else
{
lean_object* v___x_1306_; 
lean_dec(v___x_1302_);
lean_inc_ref(v_h_1295_);
v___x_1306_ = l_Lean_Meta_congrArg_x3f(v_h_1295_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref_known(v___x_1306_, 1);
if (lean_obj_tag(v_a_1307_) == 1)
{
lean_object* v_val_1308_; lean_object* v_snd_1309_; lean_object* v_fst_1310_; lean_object* v_fst_1311_; lean_object* v_snd_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; 
lean_dec_ref(v_h_1295_);
v_val_1308_ = lean_ctor_get(v_a_1307_, 0);
lean_inc(v_val_1308_);
lean_dec_ref_known(v_a_1307_, 1);
v_snd_1309_ = lean_ctor_get(v_val_1308_, 1);
lean_inc(v_snd_1309_);
v_fst_1310_ = lean_ctor_get(v_val_1308_, 0);
lean_inc(v_fst_1310_);
lean_dec(v_val_1308_);
v_fst_1311_ = lean_ctor_get(v_snd_1309_, 0);
lean_inc(v_fst_1311_);
v_snd_1312_ = lean_ctor_get(v_snd_1309_, 1);
lean_inc(v_snd_1312_);
lean_dec(v_snd_1309_);
v___x_1313_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__8));
v___x_1314_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__0, &l_Lean_Meta_mkCongrFun___closed__0_once, _init_l_Lean_Meta_mkCongrFun___closed__0);
v___x_1315_ = lean_array_push(v___x_1314_, v_a_1296_);
v___x_1316_ = l_Lean_Expr_beta(v_fst_1311_, v___x_1315_);
v___x_1317_ = 0;
v___x_1318_ = l_Lean_Expr_lam___override(v___x_1313_, v_fst_1310_, v___x_1316_, v___x_1317_);
v___x_1319_ = l_Lean_Meta_mkCongrArg(v___x_1318_, v_snd_1312_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1319_;
}
else
{
lean_object* v___x_1320_; 
lean_dec(v_a_1307_);
lean_inc_ref(v_h_1295_);
v___x_1320_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_1295_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1320_) == 0)
{
lean_object* v_a_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref_known(v___x_1320_, 1);
v___x_1322_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1323_ = lean_unsigned_to_nat(3u);
v___x_1324_ = l_Lean_Expr_isAppOfArity(v_a_1321_, v___x_1322_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
lean_dec_ref(v_a_1296_);
v___x_1325_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1326_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1327_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1295_, v_a_1321_);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1326_);
lean_ctor_set(v___x_1328_, 1, v___x_1327_);
v___x_1329_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1325_, v___x_1328_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1330_ = l_Lean_Expr_appFn_x21(v_a_1321_);
v___x_1331_ = l_Lean_Expr_appFn_x21(v___x_1330_);
v___x_1332_ = l_Lean_Expr_appArg_x21(v___x_1331_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = l_Lean_Expr_appArg_x21(v___x_1330_);
lean_dec_ref(v___x_1330_);
v___x_1334_ = l_Lean_Expr_appArg_x21(v_a_1321_);
v___x_1335_ = l_Lean_Meta_whnfD(v___x_1332_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1335_) == 0)
{
lean_object* v_a_1336_; 
v_a_1336_ = lean_ctor_get(v___x_1335_, 0);
lean_inc(v_a_1336_);
lean_dec_ref_known(v___x_1335_, 1);
if (lean_obj_tag(v_a_1336_) == 7)
{
lean_object* v_binderName_1337_; lean_object* v_binderType_1338_; lean_object* v_body_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
lean_dec(v_a_1321_);
v_binderName_1337_ = lean_ctor_get(v_a_1336_, 0);
lean_inc(v_binderName_1337_);
v_binderType_1338_ = lean_ctor_get(v_a_1336_, 1);
lean_inc_ref_n(v_binderType_1338_, 3);
v_body_1339_ = lean_ctor_get(v_a_1336_, 2);
lean_inc_ref(v_body_1339_);
lean_dec_ref_known(v_a_1336_, 3);
v___x_1340_ = 0;
v___x_1341_ = l_Lean_mkLambda(v_binderName_1337_, v___x_1340_, v_binderType_1338_, v_body_1339_);
v___x_1342_ = l_Lean_Meta_getLevel(v_binderType_1338_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
lean_inc_ref(v_a_1296_);
lean_inc_ref(v___x_1341_);
v___x_1344_ = l_Lean_Expr_app___override(v___x_1341_, v_a_1296_);
v___x_1345_ = l_Lean_Meta_getLevel(v___x_1344_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1359_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1348_ = v___x_1345_;
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1345_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1359_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1357_; 
v___x_1350_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1351_ = lean_box(0);
v___x_1352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1352_, 0, v_a_1346_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1353_, 0, v_a_1343_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = l_Lean_mkConst(v___x_1350_, v___x_1353_);
v___x_1355_ = l_Lean_mkApp6(v___x_1354_, v_binderType_1338_, v___x_1341_, v___x_1333_, v___x_1334_, v_h_1295_, v_a_1296_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 0, v___x_1355_);
v___x_1357_ = v___x_1348_;
goto v_reusejp_1356_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v___x_1355_);
v___x_1357_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1356_;
}
v_reusejp_1356_:
{
return v___x_1357_;
}
}
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_a_1343_);
lean_dec_ref(v___x_1341_);
lean_dec_ref(v_binderType_1338_);
lean_dec_ref(v___x_1334_);
lean_dec_ref(v___x_1333_);
lean_dec_ref(v_a_1296_);
lean_dec_ref(v_h_1295_);
v_a_1360_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1345_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1345_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
}
}
}
}
else
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
lean_dec_ref(v___x_1341_);
lean_dec_ref(v_binderType_1338_);
lean_dec_ref(v___x_1334_);
lean_dec_ref(v___x_1333_);
lean_dec_ref(v_a_1296_);
lean_dec_ref(v_h_1295_);
v_a_1368_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1342_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1342_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
}
else
{
lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
lean_dec(v_a_1336_);
lean_dec_ref(v___x_1334_);
lean_dec_ref(v___x_1333_);
lean_dec_ref(v_a_1296_);
v___x_1376_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__1));
v___x_1377_ = lean_obj_once(&l_Lean_Meta_mkCongrFun___closed__3, &l_Lean_Meta_mkCongrFun___closed__3_once, _init_l_Lean_Meta_mkCongrFun___closed__3);
v___x_1378_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_1295_, v_a_1321_);
v___x_1379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1379_, 0, v___x_1377_);
lean_ctor_set(v___x_1379_, 1, v___x_1378_);
v___x_1380_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1376_, v___x_1379_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
return v___x_1380_;
}
}
else
{
lean_dec_ref(v___x_1334_);
lean_dec_ref(v___x_1333_);
lean_dec(v_a_1321_);
lean_dec_ref(v_a_1296_);
lean_dec_ref(v_h_1295_);
return v___x_1335_;
}
}
}
else
{
lean_dec_ref(v_a_1296_);
lean_dec_ref(v_h_1295_);
return v___x_1320_;
}
}
}
else
{
lean_object* v_a_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1388_; 
lean_dec_ref(v_a_1296_);
lean_dec_ref(v_h_1295_);
v_a_1381_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1388_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1388_ == 0)
{
v___x_1383_ = v___x_1306_;
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_a_1381_);
lean_dec(v___x_1306_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1388_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___x_1386_; 
if (v_isShared_1384_ == 0)
{
v___x_1386_ = v___x_1383_;
goto v_reusejp_1385_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v_a_1381_);
v___x_1386_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1385_;
}
v_reusejp_1385_:
{
return v___x_1386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongrFun___boxed(lean_object* v_h_1389_, lean_object* v_a_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_, lean_object* v_a_1393_, lean_object* v_a_1394_, lean_object* v_a_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_Meta_mkCongrFun(v_h_1389_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_, v_a_1394_);
lean_dec(v_a_1394_);
lean_dec_ref(v_a_1393_);
lean_dec(v_a_1392_);
lean_dec_ref(v_a_1391_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr(lean_object* v_h_u2081_1400_, lean_object* v_h_u2082_1401_, lean_object* v_a_1402_, lean_object* v_a_1403_, lean_object* v_a_1404_, lean_object* v_a_1405_){
_start:
{
lean_object* v___x_1407_; uint8_t v___x_1408_; 
v___x_1407_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_1408_ = l_Lean_Expr_isAppOf(v_h_u2081_1400_, v___x_1407_);
if (v___x_1408_ == 0)
{
uint8_t v___x_1409_; 
v___x_1409_ = l_Lean_Expr_isAppOf(v_h_u2082_1401_, v___x_1407_);
if (v___x_1409_ == 0)
{
lean_object* v___x_1410_; 
lean_inc_ref(v_h_u2081_1400_);
v___x_1410_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2081_1400_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1410_) == 0)
{
lean_object* v_a_1411_; lean_object* v___x_1412_; 
v_a_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___x_1410_, 1);
lean_inc_ref(v_h_u2082_1401_);
v___x_1412_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h_u2082_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1412_) == 0)
{
lean_object* v_a_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; uint8_t v___x_1416_; 
v_a_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc(v_a_1413_);
lean_dec_ref_known(v___x_1412_, 1);
v___x_1414_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_1415_ = lean_unsigned_to_nat(3u);
v___x_1416_ = l_Lean_Expr_isAppOfArity(v_a_1411_, v___x_1414_, v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; 
lean_dec(v_a_1413_);
lean_dec_ref(v_h_u2082_1401_);
v___x_1417_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1418_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1419_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1400_, v_a_1411_);
v___x_1420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1420_, 0, v___x_1418_);
lean_ctor_set(v___x_1420_, 1, v___x_1419_);
v___x_1421_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1417_, v___x_1420_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1421_;
}
else
{
uint8_t v___x_1422_; 
v___x_1422_ = l_Lean_Expr_isAppOfArity(v_a_1413_, v___x_1414_, v___x_1415_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
lean_dec(v_a_1411_);
lean_dec_ref(v_h_u2081_1400_);
v___x_1423_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1424_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_1425_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2082_1401_, v_a_1413_);
v___x_1426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1424_);
lean_ctor_set(v___x_1426_, 1, v___x_1425_);
v___x_1427_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1423_, v___x_1426_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1428_ = l_Lean_Expr_appFn_x21(v_a_1411_);
v___x_1429_ = l_Lean_Expr_appFn_x21(v___x_1428_);
v___x_1430_ = l_Lean_Expr_appArg_x21(v___x_1429_);
lean_dec_ref(v___x_1429_);
v___x_1431_ = l_Lean_Expr_appArg_x21(v___x_1428_);
lean_dec_ref(v___x_1428_);
v___x_1432_ = l_Lean_Expr_appArg_x21(v_a_1411_);
v___x_1433_ = l_Lean_Expr_appFn_x21(v_a_1413_);
v___x_1434_ = l_Lean_Expr_appFn_x21(v___x_1433_);
v___x_1435_ = l_Lean_Expr_appArg_x21(v___x_1434_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = l_Lean_Expr_appArg_x21(v___x_1433_);
lean_dec_ref(v___x_1433_);
v___x_1437_ = l_Lean_Expr_appArg_x21(v_a_1413_);
lean_dec(v_a_1413_);
v___x_1438_ = l_Lean_Meta_whnfD(v___x_1430_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v_a_1439_; 
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
lean_inc(v_a_1439_);
lean_dec_ref_known(v___x_1438_, 1);
if (lean_obj_tag(v_a_1439_) == 7)
{
lean_object* v_body_1446_; uint8_t v___x_1447_; 
v_body_1446_ = lean_ctor_get(v_a_1439_, 2);
lean_inc_ref(v_body_1446_);
lean_dec_ref_known(v_a_1439_, 3);
v___x_1447_ = l_Lean_Expr_hasLooseBVars(v_body_1446_);
if (v___x_1447_ == 0)
{
lean_object* v___x_1448_; 
lean_dec(v_a_1411_);
lean_inc_ref(v___x_1435_);
v___x_1448_ = l_Lean_Meta_getLevel(v___x_1435_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___x_1448_, 1);
lean_inc_ref(v_body_1446_);
v___x_1450_ = l_Lean_Meta_getLevel(v_body_1446_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; lean_object* v___x_1453_; uint8_t v_isShared_1454_; uint8_t v_isSharedCheck_1464_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1464_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1453_ = v___x_1450_;
v_isShared_1454_ = v_isSharedCheck_1464_;
goto v_resetjp_1452_;
}
else
{
lean_inc(v_a_1451_);
lean_dec(v___x_1450_);
v___x_1453_ = lean_box(0);
v_isShared_1454_ = v_isSharedCheck_1464_;
goto v_resetjp_1452_;
}
v_resetjp_1452_:
{
lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1462_; 
v___x_1455_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1456_ = lean_box(0);
v___x_1457_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1457_, 0, v_a_1451_);
lean_ctor_set(v___x_1457_, 1, v___x_1456_);
v___x_1458_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1458_, 0, v_a_1449_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
v___x_1459_ = l_Lean_mkConst(v___x_1455_, v___x_1458_);
v___x_1460_ = l_Lean_mkApp8(v___x_1459_, v___x_1435_, v_body_1446_, v___x_1431_, v___x_1432_, v___x_1436_, v___x_1437_, v_h_u2081_1400_, v_h_u2082_1401_);
if (v_isShared_1454_ == 0)
{
lean_ctor_set(v___x_1453_, 0, v___x_1460_);
v___x_1462_ = v___x_1453_;
goto v_reusejp_1461_;
}
else
{
lean_object* v_reuseFailAlloc_1463_; 
v_reuseFailAlloc_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1463_, 0, v___x_1460_);
v___x_1462_ = v_reuseFailAlloc_1463_;
goto v_reusejp_1461_;
}
v_reusejp_1461_:
{
return v___x_1462_;
}
}
}
else
{
lean_object* v_a_1465_; lean_object* v___x_1467_; uint8_t v_isShared_1468_; uint8_t v_isSharedCheck_1472_; 
lean_dec(v_a_1449_);
lean_dec_ref(v_body_1446_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_h_u2082_1401_);
lean_dec_ref(v_h_u2081_1400_);
v_a_1465_ = lean_ctor_get(v___x_1450_, 0);
v_isSharedCheck_1472_ = !lean_is_exclusive(v___x_1450_);
if (v_isSharedCheck_1472_ == 0)
{
v___x_1467_ = v___x_1450_;
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
else
{
lean_inc(v_a_1465_);
lean_dec(v___x_1450_);
v___x_1467_ = lean_box(0);
v_isShared_1468_ = v_isSharedCheck_1472_;
goto v_resetjp_1466_;
}
v_resetjp_1466_:
{
lean_object* v___x_1470_; 
if (v_isShared_1468_ == 0)
{
v___x_1470_ = v___x_1467_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_a_1465_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
else
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1480_; 
lean_dec_ref(v_body_1446_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_h_u2082_1401_);
lean_dec_ref(v_h_u2081_1400_);
v_a_1473_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1475_ = v___x_1448_;
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1448_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1480_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
lean_object* v___x_1478_; 
if (v_isShared_1476_ == 0)
{
v___x_1478_ = v___x_1475_;
goto v_reusejp_1477_;
}
else
{
lean_object* v_reuseFailAlloc_1479_; 
v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1479_, 0, v_a_1473_);
v___x_1478_ = v_reuseFailAlloc_1479_;
goto v_reusejp_1477_;
}
v_reusejp_1477_:
{
return v___x_1478_;
}
}
}
}
else
{
lean_dec_ref(v_body_1446_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_h_u2082_1401_);
goto v___jp_1440_;
}
}
else
{
lean_dec(v_a_1439_);
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec_ref(v_h_u2082_1401_);
goto v___jp_1440_;
}
v___jp_1440_:
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1441_ = ((lean_object*)(l_Lean_Meta_mkCongr___closed__1));
v___x_1442_ = lean_obj_once(&l_Lean_Meta_mkCongrArg___closed__2, &l_Lean_Meta_mkCongrArg___closed__2_once, _init_l_Lean_Meta_mkCongrArg___closed__2);
v___x_1443_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_u2081_1400_, v_a_1411_);
v___x_1444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1444_, 0, v___x_1442_);
lean_ctor_set(v___x_1444_, 1, v___x_1443_);
v___x_1445_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_1441_, v___x_1444_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1445_;
}
}
else
{
lean_dec_ref(v___x_1437_);
lean_dec_ref(v___x_1436_);
lean_dec_ref(v___x_1435_);
lean_dec_ref(v___x_1432_);
lean_dec_ref(v___x_1431_);
lean_dec(v_a_1411_);
lean_dec_ref(v_h_u2082_1401_);
lean_dec_ref(v_h_u2081_1400_);
return v___x_1438_;
}
}
}
}
else
{
lean_dec(v_a_1411_);
lean_dec_ref(v_h_u2082_1401_);
lean_dec_ref(v_h_u2081_1400_);
return v___x_1412_;
}
}
else
{
lean_dec_ref(v_h_u2082_1401_);
lean_dec_ref(v_h_u2081_1400_);
return v___x_1410_;
}
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; 
v___x_1481_ = l_Lean_Expr_appArg_x21(v_h_u2082_1401_);
lean_dec_ref(v_h_u2082_1401_);
v___x_1482_ = l_Lean_Meta_mkCongrFun(v_h_u2081_1400_, v___x_1481_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1482_;
}
}
else
{
lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1483_ = l_Lean_Expr_appArg_x21(v_h_u2081_1400_);
lean_dec_ref(v_h_u2081_1400_);
v___x_1484_ = l_Lean_Meta_mkCongrArg(v___x_1483_, v_h_u2082_1401_, v_a_1402_, v_a_1403_, v_a_1404_, v_a_1405_);
return v___x_1484_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkCongr___boxed(lean_object* v_h_u2081_1485_, lean_object* v_h_u2082_1486_, lean_object* v_a_1487_, lean_object* v_a_1488_, lean_object* v_a_1489_, lean_object* v_a_1490_, lean_object* v_a_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Meta_mkCongr(v_h_u2081_1485_, v_h_u2082_1486_, v_a_1487_, v_a_1488_, v_a_1489_, v_a_1490_);
lean_dec(v_a_1490_);
lean_dec_ref(v_a_1489_);
lean_dec(v_a_1488_);
lean_dec_ref(v_a_1487_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(lean_object* v_e_1493_, lean_object* v___y_1494_){
_start:
{
uint8_t v___x_1496_; 
v___x_1496_ = l_Lean_Expr_hasMVar(v_e_1493_);
if (v___x_1496_ == 0)
{
lean_object* v___x_1497_; 
v___x_1497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1497_, 0, v_e_1493_);
return v___x_1497_;
}
else
{
lean_object* v___x_1498_; lean_object* v_mctx_1499_; lean_object* v___x_1500_; lean_object* v_fst_1501_; lean_object* v_snd_1502_; lean_object* v___x_1503_; lean_object* v_cache_1504_; lean_object* v_zetaDeltaFVarIds_1505_; lean_object* v_postponed_1506_; lean_object* v_diag_1507_; lean_object* v___x_1509_; uint8_t v_isShared_1510_; uint8_t v_isSharedCheck_1516_; 
v___x_1498_ = lean_st_ref_get(v___y_1494_);
v_mctx_1499_ = lean_ctor_get(v___x_1498_, 0);
lean_inc_ref(v_mctx_1499_);
lean_dec(v___x_1498_);
v___x_1500_ = l_Lean_instantiateMVarsCore(v_mctx_1499_, v_e_1493_);
v_fst_1501_ = lean_ctor_get(v___x_1500_, 0);
lean_inc(v_fst_1501_);
v_snd_1502_ = lean_ctor_get(v___x_1500_, 1);
lean_inc(v_snd_1502_);
lean_dec_ref(v___x_1500_);
v___x_1503_ = lean_st_ref_take(v___y_1494_);
v_cache_1504_ = lean_ctor_get(v___x_1503_, 1);
v_zetaDeltaFVarIds_1505_ = lean_ctor_get(v___x_1503_, 2);
v_postponed_1506_ = lean_ctor_get(v___x_1503_, 3);
v_diag_1507_ = lean_ctor_get(v___x_1503_, 4);
v_isSharedCheck_1516_ = !lean_is_exclusive(v___x_1503_);
if (v_isSharedCheck_1516_ == 0)
{
lean_object* v_unused_1517_; 
v_unused_1517_ = lean_ctor_get(v___x_1503_, 0);
lean_dec(v_unused_1517_);
v___x_1509_ = v___x_1503_;
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
else
{
lean_inc(v_diag_1507_);
lean_inc(v_postponed_1506_);
lean_inc(v_zetaDeltaFVarIds_1505_);
lean_inc(v_cache_1504_);
lean_dec(v___x_1503_);
v___x_1509_ = lean_box(0);
v_isShared_1510_ = v_isSharedCheck_1516_;
goto v_resetjp_1508_;
}
v_resetjp_1508_:
{
lean_object* v___x_1512_; 
if (v_isShared_1510_ == 0)
{
lean_ctor_set(v___x_1509_, 0, v_snd_1502_);
v___x_1512_ = v___x_1509_;
goto v_reusejp_1511_;
}
else
{
lean_object* v_reuseFailAlloc_1515_; 
v_reuseFailAlloc_1515_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1515_, 0, v_snd_1502_);
lean_ctor_set(v_reuseFailAlloc_1515_, 1, v_cache_1504_);
lean_ctor_set(v_reuseFailAlloc_1515_, 2, v_zetaDeltaFVarIds_1505_);
lean_ctor_set(v_reuseFailAlloc_1515_, 3, v_postponed_1506_);
lean_ctor_set(v_reuseFailAlloc_1515_, 4, v_diag_1507_);
v___x_1512_ = v_reuseFailAlloc_1515_;
goto v_reusejp_1511_;
}
v_reusejp_1511_:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_st_ref_put(v___y_1494_, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v_fst_1501_);
return v___x_1514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg___boxed(lean_object* v_e_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1518_, v___y_1519_);
lean_dec(v___y_1519_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(lean_object* v_e_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v_e_1522_, v___y_1524_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___boxed(lean_object* v_e_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1(v_e_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1536_, lean_object* v_x_1537_, lean_object* v_x_1538_, lean_object* v_x_1539_){
_start:
{
lean_object* v_ks_1540_; lean_object* v_vs_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1565_; 
v_ks_1540_ = lean_ctor_get(v_x_1536_, 0);
v_vs_1541_ = lean_ctor_get(v_x_1536_, 1);
v_isSharedCheck_1565_ = !lean_is_exclusive(v_x_1536_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1543_ = v_x_1536_;
v_isShared_1544_ = v_isSharedCheck_1565_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_vs_1541_);
lean_inc(v_ks_1540_);
lean_dec(v_x_1536_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1565_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; uint8_t v___x_1546_; 
v___x_1545_ = lean_array_get_size(v_ks_1540_);
v___x_1546_ = lean_nat_dec_lt(v_x_1537_, v___x_1545_);
if (v___x_1546_ == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; 
lean_dec(v_x_1537_);
v___x_1547_ = lean_array_push(v_ks_1540_, v_x_1538_);
v___x_1548_ = lean_array_push(v_vs_1541_, v_x_1539_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___x_1548_);
lean_ctor_set(v___x_1543_, 0, v___x_1547_);
v___x_1550_ = v___x_1543_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1547_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
else
{
lean_object* v_k_x27_1552_; uint8_t v___x_1553_; 
v_k_x27_1552_ = lean_array_fget_borrowed(v_ks_1540_, v_x_1537_);
v___x_1553_ = l_Lean_instBEqMVarId_beq(v_x_1538_, v_k_x27_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1555_; 
if (v_isShared_1544_ == 0)
{
v___x_1555_ = v___x_1543_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_ks_1540_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_vs_1541_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(1u);
v___x_1557_ = lean_nat_add(v_x_1537_, v___x_1556_);
lean_dec(v_x_1537_);
v_x_1536_ = v___x_1555_;
v_x_1537_ = v___x_1557_;
goto _start;
}
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1563_; 
v___x_1560_ = lean_array_fset(v_ks_1540_, v_x_1537_, v_x_1538_);
v___x_1561_ = lean_array_fset(v_vs_1541_, v_x_1537_, v_x_1539_);
lean_dec(v_x_1537_);
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___x_1561_);
lean_ctor_set(v___x_1543_, 0, v___x_1560_);
v___x_1563_ = v___x_1543_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v___x_1560_);
lean_ctor_set(v_reuseFailAlloc_1564_, 1, v___x_1561_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_1566_, lean_object* v_k_1567_, lean_object* v_v_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = lean_unsigned_to_nat(0u);
v___x_1570_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_1566_, v___x_1569_, v_k_1567_, v_v_1568_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(lean_object* v_x_1572_, size_t v_x_1573_, size_t v_x_1574_, lean_object* v_x_1575_, lean_object* v_x_1576_){
_start:
{
if (lean_obj_tag(v_x_1572_) == 0)
{
lean_object* v_es_1577_; size_t v___x_1578_; size_t v___x_1579_; lean_object* v_j_1580_; lean_object* v___x_1581_; uint8_t v___x_1582_; 
v_es_1577_ = lean_ctor_get(v_x_1572_, 0);
v___x_1578_ = ((size_t)31ULL);
v___x_1579_ = lean_usize_land(v_x_1573_, v___x_1578_);
v_j_1580_ = lean_usize_to_nat(v___x_1579_);
v___x_1581_ = lean_array_get_size(v_es_1577_);
v___x_1582_ = lean_nat_dec_lt(v_j_1580_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_dec(v_j_1580_);
lean_dec(v_x_1576_);
lean_dec(v_x_1575_);
return v_x_1572_;
}
else
{
lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1621_; 
lean_inc_ref(v_es_1577_);
v_isSharedCheck_1621_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1621_ == 0)
{
lean_object* v_unused_1622_; 
v_unused_1622_ = lean_ctor_get(v_x_1572_, 0);
lean_dec(v_unused_1622_);
v___x_1584_ = v_x_1572_;
v_isShared_1585_ = v_isSharedCheck_1621_;
goto v_resetjp_1583_;
}
else
{
lean_dec(v_x_1572_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1621_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v_v_1586_; lean_object* v___x_1587_; lean_object* v_xs_x27_1588_; lean_object* v___y_1590_; 
v_v_1586_ = lean_array_fget(v_es_1577_, v_j_1580_);
v___x_1587_ = lean_box(0);
v_xs_x27_1588_ = lean_array_fset(v_es_1577_, v_j_1580_, v___x_1587_);
switch(lean_obj_tag(v_v_1586_))
{
case 0:
{
lean_object* v_key_1595_; lean_object* v_val_1596_; lean_object* v___x_1598_; uint8_t v_isShared_1599_; uint8_t v_isSharedCheck_1606_; 
v_key_1595_ = lean_ctor_get(v_v_1586_, 0);
v_val_1596_ = lean_ctor_get(v_v_1586_, 1);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_v_1586_);
if (v_isSharedCheck_1606_ == 0)
{
v___x_1598_ = v_v_1586_;
v_isShared_1599_ = v_isSharedCheck_1606_;
goto v_resetjp_1597_;
}
else
{
lean_inc(v_val_1596_);
lean_inc(v_key_1595_);
lean_dec(v_v_1586_);
v___x_1598_ = lean_box(0);
v_isShared_1599_ = v_isSharedCheck_1606_;
goto v_resetjp_1597_;
}
v_resetjp_1597_:
{
uint8_t v___x_1600_; 
v___x_1600_ = l_Lean_instBEqMVarId_beq(v_x_1575_, v_key_1595_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; lean_object* v___x_1602_; 
lean_del_object(v___x_1598_);
v___x_1601_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1595_, v_val_1596_, v_x_1575_, v_x_1576_);
v___x_1602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1602_, 0, v___x_1601_);
v___y_1590_ = v___x_1602_;
goto v___jp_1589_;
}
else
{
lean_object* v___x_1604_; 
lean_dec(v_val_1596_);
lean_dec(v_key_1595_);
if (v_isShared_1599_ == 0)
{
lean_ctor_set(v___x_1598_, 1, v_x_1576_);
lean_ctor_set(v___x_1598_, 0, v_x_1575_);
v___x_1604_ = v___x_1598_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_x_1575_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_x_1576_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
v___y_1590_ = v___x_1604_;
goto v___jp_1589_;
}
}
}
}
case 1:
{
lean_object* v_node_1607_; lean_object* v___x_1609_; uint8_t v_isShared_1610_; uint8_t v_isSharedCheck_1619_; 
v_node_1607_ = lean_ctor_get(v_v_1586_, 0);
v_isSharedCheck_1619_ = !lean_is_exclusive(v_v_1586_);
if (v_isSharedCheck_1619_ == 0)
{
v___x_1609_ = v_v_1586_;
v_isShared_1610_ = v_isSharedCheck_1619_;
goto v_resetjp_1608_;
}
else
{
lean_inc(v_node_1607_);
lean_dec(v_v_1586_);
v___x_1609_ = lean_box(0);
v_isShared_1610_ = v_isSharedCheck_1619_;
goto v_resetjp_1608_;
}
v_resetjp_1608_:
{
size_t v___x_1611_; size_t v___x_1612_; size_t v___x_1613_; size_t v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1611_ = ((size_t)5ULL);
v___x_1612_ = lean_usize_shift_right(v_x_1573_, v___x_1611_);
v___x_1613_ = ((size_t)1ULL);
v___x_1614_ = lean_usize_add(v_x_1574_, v___x_1613_);
v___x_1615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_node_1607_, v___x_1612_, v___x_1614_, v_x_1575_, v_x_1576_);
if (v_isShared_1610_ == 0)
{
lean_ctor_set(v___x_1609_, 0, v___x_1615_);
v___x_1617_ = v___x_1609_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
v___y_1590_ = v___x_1617_;
goto v___jp_1589_;
}
}
}
default: 
{
lean_object* v___x_1620_; 
v___x_1620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1620_, 0, v_x_1575_);
lean_ctor_set(v___x_1620_, 1, v_x_1576_);
v___y_1590_ = v___x_1620_;
goto v___jp_1589_;
}
}
v___jp_1589_:
{
lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1591_ = lean_array_fset(v_xs_x27_1588_, v_j_1580_, v___y_1590_);
lean_dec(v_j_1580_);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 0, v___x_1591_);
v___x_1593_ = v___x_1584_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
else
{
lean_object* v_ks_1623_; lean_object* v_vs_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1642_; 
v_ks_1623_ = lean_ctor_get(v_x_1572_, 0);
v_vs_1624_ = lean_ctor_get(v_x_1572_, 1);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_x_1572_);
if (v_isSharedCheck_1642_ == 0)
{
v___x_1626_ = v_x_1572_;
v_isShared_1627_ = v_isSharedCheck_1642_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_vs_1624_);
lean_inc(v_ks_1623_);
lean_dec(v_x_1572_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1642_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_ks_1623_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_vs_1624_);
v___x_1629_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
lean_object* v_newNode_1630_; size_t v___x_1631_; uint8_t v___x_1632_; 
v_newNode_1630_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v___x_1629_, v_x_1575_, v_x_1576_);
v___x_1631_ = ((size_t)7ULL);
v___x_1632_ = lean_usize_dec_le(v___x_1631_, v_x_1574_);
if (v___x_1632_ == 0)
{
lean_object* v___x_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1633_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1630_);
v___x_1634_ = lean_unsigned_to_nat(4u);
v___x_1635_ = lean_nat_dec_lt(v___x_1633_, v___x_1634_);
lean_dec(v___x_1633_);
if (v___x_1635_ == 0)
{
lean_object* v_ks_1636_; lean_object* v_vs_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v_ks_1636_ = lean_ctor_get(v_newNode_1630_, 0);
lean_inc_ref(v_ks_1636_);
v_vs_1637_ = lean_ctor_get(v_newNode_1630_, 1);
lean_inc_ref(v_vs_1637_);
lean_dec_ref(v_newNode_1630_);
v___x_1638_ = lean_unsigned_to_nat(0u);
v___x_1639_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_1640_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1574_, v_ks_1636_, v_vs_1637_, v___x_1638_, v___x_1639_);
lean_dec_ref(v_vs_1637_);
lean_dec_ref(v_ks_1636_);
return v___x_1640_;
}
else
{
return v_newNode_1630_;
}
}
else
{
return v_newNode_1630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_1643_, lean_object* v_keys_1644_, lean_object* v_vals_1645_, lean_object* v_i_1646_, lean_object* v_entries_1647_){
_start:
{
lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = lean_array_get_size(v_keys_1644_);
v___x_1649_ = lean_nat_dec_lt(v_i_1646_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_dec(v_i_1646_);
return v_entries_1647_;
}
else
{
lean_object* v_k_1650_; lean_object* v_v_1651_; uint64_t v___x_1652_; size_t v_h_1653_; size_t v___x_1654_; lean_object* v___x_1655_; size_t v___x_1656_; size_t v___x_1657_; size_t v___x_1658_; size_t v_h_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_k_1650_ = lean_array_fget_borrowed(v_keys_1644_, v_i_1646_);
v_v_1651_ = lean_array_fget_borrowed(v_vals_1645_, v_i_1646_);
v___x_1652_ = l_Lean_instHashableMVarId_hash(v_k_1650_);
v_h_1653_ = lean_uint64_to_usize(v___x_1652_);
v___x_1654_ = ((size_t)5ULL);
v___x_1655_ = lean_unsigned_to_nat(1u);
v___x_1656_ = ((size_t)1ULL);
v___x_1657_ = lean_usize_sub(v_depth_1643_, v___x_1656_);
v___x_1658_ = lean_usize_mul(v___x_1654_, v___x_1657_);
v_h_1659_ = lean_usize_shift_right(v_h_1653_, v___x_1658_);
v___x_1660_ = lean_nat_add(v_i_1646_, v___x_1655_);
lean_dec(v_i_1646_);
lean_inc(v_v_1651_);
lean_inc(v_k_1650_);
v___x_1661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_entries_1647_, v_h_1659_, v_depth_1643_, v_k_1650_, v_v_1651_);
v_i_1646_ = v___x_1660_;
v_entries_1647_ = v___x_1661_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1663_, lean_object* v_keys_1664_, lean_object* v_vals_1665_, lean_object* v_i_1666_, lean_object* v_entries_1667_){
_start:
{
size_t v_depth_boxed_1668_; lean_object* v_res_1669_; 
v_depth_boxed_1668_ = lean_unbox_usize(v_depth_1663_);
lean_dec(v_depth_1663_);
v_res_1669_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_1668_, v_keys_1664_, v_vals_1665_, v_i_1666_, v_entries_1667_);
lean_dec_ref(v_vals_1665_);
lean_dec_ref(v_keys_1664_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_){
_start:
{
size_t v_x_1971__boxed_1675_; size_t v_x_1972__boxed_1676_; lean_object* v_res_1677_; 
v_x_1971__boxed_1675_ = lean_unbox_usize(v_x_1671_);
lean_dec(v_x_1671_);
v_x_1972__boxed_1676_ = lean_unbox_usize(v_x_1672_);
lean_dec(v_x_1672_);
v_res_1677_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1670_, v_x_1971__boxed_1675_, v_x_1972__boxed_1676_, v_x_1673_, v_x_1674_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_){
_start:
{
uint64_t v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; lean_object* v___x_1684_; 
v___x_1681_ = l_Lean_instHashableMVarId_hash(v_x_1679_);
v___x_1682_ = lean_uint64_to_usize(v___x_1681_);
v___x_1683_ = ((size_t)1ULL);
v___x_1684_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1678_, v___x_1682_, v___x_1683_, v_x_1679_, v_x_1680_);
return v___x_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(lean_object* v_mvarId_1685_, lean_object* v_val_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v___x_1689_; lean_object* v_mctx_1690_; lean_object* v_cache_1691_; lean_object* v_zetaDeltaFVarIds_1692_; lean_object* v_postponed_1693_; lean_object* v_diag_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1723_; 
v___x_1689_ = lean_st_ref_take(v___y_1687_);
v_mctx_1690_ = lean_ctor_get(v___x_1689_, 0);
v_cache_1691_ = lean_ctor_get(v___x_1689_, 1);
v_zetaDeltaFVarIds_1692_ = lean_ctor_get(v___x_1689_, 2);
v_postponed_1693_ = lean_ctor_get(v___x_1689_, 3);
v_diag_1694_ = lean_ctor_get(v___x_1689_, 4);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1696_ = v___x_1689_;
v_isShared_1697_ = v_isSharedCheck_1723_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_diag_1694_);
lean_inc(v_postponed_1693_);
lean_inc(v_zetaDeltaFVarIds_1692_);
lean_inc(v_cache_1691_);
lean_inc(v_mctx_1690_);
lean_dec(v___x_1689_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1723_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v_depth_1698_; lean_object* v_levelAssignDepth_1699_; lean_object* v_lmvarCounter_1700_; lean_object* v_mvarCounter_1701_; lean_object* v_lDecls_1702_; lean_object* v_decls_1703_; lean_object* v_userNames_1704_; lean_object* v_lAssignment_1705_; lean_object* v_eAssignment_1706_; lean_object* v_dAssignment_1707_; lean_object* v_instanceTypedMVars_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1722_; 
v_depth_1698_ = lean_ctor_get(v_mctx_1690_, 0);
v_levelAssignDepth_1699_ = lean_ctor_get(v_mctx_1690_, 1);
v_lmvarCounter_1700_ = lean_ctor_get(v_mctx_1690_, 2);
v_mvarCounter_1701_ = lean_ctor_get(v_mctx_1690_, 3);
v_lDecls_1702_ = lean_ctor_get(v_mctx_1690_, 4);
v_decls_1703_ = lean_ctor_get(v_mctx_1690_, 5);
v_userNames_1704_ = lean_ctor_get(v_mctx_1690_, 6);
v_lAssignment_1705_ = lean_ctor_get(v_mctx_1690_, 7);
v_eAssignment_1706_ = lean_ctor_get(v_mctx_1690_, 8);
v_dAssignment_1707_ = lean_ctor_get(v_mctx_1690_, 9);
v_instanceTypedMVars_1708_ = lean_ctor_get(v_mctx_1690_, 10);
v_isSharedCheck_1722_ = !lean_is_exclusive(v_mctx_1690_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1710_ = v_mctx_1690_;
v_isShared_1711_ = v_isSharedCheck_1722_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_instanceTypedMVars_1708_);
lean_inc(v_dAssignment_1707_);
lean_inc(v_eAssignment_1706_);
lean_inc(v_lAssignment_1705_);
lean_inc(v_userNames_1704_);
lean_inc(v_decls_1703_);
lean_inc(v_lDecls_1702_);
lean_inc(v_mvarCounter_1701_);
lean_inc(v_lmvarCounter_1700_);
lean_inc(v_levelAssignDepth_1699_);
lean_inc(v_depth_1698_);
lean_dec(v_mctx_1690_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1722_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1715_; 
v___x_1712_ = lean_box(0);
v___x_1713_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_eAssignment_1706_, v_mvarId_1685_, v_val_1686_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 8, v___x_1713_);
v___x_1715_ = v___x_1710_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_depth_1698_);
lean_ctor_set(v_reuseFailAlloc_1721_, 1, v_levelAssignDepth_1699_);
lean_ctor_set(v_reuseFailAlloc_1721_, 2, v_lmvarCounter_1700_);
lean_ctor_set(v_reuseFailAlloc_1721_, 3, v_mvarCounter_1701_);
lean_ctor_set(v_reuseFailAlloc_1721_, 4, v_lDecls_1702_);
lean_ctor_set(v_reuseFailAlloc_1721_, 5, v_decls_1703_);
lean_ctor_set(v_reuseFailAlloc_1721_, 6, v_userNames_1704_);
lean_ctor_set(v_reuseFailAlloc_1721_, 7, v_lAssignment_1705_);
lean_ctor_set(v_reuseFailAlloc_1721_, 8, v___x_1713_);
lean_ctor_set(v_reuseFailAlloc_1721_, 9, v_dAssignment_1707_);
lean_ctor_set(v_reuseFailAlloc_1721_, 10, v_instanceTypedMVars_1708_);
v___x_1715_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
lean_object* v___x_1717_; 
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1715_);
v___x_1717_ = v___x_1696_;
goto v_reusejp_1716_;
}
else
{
lean_object* v_reuseFailAlloc_1720_; 
v_reuseFailAlloc_1720_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1720_, 0, v___x_1715_);
lean_ctor_set(v_reuseFailAlloc_1720_, 1, v_cache_1691_);
lean_ctor_set(v_reuseFailAlloc_1720_, 2, v_zetaDeltaFVarIds_1692_);
lean_ctor_set(v_reuseFailAlloc_1720_, 3, v_postponed_1693_);
lean_ctor_set(v_reuseFailAlloc_1720_, 4, v_diag_1694_);
v___x_1717_ = v_reuseFailAlloc_1720_;
goto v_reusejp_1716_;
}
v_reusejp_1716_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
v___x_1718_ = lean_st_ref_put(v___y_1687_, v___x_1717_);
v___x_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1719_, 0, v___x_1712_);
return v___x_1719_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg___boxed(lean_object* v_mvarId_1724_, lean_object* v_val_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v_res_1728_; 
v_res_1728_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1724_, v_val_1725_, v___y_1726_);
lean_dec(v___y_1726_);
return v_res_1728_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(lean_object* v_as_1729_, size_t v_i_1730_, size_t v_stop_1731_, lean_object* v_b_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_){
_start:
{
uint8_t v___x_1738_; 
v___x_1738_ = lean_usize_dec_eq(v_i_1730_, v_stop_1731_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
v___x_1739_ = lean_array_uget_borrowed(v_as_1729_, v_i_1730_);
lean_inc(v___x_1739_);
v___x_1740_ = l_Lean_MVarId_getDecl(v___x_1739_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1740_) == 0)
{
lean_object* v_a_1741_; lean_object* v_type_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v_a_1741_ = lean_ctor_get(v___x_1740_, 0);
lean_inc(v_a_1741_);
lean_dec_ref_known(v___x_1740_, 1);
v_type_1742_ = lean_ctor_get(v_a_1741_, 2);
lean_inc_ref(v_type_1742_);
lean_dec(v_a_1741_);
v___x_1743_ = lean_box(0);
v___x_1744_ = l_Lean_Meta_synthInstance(v_type_1742_, v___x_1743_, v___y_1733_, v___y_1734_, v___y_1735_, v___y_1736_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_a_1745_; lean_object* v___x_1746_; 
v_a_1745_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_a_1745_);
lean_dec_ref_known(v___x_1744_, 1);
lean_inc(v___x_1739_);
v___x_1746_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v___x_1739_, v_a_1745_, v___y_1734_);
if (lean_obj_tag(v___x_1746_) == 0)
{
lean_object* v_a_1747_; size_t v___x_1748_; size_t v___x_1749_; 
v_a_1747_ = lean_ctor_get(v___x_1746_, 0);
lean_inc(v_a_1747_);
lean_dec_ref_known(v___x_1746_, 1);
v___x_1748_ = ((size_t)1ULL);
v___x_1749_ = lean_usize_add(v_i_1730_, v___x_1748_);
v_i_1730_ = v___x_1749_;
v_b_1732_ = v_a_1747_;
goto _start;
}
else
{
return v___x_1746_;
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
v_a_1751_ = lean_ctor_get(v___x_1744_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1744_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1744_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1744_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
v_a_1759_ = lean_ctor_get(v___x_1740_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1740_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1740_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1740_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
else
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_b_1732_);
return v___x_1767_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2___boxed(lean_object* v_as_1768_, lean_object* v_i_1769_, lean_object* v_stop_1770_, lean_object* v_b_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
size_t v_i_boxed_1777_; size_t v_stop_boxed_1778_; lean_object* v_res_1779_; 
v_i_boxed_1777_ = lean_unbox_usize(v_i_1769_);
lean_dec(v_i_1769_);
v_stop_boxed_1778_ = lean_unbox_usize(v_stop_1770_);
lean_dec(v_stop_1770_);
v_res_1779_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_as_1768_, v_i_boxed_1777_, v_stop_boxed_1778_, v_b_1771_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
lean_dec(v___y_1775_);
lean_dec_ref(v___y_1774_);
lean_dec(v___y_1773_);
lean_dec_ref(v___y_1772_);
lean_dec_ref(v_as_1768_);
return v_res_1779_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2(void){
_start:
{
lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1783_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__1));
v___x_1784_ = l_Lean_MessageData_ofFormat(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(lean_object* v_methodName_1785_, lean_object* v_f_1786_, lean_object* v_args_1787_, lean_object* v_instMVars_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v___y_1829_; lean_object* v___x_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v___x_1838_ = lean_unsigned_to_nat(0u);
v___x_1839_ = lean_array_get_size(v_instMVars_1788_);
v___x_1840_ = lean_nat_dec_lt(v___x_1838_, v___x_1839_);
if (v___x_1840_ == 0)
{
goto v___jp_1794_;
}
else
{
lean_object* v___x_1841_; uint8_t v___x_1842_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = lean_nat_dec_le(v___x_1839_, v___x_1839_);
if (v___x_1842_ == 0)
{
if (v___x_1840_ == 0)
{
goto v___jp_1794_;
}
else
{
size_t v___x_1843_; size_t v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = ((size_t)0ULL);
v___x_1844_ = lean_usize_of_nat(v___x_1839_);
v___x_1845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1788_, v___x_1843_, v___x_1844_, v___x_1841_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
v___y_1829_ = v___x_1845_;
goto v___jp_1828_;
}
}
else
{
size_t v___x_1846_; size_t v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = ((size_t)0ULL);
v___x_1847_ = lean_usize_of_nat(v___x_1839_);
v___x_1848_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__2(v_instMVars_1788_, v___x_1846_, v___x_1847_, v___x_1841_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
v___y_1829_ = v___x_1848_;
goto v___jp_1828_;
}
}
v___jp_1794_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v_a_1797_; lean_object* v___x_1798_; 
v___x_1795_ = l_Lean_mkAppN(v_f_1786_, v_args_1787_);
v___x_1796_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__1___redArg(v___x_1795_, v_a_1790_);
v_a_1797_ = lean_ctor_get(v___x_1796_, 0);
lean_inc_n(v_a_1797_, 2);
lean_dec_ref(v___x_1796_);
v___x_1798_ = l_Lean_Meta_hasAssignableMVar(v_a_1797_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1819_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1819_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1819_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_unbox(v_a_1799_);
lean_dec(v_a_1799_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1805_; 
lean_dec(v_methodName_1785_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v_a_1797_);
v___x_1805_ = v___x_1801_;
goto v_reusejp_1804_;
}
else
{
lean_object* v_reuseFailAlloc_1806_; 
v_reuseFailAlloc_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1806_, 0, v_a_1797_);
v___x_1805_ = v_reuseFailAlloc_1806_;
goto v_reusejp_1804_;
}
v_reusejp_1804_:
{
return v___x_1805_;
}
}
else
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v_a_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1818_; 
lean_del_object(v___x_1801_);
v___x_1807_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___closed__2);
v___x_1808_ = l_Lean_indentExpr(v_a_1797_);
v___x_1809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1809_, 0, v___x_1807_);
lean_ctor_set(v___x_1809_, 1, v___x_1808_);
v___x_1810_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v_methodName_1785_, v___x_1809_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
v_a_1811_ = lean_ctor_get(v___x_1810_, 0);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1818_ == 0)
{
v___x_1813_ = v___x_1810_;
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_a_1811_);
lean_dec(v___x_1810_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1818_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v___x_1816_; 
if (v_isShared_1814_ == 0)
{
v___x_1816_ = v___x_1813_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_a_1811_);
v___x_1816_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
return v___x_1816_;
}
}
}
}
}
else
{
lean_object* v_a_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1827_; 
lean_dec(v_a_1797_);
lean_dec(v_methodName_1785_);
v_a_1820_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1827_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1827_ == 0)
{
v___x_1822_ = v___x_1798_;
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_a_1820_);
lean_dec(v___x_1798_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1827_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1825_; 
if (v_isShared_1823_ == 0)
{
v___x_1825_ = v___x_1822_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v_a_1820_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
}
v___jp_1828_:
{
if (lean_obj_tag(v___y_1829_) == 0)
{
lean_dec_ref_known(v___y_1829_, 1);
goto v___jp_1794_;
}
else
{
lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1837_; 
lean_dec_ref(v_f_1786_);
lean_dec(v_methodName_1785_);
v_a_1830_ = lean_ctor_get(v___y_1829_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___y_1829_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1832_ = v___y_1829_;
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___y_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1837_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1835_; 
if (v_isShared_1833_ == 0)
{
v___x_1835_ = v___x_1832_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v_a_1830_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal___boxed(lean_object* v_methodName_1849_, lean_object* v_f_1850_, lean_object* v_args_1851_, lean_object* v_instMVars_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_, lean_object* v_a_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v_methodName_1849_, v_f_1850_, v_args_1851_, v_instMVars_1852_, v_a_1853_, v_a_1854_, v_a_1855_, v_a_1856_);
lean_dec(v_a_1856_);
lean_dec_ref(v_a_1855_);
lean_dec(v_a_1854_);
lean_dec_ref(v_a_1853_);
lean_dec_ref(v_instMVars_1852_);
lean_dec_ref(v_args_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(lean_object* v_mvarId_1859_, lean_object* v_val_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v___x_1866_; 
v___x_1866_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___redArg(v_mvarId_1859_, v_val_1860_, v___y_1862_);
return v___x_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0___boxed(lean_object* v_mvarId_1867_, lean_object* v_val_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0(v_mvarId_1867_, v_val_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_);
lean_dec(v___y_1872_);
lean_dec_ref(v___y_1871_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0(lean_object* v_00_u03b2_1875_, lean_object* v_x_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0___redArg(v_x_1876_, v_x_1877_, v_x_1878_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_1880_, lean_object* v_x_1881_, size_t v_x_1882_, size_t v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_){
_start:
{
lean_object* v___x_1886_; 
v___x_1886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___redArg(v_x_1881_, v_x_1882_, v_x_1883_, v_x_1884_, v_x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_1887_, lean_object* v_x_1888_, lean_object* v_x_1889_, lean_object* v_x_1890_, lean_object* v_x_1891_, lean_object* v_x_1892_){
_start:
{
size_t v_x_2411__boxed_1893_; size_t v_x_2412__boxed_1894_; lean_object* v_res_1895_; 
v_x_2411__boxed_1893_ = lean_unbox_usize(v_x_1889_);
lean_dec(v_x_1889_);
v_x_2412__boxed_1894_ = lean_unbox_usize(v_x_1890_);
lean_dec(v_x_1890_);
v_res_1895_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2(v_00_u03b2_1887_, v_x_1888_, v_x_2411__boxed_1893_, v_x_2412__boxed_1894_, v_x_1891_, v_x_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_1896_, lean_object* v_n_1897_, lean_object* v_k_1898_, lean_object* v_v_1899_){
_start:
{
lean_object* v___x_1900_; 
v___x_1900_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1897_, v_k_1898_, v_v_1899_);
return v___x_1900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_1901_, size_t v_depth_1902_, lean_object* v_keys_1903_, lean_object* v_vals_1904_, lean_object* v_heq_1905_, lean_object* v_i_1906_, lean_object* v_entries_1907_){
_start:
{
lean_object* v___x_1908_; 
v___x_1908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1902_, v_keys_1903_, v_vals_1904_, v_i_1906_, v_entries_1907_);
return v___x_1908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1909_, lean_object* v_depth_1910_, lean_object* v_keys_1911_, lean_object* v_vals_1912_, lean_object* v_heq_1913_, lean_object* v_i_1914_, lean_object* v_entries_1915_){
_start:
{
size_t v_depth_boxed_1916_; lean_object* v_res_1917_; 
v_depth_boxed_1916_ = lean_unbox_usize(v_depth_1910_);
lean_dec(v_depth_1910_);
v_res_1917_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1909_, v_depth_boxed_1916_, v_keys_1911_, v_vals_1912_, v_heq_1913_, v_i_1914_, v_entries_1915_);
lean_dec_ref(v_vals_1912_);
lean_dec_ref(v_keys_1911_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1918_, lean_object* v_x_1919_, lean_object* v_x_1920_, lean_object* v_x_1921_, lean_object* v_x_1922_){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1919_, v_x_1920_, v_x_1921_, v_x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__2));
v___x_1929_ = l_Lean_stringToMessageData(v___x_1928_);
return v___x_1929_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5(void){
_start:
{
lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1931_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__4));
v___x_1932_ = l_Lean_stringToMessageData(v___x_1931_);
return v___x_1932_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; 
v___x_1936_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__7));
v___x_1937_ = l_Lean_MessageData_ofFormat(v___x_1936_);
return v___x_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(lean_object* v_f_1938_, lean_object* v_xs_1939_, lean_object* v_type_1940_, lean_object* v_i_1941_, lean_object* v_j_1942_, lean_object* v_args_1943_, lean_object* v_instMVars_1944_, lean_object* v_a_1945_, lean_object* v_a_1946_, lean_object* v_a_1947_, lean_object* v_a_1948_){
_start:
{
lean_object* v___x_1950_; uint8_t v___x_1951_; 
v___x_1950_ = lean_array_get_size(v_xs_1939_);
v___x_1951_ = lean_nat_dec_le(v___x_1950_, v_i_1941_);
if (v___x_1951_ == 0)
{
if (lean_obj_tag(v_type_1940_) == 7)
{
lean_object* v_binderName_1952_; lean_object* v_binderType_1953_; lean_object* v_body_1954_; uint8_t v_binderInfo_1955_; lean_object* v___x_1956_; lean_object* v_d_1957_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1962_; 
v_binderName_1952_ = lean_ctor_get(v_type_1940_, 0);
lean_inc(v_binderName_1952_);
v_binderType_1953_ = lean_ctor_get(v_type_1940_, 1);
lean_inc_ref(v_binderType_1953_);
v_body_1954_ = lean_ctor_get(v_type_1940_, 2);
lean_inc_ref(v_body_1954_);
v_binderInfo_1955_ = lean_ctor_get_uint8(v_type_1940_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_type_1940_, 3);
v___x_1956_ = lean_array_get_size(v_args_1943_);
v_d_1957_ = lean_expr_instantiate_rev_range(v_binderType_1953_, v_j_1942_, v___x_1956_, v_args_1943_);
lean_dec_ref(v_binderType_1953_);
switch(v_binderInfo_1955_)
{
case 1:
{
v___y_1959_ = v_a_1945_;
v___y_1960_ = v_a_1946_;
v___y_1961_ = v_a_1947_;
v___y_1962_ = v_a_1948_;
goto v___jp_1958_;
}
case 2:
{
v___y_1959_ = v_a_1945_;
v___y_1960_ = v_a_1946_;
v___y_1961_ = v_a_1947_;
v___y_1962_ = v_a_1948_;
goto v___jp_1958_;
}
case 3:
{
lean_object* v___x_1969_; uint8_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_d_1957_);
v___x_1970_ = 1;
v___x_1971_ = l_Lean_Meta_mkFreshExprMVar(v___x_1969_, v___x_1970_, v_binderName_1952_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc_n(v_a_1972_, 2);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = lean_array_push(v_args_1943_, v_a_1972_);
v___x_1974_ = l_Lean_Expr_mvarId_x21(v_a_1972_);
lean_dec(v_a_1972_);
v___x_1975_ = lean_array_push(v_instMVars_1944_, v___x_1974_);
v_type_1940_ = v_body_1954_;
v_args_1943_ = v___x_1973_;
v_instMVars_1944_ = v___x_1975_;
goto _start;
}
else
{
lean_dec_ref(v_body_1954_);
lean_dec_ref(v_instMVars_1944_);
lean_dec_ref(v_args_1943_);
lean_dec(v_j_1942_);
lean_dec(v_i_1941_);
lean_dec_ref(v_f_1938_);
return v___x_1971_;
}
}
default: 
{
lean_object* v_x_1977_; lean_object* v___y_1979_; lean_object* v___x_1996_; 
lean_dec(v_binderName_1952_);
v_x_1977_ = lean_array_fget_borrowed(v_xs_1939_, v_i_1941_);
lean_inc(v_a_1948_);
lean_inc_ref(v_a_1947_);
lean_inc(v_a_1946_);
lean_inc_ref(v_a_1945_);
lean_inc(v_x_1977_);
v___x_1996_ = lean_infer_type(v_x_1977_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; uint8_t v_transparency_1999_; uint8_t v___x_2000_; uint8_t v___x_2001_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l_Lean_Meta_Context_config(v_a_1945_);
v_transparency_1999_ = lean_ctor_get_uint8(v___x_1998_, 9);
lean_dec_ref(v___x_1998_);
v___x_2000_ = 1;
v___x_2001_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_1999_, v___x_2000_);
if (v___x_2001_ == 0)
{
lean_object* v___x_2002_; 
v___x_2002_ = l_Lean_Meta_isExprDefEq(v_d_1957_, v_a_1997_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
v___y_1979_ = v___x_2002_;
goto v___jp_1978_;
}
else
{
lean_object* v_keyedConfig_2003_; uint8_t v_trackZetaDelta_2004_; lean_object* v_zetaDeltaSet_2005_; lean_object* v_lctx_2006_; lean_object* v_localInstances_2007_; lean_object* v_defEqCtx_x3f_2008_; lean_object* v_synthPendingDepth_2009_; lean_object* v_customCanUnfoldPredicate_x3f_2010_; uint8_t v_univApprox_2011_; uint8_t v_inTypeClassResolution_2012_; uint8_t v_cacheInferType_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_keyedConfig_2003_ = lean_ctor_get(v_a_1945_, 0);
v_trackZetaDelta_2004_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7);
v_zetaDeltaSet_2005_ = lean_ctor_get(v_a_1945_, 1);
v_lctx_2006_ = lean_ctor_get(v_a_1945_, 2);
v_localInstances_2007_ = lean_ctor_get(v_a_1945_, 3);
v_defEqCtx_x3f_2008_ = lean_ctor_get(v_a_1945_, 4);
v_synthPendingDepth_2009_ = lean_ctor_get(v_a_1945_, 5);
v_customCanUnfoldPredicate_x3f_2010_ = lean_ctor_get(v_a_1945_, 6);
v_univApprox_2011_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2012_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7 + 2);
v_cacheInferType_2013_ = lean_ctor_get_uint8(v_a_1945_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2003_);
v___x_2014_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2000_, v_keyedConfig_2003_);
lean_inc(v_customCanUnfoldPredicate_x3f_2010_);
lean_inc(v_synthPendingDepth_2009_);
lean_inc(v_defEqCtx_x3f_2008_);
lean_inc_ref(v_localInstances_2007_);
lean_inc_ref(v_lctx_2006_);
lean_inc(v_zetaDeltaSet_2005_);
v___x_2015_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2015_, 0, v___x_2014_);
lean_ctor_set(v___x_2015_, 1, v_zetaDeltaSet_2005_);
lean_ctor_set(v___x_2015_, 2, v_lctx_2006_);
lean_ctor_set(v___x_2015_, 3, v_localInstances_2007_);
lean_ctor_set(v___x_2015_, 4, v_defEqCtx_x3f_2008_);
lean_ctor_set(v___x_2015_, 5, v_synthPendingDepth_2009_);
lean_ctor_set(v___x_2015_, 6, v_customCanUnfoldPredicate_x3f_2010_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7, v_trackZetaDelta_2004_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7 + 1, v_univApprox_2011_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2012_);
lean_ctor_set_uint8(v___x_2015_, sizeof(void*)*7 + 3, v_cacheInferType_2013_);
v___x_2016_ = l_Lean_Meta_isExprDefEq(v_d_1957_, v_a_1997_, v___x_2015_, v_a_1946_, v_a_1947_, v_a_1948_);
lean_dec_ref_known(v___x_2015_, 7);
v___y_1979_ = v___x_2016_;
goto v___jp_1978_;
}
}
else
{
lean_dec_ref(v_d_1957_);
lean_dec_ref(v_body_1954_);
lean_dec_ref(v_instMVars_1944_);
lean_dec_ref(v_args_1943_);
lean_dec(v_j_1942_);
lean_dec(v_i_1941_);
lean_dec_ref(v_f_1938_);
return v___x_1996_;
}
v___jp_1978_:
{
if (lean_obj_tag(v___y_1979_) == 0)
{
lean_object* v_a_1980_; uint8_t v___x_1981_; 
v_a_1980_ = lean_ctor_get(v___y_1979_, 0);
lean_inc(v_a_1980_);
lean_dec_ref_known(v___y_1979_, 1);
v___x_1981_ = lean_unbox(v_a_1980_);
lean_dec(v_a_1980_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
lean_dec_ref(v_body_1954_);
lean_dec_ref(v_instMVars_1944_);
lean_dec(v_j_1942_);
lean_dec(v_i_1941_);
v___x_1982_ = l_Lean_mkAppN(v_f_1938_, v_args_1943_);
lean_dec_ref(v_args_1943_);
lean_inc(v_x_1977_);
v___x_1983_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_1982_, v_x_1977_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_1983_;
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = lean_unsigned_to_nat(1u);
v___x_1985_ = lean_nat_add(v_i_1941_, v___x_1984_);
lean_dec(v_i_1941_);
lean_inc(v_x_1977_);
v___x_1986_ = lean_array_push(v_args_1943_, v_x_1977_);
v_type_1940_ = v_body_1954_;
v_i_1941_ = v___x_1985_;
v_args_1943_ = v___x_1986_;
goto _start;
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_body_1954_);
lean_dec_ref(v_instMVars_1944_);
lean_dec_ref(v_args_1943_);
lean_dec(v_j_1942_);
lean_dec(v_i_1941_);
lean_dec_ref(v_f_1938_);
v_a_1988_ = lean_ctor_get(v___y_1979_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___y_1979_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___y_1979_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___y_1979_);
v___x_1990_ = lean_box(0);
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
v_resetjp_1989_:
{
lean_object* v___x_1993_; 
if (v_isShared_1991_ == 0)
{
v___x_1993_ = v___x_1990_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v_a_1988_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
return v___x_1993_;
}
}
}
}
}
}
v___jp_1958_:
{
lean_object* v___x_1963_; uint8_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1963_, 0, v_d_1957_);
v___x_1964_ = 0;
v___x_1965_ = l_Lean_Meta_mkFreshExprMVar(v___x_1963_, v___x_1964_, v_binderName_1952_, v___y_1959_, v___y_1960_, v___y_1961_, v___y_1962_);
if (lean_obj_tag(v___x_1965_) == 0)
{
lean_object* v_a_1966_; lean_object* v___x_1967_; 
v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1965_, 1);
v___x_1967_ = lean_array_push(v_args_1943_, v_a_1966_);
v_type_1940_ = v_body_1954_;
v_args_1943_ = v___x_1967_;
v_a_1945_ = v___y_1959_;
v_a_1946_ = v___y_1960_;
v_a_1947_ = v___y_1961_;
v_a_1948_ = v___y_1962_;
goto _start;
}
else
{
lean_dec_ref(v_body_1954_);
lean_dec_ref(v_instMVars_1944_);
lean_dec_ref(v_args_1943_);
lean_dec(v_j_1942_);
lean_dec(v_i_1941_);
lean_dec_ref(v_f_1938_);
return v___x_1965_;
}
}
}
else
{
lean_object* v___x_2017_; lean_object* v_type_2018_; lean_object* v___x_2019_; 
v___x_2017_ = lean_array_get_size(v_args_1943_);
v_type_2018_ = lean_expr_instantiate_rev_range(v_type_1940_, v_j_1942_, v___x_2017_, v_args_1943_);
lean_dec(v_j_1942_);
lean_dec_ref(v_type_1940_);
v___x_2019_ = l_Lean_Meta_whnfD(v_type_2018_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v_a_2020_; uint8_t v___x_2021_; 
v_a_2020_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2020_);
lean_dec_ref_known(v___x_2019_, 1);
v___x_2021_ = l_Lean_Expr_isForall(v_a_2020_);
if (v___x_2021_ == 0)
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
lean_dec(v_a_2020_);
lean_dec_ref(v_instMVars_1944_);
lean_dec_ref(v_args_1943_);
lean_dec(v_i_1941_);
v___x_2022_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2023_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__3);
v___x_2024_ = l_Lean_indentExpr(v_f_1938_);
v___x_2025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2023_);
lean_ctor_set(v___x_2025_, 1, v___x_2024_);
v___x_2026_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__5);
v___x_2027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2027_, 0, v___x_2025_);
lean_ctor_set(v___x_2027_, 1, v___x_2026_);
v___x_2028_ = lean_unsigned_to_nat(0u);
v___x_2029_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_2030_ = l_Lean_MessageData_arrayExpr_toMessageData(v_xs_1939_, v___x_2028_, v___x_2029_);
v___x_2031_ = l_Lean_indentD(v___x_2030_);
v___x_2032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2027_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
v___x_2033_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_2022_, v___x_2032_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
return v___x_2033_;
}
else
{
v_type_1940_ = v_a_2020_;
v_j_1942_ = v___x_2017_;
goto _start;
}
}
else
{
lean_dec_ref(v_instMVars_1944_);
lean_dec_ref(v_args_1943_);
lean_dec(v_i_1941_);
lean_dec_ref(v_f_1938_);
return v___x_2019_;
}
}
}
else
{
lean_object* v___x_2035_; lean_object* v___x_2036_; 
lean_dec(v_j_1942_);
lean_dec(v_i_1941_);
lean_dec_ref(v_type_1940_);
v___x_2035_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__1));
v___x_2036_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_2035_, v_f_1938_, v_args_1943_, v_instMVars_1944_, v_a_1945_, v_a_1946_, v_a_1947_, v_a_1948_);
lean_dec_ref(v_instMVars_1944_);
lean_dec_ref(v_args_1943_);
return v___x_2036_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___boxed(lean_object* v_f_2037_, lean_object* v_xs_2038_, lean_object* v_type_2039_, lean_object* v_i_2040_, lean_object* v_j_2041_, lean_object* v_args_2042_, lean_object* v_instMVars_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2037_, v_xs_2038_, v_type_2039_, v_i_2040_, v_j_2041_, v_args_2042_, v_instMVars_2043_, v_a_2044_, v_a_2045_, v_a_2046_, v_a_2047_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
lean_dec(v_a_2045_);
lean_dec_ref(v_a_2044_);
lean_dec_ref(v_xs_2038_);
return v_res_2049_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(lean_object* v_f_2052_, lean_object* v_fType_2053_, lean_object* v_xs_2054_, lean_object* v_a_2055_, lean_object* v_a_2056_, lean_object* v_a_2057_, lean_object* v_a_2058_){
_start:
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; 
v___x_2060_ = lean_unsigned_to_nat(0u);
v___x_2061_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_2062_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop(v_f_2052_, v_xs_2054_, v_fType_2053_, v___x_2060_, v___x_2060_, v___x_2061_, v___x_2061_, v_a_2055_, v_a_2056_, v_a_2057_, v_a_2058_);
return v___x_2062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed(lean_object* v_f_2063_, lean_object* v_fType_2064_, lean_object* v_xs_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_f_2063_, v_fType_2064_, v_xs_2065_, v_a_2066_, v_a_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
lean_dec(v_a_2067_);
lean_dec_ref(v_a_2066_);
lean_dec_ref(v_xs_2065_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(lean_object* v_x_2072_, lean_object* v_x_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
if (lean_obj_tag(v_x_2072_) == 0)
{
lean_object* v___x_2079_; lean_object* v___x_2080_; 
v___x_2079_ = l_List_reverse___redArg(v_x_2073_);
v___x_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
return v___x_2080_;
}
else
{
lean_object* v_tail_2081_; lean_object* v___x_2083_; uint8_t v_isShared_2084_; uint8_t v_isSharedCheck_2099_; 
v_tail_2081_ = lean_ctor_get(v_x_2072_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_x_2072_);
if (v_isSharedCheck_2099_ == 0)
{
lean_object* v_unused_2100_; 
v_unused_2100_ = lean_ctor_get(v_x_2072_, 0);
lean_dec(v_unused_2100_);
v___x_2083_ = v_x_2072_;
v_isShared_2084_ = v_isSharedCheck_2099_;
goto v_resetjp_2082_;
}
else
{
lean_inc(v_tail_2081_);
lean_dec(v_x_2072_);
v___x_2083_ = lean_box(0);
v_isShared_2084_ = v_isSharedCheck_2099_;
goto v_resetjp_2082_;
}
v_resetjp_2082_:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lean_Meta_mkFreshLevelMVar(v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
lean_inc(v_a_2086_);
lean_dec_ref_known(v___x_2085_, 1);
if (v_isShared_2084_ == 0)
{
lean_ctor_set(v___x_2083_, 1, v_x_2073_);
lean_ctor_set(v___x_2083_, 0, v_a_2086_);
v___x_2088_ = v___x_2083_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2086_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v_x_2073_);
v___x_2088_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v_x_2072_ = v_tail_2081_;
v_x_2073_ = v___x_2088_;
goto _start;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_del_object(v___x_2083_);
lean_dec(v_tail_2081_);
lean_dec(v_x_2073_);
v_a_2091_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2085_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2085_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1___boxed(lean_object* v_x_2101_, lean_object* v_x_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_x_2101_, v_x_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
lean_dec(v___y_2104_);
lean_dec_ref(v___y_2103_);
return v_res_2108_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_2109_; 
v___x_2109_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_2109_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_2111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
return v___x_2111_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2113_ = lean_unsigned_to_nat(0u);
v___x_2114_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2113_);
lean_ctor_set(v___x_2114_, 1, v___x_2113_);
lean_ctor_set(v___x_2114_, 2, v___x_2113_);
lean_ctor_set(v___x_2114_, 3, v___x_2113_);
lean_ctor_set(v___x_2114_, 4, v___x_2112_);
lean_ctor_set(v___x_2114_, 5, v___x_2112_);
lean_ctor_set(v___x_2114_, 6, v___x_2112_);
lean_ctor_set(v___x_2114_, 7, v___x_2112_);
lean_ctor_set(v___x_2114_, 8, v___x_2112_);
lean_ctor_set(v___x_2114_, 9, v___x_2112_);
lean_ctor_set(v___x_2114_, 10, v___x_2112_);
return v___x_2114_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
v___x_2115_ = lean_unsigned_to_nat(32u);
v___x_2116_ = lean_mk_empty_array_with_capacity(v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
return v___x_2117_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2118_ = ((size_t)5ULL);
v___x_2119_ = lean_unsigned_to_nat(0u);
v___x_2120_ = lean_unsigned_to_nat(32u);
v___x_2121_ = lean_mk_empty_array_with_capacity(v___x_2120_);
v___x_2122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_2123_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2123_, 0, v___x_2122_);
lean_ctor_set(v___x_2123_, 1, v___x_2121_);
lean_ctor_set(v___x_2123_, 2, v___x_2119_);
lean_ctor_set(v___x_2123_, 3, v___x_2119_);
lean_ctor_set_usize(v___x_2123_, 4, v___x_2118_);
return v___x_2123_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2124_ = lean_box(1);
v___x_2125_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_2126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_2127_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2127_, 0, v___x_2126_);
lean_ctor_set(v___x_2127_, 1, v___x_2125_);
lean_ctor_set(v___x_2127_, 2, v___x_2124_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2129_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_2130_ = l_Lean_stringToMessageData(v___x_2129_);
return v___x_2130_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; 
v___x_2132_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_2133_ = l_Lean_stringToMessageData(v___x_2132_);
return v___x_2133_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2135_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_2136_ = l_Lean_stringToMessageData(v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2138_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_2139_ = l_Lean_stringToMessageData(v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2141_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_2142_ = l_Lean_stringToMessageData(v___x_2141_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2144_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_2145_ = l_Lean_stringToMessageData(v___x_2144_);
return v___x_2145_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_2148_ = l_Lean_stringToMessageData(v___x_2147_);
return v___x_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_2149_, lean_object* v_declHint_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v_env_2155_; uint8_t v___x_2156_; 
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_st_ref_get(v___y_2151_);
v_env_2155_ = lean_ctor_get(v___x_2154_, 0);
lean_inc_ref(v_env_2155_);
lean_dec(v___x_2154_);
v___x_2156_ = l_Lean_Name_isAnonymous(v_declHint_2150_);
if (v___x_2156_ == 0)
{
uint8_t v_isExporting_2157_; 
v_isExporting_2157_ = lean_ctor_get_uint8(v_env_2155_, sizeof(void*)*8);
if (v_isExporting_2157_ == 0)
{
lean_object* v___x_2158_; 
lean_dec_ref(v_env_2155_);
lean_dec(v_declHint_2150_);
v___x_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2158_, 0, v_msg_2149_);
return v___x_2158_;
}
else
{
lean_object* v___x_2159_; uint8_t v___x_2160_; 
lean_inc_ref(v_env_2155_);
v___x_2159_ = l_Lean_Environment_setExporting(v_env_2155_, v___x_2156_);
lean_inc(v_declHint_2150_);
lean_inc_ref(v___x_2159_);
v___x_2160_ = l_Lean_Environment_contains(v___x_2159_, v_declHint_2150_, v_isExporting_2157_);
if (v___x_2160_ == 0)
{
lean_object* v___x_2161_; 
lean_dec_ref(v___x_2159_);
lean_dec_ref(v_env_2155_);
lean_dec(v_declHint_2150_);
v___x_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_msg_2149_);
return v___x_2161_;
}
else
{
lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v_c_2167_; lean_object* v___x_2168_; 
v___x_2162_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_2163_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_2164_ = l_Lean_Options_empty;
v___x_2165_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2165_, 0, v___x_2159_);
lean_ctor_set(v___x_2165_, 1, v___x_2162_);
lean_ctor_set(v___x_2165_, 2, v___x_2163_);
lean_ctor_set(v___x_2165_, 3, v___x_2164_);
lean_inc(v_declHint_2150_);
v___x_2166_ = l_Lean_MessageData_ofConstName(v_declHint_2150_, v___x_2156_);
v_c_2167_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_2167_, 0, v___x_2165_);
lean_ctor_set(v_c_2167_, 1, v___x_2166_);
v___x_2168_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_2155_, v_declHint_2150_);
if (lean_obj_tag(v___x_2168_) == 0)
{
lean_object* v___x_2169_; lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v_env_2155_);
lean_dec(v_declHint_2150_);
v___x_2169_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2170_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2170_, 0, v___x_2169_);
lean_ctor_set(v___x_2170_, 1, v_c_2167_);
v___x_2171_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_2172_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2172_, 0, v___x_2170_);
lean_ctor_set(v___x_2172_, 1, v___x_2171_);
v___x_2173_ = l_Lean_MessageData_note(v___x_2172_);
v___x_2174_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2174_, 0, v_msg_2149_);
lean_ctor_set(v___x_2174_, 1, v___x_2173_);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
return v___x_2175_;
}
else
{
lean_object* v_val_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2210_; 
v_val_2176_ = lean_ctor_get(v___x_2168_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2168_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2178_ = v___x_2168_;
v_isShared_2179_ = v_isSharedCheck_2210_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_val_2176_);
lean_dec(v___x_2168_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2210_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v_mod_2182_; uint8_t v___x_2183_; 
v___x_2180_ = l_Lean_Environment_header(v_env_2155_);
lean_dec_ref(v_env_2155_);
v___x_2181_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2180_);
v_mod_2182_ = lean_array_get(v___x_2153_, v___x_2181_, v_val_2176_);
lean_dec(v_val_2176_);
lean_dec_ref(v___x_2181_);
v___x_2183_ = l_Lean_isPrivateName(v_declHint_2150_);
lean_dec(v_declHint_2150_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_2185_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2184_);
lean_ctor_set(v___x_2185_, 1, v_c_2167_);
v___x_2186_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_2187_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2185_);
lean_ctor_set(v___x_2187_, 1, v___x_2186_);
v___x_2188_ = l_Lean_MessageData_ofName(v_mod_2182_);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2187_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_MessageData_note(v___x_2191_);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v_msg_2149_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2193_);
v___x_2195_ = v___x_2178_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
else
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2197_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_2198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2197_);
lean_ctor_set(v___x_2198_, 1, v_c_2167_);
v___x_2199_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = l_Lean_MessageData_ofName(v_mod_2182_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_2204_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
v___x_2205_ = l_Lean_MessageData_note(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2206_, 0, v_msg_2149_);
lean_ctor_set(v___x_2206_, 1, v___x_2205_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 0);
lean_ctor_set(v___x_2178_, 0, v___x_2206_);
v___x_2208_ = v___x_2178_;
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
}
}
}
else
{
lean_object* v___x_2211_; 
lean_dec_ref(v_env_2155_);
lean_dec(v_declHint_2150_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v_msg_2149_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_2212_, lean_object* v_declHint_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2212_, v_declHint_2213_, v___y_2214_);
lean_dec(v___y_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(lean_object* v_msg_2217_, lean_object* v_declHint_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2234_; 
v___x_2224_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2217_, v_declHint_2218_, v___y_2222_);
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2234_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2234_ == 0)
{
v___x_2227_ = v___x_2224_;
v_isShared_2228_ = v_isSharedCheck_2234_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_dec(v___x_2224_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2234_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2232_; 
v___x_2229_ = l_Lean_unknownIdentifierMessageTag;
v___x_2230_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2230_, 0, v___x_2229_);
lean_ctor_set(v___x_2230_, 1, v_a_2225_);
if (v_isShared_2228_ == 0)
{
lean_ctor_set(v___x_2227_, 0, v___x_2230_);
v___x_2232_ = v___x_2227_;
goto v_reusejp_2231_;
}
else
{
lean_object* v_reuseFailAlloc_2233_; 
v_reuseFailAlloc_2233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2233_, 0, v___x_2230_);
v___x_2232_ = v_reuseFailAlloc_2233_;
goto v_reusejp_2231_;
}
v_reusejp_2231_:
{
return v___x_2232_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4___boxed(lean_object* v_msg_2235_, lean_object* v_declHint_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2235_, v_declHint_2236_, v___y_2237_, v___y_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(lean_object* v_ref_2243_, lean_object* v_msg_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_){
_start:
{
lean_object* v_toCold_2250_; lean_object* v_currRecDepth_2251_; lean_object* v_ref_2252_; uint16_t v_optionFlags_2253_; uint8_t v_suppressElabErrors_2254_; uint8_t v_isRecordingDeps_2255_; lean_object* v_ref_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_toCold_2250_ = lean_ctor_get(v___y_2247_, 0);
v_currRecDepth_2251_ = lean_ctor_get(v___y_2247_, 1);
v_ref_2252_ = lean_ctor_get(v___y_2247_, 2);
v_optionFlags_2253_ = lean_ctor_get_uint16(v___y_2247_, sizeof(void*)*3);
v_suppressElabErrors_2254_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2255_ = lean_ctor_get_uint8(v___y_2247_, sizeof(void*)*3 + 3);
v_ref_2256_ = l_Lean_replaceRef(v_ref_2243_, v_ref_2252_);
lean_inc(v_currRecDepth_2251_);
lean_inc_ref(v_toCold_2250_);
v___x_2257_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2257_, 0, v_toCold_2250_);
lean_ctor_set(v___x_2257_, 1, v_currRecDepth_2251_);
lean_ctor_set(v___x_2257_, 2, v_ref_2256_);
lean_ctor_set_uint16(v___x_2257_, sizeof(void*)*3, v_optionFlags_2253_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*3 + 2, v_suppressElabErrors_2254_);
lean_ctor_set_uint8(v___x_2257_, sizeof(void*)*3 + 3, v_isRecordingDeps_2255_);
v___x_2258_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v_msg_2244_, v___y_2245_, v___y_2246_, v___x_2257_, v___y_2248_);
lean_dec_ref_known(v___x_2257_, 3);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg___boxed(lean_object* v_ref_2259_, lean_object* v_msg_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_){
_start:
{
lean_object* v_res_2266_; 
v_res_2266_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2259_, v_msg_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_);
lean_dec(v___y_2264_);
lean_dec_ref(v___y_2263_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v_ref_2259_);
return v_res_2266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(lean_object* v_ref_2267_, lean_object* v_msg_2268_, lean_object* v_declHint_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___x_2275_; lean_object* v_a_2276_; lean_object* v___x_2277_; 
v___x_2275_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4(v_msg_2268_, v_declHint_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
v___x_2277_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2267_, v_a_2276_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
return v___x_2277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_ref_2278_, lean_object* v_msg_2279_, lean_object* v_declHint_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_, lean_object* v___y_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2278_, v_msg_2279_, v_declHint_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_);
lean_dec(v___y_2284_);
lean_dec_ref(v___y_2283_);
lean_dec(v___y_2282_);
lean_dec_ref(v___y_2281_);
lean_dec(v_ref_2278_);
return v_res_2286_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2288_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__0));
v___x_2289_ = l_Lean_stringToMessageData(v___x_2288_);
return v___x_2289_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
v___x_2291_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__2));
v___x_2292_ = l_Lean_stringToMessageData(v___x_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(lean_object* v_ref_2293_, lean_object* v_constName_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v___x_2300_; uint8_t v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2300_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__1);
v___x_2301_ = 0;
lean_inc(v_constName_2294_);
v___x_2302_ = l_Lean_MessageData_ofConstName(v_constName_2294_, v___x_2301_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2300_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___closed__3);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2303_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2293_, v___x_2305_, v_constName_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_ref_2307_, lean_object* v_constName_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
lean_object* v_res_2314_; 
v_res_2314_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2307_, v_constName_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v_ref_2307_);
return v_res_2314_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(lean_object* v_constName_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_, lean_object* v___y_2319_){
_start:
{
lean_object* v_ref_2321_; lean_object* v___x_2322_; 
v_ref_2321_ = lean_ctor_get(v___y_2318_, 2);
v___x_2322_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2321_, v_constName_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_);
return v___x_2322_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg___boxed(lean_object* v_constName_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
lean_object* v_res_2329_; 
v_res_2329_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2323_, v___y_2324_, v___y_2325_, v___y_2326_, v___y_2327_);
lean_dec(v___y_2327_);
lean_dec_ref(v___y_2326_);
lean_dec(v___y_2325_);
lean_dec_ref(v___y_2324_);
return v_res_2329_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object* v_constName_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; lean_object* v_env_2337_; uint8_t v___x_2338_; lean_object* v___x_2339_; 
v___x_2336_ = lean_st_ref_get(v___y_2334_);
v_env_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_ref(v_env_2337_);
lean_dec(v___x_2336_);
v___x_2338_ = 0;
lean_inc(v_constName_2330_);
v___x_2339_ = l_Lean_Environment_findConstVal_x3f(v_env_2337_, v_constName_2330_, v___x_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v___x_2340_; 
v___x_2340_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2340_;
}
else
{
lean_object* v_val_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_constName_2330_);
v_val_2341_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2339_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_val_2341_);
lean_dec(v___x_2339_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 0);
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_val_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0___boxed(lean_object* v_constName_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2349_, v___y_2350_, v___y_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
lean_dec(v___y_2351_);
lean_dec_ref(v___y_2350_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(lean_object* v_constName_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___x_2362_; 
lean_inc(v_constName_2356_);
v___x_2362_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v_constName_2356_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_object* v_a_2363_; lean_object* v_levelParams_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_a_2363_);
lean_dec_ref_known(v___x_2362_, 1);
v_levelParams_2364_ = lean_ctor_get(v_a_2363_, 1);
v___x_2365_ = lean_box(0);
lean_inc(v_levelParams_2364_);
v___x_2366_ = l_List_mapM_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__1(v_levelParams_2364_, v___x_2365_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc_n(v_a_2367_, 2);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = l_Lean_mkConst(v_constName_2356_, v_a_2367_);
v___x_2369_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_2363_, v_a_2367_, v_a_2360_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2378_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2378_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2374_; lean_object* v___x_2376_; 
v___x_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2368_);
lean_ctor_set(v___x_2374_, 1, v_a_2370_);
if (v_isShared_2373_ == 0)
{
lean_ctor_set(v___x_2372_, 0, v___x_2374_);
v___x_2376_ = v___x_2372_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v___x_2374_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec_ref(v___x_2368_);
v_a_2379_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2369_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2369_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_a_2363_);
lean_dec(v_constName_2356_);
v_a_2387_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2366_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2366_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec(v_constName_2356_);
v_a_2395_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2362_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2362_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun___boxed(lean_object* v_constName_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v_res_2409_; 
v_res_2409_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2403_, v_a_2404_, v_a_2405_, v_a_2406_, v_a_2407_);
lean_dec(v_a_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
return v_res_2409_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(lean_object* v_00_u03b1_2410_, lean_object* v_constName_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_){
_start:
{
lean_object* v___x_2417_; 
v___x_2417_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___redArg(v_constName_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
return v___x_2417_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2418_, lean_object* v_constName_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v_res_2425_; 
v_res_2425_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0(v_00_u03b1_2418_, v_constName_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
return v_res_2425_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(lean_object* v_00_u03b1_2426_, lean_object* v_ref_2427_, lean_object* v_constName_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___redArg(v_ref_2427_, v_constName_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b1_2435_, lean_object* v_ref_2436_, lean_object* v_constName_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1(v_00_u03b1_2435_, v_ref_2436_, v_constName_2437_, v___y_2438_, v___y_2439_, v___y_2440_, v___y_2441_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v_ref_2436_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b1_2444_, lean_object* v_ref_2445_, lean_object* v_msg_2446_, lean_object* v_declHint_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v___x_2453_; 
v___x_2453_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2445_, v_msg_2446_, v_declHint_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
return v___x_2453_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b1_2454_, lean_object* v_ref_2455_, lean_object* v_msg_2456_, lean_object* v_declHint_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_){
_start:
{
lean_object* v_res_2463_; 
v_res_2463_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2454_, v_ref_2455_, v_msg_2456_, v_declHint_2457_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
lean_dec(v___y_2461_);
lean_dec_ref(v___y_2460_);
lean_dec(v___y_2459_);
lean_dec_ref(v___y_2458_);
lean_dec(v_ref_2455_);
return v_res_2463_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(lean_object* v_msg_2464_, lean_object* v_declHint_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_){
_start:
{
lean_object* v___x_2471_; 
v___x_2471_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___redArg(v_msg_2464_, v_declHint_2465_, v___y_2469_);
return v___x_2471_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_2472_, lean_object* v_declHint_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__4_spec__5(v_msg_2472_, v_declHint_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec(v___y_2475_);
lean_dec_ref(v___y_2474_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(lean_object* v_00_u03b1_2480_, lean_object* v_ref_2481_, lean_object* v_msg_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
lean_object* v___x_2488_; 
v___x_2488_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___redArg(v_ref_2481_, v_msg_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
return v___x_2488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5___boxed(lean_object* v_00_u03b1_2489_, lean_object* v_ref_2490_, lean_object* v_msg_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v_res_2497_; 
v_res_2497_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0_spec__0_spec__1_spec__3_spec__5(v_00_u03b1_2489_, v_ref_2490_, v_msg_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v_ref_2490_);
return v_res_2497_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__0));
v___x_2500_ = l_Lean_stringToMessageData(v___x_2499_);
return v___x_2500_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
v___x_2502_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__2));
v___x_2503_ = l_Lean_stringToMessageData(v___x_2502_);
return v___x_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(lean_object* v_inst_2504_, lean_object* v_f_2505_, lean_object* v_inst_2506_, lean_object* v_xs_2507_, lean_object* v_x_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2514_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_2515_ = lean_apply_1(v_inst_2504_, v_f_2505_);
v___x_2516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2514_);
lean_ctor_set(v___x_2516_, 1, v___x_2515_);
v___x_2517_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_2518_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2516_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = lean_apply_1(v_inst_2506_, v_xs_2507_);
v___x_2520_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2518_);
lean_ctor_set(v___x_2520_, 1, v___x_2519_);
v___x_2521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
return v___x_2521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed(lean_object* v_inst_2522_, lean_object* v_f_2523_, lean_object* v_inst_2524_, lean_object* v_xs_2525_, lean_object* v_x_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0(v_inst_2522_, v_f_2523_, v_inst_2524_, v_xs_2525_, v_x_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec_ref(v_x_2526_);
return v_res_2532_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0(void){
_start:
{
lean_object* v___x_2533_; 
v___x_2533_ = l_instMonadEIO___redArg();
return v___x_2533_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__0);
v___x_2535_ = l_StateRefT_x27_instMonad___redArg(v___x_2534_);
return v___x_2535_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8(void){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2542_ = l_Lean_Core_instMonadTraceCoreM;
v___x_2543_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2544_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___x_2543_, v___x_2542_);
return v___x_2544_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___f_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__8);
v___f_2546_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___x_2547_ = l_Lean_instMonadTraceOfMonadLift___redArg(v___f_2546_, v___x_2545_);
return v___x_2547_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2550_ = l_Lean_Core_instMonadQuotationCoreM;
v___x_2551_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__7));
v___x_2552_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__11));
v___x_2553_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___x_2552_, v___x_2551_, v___x_2550_);
return v___x_2553_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___f_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; 
v___x_2554_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__12);
v___f_2555_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__6));
v___f_2556_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__10));
v___x_2557_ = l_Lean_instMonadQuotationOfMonadFunctorOfMonadLift___redArg(v___f_2556_, v___f_2555_, v___x_2554_);
return v___x_2557_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14(void){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_instMonadExceptOfEIO___redArg();
return v___x_2558_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15(void){
_start:
{
lean_object* v___x_2559_; lean_object* v___x_2560_; 
v___x_2559_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__14);
v___x_2560_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2559_);
return v___x_2560_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__15);
v___x_2562_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2561_);
return v___x_2562_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17(void){
_start:
{
lean_object* v___x_2563_; lean_object* v___x_2564_; 
v___x_2563_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__16);
v___x_2564_ = l_Lean_instMonadAlwaysExceptStateRefT_x27___redArg(v___x_2563_);
return v___x_2564_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18(void){
_start:
{
lean_object* v___x_2565_; lean_object* v___x_2566_; 
v___x_2565_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__17);
v___x_2566_ = l_Lean_instMonadAlwaysExceptReaderT___redArg(v___x_2565_);
return v___x_2566_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25(void){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2578_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2579_ = l_Lean_Name_append(v___x_2578_, v___x_2577_);
return v___x_2579_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2586_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2587_ = l_Lean_Name_append(v___x_2586_, v___x_2585_);
return v___x_2587_;
}
}
static double _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30(void){
_start:
{
lean_object* v___x_2588_; double v___x_2589_; 
v___x_2588_ = lean_unsigned_to_nat(1000000000u);
v___x_2589_ = lean_float_of_nat(v___x_2588_);
return v___x_2589_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2596_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__24));
v___x_2597_ = l_Lean_Name_append(v___x_2596_, v___x_2595_);
return v___x_2597_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(lean_object* v_inst_2598_, lean_object* v_inst_2599_, lean_object* v_f_2600_, lean_object* v_xs_2601_, lean_object* v_k_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_, lean_object* v_a_2605_, lean_object* v_a_2606_){
_start:
{
lean_object* v___x_2608_; lean_object* v_toApplicative_2609_; lean_object* v_toFunctor_2610_; lean_object* v_toSeq_2611_; lean_object* v_toSeqLeft_2612_; lean_object* v_toSeqRight_2613_; lean_object* v___f_2614_; lean_object* v___f_2615_; lean_object* v___f_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; lean_object* v___f_2619_; lean_object* v___f_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v_toApplicative_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2864_; 
v___x_2608_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__1);
v_toApplicative_2609_ = lean_ctor_get(v___x_2608_, 0);
v_toFunctor_2610_ = lean_ctor_get(v_toApplicative_2609_, 0);
v_toSeq_2611_ = lean_ctor_get(v_toApplicative_2609_, 2);
v_toSeqLeft_2612_ = lean_ctor_get(v_toApplicative_2609_, 3);
v_toSeqRight_2613_ = lean_ctor_get(v_toApplicative_2609_, 4);
v___f_2614_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__2));
v___f_2615_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__3));
lean_inc_ref_n(v_toFunctor_2610_, 2);
v___f_2616_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2616_, 0, v_toFunctor_2610_);
v___f_2617_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2617_, 0, v_toFunctor_2610_);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___f_2616_);
lean_ctor_set(v___x_2618_, 1, v___f_2617_);
lean_inc(v_toSeqRight_2613_);
v___f_2619_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2619_, 0, v_toSeqRight_2613_);
lean_inc(v_toSeqLeft_2612_);
v___f_2620_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2620_, 0, v_toSeqLeft_2612_);
lean_inc(v_toSeq_2611_);
v___f_2621_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2621_, 0, v_toSeq_2611_);
v___x_2622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2618_);
lean_ctor_set(v___x_2622_, 1, v___f_2614_);
lean_ctor_set(v___x_2622_, 2, v___f_2621_);
lean_ctor_set(v___x_2622_, 3, v___f_2620_);
lean_ctor_set(v___x_2622_, 4, v___f_2619_);
v___x_2623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2623_, 0, v___x_2622_);
lean_ctor_set(v___x_2623_, 1, v___f_2615_);
v___x_2624_ = l_StateRefT_x27_instMonad___redArg(v___x_2623_);
v_toApplicative_2625_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2864_ == 0)
{
lean_object* v_unused_2865_; 
v_unused_2865_ = lean_ctor_get(v___x_2624_, 1);
lean_dec(v_unused_2865_);
v___x_2627_ = v___x_2624_;
v_isShared_2628_ = v_isSharedCheck_2864_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_toApplicative_2625_);
lean_dec(v___x_2624_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2864_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v_toFunctor_2629_; lean_object* v_toSeq_2630_; lean_object* v_toSeqLeft_2631_; lean_object* v_toSeqRight_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2862_; 
v_toFunctor_2629_ = lean_ctor_get(v_toApplicative_2625_, 0);
v_toSeq_2630_ = lean_ctor_get(v_toApplicative_2625_, 2);
v_toSeqLeft_2631_ = lean_ctor_get(v_toApplicative_2625_, 3);
v_toSeqRight_2632_ = lean_ctor_get(v_toApplicative_2625_, 4);
v_isSharedCheck_2862_ = !lean_is_exclusive(v_toApplicative_2625_);
if (v_isSharedCheck_2862_ == 0)
{
lean_object* v_unused_2863_; 
v_unused_2863_ = lean_ctor_get(v_toApplicative_2625_, 1);
lean_dec(v_unused_2863_);
v___x_2634_ = v_toApplicative_2625_;
v_isShared_2635_ = v_isSharedCheck_2862_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_toSeqRight_2632_);
lean_inc(v_toSeqLeft_2631_);
lean_inc(v_toSeq_2630_);
lean_inc(v_toFunctor_2629_);
lean_dec(v_toApplicative_2625_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2862_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___f_2636_; lean_object* v___f_2637_; lean_object* v___f_2638_; lean_object* v___f_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; lean_object* v___f_2642_; lean_object* v___f_2643_; lean_object* v___x_2645_; 
v___f_2636_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__4));
v___f_2637_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__5));
lean_inc_ref(v_toFunctor_2629_);
v___f_2638_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_2638_, 0, v_toFunctor_2629_);
v___f_2639_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2639_, 0, v_toFunctor_2629_);
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___f_2638_);
lean_ctor_set(v___x_2640_, 1, v___f_2639_);
v___f_2641_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_2641_, 0, v_toSeqRight_2632_);
v___f_2642_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_2642_, 0, v_toSeqLeft_2631_);
v___f_2643_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_2643_, 0, v_toSeq_2630_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 4, v___f_2641_);
lean_ctor_set(v___x_2634_, 3, v___f_2642_);
lean_ctor_set(v___x_2634_, 2, v___f_2643_);
lean_ctor_set(v___x_2634_, 1, v___f_2636_);
lean_ctor_set(v___x_2634_, 0, v___x_2640_);
v___x_2645_ = v___x_2634_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v___x_2640_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v___f_2636_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v___f_2643_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v___f_2642_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v___f_2641_);
v___x_2645_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2647_; 
if (v_isShared_2628_ == 0)
{
lean_ctor_set(v___x_2627_, 1, v___f_2637_);
lean_ctor_set(v___x_2627_, 0, v___x_2645_);
v___x_2647_ = v___x_2627_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2645_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___f_2637_);
v___x_2647_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v_toMonadRef_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v_toCold_2653_; lean_object* v_options_2654_; uint8_t v_hasTrace_2655_; 
v___x_2648_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__9);
v___x_2649_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__13);
v_toMonadRef_2650_ = lean_ctor_get(v___x_2649_, 0);
v___x_2651_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__18);
v___x_2652_ = l_Lean_KVMap_instValueBool;
v_toCold_2653_ = lean_ctor_get(v_a_2605_, 0);
v_options_2654_ = lean_ctor_get(v_toCold_2653_, 2);
v_hasTrace_2655_ = lean_ctor_get_uint8(v_options_2654_, sizeof(void*)*1);
if (v_hasTrace_2655_ == 0)
{
lean_object* v___x_2656_; 
lean_dec_ref(v___x_2647_);
lean_dec(v_xs_2601_);
lean_dec(v_f_2600_);
lean_dec_ref(v_inst_2599_);
lean_dec_ref(v_inst_2598_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2656_ = lean_apply_5(v_k_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2656_) == 0)
{
return v___x_2656_;
}
else
{
lean_object* v_a_2657_; uint8_t v___y_2659_; uint8_t v___x_2668_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
v___x_2668_ = l_Lean_Exception_isInterrupt(v_a_2657_);
if (v___x_2668_ == 0)
{
uint8_t v___x_2669_; 
lean_inc(v_a_2657_);
v___x_2669_ = l_Lean_Exception_isRuntime(v_a_2657_);
v___y_2659_ = v___x_2669_;
goto v___jp_2658_;
}
else
{
v___y_2659_ = v___x_2668_;
goto v___jp_2658_;
}
v___jp_2658_:
{
if (v___y_2659_ == 0)
{
lean_object* v___x_2661_; uint8_t v_isShared_2662_; uint8_t v_isSharedCheck_2666_; 
v_isSharedCheck_2666_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2666_ == 0)
{
lean_object* v_unused_2667_; 
v_unused_2667_ = lean_ctor_get(v___x_2656_, 0);
lean_dec(v_unused_2667_);
v___x_2661_ = v___x_2656_;
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
else
{
lean_dec(v___x_2656_);
v___x_2661_ = lean_box(0);
v_isShared_2662_ = v_isSharedCheck_2666_;
goto v_resetjp_2660_;
}
v_resetjp_2660_:
{
lean_object* v___x_2664_; 
if (v_isShared_2662_ == 0)
{
v___x_2664_ = v___x_2661_;
goto v_reusejp_2663_;
}
else
{
lean_object* v_reuseFailAlloc_2665_; 
v_reuseFailAlloc_2665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2665_, 0, v_a_2657_);
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
lean_dec(v_a_2657_);
return v___x_2656_;
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_2670_; lean_object* v___x_2671_; lean_object* v___y_2673_; lean_object* v___y_2674_; uint8_t v___y_2675_; lean_object* v___y_2700_; lean_object* v_a_2701_; lean_object* v___f_2704_; lean_object* v___f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v_a_2713_; lean_object* v___y_2727_; lean_object* v___y_2728_; lean_object* v_a_2729_; lean_object* v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; uint8_t v___y_2735_; lean_object* v___y_2744_; lean_object* v___y_2745_; lean_object* v_a_2746_; lean_object* v___y_2750_; lean_object* v___y_2751_; lean_object* v_a_2752_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v_a_2757_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v_a_2770_; lean_object* v___y_2773_; lean_object* v___y_2774_; lean_object* v___y_2775_; uint8_t v___y_2776_; lean_object* v___y_2785_; lean_object* v___y_2786_; lean_object* v_a_2787_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v_a_2793_; 
v_inheritedTraceOptions_2670_ = lean_ctor_get(v_toCold_2653_, 11);
v___x_2671_ = l_Lean_Meta_instAddMessageContextMetaM;
v___f_2704_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2704_, 0, v_inst_2598_);
lean_closure_set(v___f_2704_, 1, v_f_2600_);
lean_closure_set(v___f_2704_, 2, v_inst_2599_);
lean_closure_set(v___f_2704_, 3, v_xs_2601_);
v___f_2705_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__26));
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_2708_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_2709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2654_, v___x_2708_);
if (v___x_2709_ == 0)
{
lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2832_ = l_Lean_trace_profiler;
v___x_2833_ = l_Lean_Option_get___redArg(v___x_2652_, v_options_2654_, v___x_2832_);
v___x_2834_ = lean_unbox(v___x_2833_);
lean_dec(v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; 
lean_dec_ref(v___f_2704_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2835_ = lean_apply_5(v_k_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v___x_2839_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
v___x_2837_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2838_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2654_, v___x_2838_);
if (v___x_2839_ == 0)
{
lean_dec(v_a_2836_);
lean_dec_ref(v___x_2647_);
return v___x_2835_;
}
else
{
lean_object* v___x_2840_; lean_object* v___x_8995__overap_2841_; lean_object* v___x_2842_; 
lean_dec_ref_known(v___x_2835_, 1);
lean_inc(v_a_2836_);
v___x_2840_ = l_Lean_MessageData_ofExpr(v_a_2836_);
lean_inc_ref(v_toMonadRef_2650_);
lean_inc_ref(v___x_2647_);
v___x_8995__overap_2841_ = l_Lean_addTrace___redArg(v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, v___x_2837_, v___x_2840_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2842_ = lean_apply_5(v___x_8995__overap_2841_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v___x_2647_);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2849_ == 0)
{
lean_object* v_unused_2850_; 
v_unused_2850_ = lean_ctor_get(v___x_2842_, 0);
lean_dec(v_unused_2850_);
v___x_2844_ = v___x_2842_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v___x_2842_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v_a_2836_);
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2836_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_a_2836_);
v_a_2851_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2842_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2842_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
lean_inc(v_a_2851_);
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
v___y_2700_ = v___x_2856_;
v_a_2701_ = v_a_2851_;
goto v___jp_2699_;
}
}
}
}
}
else
{
lean_object* v_a_2859_; 
v_a_2859_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2859_);
v___y_2700_ = v___x_2835_;
v_a_2701_ = v_a_2859_;
goto v___jp_2699_;
}
}
else
{
goto v___jp_2795_;
}
}
else
{
goto v___jp_2795_;
}
v___jp_2672_:
{
if (v___y_2675_ == 0)
{
lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
lean_dec_ref(v___y_2674_);
v___x_2676_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2677_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2678_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2654_, v___x_2677_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
lean_dec_ref(v___x_2647_);
v___x_2679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2679_, 0, v___y_2673_);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_8806__overap_2681_; lean_object* v___x_2682_; 
lean_inc_ref(v___y_2673_);
v___x_2680_ = l_Lean_Exception_toMessageData(v___y_2673_);
lean_inc_ref(v_toMonadRef_2650_);
v___x_8806__overap_2681_ = l_Lean_addTrace___redArg(v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, v___x_2676_, v___x_2680_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2682_ = lean_apply_5(v___x_8806__overap_2681_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v___x_2684_; uint8_t v_isShared_2685_; uint8_t v_isSharedCheck_2689_; 
v_isSharedCheck_2689_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; 
v_unused_2690_ = lean_ctor_get(v___x_2682_, 0);
lean_dec(v_unused_2690_);
v___x_2684_ = v___x_2682_;
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
else
{
lean_dec(v___x_2682_);
v___x_2684_ = lean_box(0);
v_isShared_2685_ = v_isSharedCheck_2689_;
goto v_resetjp_2683_;
}
v_resetjp_2683_:
{
lean_object* v___x_2687_; 
if (v_isShared_2685_ == 0)
{
lean_ctor_set_tag(v___x_2684_, 1);
lean_ctor_set(v___x_2684_, 0, v___y_2673_);
v___x_2687_ = v___x_2684_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v___y_2673_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref(v___y_2673_);
v_a_2691_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2682_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2682_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_2673_);
lean_dec_ref(v___x_2647_);
return v___y_2674_;
}
}
v___jp_2699_:
{
uint8_t v___x_2702_; 
v___x_2702_ = l_Lean_Exception_isInterrupt(v_a_2701_);
if (v___x_2702_ == 0)
{
uint8_t v___x_2703_; 
lean_inc_ref(v_a_2701_);
v___x_2703_ = l_Lean_Exception_isRuntime(v_a_2701_);
v___y_2673_ = v_a_2701_;
v___y_2674_ = v___y_2700_;
v___y_2675_ = v___x_2703_;
goto v___jp_2672_;
}
else
{
v___y_2673_ = v_a_2701_;
v___y_2674_ = v___y_2700_;
v___y_2675_ = v___x_2702_;
goto v___jp_2672_;
}
}
v___jp_2710_:
{
lean_object* v___x_2714_; double v___x_2715_; double v___x_2716_; double v___x_2717_; double v___x_2718_; double v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_8867__overap_2724_; lean_object* v___x_2725_; 
v___x_2714_ = lean_io_mono_nanos_now();
v___x_2715_ = lean_float_of_nat(v___y_2712_);
v___x_2716_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_2717_ = lean_float_div(v___x_2715_, v___x_2716_);
v___x_2718_ = lean_float_of_nat(v___x_2714_);
v___x_2719_ = lean_float_div(v___x_2718_, v___x_2716_);
v___x_2720_ = lean_box_float(v___x_2717_);
v___x_2721_ = lean_box_float(v___x_2719_);
v___x_2722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2720_);
lean_ctor_set(v___x_2722_, 1, v___x_2721_);
v___x_2723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2723_, 0, v_a_2713_);
lean_ctor_set(v___x_2723_, 1, v___x_2722_);
lean_inc_ref(v_toMonadRef_2650_);
v___x_8867__overap_2724_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, lean_box(0), v___x_2651_, v___f_2705_, v___x_2706_, v_hasTrace_2655_, v___x_2707_, v_options_2654_, v___x_2709_, v___y_2711_, v___f_2704_, v___x_2723_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2725_ = lean_apply_5(v___x_8867__overap_2724_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
return v___x_2725_;
}
v___jp_2726_:
{
lean_object* v___x_2730_; 
v___x_2730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2730_, 0, v_a_2729_);
v___y_2711_ = v___y_2727_;
v___y_2712_ = v___y_2728_;
v_a_2713_ = v___x_2730_;
goto v___jp_2710_;
}
v___jp_2731_:
{
if (v___y_2735_ == 0)
{
lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; 
v___x_2736_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2737_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2738_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2654_, v___x_2737_);
if (v___x_2738_ == 0)
{
v___y_2727_ = v___y_2732_;
v___y_2728_ = v___y_2734_;
v_a_2729_ = v___y_2733_;
goto v___jp_2726_;
}
else
{
lean_object* v___x_2739_; lean_object* v___x_8886__overap_2740_; lean_object* v___x_2741_; 
lean_inc_ref(v___y_2733_);
v___x_2739_ = l_Lean_Exception_toMessageData(v___y_2733_);
lean_inc_ref(v_toMonadRef_2650_);
lean_inc_ref(v___x_2647_);
v___x_8886__overap_2740_ = l_Lean_addTrace___redArg(v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, v___x_2736_, v___x_2739_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2741_ = lean_apply_5(v___x_8886__overap_2740_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_dec_ref_known(v___x_2741_, 1);
v___y_2727_ = v___y_2732_;
v___y_2728_ = v___y_2734_;
v_a_2729_ = v___y_2733_;
goto v___jp_2726_;
}
else
{
lean_object* v_a_2742_; 
lean_dec_ref(v___y_2733_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2741_, 1);
v___y_2727_ = v___y_2732_;
v___y_2728_ = v___y_2734_;
v_a_2729_ = v_a_2742_;
goto v___jp_2726_;
}
}
}
else
{
v___y_2727_ = v___y_2732_;
v___y_2728_ = v___y_2734_;
v_a_2729_ = v___y_2733_;
goto v___jp_2726_;
}
}
v___jp_2743_:
{
uint8_t v___x_2747_; 
v___x_2747_ = l_Lean_Exception_isInterrupt(v_a_2746_);
if (v___x_2747_ == 0)
{
uint8_t v___x_2748_; 
lean_inc_ref(v_a_2746_);
v___x_2748_ = l_Lean_Exception_isRuntime(v_a_2746_);
v___y_2732_ = v___y_2744_;
v___y_2733_ = v_a_2746_;
v___y_2734_ = v___y_2745_;
v___y_2735_ = v___x_2748_;
goto v___jp_2731_;
}
else
{
v___y_2732_ = v___y_2744_;
v___y_2733_ = v_a_2746_;
v___y_2734_ = v___y_2745_;
v___y_2735_ = v___x_2747_;
goto v___jp_2731_;
}
}
v___jp_2749_:
{
lean_object* v___x_2753_; 
v___x_2753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2753_, 0, v_a_2752_);
v___y_2711_ = v___y_2750_;
v___y_2712_ = v___y_2751_;
v_a_2713_ = v___x_2753_;
goto v___jp_2710_;
}
v___jp_2754_:
{
lean_object* v___x_2758_; double v___x_2759_; double v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_8929__overap_2765_; lean_object* v___x_2766_; 
v___x_2758_ = lean_io_get_num_heartbeats();
v___x_2759_ = lean_float_of_nat(v___y_2756_);
v___x_2760_ = lean_float_of_nat(v___x_2758_);
v___x_2761_ = lean_box_float(v___x_2759_);
v___x_2762_ = lean_box_float(v___x_2760_);
v___x_2763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2761_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v_a_2757_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
lean_inc_ref(v_toMonadRef_2650_);
v___x_8929__overap_2765_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback(lean_box(0), lean_box(0), v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, lean_box(0), v___x_2651_, v___f_2705_, v___x_2706_, v_hasTrace_2655_, v___x_2707_, v_options_2654_, v___x_2709_, v___y_2755_, v___f_2704_, v___x_2764_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2766_ = lean_apply_5(v___x_8929__overap_2765_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
return v___x_2766_;
}
v___jp_2767_:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2771_, 0, v_a_2770_);
v___y_2755_ = v___y_2768_;
v___y_2756_ = v___y_2769_;
v_a_2757_ = v___x_2771_;
goto v___jp_2754_;
}
v___jp_2772_:
{
if (v___y_2776_ == 0)
{
lean_object* v___x_2777_; lean_object* v___x_2778_; uint8_t v___x_2779_; 
v___x_2777_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_2778_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_2779_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2654_, v___x_2778_);
if (v___x_2779_ == 0)
{
v___y_2768_ = v___y_2773_;
v___y_2769_ = v___y_2775_;
v_a_2770_ = v___y_2774_;
goto v___jp_2767_;
}
else
{
lean_object* v___x_2780_; lean_object* v___x_8948__overap_2781_; lean_object* v___x_2782_; 
lean_inc_ref(v___y_2774_);
v___x_2780_ = l_Lean_Exception_toMessageData(v___y_2774_);
lean_inc_ref(v_toMonadRef_2650_);
lean_inc_ref(v___x_2647_);
v___x_8948__overap_2781_ = l_Lean_addTrace___redArg(v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, v___x_2777_, v___x_2780_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2782_ = lean_apply_5(v___x_8948__overap_2781_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_dec_ref_known(v___x_2782_, 1);
v___y_2768_ = v___y_2773_;
v___y_2769_ = v___y_2775_;
v_a_2770_ = v___y_2774_;
goto v___jp_2767_;
}
else
{
lean_object* v_a_2783_; 
lean_dec_ref(v___y_2774_);
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
lean_inc(v_a_2783_);
lean_dec_ref_known(v___x_2782_, 1);
v___y_2768_ = v___y_2773_;
v___y_2769_ = v___y_2775_;
v_a_2770_ = v_a_2783_;
goto v___jp_2767_;
}
}
}
else
{
v___y_2768_ = v___y_2773_;
v___y_2769_ = v___y_2775_;
v_a_2770_ = v___y_2774_;
goto v___jp_2767_;
}
}
v___jp_2784_:
{
uint8_t v___x_2788_; 
v___x_2788_ = l_Lean_Exception_isInterrupt(v_a_2787_);
if (v___x_2788_ == 0)
{
uint8_t v___x_2789_; 
lean_inc_ref(v_a_2787_);
v___x_2789_ = l_Lean_Exception_isRuntime(v_a_2787_);
v___y_2773_ = v___y_2785_;
v___y_2774_ = v_a_2787_;
v___y_2775_ = v___y_2786_;
v___y_2776_ = v___x_2789_;
goto v___jp_2772_;
}
else
{
v___y_2773_ = v___y_2785_;
v___y_2774_ = v_a_2787_;
v___y_2775_ = v___y_2786_;
v___y_2776_ = v___x_2788_;
goto v___jp_2772_;
}
}
v___jp_2790_:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2794_, 0, v_a_2793_);
v___y_2755_ = v___y_2791_;
v___y_2756_ = v___y_2792_;
v_a_2757_ = v___x_2794_;
goto v___jp_2754_;
}
v___jp_2795_:
{
lean_object* v___x_8845__overap_2796_; lean_object* v___x_2797_; 
lean_inc_ref(v___x_2647_);
v___x_8845__overap_2796_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces(lean_box(0), v___x_2647_, v___x_2648_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2797_ = lean_apply_5(v___x_8845__overap_2796_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; uint8_t v___x_2801_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref_known(v___x_2797_, 1);
v___x_2799_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2800_ = l_Lean_Option_get___redArg(v___x_2652_, v_options_2654_, v___x_2799_);
v___x_2801_ = lean_unbox(v___x_2800_);
lean_dec(v___x_2800_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2802_; lean_object* v___x_2803_; 
v___x_2802_ = lean_io_mono_nanos_now();
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2803_ = lean_apply_5(v_k_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2803_) == 0)
{
lean_object* v_a_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; uint8_t v___x_2807_; 
v_a_2804_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2804_);
lean_dec_ref_known(v___x_2803_, 1);
v___x_2805_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2806_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2807_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2654_, v___x_2806_);
if (v___x_2807_ == 0)
{
v___y_2750_ = v_a_2798_;
v___y_2751_ = v___x_2802_;
v_a_2752_ = v_a_2804_;
goto v___jp_2749_;
}
else
{
lean_object* v___x_2808_; lean_object* v___x_8909__overap_2809_; lean_object* v___x_2810_; 
lean_inc(v_a_2804_);
v___x_2808_ = l_Lean_MessageData_ofExpr(v_a_2804_);
lean_inc_ref(v_toMonadRef_2650_);
lean_inc_ref(v___x_2647_);
v___x_8909__overap_2809_ = l_Lean_addTrace___redArg(v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, v___x_2805_, v___x_2808_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2810_ = lean_apply_5(v___x_8909__overap_2809_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_dec_ref_known(v___x_2810_, 1);
v___y_2750_ = v_a_2798_;
v___y_2751_ = v___x_2802_;
v_a_2752_ = v_a_2804_;
goto v___jp_2749_;
}
else
{
lean_object* v_a_2811_; 
lean_dec(v_a_2804_);
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___y_2744_ = v_a_2798_;
v___y_2745_ = v___x_2802_;
v_a_2746_ = v_a_2811_;
goto v___jp_2743_;
}
}
}
else
{
lean_object* v_a_2812_; 
v_a_2812_ = lean_ctor_get(v___x_2803_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2803_, 1);
v___y_2744_ = v_a_2798_;
v___y_2745_ = v___x_2802_;
v_a_2746_ = v_a_2812_;
goto v___jp_2743_;
}
}
else
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = lean_io_get_num_heartbeats();
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2814_ = lean_apply_5(v_k_2602_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_2817_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_2818_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2670_, v_options_2654_, v___x_2817_);
if (v___x_2818_ == 0)
{
v___y_2791_ = v_a_2798_;
v___y_2792_ = v___x_2813_;
v_a_2793_ = v_a_2815_;
goto v___jp_2790_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_8971__overap_2820_; lean_object* v___x_2821_; 
lean_inc(v_a_2815_);
v___x_2819_ = l_Lean_MessageData_ofExpr(v_a_2815_);
lean_inc_ref(v_toMonadRef_2650_);
lean_inc_ref(v___x_2647_);
v___x_8971__overap_2820_ = l_Lean_addTrace___redArg(v___x_2647_, v___x_2648_, v_toMonadRef_2650_, v___x_2671_, v___x_2816_, v___x_2819_);
lean_inc(v_a_2606_);
lean_inc_ref(v_a_2605_);
lean_inc(v_a_2604_);
lean_inc_ref(v_a_2603_);
v___x_2821_ = lean_apply_5(v___x_8971__overap_2820_, v_a_2603_, v_a_2604_, v_a_2605_, v_a_2606_, lean_box(0));
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_dec_ref_known(v___x_2821_, 1);
v___y_2791_ = v_a_2798_;
v___y_2792_ = v___x_2813_;
v_a_2793_ = v_a_2815_;
goto v___jp_2790_;
}
else
{
lean_object* v_a_2822_; 
lean_dec(v_a_2815_);
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___y_2785_ = v_a_2798_;
v___y_2786_ = v___x_2813_;
v_a_2787_ = v_a_2822_;
goto v___jp_2784_;
}
}
}
else
{
lean_object* v_a_2823_; 
v_a_2823_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2814_, 1);
v___y_2785_ = v_a_2798_;
v___y_2786_ = v___x_2813_;
v_a_2787_ = v_a_2823_;
goto v___jp_2784_;
}
}
}
else
{
lean_object* v_a_2824_; lean_object* v___x_2826_; uint8_t v_isShared_2827_; uint8_t v_isSharedCheck_2831_; 
lean_dec_ref(v___f_2704_);
lean_dec_ref(v___x_2647_);
lean_dec_ref(v_k_2602_);
v_a_2824_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2826_ = v___x_2797_;
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
else
{
lean_inc(v_a_2824_);
lean_dec(v___x_2797_);
v___x_2826_ = lean_box(0);
v_isShared_2827_ = v_isSharedCheck_2831_;
goto v_resetjp_2825_;
}
v_resetjp_2825_:
{
lean_object* v___x_2829_; 
if (v_isShared_2827_ == 0)
{
v___x_2829_ = v___x_2826_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
v___x_2829_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
return v___x_2829_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___boxed(lean_object* v_inst_2866_, lean_object* v_inst_2867_, lean_object* v_f_2868_, lean_object* v_xs_2869_, lean_object* v_k_2870_, lean_object* v_a_2871_, lean_object* v_a_2872_, lean_object* v_a_2873_, lean_object* v_a_2874_, lean_object* v_a_2875_){
_start:
{
lean_object* v_res_2876_; 
v_res_2876_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2866_, v_inst_2867_, v_f_2868_, v_xs_2869_, v_k_2870_, v_a_2871_, v_a_2872_, v_a_2873_, v_a_2874_);
lean_dec(v_a_2874_);
lean_dec_ref(v_a_2873_);
lean_dec(v_a_2872_);
lean_dec_ref(v_a_2871_);
return v_res_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(lean_object* v_00_u03b1_2877_, lean_object* v_00_u03b2_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_f_2881_, lean_object* v_xs_2882_, lean_object* v_k_2883_, lean_object* v_a_2884_, lean_object* v_a_2885_, lean_object* v_a_2886_, lean_object* v_a_2887_){
_start:
{
lean_object* v___x_2889_; 
v___x_2889_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg(v_inst_2879_, v_inst_2880_, v_f_2881_, v_xs_2882_, v_k_2883_, v_a_2884_, v_a_2885_, v_a_2886_, v_a_2887_);
return v___x_2889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___boxed(lean_object* v_00_u03b1_2890_, lean_object* v_00_u03b2_2891_, lean_object* v_inst_2892_, lean_object* v_inst_2893_, lean_object* v_f_2894_, lean_object* v_xs_2895_, lean_object* v_k_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_, lean_object* v_a_2901_){
_start:
{
lean_object* v_res_2902_; 
v_res_2902_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace(v_00_u03b1_2890_, v_00_u03b2_2891_, v_inst_2892_, v_inst_2893_, v_f_2894_, v_xs_2895_, v_k_2896_, v_a_2897_, v_a_2898_, v_a_2899_, v_a_2900_);
lean_dec(v_a_2900_);
lean_dec_ref(v_a_2899_);
lean_dec(v_a_2898_);
lean_dec_ref(v_a_2897_);
return v_res_2902_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(lean_object* v_k_2903_, uint8_t v_allowLevelAssignments_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_){
_start:
{
lean_object* v___x_2910_; 
v___x_2910_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_2904_, v_k_2903_, v___y_2905_, v___y_2906_, v___y_2907_, v___y_2908_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
v_a_2919_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2910_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2910_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg___boxed(lean_object* v_k_2927_, lean_object* v_allowLevelAssignments_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2934_; lean_object* v_res_2935_; 
v_allowLevelAssignments_boxed_2934_ = lean_unbox(v_allowLevelAssignments_2928_);
v_res_2935_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2927_, v_allowLevelAssignments_boxed_2934_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(lean_object* v_00_u03b1_2936_, lean_object* v_k_2937_, uint8_t v_allowLevelAssignments_2938_, lean_object* v___y_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___redArg(v_k_2937_, v_allowLevelAssignments_2938_, v___y_2939_, v___y_2940_, v___y_2941_, v___y_2942_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed(lean_object* v_00_u03b1_2945_, lean_object* v_k_2946_, lean_object* v_allowLevelAssignments_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_, lean_object* v___y_2952_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_2953_; lean_object* v_res_2954_; 
v_allowLevelAssignments_boxed_2953_ = lean_unbox(v_allowLevelAssignments_2947_);
v_res_2954_ = l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0(v_00_u03b1_2945_, v_k_2946_, v_allowLevelAssignments_boxed_2953_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0(lean_object* v_constName_2955_, lean_object* v_xs_2956_, lean_object* v___y_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___x_2962_; 
v___x_2962_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_2955_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v_fst_2964_; lean_object* v_snd_2965_; lean_object* v___x_2966_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v_fst_2964_ = lean_ctor_get(v_a_2963_, 0);
lean_inc(v_fst_2964_);
v_snd_2965_ = lean_ctor_get(v_a_2963_, 1);
lean_inc(v_snd_2965_);
lean_dec(v_a_2963_);
v___x_2966_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs(v_fst_2964_, v_snd_2965_, v_xs_2956_, v___y_2957_, v___y_2958_, v___y_2959_, v___y_2960_);
return v___x_2966_;
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v_a_2967_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2962_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2962_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___lam__0___boxed(lean_object* v_constName_2975_, lean_object* v_xs_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Meta_mkAppM___lam__0(v_constName_2975_, v_xs_2976_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
lean_dec(v___y_2980_);
lean_dec_ref(v___y_2979_);
lean_dec(v___y_2978_);
lean_dec_ref(v___y_2977_);
lean_dec_ref(v_xs_2976_);
return v_res_2982_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2983_ = lean_unsigned_to_nat(32u);
v___x_2984_ = lean_mk_empty_array_with_capacity(v___x_2983_);
v___x_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2985_, 0, v___x_2984_);
return v___x_2985_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1(void){
_start:
{
size_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; 
v___x_2986_ = ((size_t)5ULL);
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = lean_unsigned_to_nat(32u);
v___x_2989_ = lean_mk_empty_array_with_capacity(v___x_2988_);
v___x_2990_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__0);
v___x_2991_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2991_, 0, v___x_2990_);
lean_ctor_set(v___x_2991_, 1, v___x_2989_);
lean_ctor_set(v___x_2991_, 2, v___x_2987_);
lean_ctor_set(v___x_2991_, 3, v___x_2987_);
lean_ctor_set_usize(v___x_2991_, 4, v___x_2986_);
return v___x_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(lean_object* v___y_2992_){
_start:
{
lean_object* v___x_2994_; lean_object* v_traceState_2995_; lean_object* v_traces_2996_; lean_object* v___x_2997_; lean_object* v_traceState_2998_; lean_object* v_env_2999_; lean_object* v_nextMacroScope_3000_; lean_object* v_ngen_3001_; lean_object* v_auxDeclNGen_3002_; lean_object* v_cache_3003_; lean_object* v_recordedDeps_3004_; lean_object* v_messages_3005_; lean_object* v_infoState_3006_; lean_object* v_snapshotTasks_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3026_; 
v___x_2994_ = lean_st_ref_get(v___y_2992_);
v_traceState_2995_ = lean_ctor_get(v___x_2994_, 4);
lean_inc_ref(v_traceState_2995_);
lean_dec(v___x_2994_);
v_traces_2996_ = lean_ctor_get(v_traceState_2995_, 0);
lean_inc_ref(v_traces_2996_);
lean_dec_ref(v_traceState_2995_);
v___x_2997_ = lean_st_ref_take(v___y_2992_);
v_traceState_2998_ = lean_ctor_get(v___x_2997_, 4);
v_env_2999_ = lean_ctor_get(v___x_2997_, 0);
v_nextMacroScope_3000_ = lean_ctor_get(v___x_2997_, 1);
v_ngen_3001_ = lean_ctor_get(v___x_2997_, 2);
v_auxDeclNGen_3002_ = lean_ctor_get(v___x_2997_, 3);
v_cache_3003_ = lean_ctor_get(v___x_2997_, 5);
v_recordedDeps_3004_ = lean_ctor_get(v___x_2997_, 6);
v_messages_3005_ = lean_ctor_get(v___x_2997_, 7);
v_infoState_3006_ = lean_ctor_get(v___x_2997_, 8);
v_snapshotTasks_3007_ = lean_ctor_get(v___x_2997_, 9);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3009_ = v___x_2997_;
v_isShared_3010_ = v_isSharedCheck_3026_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_snapshotTasks_3007_);
lean_inc(v_infoState_3006_);
lean_inc(v_messages_3005_);
lean_inc(v_recordedDeps_3004_);
lean_inc(v_cache_3003_);
lean_inc(v_traceState_2998_);
lean_inc(v_auxDeclNGen_3002_);
lean_inc(v_ngen_3001_);
lean_inc(v_nextMacroScope_3000_);
lean_inc(v_env_2999_);
lean_dec(v___x_2997_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3026_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
uint64_t v_tid_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3024_; 
v_tid_3011_ = lean_ctor_get_uint64(v_traceState_2998_, sizeof(void*)*1);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_traceState_2998_);
if (v_isSharedCheck_3024_ == 0)
{
lean_object* v_unused_3025_; 
v_unused_3025_ = lean_ctor_get(v_traceState_2998_, 0);
lean_dec(v_unused_3025_);
v___x_3013_ = v_traceState_2998_;
v_isShared_3014_ = v_isSharedCheck_3024_;
goto v_resetjp_3012_;
}
else
{
lean_dec(v_traceState_2998_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3024_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3015_; lean_object* v___x_3017_; 
v___x_3015_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___closed__1);
if (v_isShared_3014_ == 0)
{
lean_ctor_set(v___x_3013_, 0, v___x_3015_);
v___x_3017_ = v___x_3013_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v___x_3015_);
lean_ctor_set_uint64(v_reuseFailAlloc_3023_, sizeof(void*)*1, v_tid_3011_);
v___x_3017_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 4, v___x_3017_);
v___x_3019_ = v___x_3009_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_env_2999_);
lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_nextMacroScope_3000_);
lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_ngen_3001_);
lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_auxDeclNGen_3002_);
lean_ctor_set(v_reuseFailAlloc_3022_, 4, v___x_3017_);
lean_ctor_set(v_reuseFailAlloc_3022_, 5, v_cache_3003_);
lean_ctor_set(v_reuseFailAlloc_3022_, 6, v_recordedDeps_3004_);
lean_ctor_set(v_reuseFailAlloc_3022_, 7, v_messages_3005_);
lean_ctor_set(v_reuseFailAlloc_3022_, 8, v_infoState_3006_);
lean_ctor_set(v_reuseFailAlloc_3022_, 9, v_snapshotTasks_3007_);
v___x_3019_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; lean_object* v___x_3021_; 
v___x_3020_ = lean_st_ref_put(v___y_2992_, v___x_3019_);
v___x_3021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3021_, 0, v_traces_2996_);
return v___x_3021_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg___boxed(lean_object* v___y_3027_, lean_object* v___y_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3027_);
lean_dec(v___y_3027_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(lean_object* v_opts_3030_, lean_object* v_opt_3031_){
_start:
{
lean_object* v_name_3032_; lean_object* v_defValue_3033_; lean_object* v_map_3034_; lean_object* v___x_3035_; 
v_name_3032_ = lean_ctor_get(v_opt_3031_, 0);
v_defValue_3033_ = lean_ctor_get(v_opt_3031_, 1);
v_map_3034_ = lean_ctor_get(v_opts_3030_, 0);
v___x_3035_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3034_, v_name_3032_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_inc(v_defValue_3033_);
return v_defValue_3033_;
}
else
{
lean_object* v_val_3036_; 
v_val_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_val_3036_);
lean_dec_ref_known(v___x_3035_, 1);
if (lean_obj_tag(v_val_3036_) == 3)
{
lean_object* v_v_3037_; 
v_v_3037_ = lean_ctor_get(v_val_3036_, 0);
lean_inc(v_v_3037_);
lean_dec_ref_known(v_val_3036_, 1);
return v_v_3037_;
}
else
{
lean_dec(v_val_3036_);
lean_inc(v_defValue_3033_);
return v_defValue_3033_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9___boxed(lean_object* v_opts_3038_, lean_object* v_opt_3039_){
_start:
{
lean_object* v_res_3040_; 
v_res_3040_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3038_, v_opt_3039_);
lean_dec_ref(v_opt_3039_);
lean_dec_ref(v_opts_3038_);
return v_res_3040_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(lean_object* v_opts_3041_, lean_object* v_opt_3042_){
_start:
{
lean_object* v_name_3043_; lean_object* v_defValue_3044_; lean_object* v_map_3045_; lean_object* v___x_3046_; 
v_name_3043_ = lean_ctor_get(v_opt_3042_, 0);
v_defValue_3044_ = lean_ctor_get(v_opt_3042_, 1);
v_map_3045_ = lean_ctor_get(v_opts_3041_, 0);
v___x_3046_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3045_, v_name_3043_);
if (lean_obj_tag(v___x_3046_) == 0)
{
uint8_t v___x_3047_; 
v___x_3047_ = lean_unbox(v_defValue_3044_);
return v___x_3047_;
}
else
{
lean_object* v_val_3048_; 
v_val_3048_ = lean_ctor_get(v___x_3046_, 0);
lean_inc(v_val_3048_);
lean_dec_ref_known(v___x_3046_, 1);
if (lean_obj_tag(v_val_3048_) == 1)
{
uint8_t v_v_3049_; 
v_v_3049_ = lean_ctor_get_uint8(v_val_3048_, 0);
lean_dec_ref_known(v_val_3048_, 0);
return v_v_3049_;
}
else
{
uint8_t v___x_3050_; 
lean_dec(v_val_3048_);
v___x_3050_ = lean_unbox(v_defValue_3044_);
return v___x_3050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4___boxed(lean_object* v_opts_3051_, lean_object* v_opt_3052_){
_start:
{
uint8_t v_res_3053_; lean_object* v_r_3054_; 
v_res_3053_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3051_, v_opt_3052_);
lean_dec_ref(v_opt_3052_);
lean_dec_ref(v_opts_3051_);
v_r_3054_ = lean_box(v_res_3053_);
return v_r_3054_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(lean_object* v_e_3055_){
_start:
{
if (lean_obj_tag(v_e_3055_) == 0)
{
uint8_t v___x_3056_; 
v___x_3056_ = 2;
return v___x_3056_;
}
else
{
lean_object* v_a_3057_; uint8_t v___x_3058_; 
v_a_3057_ = lean_ctor_get(v_e_3055_, 0);
v___x_3058_ = l_Lean_Expr_hasSyntheticSorry(v_a_3057_);
if (v___x_3058_ == 0)
{
uint8_t v___x_3059_; 
v___x_3059_ = 0;
return v___x_3059_;
}
else
{
uint8_t v___x_3060_; 
v___x_3060_ = 1;
return v___x_3060_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8___boxed(lean_object* v_e_3061_){
_start:
{
uint8_t v_res_3062_; lean_object* v_r_3063_; 
v_res_3062_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_e_3061_);
lean_dec_ref(v_e_3061_);
v_r_3063_ = lean_box(v_res_3062_);
return v_r_3063_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(size_t v_sz_3064_, size_t v_i_3065_, lean_object* v_bs_3066_){
_start:
{
uint8_t v___x_3067_; 
v___x_3067_ = lean_usize_dec_lt(v_i_3065_, v_sz_3064_);
if (v___x_3067_ == 0)
{
return v_bs_3066_;
}
else
{
lean_object* v_v_3068_; lean_object* v_msg_3069_; lean_object* v___x_3070_; lean_object* v_bs_x27_3071_; size_t v___x_3072_; size_t v___x_3073_; lean_object* v___x_3074_; 
v_v_3068_ = lean_array_uget_borrowed(v_bs_3066_, v_i_3065_);
v_msg_3069_ = lean_ctor_get(v_v_3068_, 1);
lean_inc_ref(v_msg_3069_);
v___x_3070_ = lean_unsigned_to_nat(0u);
v_bs_x27_3071_ = lean_array_uset(v_bs_3066_, v_i_3065_, v___x_3070_);
v___x_3072_ = ((size_t)1ULL);
v___x_3073_ = lean_usize_add(v_i_3065_, v___x_3072_);
v___x_3074_ = lean_array_uset(v_bs_x27_3071_, v_i_3065_, v_msg_3069_);
v_i_3065_ = v___x_3073_;
v_bs_3066_ = v___x_3074_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7___boxed(lean_object* v_sz_3076_, lean_object* v_i_3077_, lean_object* v_bs_3078_){
_start:
{
size_t v_sz_boxed_3079_; size_t v_i_boxed_3080_; lean_object* v_res_3081_; 
v_sz_boxed_3079_ = lean_unbox_usize(v_sz_3076_);
lean_dec(v_sz_3076_);
v_i_boxed_3080_ = lean_unbox_usize(v_i_3077_);
lean_dec(v_i_3077_);
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_boxed_3079_, v_i_boxed_3080_, v_bs_3078_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(lean_object* v_oldTraces_3082_, lean_object* v_data_3083_, lean_object* v_ref_3084_, lean_object* v_msg_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_toCold_3091_; lean_object* v_currRecDepth_3092_; lean_object* v_ref_3093_; uint16_t v_optionFlags_3094_; uint8_t v_suppressElabErrors_3095_; uint8_t v_isRecordingDeps_3096_; lean_object* v_ref_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v_traceState_3100_; lean_object* v_traces_3101_; lean_object* v___x_3102_; size_t v_sz_3103_; size_t v___x_3104_; lean_object* v___x_3105_; lean_object* v_msg_3106_; lean_object* v___x_3107_; lean_object* v_a_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3146_; 
v_toCold_3091_ = lean_ctor_get(v___y_3088_, 0);
v_currRecDepth_3092_ = lean_ctor_get(v___y_3088_, 1);
v_ref_3093_ = lean_ctor_get(v___y_3088_, 2);
v_optionFlags_3094_ = lean_ctor_get_uint16(v___y_3088_, sizeof(void*)*3);
v_suppressElabErrors_3095_ = lean_ctor_get_uint8(v___y_3088_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3096_ = lean_ctor_get_uint8(v___y_3088_, sizeof(void*)*3 + 3);
v_ref_3097_ = l_Lean_replaceRef(v_ref_3084_, v_ref_3093_);
lean_inc(v_currRecDepth_3092_);
lean_inc_ref(v_toCold_3091_);
v___x_3098_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3098_, 0, v_toCold_3091_);
lean_ctor_set(v___x_3098_, 1, v_currRecDepth_3092_);
lean_ctor_set(v___x_3098_, 2, v_ref_3097_);
lean_ctor_set_uint16(v___x_3098_, sizeof(void*)*3, v_optionFlags_3094_);
lean_ctor_set_uint8(v___x_3098_, sizeof(void*)*3 + 2, v_suppressElabErrors_3095_);
lean_ctor_set_uint8(v___x_3098_, sizeof(void*)*3 + 3, v_isRecordingDeps_3096_);
v___x_3099_ = lean_st_ref_get(v___y_3089_);
v_traceState_3100_ = lean_ctor_get(v___x_3099_, 4);
lean_inc_ref(v_traceState_3100_);
lean_dec(v___x_3099_);
v_traces_3101_ = lean_ctor_get(v_traceState_3100_, 0);
lean_inc_ref(v_traces_3101_);
lean_dec_ref(v_traceState_3100_);
v___x_3102_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3101_);
lean_dec_ref(v_traces_3101_);
v_sz_3103_ = lean_array_size(v___x_3102_);
v___x_3104_ = ((size_t)0ULL);
v___x_3105_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6_spec__7(v_sz_3103_, v___x_3104_, v___x_3102_);
v_msg_3106_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3106_, 0, v_data_3083_);
lean_ctor_set(v_msg_3106_, 1, v_msg_3085_);
lean_ctor_set(v_msg_3106_, 2, v___x_3105_);
v___x_3107_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3106_, v___y_3086_, v___y_3087_, v___x_3098_, v___y_3089_);
lean_dec_ref_known(v___x_3098_, 3);
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3110_ = v___x_3107_;
v_isShared_3111_ = v_isSharedCheck_3146_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_a_3108_);
lean_dec(v___x_3107_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3146_;
goto v_resetjp_3109_;
}
v_resetjp_3109_:
{
lean_object* v___x_3112_; lean_object* v_traceState_3113_; lean_object* v_env_3114_; lean_object* v_nextMacroScope_3115_; lean_object* v_ngen_3116_; lean_object* v_auxDeclNGen_3117_; lean_object* v_cache_3118_; lean_object* v_recordedDeps_3119_; lean_object* v_messages_3120_; lean_object* v_infoState_3121_; lean_object* v_snapshotTasks_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3145_; 
v___x_3112_ = lean_st_ref_take(v___y_3089_);
v_traceState_3113_ = lean_ctor_get(v___x_3112_, 4);
v_env_3114_ = lean_ctor_get(v___x_3112_, 0);
v_nextMacroScope_3115_ = lean_ctor_get(v___x_3112_, 1);
v_ngen_3116_ = lean_ctor_get(v___x_3112_, 2);
v_auxDeclNGen_3117_ = lean_ctor_get(v___x_3112_, 3);
v_cache_3118_ = lean_ctor_get(v___x_3112_, 5);
v_recordedDeps_3119_ = lean_ctor_get(v___x_3112_, 6);
v_messages_3120_ = lean_ctor_get(v___x_3112_, 7);
v_infoState_3121_ = lean_ctor_get(v___x_3112_, 8);
v_snapshotTasks_3122_ = lean_ctor_get(v___x_3112_, 9);
v_isSharedCheck_3145_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3145_ == 0)
{
v___x_3124_ = v___x_3112_;
v_isShared_3125_ = v_isSharedCheck_3145_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_snapshotTasks_3122_);
lean_inc(v_infoState_3121_);
lean_inc(v_messages_3120_);
lean_inc(v_recordedDeps_3119_);
lean_inc(v_cache_3118_);
lean_inc(v_traceState_3113_);
lean_inc(v_auxDeclNGen_3117_);
lean_inc(v_ngen_3116_);
lean_inc(v_nextMacroScope_3115_);
lean_inc(v_env_3114_);
lean_dec(v___x_3112_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3145_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
uint64_t v_tid_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3143_; 
v_tid_3126_ = lean_ctor_get_uint64(v_traceState_3113_, sizeof(void*)*1);
v_isSharedCheck_3143_ = !lean_is_exclusive(v_traceState_3113_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; 
v_unused_3144_ = lean_ctor_get(v_traceState_3113_, 0);
lean_dec(v_unused_3144_);
v___x_3128_ = v_traceState_3113_;
v_isShared_3129_ = v_isSharedCheck_3143_;
goto v_resetjp_3127_;
}
else
{
lean_dec(v_traceState_3113_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3143_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3130_ = lean_box(0);
v___x_3131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3131_, 0, v_ref_3084_);
lean_ctor_set(v___x_3131_, 1, v_a_3108_);
v___x_3132_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3082_, v___x_3131_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3132_);
v___x_3134_ = v___x_3128_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3132_);
lean_ctor_set_uint64(v_reuseFailAlloc_3142_, sizeof(void*)*1, v_tid_3126_);
v___x_3134_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
lean_object* v___x_3136_; 
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 4, v___x_3134_);
v___x_3136_ = v___x_3124_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_env_3114_);
lean_ctor_set(v_reuseFailAlloc_3141_, 1, v_nextMacroScope_3115_);
lean_ctor_set(v_reuseFailAlloc_3141_, 2, v_ngen_3116_);
lean_ctor_set(v_reuseFailAlloc_3141_, 3, v_auxDeclNGen_3117_);
lean_ctor_set(v_reuseFailAlloc_3141_, 4, v___x_3134_);
lean_ctor_set(v_reuseFailAlloc_3141_, 5, v_cache_3118_);
lean_ctor_set(v_reuseFailAlloc_3141_, 6, v_recordedDeps_3119_);
lean_ctor_set(v_reuseFailAlloc_3141_, 7, v_messages_3120_);
lean_ctor_set(v_reuseFailAlloc_3141_, 8, v_infoState_3121_);
lean_ctor_set(v_reuseFailAlloc_3141_, 9, v_snapshotTasks_3122_);
v___x_3136_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
lean_object* v___x_3137_; lean_object* v___x_3139_; 
v___x_3137_ = lean_st_ref_put(v___y_3089_, v___x_3136_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set(v___x_3110_, 0, v___x_3130_);
v___x_3139_ = v___x_3110_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v___x_3130_);
v___x_3139_ = v_reuseFailAlloc_3140_;
goto v_reusejp_3138_;
}
v_reusejp_3138_:
{
return v___x_3139_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6___boxed(lean_object* v_oldTraces_3147_, lean_object* v_data_3148_, lean_object* v_ref_3149_, lean_object* v_msg_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3147_, v_data_3148_, v_ref_3149_, v_msg_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(lean_object* v_x_3157_){
_start:
{
if (lean_obj_tag(v_x_3157_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_a_3159_ = lean_ctor_get(v_x_3157_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v_x_3157_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v_x_3157_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v_x_3157_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
lean_ctor_set_tag(v___x_3161_, 1);
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
v_a_3167_ = lean_ctor_get(v_x_3157_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v_x_3157_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v_x_3157_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v_x_3157_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
lean_ctor_set_tag(v___x_3169_, 0);
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg___boxed(lean_object* v_x_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v_res_3177_; 
v_res_3177_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3175_);
return v_res_3177_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0(void){
_start:
{
lean_object* v___x_3178_; double v___x_3179_; 
v___x_3178_ = lean_unsigned_to_nat(0u);
v___x_3179_ = lean_float_of_nat(v___x_3178_);
return v___x_3179_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__1));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3(void){
_start:
{
lean_object* v___x_3183_; double v___x_3184_; 
v___x_3183_ = lean_unsigned_to_nat(1000u);
v___x_3184_ = lean_float_of_nat(v___x_3183_);
return v___x_3184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(lean_object* v_cls_3185_, uint8_t v_collapsed_3186_, lean_object* v_tag_3187_, lean_object* v_opts_3188_, uint8_t v_clsEnabled_3189_, lean_object* v_oldTraces_3190_, lean_object* v_msg_3191_, lean_object* v_resStartStop_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_fst_3198_; lean_object* v_snd_3199_; lean_object* v___y_3201_; lean_object* v___y_3202_; lean_object* v_data_3203_; lean_object* v_fst_3214_; lean_object* v_snd_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; lean_object* v___y_3219_; lean_object* v_a_3220_; uint8_t v___y_3235_; double v___y_3267_; 
v_fst_3198_ = lean_ctor_get(v_resStartStop_3192_, 0);
lean_inc(v_fst_3198_);
v_snd_3199_ = lean_ctor_get(v_resStartStop_3192_, 1);
lean_inc(v_snd_3199_);
lean_dec_ref(v_resStartStop_3192_);
v_fst_3214_ = lean_ctor_get(v_snd_3199_, 0);
lean_inc(v_fst_3214_);
v_snd_3215_ = lean_ctor_get(v_snd_3199_, 1);
lean_inc(v_snd_3215_);
lean_dec(v_snd_3199_);
v___x_3216_ = l_Lean_trace_profiler;
v___x_3217_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3188_, v___x_3216_);
if (v___x_3217_ == 0)
{
v___y_3235_ = v___x_3217_;
goto v___jp_3234_;
}
else
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3273_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_opts_3188_, v___x_3272_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; double v___x_3276_; double v___x_3277_; double v___x_3278_; 
v___x_3274_ = l_Lean_trace_profiler_threshold;
v___x_3275_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3188_, v___x_3274_);
v___x_3276_ = lean_float_of_nat(v___x_3275_);
v___x_3277_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__3);
v___x_3278_ = lean_float_div(v___x_3276_, v___x_3277_);
v___y_3267_ = v___x_3278_;
goto v___jp_3266_;
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; double v___x_3281_; 
v___x_3279_ = l_Lean_trace_profiler_threshold;
v___x_3280_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__9(v_opts_3188_, v___x_3279_);
v___x_3281_ = lean_float_of_nat(v___x_3280_);
v___y_3267_ = v___x_3281_;
goto v___jp_3266_;
}
}
v___jp_3200_:
{
lean_object* v___x_3204_; 
lean_inc(v___y_3202_);
v___x_3204_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__6(v_oldTraces_3190_, v_data_3203_, v___y_3202_, v___y_3201_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v___x_3205_; 
lean_dec_ref_known(v___x_3204_, 1);
v___x_3205_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3198_);
return v___x_3205_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
lean_dec(v_fst_3198_);
v_a_3206_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___x_3204_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___x_3204_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
}
}
}
}
v___jp_3218_:
{
uint8_t v_result_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; double v___x_3224_; lean_object* v_data_3225_; 
v_result_3221_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__8(v_fst_3198_);
v___x_3222_ = lean_box(v_result_3221_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
v___x_3224_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
lean_inc_ref(v_tag_3187_);
lean_inc_ref(v___x_3223_);
lean_inc(v_cls_3185_);
v_data_3225_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3225_, 0, v_cls_3185_);
lean_ctor_set(v_data_3225_, 1, v___x_3223_);
lean_ctor_set(v_data_3225_, 2, v_tag_3187_);
lean_ctor_set_float(v_data_3225_, sizeof(void*)*3, v___x_3224_);
lean_ctor_set_float(v_data_3225_, sizeof(void*)*3 + 8, v___x_3224_);
lean_ctor_set_uint8(v_data_3225_, sizeof(void*)*3 + 16, v_collapsed_3186_);
if (v___x_3217_ == 0)
{
lean_dec_ref_known(v___x_3223_, 1);
lean_dec(v_snd_3215_);
lean_dec(v_fst_3214_);
lean_dec_ref(v_tag_3187_);
lean_dec(v_cls_3185_);
v___y_3201_ = v_a_3220_;
v___y_3202_ = v___y_3219_;
v_data_3203_ = v_data_3225_;
goto v___jp_3200_;
}
else
{
lean_object* v_data_3226_; double v___x_3227_; double v___x_3228_; 
lean_dec_ref_known(v_data_3225_, 3);
v_data_3226_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3226_, 0, v_cls_3185_);
lean_ctor_set(v_data_3226_, 1, v___x_3223_);
lean_ctor_set(v_data_3226_, 2, v_tag_3187_);
v___x_3227_ = lean_unbox_float(v_fst_3214_);
lean_dec(v_fst_3214_);
lean_ctor_set_float(v_data_3226_, sizeof(void*)*3, v___x_3227_);
v___x_3228_ = lean_unbox_float(v_snd_3215_);
lean_dec(v_snd_3215_);
lean_ctor_set_float(v_data_3226_, sizeof(void*)*3 + 8, v___x_3228_);
lean_ctor_set_uint8(v_data_3226_, sizeof(void*)*3 + 16, v_collapsed_3186_);
v___y_3201_ = v_a_3220_;
v___y_3202_ = v___y_3219_;
v_data_3203_ = v_data_3226_;
goto v___jp_3200_;
}
}
v___jp_3229_:
{
lean_object* v_ref_3230_; lean_object* v___x_3231_; 
v_ref_3230_ = lean_ctor_get(v___y_3195_, 2);
lean_inc(v___y_3196_);
lean_inc_ref(v___y_3195_);
lean_inc(v___y_3194_);
lean_inc_ref(v___y_3193_);
lean_inc(v_fst_3198_);
v___x_3231_ = lean_apply_6(v_msg_3191_, v_fst_3198_, v___y_3193_, v___y_3194_, v___y_3195_, v___y_3196_, lean_box(0));
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
v___y_3219_ = v_ref_3230_;
v_a_3220_ = v_a_3232_;
goto v___jp_3218_;
}
else
{
lean_object* v___x_3233_; 
lean_dec_ref_known(v___x_3231_, 1);
v___x_3233_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__2);
v___y_3219_ = v_ref_3230_;
v_a_3220_ = v___x_3233_;
goto v___jp_3218_;
}
}
v___jp_3234_:
{
if (v_clsEnabled_3189_ == 0)
{
if (v___y_3235_ == 0)
{
lean_object* v___x_3236_; lean_object* v_traceState_3237_; lean_object* v_env_3238_; lean_object* v_nextMacroScope_3239_; lean_object* v_ngen_3240_; lean_object* v_auxDeclNGen_3241_; lean_object* v_cache_3242_; lean_object* v_recordedDeps_3243_; lean_object* v_messages_3244_; lean_object* v_infoState_3245_; lean_object* v_snapshotTasks_3246_; lean_object* v___x_3248_; uint8_t v_isShared_3249_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_snd_3215_);
lean_dec(v_fst_3214_);
lean_dec_ref(v_msg_3191_);
lean_dec_ref(v_tag_3187_);
lean_dec(v_cls_3185_);
v___x_3236_ = lean_st_ref_take(v___y_3196_);
v_traceState_3237_ = lean_ctor_get(v___x_3236_, 4);
v_env_3238_ = lean_ctor_get(v___x_3236_, 0);
v_nextMacroScope_3239_ = lean_ctor_get(v___x_3236_, 1);
v_ngen_3240_ = lean_ctor_get(v___x_3236_, 2);
v_auxDeclNGen_3241_ = lean_ctor_get(v___x_3236_, 3);
v_cache_3242_ = lean_ctor_get(v___x_3236_, 5);
v_recordedDeps_3243_ = lean_ctor_get(v___x_3236_, 6);
v_messages_3244_ = lean_ctor_get(v___x_3236_, 7);
v_infoState_3245_ = lean_ctor_get(v___x_3236_, 8);
v_snapshotTasks_3246_ = lean_ctor_get(v___x_3236_, 9);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3236_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3248_ = v___x_3236_;
v_isShared_3249_ = v_isSharedCheck_3265_;
goto v_resetjp_3247_;
}
else
{
lean_inc(v_snapshotTasks_3246_);
lean_inc(v_infoState_3245_);
lean_inc(v_messages_3244_);
lean_inc(v_recordedDeps_3243_);
lean_inc(v_cache_3242_);
lean_inc(v_traceState_3237_);
lean_inc(v_auxDeclNGen_3241_);
lean_inc(v_ngen_3240_);
lean_inc(v_nextMacroScope_3239_);
lean_inc(v_env_3238_);
lean_dec(v___x_3236_);
v___x_3248_ = lean_box(0);
v_isShared_3249_ = v_isSharedCheck_3265_;
goto v_resetjp_3247_;
}
v_resetjp_3247_:
{
uint64_t v_tid_3250_; lean_object* v_traces_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3264_; 
v_tid_3250_ = lean_ctor_get_uint64(v_traceState_3237_, sizeof(void*)*1);
v_traces_3251_ = lean_ctor_get(v_traceState_3237_, 0);
v_isSharedCheck_3264_ = !lean_is_exclusive(v_traceState_3237_);
if (v_isSharedCheck_3264_ == 0)
{
v___x_3253_ = v_traceState_3237_;
v_isShared_3254_ = v_isSharedCheck_3264_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_traces_3251_);
lean_dec(v_traceState_3237_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3264_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3255_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3190_, v_traces_3251_);
lean_dec_ref(v_traces_3251_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3255_);
v___x_3257_ = v___x_3253_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3263_; 
v_reuseFailAlloc_3263_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3263_, 0, v___x_3255_);
lean_ctor_set_uint64(v_reuseFailAlloc_3263_, sizeof(void*)*1, v_tid_3250_);
v___x_3257_ = v_reuseFailAlloc_3263_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
lean_object* v___x_3259_; 
if (v_isShared_3249_ == 0)
{
lean_ctor_set(v___x_3248_, 4, v___x_3257_);
v___x_3259_ = v___x_3248_;
goto v_reusejp_3258_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_env_3238_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v_nextMacroScope_3239_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_ngen_3240_);
lean_ctor_set(v_reuseFailAlloc_3262_, 3, v_auxDeclNGen_3241_);
lean_ctor_set(v_reuseFailAlloc_3262_, 4, v___x_3257_);
lean_ctor_set(v_reuseFailAlloc_3262_, 5, v_cache_3242_);
lean_ctor_set(v_reuseFailAlloc_3262_, 6, v_recordedDeps_3243_);
lean_ctor_set(v_reuseFailAlloc_3262_, 7, v_messages_3244_);
lean_ctor_set(v_reuseFailAlloc_3262_, 8, v_infoState_3245_);
lean_ctor_set(v_reuseFailAlloc_3262_, 9, v_snapshotTasks_3246_);
v___x_3259_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3258_;
}
v_reusejp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = lean_st_ref_put(v___y_3196_, v___x_3259_);
v___x_3261_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_fst_3198_);
return v___x_3261_;
}
}
}
}
}
else
{
goto v___jp_3229_;
}
}
else
{
goto v___jp_3229_;
}
}
v___jp_3266_:
{
double v___x_3268_; double v___x_3269_; double v___x_3270_; uint8_t v___x_3271_; 
v___x_3268_ = lean_unbox_float(v_snd_3215_);
v___x_3269_ = lean_unbox_float(v_fst_3214_);
v___x_3270_ = lean_float_sub(v___x_3268_, v___x_3269_);
v___x_3271_ = lean_float_decLt(v___y_3267_, v___x_3270_);
v___y_3235_ = v___x_3271_;
goto v___jp_3234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___boxed(lean_object* v_cls_3282_, lean_object* v_collapsed_3283_, lean_object* v_tag_3284_, lean_object* v_opts_3285_, lean_object* v_clsEnabled_3286_, lean_object* v_oldTraces_3287_, lean_object* v_msg_3288_, lean_object* v_resStartStop_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_){
_start:
{
uint8_t v_collapsed_boxed_3295_; uint8_t v_clsEnabled_boxed_3296_; lean_object* v_res_3297_; 
v_collapsed_boxed_3295_ = lean_unbox(v_collapsed_3283_);
v_clsEnabled_boxed_3296_ = lean_unbox(v_clsEnabled_3286_);
v_res_3297_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v_cls_3282_, v_collapsed_boxed_3295_, v_tag_3284_, v_opts_3285_, v_clsEnabled_boxed_3296_, v_oldTraces_3287_, v_msg_3288_, v_resStartStop_3289_, v___y_3290_, v___y_3291_, v___y_3292_, v___y_3293_);
lean_dec(v___y_3293_);
lean_dec_ref(v___y_3292_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v_opts_3285_);
return v_res_3297_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(lean_object* v_a_3298_, lean_object* v_a_3299_){
_start:
{
if (lean_obj_tag(v_a_3298_) == 0)
{
lean_object* v___x_3300_; 
v___x_3300_ = l_List_reverse___redArg(v_a_3299_);
return v___x_3300_;
}
else
{
lean_object* v_head_3301_; lean_object* v_tail_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3311_; 
v_head_3301_ = lean_ctor_get(v_a_3298_, 0);
v_tail_3302_ = lean_ctor_get(v_a_3298_, 1);
v_isSharedCheck_3311_ = !lean_is_exclusive(v_a_3298_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3304_ = v_a_3298_;
v_isShared_3305_ = v_isSharedCheck_3311_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_tail_3302_);
lean_inc(v_head_3301_);
lean_dec(v_a_3298_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3311_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3306_ = l_Lean_MessageData_ofExpr(v_head_3301_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 1, v_a_3299_);
lean_ctor_set(v___x_3304_, 0, v___x_3306_);
v___x_3308_ = v___x_3304_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_a_3299_);
v___x_3308_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
v_a_3298_ = v_tail_3302_;
v_a_3299_ = v___x_3308_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(lean_object* v_f_3312_, lean_object* v_xs_3313_, lean_object* v_x_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v___x_3320_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3321_ = l_Lean_MessageData_ofName(v_f_3312_);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3322_);
lean_ctor_set(v___x_3324_, 1, v___x_3323_);
v___x_3325_ = lean_array_to_list(v_xs_3313_);
v___x_3326_ = lean_box(0);
v___x_3327_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3325_, v___x_3326_);
v___x_3328_ = l_Lean_MessageData_ofList(v___x_3327_);
v___x_3329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3324_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed(lean_object* v_f_3331_, lean_object* v_xs_3332_, lean_object* v_x_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_res_3339_; 
v_res_3339_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0(v_f_3331_, v_xs_3332_, v_x_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec_ref(v_x_3333_);
return v_res_3339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(lean_object* v_cls_3342_, lean_object* v_msg_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v_ref_3349_; lean_object* v___x_3350_; lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3396_; 
v_ref_3349_ = lean_ctor_get(v___y_3346_, 2);
v___x_3350_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0_spec__0(v_msg_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3353_ = v___x_3350_;
v_isShared_3354_ = v_isSharedCheck_3396_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3350_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3396_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3355_; lean_object* v_traceState_3356_; lean_object* v_env_3357_; lean_object* v_nextMacroScope_3358_; lean_object* v_ngen_3359_; lean_object* v_auxDeclNGen_3360_; lean_object* v_cache_3361_; lean_object* v_recordedDeps_3362_; lean_object* v_messages_3363_; lean_object* v_infoState_3364_; lean_object* v_snapshotTasks_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3395_; 
v___x_3355_ = lean_st_ref_take(v___y_3347_);
v_traceState_3356_ = lean_ctor_get(v___x_3355_, 4);
v_env_3357_ = lean_ctor_get(v___x_3355_, 0);
v_nextMacroScope_3358_ = lean_ctor_get(v___x_3355_, 1);
v_ngen_3359_ = lean_ctor_get(v___x_3355_, 2);
v_auxDeclNGen_3360_ = lean_ctor_get(v___x_3355_, 3);
v_cache_3361_ = lean_ctor_get(v___x_3355_, 5);
v_recordedDeps_3362_ = lean_ctor_get(v___x_3355_, 6);
v_messages_3363_ = lean_ctor_get(v___x_3355_, 7);
v_infoState_3364_ = lean_ctor_get(v___x_3355_, 8);
v_snapshotTasks_3365_ = lean_ctor_get(v___x_3355_, 9);
v_isSharedCheck_3395_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3395_ == 0)
{
v___x_3367_ = v___x_3355_;
v_isShared_3368_ = v_isSharedCheck_3395_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_snapshotTasks_3365_);
lean_inc(v_infoState_3364_);
lean_inc(v_messages_3363_);
lean_inc(v_recordedDeps_3362_);
lean_inc(v_cache_3361_);
lean_inc(v_traceState_3356_);
lean_inc(v_auxDeclNGen_3360_);
lean_inc(v_ngen_3359_);
lean_inc(v_nextMacroScope_3358_);
lean_inc(v_env_3357_);
lean_dec(v___x_3355_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3395_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
uint64_t v_tid_3369_; lean_object* v_traces_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3394_; 
v_tid_3369_ = lean_ctor_get_uint64(v_traceState_3356_, sizeof(void*)*1);
v_traces_3370_ = lean_ctor_get(v_traceState_3356_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v_traceState_3356_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3372_ = v_traceState_3356_;
v_isShared_3373_ = v_isSharedCheck_3394_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_traces_3370_);
lean_dec(v_traceState_3356_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3394_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; double v___x_3376_; uint8_t v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3385_; 
v___x_3374_ = lean_box(0);
v___x_3375_ = lean_box(0);
v___x_3376_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5___closed__0);
v___x_3377_ = 0;
v___x_3378_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3379_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3379_, 0, v_cls_3342_);
lean_ctor_set(v___x_3379_, 1, v___x_3375_);
lean_ctor_set(v___x_3379_, 2, v___x_3378_);
lean_ctor_set_float(v___x_3379_, sizeof(void*)*3, v___x_3376_);
lean_ctor_set_float(v___x_3379_, sizeof(void*)*3 + 8, v___x_3376_);
lean_ctor_set_uint8(v___x_3379_, sizeof(void*)*3 + 16, v___x_3377_);
v___x_3380_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___closed__0));
v___x_3381_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3379_);
lean_ctor_set(v___x_3381_, 1, v_a_3351_);
lean_ctor_set(v___x_3381_, 2, v___x_3380_);
lean_inc(v_ref_3349_);
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v_ref_3349_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = l_Lean_PersistentArray_push___redArg(v_traces_3370_, v___x_3382_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3383_);
v___x_3385_ = v___x_3372_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3383_);
lean_ctor_set_uint64(v_reuseFailAlloc_3393_, sizeof(void*)*1, v_tid_3369_);
v___x_3385_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3387_; 
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 4, v___x_3385_);
v___x_3387_ = v___x_3367_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_env_3357_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v_nextMacroScope_3358_);
lean_ctor_set(v_reuseFailAlloc_3392_, 2, v_ngen_3359_);
lean_ctor_set(v_reuseFailAlloc_3392_, 3, v_auxDeclNGen_3360_);
lean_ctor_set(v_reuseFailAlloc_3392_, 4, v___x_3385_);
lean_ctor_set(v_reuseFailAlloc_3392_, 5, v_cache_3361_);
lean_ctor_set(v_reuseFailAlloc_3392_, 6, v_recordedDeps_3362_);
lean_ctor_set(v_reuseFailAlloc_3392_, 7, v_messages_3363_);
lean_ctor_set(v_reuseFailAlloc_3392_, 8, v_infoState_3364_);
lean_ctor_set(v_reuseFailAlloc_3392_, 9, v_snapshotTasks_3365_);
v___x_3387_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3388_; lean_object* v___x_3390_; 
v___x_3388_ = lean_st_ref_put(v___y_3347_, v___x_3387_);
if (v_isShared_3354_ == 0)
{
lean_ctor_set(v___x_3353_, 0, v___x_3374_);
v___x_3390_ = v___x_3353_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3374_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2___boxed(lean_object* v_cls_3397_, lean_object* v_msg_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_res_3404_; 
v_res_3404_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v_cls_3397_, v_msg_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
return v_res_3404_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(lean_object* v_f_3405_, lean_object* v_xs_3406_, lean_object* v_k_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_){
_start:
{
lean_object* v_toCold_3413_; lean_object* v_options_3414_; uint8_t v_hasTrace_3415_; 
v_toCold_3413_ = lean_ctor_get(v_a_3410_, 0);
v_options_3414_ = lean_ctor_get(v_toCold_3413_, 2);
v_hasTrace_3415_ = lean_ctor_get_uint8(v_options_3414_, sizeof(void*)*1);
if (v_hasTrace_3415_ == 0)
{
lean_object* v___x_3416_; 
lean_dec_ref(v_xs_3406_);
lean_dec(v_f_3405_);
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
lean_inc(v_a_3409_);
lean_inc_ref(v_a_3408_);
v___x_3416_ = lean_apply_5(v_k_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, lean_box(0));
return v___x_3416_;
}
else
{
lean_object* v_inheritedTraceOptions_3417_; lean_object* v___f_3418_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; lean_object* v___y_3446_; lean_object* v_a_3447_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; uint8_t v___x_3453_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v_a_3457_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v_a_3472_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; uint8_t v___y_3478_; lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v_a_3488_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v_a_3494_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v_a_3499_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v_a_3511_; lean_object* v___y_3514_; lean_object* v___y_3515_; lean_object* v___y_3516_; uint8_t v___y_3517_; lean_object* v___y_3525_; lean_object* v___y_3526_; lean_object* v_a_3527_; lean_object* v___y_3531_; lean_object* v___y_3532_; lean_object* v_a_3533_; 
v_inheritedTraceOptions_3417_ = lean_ctor_get(v_toCold_3413_, 11);
v___f_3418_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3418_, 0, v_f_3405_);
lean_closure_set(v___f_3418_, 1, v_xs_3406_);
v___x_3450_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3451_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3452_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3453_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3414_, v___x_3452_);
if (v___x_3453_ == 0)
{
lean_object* v___x_3560_; uint8_t v___x_3561_; 
v___x_3560_ = l_Lean_trace_profiler;
v___x_3561_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3414_, v___x_3560_);
if (v___x_3561_ == 0)
{
lean_object* v___x_3562_; 
lean_dec_ref(v___f_3418_);
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
lean_inc(v_a_3409_);
lean_inc_ref(v_a_3408_);
v___x_3562_ = lean_apply_5(v_k_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, lean_box(0));
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; uint8_t v___x_3566_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3563_);
v___x_3564_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3565_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3566_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3414_, v___x_3565_);
if (v___x_3566_ == 0)
{
lean_dec(v_a_3563_);
return v___x_3562_;
}
else
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
lean_dec_ref_known(v___x_3562_, 1);
lean_inc(v_a_3563_);
v___x_3567_ = l_Lean_MessageData_ofExpr(v_a_3563_);
v___x_3568_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3564_, v___x_3567_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v___x_3568_, 0);
lean_dec(v_unused_3576_);
v___x_3570_ = v___x_3568_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_dec(v___x_3568_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 0, v_a_3563_);
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3563_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_a_3563_);
v_a_3577_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3568_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3568_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
lean_inc(v_a_3577_);
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
v___y_3446_ = v___x_3582_;
v_a_3447_ = v_a_3577_;
goto v___jp_3445_;
}
}
}
}
}
else
{
lean_object* v_a_3585_; 
v_a_3585_ = lean_ctor_get(v___x_3562_, 0);
lean_inc(v_a_3585_);
v___y_3446_ = v___x_3562_;
v_a_3447_ = v_a_3585_;
goto v___jp_3445_;
}
}
else
{
goto v___jp_3535_;
}
}
else
{
goto v___jp_3535_;
}
v___jp_3419_:
{
if (v___y_3422_ == 0)
{
lean_object* v___x_3423_; lean_object* v___x_3424_; uint8_t v___x_3425_; 
lean_dec_ref(v___y_3421_);
v___x_3423_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3424_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3425_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3414_, v___x_3424_);
if (v___x_3425_ == 0)
{
lean_object* v___x_3426_; 
v___x_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3426_, 0, v___y_3420_);
return v___x_3426_;
}
else
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
lean_inc_ref(v___y_3420_);
v___x_3427_ = l_Lean_Exception_toMessageData(v___y_3420_);
v___x_3428_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3423_, v___x_3427_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3435_ == 0)
{
lean_object* v_unused_3436_; 
v_unused_3436_ = lean_ctor_get(v___x_3428_, 0);
lean_dec(v_unused_3436_);
v___x_3430_ = v___x_3428_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_dec(v___x_3428_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
lean_ctor_set_tag(v___x_3430_, 1);
lean_ctor_set(v___x_3430_, 0, v___y_3420_);
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v___y_3420_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec_ref(v___y_3420_);
v_a_3437_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3428_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3428_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3420_);
return v___y_3421_;
}
}
v___jp_3445_:
{
uint8_t v___x_3448_; 
v___x_3448_ = l_Lean_Exception_isInterrupt(v_a_3447_);
if (v___x_3448_ == 0)
{
uint8_t v___x_3449_; 
lean_inc_ref(v_a_3447_);
v___x_3449_ = l_Lean_Exception_isRuntime(v_a_3447_);
v___y_3420_ = v_a_3447_;
v___y_3421_ = v___y_3446_;
v___y_3422_ = v___x_3449_;
goto v___jp_3419_;
}
else
{
v___y_3420_ = v_a_3447_;
v___y_3421_ = v___y_3446_;
v___y_3422_ = v___x_3448_;
goto v___jp_3419_;
}
}
v___jp_3454_:
{
lean_object* v___x_3458_; double v___x_3459_; double v___x_3460_; double v___x_3461_; double v___x_3462_; double v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3458_ = lean_io_mono_nanos_now();
v___x_3459_ = lean_float_of_nat(v___y_3455_);
v___x_3460_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3461_ = lean_float_div(v___x_3459_, v___x_3460_);
v___x_3462_ = lean_float_of_nat(v___x_3458_);
v___x_3463_ = lean_float_div(v___x_3462_, v___x_3460_);
v___x_3464_ = lean_box_float(v___x_3461_);
v___x_3465_ = lean_box_float(v___x_3463_);
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v_a_3457_);
lean_ctor_set(v___x_3467_, 1, v___x_3466_);
v___x_3468_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3450_, v_hasTrace_3415_, v___x_3451_, v_options_3414_, v___x_3453_, v___y_3456_, v___f_3418_, v___x_3467_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
return v___x_3468_;
}
v___jp_3469_:
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3473_, 0, v_a_3472_);
v___y_3455_ = v___y_3470_;
v___y_3456_ = v___y_3471_;
v_a_3457_ = v___x_3473_;
goto v___jp_3454_;
}
v___jp_3474_:
{
if (v___y_3478_ == 0)
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3480_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3481_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3414_, v___x_3480_);
if (v___x_3481_ == 0)
{
v___y_3470_ = v___y_3475_;
v___y_3471_ = v___y_3476_;
v_a_3472_ = v___y_3477_;
goto v___jp_3469_;
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_inc_ref(v___y_3477_);
v___x_3482_ = l_Lean_Exception_toMessageData(v___y_3477_);
v___x_3483_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3479_, v___x_3482_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
if (lean_obj_tag(v___x_3483_) == 0)
{
lean_dec_ref_known(v___x_3483_, 1);
v___y_3470_ = v___y_3475_;
v___y_3471_ = v___y_3476_;
v_a_3472_ = v___y_3477_;
goto v___jp_3469_;
}
else
{
lean_object* v_a_3484_; 
lean_dec_ref(v___y_3477_);
v_a_3484_ = lean_ctor_get(v___x_3483_, 0);
lean_inc(v_a_3484_);
lean_dec_ref_known(v___x_3483_, 1);
v___y_3470_ = v___y_3475_;
v___y_3471_ = v___y_3476_;
v_a_3472_ = v_a_3484_;
goto v___jp_3469_;
}
}
}
else
{
v___y_3470_ = v___y_3475_;
v___y_3471_ = v___y_3476_;
v_a_3472_ = v___y_3477_;
goto v___jp_3469_;
}
}
v___jp_3485_:
{
uint8_t v___x_3489_; 
v___x_3489_ = l_Lean_Exception_isInterrupt(v_a_3488_);
if (v___x_3489_ == 0)
{
uint8_t v___x_3490_; 
lean_inc_ref(v_a_3488_);
v___x_3490_ = l_Lean_Exception_isRuntime(v_a_3488_);
v___y_3475_ = v___y_3486_;
v___y_3476_ = v___y_3487_;
v___y_3477_ = v_a_3488_;
v___y_3478_ = v___x_3490_;
goto v___jp_3474_;
}
else
{
v___y_3475_ = v___y_3486_;
v___y_3476_ = v___y_3487_;
v___y_3477_ = v_a_3488_;
v___y_3478_ = v___x_3489_;
goto v___jp_3474_;
}
}
v___jp_3491_:
{
lean_object* v___x_3495_; 
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_a_3494_);
v___y_3455_ = v___y_3492_;
v___y_3456_ = v___y_3493_;
v_a_3457_ = v___x_3495_;
goto v___jp_3454_;
}
v___jp_3496_:
{
lean_object* v___x_3500_; double v___x_3501_; double v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3507_; 
v___x_3500_ = lean_io_get_num_heartbeats();
v___x_3501_ = lean_float_of_nat(v___y_3497_);
v___x_3502_ = lean_float_of_nat(v___x_3500_);
v___x_3503_ = lean_box_float(v___x_3501_);
v___x_3504_ = lean_box_float(v___x_3502_);
v___x_3505_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3505_, 0, v___x_3503_);
lean_ctor_set(v___x_3505_, 1, v___x_3504_);
v___x_3506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3506_, 0, v_a_3499_);
lean_ctor_set(v___x_3506_, 1, v___x_3505_);
v___x_3507_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3450_, v_hasTrace_3415_, v___x_3451_, v_options_3414_, v___x_3453_, v___y_3498_, v___f_3418_, v___x_3506_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
return v___x_3507_;
}
v___jp_3508_:
{
lean_object* v___x_3512_; 
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v_a_3511_);
v___y_3497_ = v___y_3509_;
v___y_3498_ = v___y_3510_;
v_a_3499_ = v___x_3512_;
goto v___jp_3496_;
}
v___jp_3513_:
{
if (v___y_3517_ == 0)
{
lean_object* v___x_3518_; lean_object* v___x_3519_; uint8_t v___x_3520_; 
v___x_3518_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3519_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3520_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3414_, v___x_3519_);
if (v___x_3520_ == 0)
{
v___y_3509_ = v___y_3515_;
v___y_3510_ = v___y_3516_;
v_a_3511_ = v___y_3514_;
goto v___jp_3508_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
lean_inc_ref(v___y_3514_);
v___x_3521_ = l_Lean_Exception_toMessageData(v___y_3514_);
v___x_3522_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3518_, v___x_3521_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_dec_ref_known(v___x_3522_, 1);
v___y_3509_ = v___y_3515_;
v___y_3510_ = v___y_3516_;
v_a_3511_ = v___y_3514_;
goto v___jp_3508_;
}
else
{
lean_object* v_a_3523_; 
lean_dec_ref(v___y_3514_);
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
v___y_3509_ = v___y_3515_;
v___y_3510_ = v___y_3516_;
v_a_3511_ = v_a_3523_;
goto v___jp_3508_;
}
}
}
else
{
v___y_3509_ = v___y_3515_;
v___y_3510_ = v___y_3516_;
v_a_3511_ = v___y_3514_;
goto v___jp_3508_;
}
}
v___jp_3524_:
{
uint8_t v___x_3528_; 
v___x_3528_ = l_Lean_Exception_isInterrupt(v_a_3527_);
if (v___x_3528_ == 0)
{
uint8_t v___x_3529_; 
lean_inc_ref(v_a_3527_);
v___x_3529_ = l_Lean_Exception_isRuntime(v_a_3527_);
v___y_3514_ = v_a_3527_;
v___y_3515_ = v___y_3525_;
v___y_3516_ = v___y_3526_;
v___y_3517_ = v___x_3529_;
goto v___jp_3513_;
}
else
{
v___y_3514_ = v_a_3527_;
v___y_3515_ = v___y_3525_;
v___y_3516_ = v___y_3526_;
v___y_3517_ = v___x_3528_;
goto v___jp_3513_;
}
}
v___jp_3530_:
{
lean_object* v___x_3534_; 
v___x_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3534_, 0, v_a_3533_);
v___y_3497_ = v___y_3531_;
v___y_3498_ = v___y_3532_;
v_a_3499_ = v___x_3534_;
goto v___jp_3496_;
}
v___jp_3535_:
{
lean_object* v___x_3536_; lean_object* v_a_3537_; lean_object* v___x_3538_; uint8_t v___x_3539_; 
v___x_3536_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3411_);
v_a_3537_ = lean_ctor_get(v___x_3536_, 0);
lean_inc(v_a_3537_);
lean_dec_ref(v___x_3536_);
v___x_3538_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3539_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3414_, v___x_3538_);
if (v___x_3539_ == 0)
{
lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3540_ = lean_io_mono_nanos_now();
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
lean_inc(v_a_3409_);
lean_inc_ref(v_a_3408_);
v___x_3541_ = lean_apply_5(v_k_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, lean_box(0));
if (lean_obj_tag(v___x_3541_) == 0)
{
lean_object* v_a_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; uint8_t v___x_3545_; 
v_a_3542_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3542_);
lean_dec_ref_known(v___x_3541_, 1);
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3544_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3545_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3414_, v___x_3544_);
if (v___x_3545_ == 0)
{
v___y_3492_ = v___x_3540_;
v___y_3493_ = v_a_3537_;
v_a_3494_ = v_a_3542_;
goto v___jp_3491_;
}
else
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
lean_inc(v_a_3542_);
v___x_3546_ = l_Lean_MessageData_ofExpr(v_a_3542_);
v___x_3547_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3543_, v___x_3546_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
if (lean_obj_tag(v___x_3547_) == 0)
{
lean_dec_ref_known(v___x_3547_, 1);
v___y_3492_ = v___x_3540_;
v___y_3493_ = v_a_3537_;
v_a_3494_ = v_a_3542_;
goto v___jp_3491_;
}
else
{
lean_object* v_a_3548_; 
lean_dec(v_a_3542_);
v_a_3548_ = lean_ctor_get(v___x_3547_, 0);
lean_inc(v_a_3548_);
lean_dec_ref_known(v___x_3547_, 1);
v___y_3486_ = v___x_3540_;
v___y_3487_ = v_a_3537_;
v_a_3488_ = v_a_3548_;
goto v___jp_3485_;
}
}
}
else
{
lean_object* v_a_3549_; 
v_a_3549_ = lean_ctor_get(v___x_3541_, 0);
lean_inc(v_a_3549_);
lean_dec_ref_known(v___x_3541_, 1);
v___y_3486_ = v___x_3540_;
v___y_3487_ = v_a_3537_;
v_a_3488_ = v_a_3549_;
goto v___jp_3485_;
}
}
else
{
lean_object* v___x_3550_; lean_object* v___x_3551_; 
v___x_3550_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3411_);
lean_inc_ref(v_a_3410_);
lean_inc(v_a_3409_);
lean_inc_ref(v_a_3408_);
v___x_3551_ = lean_apply_5(v_k_3407_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_, lean_box(0));
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; uint8_t v___x_3555_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3552_);
lean_dec_ref_known(v___x_3551_, 1);
v___x_3553_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3554_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3555_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3417_, v_options_3414_, v___x_3554_);
if (v___x_3555_ == 0)
{
v___y_3531_ = v___x_3550_;
v___y_3532_ = v_a_3537_;
v_a_3533_ = v_a_3552_;
goto v___jp_3530_;
}
else
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
lean_inc(v_a_3552_);
v___x_3556_ = l_Lean_MessageData_ofExpr(v_a_3552_);
v___x_3557_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3553_, v___x_3556_, v_a_3408_, v_a_3409_, v_a_3410_, v_a_3411_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_dec_ref_known(v___x_3557_, 1);
v___y_3531_ = v___x_3550_;
v___y_3532_ = v_a_3537_;
v_a_3533_ = v_a_3552_;
goto v___jp_3530_;
}
else
{
lean_object* v_a_3558_; 
lean_dec(v_a_3552_);
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
v___y_3525_ = v___x_3550_;
v___y_3526_ = v_a_3537_;
v_a_3527_ = v_a_3558_;
goto v___jp_3524_;
}
}
}
else
{
lean_object* v_a_3559_; 
v_a_3559_ = lean_ctor_get(v___x_3551_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3551_, 1);
v___y_3525_ = v___x_3550_;
v___y_3526_ = v_a_3537_;
v_a_3527_ = v_a_3559_;
goto v___jp_3524_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1___boxed(lean_object* v_f_3586_, lean_object* v_xs_3587_, lean_object* v_k_3588_, lean_object* v_a_3589_, lean_object* v_a_3590_, lean_object* v_a_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_){
_start:
{
lean_object* v_res_3594_; 
v_res_3594_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_f_3586_, v_xs_3587_, v_k_3588_, v_a_3589_, v_a_3590_, v_a_3591_, v_a_3592_);
lean_dec(v_a_3592_);
lean_dec_ref(v_a_3591_);
lean_dec(v_a_3590_);
lean_dec_ref(v_a_3589_);
return v_res_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM(lean_object* v_constName_3595_, lean_object* v_xs_3596_, lean_object* v_a_3597_, lean_object* v_a_3598_, lean_object* v_a_3599_, lean_object* v_a_3600_){
_start:
{
lean_object* v___f_3602_; uint8_t v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
lean_inc_ref(v_xs_3596_);
lean_inc(v_constName_3595_);
v___f_3602_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3602_, 0, v_constName_3595_);
lean_closure_set(v___f_3602_, 1, v_xs_3596_);
v___x_3603_ = 0;
v___x_3604_ = lean_box(v___x_3603_);
v___x_3605_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3605_, 0, lean_box(0));
lean_closure_set(v___x_3605_, 1, v___f_3602_);
lean_closure_set(v___x_3605_, 2, v___x_3604_);
v___x_3606_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1(v_constName_3595_, v_xs_3596_, v___x_3605_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM___boxed(lean_object* v_constName_3607_, lean_object* v_xs_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_, lean_object* v_a_3612_, lean_object* v_a_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_Meta_mkAppM(v_constName_3607_, v_xs_3608_, v_a_3609_, v_a_3610_, v_a_3611_, v_a_3612_);
lean_dec(v_a_3612_);
lean_dec_ref(v_a_3611_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v___x_3620_; 
v___x_3620_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v___y_3618_);
return v___x_3620_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___boxed(lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_res_3626_; 
v_res_3626_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3(v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
lean_dec(v___y_3624_);
lean_dec_ref(v___y_3623_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(lean_object* v_00_u03b1_3627_, lean_object* v_x_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
lean_object* v___x_3634_; 
v___x_3634_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___redArg(v_x_3628_);
return v___x_3634_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7___boxed(lean_object* v_00_u03b1_3635_, lean_object* v_x_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
lean_object* v_res_3642_; 
v_res_3642_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5_spec__7(v_00_u03b1_3635_, v_x_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
return v_res_3642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(lean_object* v_f_3643_, lean_object* v_xs_3644_, lean_object* v_x_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_){
_start:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3651_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_3652_ = l_Lean_MessageData_ofExpr(v_f_3643_);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3653_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_array_to_list(v_xs_3644_);
v___x_3657_ = lean_box(0);
v___x_3658_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__1(v___x_3656_, v___x_3657_);
v___x_3659_ = l_Lean_MessageData_ofList(v___x_3658_);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3655_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3660_);
return v___x_3661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed(lean_object* v_f_3662_, lean_object* v_xs_3663_, lean_object* v_x_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_){
_start:
{
lean_object* v_res_3670_; 
v_res_3670_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0(v_f_3662_, v_xs_3663_, v_x_3664_, v___y_3665_, v___y_3666_, v___y_3667_, v___y_3668_);
lean_dec(v___y_3668_);
lean_dec_ref(v___y_3667_);
lean_dec(v___y_3666_);
lean_dec_ref(v___y_3665_);
lean_dec_ref(v_x_3664_);
return v_res_3670_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(lean_object* v_f_3671_, lean_object* v_xs_3672_, lean_object* v_k_3673_, lean_object* v_a_3674_, lean_object* v_a_3675_, lean_object* v_a_3676_, lean_object* v_a_3677_){
_start:
{
lean_object* v_toCold_3679_; lean_object* v_options_3680_; uint8_t v_hasTrace_3681_; 
v_toCold_3679_ = lean_ctor_get(v_a_3676_, 0);
v_options_3680_ = lean_ctor_get(v_toCold_3679_, 2);
v_hasTrace_3681_ = lean_ctor_get_uint8(v_options_3680_, sizeof(void*)*1);
if (v_hasTrace_3681_ == 0)
{
lean_object* v___x_3682_; 
lean_dec_ref(v_xs_3672_);
lean_dec_ref(v_f_3671_);
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
lean_inc(v_a_3675_);
lean_inc_ref(v_a_3674_);
v___x_3682_ = lean_apply_5(v_k_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, lean_box(0));
return v___x_3682_;
}
else
{
lean_object* v_inheritedTraceOptions_3683_; lean_object* v___f_3684_; lean_object* v___y_3686_; lean_object* v___y_3687_; uint8_t v___y_3688_; lean_object* v___y_3712_; lean_object* v_a_3713_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; lean_object* v___y_3721_; lean_object* v___y_3722_; lean_object* v_a_3723_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v_a_3738_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; uint8_t v___y_3744_; lean_object* v___y_3752_; lean_object* v___y_3753_; lean_object* v_a_3754_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_a_3760_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_a_3765_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v_a_3777_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; uint8_t v___y_3783_; lean_object* v___y_3791_; lean_object* v___y_3792_; lean_object* v_a_3793_; lean_object* v___y_3797_; lean_object* v___y_3798_; lean_object* v_a_3799_; 
v_inheritedTraceOptions_3683_ = lean_ctor_get(v_toCold_3679_, 11);
v___f_3684_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3684_, 0, v_f_3671_);
lean_closure_set(v___f_3684_, 1, v_xs_3672_);
v___x_3716_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_3717_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_3718_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_3719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3680_, v___x_3718_);
if (v___x_3719_ == 0)
{
lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = l_Lean_trace_profiler;
v___x_3827_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3680_, v___x_3826_);
if (v___x_3827_ == 0)
{
lean_object* v___x_3828_; 
lean_dec_ref(v___f_3684_);
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
lean_inc(v_a_3675_);
lean_inc_ref(v_a_3674_);
v___x_3828_ = lean_apply_5(v_k_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, lean_box(0));
if (lean_obj_tag(v___x_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; uint8_t v___x_3832_; 
v_a_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3829_);
v___x_3830_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3831_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3832_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3680_, v___x_3831_);
if (v___x_3832_ == 0)
{
lean_dec(v_a_3829_);
return v___x_3828_;
}
else
{
lean_object* v___x_3833_; lean_object* v___x_3834_; 
lean_dec_ref_known(v___x_3828_, 1);
lean_inc(v_a_3829_);
v___x_3833_ = l_Lean_MessageData_ofExpr(v_a_3829_);
v___x_3834_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3830_, v___x_3833_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3841_; 
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3841_ == 0)
{
lean_object* v_unused_3842_; 
v_unused_3842_ = lean_ctor_get(v___x_3834_, 0);
lean_dec(v_unused_3842_);
v___x_3836_ = v___x_3834_;
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
else
{
lean_dec(v___x_3834_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3841_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v___x_3839_; 
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v_a_3829_);
v___x_3839_ = v___x_3836_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v_a_3829_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
else
{
lean_object* v_a_3843_; lean_object* v___x_3845_; uint8_t v_isShared_3846_; uint8_t v_isSharedCheck_3850_; 
lean_dec(v_a_3829_);
v_a_3843_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3850_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3850_ == 0)
{
v___x_3845_ = v___x_3834_;
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
else
{
lean_inc(v_a_3843_);
lean_dec(v___x_3834_);
v___x_3845_ = lean_box(0);
v_isShared_3846_ = v_isSharedCheck_3850_;
goto v_resetjp_3844_;
}
v_resetjp_3844_:
{
lean_object* v___x_3848_; 
lean_inc(v_a_3843_);
if (v_isShared_3846_ == 0)
{
v___x_3848_ = v___x_3845_;
goto v_reusejp_3847_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v_a_3843_);
v___x_3848_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3847_;
}
v_reusejp_3847_:
{
v___y_3712_ = v___x_3848_;
v_a_3713_ = v_a_3843_;
goto v___jp_3711_;
}
}
}
}
}
else
{
lean_object* v_a_3851_; 
v_a_3851_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_a_3851_);
v___y_3712_ = v___x_3828_;
v_a_3713_ = v_a_3851_;
goto v___jp_3711_;
}
}
else
{
goto v___jp_3801_;
}
}
else
{
goto v___jp_3801_;
}
v___jp_3685_:
{
if (v___y_3688_ == 0)
{
lean_object* v___x_3689_; lean_object* v___x_3690_; uint8_t v___x_3691_; 
lean_dec_ref(v___y_3687_);
v___x_3689_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3690_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3691_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3680_, v___x_3690_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___y_3686_);
return v___x_3692_;
}
else
{
lean_object* v___x_3693_; lean_object* v___x_3694_; 
lean_inc_ref(v___y_3686_);
v___x_3693_ = l_Lean_Exception_toMessageData(v___y_3686_);
v___x_3694_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3689_, v___x_3693_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v___x_3694_, 0);
lean_dec(v_unused_3702_);
v___x_3696_ = v___x_3694_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_dec(v___x_3694_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
lean_ctor_set_tag(v___x_3696_, 1);
lean_ctor_set(v___x_3696_, 0, v___y_3686_);
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v___y_3686_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v___y_3686_);
v_a_3703_ = lean_ctor_get(v___x_3694_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3694_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3694_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3694_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_3686_);
return v___y_3687_;
}
}
v___jp_3711_:
{
uint8_t v___x_3714_; 
v___x_3714_ = l_Lean_Exception_isInterrupt(v_a_3713_);
if (v___x_3714_ == 0)
{
uint8_t v___x_3715_; 
lean_inc_ref(v_a_3713_);
v___x_3715_ = l_Lean_Exception_isRuntime(v_a_3713_);
v___y_3686_ = v_a_3713_;
v___y_3687_ = v___y_3712_;
v___y_3688_ = v___x_3715_;
goto v___jp_3685_;
}
else
{
v___y_3686_ = v_a_3713_;
v___y_3687_ = v___y_3712_;
v___y_3688_ = v___x_3714_;
goto v___jp_3685_;
}
}
v___jp_3720_:
{
lean_object* v___x_3724_; double v___x_3725_; double v___x_3726_; double v___x_3727_; double v___x_3728_; double v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3724_ = lean_io_mono_nanos_now();
v___x_3725_ = lean_float_of_nat(v___y_3722_);
v___x_3726_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_3727_ = lean_float_div(v___x_3725_, v___x_3726_);
v___x_3728_ = lean_float_of_nat(v___x_3724_);
v___x_3729_ = lean_float_div(v___x_3728_, v___x_3726_);
v___x_3730_ = lean_box_float(v___x_3727_);
v___x_3731_ = lean_box_float(v___x_3729_);
v___x_3732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3731_);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v_a_3723_);
lean_ctor_set(v___x_3733_, 1, v___x_3732_);
v___x_3734_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3716_, v_hasTrace_3681_, v___x_3717_, v_options_3680_, v___x_3719_, v___y_3721_, v___f_3684_, v___x_3733_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3734_;
}
v___jp_3735_:
{
lean_object* v___x_3739_; 
v___x_3739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3739_, 0, v_a_3738_);
v___y_3721_ = v___y_3736_;
v___y_3722_ = v___y_3737_;
v_a_3723_ = v___x_3739_;
goto v___jp_3720_;
}
v___jp_3740_:
{
if (v___y_3744_ == 0)
{
lean_object* v___x_3745_; lean_object* v___x_3746_; uint8_t v___x_3747_; 
v___x_3745_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3746_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3747_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3680_, v___x_3746_);
if (v___x_3747_ == 0)
{
v___y_3736_ = v___y_3741_;
v___y_3737_ = v___y_3743_;
v_a_3738_ = v___y_3742_;
goto v___jp_3735_;
}
else
{
lean_object* v___x_3748_; lean_object* v___x_3749_; 
lean_inc_ref(v___y_3742_);
v___x_3748_ = l_Lean_Exception_toMessageData(v___y_3742_);
v___x_3749_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3745_, v___x_3748_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_dec_ref_known(v___x_3749_, 1);
v___y_3736_ = v___y_3741_;
v___y_3737_ = v___y_3743_;
v_a_3738_ = v___y_3742_;
goto v___jp_3735_;
}
else
{
lean_object* v_a_3750_; 
lean_dec_ref(v___y_3742_);
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v___x_3749_, 1);
v___y_3736_ = v___y_3741_;
v___y_3737_ = v___y_3743_;
v_a_3738_ = v_a_3750_;
goto v___jp_3735_;
}
}
}
else
{
v___y_3736_ = v___y_3741_;
v___y_3737_ = v___y_3743_;
v_a_3738_ = v___y_3742_;
goto v___jp_3735_;
}
}
v___jp_3751_:
{
uint8_t v___x_3755_; 
v___x_3755_ = l_Lean_Exception_isInterrupt(v_a_3754_);
if (v___x_3755_ == 0)
{
uint8_t v___x_3756_; 
lean_inc_ref(v_a_3754_);
v___x_3756_ = l_Lean_Exception_isRuntime(v_a_3754_);
v___y_3741_ = v___y_3752_;
v___y_3742_ = v_a_3754_;
v___y_3743_ = v___y_3753_;
v___y_3744_ = v___x_3756_;
goto v___jp_3740_;
}
else
{
v___y_3741_ = v___y_3752_;
v___y_3742_ = v_a_3754_;
v___y_3743_ = v___y_3753_;
v___y_3744_ = v___x_3755_;
goto v___jp_3740_;
}
}
v___jp_3757_:
{
lean_object* v___x_3761_; 
v___x_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3761_, 0, v_a_3760_);
v___y_3721_ = v___y_3758_;
v___y_3722_ = v___y_3759_;
v_a_3723_ = v___x_3761_;
goto v___jp_3720_;
}
v___jp_3762_:
{
lean_object* v___x_3766_; double v___x_3767_; double v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3766_ = lean_io_get_num_heartbeats();
v___x_3767_ = lean_float_of_nat(v___y_3764_);
v___x_3768_ = lean_float_of_nat(v___x_3766_);
v___x_3769_ = lean_box_float(v___x_3767_);
v___x_3770_ = lean_box_float(v___x_3768_);
v___x_3771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3769_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3772_, 0, v_a_3765_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_3716_, v_hasTrace_3681_, v___x_3717_, v_options_3680_, v___x_3719_, v___y_3763_, v___f_3684_, v___x_3772_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
return v___x_3773_;
}
v___jp_3774_:
{
lean_object* v___x_3778_; 
v___x_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3778_, 0, v_a_3777_);
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v_a_3765_ = v___x_3778_;
goto v___jp_3762_;
}
v___jp_3779_:
{
if (v___y_3783_ == 0)
{
lean_object* v___x_3784_; lean_object* v___x_3785_; uint8_t v___x_3786_; 
v___x_3784_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_3785_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_3786_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3680_, v___x_3785_);
if (v___x_3786_ == 0)
{
v___y_3775_ = v___y_3780_;
v___y_3776_ = v___y_3781_;
v_a_3777_ = v___y_3782_;
goto v___jp_3774_;
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
lean_inc_ref(v___y_3782_);
v___x_3787_ = l_Lean_Exception_toMessageData(v___y_3782_);
v___x_3788_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3784_, v___x_3787_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3788_) == 0)
{
lean_dec_ref_known(v___x_3788_, 1);
v___y_3775_ = v___y_3780_;
v___y_3776_ = v___y_3781_;
v_a_3777_ = v___y_3782_;
goto v___jp_3774_;
}
else
{
lean_object* v_a_3789_; 
lean_dec_ref(v___y_3782_);
v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
lean_inc(v_a_3789_);
lean_dec_ref_known(v___x_3788_, 1);
v___y_3775_ = v___y_3780_;
v___y_3776_ = v___y_3781_;
v_a_3777_ = v_a_3789_;
goto v___jp_3774_;
}
}
}
else
{
v___y_3775_ = v___y_3780_;
v___y_3776_ = v___y_3781_;
v_a_3777_ = v___y_3782_;
goto v___jp_3774_;
}
}
v___jp_3790_:
{
uint8_t v___x_3794_; 
v___x_3794_ = l_Lean_Exception_isInterrupt(v_a_3793_);
if (v___x_3794_ == 0)
{
uint8_t v___x_3795_; 
lean_inc_ref(v_a_3793_);
v___x_3795_ = l_Lean_Exception_isRuntime(v_a_3793_);
v___y_3780_ = v___y_3791_;
v___y_3781_ = v___y_3792_;
v___y_3782_ = v_a_3793_;
v___y_3783_ = v___x_3795_;
goto v___jp_3779_;
}
else
{
v___y_3780_ = v___y_3791_;
v___y_3781_ = v___y_3792_;
v___y_3782_ = v_a_3793_;
v___y_3783_ = v___x_3794_;
goto v___jp_3779_;
}
}
v___jp_3796_:
{
lean_object* v___x_3800_; 
v___x_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3800_, 0, v_a_3799_);
v___y_3763_ = v___y_3797_;
v___y_3764_ = v___y_3798_;
v_a_3765_ = v___x_3800_;
goto v___jp_3762_;
}
v___jp_3801_:
{
lean_object* v___x_3802_; lean_object* v_a_3803_; lean_object* v___x_3804_; uint8_t v___x_3805_; 
v___x_3802_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_3677_);
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref(v___x_3802_);
v___x_3804_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3805_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_3680_, v___x_3804_);
if (v___x_3805_ == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3807_; 
v___x_3806_ = lean_io_mono_nanos_now();
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
lean_inc(v_a_3675_);
lean_inc_ref(v_a_3674_);
v___x_3807_ = lean_apply_5(v_k_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, lean_box(0));
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
v___x_3809_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3810_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3811_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3680_, v___x_3810_);
if (v___x_3811_ == 0)
{
v___y_3758_ = v_a_3803_;
v___y_3759_ = v___x_3806_;
v_a_3760_ = v_a_3808_;
goto v___jp_3757_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; 
lean_inc(v_a_3808_);
v___x_3812_ = l_Lean_MessageData_ofExpr(v_a_3808_);
v___x_3813_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3809_, v___x_3812_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_dec_ref_known(v___x_3813_, 1);
v___y_3758_ = v_a_3803_;
v___y_3759_ = v___x_3806_;
v_a_3760_ = v_a_3808_;
goto v___jp_3757_;
}
else
{
lean_object* v_a_3814_; 
lean_dec(v_a_3808_);
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v___y_3752_ = v_a_3803_;
v___y_3753_ = v___x_3806_;
v_a_3754_ = v_a_3814_;
goto v___jp_3751_;
}
}
}
else
{
lean_object* v_a_3815_; 
v_a_3815_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v___x_3807_, 1);
v___y_3752_ = v_a_3803_;
v___y_3753_ = v___x_3806_;
v_a_3754_ = v_a_3815_;
goto v___jp_3751_;
}
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3817_; 
v___x_3816_ = lean_io_get_num_heartbeats();
lean_inc(v_a_3677_);
lean_inc_ref(v_a_3676_);
lean_inc(v_a_3675_);
lean_inc_ref(v_a_3674_);
v___x_3817_ = lean_apply_5(v_k_3673_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_, lean_box(0));
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v_a_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; uint8_t v___x_3821_; 
v_a_3818_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3817_, 1);
v___x_3819_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_3820_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_3821_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3680_, v___x_3820_);
if (v___x_3821_ == 0)
{
v___y_3797_ = v_a_3803_;
v___y_3798_ = v___x_3816_;
v_a_3799_ = v_a_3818_;
goto v___jp_3796_;
}
else
{
lean_object* v___x_3822_; lean_object* v___x_3823_; 
lean_inc(v_a_3818_);
v___x_3822_ = l_Lean_MessageData_ofExpr(v_a_3818_);
v___x_3823_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_3819_, v___x_3822_, v_a_3674_, v_a_3675_, v_a_3676_, v_a_3677_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_dec_ref_known(v___x_3823_, 1);
v___y_3797_ = v_a_3803_;
v___y_3798_ = v___x_3816_;
v_a_3799_ = v_a_3818_;
goto v___jp_3796_;
}
else
{
lean_object* v_a_3824_; 
lean_dec(v_a_3818_);
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v___x_3823_, 1);
v___y_3791_ = v_a_3803_;
v___y_3792_ = v___x_3816_;
v_a_3793_ = v_a_3824_;
goto v___jp_3790_;
}
}
}
else
{
lean_object* v_a_3825_; 
v_a_3825_ = lean_ctor_get(v___x_3817_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3817_, 1);
v___y_3791_ = v_a_3803_;
v___y_3792_ = v___x_3816_;
v_a_3793_ = v_a_3825_;
goto v___jp_3790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0___boxed(lean_object* v_f_3852_, lean_object* v_xs_3853_, lean_object* v_k_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_){
_start:
{
lean_object* v_res_3860_; 
v_res_3860_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3852_, v_xs_3853_, v_k_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
lean_dec(v_a_3858_);
lean_dec_ref(v_a_3857_);
lean_dec(v_a_3856_);
lean_dec_ref(v_a_3855_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27(lean_object* v_f_3861_, lean_object* v_xs_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_){
_start:
{
lean_object* v___x_3868_; 
lean_inc(v_a_3866_);
lean_inc_ref(v_a_3865_);
lean_inc(v_a_3864_);
lean_inc_ref(v_a_3863_);
lean_inc_ref(v_f_3861_);
v___x_3868_ = lean_infer_type(v_f_3861_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3870_; uint8_t v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
lean_inc_ref(v_xs_3862_);
lean_inc_ref(v_f_3861_);
v___x_3870_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___boxed), 8, 3);
lean_closure_set(v___x_3870_, 0, v_f_3861_);
lean_closure_set(v___x_3870_, 1, v_a_3869_);
lean_closure_set(v___x_3870_, 2, v_xs_3862_);
v___x_3871_ = 0;
v___x_3872_ = lean_box(v___x_3871_);
v___x_3873_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_3873_, 0, lean_box(0));
lean_closure_set(v___x_3873_, 1, v___x_3870_);
lean_closure_set(v___x_3873_, 2, v___x_3872_);
v___x_3874_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_x27_spec__0(v_f_3861_, v_xs_3862_, v___x_3873_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_);
return v___x_3874_;
}
else
{
lean_dec_ref(v_xs_3862_);
lean_dec_ref(v_f_3861_);
return v___x_3868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppM_x27___boxed(lean_object* v_f_3875_, lean_object* v_xs_3876_, lean_object* v_a_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v_res_3882_; 
v_res_3882_ = l_Lean_Meta_mkAppM_x27(v_f_3875_, v_xs_3876_, v_a_3877_, v_a_3878_, v_a_3879_, v_a_3880_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3879_);
lean_dec(v_a_3878_);
lean_dec_ref(v_a_3877_);
return v_res_3882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(lean_object* v_as_3883_, size_t v_i_3884_, size_t v_stop_3885_, lean_object* v_b_3886_){
_start:
{
lean_object* v___y_3888_; uint8_t v___x_3892_; 
v___x_3892_ = lean_usize_dec_eq(v_i_3884_, v_stop_3885_);
if (v___x_3892_ == 0)
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_array_uget_borrowed(v_as_3883_, v_i_3884_);
if (lean_obj_tag(v___x_3893_) == 0)
{
v___y_3888_ = v_b_3886_;
goto v___jp_3887_;
}
else
{
lean_object* v_val_3894_; lean_object* v___x_3895_; 
v_val_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_val_3894_);
v___x_3895_ = lean_array_push(v_b_3886_, v_val_3894_);
v___y_3888_ = v___x_3895_;
goto v___jp_3887_;
}
}
else
{
return v_b_3886_;
}
v___jp_3887_:
{
size_t v___x_3889_; size_t v___x_3890_; 
v___x_3889_ = ((size_t)1ULL);
v___x_3890_ = lean_usize_add(v_i_3884_, v___x_3889_);
v_i_3884_ = v___x_3890_;
v_b_3886_ = v___y_3888_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0___boxed(lean_object* v_as_3896_, lean_object* v_i_3897_, lean_object* v_stop_3898_, lean_object* v_b_3899_){
_start:
{
size_t v_i_boxed_3900_; size_t v_stop_boxed_3901_; lean_object* v_res_3902_; 
v_i_boxed_3900_ = lean_unbox_usize(v_i_3897_);
lean_dec(v_i_3897_);
v_stop_boxed_3901_ = lean_unbox_usize(v_stop_3898_);
lean_dec(v_stop_3898_);
v_res_3902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_as_3896_, v_i_boxed_3900_, v_stop_boxed_3901_, v_b_3899_);
lean_dec_ref(v_as_3896_);
return v_res_3902_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4(void){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__3));
v___x_3910_ = l_Lean_MessageData_ofFormat(v___x_3909_);
return v___x_3910_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5(void){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; 
v___x_3911_ = lean_box(1);
v___x_3912_ = l_Lean_MessageData_ofFormat(v___x_3911_);
return v___x_3912_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__7));
v___x_3917_ = l_Lean_MessageData_ofFormat(v___x_3916_);
return v___x_3917_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(lean_object* v_f_3918_, lean_object* v_xs_3919_, lean_object* v_x_3920_, lean_object* v_x_3921_, lean_object* v_x_3922_, lean_object* v_x_3923_, lean_object* v_x_3924_, lean_object* v_a_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_){
_start:
{
if (lean_obj_tag(v_x_3924_) == 7)
{
lean_object* v_binderName_3930_; lean_object* v_binderType_3931_; lean_object* v_body_3932_; uint8_t v_binderInfo_3933_; lean_object* v___x_3934_; uint8_t v___x_3935_; 
v_binderName_3930_ = lean_ctor_get(v_x_3924_, 0);
lean_inc(v_binderName_3930_);
v_binderType_3931_ = lean_ctor_get(v_x_3924_, 1);
lean_inc_ref(v_binderType_3931_);
v_body_3932_ = lean_ctor_get(v_x_3924_, 2);
lean_inc_ref(v_body_3932_);
v_binderInfo_3933_ = lean_ctor_get_uint8(v_x_3924_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_x_3924_, 3);
v___x_3934_ = lean_array_get_size(v_xs_3919_);
v___x_3935_ = lean_nat_dec_lt(v_x_3920_, v___x_3934_);
if (v___x_3935_ == 0)
{
lean_object* v___x_3936_; lean_object* v___x_3937_; 
lean_dec_ref(v_body_3932_);
lean_dec_ref(v_binderType_3931_);
lean_dec(v_binderName_3930_);
lean_dec(v_x_3922_);
lean_dec(v_x_3920_);
v___x_3936_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3937_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_3936_, v_f_3918_, v_x_3921_, v_x_3923_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec_ref(v_x_3923_);
lean_dec_ref(v_x_3921_);
return v___x_3937_;
}
else
{
lean_object* v___x_3938_; lean_object* v_d_3939_; lean_object* v___x_3940_; 
v___x_3938_ = lean_array_get_size(v_x_3921_);
v_d_3939_ = lean_expr_instantiate_rev_range(v_binderType_3931_, v_x_3922_, v___x_3938_, v_x_3921_);
lean_dec_ref(v_binderType_3931_);
v___x_3940_ = lean_array_fget_borrowed(v_xs_3919_, v_x_3920_);
if (lean_obj_tag(v___x_3940_) == 0)
{
if (v_binderInfo_3933_ == 3)
{
lean_object* v___x_3941_; uint8_t v___x_3942_; lean_object* v___x_3943_; 
v___x_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3941_, 0, v_d_3939_);
v___x_3942_ = 1;
v___x_3943_ = l_Lean_Meta_mkFreshExprMVar(v___x_3941_, v___x_3942_, v_binderName_3930_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_object* v_a_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; 
v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
lean_inc_n(v_a_3944_, 2);
lean_dec_ref_known(v___x_3943_, 1);
v___x_3945_ = lean_unsigned_to_nat(1u);
v___x_3946_ = lean_nat_add(v_x_3920_, v___x_3945_);
lean_dec(v_x_3920_);
v___x_3947_ = lean_array_push(v_x_3921_, v_a_3944_);
v___x_3948_ = l_Lean_Expr_mvarId_x21(v_a_3944_);
lean_dec(v_a_3944_);
v___x_3949_ = lean_array_push(v_x_3923_, v___x_3948_);
v_x_3920_ = v___x_3946_;
v_x_3921_ = v___x_3947_;
v_x_3923_ = v___x_3949_;
v_x_3924_ = v_body_3932_;
goto _start;
}
else
{
lean_dec_ref(v_body_3932_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3921_);
lean_dec(v_x_3920_);
lean_dec_ref(v_f_3918_);
return v___x_3943_;
}
}
else
{
lean_object* v___x_3951_; uint8_t v___x_3952_; lean_object* v___x_3953_; 
v___x_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_d_3939_);
v___x_3952_ = 0;
v___x_3953_ = l_Lean_Meta_mkFreshExprMVar(v___x_3951_, v___x_3952_, v_binderName_3930_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
if (lean_obj_tag(v___x_3953_) == 0)
{
lean_object* v_a_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc(v_a_3954_);
lean_dec_ref_known(v___x_3953_, 1);
v___x_3955_ = lean_unsigned_to_nat(1u);
v___x_3956_ = lean_nat_add(v_x_3920_, v___x_3955_);
lean_dec(v_x_3920_);
v___x_3957_ = lean_array_push(v_x_3921_, v_a_3954_);
v_x_3920_ = v___x_3956_;
v_x_3921_ = v___x_3957_;
v_x_3924_ = v_body_3932_;
goto _start;
}
else
{
lean_dec_ref(v_body_3932_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3921_);
lean_dec(v_x_3920_);
lean_dec_ref(v_f_3918_);
return v___x_3953_;
}
}
}
else
{
lean_object* v_val_3959_; lean_object* v___x_3960_; 
lean_dec(v_binderName_3930_);
v_val_3959_ = lean_ctor_get(v___x_3940_, 0);
lean_inc(v_a_3928_);
lean_inc_ref(v_a_3927_);
lean_inc(v_a_3926_);
lean_inc_ref(v_a_3925_);
lean_inc(v_val_3959_);
v___x_3960_ = lean_infer_type(v_val_3959_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
if (lean_obj_tag(v___x_3960_) == 0)
{
lean_object* v_a_3961_; lean_object* v___x_3962_; 
v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
lean_inc(v_a_3961_);
lean_dec_ref_known(v___x_3960_, 1);
v___x_3962_ = l_Lean_Meta_isExprDefEq(v_d_3939_, v_a_3961_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; uint8_t v___x_3964_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = lean_unbox(v_a_3963_);
lean_dec(v_a_3963_);
if (v___x_3964_ == 0)
{
lean_object* v___x_3965_; lean_object* v___x_3966_; 
lean_dec_ref(v_body_3932_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec(v_x_3920_);
v___x_3965_ = l_Lean_mkAppN(v_f_3918_, v_x_3921_);
lean_dec_ref(v_x_3921_);
lean_inc(v_val_3959_);
v___x_3966_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v___x_3965_, v_val_3959_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
return v___x_3966_;
}
else
{
lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = lean_unsigned_to_nat(1u);
v___x_3968_ = lean_nat_add(v_x_3920_, v___x_3967_);
lean_dec(v_x_3920_);
lean_inc(v_val_3959_);
v___x_3969_ = lean_array_push(v_x_3921_, v_val_3959_);
v_x_3920_ = v___x_3968_;
v_x_3921_ = v___x_3969_;
v_x_3924_ = v_body_3932_;
goto _start;
}
}
else
{
lean_object* v_a_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3978_; 
lean_dec_ref(v_body_3932_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3921_);
lean_dec(v_x_3920_);
lean_dec_ref(v_f_3918_);
v_a_3971_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3978_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3978_ == 0)
{
v___x_3973_ = v___x_3962_;
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_a_3971_);
lean_dec(v___x_3962_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3978_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3976_; 
if (v_isShared_3974_ == 0)
{
v___x_3976_ = v___x_3973_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
}
}
else
{
lean_dec_ref(v_d_3939_);
lean_dec_ref(v_body_3932_);
lean_dec_ref(v_x_3923_);
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3921_);
lean_dec(v_x_3920_);
lean_dec_ref(v_f_3918_);
return v___x_3960_;
}
}
}
}
else
{
lean_object* v___x_3979_; lean_object* v_type_3980_; lean_object* v___x_3981_; 
v___x_3979_ = lean_array_get_size(v_x_3921_);
v_type_3980_ = lean_expr_instantiate_rev_range(v_x_3924_, v_x_3922_, v___x_3979_, v_x_3921_);
lean_dec(v_x_3922_);
lean_dec_ref(v_x_3924_);
v___x_3981_ = l_Lean_Meta_whnfD(v_type_3980_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_object* v_a_3982_; uint8_t v___x_3983_; 
v_a_3982_ = lean_ctor_get(v___x_3981_, 0);
lean_inc(v_a_3982_);
lean_dec_ref_known(v___x_3981_, 1);
v___x_3983_ = l_Lean_Expr_isForall(v_a_3982_);
if (v___x_3983_ == 0)
{
lean_object* v___x_3984_; uint8_t v___x_3985_; 
lean_dec(v_a_3982_);
v___x_3984_ = lean_array_get_size(v_xs_3919_);
v___x_3985_ = lean_nat_dec_eq(v_x_3920_, v___x_3984_);
lean_dec(v_x_3920_);
if (v___x_3985_ == 0)
{
lean_object* v___x_3986_; lean_object* v___y_3988_; lean_object* v___x_4001_; uint8_t v___x_4002_; 
lean_dec_ref(v_x_3923_);
lean_dec_ref(v_x_3921_);
v___x_3986_ = lean_unsigned_to_nat(0u);
v___x_4001_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4002_ = lean_nat_dec_lt(v___x_3986_, v___x_3984_);
if (v___x_4002_ == 0)
{
v___y_3988_ = v___x_4001_;
goto v___jp_3987_;
}
else
{
uint8_t v___x_4003_; 
v___x_4003_ = lean_nat_dec_le(v___x_3984_, v___x_3984_);
if (v___x_4003_ == 0)
{
if (v___x_4002_ == 0)
{
v___y_3988_ = v___x_4001_;
goto v___jp_3987_;
}
else
{
size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = ((size_t)0ULL);
v___x_4005_ = lean_usize_of_nat(v___x_3984_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3919_, v___x_4004_, v___x_4005_, v___x_4001_);
v___y_3988_ = v___x_4006_;
goto v___jp_3987_;
}
}
else
{
size_t v___x_4007_; size_t v___x_4008_; lean_object* v___x_4009_; 
v___x_4007_ = ((size_t)0ULL);
v___x_4008_ = lean_usize_of_nat(v___x_3984_);
v___x_4009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux_spec__0(v_xs_3919_, v___x_4007_, v___x_4008_, v___x_4001_);
v___y_3988_ = v___x_4009_;
goto v___jp_3987_;
}
}
v___jp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3989_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_3990_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__4);
v___x_3991_ = l_Lean_indentExpr(v_f_3918_);
v___x_3992_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3990_);
lean_ctor_set(v___x_3992_, 1, v___x_3991_);
v___x_3993_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__5);
v___x_3994_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3992_);
lean_ctor_set(v___x_3994_, 1, v___x_3993_);
v___x_3995_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__8);
v___x_3996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3994_);
lean_ctor_set(v___x_3996_, 1, v___x_3995_);
v___x_3997_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs_loop___closed__8);
v___x_3998_ = l_Lean_MessageData_arrayExpr_toMessageData(v___y_3988_, v___x_3986_, v___x_3997_);
lean_dec_ref(v___y_3988_);
v___x_3999_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3999_, 0, v___x_3996_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_3989_, v___x_3999_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
return v___x_4000_;
}
}
else
{
lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4010_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___closed__1));
v___x_4011_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMFinal(v___x_4010_, v_f_3918_, v_x_3921_, v_x_3923_, v_a_3925_, v_a_3926_, v_a_3927_, v_a_3928_);
lean_dec_ref(v_x_3923_);
lean_dec_ref(v_x_3921_);
return v___x_4011_;
}
}
else
{
v_x_3922_ = v___x_3979_;
v_x_3924_ = v_a_3982_;
goto _start;
}
}
else
{
lean_dec_ref(v_x_3923_);
lean_dec_ref(v_x_3921_);
lean_dec(v_x_3920_);
lean_dec_ref(v_f_3918_);
return v___x_3981_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed(lean_object* v_f_4013_, lean_object* v_xs_4014_, lean_object* v_x_4015_, lean_object* v_x_4016_, lean_object* v_x_4017_, lean_object* v_x_4018_, lean_object* v_x_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_){
_start:
{
lean_object* v_res_4025_; 
v_res_4025_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_f_4013_, v_xs_4014_, v_x_4015_, v_x_4016_, v_x_4017_, v_x_4018_, v_x_4019_, v_a_4020_, v_a_4021_, v_a_4022_, v_a_4023_);
lean_dec(v_a_4023_);
lean_dec_ref(v_a_4022_);
lean_dec(v_a_4021_);
lean_dec_ref(v_a_4020_);
lean_dec_ref(v_xs_4014_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0(lean_object* v_constName_4026_, lean_object* v_xs_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun(v_constName_4026_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v_fst_4035_; lean_object* v_snd_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
v_fst_4035_ = lean_ctor_get(v_a_4034_, 0);
lean_inc(v_fst_4035_);
v_snd_4036_ = lean_ctor_get(v_a_4034_, 1);
lean_inc(v_snd_4036_);
lean_dec(v_a_4034_);
v___x_4037_ = lean_unsigned_to_nat(0u);
v___x_4038_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
v___x_4039_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux(v_fst_4035_, v_xs_4027_, v___x_4037_, v___x_4038_, v___x_4037_, v___x_4038_, v_snd_4036_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
return v___x_4039_;
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4042_; uint8_t v_isShared_4043_; uint8_t v_isSharedCheck_4047_; 
v_a_4040_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4047_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4047_ == 0)
{
v___x_4042_ = v___x_4033_;
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
else
{
lean_inc(v_a_4040_);
lean_dec(v___x_4033_);
v___x_4042_ = lean_box(0);
v_isShared_4043_ = v_isSharedCheck_4047_;
goto v_resetjp_4041_;
}
v_resetjp_4041_:
{
lean_object* v___x_4045_; 
if (v_isShared_4043_ == 0)
{
v___x_4045_ = v___x_4042_;
goto v_reusejp_4044_;
}
else
{
lean_object* v_reuseFailAlloc_4046_; 
v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4046_, 0, v_a_4040_);
v___x_4045_ = v_reuseFailAlloc_4046_;
goto v_reusejp_4044_;
}
v_reusejp_4044_:
{
return v___x_4045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___lam__0___boxed(lean_object* v_constName_4048_, lean_object* v_xs_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v_res_4055_; 
v_res_4055_ = l_Lean_Meta_mkAppOptM___lam__0(v_constName_4048_, v_xs_4049_, v___y_4050_, v___y_4051_, v___y_4052_, v___y_4053_);
lean_dec(v___y_4053_);
lean_dec_ref(v___y_4052_);
lean_dec(v___y_4051_);
lean_dec_ref(v___y_4050_);
lean_dec_ref(v_xs_4049_);
return v_res_4055_;
}
}
static lean_object* _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2(void){
_start:
{
lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4059_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__1));
v___x_4060_ = l_Lean_MessageData_ofFormat(v___x_4059_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
if (lean_obj_tag(v_a_4061_) == 0)
{
lean_object* v___x_4063_; 
v___x_4063_ = l_List_reverse___redArg(v_a_4062_);
return v___x_4063_;
}
else
{
lean_object* v_head_4064_; lean_object* v_tail_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4078_; 
v_head_4064_ = lean_ctor_get(v_a_4061_, 0);
v_tail_4065_ = lean_ctor_get(v_a_4061_, 1);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_a_4061_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4067_ = v_a_4061_;
v_isShared_4068_ = v_isSharedCheck_4078_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_tail_4065_);
lean_inc(v_head_4064_);
lean_dec(v_a_4061_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4078_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___y_4070_; 
if (lean_obj_tag(v_head_4064_) == 0)
{
lean_object* v___x_4075_; 
v___x_4075_ = lean_obj_once(&l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2, &l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2_once, _init_l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0___closed__2);
v___y_4070_ = v___x_4075_;
goto v___jp_4069_;
}
else
{
lean_object* v_val_4076_; lean_object* v___x_4077_; 
v_val_4076_ = lean_ctor_get(v_head_4064_, 0);
lean_inc(v_val_4076_);
lean_dec_ref_known(v_head_4064_, 1);
v___x_4077_ = l_Lean_MessageData_ofExpr(v_val_4076_);
v___y_4070_ = v___x_4077_;
goto v___jp_4069_;
}
v___jp_4069_:
{
lean_object* v___x_4072_; 
if (v_isShared_4068_ == 0)
{
lean_ctor_set(v___x_4067_, 1, v_a_4062_);
lean_ctor_set(v___x_4067_, 0, v___y_4070_);
v___x_4072_ = v___x_4067_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v___y_4070_);
lean_ctor_set(v_reuseFailAlloc_4074_, 1, v_a_4062_);
v___x_4072_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
v_a_4061_ = v_tail_4065_;
v_a_4062_ = v___x_4072_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(lean_object* v_f_4079_, lean_object* v_xs_4080_, lean_object* v_x_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4087_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4088_ = l_Lean_MessageData_ofName(v_f_4079_);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_array_to_list(v_xs_4080_);
v___x_4093_ = lean_box(0);
v___x_4094_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4092_, v___x_4093_);
v___x_4095_ = l_Lean_MessageData_ofList(v___x_4094_);
v___x_4096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4096_, 0, v___x_4091_);
lean_ctor_set(v___x_4096_, 1, v___x_4095_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
return v___x_4097_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed(lean_object* v_f_4098_, lean_object* v_xs_4099_, lean_object* v_x_4100_, lean_object* v___y_4101_, lean_object* v___y_4102_, lean_object* v___y_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0(v_f_4098_, v_xs_4099_, v_x_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
lean_dec(v___y_4104_);
lean_dec_ref(v___y_4103_);
lean_dec(v___y_4102_);
lean_dec_ref(v___y_4101_);
lean_dec_ref(v_x_4100_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(lean_object* v_f_4107_, lean_object* v_xs_4108_, lean_object* v_k_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_){
_start:
{
lean_object* v_toCold_4115_; lean_object* v_options_4116_; uint8_t v_hasTrace_4117_; 
v_toCold_4115_ = lean_ctor_get(v_a_4112_, 0);
v_options_4116_ = lean_ctor_get(v_toCold_4115_, 2);
v_hasTrace_4117_ = lean_ctor_get_uint8(v_options_4116_, sizeof(void*)*1);
if (v_hasTrace_4117_ == 0)
{
lean_object* v___x_4118_; 
lean_dec_ref(v_xs_4108_);
lean_dec(v_f_4107_);
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
lean_inc(v_a_4111_);
lean_inc_ref(v_a_4110_);
v___x_4118_ = lean_apply_5(v_k_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, lean_box(0));
return v___x_4118_;
}
else
{
lean_object* v_inheritedTraceOptions_4119_; lean_object* v___f_4120_; lean_object* v___y_4122_; lean_object* v___y_4123_; uint8_t v___y_4124_; lean_object* v___y_4148_; lean_object* v_a_4149_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; uint8_t v___x_4155_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v_a_4159_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v_a_4174_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; uint8_t v___y_4180_; lean_object* v___y_4188_; lean_object* v___y_4189_; lean_object* v_a_4190_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v_a_4196_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v_a_4201_; lean_object* v___y_4211_; lean_object* v___y_4212_; lean_object* v_a_4213_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; uint8_t v___y_4219_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v_a_4229_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v_a_4235_; 
v_inheritedTraceOptions_4119_ = lean_ctor_get(v_toCold_4115_, 11);
v___f_4120_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4120_, 0, v_f_4107_);
lean_closure_set(v___f_4120_, 1, v_xs_4108_);
v___x_4152_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4153_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4154_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4119_, v_options_4116_, v___x_4154_);
if (v___x_4155_ == 0)
{
lean_object* v___x_4262_; uint8_t v___x_4263_; 
v___x_4262_ = l_Lean_trace_profiler;
v___x_4263_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4116_, v___x_4262_);
if (v___x_4263_ == 0)
{
lean_object* v___x_4264_; 
lean_dec_ref(v___f_4120_);
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
lean_inc(v_a_4111_);
lean_inc_ref(v_a_4110_);
v___x_4264_ = lean_apply_5(v_k_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, lean_box(0));
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; uint8_t v___x_4268_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
v___x_4266_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4267_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4268_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4119_, v_options_4116_, v___x_4267_);
if (v___x_4268_ == 0)
{
lean_dec(v_a_4265_);
return v___x_4264_;
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
lean_dec_ref_known(v___x_4264_, 1);
lean_inc(v_a_4265_);
v___x_4269_ = l_Lean_MessageData_ofExpr(v_a_4265_);
v___x_4270_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4266_, v___x_4269_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4277_ == 0)
{
lean_object* v_unused_4278_; 
v_unused_4278_ = lean_ctor_get(v___x_4270_, 0);
lean_dec(v_unused_4278_);
v___x_4272_ = v___x_4270_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_dec(v___x_4270_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v_a_4265_);
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4265_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec(v_a_4265_);
v_a_4279_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4270_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4270_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
lean_inc(v_a_4279_);
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
v___y_4148_ = v___x_4284_;
v_a_4149_ = v_a_4279_;
goto v___jp_4147_;
}
}
}
}
}
else
{
lean_object* v_a_4287_; 
v_a_4287_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4287_);
v___y_4148_ = v___x_4264_;
v_a_4149_ = v_a_4287_;
goto v___jp_4147_;
}
}
else
{
goto v___jp_4237_;
}
}
else
{
goto v___jp_4237_;
}
v___jp_4121_:
{
if (v___y_4124_ == 0)
{
lean_object* v___x_4125_; lean_object* v___x_4126_; uint8_t v___x_4127_; 
lean_dec_ref(v___y_4123_);
v___x_4125_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4126_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4127_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4119_, v_options_4116_, v___x_4126_);
if (v___x_4127_ == 0)
{
lean_object* v___x_4128_; 
v___x_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4128_, 0, v___y_4122_);
return v___x_4128_;
}
else
{
lean_object* v___x_4129_; lean_object* v___x_4130_; 
lean_inc_ref(v___y_4122_);
v___x_4129_ = l_Lean_Exception_toMessageData(v___y_4122_);
v___x_4130_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4125_, v___x_4129_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4130_) == 0)
{
lean_object* v___x_4132_; uint8_t v_isShared_4133_; uint8_t v_isSharedCheck_4137_; 
v_isSharedCheck_4137_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4137_ == 0)
{
lean_object* v_unused_4138_; 
v_unused_4138_ = lean_ctor_get(v___x_4130_, 0);
lean_dec(v_unused_4138_);
v___x_4132_ = v___x_4130_;
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
else
{
lean_dec(v___x_4130_);
v___x_4132_ = lean_box(0);
v_isShared_4133_ = v_isSharedCheck_4137_;
goto v_resetjp_4131_;
}
v_resetjp_4131_:
{
lean_object* v___x_4135_; 
if (v_isShared_4133_ == 0)
{
lean_ctor_set_tag(v___x_4132_, 1);
lean_ctor_set(v___x_4132_, 0, v___y_4122_);
v___x_4135_ = v___x_4132_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___y_4122_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
}
else
{
lean_object* v_a_4139_; lean_object* v___x_4141_; uint8_t v_isShared_4142_; uint8_t v_isSharedCheck_4146_; 
lean_dec_ref(v___y_4122_);
v_a_4139_ = lean_ctor_get(v___x_4130_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4130_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4141_ = v___x_4130_;
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
else
{
lean_inc(v_a_4139_);
lean_dec(v___x_4130_);
v___x_4141_ = lean_box(0);
v_isShared_4142_ = v_isSharedCheck_4146_;
goto v_resetjp_4140_;
}
v_resetjp_4140_:
{
lean_object* v___x_4144_; 
if (v_isShared_4142_ == 0)
{
v___x_4144_ = v___x_4141_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_a_4139_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4122_);
return v___y_4123_;
}
}
v___jp_4147_:
{
uint8_t v___x_4150_; 
v___x_4150_ = l_Lean_Exception_isInterrupt(v_a_4149_);
if (v___x_4150_ == 0)
{
uint8_t v___x_4151_; 
lean_inc_ref(v_a_4149_);
v___x_4151_ = l_Lean_Exception_isRuntime(v_a_4149_);
v___y_4122_ = v_a_4149_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___x_4151_;
goto v___jp_4121_;
}
else
{
v___y_4122_ = v_a_4149_;
v___y_4123_ = v___y_4148_;
v___y_4124_ = v___x_4150_;
goto v___jp_4121_;
}
}
v___jp_4156_:
{
lean_object* v___x_4160_; double v___x_4161_; double v___x_4162_; double v___x_4163_; double v___x_4164_; double v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4160_ = lean_io_mono_nanos_now();
v___x_4161_ = lean_float_of_nat(v___y_4158_);
v___x_4162_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4163_ = lean_float_div(v___x_4161_, v___x_4162_);
v___x_4164_ = lean_float_of_nat(v___x_4160_);
v___x_4165_ = lean_float_div(v___x_4164_, v___x_4162_);
v___x_4166_ = lean_box_float(v___x_4163_);
v___x_4167_ = lean_box_float(v___x_4165_);
v___x_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v_a_4159_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4152_, v_hasTrace_4117_, v___x_4153_, v_options_4116_, v___x_4155_, v___y_4157_, v___f_4120_, v___x_4169_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
return v___x_4170_;
}
v___jp_4171_:
{
lean_object* v___x_4175_; 
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v_a_4174_);
v___y_4157_ = v___y_4172_;
v___y_4158_ = v___y_4173_;
v_a_4159_ = v___x_4175_;
goto v___jp_4156_;
}
v___jp_4176_:
{
if (v___y_4180_ == 0)
{
lean_object* v___x_4181_; lean_object* v___x_4182_; uint8_t v___x_4183_; 
v___x_4181_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4182_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4119_, v_options_4116_, v___x_4182_);
if (v___x_4183_ == 0)
{
v___y_4172_ = v___y_4178_;
v___y_4173_ = v___y_4179_;
v_a_4174_ = v___y_4177_;
goto v___jp_4171_;
}
else
{
lean_object* v___x_4184_; lean_object* v___x_4185_; 
lean_inc_ref(v___y_4177_);
v___x_4184_ = l_Lean_Exception_toMessageData(v___y_4177_);
v___x_4185_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4181_, v___x_4184_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4185_) == 0)
{
lean_dec_ref_known(v___x_4185_, 1);
v___y_4172_ = v___y_4178_;
v___y_4173_ = v___y_4179_;
v_a_4174_ = v___y_4177_;
goto v___jp_4171_;
}
else
{
lean_object* v_a_4186_; 
lean_dec_ref(v___y_4177_);
v_a_4186_ = lean_ctor_get(v___x_4185_, 0);
lean_inc(v_a_4186_);
lean_dec_ref_known(v___x_4185_, 1);
v___y_4172_ = v___y_4178_;
v___y_4173_ = v___y_4179_;
v_a_4174_ = v_a_4186_;
goto v___jp_4171_;
}
}
}
else
{
v___y_4172_ = v___y_4178_;
v___y_4173_ = v___y_4179_;
v_a_4174_ = v___y_4177_;
goto v___jp_4171_;
}
}
v___jp_4187_:
{
uint8_t v___x_4191_; 
v___x_4191_ = l_Lean_Exception_isInterrupt(v_a_4190_);
if (v___x_4191_ == 0)
{
uint8_t v___x_4192_; 
lean_inc_ref(v_a_4190_);
v___x_4192_ = l_Lean_Exception_isRuntime(v_a_4190_);
v___y_4177_ = v_a_4190_;
v___y_4178_ = v___y_4188_;
v___y_4179_ = v___y_4189_;
v___y_4180_ = v___x_4192_;
goto v___jp_4176_;
}
else
{
v___y_4177_ = v_a_4190_;
v___y_4178_ = v___y_4188_;
v___y_4179_ = v___y_4189_;
v___y_4180_ = v___x_4191_;
goto v___jp_4176_;
}
}
v___jp_4193_:
{
lean_object* v___x_4197_; 
v___x_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4197_, 0, v_a_4196_);
v___y_4157_ = v___y_4194_;
v___y_4158_ = v___y_4195_;
v_a_4159_ = v___x_4197_;
goto v___jp_4156_;
}
v___jp_4198_:
{
lean_object* v___x_4202_; double v___x_4203_; double v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
v___x_4202_ = lean_io_get_num_heartbeats();
v___x_4203_ = lean_float_of_nat(v___y_4200_);
v___x_4204_ = lean_float_of_nat(v___x_4202_);
v___x_4205_ = lean_box_float(v___x_4203_);
v___x_4206_ = lean_box_float(v___x_4204_);
v___x_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4205_);
lean_ctor_set(v___x_4207_, 1, v___x_4206_);
v___x_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4208_, 0, v_a_4201_);
lean_ctor_set(v___x_4208_, 1, v___x_4207_);
v___x_4209_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4152_, v_hasTrace_4117_, v___x_4153_, v_options_4116_, v___x_4155_, v___y_4199_, v___f_4120_, v___x_4208_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
return v___x_4209_;
}
v___jp_4210_:
{
lean_object* v___x_4214_; 
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v_a_4213_);
v___y_4199_ = v___y_4211_;
v___y_4200_ = v___y_4212_;
v_a_4201_ = v___x_4214_;
goto v___jp_4198_;
}
v___jp_4215_:
{
if (v___y_4219_ == 0)
{
lean_object* v___x_4220_; lean_object* v___x_4221_; uint8_t v___x_4222_; 
v___x_4220_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4221_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4222_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4119_, v_options_4116_, v___x_4221_);
if (v___x_4222_ == 0)
{
v___y_4211_ = v___y_4216_;
v___y_4212_ = v___y_4217_;
v_a_4213_ = v___y_4218_;
goto v___jp_4210_;
}
else
{
lean_object* v___x_4223_; lean_object* v___x_4224_; 
lean_inc_ref(v___y_4218_);
v___x_4223_ = l_Lean_Exception_toMessageData(v___y_4218_);
v___x_4224_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4220_, v___x_4223_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_dec_ref_known(v___x_4224_, 1);
v___y_4211_ = v___y_4216_;
v___y_4212_ = v___y_4217_;
v_a_4213_ = v___y_4218_;
goto v___jp_4210_;
}
else
{
lean_object* v_a_4225_; 
lean_dec_ref(v___y_4218_);
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
v___y_4211_ = v___y_4216_;
v___y_4212_ = v___y_4217_;
v_a_4213_ = v_a_4225_;
goto v___jp_4210_;
}
}
}
else
{
v___y_4211_ = v___y_4216_;
v___y_4212_ = v___y_4217_;
v_a_4213_ = v___y_4218_;
goto v___jp_4210_;
}
}
v___jp_4226_:
{
uint8_t v___x_4230_; 
v___x_4230_ = l_Lean_Exception_isInterrupt(v_a_4229_);
if (v___x_4230_ == 0)
{
uint8_t v___x_4231_; 
lean_inc_ref(v_a_4229_);
v___x_4231_ = l_Lean_Exception_isRuntime(v_a_4229_);
v___y_4216_ = v___y_4227_;
v___y_4217_ = v___y_4228_;
v___y_4218_ = v_a_4229_;
v___y_4219_ = v___x_4231_;
goto v___jp_4215_;
}
else
{
v___y_4216_ = v___y_4227_;
v___y_4217_ = v___y_4228_;
v___y_4218_ = v_a_4229_;
v___y_4219_ = v___x_4230_;
goto v___jp_4215_;
}
}
v___jp_4232_:
{
lean_object* v___x_4236_; 
v___x_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4236_, 0, v_a_4235_);
v___y_4199_ = v___y_4233_;
v___y_4200_ = v___y_4234_;
v_a_4201_ = v___x_4236_;
goto v___jp_4198_;
}
v___jp_4237_:
{
lean_object* v___x_4238_; lean_object* v_a_4239_; lean_object* v___x_4240_; uint8_t v___x_4241_; 
v___x_4238_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4113_);
v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
lean_inc(v_a_4239_);
lean_dec_ref(v___x_4238_);
v___x_4240_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4241_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4116_, v___x_4240_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
v___x_4242_ = lean_io_mono_nanos_now();
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
lean_inc(v_a_4111_);
lean_inc_ref(v_a_4110_);
v___x_4243_ = lean_apply_5(v_k_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, lean_box(0));
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v_a_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref_known(v___x_4243_, 1);
v___x_4245_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4246_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4247_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4119_, v_options_4116_, v___x_4246_);
if (v___x_4247_ == 0)
{
v___y_4194_ = v_a_4239_;
v___y_4195_ = v___x_4242_;
v_a_4196_ = v_a_4244_;
goto v___jp_4193_;
}
else
{
lean_object* v___x_4248_; lean_object* v___x_4249_; 
lean_inc(v_a_4244_);
v___x_4248_ = l_Lean_MessageData_ofExpr(v_a_4244_);
v___x_4249_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4245_, v___x_4248_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_dec_ref_known(v___x_4249_, 1);
v___y_4194_ = v_a_4239_;
v___y_4195_ = v___x_4242_;
v_a_4196_ = v_a_4244_;
goto v___jp_4193_;
}
else
{
lean_object* v_a_4250_; 
lean_dec(v_a_4244_);
v_a_4250_ = lean_ctor_get(v___x_4249_, 0);
lean_inc(v_a_4250_);
lean_dec_ref_known(v___x_4249_, 1);
v___y_4188_ = v_a_4239_;
v___y_4189_ = v___x_4242_;
v_a_4190_ = v_a_4250_;
goto v___jp_4187_;
}
}
}
else
{
lean_object* v_a_4251_; 
v_a_4251_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v___x_4243_, 1);
v___y_4188_ = v_a_4239_;
v___y_4189_ = v___x_4242_;
v_a_4190_ = v_a_4251_;
goto v___jp_4187_;
}
}
else
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4113_);
lean_inc_ref(v_a_4112_);
lean_inc(v_a_4111_);
lean_inc_ref(v_a_4110_);
v___x_4253_ = lean_apply_5(v_k_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_, lean_box(0));
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
v___x_4255_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4256_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4119_, v_options_4116_, v___x_4256_);
if (v___x_4257_ == 0)
{
v___y_4233_ = v_a_4239_;
v___y_4234_ = v___x_4252_;
v_a_4235_ = v_a_4254_;
goto v___jp_4232_;
}
else
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
lean_inc(v_a_4254_);
v___x_4258_ = l_Lean_MessageData_ofExpr(v_a_4254_);
v___x_4259_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4255_, v___x_4258_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_dec_ref_known(v___x_4259_, 1);
v___y_4233_ = v_a_4239_;
v___y_4234_ = v___x_4252_;
v_a_4235_ = v_a_4254_;
goto v___jp_4232_;
}
else
{
lean_object* v_a_4260_; 
lean_dec(v_a_4254_);
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___y_4227_ = v_a_4239_;
v___y_4228_ = v___x_4252_;
v_a_4229_ = v_a_4260_;
goto v___jp_4226_;
}
}
}
else
{
lean_object* v_a_4261_; 
v_a_4261_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4253_, 1);
v___y_4227_ = v_a_4239_;
v___y_4228_ = v___x_4252_;
v_a_4229_ = v_a_4261_;
goto v___jp_4226_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0___boxed(lean_object* v_f_4288_, lean_object* v_xs_4289_, lean_object* v_k_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_, lean_object* v_a_4293_, lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
lean_object* v_res_4296_; 
v_res_4296_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_f_4288_, v_xs_4289_, v_k_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_);
lean_dec(v_a_4294_);
lean_dec_ref(v_a_4293_);
lean_dec(v_a_4292_);
lean_dec_ref(v_a_4291_);
return v_res_4296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM(lean_object* v_constName_4297_, lean_object* v_xs_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_){
_start:
{
lean_object* v___f_4304_; uint8_t v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; 
lean_inc_ref(v_xs_4298_);
lean_inc(v_constName_4297_);
v___f_4304_ = lean_alloc_closure((void*)(l_Lean_Meta_mkAppOptM___lam__0___boxed), 7, 2);
lean_closure_set(v___f_4304_, 0, v_constName_4297_);
lean_closure_set(v___f_4304_, 1, v_xs_4298_);
v___x_4305_ = 0;
v___x_4306_ = lean_box(v___x_4305_);
v___x_4307_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4307_, 0, lean_box(0));
lean_closure_set(v___x_4307_, 1, v___f_4304_);
lean_closure_set(v___x_4307_, 2, v___x_4306_);
v___x_4308_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0(v_constName_4297_, v_xs_4298_, v___x_4307_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
return v___x_4308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM___boxed(lean_object* v_constName_4309_, lean_object* v_xs_4310_, lean_object* v_a_4311_, lean_object* v_a_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_Meta_mkAppOptM(v_constName_4309_, v_xs_4310_, v_a_4311_, v_a_4312_, v_a_4313_, v_a_4314_);
lean_dec(v_a_4314_);
lean_dec_ref(v_a_4313_);
lean_dec(v_a_4312_);
lean_dec_ref(v_a_4311_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(lean_object* v_f_4317_, lean_object* v_xs_4318_, lean_object* v_x_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_){
_start:
{
lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; 
v___x_4325_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__1);
v___x_4326_ = l_Lean_MessageData_ofExpr(v_f_4317_);
v___x_4327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4327_, 0, v___x_4325_);
lean_ctor_set(v___x_4327_, 1, v___x_4326_);
v___x_4328_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___lam__0___closed__3);
v___x_4329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4329_, 0, v___x_4327_);
lean_ctor_set(v___x_4329_, 1, v___x_4328_);
v___x_4330_ = lean_array_to_list(v_xs_4318_);
v___x_4331_ = lean_box(0);
v___x_4332_ = l_List_mapTR_loop___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_spec__0_spec__0(v___x_4330_, v___x_4331_);
v___x_4333_ = l_Lean_MessageData_ofList(v___x_4332_);
v___x_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4329_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4335_, 0, v___x_4334_);
return v___x_4335_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed(lean_object* v_f_4336_, lean_object* v_xs_4337_, lean_object* v_x_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0(v_f_4336_, v_xs_4337_, v_x_4338_, v___y_4339_, v___y_4340_, v___y_4341_, v___y_4342_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
lean_dec(v___y_4340_);
lean_dec_ref(v___y_4339_);
lean_dec_ref(v_x_4338_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(lean_object* v_f_4345_, lean_object* v_xs_4346_, lean_object* v_k_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_){
_start:
{
lean_object* v_toCold_4353_; lean_object* v_options_4354_; uint8_t v_hasTrace_4355_; 
v_toCold_4353_ = lean_ctor_get(v_a_4350_, 0);
v_options_4354_ = lean_ctor_get(v_toCold_4353_, 2);
v_hasTrace_4355_ = lean_ctor_get_uint8(v_options_4354_, sizeof(void*)*1);
if (v_hasTrace_4355_ == 0)
{
lean_object* v___x_4356_; 
lean_dec_ref(v_xs_4346_);
lean_dec_ref(v_f_4345_);
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
lean_inc(v_a_4349_);
lean_inc_ref(v_a_4348_);
v___x_4356_ = lean_apply_5(v_k_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, lean_box(0));
return v___x_4356_;
}
else
{
lean_object* v_inheritedTraceOptions_4357_; lean_object* v___f_4358_; lean_object* v___y_4360_; lean_object* v___y_4361_; uint8_t v___y_4362_; lean_object* v___y_4386_; lean_object* v_a_4387_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; uint8_t v___x_4393_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v_a_4397_; lean_object* v___y_4410_; lean_object* v___y_4411_; lean_object* v_a_4412_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; uint8_t v___y_4418_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v_a_4428_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v_a_4434_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v_a_4439_; lean_object* v___y_4449_; lean_object* v___y_4450_; lean_object* v_a_4451_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; uint8_t v___y_4457_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v_a_4467_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v_a_4473_; 
v_inheritedTraceOptions_4357_ = lean_ctor_get(v_toCold_4353_, 11);
v___f_4358_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___lam__0___boxed), 8, 2);
lean_closure_set(v___f_4358_, 0, v_f_4345_);
lean_closure_set(v___f_4358_, 1, v_xs_4346_);
v___x_4390_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_4391_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__28));
v___x_4392_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__29);
v___x_4393_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4357_, v_options_4354_, v___x_4392_);
if (v___x_4393_ == 0)
{
lean_object* v___x_4500_; uint8_t v___x_4501_; 
v___x_4500_ = l_Lean_trace_profiler;
v___x_4501_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4354_, v___x_4500_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; 
lean_dec_ref(v___f_4358_);
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
lean_inc(v_a_4349_);
lean_inc_ref(v_a_4348_);
v___x_4502_ = lean_apply_5(v_k_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, lean_box(0));
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; uint8_t v___x_4506_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
v___x_4504_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4505_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4506_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4357_, v_options_4354_, v___x_4505_);
if (v___x_4506_ == 0)
{
lean_dec(v_a_4503_);
return v___x_4502_;
}
else
{
lean_object* v___x_4507_; lean_object* v___x_4508_; 
lean_dec_ref_known(v___x_4502_, 1);
lean_inc(v_a_4503_);
v___x_4507_ = l_Lean_MessageData_ofExpr(v_a_4503_);
v___x_4508_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4504_, v___x_4507_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4508_) == 0)
{
lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4515_; 
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4515_ == 0)
{
lean_object* v_unused_4516_; 
v_unused_4516_ = lean_ctor_get(v___x_4508_, 0);
lean_dec(v_unused_4516_);
v___x_4510_ = v___x_4508_;
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
else
{
lean_dec(v___x_4508_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4515_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4513_; 
if (v_isShared_4511_ == 0)
{
lean_ctor_set(v___x_4510_, 0, v_a_4503_);
v___x_4513_ = v___x_4510_;
goto v_reusejp_4512_;
}
else
{
lean_object* v_reuseFailAlloc_4514_; 
v_reuseFailAlloc_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4514_, 0, v_a_4503_);
v___x_4513_ = v_reuseFailAlloc_4514_;
goto v_reusejp_4512_;
}
v_reusejp_4512_:
{
return v___x_4513_;
}
}
}
else
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4524_; 
lean_dec(v_a_4503_);
v_a_4517_ = lean_ctor_get(v___x_4508_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4519_ = v___x_4508_;
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v___x_4508_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4524_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
lean_inc(v_a_4517_);
if (v_isShared_4520_ == 0)
{
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
v___y_4386_ = v___x_4522_;
v_a_4387_ = v_a_4517_;
goto v___jp_4385_;
}
}
}
}
}
else
{
lean_object* v_a_4525_; 
v_a_4525_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4525_);
v___y_4386_ = v___x_4502_;
v_a_4387_ = v_a_4525_;
goto v___jp_4385_;
}
}
else
{
goto v___jp_4475_;
}
}
else
{
goto v___jp_4475_;
}
v___jp_4359_:
{
if (v___y_4362_ == 0)
{
lean_object* v___x_4363_; lean_object* v___x_4364_; uint8_t v___x_4365_; 
lean_dec_ref(v___y_4361_);
v___x_4363_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4364_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4365_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4357_, v_options_4354_, v___x_4364_);
if (v___x_4365_ == 0)
{
lean_object* v___x_4366_; 
v___x_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4366_, 0, v___y_4360_);
return v___x_4366_;
}
else
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
lean_inc_ref(v___y_4360_);
v___x_4367_ = l_Lean_Exception_toMessageData(v___y_4360_);
v___x_4368_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4363_, v___x_4367_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4368_) == 0)
{
lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4375_; 
v_isSharedCheck_4375_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4375_ == 0)
{
lean_object* v_unused_4376_; 
v_unused_4376_ = lean_ctor_get(v___x_4368_, 0);
lean_dec(v_unused_4376_);
v___x_4370_ = v___x_4368_;
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
else
{
lean_dec(v___x_4368_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4375_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4373_; 
if (v_isShared_4371_ == 0)
{
lean_ctor_set_tag(v___x_4370_, 1);
lean_ctor_set(v___x_4370_, 0, v___y_4360_);
v___x_4373_ = v___x_4370_;
goto v_reusejp_4372_;
}
else
{
lean_object* v_reuseFailAlloc_4374_; 
v_reuseFailAlloc_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4374_, 0, v___y_4360_);
v___x_4373_ = v_reuseFailAlloc_4374_;
goto v_reusejp_4372_;
}
v_reusejp_4372_:
{
return v___x_4373_;
}
}
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec_ref(v___y_4360_);
v_a_4377_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4368_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4368_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
}
else
{
lean_dec_ref(v___y_4360_);
return v___y_4361_;
}
}
v___jp_4385_:
{
uint8_t v___x_4388_; 
v___x_4388_ = l_Lean_Exception_isInterrupt(v_a_4387_);
if (v___x_4388_ == 0)
{
uint8_t v___x_4389_; 
lean_inc_ref(v_a_4387_);
v___x_4389_ = l_Lean_Exception_isRuntime(v_a_4387_);
v___y_4360_ = v_a_4387_;
v___y_4361_ = v___y_4386_;
v___y_4362_ = v___x_4389_;
goto v___jp_4359_;
}
else
{
v___y_4360_ = v_a_4387_;
v___y_4361_ = v___y_4386_;
v___y_4362_ = v___x_4388_;
goto v___jp_4359_;
}
}
v___jp_4394_:
{
lean_object* v___x_4398_; double v___x_4399_; double v___x_4400_; double v___x_4401_; double v___x_4402_; double v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; 
v___x_4398_ = lean_io_mono_nanos_now();
v___x_4399_ = lean_float_of_nat(v___y_4396_);
v___x_4400_ = lean_float_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__30);
v___x_4401_ = lean_float_div(v___x_4399_, v___x_4400_);
v___x_4402_ = lean_float_of_nat(v___x_4398_);
v___x_4403_ = lean_float_div(v___x_4402_, v___x_4400_);
v___x_4404_ = lean_box_float(v___x_4401_);
v___x_4405_ = lean_box_float(v___x_4403_);
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4407_, 0, v_a_4397_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
v___x_4408_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4390_, v_hasTrace_4355_, v___x_4391_, v_options_4354_, v___x_4393_, v___y_4395_, v___f_4358_, v___x_4407_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
return v___x_4408_;
}
v___jp_4409_:
{
lean_object* v___x_4413_; 
v___x_4413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4413_, 0, v_a_4412_);
v___y_4395_ = v___y_4410_;
v___y_4396_ = v___y_4411_;
v_a_4397_ = v___x_4413_;
goto v___jp_4394_;
}
v___jp_4414_:
{
if (v___y_4418_ == 0)
{
lean_object* v___x_4419_; lean_object* v___x_4420_; uint8_t v___x_4421_; 
v___x_4419_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4420_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4421_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4357_, v_options_4354_, v___x_4420_);
if (v___x_4421_ == 0)
{
v___y_4410_ = v___y_4415_;
v___y_4411_ = v___y_4416_;
v_a_4412_ = v___y_4417_;
goto v___jp_4409_;
}
else
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
lean_inc_ref(v___y_4417_);
v___x_4422_ = l_Lean_Exception_toMessageData(v___y_4417_);
v___x_4423_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4419_, v___x_4422_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_dec_ref_known(v___x_4423_, 1);
v___y_4410_ = v___y_4415_;
v___y_4411_ = v___y_4416_;
v_a_4412_ = v___y_4417_;
goto v___jp_4409_;
}
else
{
lean_object* v_a_4424_; 
lean_dec_ref(v___y_4417_);
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
v___y_4410_ = v___y_4415_;
v___y_4411_ = v___y_4416_;
v_a_4412_ = v_a_4424_;
goto v___jp_4409_;
}
}
}
else
{
v___y_4410_ = v___y_4415_;
v___y_4411_ = v___y_4416_;
v_a_4412_ = v___y_4417_;
goto v___jp_4409_;
}
}
v___jp_4425_:
{
uint8_t v___x_4429_; 
v___x_4429_ = l_Lean_Exception_isInterrupt(v_a_4428_);
if (v___x_4429_ == 0)
{
uint8_t v___x_4430_; 
lean_inc_ref(v_a_4428_);
v___x_4430_ = l_Lean_Exception_isRuntime(v_a_4428_);
v___y_4415_ = v___y_4426_;
v___y_4416_ = v___y_4427_;
v___y_4417_ = v_a_4428_;
v___y_4418_ = v___x_4430_;
goto v___jp_4414_;
}
else
{
v___y_4415_ = v___y_4426_;
v___y_4416_ = v___y_4427_;
v___y_4417_ = v_a_4428_;
v___y_4418_ = v___x_4429_;
goto v___jp_4414_;
}
}
v___jp_4431_:
{
lean_object* v___x_4435_; 
v___x_4435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4435_, 0, v_a_4434_);
v___y_4395_ = v___y_4432_;
v___y_4396_ = v___y_4433_;
v_a_4397_ = v___x_4435_;
goto v___jp_4394_;
}
v___jp_4436_:
{
lean_object* v___x_4440_; double v___x_4441_; double v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; 
v___x_4440_ = lean_io_get_num_heartbeats();
v___x_4441_ = lean_float_of_nat(v___y_4438_);
v___x_4442_ = lean_float_of_nat(v___x_4440_);
v___x_4443_ = lean_box_float(v___x_4441_);
v___x_4444_ = lean_box_float(v___x_4442_);
v___x_4445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4445_, 0, v___x_4443_);
lean_ctor_set(v___x_4445_, 1, v___x_4444_);
v___x_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4446_, 0, v_a_4439_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
v___x_4447_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__5(v___x_4390_, v_hasTrace_4355_, v___x_4391_, v_options_4354_, v___x_4393_, v___y_4437_, v___f_4358_, v___x_4446_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
return v___x_4447_;
}
v___jp_4448_:
{
lean_object* v___x_4452_; 
v___x_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4452_, 0, v_a_4451_);
v___y_4437_ = v___y_4449_;
v___y_4438_ = v___y_4450_;
v_a_4439_ = v___x_4452_;
goto v___jp_4436_;
}
v___jp_4453_:
{
if (v___y_4457_ == 0)
{
lean_object* v___x_4458_; lean_object* v___x_4459_; uint8_t v___x_4460_; 
v___x_4458_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_4459_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__25);
v___x_4460_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4357_, v_options_4354_, v___x_4459_);
if (v___x_4460_ == 0)
{
v___y_4449_ = v___y_4454_;
v___y_4450_ = v___y_4456_;
v_a_4451_ = v___y_4455_;
goto v___jp_4448_;
}
else
{
lean_object* v___x_4461_; lean_object* v___x_4462_; 
lean_inc_ref(v___y_4455_);
v___x_4461_ = l_Lean_Exception_toMessageData(v___y_4455_);
v___x_4462_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4458_, v___x_4461_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4462_) == 0)
{
lean_dec_ref_known(v___x_4462_, 1);
v___y_4449_ = v___y_4454_;
v___y_4450_ = v___y_4456_;
v_a_4451_ = v___y_4455_;
goto v___jp_4448_;
}
else
{
lean_object* v_a_4463_; 
lean_dec_ref(v___y_4455_);
v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
lean_inc(v_a_4463_);
lean_dec_ref_known(v___x_4462_, 1);
v___y_4449_ = v___y_4454_;
v___y_4450_ = v___y_4456_;
v_a_4451_ = v_a_4463_;
goto v___jp_4448_;
}
}
}
else
{
v___y_4449_ = v___y_4454_;
v___y_4450_ = v___y_4456_;
v_a_4451_ = v___y_4455_;
goto v___jp_4448_;
}
}
v___jp_4464_:
{
uint8_t v___x_4468_; 
v___x_4468_ = l_Lean_Exception_isInterrupt(v_a_4467_);
if (v___x_4468_ == 0)
{
uint8_t v___x_4469_; 
lean_inc_ref(v_a_4467_);
v___x_4469_ = l_Lean_Exception_isRuntime(v_a_4467_);
v___y_4454_ = v___y_4465_;
v___y_4455_ = v_a_4467_;
v___y_4456_ = v___y_4466_;
v___y_4457_ = v___x_4469_;
goto v___jp_4453_;
}
else
{
v___y_4454_ = v___y_4465_;
v___y_4455_ = v_a_4467_;
v___y_4456_ = v___y_4466_;
v___y_4457_ = v___x_4468_;
goto v___jp_4453_;
}
}
v___jp_4470_:
{
lean_object* v___x_4474_; 
v___x_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4474_, 0, v_a_4473_);
v___y_4437_ = v___y_4471_;
v___y_4438_ = v___y_4472_;
v_a_4439_ = v___x_4474_;
goto v___jp_4436_;
}
v___jp_4475_:
{
lean_object* v___x_4476_; lean_object* v_a_4477_; lean_object* v___x_4478_; uint8_t v___x_4479_; 
v___x_4476_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__3___redArg(v_a_4351_);
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4476_);
v___x_4478_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4479_ = l_Lean_Option_get___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__4(v_options_4354_, v___x_4478_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v___x_4481_; 
v___x_4480_ = lean_io_mono_nanos_now();
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
lean_inc(v_a_4349_);
lean_inc_ref(v_a_4348_);
v___x_4481_ = lean_apply_5(v_k_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, lean_box(0));
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; uint8_t v___x_4485_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
v___x_4483_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4484_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4485_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4357_, v_options_4354_, v___x_4484_);
if (v___x_4485_ == 0)
{
v___y_4432_ = v_a_4477_;
v___y_4433_ = v___x_4480_;
v_a_4434_ = v_a_4482_;
goto v___jp_4431_;
}
else
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
lean_inc(v_a_4482_);
v___x_4486_ = l_Lean_MessageData_ofExpr(v_a_4482_);
v___x_4487_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4483_, v___x_4486_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_dec_ref_known(v___x_4487_, 1);
v___y_4432_ = v_a_4477_;
v___y_4433_ = v___x_4480_;
v_a_4434_ = v_a_4482_;
goto v___jp_4431_;
}
else
{
lean_object* v_a_4488_; 
lean_dec(v_a_4482_);
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4487_, 1);
v___y_4426_ = v_a_4477_;
v___y_4427_ = v___x_4480_;
v_a_4428_ = v_a_4488_;
goto v___jp_4425_;
}
}
}
else
{
lean_object* v_a_4489_; 
v_a_4489_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4481_, 1);
v___y_4426_ = v_a_4477_;
v___y_4427_ = v___x_4480_;
v_a_4428_ = v_a_4489_;
goto v___jp_4425_;
}
}
else
{
lean_object* v___x_4490_; lean_object* v___x_4491_; 
v___x_4490_ = lean_io_get_num_heartbeats();
lean_inc(v_a_4351_);
lean_inc_ref(v_a_4350_);
lean_inc(v_a_4349_);
lean_inc_ref(v_a_4348_);
v___x_4491_ = lean_apply_5(v_k_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_, lean_box(0));
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_object* v_a_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; uint8_t v___x_4495_; 
v_a_4492_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v___x_4491_, 1);
v___x_4493_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_4494_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__33);
v___x_4495_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4357_, v_options_4354_, v___x_4494_);
if (v___x_4495_ == 0)
{
v___y_4471_ = v_a_4477_;
v___y_4472_ = v___x_4490_;
v_a_4473_ = v_a_4492_;
goto v___jp_4470_;
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4497_; 
lean_inc(v_a_4492_);
v___x_4496_ = l_Lean_MessageData_ofExpr(v_a_4492_);
v___x_4497_ = l_Lean_addTrace___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppM_spec__1_spec__2(v___x_4493_, v___x_4496_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_dec_ref_known(v___x_4497_, 1);
v___y_4471_ = v_a_4477_;
v___y_4472_ = v___x_4490_;
v_a_4473_ = v_a_4492_;
goto v___jp_4470_;
}
else
{
lean_object* v_a_4498_; 
lean_dec(v_a_4492_);
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc(v_a_4498_);
lean_dec_ref_known(v___x_4497_, 1);
v___y_4465_ = v_a_4477_;
v___y_4466_ = v___x_4490_;
v_a_4467_ = v_a_4498_;
goto v___jp_4464_;
}
}
}
else
{
lean_object* v_a_4499_; 
v_a_4499_ = lean_ctor_get(v___x_4491_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4491_, 1);
v___y_4465_ = v_a_4477_;
v___y_4466_ = v___x_4490_;
v_a_4467_ = v_a_4499_;
goto v___jp_4464_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0___boxed(lean_object* v_f_4526_, lean_object* v_xs_4527_, lean_object* v_k_4528_, lean_object* v_a_4529_, lean_object* v_a_4530_, lean_object* v_a_4531_, lean_object* v_a_4532_, lean_object* v_a_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4526_, v_xs_4527_, v_k_4528_, v_a_4529_, v_a_4530_, v_a_4531_, v_a_4532_);
lean_dec(v_a_4532_);
lean_dec_ref(v_a_4531_);
lean_dec(v_a_4530_);
lean_dec_ref(v_a_4529_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27(lean_object* v_f_4535_, lean_object* v_xs_4536_, lean_object* v_a_4537_, lean_object* v_a_4538_, lean_object* v_a_4539_, lean_object* v_a_4540_){
_start:
{
lean_object* v___x_4542_; 
lean_inc(v_a_4540_);
lean_inc_ref(v_a_4539_);
lean_inc(v_a_4538_);
lean_inc_ref(v_a_4537_);
lean_inc_ref(v_f_4535_);
v___x_4542_ = lean_infer_type(v_f_4535_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
lean_dec_ref_known(v___x_4542_, 1);
v___x_4544_ = lean_unsigned_to_nat(0u);
v___x_4545_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppMArgs___closed__0));
lean_inc_ref(v_xs_4536_);
lean_inc_ref(v_f_4535_);
v___x_4546_ = lean_alloc_closure((void*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAppOptMAux___boxed), 12, 7);
lean_closure_set(v___x_4546_, 0, v_f_4535_);
lean_closure_set(v___x_4546_, 1, v_xs_4536_);
lean_closure_set(v___x_4546_, 2, v___x_4544_);
lean_closure_set(v___x_4546_, 3, v___x_4545_);
lean_closure_set(v___x_4546_, 4, v___x_4544_);
lean_closure_set(v___x_4546_, 5, v___x_4545_);
lean_closure_set(v___x_4546_, 6, v_a_4543_);
v___x_4547_ = 0;
v___x_4548_ = lean_box(v___x_4547_);
v___x_4549_ = lean_alloc_closure((void*)(l_Lean_Meta_withNewMCtxDepth___at___00Lean_Meta_mkAppM_spec__0___boxed), 8, 3);
lean_closure_set(v___x_4549_, 0, lean_box(0));
lean_closure_set(v___x_4549_, 1, v___x_4546_);
lean_closure_set(v___x_4549_, 2, v___x_4548_);
v___x_4550_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___at___00Lean_Meta_mkAppOptM_x27_spec__0(v_f_4535_, v_xs_4536_, v___x_4549_, v_a_4537_, v_a_4538_, v_a_4539_, v_a_4540_);
return v___x_4550_;
}
else
{
lean_dec_ref(v_xs_4536_);
lean_dec_ref(v_f_4535_);
return v___x_4542_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAppOptM_x27___boxed(lean_object* v_f_4551_, lean_object* v_xs_4552_, lean_object* v_a_4553_, lean_object* v_a_4554_, lean_object* v_a_4555_, lean_object* v_a_4556_, lean_object* v_a_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_Meta_mkAppOptM_x27(v_f_4551_, v_xs_4552_, v_a_4553_, v_a_4554_, v_a_4555_, v_a_4556_);
lean_dec(v_a_4556_);
lean_dec_ref(v_a_4555_);
lean_dec(v_a_4554_);
lean_dec_ref(v_a_4553_);
return v_res_4558_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqNDRec___closed__4(void){
_start:
{
lean_object* v___x_4566_; lean_object* v___x_4567_; 
v___x_4566_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__3));
v___x_4567_ = l_Lean_MessageData_ofFormat(v___x_4566_);
return v___x_4567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec(lean_object* v_motive_4568_, lean_object* v_h1_4569_, lean_object* v_h2_4570_, lean_object* v_a_4571_, lean_object* v_a_4572_, lean_object* v_a_4573_, lean_object* v_a_4574_){
_start:
{
lean_object* v___y_4577_; lean_object* v___y_4578_; lean_object* v___y_4579_; lean_object* v___y_4580_; lean_object* v___x_4586_; uint8_t v___x_4587_; 
v___x_4586_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4587_ = l_Lean_Expr_isAppOf(v_h2_4570_, v___x_4586_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; 
lean_inc_ref(v_h2_4570_);
v___x_4588_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4570_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_object* v_a_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; uint8_t v___x_4592_; 
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc(v_a_4589_);
lean_dec_ref_known(v___x_4588_, 1);
v___x_4590_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4591_ = lean_unsigned_to_nat(3u);
v___x_4592_ = l_Lean_Expr_isAppOfArity(v_a_4589_, v___x_4590_, v___x_4591_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
lean_dec_ref(v_h1_4569_);
lean_dec_ref(v_motive_4568_);
v___x_4593_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4594_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4595_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h2_4570_, v_a_4589_);
v___x_4596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4594_);
lean_ctor_set(v___x_4596_, 1, v___x_4595_);
v___x_4597_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4593_, v___x_4596_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
return v___x_4597_;
}
else
{
lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4598_ = l_Lean_Expr_appFn_x21(v_a_4589_);
v___x_4599_ = l_Lean_Expr_appFn_x21(v___x_4598_);
v___x_4600_ = l_Lean_Expr_appArg_x21(v___x_4599_);
lean_dec_ref(v___x_4599_);
v___x_4601_ = l_Lean_Expr_appArg_x21(v___x_4598_);
lean_dec_ref(v___x_4598_);
v___x_4602_ = l_Lean_Expr_appArg_x21(v_a_4589_);
lean_dec(v_a_4589_);
lean_inc_ref(v___x_4600_);
v___x_4603_ = l_Lean_Meta_getLevel(v___x_4600_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
if (lean_obj_tag(v___x_4603_) == 0)
{
lean_object* v_a_4604_; lean_object* v___x_4605_; 
v_a_4604_ = lean_ctor_get(v___x_4603_, 0);
lean_inc(v_a_4604_);
lean_dec_ref_known(v___x_4603_, 1);
lean_inc_ref(v_motive_4568_);
v___x_4605_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4568_, v_a_4571_, v_a_4572_, v_a_4573_, v_a_4574_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4608_; uint8_t v_isShared_4609_; uint8_t v_isSharedCheck_4629_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4608_ = v___x_4605_;
v_isShared_4609_ = v_isSharedCheck_4629_;
goto v_resetjp_4607_;
}
else
{
lean_inc(v_a_4606_);
lean_dec(v___x_4605_);
v___x_4608_ = lean_box(0);
v_isShared_4609_ = v_isSharedCheck_4629_;
goto v_resetjp_4607_;
}
v_resetjp_4607_:
{
if (lean_obj_tag(v_a_4606_) == 7)
{
lean_object* v_body_4610_; 
v_body_4610_ = lean_ctor_get(v_a_4606_, 2);
lean_inc_ref(v_body_4610_);
lean_dec_ref_known(v_a_4606_, 3);
if (lean_obj_tag(v_body_4610_) == 3)
{
lean_object* v_u_4611_; lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v___x_4615_; lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4627_; 
v_u_4611_ = lean_ctor_get(v_body_4610_, 0);
lean_inc(v_u_4611_);
lean_dec_ref_known(v_body_4610_, 1);
v___x_4612_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4613_ = lean_box(0);
v___x_4614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4614_, 0, v_a_4604_);
lean_ctor_set(v___x_4614_, 1, v___x_4613_);
v___x_4615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4615_, 0, v_u_4611_);
lean_ctor_set(v___x_4615_, 1, v___x_4614_);
v___x_4616_ = l_Lean_mkConst(v___x_4612_, v___x_4615_);
v___x_4617_ = lean_unsigned_to_nat(6u);
v___x_4618_ = lean_mk_empty_array_with_capacity(v___x_4617_);
v___x_4619_ = lean_array_push(v___x_4618_, v___x_4600_);
v___x_4620_ = lean_array_push(v___x_4619_, v___x_4601_);
v___x_4621_ = lean_array_push(v___x_4620_, v_motive_4568_);
v___x_4622_ = lean_array_push(v___x_4621_, v_h1_4569_);
v___x_4623_ = lean_array_push(v___x_4622_, v___x_4602_);
v___x_4624_ = lean_array_push(v___x_4623_, v_h2_4570_);
v___x_4625_ = l_Lean_mkAppN(v___x_4616_, v___x_4624_);
lean_dec_ref(v___x_4624_);
if (v_isShared_4609_ == 0)
{
lean_ctor_set(v___x_4608_, 0, v___x_4625_);
v___x_4627_ = v___x_4608_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
else
{
lean_dec_ref(v_body_4610_);
lean_del_object(v___x_4608_);
lean_dec(v_a_4604_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4600_);
lean_dec_ref(v_h2_4570_);
lean_dec_ref(v_h1_4569_);
v___y_4577_ = v_a_4571_;
v___y_4578_ = v_a_4572_;
v___y_4579_ = v_a_4573_;
v___y_4580_ = v_a_4574_;
goto v___jp_4576_;
}
}
else
{
lean_del_object(v___x_4608_);
lean_dec(v_a_4606_);
lean_dec(v_a_4604_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4600_);
lean_dec_ref(v_h2_4570_);
lean_dec_ref(v_h1_4569_);
v___y_4577_ = v_a_4571_;
v___y_4578_ = v_a_4572_;
v___y_4579_ = v_a_4573_;
v___y_4580_ = v_a_4574_;
goto v___jp_4576_;
}
}
}
else
{
lean_dec(v_a_4604_);
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4600_);
lean_dec_ref(v_h2_4570_);
lean_dec_ref(v_h1_4569_);
lean_dec_ref(v_motive_4568_);
return v___x_4605_;
}
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
lean_dec_ref(v___x_4602_);
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___x_4600_);
lean_dec_ref(v_h2_4570_);
lean_dec_ref(v_h1_4569_);
lean_dec_ref(v_motive_4568_);
v_a_4630_ = lean_ctor_get(v___x_4603_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4603_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4603_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4570_);
lean_dec_ref(v_h1_4569_);
lean_dec_ref(v_motive_4568_);
return v___x_4588_;
}
}
else
{
lean_object* v___x_4638_; 
lean_dec_ref(v_h2_4570_);
lean_dec_ref(v_motive_4568_);
v___x_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4638_, 0, v_h1_4569_);
return v___x_4638_;
}
v___jp_4576_:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; 
v___x_4581_ = ((lean_object*)(l_Lean_Meta_mkEqNDRec___closed__1));
v___x_4582_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4583_ = l_Lean_indentExpr(v_motive_4568_);
v___x_4584_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4582_);
lean_ctor_set(v___x_4584_, 1, v___x_4583_);
v___x_4585_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4581_, v___x_4584_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
return v___x_4585_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqNDRec___boxed(lean_object* v_motive_4639_, lean_object* v_h1_4640_, lean_object* v_h2_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
lean_object* v_res_4647_; 
v_res_4647_ = l_Lean_Meta_mkEqNDRec(v_motive_4639_, v_h1_4640_, v_h2_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec(lean_object* v_motive_4652_, lean_object* v_h1_4653_, lean_object* v_h2_4654_, lean_object* v_a_4655_, lean_object* v_a_4656_, lean_object* v_a_4657_, lean_object* v_a_4658_){
_start:
{
lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___x_4670_; uint8_t v___x_4671_; 
v___x_4670_ = ((lean_object*)(l_Lean_Meta_mkEqRefl___closed__1));
v___x_4671_ = l_Lean_Expr_isAppOf(v_h2_4654_, v___x_4670_);
if (v___x_4671_ == 0)
{
lean_object* v___x_4672_; 
lean_inc_ref(v_h2_4654_);
v___x_4672_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_h2_4654_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_object* v_a_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v_a_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_a_4673_);
lean_dec_ref_known(v___x_4672_, 1);
v___x_4674_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4675_ = lean_unsigned_to_nat(3u);
v___x_4676_ = l_Lean_Expr_isAppOfArity(v_a_4673_, v___x_4674_, v___x_4675_);
if (v___x_4676_ == 0)
{
lean_object* v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
lean_dec(v_a_4673_);
lean_dec_ref(v_h1_4653_);
lean_dec_ref(v_motive_4652_);
v___x_4677_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4678_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4679_ = l_Lean_indentExpr(v_h2_4654_);
v___x_4680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4678_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
v___x_4681_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4677_, v___x_4680_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
return v___x_4681_;
}
else
{
lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4682_ = l_Lean_Expr_appFn_x21(v_a_4673_);
v___x_4683_ = l_Lean_Expr_appFn_x21(v___x_4682_);
v___x_4684_ = l_Lean_Expr_appArg_x21(v___x_4683_);
lean_dec_ref(v___x_4683_);
v___x_4685_ = l_Lean_Expr_appArg_x21(v___x_4682_);
lean_dec_ref(v___x_4682_);
v___x_4686_ = l_Lean_Expr_appArg_x21(v_a_4673_);
lean_dec(v_a_4673_);
lean_inc_ref(v___x_4684_);
v___x_4687_ = l_Lean_Meta_getLevel(v___x_4684_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
if (lean_obj_tag(v___x_4687_) == 0)
{
lean_object* v_a_4688_; lean_object* v___x_4689_; 
v_a_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc(v_a_4688_);
lean_dec_ref_known(v___x_4687_, 1);
lean_inc_ref(v_motive_4652_);
v___x_4689_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_motive_4652_, v_a_4655_, v_a_4656_, v_a_4657_, v_a_4658_);
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_object* v_a_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4714_; 
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4689_);
if (v_isSharedCheck_4714_ == 0)
{
v___x_4692_ = v___x_4689_;
v_isShared_4693_ = v_isSharedCheck_4714_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_a_4690_);
lean_dec(v___x_4689_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4714_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
if (lean_obj_tag(v_a_4690_) == 7)
{
lean_object* v_body_4694_; 
v_body_4694_ = lean_ctor_get(v_a_4690_, 2);
lean_inc_ref(v_body_4694_);
lean_dec_ref_known(v_a_4690_, 3);
if (lean_obj_tag(v_body_4694_) == 7)
{
lean_object* v_body_4695_; 
v_body_4695_ = lean_ctor_get(v_body_4694_, 2);
lean_inc_ref(v_body_4695_);
lean_dec_ref_known(v_body_4694_, 3);
if (lean_obj_tag(v_body_4695_) == 3)
{
lean_object* v_u_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4712_; 
v_u_4696_ = lean_ctor_get(v_body_4695_, 0);
lean_inc(v_u_4696_);
lean_dec_ref_known(v_body_4695_, 1);
v___x_4697_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4698_ = lean_box(0);
v___x_4699_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4699_, 0, v_a_4688_);
lean_ctor_set(v___x_4699_, 1, v___x_4698_);
v___x_4700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4700_, 0, v_u_4696_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
v___x_4701_ = l_Lean_mkConst(v___x_4697_, v___x_4700_);
v___x_4702_ = lean_unsigned_to_nat(6u);
v___x_4703_ = lean_mk_empty_array_with_capacity(v___x_4702_);
v___x_4704_ = lean_array_push(v___x_4703_, v___x_4684_);
v___x_4705_ = lean_array_push(v___x_4704_, v___x_4685_);
v___x_4706_ = lean_array_push(v___x_4705_, v_motive_4652_);
v___x_4707_ = lean_array_push(v___x_4706_, v_h1_4653_);
v___x_4708_ = lean_array_push(v___x_4707_, v___x_4686_);
v___x_4709_ = lean_array_push(v___x_4708_, v_h2_4654_);
v___x_4710_ = l_Lean_mkAppN(v___x_4701_, v___x_4709_);
lean_dec_ref(v___x_4709_);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 0, v___x_4710_);
v___x_4712_ = v___x_4692_;
goto v_reusejp_4711_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4710_);
v___x_4712_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4711_;
}
v_reusejp_4711_:
{
return v___x_4712_;
}
}
else
{
lean_dec_ref(v_body_4695_);
lean_del_object(v___x_4692_);
lean_dec(v_a_4688_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v___x_4685_);
lean_dec_ref(v___x_4684_);
lean_dec_ref(v_h2_4654_);
lean_dec_ref(v_h1_4653_);
v___y_4661_ = v_a_4655_;
v___y_4662_ = v_a_4656_;
v___y_4663_ = v_a_4657_;
v___y_4664_ = v_a_4658_;
goto v___jp_4660_;
}
}
else
{
lean_dec_ref(v_body_4694_);
lean_del_object(v___x_4692_);
lean_dec(v_a_4688_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v___x_4685_);
lean_dec_ref(v___x_4684_);
lean_dec_ref(v_h2_4654_);
lean_dec_ref(v_h1_4653_);
v___y_4661_ = v_a_4655_;
v___y_4662_ = v_a_4656_;
v___y_4663_ = v_a_4657_;
v___y_4664_ = v_a_4658_;
goto v___jp_4660_;
}
}
else
{
lean_del_object(v___x_4692_);
lean_dec(v_a_4690_);
lean_dec(v_a_4688_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v___x_4685_);
lean_dec_ref(v___x_4684_);
lean_dec_ref(v_h2_4654_);
lean_dec_ref(v_h1_4653_);
v___y_4661_ = v_a_4655_;
v___y_4662_ = v_a_4656_;
v___y_4663_ = v_a_4657_;
v___y_4664_ = v_a_4658_;
goto v___jp_4660_;
}
}
}
else
{
lean_dec(v_a_4688_);
lean_dec_ref(v___x_4686_);
lean_dec_ref(v___x_4685_);
lean_dec_ref(v___x_4684_);
lean_dec_ref(v_h2_4654_);
lean_dec_ref(v_h1_4653_);
lean_dec_ref(v_motive_4652_);
return v___x_4689_;
}
}
else
{
lean_object* v_a_4715_; lean_object* v___x_4717_; uint8_t v_isShared_4718_; uint8_t v_isSharedCheck_4722_; 
lean_dec_ref(v___x_4686_);
lean_dec_ref(v___x_4685_);
lean_dec_ref(v___x_4684_);
lean_dec_ref(v_h2_4654_);
lean_dec_ref(v_h1_4653_);
lean_dec_ref(v_motive_4652_);
v_a_4715_ = lean_ctor_get(v___x_4687_, 0);
v_isSharedCheck_4722_ = !lean_is_exclusive(v___x_4687_);
if (v_isSharedCheck_4722_ == 0)
{
v___x_4717_ = v___x_4687_;
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
else
{
lean_inc(v_a_4715_);
lean_dec(v___x_4687_);
v___x_4717_ = lean_box(0);
v_isShared_4718_ = v_isSharedCheck_4722_;
goto v_resetjp_4716_;
}
v_resetjp_4716_:
{
lean_object* v___x_4720_; 
if (v_isShared_4718_ == 0)
{
v___x_4720_ = v___x_4717_;
goto v_reusejp_4719_;
}
else
{
lean_object* v_reuseFailAlloc_4721_; 
v_reuseFailAlloc_4721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4721_, 0, v_a_4715_);
v___x_4720_ = v_reuseFailAlloc_4721_;
goto v_reusejp_4719_;
}
v_reusejp_4719_:
{
return v___x_4720_;
}
}
}
}
}
else
{
lean_dec_ref(v_h2_4654_);
lean_dec_ref(v_h1_4653_);
lean_dec_ref(v_motive_4652_);
return v___x_4672_;
}
}
else
{
lean_object* v___x_4723_; 
lean_dec_ref(v_h2_4654_);
lean_dec_ref(v_motive_4652_);
v___x_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4723_, 0, v_h1_4653_);
return v___x_4723_;
}
v___jp_4660_:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
v___x_4665_ = ((lean_object*)(l_Lean_Meta_mkEqRec___closed__1));
v___x_4666_ = lean_obj_once(&l_Lean_Meta_mkEqNDRec___closed__4, &l_Lean_Meta_mkEqNDRec___closed__4_once, _init_l_Lean_Meta_mkEqNDRec___closed__4);
v___x_4667_ = l_Lean_indentExpr(v_motive_4652_);
v___x_4668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4666_);
lean_ctor_set(v___x_4668_, 1, v___x_4667_);
v___x_4669_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4665_, v___x_4668_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
return v___x_4669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqRec___boxed(lean_object* v_motive_4724_, lean_object* v_h1_4725_, lean_object* v_h2_4726_, lean_object* v_a_4727_, lean_object* v_a_4728_, lean_object* v_a_4729_, lean_object* v_a_4730_, lean_object* v_a_4731_){
_start:
{
lean_object* v_res_4732_; 
v_res_4732_ = l_Lean_Meta_mkEqRec(v_motive_4724_, v_h1_4725_, v_h2_4726_, v_a_4727_, v_a_4728_, v_a_4729_, v_a_4730_);
lean_dec(v_a_4730_);
lean_dec_ref(v_a_4729_);
lean_dec(v_a_4728_);
lean_dec_ref(v_a_4727_);
return v_res_4732_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore(lean_object* v_00_u03b1_4737_, lean_object* v_00_u03b2_4738_, lean_object* v_h_4739_, lean_object* v_a_4740_, lean_object* v_a_4741_, lean_object* v_a_4742_, lean_object* v_a_4743_, lean_object* v_a_4744_){
_start:
{
lean_object* v___x_4746_; 
lean_inc_ref(v_00_u03b1_4737_);
v___x_4746_ = l_Lean_Meta_getLevel(v_00_u03b1_4737_, v_a_4741_, v_a_4742_, v_a_4743_, v_a_4744_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; lean_object* v___x_4749_; uint8_t v_isShared_4750_; uint8_t v_isSharedCheck_4759_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4759_ == 0)
{
v___x_4749_ = v___x_4746_;
v_isShared_4750_ = v_isSharedCheck_4759_;
goto v_resetjp_4748_;
}
else
{
lean_inc(v_a_4747_);
lean_dec(v___x_4746_);
v___x_4749_ = lean_box(0);
v_isShared_4750_ = v_isSharedCheck_4759_;
goto v_resetjp_4748_;
}
v_resetjp_4748_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4757_; 
v___x_4751_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4752_ = lean_box(0);
v___x_4753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4753_, 0, v_a_4747_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
v___x_4754_ = l_Lean_mkConst(v___x_4751_, v___x_4753_);
v___x_4755_ = l_Lean_mkApp4(v___x_4754_, v_00_u03b1_4737_, v_00_u03b2_4738_, v_h_4739_, v_a_4740_);
if (v_isShared_4750_ == 0)
{
lean_ctor_set(v___x_4749_, 0, v___x_4755_);
v___x_4757_ = v___x_4749_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4755_);
v___x_4757_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
return v___x_4757_;
}
}
}
else
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec_ref(v_a_4740_);
lean_dec_ref(v_h_4739_);
lean_dec_ref(v_00_u03b2_4738_);
lean_dec_ref(v_00_u03b1_4737_);
v_a_4760_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4746_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4746_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPCore___boxed(lean_object* v_00_u03b1_4768_, lean_object* v_00_u03b2_4769_, lean_object* v_h_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_, lean_object* v_a_4773_, lean_object* v_a_4774_, lean_object* v_a_4775_, lean_object* v_a_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l_Lean_Meta_mkEqMPCore(v_00_u03b1_4768_, v_00_u03b2_4769_, v_h_4770_, v_a_4771_, v_a_4772_, v_a_4773_, v_a_4774_, v_a_4775_);
lean_dec(v_a_4775_);
lean_dec_ref(v_a_4774_);
lean_dec(v_a_4773_);
lean_dec_ref(v_a_4772_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP(lean_object* v_eqProof_4778_, lean_object* v_pr_4779_, lean_object* v_a_4780_, lean_object* v_a_4781_, lean_object* v_a_4782_, lean_object* v_a_4783_){
_start:
{
lean_object* v___x_4785_; 
lean_inc_ref(v_eqProof_4778_);
v___x_4785_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_infer(v_eqProof_4778_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; uint8_t v___x_4789_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
lean_inc(v_a_4786_);
lean_dec_ref_known(v___x_4785_, 1);
v___x_4787_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4788_ = lean_unsigned_to_nat(3u);
v___x_4789_ = l_Lean_Expr_isAppOfArity(v_a_4786_, v___x_4787_, v___x_4788_);
if (v___x_4789_ == 0)
{
lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
lean_dec_ref(v_pr_4779_);
v___x_4790_ = ((lean_object*)(l_Lean_Meta_mkEqMPCore___closed__1));
v___x_4791_ = lean_obj_once(&l_Lean_Meta_mkEqSymm___closed__4, &l_Lean_Meta_mkEqSymm___closed__4_once, _init_l_Lean_Meta_mkEqSymm___closed__4);
v___x_4792_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_eqProof_4778_, v_a_4786_);
v___x_4793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4791_);
lean_ctor_set(v___x_4793_, 1, v___x_4792_);
v___x_4794_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_4790_, v___x_4793_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
return v___x_4794_;
}
else
{
lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4795_ = l_Lean_Expr_appFn_x21(v_a_4786_);
v___x_4796_ = l_Lean_Expr_appArg_x21(v___x_4795_);
lean_dec_ref(v___x_4795_);
v___x_4797_ = l_Lean_Expr_appArg_x21(v_a_4786_);
lean_dec(v_a_4786_);
v___x_4798_ = l_Lean_Meta_mkEqMPCore(v___x_4796_, v___x_4797_, v_eqProof_4778_, v_pr_4779_, v_a_4780_, v_a_4781_, v_a_4782_, v_a_4783_);
return v___x_4798_;
}
}
else
{
lean_dec_ref(v_pr_4779_);
lean_dec_ref(v_eqProof_4778_);
return v___x_4785_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMP___boxed(lean_object* v_eqProof_4799_, lean_object* v_pr_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_, lean_object* v_a_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Lean_Meta_mkEqMP(v_eqProof_4799_, v_pr_4800_, v_a_4801_, v_a_4802_, v_a_4803_, v_a_4804_);
lean_dec(v_a_4804_);
lean_dec_ref(v_a_4803_);
lean_dec(v_a_4802_);
lean_dec_ref(v_a_4801_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR(lean_object* v_eqProof_4811_, lean_object* v_pr_4812_, lean_object* v_a_4813_, lean_object* v_a_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_){
_start:
{
lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v___x_4818_ = ((lean_object*)(l_Lean_Meta_mkEqMPR___closed__1));
v___x_4819_ = lean_unsigned_to_nat(2u);
v___x_4820_ = lean_mk_empty_array_with_capacity(v___x_4819_);
v___x_4821_ = lean_array_push(v___x_4820_, v_eqProof_4811_);
v___x_4822_ = lean_array_push(v___x_4821_, v_pr_4812_);
v___x_4823_ = l_Lean_Meta_mkAppM(v___x_4818_, v___x_4822_, v_a_4813_, v_a_4814_, v_a_4815_, v_a_4816_);
return v___x_4823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqMPR___boxed(lean_object* v_eqProof_4824_, lean_object* v_pr_4825_, lean_object* v_a_4826_, lean_object* v_a_4827_, lean_object* v_a_4828_, lean_object* v_a_4829_, lean_object* v_a_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l_Lean_Meta_mkEqMPR(v_eqProof_4824_, v_pr_4825_, v_a_4826_, v_a_4827_, v_a_4828_, v_a_4829_);
lean_dec(v_a_4829_);
lean_dec_ref(v_a_4828_);
lean_dec(v_a_4827_);
lean_dec_ref(v_a_4826_);
return v_res_4831_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(lean_object* v_msg_4832_, lean_object* v___y_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v___f_4838_; lean_object* v___x_12329__overap_4839_; lean_object* v___x_4840_; 
v___f_4838_ = ((lean_object*)(l_panic___at___00Lean_Meta_congrArg_x3f_spec__0___closed__0));
v___x_12329__overap_4839_ = lean_panic_fn_borrowed(v___f_4838_, v_msg_4832_);
lean_inc(v___y_4836_);
lean_inc_ref(v___y_4835_);
lean_inc(v___y_4834_);
lean_inc_ref(v___y_4833_);
v___x_4840_ = lean_apply_5(v___x_12329__overap_4839_, v___y_4833_, v___y_4834_, v___y_4835_, v___y_4836_, lean_box(0));
return v___x_4840_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_mkNoConfusion_spec__0___boxed(lean_object* v_msg_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_, lean_object* v___y_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_){
_start:
{
lean_object* v_res_4847_; 
v_res_4847_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v_msg_4841_, v___y_4842_, v___y_4843_, v___y_4844_, v___y_4845_);
lean_dec(v___y_4845_);
lean_dec_ref(v___y_4844_);
lean_dec(v___y_4843_);
lean_dec_ref(v___y_4842_);
return v_res_4847_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(lean_object* v_constName_4848_, uint8_t v_skipRealize_4849_, lean_object* v___y_4850_){
_start:
{
lean_object* v___x_4852_; lean_object* v_env_4853_; uint8_t v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v___x_4852_ = lean_st_ref_get(v___y_4850_);
v_env_4853_ = lean_ctor_get(v___x_4852_, 0);
lean_inc_ref(v_env_4853_);
lean_dec(v___x_4852_);
v___x_4854_ = l_Lean_Environment_contains(v_env_4853_, v_constName_4848_, v_skipRealize_4849_);
v___x_4855_ = lean_box(v___x_4854_);
v___x_4856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4855_);
return v___x_4856_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg___boxed(lean_object* v_constName_4857_, lean_object* v_skipRealize_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
uint8_t v_skipRealize_boxed_4861_; lean_object* v_res_4862_; 
v_skipRealize_boxed_4861_ = lean_unbox(v_skipRealize_4858_);
v_res_4862_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4857_, v_skipRealize_boxed_4861_, v___y_4859_);
lean_dec(v___y_4859_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(lean_object* v_constName_4863_, uint8_t v_skipRealize_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_, lean_object* v___y_4868_){
_start:
{
lean_object* v___x_4870_; 
v___x_4870_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v_constName_4863_, v_skipRealize_4864_, v___y_4868_);
return v___x_4870_;
}
}
LEAN_EXPORT lean_object* l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___boxed(lean_object* v_constName_4871_, lean_object* v_skipRealize_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_, lean_object* v___y_4877_){
_start:
{
uint8_t v_skipRealize_boxed_4878_; lean_object* v_res_4879_; 
v_skipRealize_boxed_4878_ = lean_unbox(v_skipRealize_4872_);
v_res_4879_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2(v_constName_4871_, v_skipRealize_boxed_4878_, v___y_4873_, v___y_4874_, v___y_4875_, v___y_4876_);
lean_dec(v___y_4876_);
lean_dec_ref(v___y_4875_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
return v_res_4879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0(uint8_t v___y_4880_, uint8_t v___x_4881_, lean_object* v_P_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v___x_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; uint8_t v___x_4891_; lean_object* v___x_4892_; 
v___x_4888_ = lean_unsigned_to_nat(1u);
v___x_4889_ = lean_mk_empty_array_with_capacity(v___x_4888_);
lean_inc_ref(v_P_4882_);
v___x_4890_ = lean_array_push(v___x_4889_, v_P_4882_);
v___x_4891_ = 1;
v___x_4892_ = l_Lean_Meta_mkLambdaFVars(v___x_4890_, v_P_4882_, v___y_4880_, v___x_4881_, v___y_4880_, v___x_4881_, v___x_4891_, v___y_4883_, v___y_4884_, v___y_4885_, v___y_4886_);
lean_dec_ref(v___x_4890_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___lam__0___boxed(lean_object* v___y_4893_, lean_object* v___x_4894_, lean_object* v_P_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
uint8_t v___y_13587__boxed_4901_; uint8_t v___x_13588__boxed_4902_; lean_object* v_res_4903_; 
v___y_13587__boxed_4901_ = lean_unbox(v___y_4893_);
v___x_13588__boxed_4902_ = lean_unbox(v___x_4894_);
v_res_4903_ = l_Lean_Meta_mkNoConfusion___lam__0(v___y_13587__boxed_4901_, v___x_13588__boxed_4902_, v_P_4895_, v___y_4896_, v___y_4897_, v___y_4898_, v___y_4899_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
lean_dec(v___y_4897_);
lean_dec_ref(v___y_4896_);
return v_res_4903_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4905_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__0));
v___x_4906_ = l_Lean_stringToMessageData(v___x_4905_);
return v___x_4906_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___x_4909_; 
v___x_4908_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__2));
v___x_4909_ = l_Lean_stringToMessageData(v___x_4908_);
return v___x_4909_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(lean_object* v_range_4910_, lean_object* v_b_4911_, lean_object* v_i_4912_, lean_object* v___y_4913_, lean_object* v___y_4914_, lean_object* v___y_4915_, lean_object* v___y_4916_){
_start:
{
lean_object* v_stop_4918_; lean_object* v_step_4919_; lean_object* v_a_4921_; uint8_t v___x_4924_; 
v_stop_4918_ = lean_ctor_get(v_range_4910_, 1);
v_step_4919_ = lean_ctor_get(v_range_4910_, 2);
v___x_4924_ = lean_nat_dec_lt(v_i_4912_, v_stop_4918_);
if (v___x_4924_ == 0)
{
lean_object* v___x_4925_; 
lean_dec(v_i_4912_);
v___x_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4925_, 0, v_b_4911_);
return v___x_4925_;
}
else
{
lean_object* v___x_4926_; 
lean_inc(v___y_4916_);
lean_inc_ref(v___y_4915_);
lean_inc(v___y_4914_);
lean_inc_ref(v___y_4913_);
lean_inc_ref(v_b_4911_);
v___x_4926_ = lean_infer_type(v_b_4911_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4926_) == 0)
{
lean_object* v_a_4927_; lean_object* v___x_4928_; 
v_a_4927_ = lean_ctor_get(v___x_4926_, 0);
lean_inc(v_a_4927_);
lean_dec_ref_known(v___x_4926_, 1);
v___x_4928_ = l_Lean_Meta_whnfForall(v_a_4927_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_object* v_a_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v_a_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc(v_a_4929_);
lean_dec_ref_known(v___x_4928_, 1);
v___x_4930_ = l_Lean_Expr_bindingDomain_x21(v_a_4929_);
lean_dec(v_a_4929_);
lean_inc(v___y_4916_);
lean_inc_ref(v___y_4915_);
lean_inc(v___y_4914_);
lean_inc_ref(v___y_4913_);
v___x_4931_ = lean_whnf(v___x_4930_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_object* v_a_4932_; lean_object* v___x_4933_; lean_object* v___x_4934_; uint8_t v___x_4935_; 
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
lean_inc(v_a_4932_);
lean_dec_ref_known(v___x_4931_, 1);
v___x_4933_ = ((lean_object*)(l_Lean_Meta_mkHEq___closed__1));
v___x_4934_ = lean_unsigned_to_nat(4u);
v___x_4935_ = l_Lean_Expr_isAppOfArity(v_a_4932_, v___x_4933_, v___x_4934_);
if (v___x_4935_ == 0)
{
lean_object* v___x_4936_; lean_object* v___x_4937_; uint8_t v___x_4938_; 
v___x_4936_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_4937_ = lean_unsigned_to_nat(3u);
v___x_4938_ = l_Lean_Expr_isAppOfArity(v_a_4932_, v___x_4936_, v___x_4937_);
if (v___x_4938_ == 0)
{
lean_object* v___x_4939_; 
lean_dec(v_i_4912_);
lean_inc(v___y_4916_);
lean_inc_ref(v___y_4915_);
lean_inc(v___y_4914_);
lean_inc_ref(v___y_4913_);
v___x_4939_ = lean_infer_type(v_b_4911_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_object* v_a_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v_a_4950_; lean_object* v___x_4952_; uint8_t v_isShared_4953_; uint8_t v_isSharedCheck_4957_; 
v_a_4940_ = lean_ctor_get(v___x_4939_, 0);
lean_inc(v_a_4940_);
lean_dec_ref_known(v___x_4939_, 1);
v___x_4941_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__1);
v___x_4942_ = l_Lean_MessageData_ofExpr(v_a_4932_);
v___x_4943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4943_, 0, v___x_4941_);
lean_ctor_set(v___x_4943_, 1, v___x_4942_);
v___x_4944_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___closed__3);
v___x_4945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4943_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
v___x_4946_ = lean_unsigned_to_nat(30u);
v___x_4947_ = l_Lean_inlineExpr(v_a_4940_, v___x_4946_);
v___x_4948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4945_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
v___x_4949_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_4948_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
v_a_4950_ = lean_ctor_get(v___x_4949_, 0);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4949_);
if (v_isSharedCheck_4957_ == 0)
{
v___x_4952_ = v___x_4949_;
v_isShared_4953_ = v_isSharedCheck_4957_;
goto v_resetjp_4951_;
}
else
{
lean_inc(v_a_4950_);
lean_dec(v___x_4949_);
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
else
{
lean_dec(v_a_4932_);
return v___x_4939_;
}
}
else
{
lean_object* v___x_4958_; lean_object* v___x_4959_; lean_object* v___x_4960_; 
v___x_4958_ = l_Lean_Expr_appFn_x21(v_a_4932_);
lean_dec(v_a_4932_);
v___x_4959_ = l_Lean_Expr_appArg_x21(v___x_4958_);
lean_dec_ref(v___x_4958_);
v___x_4960_ = l_Lean_Meta_mkEqRefl(v___x_4959_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; lean_object* v___x_4962_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref_known(v___x_4960_, 1);
v___x_4962_ = l_Lean_Expr_app___override(v_b_4911_, v_a_4961_);
v_a_4921_ = v___x_4962_;
goto v___jp_4920_;
}
else
{
lean_dec(v_i_4912_);
lean_dec_ref(v_b_4911_);
return v___x_4960_;
}
}
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; 
v___x_4963_ = l_Lean_Expr_appFn_x21(v_a_4932_);
lean_dec(v_a_4932_);
v___x_4964_ = l_Lean_Expr_appFn_x21(v___x_4963_);
lean_dec_ref(v___x_4963_);
v___x_4965_ = l_Lean_Expr_appArg_x21(v___x_4964_);
lean_dec_ref(v___x_4964_);
v___x_4966_ = l_Lean_Meta_mkHEqRefl(v___x_4965_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_);
if (lean_obj_tag(v___x_4966_) == 0)
{
lean_object* v_a_4967_; lean_object* v___x_4968_; 
v_a_4967_ = lean_ctor_get(v___x_4966_, 0);
lean_inc(v_a_4967_);
lean_dec_ref_known(v___x_4966_, 1);
v___x_4968_ = l_Lean_Expr_app___override(v_b_4911_, v_a_4967_);
v_a_4921_ = v___x_4968_;
goto v___jp_4920_;
}
else
{
lean_dec(v_i_4912_);
lean_dec_ref(v_b_4911_);
return v___x_4966_;
}
}
}
else
{
lean_dec(v_i_4912_);
lean_dec_ref(v_b_4911_);
return v___x_4931_;
}
}
else
{
lean_dec(v_i_4912_);
lean_dec_ref(v_b_4911_);
return v___x_4928_;
}
}
else
{
lean_dec(v_i_4912_);
lean_dec_ref(v_b_4911_);
return v___x_4926_;
}
}
v___jp_4920_:
{
lean_object* v___x_4922_; 
v___x_4922_ = lean_nat_add(v_i_4912_, v_step_4919_);
lean_dec(v_i_4912_);
v_b_4911_ = v_a_4921_;
v_i_4912_ = v___x_4922_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg___boxed(lean_object* v_range_4969_, lean_object* v_b_4970_, lean_object* v_i_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_4969_, v_b_4970_, v_i_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec_ref(v_range_4969_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(lean_object* v_k_4978_, lean_object* v_b_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v___x_4985_; 
lean_inc(v___y_4983_);
lean_inc_ref(v___y_4982_);
lean_inc(v___y_4981_);
lean_inc_ref(v___y_4980_);
v___x_4985_ = lean_apply_6(v_k_4978_, v_b_4979_, v___y_4980_, v___y_4981_, v___y_4982_, v___y_4983_, lean_box(0));
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed(lean_object* v_k_4986_, lean_object* v_b_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v_res_4993_; 
v_res_4993_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0(v_k_4986_, v_b_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_);
lean_dec(v___y_4991_);
lean_dec_ref(v___y_4990_);
lean_dec(v___y_4989_);
lean_dec_ref(v___y_4988_);
return v_res_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(lean_object* v_name_4994_, uint8_t v_bi_4995_, lean_object* v_type_4996_, lean_object* v_k_4997_, uint8_t v_kind_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_){
_start:
{
lean_object* v___f_5004_; lean_object* v___x_5005_; 
v___f_5004_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5004_, 0, v_k_4997_);
v___x_5005_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_4994_, v_bi_4995_, v_type_4996_, v___f_5004_, v_kind_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_object* v_a_5006_; lean_object* v___x_5008_; uint8_t v_isShared_5009_; uint8_t v_isSharedCheck_5013_; 
v_a_5006_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5013_ == 0)
{
v___x_5008_ = v___x_5005_;
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
else
{
lean_inc(v_a_5006_);
lean_dec(v___x_5005_);
v___x_5008_ = lean_box(0);
v_isShared_5009_ = v_isSharedCheck_5013_;
goto v_resetjp_5007_;
}
v_resetjp_5007_:
{
lean_object* v___x_5011_; 
if (v_isShared_5009_ == 0)
{
v___x_5011_ = v___x_5008_;
goto v_reusejp_5010_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_a_5006_);
v___x_5011_ = v_reuseFailAlloc_5012_;
goto v_reusejp_5010_;
}
v_reusejp_5010_:
{
return v___x_5011_;
}
}
}
else
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
v_a_5014_ = lean_ctor_get(v___x_5005_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v___x_5005_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v___x_5005_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v___x_5005_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
v___x_5019_ = v___x_5016_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v_a_5014_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg___boxed(lean_object* v_name_5022_, lean_object* v_bi_5023_, lean_object* v_type_5024_, lean_object* v_k_5025_, lean_object* v_kind_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
uint8_t v_bi_boxed_5032_; uint8_t v_kind_boxed_5033_; lean_object* v_res_5034_; 
v_bi_boxed_5032_ = lean_unbox(v_bi_5023_);
v_kind_boxed_5033_ = lean_unbox(v_kind_5026_);
v_res_5034_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5022_, v_bi_boxed_5032_, v_type_5024_, v_k_5025_, v_kind_boxed_5033_, v___y_5027_, v___y_5028_, v___y_5029_, v___y_5030_);
lean_dec(v___y_5030_);
lean_dec_ref(v___y_5029_);
lean_dec(v___y_5028_);
lean_dec_ref(v___y_5027_);
return v_res_5034_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(lean_object* v_name_5035_, lean_object* v_type_5036_, lean_object* v_k_5037_, lean_object* v___y_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_){
_start:
{
uint8_t v___x_5043_; uint8_t v___x_5044_; lean_object* v___x_5045_; 
v___x_5043_ = 0;
v___x_5044_ = 0;
v___x_5045_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5035_, v___x_5043_, v_type_5036_, v_k_5037_, v___x_5044_, v___y_5038_, v___y_5039_, v___y_5040_, v___y_5041_);
return v___x_5045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg___boxed(lean_object* v_name_5046_, lean_object* v_type_5047_, lean_object* v_k_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5046_, v_type_5047_, v_k_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
return v_res_5054_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__4(void){
_start:
{
lean_object* v___x_5061_; lean_object* v___x_5062_; 
v___x_5061_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__3));
v___x_5062_ = l_Lean_MessageData_ofFormat(v___x_5061_);
return v___x_5062_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__6(void){
_start:
{
lean_object* v___x_5064_; lean_object* v___x_5065_; 
v___x_5064_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__5));
v___x_5065_ = l_Lean_stringToMessageData(v___x_5064_);
return v___x_5065_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__8(void){
_start:
{
lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5067_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__7));
v___x_5068_ = l_Lean_stringToMessageData(v___x_5067_);
return v___x_5068_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__11(void){
_start:
{
lean_object* v___x_5072_; lean_object* v___x_5073_; 
v___x_5072_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__10));
v___x_5073_ = l_Lean_MessageData_ofFormat(v___x_5072_);
return v___x_5073_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__14(void){
_start:
{
lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5081_; 
v___x_5076_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__13));
v___x_5077_ = lean_unsigned_to_nat(10u);
v___x_5078_ = lean_unsigned_to_nat(511u);
v___x_5079_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__12));
v___x_5080_ = ((lean_object*)(l_Lean_Meta_congrArg_x3f___closed__3));
v___x_5081_ = l_mkPanicMessageWithDecl(v___x_5080_, v___x_5079_, v___x_5078_, v___x_5077_, v___x_5076_);
return v___x_5081_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__16(void){
_start:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; 
v___x_5083_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__15));
v___x_5084_ = l_Lean_stringToMessageData(v___x_5083_);
return v___x_5084_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__23(void){
_start:
{
lean_object* v___x_5093_; lean_object* v___x_5094_; 
v___x_5093_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__22));
v___x_5094_ = l_Lean_stringToMessageData(v___x_5093_);
return v___x_5094_;
}
}
static lean_object* _init_l_Lean_Meta_mkNoConfusion___closed__24(void){
_start:
{
lean_object* v___x_5095_; lean_object* v___x_5096_; 
v___x_5095_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5096_ = l_Lean_MessageData_ofName(v___x_5095_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion(lean_object* v_target_5097_, lean_object* v_h_5098_, lean_object* v_a_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v___x_5104_; 
lean_inc(v_a_5102_);
lean_inc_ref(v_a_5101_);
lean_inc(v_a_5100_);
lean_inc_ref(v_a_5099_);
lean_inc_ref(v_h_5098_);
v___x_5104_ = lean_infer_type(v_h_5098_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5104_) == 0)
{
lean_object* v_a_5105_; lean_object* v___x_5106_; 
v_a_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc(v_a_5105_);
lean_dec_ref_known(v___x_5104_, 1);
lean_inc(v_a_5102_);
lean_inc_ref(v_a_5101_);
lean_inc(v_a_5100_);
lean_inc_ref(v_a_5099_);
v___x_5106_ = lean_whnf(v_a_5105_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5106_) == 0)
{
lean_object* v_a_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; uint8_t v___x_5110_; 
v_a_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc(v_a_5107_);
lean_dec_ref_known(v___x_5106_, 1);
v___x_5108_ = ((lean_object*)(l_Lean_Meta_mkEq___closed__1));
v___x_5109_ = lean_unsigned_to_nat(3u);
v___x_5110_ = l_Lean_Expr_isAppOfArity(v_a_5107_, v___x_5108_, v___x_5109_);
if (v___x_5110_ == 0)
{
lean_object* v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; lean_object* v___x_5114_; lean_object* v___x_5115_; 
lean_dec_ref(v_target_5097_);
v___x_5111_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5112_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__4, &l_Lean_Meta_mkNoConfusion___closed__4_once, _init_l_Lean_Meta_mkNoConfusion___closed__4);
v___x_5113_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_h_5098_, v_a_5107_);
v___x_5114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5114_, 0, v___x_5112_);
lean_ctor_set(v___x_5114_, 1, v___x_5113_);
v___x_5115_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5111_, v___x_5114_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
return v___x_5115_;
}
else
{
lean_object* v___x_5116_; lean_object* v___x_5117_; lean_object* v___x_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v___y_5122_; lean_object* v___y_5123_; lean_object* v___y_5124_; lean_object* v___y_5125_; lean_object* v___x_5134_; 
v___x_5116_ = l_Lean_Expr_appFn_x21(v_a_5107_);
v___x_5117_ = l_Lean_Expr_appFn_x21(v___x_5116_);
v___x_5118_ = l_Lean_Expr_appArg_x21(v___x_5117_);
lean_dec_ref(v___x_5117_);
v___x_5119_ = l_Lean_Expr_appArg_x21(v___x_5116_);
lean_dec_ref(v___x_5116_);
v___x_5120_ = l_Lean_Expr_appArg_x21(v_a_5107_);
lean_dec(v_a_5107_);
v___x_5134_ = l_Lean_Meta_whnfD(v___x_5118_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5134_) == 0)
{
lean_object* v_a_5135_; lean_object* v___y_5137_; lean_object* v___y_5138_; lean_object* v___y_5139_; lean_object* v___y_5140_; lean_object* v___x_5146_; 
v_a_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc(v_a_5135_);
lean_dec_ref_known(v___x_5134_, 1);
v___x_5146_ = l_Lean_Expr_getAppFn(v_a_5135_);
if (lean_obj_tag(v___x_5146_) == 4)
{
lean_object* v_declName_5147_; lean_object* v_us_5148_; lean_object* v___x_5149_; lean_object* v_env_5150_; uint8_t v___x_5151_; lean_object* v___x_5152_; 
v_declName_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_declName_5147_);
v_us_5148_ = lean_ctor_get(v___x_5146_, 1);
lean_inc(v_us_5148_);
lean_dec_ref_known(v___x_5146_, 2);
v___x_5149_ = lean_st_ref_get(v_a_5102_);
v_env_5150_ = lean_ctor_get(v___x_5149_, 0);
lean_inc_ref(v_env_5150_);
lean_dec(v___x_5149_);
v___x_5151_ = 0;
v___x_5152_ = l_Lean_Environment_find_x3f(v_env_5150_, v_declName_5147_, v___x_5151_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_dec(v_us_5148_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v___y_5137_ = v_a_5099_;
v___y_5138_ = v_a_5100_;
v___y_5139_ = v_a_5101_;
v___y_5140_ = v_a_5102_;
goto v___jp_5136_;
}
else
{
lean_object* v_val_5153_; 
v_val_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc(v_val_5153_);
lean_dec_ref_known(v___x_5152_, 1);
if (lean_obj_tag(v_val_5153_) == 5)
{
lean_object* v_val_5154_; lean_object* v___x_5155_; 
v_val_5154_ = lean_ctor_get(v_val_5153_, 0);
lean_inc_ref(v_val_5154_);
lean_dec_ref_known(v_val_5153_, 1);
lean_inc_ref(v_target_5097_);
v___x_5155_ = l_Lean_Meta_getLevel(v_target_5097_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5155_) == 0)
{
lean_object* v_a_5156_; lean_object* v___x_5157_; 
v_a_5156_ = lean_ctor_get(v___x_5155_, 0);
lean_inc(v_a_5156_);
lean_dec_ref_known(v___x_5155_, 1);
lean_inc_ref(v___x_5119_);
v___x_5157_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5119_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5157_) == 0)
{
lean_object* v_a_5158_; 
v_a_5158_ = lean_ctor_get(v___x_5157_, 0);
lean_inc(v_a_5158_);
lean_dec_ref_known(v___x_5157_, 1);
if (lean_obj_tag(v_a_5158_) == 1)
{
lean_object* v_val_5159_; lean_object* v_fst_5160_; lean_object* v_snd_5161_; lean_object* v___x_5163_; uint8_t v_isShared_5164_; uint8_t v_isSharedCheck_5375_; 
v_val_5159_ = lean_ctor_get(v_a_5158_, 0);
lean_inc(v_val_5159_);
lean_dec_ref_known(v_a_5158_, 1);
v_fst_5160_ = lean_ctor_get(v_val_5159_, 0);
v_snd_5161_ = lean_ctor_get(v_val_5159_, 1);
v_isSharedCheck_5375_ = !lean_is_exclusive(v_val_5159_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5163_ = v_val_5159_;
v_isShared_5164_ = v_isSharedCheck_5375_;
goto v_resetjp_5162_;
}
else
{
lean_inc(v_snd_5161_);
lean_inc(v_fst_5160_);
lean_dec(v_val_5159_);
v___x_5163_ = lean_box(0);
v_isShared_5164_ = v_isSharedCheck_5375_;
goto v_resetjp_5162_;
}
v_resetjp_5162_:
{
lean_object* v___x_5165_; 
lean_inc_ref(v___x_5120_);
v___x_5165_ = l_Lean_Meta_constructorApp_x27_x3f(v___x_5120_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref_known(v___x_5165_, 1);
if (lean_obj_tag(v_a_5166_) == 1)
{
lean_object* v_val_5167_; lean_object* v_fst_5168_; lean_object* v_snd_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5366_; 
v_val_5167_ = lean_ctor_get(v_a_5166_, 0);
lean_inc(v_val_5167_);
lean_dec_ref_known(v_a_5166_, 1);
v_fst_5168_ = lean_ctor_get(v_val_5167_, 0);
v_snd_5169_ = lean_ctor_get(v_val_5167_, 1);
v_isSharedCheck_5366_ = !lean_is_exclusive(v_val_5167_);
if (v_isSharedCheck_5366_ == 0)
{
v___x_5171_ = v_val_5167_;
v_isShared_5172_ = v_isSharedCheck_5366_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_snd_5169_);
lean_inc(v_fst_5168_);
lean_dec(v_val_5167_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5366_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v_toConstantVal_5173_; lean_object* v_cidx_5174_; lean_object* v_numParams_5175_; lean_object* v_numFields_5176_; lean_object* v___y_5178_; lean_object* v___y_5179_; lean_object* v___y_5180_; lean_object* v___y_5181_; lean_object* v___y_5182_; lean_object* v___y_5183_; uint8_t v___y_5268_; lean_object* v_cidx_5296_; uint8_t v___x_5297_; 
v_toConstantVal_5173_ = lean_ctor_get(v_fst_5160_, 0);
lean_inc_ref(v_toConstantVal_5173_);
v_cidx_5174_ = lean_ctor_get(v_fst_5160_, 2);
lean_inc(v_cidx_5174_);
v_numParams_5175_ = lean_ctor_get(v_fst_5160_, 3);
lean_inc(v_numParams_5175_);
v_numFields_5176_ = lean_ctor_get(v_fst_5160_, 4);
lean_inc(v_numFields_5176_);
lean_dec(v_fst_5160_);
v_cidx_5296_ = lean_ctor_get(v_fst_5168_, 2);
lean_inc(v_cidx_5296_);
lean_dec(v_fst_5168_);
v___x_5297_ = lean_nat_dec_eq(v_cidx_5174_, v_cidx_5296_);
lean_dec(v_cidx_5296_);
lean_dec(v_cidx_5174_);
if (v___x_5297_ == 0)
{
if (v___x_5110_ == 0)
{
lean_dec_ref(v_val_5154_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
v___y_5268_ = v___x_5110_;
goto v___jp_5267_;
}
else
{
lean_object* v_toConstantVal_5298_; lean_object* v_name_5299_; lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; lean_object* v_a_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v_a_5306_; uint8_t v___x_5324_; 
lean_dec(v_numFields_5176_);
lean_dec(v_numParams_5175_);
lean_dec_ref(v_toConstantVal_5173_);
lean_del_object(v___x_5171_);
lean_dec(v_snd_5169_);
lean_del_object(v___x_5163_);
lean_dec(v_snd_5161_);
v_toConstantVal_5298_ = lean_ctor_get(v_val_5154_, 0);
lean_inc_ref(v_toConstantVal_5298_);
lean_dec_ref(v_val_5154_);
v_name_5299_ = lean_ctor_get(v_toConstantVal_5298_, 0);
lean_inc(v_name_5299_);
lean_dec_ref(v_toConstantVal_5298_);
v___x_5300_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__19));
v___x_5301_ = l_Lean_Name_str___override(v_name_5299_, v___x_5300_);
lean_inc(v___x_5301_);
v___x_5302_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5301_, v___x_5110_, v_a_5102_);
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref(v___x_5302_);
v___x_5304_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__21));
v___x_5305_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5304_, v___x_5110_, v_a_5102_);
v_a_5306_ = lean_ctor_get(v___x_5305_, 0);
lean_inc(v_a_5306_);
lean_dec_ref(v___x_5305_);
v___x_5324_ = lean_unbox(v_a_5303_);
lean_dec(v_a_5303_);
if (v___x_5324_ == 0)
{
lean_dec(v_a_5306_);
lean_dec(v_a_5156_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
goto v___jp_5307_;
}
else
{
uint8_t v___x_5325_; 
v___x_5325_ = lean_unbox(v_a_5306_);
lean_dec(v_a_5306_);
if (v___x_5325_ == 0)
{
lean_dec(v_a_5156_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
goto v___jp_5307_;
}
else
{
lean_object* v___x_5326_; lean_object* v_dummy_5327_; lean_object* v_nargs_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5326_ = l_Lean_mkConst(v___x_5301_, v_us_5148_);
v_dummy_5327_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5328_ = l_Lean_Expr_getAppNumArgs(v_a_5135_);
lean_inc(v_nargs_5328_);
v___x_5329_ = lean_mk_array(v_nargs_5328_, v_dummy_5327_);
v___x_5330_ = lean_unsigned_to_nat(1u);
v___x_5331_ = lean_nat_sub(v_nargs_5328_, v___x_5330_);
lean_dec(v_nargs_5328_);
lean_inc_n(v_a_5135_, 2);
v___x_5332_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5135_, v___x_5329_, v___x_5331_);
v___x_5333_ = l_Lean_mkAppN(v___x_5326_, v___x_5332_);
lean_dec_ref(v___x_5332_);
v___x_5334_ = l_Lean_Meta_getLevel(v_a_5135_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
if (lean_obj_tag(v___x_5334_) == 0)
{
lean_object* v_a_5335_; lean_object* v___x_5337_; uint8_t v_isShared_5338_; uint8_t v_isSharedCheck_5357_; 
v_a_5335_ = lean_ctor_get(v___x_5334_, 0);
v_isSharedCheck_5357_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5357_ == 0)
{
v___x_5337_ = v___x_5334_;
v_isShared_5338_ = v_isSharedCheck_5357_;
goto v_resetjp_5336_;
}
else
{
lean_inc(v_a_5335_);
lean_dec(v___x_5334_);
v___x_5337_ = lean_box(0);
v_isShared_5338_ = v_isSharedCheck_5357_;
goto v_resetjp_5336_;
}
v_resetjp_5336_:
{
lean_object* v___x_5339_; lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; lean_object* v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5355_; 
v___x_5339_ = ((lean_object*)(l_Lean_Meta_mkFalseElim___closed__2));
v___x_5340_ = lean_box(0);
v___x_5341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5341_, 0, v_a_5156_);
lean_ctor_set(v___x_5341_, 1, v___x_5340_);
v___x_5342_ = l_Lean_mkConst(v___x_5339_, v___x_5341_);
v___x_5343_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5343_, 0, v_a_5335_);
lean_ctor_set(v___x_5343_, 1, v___x_5340_);
v___x_5344_ = l_Lean_mkConst(v___x_5304_, v___x_5343_);
v___x_5345_ = lean_unsigned_to_nat(5u);
v___x_5346_ = lean_mk_empty_array_with_capacity(v___x_5345_);
v___x_5347_ = lean_array_push(v___x_5346_, v_a_5135_);
v___x_5348_ = lean_array_push(v___x_5347_, v___x_5333_);
v___x_5349_ = lean_array_push(v___x_5348_, v___x_5119_);
v___x_5350_ = lean_array_push(v___x_5349_, v___x_5120_);
v___x_5351_ = lean_array_push(v___x_5350_, v_h_5098_);
v___x_5352_ = l_Lean_mkAppN(v___x_5344_, v___x_5351_);
lean_dec_ref(v___x_5351_);
v___x_5353_ = l_Lean_mkAppB(v___x_5342_, v_target_5097_, v___x_5352_);
if (v_isShared_5338_ == 0)
{
lean_ctor_set(v___x_5337_, 0, v___x_5353_);
v___x_5355_ = v___x_5337_;
goto v_reusejp_5354_;
}
else
{
lean_object* v_reuseFailAlloc_5356_; 
v_reuseFailAlloc_5356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5356_, 0, v___x_5353_);
v___x_5355_ = v_reuseFailAlloc_5356_;
goto v_reusejp_5354_;
}
v_reusejp_5354_:
{
return v___x_5355_;
}
}
}
else
{
lean_object* v_a_5358_; lean_object* v___x_5360_; uint8_t v_isShared_5361_; uint8_t v_isSharedCheck_5365_; 
lean_dec_ref(v___x_5333_);
lean_dec(v_a_5156_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v_a_5358_ = lean_ctor_get(v___x_5334_, 0);
v_isSharedCheck_5365_ = !lean_is_exclusive(v___x_5334_);
if (v_isSharedCheck_5365_ == 0)
{
v___x_5360_ = v___x_5334_;
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
else
{
lean_inc(v_a_5358_);
lean_dec(v___x_5334_);
v___x_5360_ = lean_box(0);
v_isShared_5361_ = v_isSharedCheck_5365_;
goto v_resetjp_5359_;
}
v_resetjp_5359_:
{
lean_object* v___x_5363_; 
if (v_isShared_5361_ == 0)
{
v___x_5363_ = v___x_5360_;
goto v_reusejp_5362_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v_a_5358_);
v___x_5363_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5362_;
}
v_reusejp_5362_:
{
return v___x_5363_;
}
}
}
}
}
v___jp_5307_:
{
lean_object* v___x_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v___x_5311_; lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
v___x_5308_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5309_ = l_Lean_MessageData_ofName(v___x_5301_);
v___x_5310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5310_, 0, v___x_5308_);
lean_ctor_set(v___x_5310_, 1, v___x_5309_);
v___x_5311_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__23, &l_Lean_Meta_mkNoConfusion___closed__23_once, _init_l_Lean_Meta_mkNoConfusion___closed__23);
v___x_5312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5312_, 0, v___x_5310_);
lean_ctor_set(v___x_5312_, 1, v___x_5311_);
v___x_5313_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__24, &l_Lean_Meta_mkNoConfusion___closed__24_once, _init_l_Lean_Meta_mkNoConfusion___closed__24);
v___x_5314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5314_, 0, v___x_5312_);
lean_ctor_set(v___x_5314_, 1, v___x_5313_);
v___x_5315_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5314_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
v_a_5316_ = lean_ctor_get(v___x_5315_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5315_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5315_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5315_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
return v___x_5321_;
}
}
}
}
}
else
{
lean_dec_ref(v_val_5154_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
v___y_5268_ = v___x_5151_;
goto v___jp_5267_;
}
v___jp_5177_:
{
lean_object* v___x_5184_; 
lean_inc(v___y_5179_);
v___x_5184_ = l_Lean_getConstVal___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(v___y_5179_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
if (lean_obj_tag(v___x_5184_) == 0)
{
lean_object* v_a_5185_; lean_object* v_nargs_5186_; lean_object* v_type_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5256_; 
v_a_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc(v_a_5185_);
lean_dec_ref_known(v___x_5184_, 1);
v_nargs_5186_ = l_Lean_Expr_getAppNumArgs(v_a_5135_);
v_type_5187_ = lean_ctor_get(v_a_5185_, 2);
v_isSharedCheck_5256_ = !lean_is_exclusive(v_a_5185_);
if (v_isSharedCheck_5256_ == 0)
{
lean_object* v_unused_5257_; lean_object* v_unused_5258_; 
v_unused_5257_ = lean_ctor_get(v_a_5185_, 1);
lean_dec(v_unused_5257_);
v_unused_5258_ = lean_ctor_get(v_a_5185_, 0);
lean_dec(v_unused_5258_);
v___x_5189_ = v_a_5185_;
v_isShared_5190_ = v_isSharedCheck_5256_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_type_5187_);
lean_dec(v_a_5185_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5256_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v_dummy_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v___x_5196_; lean_object* v_start_5197_; lean_object* v_stop_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; lean_object* v___x_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; lean_object* v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; uint8_t v___x_5212_; 
v_dummy_5191_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
lean_inc(v_nargs_5186_);
v___x_5192_ = lean_mk_array(v_nargs_5186_, v_dummy_5191_);
v___x_5193_ = lean_unsigned_to_nat(1u);
v___x_5194_ = lean_nat_sub(v_nargs_5186_, v___x_5193_);
lean_dec(v_nargs_5186_);
v___x_5195_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5135_, v___x_5192_, v___x_5194_);
lean_inc_n(v_numParams_5175_, 2);
lean_inc(v___y_5178_);
v___x_5196_ = l_Array_toSubarray___redArg(v___x_5195_, v___y_5178_, v_numParams_5175_);
v_start_5197_ = lean_ctor_get(v___x_5196_, 1);
v_stop_5198_ = lean_ctor_get(v___x_5196_, 2);
v___x_5199_ = lean_array_get_size(v_snd_5161_);
v___x_5200_ = l_Array_toSubarray___redArg(v_snd_5161_, v_numParams_5175_, v___x_5199_);
v___x_5201_ = lean_array_get_size(v_snd_5169_);
v___x_5202_ = l_Subarray_copy___redArg(v___x_5200_);
v___x_5203_ = l_Array_toSubarray___redArg(v_snd_5169_, v_numParams_5175_, v___x_5201_);
v___x_5204_ = l_Subarray_copy___redArg(v___x_5203_);
v___x_5205_ = l_Lean_Expr_getNumHeadForalls(v_type_5187_);
lean_dec_ref(v_type_5187_);
v___x_5206_ = lean_nat_sub(v_stop_5198_, v_start_5197_);
v___x_5207_ = lean_array_get_size(v___x_5202_);
v___x_5208_ = lean_nat_add(v___x_5206_, v___x_5207_);
lean_dec(v___x_5206_);
v___x_5209_ = lean_array_get_size(v___x_5204_);
v___x_5210_ = lean_nat_add(v___x_5208_, v___x_5209_);
lean_dec(v___x_5208_);
v___x_5211_ = lean_nat_add(v___x_5210_, v___x_5109_);
lean_dec(v___x_5210_);
v___x_5212_ = lean_nat_dec_le(v___x_5211_, v___x_5205_);
if (v___x_5212_ == 0)
{
lean_object* v___x_5213_; lean_object* v___x_5214_; 
lean_dec(v___x_5211_);
lean_dec(v___x_5205_);
lean_dec_ref(v___x_5204_);
lean_dec_ref(v___x_5202_);
lean_dec_ref(v___x_5196_);
lean_del_object(v___x_5189_);
lean_dec(v___y_5179_);
lean_dec(v___y_5178_);
lean_del_object(v___x_5171_);
lean_dec(v_a_5156_);
lean_dec(v_us_5148_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v___x_5213_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__14, &l_Lean_Meta_mkNoConfusion___closed__14_once, _init_l_Lean_Meta_mkNoConfusion___closed__14);
v___x_5214_ = l_panic___at___00Lean_Meta_mkNoConfusion_spec__0(v___x_5213_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
return v___x_5214_;
}
else
{
lean_object* v___x_5216_; 
if (v_isShared_5172_ == 0)
{
lean_ctor_set_tag(v___x_5171_, 1);
lean_ctor_set(v___x_5171_, 1, v_us_5148_);
lean_ctor_set(v___x_5171_, 0, v_a_5156_);
v___x_5216_ = v___x_5171_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5255_; 
v_reuseFailAlloc_5255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5255_, 0, v_a_5156_);
lean_ctor_set(v_reuseFailAlloc_5255_, 1, v_us_5148_);
v___x_5216_ = v_reuseFailAlloc_5255_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; lean_object* v___x_5227_; 
v___x_5217_ = l_Lean_mkConst(v___y_5179_, v___x_5216_);
v___x_5218_ = l_Subarray_copy___redArg(v___x_5196_);
v___x_5219_ = l_Lean_mkAppN(v___x_5217_, v___x_5218_);
lean_dec_ref(v___x_5218_);
v___x_5220_ = lean_mk_empty_array_with_capacity(v___x_5193_);
v___x_5221_ = lean_array_push(v___x_5220_, v_target_5097_);
v___x_5222_ = l_Array_append___redArg(v___x_5221_, v___x_5202_);
lean_dec_ref(v___x_5202_);
v___x_5223_ = l_Array_append___redArg(v___x_5222_, v___x_5204_);
lean_dec_ref(v___x_5204_);
v___x_5224_ = l_Lean_mkAppN(v___x_5219_, v___x_5223_);
lean_dec_ref(v___x_5223_);
v___x_5225_ = lean_nat_sub(v___x_5205_, v___x_5211_);
lean_dec(v___x_5211_);
lean_dec(v___x_5205_);
lean_inc(v___y_5178_);
if (v_isShared_5190_ == 0)
{
lean_ctor_set(v___x_5189_, 2, v___x_5193_);
lean_ctor_set(v___x_5189_, 1, v___x_5225_);
lean_ctor_set(v___x_5189_, 0, v___y_5178_);
v___x_5227_ = v___x_5189_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5254_; 
v_reuseFailAlloc_5254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5254_, 0, v___y_5178_);
lean_ctor_set(v_reuseFailAlloc_5254_, 1, v___x_5225_);
lean_ctor_set(v_reuseFailAlloc_5254_, 2, v___x_5193_);
v___x_5227_ = v_reuseFailAlloc_5254_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
lean_object* v___x_5228_; 
v___x_5228_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v___x_5227_, v___x_5224_, v___y_5178_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
lean_dec_ref(v___x_5227_);
if (lean_obj_tag(v___x_5228_) == 0)
{
lean_object* v_a_5229_; lean_object* v___x_5230_; 
v_a_5229_ = lean_ctor_get(v___x_5228_, 0);
lean_inc_n(v_a_5229_, 2);
lean_dec_ref_known(v___x_5228_, 1);
lean_inc(v___y_5183_);
lean_inc_ref(v___y_5182_);
lean_inc(v___y_5181_);
lean_inc_ref(v___y_5180_);
v___x_5230_ = lean_infer_type(v_a_5229_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; lean_object* v___x_5232_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref_known(v___x_5230_, 1);
v___x_5232_ = l_Lean_Meta_whnfForall(v_a_5231_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
if (lean_obj_tag(v___x_5232_) == 0)
{
lean_object* v_a_5233_; lean_object* v___x_5235_; uint8_t v_isShared_5236_; uint8_t v_isSharedCheck_5253_; 
v_a_5233_ = lean_ctor_get(v___x_5232_, 0);
v_isSharedCheck_5253_ = !lean_is_exclusive(v___x_5232_);
if (v_isSharedCheck_5253_ == 0)
{
v___x_5235_ = v___x_5232_;
v_isShared_5236_ = v_isSharedCheck_5253_;
goto v_resetjp_5234_;
}
else
{
lean_inc(v_a_5233_);
lean_dec(v___x_5232_);
v___x_5235_ = lean_box(0);
v_isShared_5236_ = v_isSharedCheck_5253_;
goto v_resetjp_5234_;
}
v_resetjp_5234_:
{
lean_object* v___x_5237_; uint8_t v___x_5238_; 
v___x_5237_ = l_Lean_Expr_bindingDomain_x21(v_a_5233_);
lean_dec(v_a_5233_);
v___x_5238_ = l_Lean_Expr_isHEq(v___x_5237_);
lean_dec_ref(v___x_5237_);
if (v___x_5238_ == 0)
{
lean_object* v___x_5239_; lean_object* v___x_5241_; 
v___x_5239_ = l_Lean_Expr_app___override(v_a_5229_, v_h_5098_);
if (v_isShared_5236_ == 0)
{
lean_ctor_set(v___x_5235_, 0, v___x_5239_);
v___x_5241_ = v___x_5235_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v___x_5239_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
else
{
lean_object* v___x_5243_; 
lean_del_object(v___x_5235_);
v___x_5243_ = l_Lean_Meta_mkHEqOfEq(v_h_5098_, v___y_5180_, v___y_5181_, v___y_5182_, v___y_5183_);
if (lean_obj_tag(v___x_5243_) == 0)
{
lean_object* v_a_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5252_; 
v_a_5244_ = lean_ctor_get(v___x_5243_, 0);
v_isSharedCheck_5252_ = !lean_is_exclusive(v___x_5243_);
if (v_isSharedCheck_5252_ == 0)
{
v___x_5246_ = v___x_5243_;
v_isShared_5247_ = v_isSharedCheck_5252_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_a_5244_);
lean_dec(v___x_5243_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5252_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
lean_object* v___x_5248_; lean_object* v___x_5250_; 
v___x_5248_ = l_Lean_Expr_app___override(v_a_5229_, v_a_5244_);
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 0, v___x_5248_);
v___x_5250_ = v___x_5246_;
goto v_reusejp_5249_;
}
else
{
lean_object* v_reuseFailAlloc_5251_; 
v_reuseFailAlloc_5251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5251_, 0, v___x_5248_);
v___x_5250_ = v_reuseFailAlloc_5251_;
goto v_reusejp_5249_;
}
v_reusejp_5249_:
{
return v___x_5250_;
}
}
}
else
{
lean_dec(v_a_5229_);
return v___x_5243_;
}
}
}
}
else
{
lean_dec(v_a_5229_);
lean_dec_ref(v_h_5098_);
return v___x_5232_;
}
}
else
{
lean_dec(v_a_5229_);
lean_dec_ref(v_h_5098_);
return v___x_5230_;
}
}
else
{
lean_dec_ref(v_h_5098_);
return v___x_5228_;
}
}
}
}
}
}
else
{
lean_object* v_a_5259_; lean_object* v___x_5261_; uint8_t v_isShared_5262_; uint8_t v_isSharedCheck_5266_; 
lean_dec(v___y_5179_);
lean_dec(v___y_5178_);
lean_dec(v_numParams_5175_);
lean_del_object(v___x_5171_);
lean_dec(v_snd_5169_);
lean_dec(v_snd_5161_);
lean_dec(v_a_5156_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v_a_5259_ = lean_ctor_get(v___x_5184_, 0);
v_isSharedCheck_5266_ = !lean_is_exclusive(v___x_5184_);
if (v_isSharedCheck_5266_ == 0)
{
v___x_5261_ = v___x_5184_;
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
else
{
lean_inc(v_a_5259_);
lean_dec(v___x_5184_);
v___x_5261_ = lean_box(0);
v_isShared_5262_ = v_isSharedCheck_5266_;
goto v_resetjp_5260_;
}
v_resetjp_5260_:
{
lean_object* v___x_5264_; 
if (v_isShared_5262_ == 0)
{
v___x_5264_ = v___x_5261_;
goto v_reusejp_5263_;
}
else
{
lean_object* v_reuseFailAlloc_5265_; 
v_reuseFailAlloc_5265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5265_, 0, v_a_5259_);
v___x_5264_ = v_reuseFailAlloc_5265_;
goto v_reusejp_5263_;
}
v_reusejp_5263_:
{
return v___x_5264_;
}
}
}
}
v___jp_5267_:
{
lean_object* v___x_5269_; uint8_t v___x_5270_; 
v___x_5269_ = lean_unsigned_to_nat(0u);
v___x_5270_ = lean_nat_dec_eq(v_numFields_5176_, v___x_5269_);
lean_dec(v_numFields_5176_);
if (v___x_5270_ == 0)
{
lean_object* v_name_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v_a_5275_; uint8_t v___x_5276_; 
v_name_5271_ = lean_ctor_get(v_toConstantVal_5173_, 0);
lean_inc(v_name_5271_);
lean_dec_ref(v_toConstantVal_5173_);
v___x_5272_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__0));
v___x_5273_ = l_Lean_Name_str___override(v_name_5271_, v___x_5272_);
lean_inc(v___x_5273_);
v___x_5274_ = l_Lean_hasConst___at___00Lean_Meta_mkNoConfusion_spec__2___redArg(v___x_5273_, v___x_5110_, v_a_5102_);
v_a_5275_ = lean_ctor_get(v___x_5274_, 0);
lean_inc(v_a_5275_);
lean_dec_ref(v___x_5274_);
v___x_5276_ = lean_unbox(v_a_5275_);
lean_dec(v_a_5275_);
if (v___x_5276_ == 0)
{
lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5280_; 
lean_dec(v_numParams_5175_);
lean_del_object(v___x_5171_);
lean_dec(v_snd_5169_);
lean_dec(v_snd_5161_);
lean_dec(v_a_5156_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v___x_5277_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__16, &l_Lean_Meta_mkNoConfusion___closed__16_once, _init_l_Lean_Meta_mkNoConfusion___closed__16);
v___x_5278_ = l_Lean_MessageData_ofName(v___x_5273_);
if (v_isShared_5164_ == 0)
{
lean_ctor_set_tag(v___x_5163_, 7);
lean_ctor_set(v___x_5163_, 1, v___x_5278_);
lean_ctor_set(v___x_5163_, 0, v___x_5277_);
v___x_5280_ = v___x_5163_;
goto v_reusejp_5279_;
}
else
{
lean_object* v_reuseFailAlloc_5290_; 
v_reuseFailAlloc_5290_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5290_, 0, v___x_5277_);
lean_ctor_set(v_reuseFailAlloc_5290_, 1, v___x_5278_);
v___x_5280_ = v_reuseFailAlloc_5290_;
goto v_reusejp_5279_;
}
v_reusejp_5279_:
{
lean_object* v___x_5281_; lean_object* v_a_5282_; lean_object* v___x_5284_; uint8_t v_isShared_5285_; uint8_t v_isSharedCheck_5289_; 
v___x_5281_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5280_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
v_isSharedCheck_5289_ = !lean_is_exclusive(v___x_5281_);
if (v_isSharedCheck_5289_ == 0)
{
v___x_5284_ = v___x_5281_;
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
else
{
lean_inc(v_a_5282_);
lean_dec(v___x_5281_);
v___x_5284_ = lean_box(0);
v_isShared_5285_ = v_isSharedCheck_5289_;
goto v_resetjp_5283_;
}
v_resetjp_5283_:
{
lean_object* v___x_5287_; 
if (v_isShared_5285_ == 0)
{
v___x_5287_ = v___x_5284_;
goto v_reusejp_5286_;
}
else
{
lean_object* v_reuseFailAlloc_5288_; 
v_reuseFailAlloc_5288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5288_, 0, v_a_5282_);
v___x_5287_ = v_reuseFailAlloc_5288_;
goto v_reusejp_5286_;
}
v_reusejp_5286_:
{
return v___x_5287_;
}
}
}
}
else
{
lean_del_object(v___x_5163_);
v___y_5178_ = v___x_5269_;
v___y_5179_ = v___x_5273_;
v___y_5180_ = v_a_5099_;
v___y_5181_ = v_a_5100_;
v___y_5182_ = v_a_5101_;
v___y_5183_ = v_a_5102_;
goto v___jp_5177_;
}
}
else
{
lean_object* v___x_5291_; lean_object* v___x_5292_; lean_object* v___f_5293_; lean_object* v___x_5294_; lean_object* v___x_5295_; 
lean_dec(v_numParams_5175_);
lean_dec_ref(v_toConstantVal_5173_);
lean_del_object(v___x_5171_);
lean_dec(v_snd_5169_);
lean_del_object(v___x_5163_);
lean_dec(v_snd_5161_);
lean_dec(v_a_5156_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v_h_5098_);
v___x_5291_ = lean_box(v___y_5268_);
v___x_5292_ = lean_box(v___x_5270_);
v___f_5293_ = lean_alloc_closure((void*)(l_Lean_Meta_mkNoConfusion___lam__0___boxed), 8, 2);
lean_closure_set(v___f_5293_, 0, v___x_5291_);
lean_closure_set(v___f_5293_, 1, v___x_5292_);
v___x_5294_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__18));
v___x_5295_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v___x_5294_, v_target_5097_, v___f_5293_, v_a_5099_, v_a_5100_, v_a_5101_, v_a_5102_);
return v___x_5295_;
}
}
}
}
else
{
lean_dec(v_a_5166_);
lean_del_object(v___x_5163_);
lean_dec(v_snd_5161_);
lean_dec(v_fst_5160_);
lean_dec(v_a_5156_);
lean_dec_ref(v_val_5154_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v___y_5122_ = v_a_5099_;
v___y_5123_ = v_a_5100_;
v___y_5124_ = v_a_5101_;
v___y_5125_ = v_a_5102_;
goto v___jp_5121_;
}
}
else
{
lean_object* v_a_5367_; lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5374_; 
lean_del_object(v___x_5163_);
lean_dec(v_snd_5161_);
lean_dec(v_fst_5160_);
lean_dec(v_a_5156_);
lean_dec_ref(v_val_5154_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v_a_5367_ = lean_ctor_get(v___x_5165_, 0);
v_isSharedCheck_5374_ = !lean_is_exclusive(v___x_5165_);
if (v_isSharedCheck_5374_ == 0)
{
v___x_5369_ = v___x_5165_;
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
else
{
lean_inc(v_a_5367_);
lean_dec(v___x_5165_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5374_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5372_; 
if (v_isShared_5370_ == 0)
{
v___x_5372_ = v___x_5369_;
goto v_reusejp_5371_;
}
else
{
lean_object* v_reuseFailAlloc_5373_; 
v_reuseFailAlloc_5373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5373_, 0, v_a_5367_);
v___x_5372_ = v_reuseFailAlloc_5373_;
goto v_reusejp_5371_;
}
v_reusejp_5371_:
{
return v___x_5372_;
}
}
}
}
}
else
{
lean_dec(v_a_5158_);
lean_dec(v_a_5156_);
lean_dec_ref(v_val_5154_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v___y_5122_ = v_a_5099_;
v___y_5123_ = v_a_5100_;
v___y_5124_ = v_a_5101_;
v___y_5125_ = v_a_5102_;
goto v___jp_5121_;
}
}
else
{
lean_object* v_a_5376_; lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
lean_dec(v_a_5156_);
lean_dec_ref(v_val_5154_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v_a_5376_ = lean_ctor_get(v___x_5157_, 0);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5157_);
if (v_isSharedCheck_5383_ == 0)
{
v___x_5378_ = v___x_5157_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_inc(v_a_5376_);
lean_dec(v___x_5157_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_a_5376_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
else
{
lean_object* v_a_5384_; lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5391_; 
lean_dec_ref(v_val_5154_);
lean_dec(v_us_5148_);
lean_dec(v_a_5135_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v_a_5384_ = lean_ctor_get(v___x_5155_, 0);
v_isSharedCheck_5391_ = !lean_is_exclusive(v___x_5155_);
if (v_isSharedCheck_5391_ == 0)
{
v___x_5386_ = v___x_5155_;
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
else
{
lean_inc(v_a_5384_);
lean_dec(v___x_5155_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5391_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5389_; 
if (v_isShared_5387_ == 0)
{
v___x_5389_ = v___x_5386_;
goto v_reusejp_5388_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_a_5384_);
v___x_5389_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5388_;
}
v_reusejp_5388_:
{
return v___x_5389_;
}
}
}
}
else
{
lean_dec(v_val_5153_);
lean_dec(v_us_5148_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v___y_5137_ = v_a_5099_;
v___y_5138_ = v_a_5100_;
v___y_5139_ = v_a_5101_;
v___y_5140_ = v_a_5102_;
goto v___jp_5136_;
}
}
}
else
{
lean_dec_ref(v___x_5146_);
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
v___y_5137_ = v_a_5099_;
v___y_5138_ = v_a_5100_;
v___y_5139_ = v_a_5101_;
v___y_5140_ = v_a_5102_;
goto v___jp_5136_;
}
v___jp_5136_:
{
lean_object* v___x_5141_; lean_object* v___x_5142_; lean_object* v___x_5143_; lean_object* v___x_5144_; lean_object* v___x_5145_; 
v___x_5141_ = ((lean_object*)(l_Lean_Meta_mkNoConfusion___closed__1));
v___x_5142_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__11, &l_Lean_Meta_mkNoConfusion___closed__11_once, _init_l_Lean_Meta_mkNoConfusion___closed__11);
v___x_5143_ = l_Lean_indentExpr(v_a_5135_);
v___x_5144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5144_, 0, v___x_5142_);
lean_ctor_set(v___x_5144_, 1, v___x_5143_);
v___x_5145_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5141_, v___x_5144_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_);
return v___x_5145_;
}
}
else
{
lean_dec_ref(v___x_5120_);
lean_dec_ref(v___x_5119_);
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
return v___x_5134_;
}
v___jp_5121_:
{
lean_object* v___x_5126_; lean_object* v___x_5127_; lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; lean_object* v___x_5131_; lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5126_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__6, &l_Lean_Meta_mkNoConfusion___closed__6_once, _init_l_Lean_Meta_mkNoConfusion___closed__6);
v___x_5127_ = l_Lean_MessageData_ofExpr(v___x_5119_);
v___x_5128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5128_, 0, v___x_5126_);
lean_ctor_set(v___x_5128_, 1, v___x_5127_);
v___x_5129_ = lean_obj_once(&l_Lean_Meta_mkNoConfusion___closed__8, &l_Lean_Meta_mkNoConfusion___closed__8_once, _init_l_Lean_Meta_mkNoConfusion___closed__8);
v___x_5130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5128_);
lean_ctor_set(v___x_5130_, 1, v___x_5129_);
v___x_5131_ = l_Lean_MessageData_ofExpr(v___x_5120_);
v___x_5132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5132_, 0, v___x_5130_);
lean_ctor_set(v___x_5132_, 1, v___x_5131_);
v___x_5133_ = l_Lean_throwError___at___00__private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException_spec__0___redArg(v___x_5132_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_);
return v___x_5133_;
}
}
}
else
{
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
return v___x_5106_;
}
}
else
{
lean_dec_ref(v_h_5098_);
lean_dec_ref(v_target_5097_);
return v___x_5104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNoConfusion___boxed(lean_object* v_target_5392_, lean_object* v_h_5393_, lean_object* v_a_5394_, lean_object* v_a_5395_, lean_object* v_a_5396_, lean_object* v_a_5397_, lean_object* v_a_5398_){
_start:
{
lean_object* v_res_5399_; 
v_res_5399_ = l_Lean_Meta_mkNoConfusion(v_target_5392_, v_h_5393_, v_a_5394_, v_a_5395_, v_a_5396_, v_a_5397_);
lean_dec(v_a_5397_);
lean_dec_ref(v_a_5396_);
lean_dec(v_a_5395_);
lean_dec_ref(v_a_5394_);
return v_res_5399_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(lean_object* v_range_5400_, lean_object* v_b_5401_, lean_object* v_i_5402_, lean_object* v_hs_5403_, lean_object* v_hl_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_){
_start:
{
lean_object* v___x_5410_; 
v___x_5410_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___redArg(v_range_5400_, v_b_5401_, v_i_5402_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_);
return v___x_5410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1___boxed(lean_object* v_range_5411_, lean_object* v_b_5412_, lean_object* v_i_5413_, lean_object* v_hs_5414_, lean_object* v_hl_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_mkNoConfusion_spec__1(v_range_5411_, v_b_5412_, v_i_5413_, v_hs_5414_, v_hl_5415_, v___y_5416_, v___y_5417_, v___y_5418_, v___y_5419_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec(v___y_5417_);
lean_dec_ref(v___y_5416_);
lean_dec_ref(v_range_5411_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(lean_object* v_00_u03b1_5422_, lean_object* v_name_5423_, uint8_t v_bi_5424_, lean_object* v_type_5425_, lean_object* v_k_5426_, uint8_t v_kind_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___x_5433_; 
v___x_5433_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___redArg(v_name_5423_, v_bi_5424_, v_type_5425_, v_k_5426_, v_kind_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3___boxed(lean_object* v_00_u03b1_5434_, lean_object* v_name_5435_, lean_object* v_bi_5436_, lean_object* v_type_5437_, lean_object* v_k_5438_, lean_object* v_kind_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_){
_start:
{
uint8_t v_bi_boxed_5445_; uint8_t v_kind_boxed_5446_; lean_object* v_res_5447_; 
v_bi_boxed_5445_ = lean_unbox(v_bi_5436_);
v_kind_boxed_5446_ = lean_unbox(v_kind_5439_);
v_res_5447_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3_spec__3(v_00_u03b1_5434_, v_name_5435_, v_bi_boxed_5445_, v_type_5437_, v_k_5438_, v_kind_boxed_5446_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
return v_res_5447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(lean_object* v_00_u03b1_5448_, lean_object* v_name_5449_, lean_object* v_type_5450_, lean_object* v_k_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_){
_start:
{
lean_object* v___x_5457_; 
v___x_5457_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___redArg(v_name_5449_, v_type_5450_, v_k_5451_, v___y_5452_, v___y_5453_, v___y_5454_, v___y_5455_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3___boxed(lean_object* v_00_u03b1_5458_, lean_object* v_name_5459_, lean_object* v_type_5460_, lean_object* v_k_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_, lean_object* v___y_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_){
_start:
{
lean_object* v_res_5467_; 
v_res_5467_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_mkNoConfusion_spec__3(v_00_u03b1_5458_, v_name_5459_, v_type_5460_, v_k_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_);
lean_dec(v___y_5465_);
lean_dec_ref(v___y_5464_);
lean_dec(v___y_5463_);
lean_dec_ref(v___y_5462_);
return v_res_5467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure(lean_object* v_monad_5473_, lean_object* v_e_5474_, lean_object* v_a_5475_, lean_object* v_a_5476_, lean_object* v_a_5477_, lean_object* v_a_5478_){
_start:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___x_5483_; lean_object* v___x_5484_; lean_object* v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5480_ = ((lean_object*)(l_Lean_Meta_mkPure___closed__2));
v___x_5481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5481_, 0, v_monad_5473_);
v___x_5482_ = lean_box(0);
v___x_5483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5483_, 0, v_e_5474_);
v___x_5484_ = lean_unsigned_to_nat(4u);
v___x_5485_ = lean_mk_empty_array_with_capacity(v___x_5484_);
v___x_5486_ = lean_array_push(v___x_5485_, v___x_5481_);
v___x_5487_ = lean_array_push(v___x_5486_, v___x_5482_);
v___x_5488_ = lean_array_push(v___x_5487_, v___x_5482_);
v___x_5489_ = lean_array_push(v___x_5488_, v___x_5483_);
v___x_5490_ = l_Lean_Meta_mkAppOptM(v___x_5480_, v___x_5489_, v_a_5475_, v_a_5476_, v_a_5477_, v_a_5478_);
return v___x_5490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPure___boxed(lean_object* v_monad_5491_, lean_object* v_e_5492_, lean_object* v_a_5493_, lean_object* v_a_5494_, lean_object* v_a_5495_, lean_object* v_a_5496_, lean_object* v_a_5497_){
_start:
{
lean_object* v_res_5498_; 
v_res_5498_ = l_Lean_Meta_mkPure(v_monad_5491_, v_e_5492_, v_a_5493_, v_a_5494_, v_a_5495_, v_a_5496_);
lean_dec(v_a_5496_);
lean_dec_ref(v_a_5495_);
lean_dec(v_a_5494_);
lean_dec_ref(v_a_5493_);
return v_res_5498_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__4(void){
_start:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5508_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__3));
v___x_5509_ = l_Lean_MessageData_ofFormat(v___x_5508_);
return v___x_5509_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__7(void){
_start:
{
lean_object* v___x_5513_; lean_object* v___x_5514_; 
v___x_5513_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__6));
v___x_5514_ = l_Lean_MessageData_ofFormat(v___x_5513_);
return v___x_5514_;
}
}
static lean_object* _init_l_Lean_Meta_mkProjection___closed__10(void){
_start:
{
lean_object* v___x_5518_; lean_object* v___x_5519_; 
v___x_5518_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__9));
v___x_5519_ = l_Lean_MessageData_ofFormat(v___x_5518_);
return v___x_5519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection(lean_object* v_s_5520_, lean_object* v_fieldName_5521_, lean_object* v_a_5522_, lean_object* v_a_5523_, lean_object* v_a_5524_, lean_object* v_a_5525_){
_start:
{
lean_object* v___x_5527_; 
lean_inc(v_a_5525_);
lean_inc_ref(v_a_5524_);
lean_inc(v_a_5523_);
lean_inc_ref(v_a_5522_);
lean_inc_ref(v_s_5520_);
v___x_5527_ = lean_infer_type(v_s_5520_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5624_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5624_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5624_ == 0)
{
v___x_5530_ = v___x_5527_;
v_isShared_5531_ = v_isSharedCheck_5624_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v___x_5527_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5624_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5532_; 
lean_inc(v_a_5525_);
lean_inc_ref(v_a_5524_);
lean_inc(v_a_5523_);
lean_inc_ref(v_a_5522_);
v___x_5532_ = lean_whnf(v_a_5528_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_);
if (lean_obj_tag(v___x_5532_) == 0)
{
lean_object* v_a_5533_; lean_object* v___x_5535_; uint8_t v_isShared_5536_; uint8_t v_isSharedCheck_5623_; 
v_a_5533_ = lean_ctor_get(v___x_5532_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v___x_5532_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5535_ = v___x_5532_;
v_isShared_5536_ = v_isSharedCheck_5623_;
goto v_resetjp_5534_;
}
else
{
lean_inc(v_a_5533_);
lean_dec(v___x_5532_);
v___x_5535_ = lean_box(0);
v_isShared_5536_ = v_isSharedCheck_5623_;
goto v_resetjp_5534_;
}
v_resetjp_5534_:
{
lean_object* v___y_5538_; lean_object* v___y_5539_; lean_object* v___y_5540_; lean_object* v___y_5541_; lean_object* v___x_5556_; 
v___x_5556_ = l_Lean_Expr_getAppFn(v_a_5533_);
if (lean_obj_tag(v___x_5556_) == 4)
{
lean_object* v_declName_5557_; lean_object* v_us_5558_; lean_object* v___x_5559_; lean_object* v_env_5560_; lean_object* v___y_5562_; lean_object* v___y_5563_; lean_object* v___y_5564_; lean_object* v___y_5565_; uint8_t v___x_5604_; 
v_declName_5557_ = lean_ctor_get(v___x_5556_, 0);
lean_inc_n(v_declName_5557_, 2);
v_us_5558_ = lean_ctor_get(v___x_5556_, 1);
lean_inc(v_us_5558_);
lean_dec_ref_known(v___x_5556_, 2);
v___x_5559_ = lean_st_ref_get(v_a_5525_);
v_env_5560_ = lean_ctor_get(v___x_5559_, 0);
lean_inc_ref_n(v_env_5560_, 2);
lean_dec(v___x_5559_);
v___x_5604_ = l_Lean_isStructure(v_env_5560_, v_declName_5557_);
if (v___x_5604_ == 0)
{
lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___x_5609_; 
v___x_5605_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5606_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
lean_inc(v_a_5533_);
lean_inc_ref(v_s_5520_);
v___x_5607_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5520_, v_a_5533_);
v___x_5608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5608_, 0, v___x_5606_);
lean_ctor_set(v___x_5608_, 1, v___x_5607_);
v___x_5609_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5605_, v___x_5608_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_);
if (lean_obj_tag(v___x_5609_) == 0)
{
lean_dec_ref_known(v___x_5609_, 1);
v___y_5562_ = v_a_5522_;
v___y_5563_ = v_a_5523_;
v___y_5564_ = v_a_5524_;
v___y_5565_ = v_a_5525_;
goto v___jp_5561_;
}
else
{
lean_object* v_a_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5617_; 
lean_dec_ref(v_env_5560_);
lean_dec(v_us_5558_);
lean_dec(v_declName_5557_);
lean_del_object(v___x_5535_);
lean_dec(v_a_5533_);
lean_del_object(v___x_5530_);
lean_dec(v_fieldName_5521_);
lean_dec_ref(v_s_5520_);
v_a_5610_ = lean_ctor_get(v___x_5609_, 0);
v_isSharedCheck_5617_ = !lean_is_exclusive(v___x_5609_);
if (v_isSharedCheck_5617_ == 0)
{
v___x_5612_ = v___x_5609_;
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_a_5610_);
lean_dec(v___x_5609_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5617_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5615_; 
if (v_isShared_5613_ == 0)
{
v___x_5615_ = v___x_5612_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5616_; 
v_reuseFailAlloc_5616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5616_, 0, v_a_5610_);
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
else
{
v___y_5562_ = v_a_5522_;
v___y_5563_ = v_a_5523_;
v___y_5564_ = v_a_5524_;
v___y_5565_ = v_a_5525_;
goto v___jp_5561_;
}
v___jp_5561_:
{
lean_object* v___x_5566_; 
lean_inc(v_fieldName_5521_);
lean_inc(v_declName_5557_);
lean_inc_ref(v_env_5560_);
v___x_5566_ = l_Lean_getProjFnForField_x3f(v_env_5560_, v_declName_5557_, v_fieldName_5521_);
if (lean_obj_tag(v___x_5566_) == 0)
{
lean_object* v___x_5567_; lean_object* v___x_5568_; size_t v_sz_5569_; size_t v___x_5570_; lean_object* v___x_5571_; 
lean_dec(v_us_5558_);
lean_del_object(v___x_5535_);
lean_inc(v_declName_5557_);
lean_inc_ref(v_env_5560_);
v___x_5567_ = l_Lean_getStructureFields(v_env_5560_, v_declName_5557_);
v___x_5568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_sz_5569_ = lean_array_size(v___x_5567_);
v___x_5570_ = ((size_t)0ULL);
lean_inc(v_fieldName_5521_);
lean_inc_ref(v_s_5520_);
v___x_5571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v_env_5560_, v_declName_5557_, v_s_5520_, v_fieldName_5521_, v___x_5567_, v_sz_5569_, v___x_5570_, v___x_5568_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
lean_dec_ref(v___x_5567_);
if (lean_obj_tag(v___x_5571_) == 0)
{
lean_object* v_a_5572_; lean_object* v___x_5574_; uint8_t v_isShared_5575_; uint8_t v_isSharedCheck_5582_; 
v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5582_ == 0)
{
v___x_5574_ = v___x_5571_;
v_isShared_5575_ = v_isSharedCheck_5582_;
goto v_resetjp_5573_;
}
else
{
lean_inc(v_a_5572_);
lean_dec(v___x_5571_);
v___x_5574_ = lean_box(0);
v_isShared_5575_ = v_isSharedCheck_5582_;
goto v_resetjp_5573_;
}
v_resetjp_5573_:
{
lean_object* v_fst_5576_; 
v_fst_5576_ = lean_ctor_get(v_a_5572_, 0);
lean_inc(v_fst_5576_);
lean_dec(v_a_5572_);
if (lean_obj_tag(v_fst_5576_) == 0)
{
lean_del_object(v___x_5574_);
v___y_5538_ = v___y_5563_;
v___y_5539_ = v___y_5564_;
v___y_5540_ = v___y_5565_;
v___y_5541_ = v___y_5562_;
goto v___jp_5537_;
}
else
{
lean_object* v_val_5577_; 
v_val_5577_ = lean_ctor_get(v_fst_5576_, 0);
lean_inc(v_val_5577_);
lean_dec_ref_known(v_fst_5576_, 1);
if (lean_obj_tag(v_val_5577_) == 0)
{
lean_del_object(v___x_5574_);
v___y_5538_ = v___y_5563_;
v___y_5539_ = v___y_5564_;
v___y_5540_ = v___y_5565_;
v___y_5541_ = v___y_5562_;
goto v___jp_5537_;
}
else
{
lean_object* v_val_5578_; lean_object* v___x_5580_; 
lean_dec(v_a_5533_);
lean_del_object(v___x_5530_);
lean_dec(v_fieldName_5521_);
lean_dec_ref(v_s_5520_);
v_val_5578_ = lean_ctor_get(v_val_5577_, 0);
lean_inc(v_val_5578_);
lean_dec_ref_known(v_val_5577_, 1);
if (v_isShared_5575_ == 0)
{
lean_ctor_set(v___x_5574_, 0, v_val_5578_);
v___x_5580_ = v___x_5574_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_val_5578_);
v___x_5580_ = v_reuseFailAlloc_5581_;
goto v_reusejp_5579_;
}
v_reusejp_5579_:
{
return v___x_5580_;
}
}
}
}
}
else
{
lean_object* v_a_5583_; lean_object* v___x_5585_; uint8_t v_isShared_5586_; uint8_t v_isSharedCheck_5590_; 
lean_dec(v_a_5533_);
lean_del_object(v___x_5530_);
lean_dec(v_fieldName_5521_);
lean_dec_ref(v_s_5520_);
v_a_5583_ = lean_ctor_get(v___x_5571_, 0);
v_isSharedCheck_5590_ = !lean_is_exclusive(v___x_5571_);
if (v_isSharedCheck_5590_ == 0)
{
v___x_5585_ = v___x_5571_;
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
else
{
lean_inc(v_a_5583_);
lean_dec(v___x_5571_);
v___x_5585_ = lean_box(0);
v_isShared_5586_ = v_isSharedCheck_5590_;
goto v_resetjp_5584_;
}
v_resetjp_5584_:
{
lean_object* v___x_5588_; 
if (v_isShared_5586_ == 0)
{
v___x_5588_ = v___x_5585_;
goto v_reusejp_5587_;
}
else
{
lean_object* v_reuseFailAlloc_5589_; 
v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
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
lean_object* v_val_5591_; lean_object* v_dummy_5592_; lean_object* v_nargs_5593_; lean_object* v___x_5594_; lean_object* v___x_5595_; lean_object* v___x_5596_; lean_object* v___x_5597_; lean_object* v___x_5598_; lean_object* v___x_5599_; lean_object* v___x_5600_; lean_object* v___x_5602_; 
lean_dec_ref(v_env_5560_);
lean_dec(v_declName_5557_);
lean_del_object(v___x_5530_);
lean_dec(v_fieldName_5521_);
v_val_5591_ = lean_ctor_get(v___x_5566_, 0);
lean_inc(v_val_5591_);
lean_dec_ref_known(v___x_5566_, 1);
v_dummy_5592_ = lean_obj_once(&l_Lean_Meta_congrArg_x3f___closed__2, &l_Lean_Meta_congrArg_x3f___closed__2_once, _init_l_Lean_Meta_congrArg_x3f___closed__2);
v_nargs_5593_ = l_Lean_Expr_getAppNumArgs(v_a_5533_);
lean_inc(v_nargs_5593_);
v___x_5594_ = lean_mk_array(v_nargs_5593_, v_dummy_5592_);
v___x_5595_ = lean_unsigned_to_nat(1u);
v___x_5596_ = lean_nat_sub(v_nargs_5593_, v___x_5595_);
lean_dec(v_nargs_5593_);
v___x_5597_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5533_, v___x_5594_, v___x_5596_);
v___x_5598_ = l_Lean_mkConst(v_val_5591_, v_us_5558_);
v___x_5599_ = l_Lean_mkAppN(v___x_5598_, v___x_5597_);
lean_dec_ref(v___x_5597_);
v___x_5600_ = l_Lean_Expr_app___override(v___x_5599_, v_s_5520_);
if (v_isShared_5536_ == 0)
{
lean_ctor_set(v___x_5535_, 0, v___x_5600_);
v___x_5602_ = v___x_5535_;
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
lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5621_; lean_object* v___x_5622_; 
lean_dec_ref(v___x_5556_);
lean_del_object(v___x_5535_);
lean_del_object(v___x_5530_);
lean_dec(v_fieldName_5521_);
v___x_5618_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5619_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__10, &l_Lean_Meta_mkProjection___closed__10_once, _init_l_Lean_Meta_mkProjection___closed__10);
v___x_5620_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5520_, v_a_5533_);
v___x_5621_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5621_, 0, v___x_5619_);
lean_ctor_set(v___x_5621_, 1, v___x_5620_);
v___x_5622_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5618_, v___x_5621_, v_a_5522_, v_a_5523_, v_a_5524_, v_a_5525_);
return v___x_5622_;
}
v___jp_5537_:
{
lean_object* v___x_5542_; lean_object* v___x_5543_; uint8_t v___x_5544_; lean_object* v___x_5545_; lean_object* v___x_5547_; 
v___x_5542_ = ((lean_object*)(l_Lean_Meta_mkProjection___closed__1));
v___x_5543_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__4, &l_Lean_Meta_mkProjection___closed__4_once, _init_l_Lean_Meta_mkProjection___closed__4);
v___x_5544_ = 1;
v___x_5545_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_fieldName_5521_, v___x_5544_);
if (v_isShared_5531_ == 0)
{
lean_ctor_set_tag(v___x_5530_, 3);
lean_ctor_set(v___x_5530_, 0, v___x_5545_);
v___x_5547_ = v___x_5530_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5555_; 
v_reuseFailAlloc_5555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5555_, 0, v___x_5545_);
v___x_5547_ = v_reuseFailAlloc_5555_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
lean_object* v___x_5548_; lean_object* v___x_5549_; lean_object* v___x_5550_; lean_object* v___x_5551_; lean_object* v___x_5552_; lean_object* v___x_5553_; lean_object* v___x_5554_; 
v___x_5548_ = l_Lean_MessageData_ofFormat(v___x_5547_);
v___x_5549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5543_);
lean_ctor_set(v___x_5549_, 1, v___x_5548_);
v___x_5550_ = lean_obj_once(&l_Lean_Meta_mkProjection___closed__7, &l_Lean_Meta_mkProjection___closed__7_once, _init_l_Lean_Meta_mkProjection___closed__7);
v___x_5551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5551_, 0, v___x_5549_);
lean_ctor_set(v___x_5551_, 1, v___x_5550_);
v___x_5552_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_hasTypeMsg(v_s_5520_, v_a_5533_);
v___x_5553_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5553_, 0, v___x_5551_);
lean_ctor_set(v___x_5553_, 1, v___x_5552_);
v___x_5554_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_throwAppBuilderException___redArg(v___x_5542_, v___x_5553_, v___y_5541_, v___y_5538_, v___y_5539_, v___y_5540_);
return v___x_5554_;
}
}
}
}
else
{
lean_del_object(v___x_5530_);
lean_dec(v_fieldName_5521_);
lean_dec_ref(v_s_5520_);
return v___x_5532_;
}
}
}
else
{
lean_dec(v_fieldName_5521_);
lean_dec_ref(v_s_5520_);
return v___x_5527_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(lean_object* v___x_5625_, lean_object* v_declName_5626_, lean_object* v_s_5627_, lean_object* v_fieldName_5628_, lean_object* v_as_5629_, size_t v_sz_5630_, size_t v_i_5631_, lean_object* v_b_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
lean_object* v_a_5639_; uint8_t v___x_5643_; 
v___x_5643_ = lean_usize_dec_lt(v_i_5631_, v_sz_5630_);
if (v___x_5643_ == 0)
{
lean_object* v___x_5644_; 
lean_dec(v_fieldName_5628_);
lean_dec_ref(v_s_5627_);
lean_dec(v_declName_5626_);
lean_dec_ref(v___x_5625_);
v___x_5644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5644_, 0, v_b_5632_);
return v___x_5644_;
}
else
{
lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v_a_5647_; lean_object* v___x_5648_; 
lean_dec_ref(v_b_5632_);
v___x_5645_ = lean_box(0);
v___x_5646_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___closed__0));
v_a_5647_ = lean_array_uget_borrowed(v_as_5629_, v_i_5631_);
lean_inc(v_a_5647_);
lean_inc(v_declName_5626_);
lean_inc_ref(v___x_5625_);
v___x_5648_ = l_Lean_isSubobjectField_x3f(v___x_5625_, v_declName_5626_, v_a_5647_);
if (lean_obj_tag(v___x_5648_) == 0)
{
v_a_5639_ = v___x_5646_;
goto v___jp_5638_;
}
else
{
lean_object* v___x_5650_; uint8_t v_isShared_5651_; uint8_t v_isSharedCheck_5707_; 
v_isSharedCheck_5707_ = !lean_is_exclusive(v___x_5648_);
if (v_isSharedCheck_5707_ == 0)
{
lean_object* v_unused_5708_; 
v_unused_5708_ = lean_ctor_get(v___x_5648_, 0);
lean_dec(v_unused_5708_);
v___x_5650_ = v___x_5648_;
v_isShared_5651_ = v_isSharedCheck_5707_;
goto v_resetjp_5649_;
}
else
{
lean_dec(v___x_5648_);
v___x_5650_ = lean_box(0);
v_isShared_5651_ = v_isSharedCheck_5707_;
goto v_resetjp_5649_;
}
v_resetjp_5649_:
{
lean_object* v___x_5652_; 
lean_inc(v_a_5647_);
lean_inc_ref(v_s_5627_);
v___x_5652_ = l_Lean_Meta_mkProjection(v_s_5627_, v_a_5647_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
if (lean_obj_tag(v___x_5652_) == 0)
{
lean_object* v_a_5653_; lean_object* v___x_5654_; 
v_a_5653_ = lean_ctor_get(v___x_5652_, 0);
lean_inc(v_a_5653_);
lean_dec_ref_known(v___x_5652_, 1);
v___x_5654_ = l_Lean_Meta_saveState___redArg(v___y_5634_, v___y_5636_);
if (lean_obj_tag(v___x_5654_) == 0)
{
lean_object* v_a_5655_; lean_object* v___x_5656_; 
v_a_5655_ = lean_ctor_get(v___x_5654_, 0);
lean_inc(v_a_5655_);
lean_dec_ref_known(v___x_5654_, 1);
lean_inc(v_fieldName_5628_);
v___x_5656_ = l_Lean_Meta_mkProjection(v_a_5653_, v_fieldName_5628_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_);
if (lean_obj_tag(v___x_5656_) == 0)
{
lean_object* v_a_5657_; lean_object* v___x_5659_; uint8_t v_isShared_5660_; uint8_t v_isSharedCheck_5669_; 
lean_dec(v_a_5655_);
lean_dec(v_fieldName_5628_);
lean_dec_ref(v_s_5627_);
lean_dec(v_declName_5626_);
lean_dec_ref(v___x_5625_);
v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5669_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5669_ == 0)
{
v___x_5659_ = v___x_5656_;
v_isShared_5660_ = v_isSharedCheck_5669_;
goto v_resetjp_5658_;
}
else
{
lean_inc(v_a_5657_);
lean_dec(v___x_5656_);
v___x_5659_ = lean_box(0);
v_isShared_5660_ = v_isSharedCheck_5669_;
goto v_resetjp_5658_;
}
v_resetjp_5658_:
{
lean_object* v___x_5662_; 
if (v_isShared_5651_ == 0)
{
lean_ctor_set(v___x_5650_, 0, v_a_5657_);
v___x_5662_ = v___x_5650_;
goto v_reusejp_5661_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5657_);
v___x_5662_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5661_;
}
v_reusejp_5661_:
{
lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5666_; 
v___x_5663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5663_, 0, v___x_5662_);
v___x_5664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5663_);
lean_ctor_set(v___x_5664_, 1, v___x_5645_);
if (v_isShared_5660_ == 0)
{
lean_ctor_set(v___x_5659_, 0, v___x_5664_);
v___x_5666_ = v___x_5659_;
goto v_reusejp_5665_;
}
else
{
lean_object* v_reuseFailAlloc_5667_; 
v_reuseFailAlloc_5667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5667_, 0, v___x_5664_);
v___x_5666_ = v_reuseFailAlloc_5667_;
goto v_reusejp_5665_;
}
v_reusejp_5665_:
{
return v___x_5666_;
}
}
}
}
else
{
lean_object* v_a_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5690_; 
lean_del_object(v___x_5650_);
v_a_5670_ = lean_ctor_get(v___x_5656_, 0);
v_isSharedCheck_5690_ = !lean_is_exclusive(v___x_5656_);
if (v_isSharedCheck_5690_ == 0)
{
v___x_5672_ = v___x_5656_;
v_isShared_5673_ = v_isSharedCheck_5690_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_a_5670_);
lean_dec(v___x_5656_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5690_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
uint8_t v___y_5675_; uint8_t v___x_5688_; 
v___x_5688_ = l_Lean_Exception_isInterrupt(v_a_5670_);
if (v___x_5688_ == 0)
{
uint8_t v___x_5689_; 
lean_inc(v_a_5670_);
v___x_5689_ = l_Lean_Exception_isRuntime(v_a_5670_);
v___y_5675_ = v___x_5689_;
goto v___jp_5674_;
}
else
{
v___y_5675_ = v___x_5688_;
goto v___jp_5674_;
}
v___jp_5674_:
{
if (v___y_5675_ == 0)
{
lean_object* v___x_5676_; 
lean_del_object(v___x_5672_);
lean_dec(v_a_5670_);
v___x_5676_ = l_Lean_Meta_SavedState_restore___redArg(v_a_5655_, v___y_5634_, v___y_5636_);
if (lean_obj_tag(v___x_5676_) == 0)
{
lean_dec_ref_known(v___x_5676_, 1);
v_a_5639_ = v___x_5646_;
goto v___jp_5638_;
}
else
{
lean_object* v_a_5677_; lean_object* v___x_5679_; uint8_t v_isShared_5680_; uint8_t v_isSharedCheck_5684_; 
lean_dec(v_fieldName_5628_);
lean_dec_ref(v_s_5627_);
lean_dec(v_declName_5626_);
lean_dec_ref(v___x_5625_);
v_a_5677_ = lean_ctor_get(v___x_5676_, 0);
v_isSharedCheck_5684_ = !lean_is_exclusive(v___x_5676_);
if (v_isSharedCheck_5684_ == 0)
{
v___x_5679_ = v___x_5676_;
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
else
{
lean_inc(v_a_5677_);
lean_dec(v___x_5676_);
v___x_5679_ = lean_box(0);
v_isShared_5680_ = v_isSharedCheck_5684_;
goto v_resetjp_5678_;
}
v_resetjp_5678_:
{
lean_object* v___x_5682_; 
if (v_isShared_5680_ == 0)
{
v___x_5682_ = v___x_5679_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5683_; 
v_reuseFailAlloc_5683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5683_, 0, v_a_5677_);
v___x_5682_ = v_reuseFailAlloc_5683_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
return v___x_5682_;
}
}
}
}
else
{
lean_object* v___x_5686_; 
lean_dec(v_a_5655_);
lean_dec(v_fieldName_5628_);
lean_dec_ref(v_s_5627_);
lean_dec(v_declName_5626_);
lean_dec_ref(v___x_5625_);
if (v_isShared_5673_ == 0)
{
v___x_5686_ = v___x_5672_;
goto v_reusejp_5685_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v_a_5670_);
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
}
}
else
{
lean_object* v_a_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5698_; 
lean_dec(v_a_5653_);
lean_del_object(v___x_5650_);
lean_dec(v_fieldName_5628_);
lean_dec_ref(v_s_5627_);
lean_dec(v_declName_5626_);
lean_dec_ref(v___x_5625_);
v_a_5691_ = lean_ctor_get(v___x_5654_, 0);
v_isSharedCheck_5698_ = !lean_is_exclusive(v___x_5654_);
if (v_isSharedCheck_5698_ == 0)
{
v___x_5693_ = v___x_5654_;
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_a_5691_);
lean_dec(v___x_5654_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5698_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5696_; 
if (v_isShared_5694_ == 0)
{
v___x_5696_ = v___x_5693_;
goto v_reusejp_5695_;
}
else
{
lean_object* v_reuseFailAlloc_5697_; 
v_reuseFailAlloc_5697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5697_, 0, v_a_5691_);
v___x_5696_ = v_reuseFailAlloc_5697_;
goto v_reusejp_5695_;
}
v_reusejp_5695_:
{
return v___x_5696_;
}
}
}
}
else
{
lean_object* v_a_5699_; lean_object* v___x_5701_; uint8_t v_isShared_5702_; uint8_t v_isSharedCheck_5706_; 
lean_del_object(v___x_5650_);
lean_dec(v_fieldName_5628_);
lean_dec_ref(v_s_5627_);
lean_dec(v_declName_5626_);
lean_dec_ref(v___x_5625_);
v_a_5699_ = lean_ctor_get(v___x_5652_, 0);
v_isSharedCheck_5706_ = !lean_is_exclusive(v___x_5652_);
if (v_isSharedCheck_5706_ == 0)
{
v___x_5701_ = v___x_5652_;
v_isShared_5702_ = v_isSharedCheck_5706_;
goto v_resetjp_5700_;
}
else
{
lean_inc(v_a_5699_);
lean_dec(v___x_5652_);
v___x_5701_ = lean_box(0);
v_isShared_5702_ = v_isSharedCheck_5706_;
goto v_resetjp_5700_;
}
v_resetjp_5700_:
{
lean_object* v___x_5704_; 
if (v_isShared_5702_ == 0)
{
v___x_5704_ = v___x_5701_;
goto v_reusejp_5703_;
}
else
{
lean_object* v_reuseFailAlloc_5705_; 
v_reuseFailAlloc_5705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5705_, 0, v_a_5699_);
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
}
}
v___jp_5638_:
{
size_t v___x_5640_; size_t v___x_5641_; 
v___x_5640_ = ((size_t)1ULL);
v___x_5641_ = lean_usize_add(v_i_5631_, v___x_5640_);
lean_inc_ref(v_a_5639_);
v_i_5631_ = v___x_5641_;
v_b_5632_ = v_a_5639_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0___boxed(lean_object* v___x_5709_, lean_object* v_declName_5710_, lean_object* v_s_5711_, lean_object* v_fieldName_5712_, lean_object* v_as_5713_, lean_object* v_sz_5714_, lean_object* v_i_5715_, lean_object* v_b_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
size_t v_sz_boxed_5722_; size_t v_i_boxed_5723_; lean_object* v_res_5724_; 
v_sz_boxed_5722_ = lean_unbox_usize(v_sz_5714_);
lean_dec(v_sz_5714_);
v_i_boxed_5723_ = lean_unbox_usize(v_i_5715_);
lean_dec(v_i_5715_);
v_res_5724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkProjection_spec__0(v___x_5709_, v_declName_5710_, v_s_5711_, v_fieldName_5712_, v_as_5713_, v_sz_boxed_5722_, v_i_boxed_5723_, v_b_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec_ref(v_as_5713_);
return v_res_5724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkProjection___boxed(lean_object* v_s_5725_, lean_object* v_fieldName_5726_, lean_object* v_a_5727_, lean_object* v_a_5728_, lean_object* v_a_5729_, lean_object* v_a_5730_, lean_object* v_a_5731_){
_start:
{
lean_object* v_res_5732_; 
v_res_5732_ = l_Lean_Meta_mkProjection(v_s_5725_, v_fieldName_5726_, v_a_5727_, v_a_5728_, v_a_5729_, v_a_5730_);
lean_dec(v_a_5730_);
lean_dec_ref(v_a_5729_);
lean_dec(v_a_5728_);
lean_dec_ref(v_a_5727_);
return v_res_5732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(lean_object* v_nil_5733_, lean_object* v_cons_5734_, lean_object* v_x_5735_){
_start:
{
if (lean_obj_tag(v_x_5735_) == 0)
{
lean_dec_ref(v_cons_5734_);
lean_inc_ref(v_nil_5733_);
return v_nil_5733_;
}
else
{
lean_object* v_head_5736_; lean_object* v_tail_5737_; lean_object* v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; 
v_head_5736_ = lean_ctor_get(v_x_5735_, 0);
lean_inc(v_head_5736_);
v_tail_5737_ = lean_ctor_get(v_x_5735_, 1);
lean_inc(v_tail_5737_);
lean_dec_ref_known(v_x_5735_, 2);
lean_inc_ref(v_cons_5734_);
v___x_5738_ = l_Lean_Expr_app___override(v_cons_5734_, v_head_5736_);
v___x_5739_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5733_, v_cons_5734_, v_tail_5737_);
v___x_5740_ = l_Lean_Expr_app___override(v___x_5738_, v___x_5739_);
return v___x_5740_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux___boxed(lean_object* v_nil_5741_, lean_object* v_cons_5742_, lean_object* v_x_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v_nil_5741_, v_cons_5742_, v_x_5743_);
lean_dec_ref(v_nil_5741_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit(lean_object* v_type_5754_, lean_object* v_xs_5755_, lean_object* v_a_5756_, lean_object* v_a_5757_, lean_object* v_a_5758_, lean_object* v_a_5759_){
_start:
{
lean_object* v___x_5761_; 
lean_inc_ref(v_type_5754_);
v___x_5761_ = l_Lean_Meta_getDecLevel(v_type_5754_, v_a_5756_, v_a_5757_, v_a_5758_, v_a_5759_);
if (lean_obj_tag(v___x_5761_) == 0)
{
lean_object* v_a_5762_; lean_object* v___x_5764_; uint8_t v_isShared_5765_; uint8_t v_isSharedCheck_5781_; 
v_a_5762_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5781_ == 0)
{
v___x_5764_ = v___x_5761_;
v_isShared_5765_ = v_isSharedCheck_5781_;
goto v_resetjp_5763_;
}
else
{
lean_inc(v_a_5762_);
lean_dec(v___x_5761_);
v___x_5764_ = lean_box(0);
v_isShared_5765_ = v_isSharedCheck_5781_;
goto v_resetjp_5763_;
}
v_resetjp_5763_:
{
lean_object* v___x_5766_; lean_object* v___x_5767_; lean_object* v___x_5768_; lean_object* v___x_5769_; lean_object* v___x_5770_; 
v___x_5766_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__2));
v___x_5767_ = lean_box(0);
v___x_5768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5768_, 0, v_a_5762_);
lean_ctor_set(v___x_5768_, 1, v___x_5767_);
lean_inc_ref(v___x_5768_);
v___x_5769_ = l_Lean_mkConst(v___x_5766_, v___x_5768_);
lean_inc_ref(v_type_5754_);
v___x_5770_ = l_Lean_Expr_app___override(v___x_5769_, v_type_5754_);
if (lean_obj_tag(v_xs_5755_) == 0)
{
lean_object* v___x_5772_; 
lean_dec_ref_known(v___x_5768_, 2);
lean_dec_ref(v_type_5754_);
if (v_isShared_5765_ == 0)
{
lean_ctor_set(v___x_5764_, 0, v___x_5770_);
v___x_5772_ = v___x_5764_;
goto v_reusejp_5771_;
}
else
{
lean_object* v_reuseFailAlloc_5773_; 
v_reuseFailAlloc_5773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5773_, 0, v___x_5770_);
v___x_5772_ = v_reuseFailAlloc_5773_;
goto v_reusejp_5771_;
}
v_reusejp_5771_:
{
return v___x_5772_;
}
}
else
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5779_; 
v___x_5774_ = ((lean_object*)(l_Lean_Meta_mkListLit___closed__4));
v___x_5775_ = l_Lean_mkConst(v___x_5774_, v___x_5768_);
v___x_5776_ = l_Lean_Expr_app___override(v___x_5775_, v_type_5754_);
v___x_5777_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkListLitAux(v___x_5770_, v___x_5776_, v_xs_5755_);
lean_dec_ref(v___x_5770_);
if (v_isShared_5765_ == 0)
{
lean_ctor_set(v___x_5764_, 0, v___x_5777_);
v___x_5779_ = v___x_5764_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v___x_5777_);
v___x_5779_ = v_reuseFailAlloc_5780_;
goto v_reusejp_5778_;
}
v_reusejp_5778_:
{
return v___x_5779_;
}
}
}
}
else
{
lean_object* v_a_5782_; lean_object* v___x_5784_; uint8_t v_isShared_5785_; uint8_t v_isSharedCheck_5789_; 
lean_dec(v_xs_5755_);
lean_dec_ref(v_type_5754_);
v_a_5782_ = lean_ctor_get(v___x_5761_, 0);
v_isSharedCheck_5789_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5789_ == 0)
{
v___x_5784_ = v___x_5761_;
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
else
{
lean_inc(v_a_5782_);
lean_dec(v___x_5761_);
v___x_5784_ = lean_box(0);
v_isShared_5785_ = v_isSharedCheck_5789_;
goto v_resetjp_5783_;
}
v_resetjp_5783_:
{
lean_object* v___x_5787_; 
if (v_isShared_5785_ == 0)
{
v___x_5787_ = v___x_5784_;
goto v_reusejp_5786_;
}
else
{
lean_object* v_reuseFailAlloc_5788_; 
v_reuseFailAlloc_5788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5788_, 0, v_a_5782_);
v___x_5787_ = v_reuseFailAlloc_5788_;
goto v_reusejp_5786_;
}
v_reusejp_5786_:
{
return v___x_5787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkListLit___boxed(lean_object* v_type_5790_, lean_object* v_xs_5791_, lean_object* v_a_5792_, lean_object* v_a_5793_, lean_object* v_a_5794_, lean_object* v_a_5795_, lean_object* v_a_5796_){
_start:
{
lean_object* v_res_5797_; 
v_res_5797_ = l_Lean_Meta_mkListLit(v_type_5790_, v_xs_5791_, v_a_5792_, v_a_5793_, v_a_5794_, v_a_5795_);
lean_dec(v_a_5795_);
lean_dec_ref(v_a_5794_);
lean_dec(v_a_5793_);
lean_dec_ref(v_a_5792_);
return v_res_5797_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit(lean_object* v_type_5802_, lean_object* v_xs_5803_, lean_object* v_a_5804_, lean_object* v_a_5805_, lean_object* v_a_5806_, lean_object* v_a_5807_){
_start:
{
lean_object* v___x_5809_; 
lean_inc_ref(v_type_5802_);
v___x_5809_ = l_Lean_Meta_getDecLevel(v_type_5802_, v_a_5804_, v_a_5805_, v_a_5806_, v_a_5807_);
if (lean_obj_tag(v___x_5809_) == 0)
{
lean_object* v_a_5810_; lean_object* v___x_5811_; 
v_a_5810_ = lean_ctor_get(v___x_5809_, 0);
lean_inc(v_a_5810_);
lean_dec_ref_known(v___x_5809_, 1);
lean_inc_ref(v_type_5802_);
v___x_5811_ = l_Lean_Meta_mkListLit(v_type_5802_, v_xs_5803_, v_a_5804_, v_a_5805_, v_a_5806_, v_a_5807_);
if (lean_obj_tag(v___x_5811_) == 0)
{
lean_object* v_a_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5825_; 
v_a_5812_ = lean_ctor_get(v___x_5811_, 0);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___x_5811_);
if (v_isSharedCheck_5825_ == 0)
{
v___x_5814_ = v___x_5811_;
v_isShared_5815_ = v_isSharedCheck_5825_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_a_5812_);
lean_dec(v___x_5811_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5825_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5816_; lean_object* v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5823_; 
v___x_5816_ = ((lean_object*)(l_Lean_Meta_mkArrayLit___closed__1));
v___x_5817_ = lean_box(0);
v___x_5818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5818_, 0, v_a_5810_);
lean_ctor_set(v___x_5818_, 1, v___x_5817_);
v___x_5819_ = l_Lean_mkConst(v___x_5816_, v___x_5818_);
v___x_5820_ = l_Lean_Expr_app___override(v___x_5819_, v_type_5802_);
v___x_5821_ = l_Lean_Expr_app___override(v___x_5820_, v_a_5812_);
if (v_isShared_5815_ == 0)
{
lean_ctor_set(v___x_5814_, 0, v___x_5821_);
v___x_5823_ = v___x_5814_;
goto v_reusejp_5822_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v___x_5821_);
v___x_5823_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5822_;
}
v_reusejp_5822_:
{
return v___x_5823_;
}
}
}
else
{
lean_dec(v_a_5810_);
lean_dec_ref(v_type_5802_);
return v___x_5811_;
}
}
else
{
lean_object* v_a_5826_; lean_object* v___x_5828_; uint8_t v_isShared_5829_; uint8_t v_isSharedCheck_5833_; 
lean_dec(v_xs_5803_);
lean_dec_ref(v_type_5802_);
v_a_5826_ = lean_ctor_get(v___x_5809_, 0);
v_isSharedCheck_5833_ = !lean_is_exclusive(v___x_5809_);
if (v_isSharedCheck_5833_ == 0)
{
v___x_5828_ = v___x_5809_;
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
else
{
lean_inc(v_a_5826_);
lean_dec(v___x_5809_);
v___x_5828_ = lean_box(0);
v_isShared_5829_ = v_isSharedCheck_5833_;
goto v_resetjp_5827_;
}
v_resetjp_5827_:
{
lean_object* v___x_5831_; 
if (v_isShared_5829_ == 0)
{
v___x_5831_ = v___x_5828_;
goto v_reusejp_5830_;
}
else
{
lean_object* v_reuseFailAlloc_5832_; 
v_reuseFailAlloc_5832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
v___x_5831_ = v_reuseFailAlloc_5832_;
goto v_reusejp_5830_;
}
v_reusejp_5830_:
{
return v___x_5831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkArrayLit___boxed(lean_object* v_type_5834_, lean_object* v_xs_5835_, lean_object* v_a_5836_, lean_object* v_a_5837_, lean_object* v_a_5838_, lean_object* v_a_5839_, lean_object* v_a_5840_){
_start:
{
lean_object* v_res_5841_; 
v_res_5841_ = l_Lean_Meta_mkArrayLit(v_type_5834_, v_xs_5835_, v_a_5836_, v_a_5837_, v_a_5838_, v_a_5839_);
lean_dec(v_a_5839_);
lean_dec_ref(v_a_5838_);
lean_dec(v_a_5837_);
lean_dec_ref(v_a_5836_);
return v_res_5841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone(lean_object* v_type_5847_, lean_object* v_a_5848_, lean_object* v_a_5849_, lean_object* v_a_5850_, lean_object* v_a_5851_){
_start:
{
lean_object* v___x_5853_; 
lean_inc_ref(v_type_5847_);
v___x_5853_ = l_Lean_Meta_getDecLevel(v_type_5847_, v_a_5848_, v_a_5849_, v_a_5850_, v_a_5851_);
if (lean_obj_tag(v___x_5853_) == 0)
{
lean_object* v_a_5854_; lean_object* v___x_5856_; uint8_t v_isShared_5857_; uint8_t v_isSharedCheck_5866_; 
v_a_5854_ = lean_ctor_get(v___x_5853_, 0);
v_isSharedCheck_5866_ = !lean_is_exclusive(v___x_5853_);
if (v_isSharedCheck_5866_ == 0)
{
v___x_5856_ = v___x_5853_;
v_isShared_5857_ = v_isSharedCheck_5866_;
goto v_resetjp_5855_;
}
else
{
lean_inc(v_a_5854_);
lean_dec(v___x_5853_);
v___x_5856_ = lean_box(0);
v_isShared_5857_ = v_isSharedCheck_5866_;
goto v_resetjp_5855_;
}
v_resetjp_5855_:
{
lean_object* v___x_5858_; lean_object* v___x_5859_; lean_object* v___x_5860_; lean_object* v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5864_; 
v___x_5858_ = ((lean_object*)(l_Lean_Meta_mkNone___closed__2));
v___x_5859_ = lean_box(0);
v___x_5860_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5860_, 0, v_a_5854_);
lean_ctor_set(v___x_5860_, 1, v___x_5859_);
v___x_5861_ = l_Lean_mkConst(v___x_5858_, v___x_5860_);
v___x_5862_ = l_Lean_Expr_app___override(v___x_5861_, v_type_5847_);
if (v_isShared_5857_ == 0)
{
lean_ctor_set(v___x_5856_, 0, v___x_5862_);
v___x_5864_ = v___x_5856_;
goto v_reusejp_5863_;
}
else
{
lean_object* v_reuseFailAlloc_5865_; 
v_reuseFailAlloc_5865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5865_, 0, v___x_5862_);
v___x_5864_ = v_reuseFailAlloc_5865_;
goto v_reusejp_5863_;
}
v_reusejp_5863_:
{
return v___x_5864_;
}
}
}
else
{
lean_object* v_a_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5874_; 
lean_dec_ref(v_type_5847_);
v_a_5867_ = lean_ctor_get(v___x_5853_, 0);
v_isSharedCheck_5874_ = !lean_is_exclusive(v___x_5853_);
if (v_isSharedCheck_5874_ == 0)
{
v___x_5869_ = v___x_5853_;
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_a_5867_);
lean_dec(v___x_5853_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5874_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v___x_5872_; 
if (v_isShared_5870_ == 0)
{
v___x_5872_ = v___x_5869_;
goto v_reusejp_5871_;
}
else
{
lean_object* v_reuseFailAlloc_5873_; 
v_reuseFailAlloc_5873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
v___x_5872_ = v_reuseFailAlloc_5873_;
goto v_reusejp_5871_;
}
v_reusejp_5871_:
{
return v___x_5872_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNone___boxed(lean_object* v_type_5875_, lean_object* v_a_5876_, lean_object* v_a_5877_, lean_object* v_a_5878_, lean_object* v_a_5879_, lean_object* v_a_5880_){
_start:
{
lean_object* v_res_5881_; 
v_res_5881_ = l_Lean_Meta_mkNone(v_type_5875_, v_a_5876_, v_a_5877_, v_a_5878_, v_a_5879_);
lean_dec(v_a_5879_);
lean_dec_ref(v_a_5878_);
lean_dec(v_a_5877_);
lean_dec_ref(v_a_5876_);
return v_res_5881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome(lean_object* v_type_5886_, lean_object* v_value_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_, lean_object* v_a_5890_, lean_object* v_a_5891_){
_start:
{
lean_object* v___x_5893_; 
lean_inc_ref(v_type_5886_);
v___x_5893_ = l_Lean_Meta_getDecLevel(v_type_5886_, v_a_5888_, v_a_5889_, v_a_5890_, v_a_5891_);
if (lean_obj_tag(v___x_5893_) == 0)
{
lean_object* v_a_5894_; lean_object* v___x_5896_; uint8_t v_isShared_5897_; uint8_t v_isSharedCheck_5906_; 
v_a_5894_ = lean_ctor_get(v___x_5893_, 0);
v_isSharedCheck_5906_ = !lean_is_exclusive(v___x_5893_);
if (v_isSharedCheck_5906_ == 0)
{
v___x_5896_ = v___x_5893_;
v_isShared_5897_ = v_isSharedCheck_5906_;
goto v_resetjp_5895_;
}
else
{
lean_inc(v_a_5894_);
lean_dec(v___x_5893_);
v___x_5896_ = lean_box(0);
v_isShared_5897_ = v_isSharedCheck_5906_;
goto v_resetjp_5895_;
}
v_resetjp_5895_:
{
lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5904_; 
v___x_5898_ = ((lean_object*)(l_Lean_Meta_mkSome___closed__1));
v___x_5899_ = lean_box(0);
v___x_5900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5900_, 0, v_a_5894_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v___x_5901_ = l_Lean_mkConst(v___x_5898_, v___x_5900_);
v___x_5902_ = l_Lean_mkAppB(v___x_5901_, v_type_5886_, v_value_5887_);
if (v_isShared_5897_ == 0)
{
lean_ctor_set(v___x_5896_, 0, v___x_5902_);
v___x_5904_ = v___x_5896_;
goto v_reusejp_5903_;
}
else
{
lean_object* v_reuseFailAlloc_5905_; 
v_reuseFailAlloc_5905_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5905_, 0, v___x_5902_);
v___x_5904_ = v_reuseFailAlloc_5905_;
goto v_reusejp_5903_;
}
v_reusejp_5903_:
{
return v___x_5904_;
}
}
}
else
{
lean_object* v_a_5907_; lean_object* v___x_5909_; uint8_t v_isShared_5910_; uint8_t v_isSharedCheck_5914_; 
lean_dec_ref(v_value_5887_);
lean_dec_ref(v_type_5886_);
v_a_5907_ = lean_ctor_get(v___x_5893_, 0);
v_isSharedCheck_5914_ = !lean_is_exclusive(v___x_5893_);
if (v_isSharedCheck_5914_ == 0)
{
v___x_5909_ = v___x_5893_;
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
else
{
lean_inc(v_a_5907_);
lean_dec(v___x_5893_);
v___x_5909_ = lean_box(0);
v_isShared_5910_ = v_isSharedCheck_5914_;
goto v_resetjp_5908_;
}
v_resetjp_5908_:
{
lean_object* v___x_5912_; 
if (v_isShared_5910_ == 0)
{
v___x_5912_ = v___x_5909_;
goto v_reusejp_5911_;
}
else
{
lean_object* v_reuseFailAlloc_5913_; 
v_reuseFailAlloc_5913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5913_, 0, v_a_5907_);
v___x_5912_ = v_reuseFailAlloc_5913_;
goto v_reusejp_5911_;
}
v_reusejp_5911_:
{
return v___x_5912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSome___boxed(lean_object* v_type_5915_, lean_object* v_value_5916_, lean_object* v_a_5917_, lean_object* v_a_5918_, lean_object* v_a_5919_, lean_object* v_a_5920_, lean_object* v_a_5921_){
_start:
{
lean_object* v_res_5922_; 
v_res_5922_ = l_Lean_Meta_mkSome(v_type_5915_, v_value_5916_, v_a_5917_, v_a_5918_, v_a_5919_, v_a_5920_);
lean_dec(v_a_5920_);
lean_dec_ref(v_a_5919_);
lean_dec(v_a_5918_);
lean_dec_ref(v_a_5917_);
return v_res_5922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide(lean_object* v_p_5928_, lean_object* v_a_5929_, lean_object* v_a_5930_, lean_object* v_a_5931_, lean_object* v_a_5932_){
_start:
{
lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5934_ = ((lean_object*)(l_Lean_Meta_mkDecide___closed__2));
v___x_5935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5935_, 0, v_p_5928_);
v___x_5936_ = lean_box(0);
v___x_5937_ = lean_unsigned_to_nat(2u);
v___x_5938_ = lean_mk_empty_array_with_capacity(v___x_5937_);
v___x_5939_ = lean_array_push(v___x_5938_, v___x_5935_);
v___x_5940_ = lean_array_push(v___x_5939_, v___x_5936_);
v___x_5941_ = l_Lean_Meta_mkAppOptM(v___x_5934_, v___x_5940_, v_a_5929_, v_a_5930_, v_a_5931_, v_a_5932_);
return v___x_5941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecide___boxed(lean_object* v_p_5942_, lean_object* v_a_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_){
_start:
{
lean_object* v_res_5948_; 
v_res_5948_ = l_Lean_Meta_mkDecide(v_p_5942_, v_a_5943_, v_a_5944_, v_a_5945_, v_a_5946_);
lean_dec(v_a_5946_);
lean_dec_ref(v_a_5945_);
lean_dec(v_a_5944_);
lean_dec_ref(v_a_5943_);
return v_res_5948_;
}
}
static lean_object* _init_l_Lean_Meta_mkDecideProof___closed__3(void){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; 
v___x_5954_ = lean_box(0);
v___x_5955_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__2));
v___x_5956_ = l_Lean_mkConst(v___x_5955_, v___x_5954_);
return v___x_5956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof(lean_object* v_p_5960_, lean_object* v_a_5961_, lean_object* v_a_5962_, lean_object* v_a_5963_, lean_object* v_a_5964_){
_start:
{
lean_object* v___x_5966_; 
v___x_5966_ = l_Lean_Meta_mkDecide(v_p_5960_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_);
if (lean_obj_tag(v___x_5966_) == 0)
{
lean_object* v_a_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; 
v_a_5967_ = lean_ctor_get(v___x_5966_, 0);
lean_inc(v_a_5967_);
lean_dec_ref_known(v___x_5966_, 1);
v___x_5968_ = lean_obj_once(&l_Lean_Meta_mkDecideProof___closed__3, &l_Lean_Meta_mkDecideProof___closed__3_once, _init_l_Lean_Meta_mkDecideProof___closed__3);
v___x_5969_ = l_Lean_Meta_mkEq(v_a_5967_, v___x_5968_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_);
if (lean_obj_tag(v___x_5969_) == 0)
{
lean_object* v_a_5970_; lean_object* v___x_5971_; 
v_a_5970_ = lean_ctor_get(v___x_5969_, 0);
lean_inc(v_a_5970_);
lean_dec_ref_known(v___x_5969_, 1);
v___x_5971_ = l_Lean_Meta_mkEqRefl(v___x_5968_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_);
if (lean_obj_tag(v___x_5971_) == 0)
{
lean_object* v_a_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
v_a_5972_ = lean_ctor_get(v___x_5971_, 0);
lean_inc(v_a_5972_);
lean_dec_ref_known(v___x_5971_, 1);
v___x_5973_ = l_Lean_Meta_mkExpectedPropHint(v_a_5972_, v_a_5970_);
v___x_5974_ = ((lean_object*)(l_Lean_Meta_mkDecideProof___closed__5));
v___x_5975_ = lean_unsigned_to_nat(1u);
v___x_5976_ = lean_mk_empty_array_with_capacity(v___x_5975_);
v___x_5977_ = lean_array_push(v___x_5976_, v___x_5973_);
v___x_5978_ = l_Lean_Meta_mkAppM(v___x_5974_, v___x_5977_, v_a_5961_, v_a_5962_, v_a_5963_, v_a_5964_);
return v___x_5978_;
}
else
{
lean_dec(v_a_5970_);
return v___x_5971_;
}
}
else
{
return v___x_5969_;
}
}
else
{
return v___x_5966_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDecideProof___boxed(lean_object* v_p_5979_, lean_object* v_a_5980_, lean_object* v_a_5981_, lean_object* v_a_5982_, lean_object* v_a_5983_, lean_object* v_a_5984_){
_start:
{
lean_object* v_res_5985_; 
v_res_5985_ = l_Lean_Meta_mkDecideProof(v_p_5979_, v_a_5980_, v_a_5981_, v_a_5982_, v_a_5983_);
lean_dec(v_a_5983_);
lean_dec_ref(v_a_5982_);
lean_dec(v_a_5981_);
lean_dec_ref(v_a_5980_);
return v_res_5985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt(lean_object* v_a_5991_, lean_object* v_b_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_5998_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_5999_ = lean_unsigned_to_nat(2u);
v___x_6000_ = lean_mk_empty_array_with_capacity(v___x_5999_);
v___x_6001_ = lean_array_push(v___x_6000_, v_a_5991_);
v___x_6002_ = lean_array_push(v___x_6001_, v_b_5992_);
v___x_6003_ = l_Lean_Meta_mkAppM(v___x_5998_, v___x_6002_, v_a_5993_, v_a_5994_, v_a_5995_, v_a_5996_);
return v___x_6003_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLt___boxed(lean_object* v_a_6004_, lean_object* v_b_6005_, lean_object* v_a_6006_, lean_object* v_a_6007_, lean_object* v_a_6008_, lean_object* v_a_6009_, lean_object* v_a_6010_){
_start:
{
lean_object* v_res_6011_; 
v_res_6011_ = l_Lean_Meta_mkLt(v_a_6004_, v_b_6005_, v_a_6006_, v_a_6007_, v_a_6008_, v_a_6009_);
lean_dec(v_a_6009_);
lean_dec_ref(v_a_6008_);
lean_dec(v_a_6007_);
lean_dec_ref(v_a_6006_);
return v_res_6011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe(lean_object* v_a_6017_, lean_object* v_b_6018_, lean_object* v_a_6019_, lean_object* v_a_6020_, lean_object* v_a_6021_, lean_object* v_a_6022_){
_start:
{
lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; 
v___x_6024_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6025_ = lean_unsigned_to_nat(2u);
v___x_6026_ = lean_mk_empty_array_with_capacity(v___x_6025_);
v___x_6027_ = lean_array_push(v___x_6026_, v_a_6017_);
v___x_6028_ = lean_array_push(v___x_6027_, v_b_6018_);
v___x_6029_ = l_Lean_Meta_mkAppM(v___x_6024_, v___x_6028_, v_a_6019_, v_a_6020_, v_a_6021_, v_a_6022_);
return v___x_6029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLe___boxed(lean_object* v_a_6030_, lean_object* v_b_6031_, lean_object* v_a_6032_, lean_object* v_a_6033_, lean_object* v_a_6034_, lean_object* v_a_6035_, lean_object* v_a_6036_){
_start:
{
lean_object* v_res_6037_; 
v_res_6037_ = l_Lean_Meta_mkLe(v_a_6030_, v_b_6031_, v_a_6032_, v_a_6033_, v_a_6034_, v_a_6035_);
lean_dec(v_a_6035_);
lean_dec_ref(v_a_6034_);
lean_dec(v_a_6033_);
lean_dec_ref(v_a_6032_);
return v_res_6037_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault(lean_object* v_00_u03b1_6043_, lean_object* v_a_6044_, lean_object* v_a_6045_, lean_object* v_a_6046_, lean_object* v_a_6047_){
_start:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; 
v___x_6049_ = ((lean_object*)(l_Lean_Meta_mkDefault___closed__2));
v___x_6050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6050_, 0, v_00_u03b1_6043_);
v___x_6051_ = lean_box(0);
v___x_6052_ = lean_unsigned_to_nat(2u);
v___x_6053_ = lean_mk_empty_array_with_capacity(v___x_6052_);
v___x_6054_ = lean_array_push(v___x_6053_, v___x_6050_);
v___x_6055_ = lean_array_push(v___x_6054_, v___x_6051_);
v___x_6056_ = l_Lean_Meta_mkAppOptM(v___x_6049_, v___x_6055_, v_a_6044_, v_a_6045_, v_a_6046_, v_a_6047_);
return v___x_6056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkDefault___boxed(lean_object* v_00_u03b1_6057_, lean_object* v_a_6058_, lean_object* v_a_6059_, lean_object* v_a_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_){
_start:
{
lean_object* v_res_6063_; 
v_res_6063_ = l_Lean_Meta_mkDefault(v_00_u03b1_6057_, v_a_6058_, v_a_6059_, v_a_6060_, v_a_6061_);
lean_dec(v_a_6061_);
lean_dec_ref(v_a_6060_);
lean_dec(v_a_6059_);
lean_dec_ref(v_a_6058_);
return v_res_6063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty(lean_object* v_00_u03b1_6069_, lean_object* v_a_6070_, lean_object* v_a_6071_, lean_object* v_a_6072_, lean_object* v_a_6073_){
_start:
{
lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; 
v___x_6075_ = ((lean_object*)(l_Lean_Meta_mkOfNonempty___closed__2));
v___x_6076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6076_, 0, v_00_u03b1_6069_);
v___x_6077_ = lean_box(0);
v___x_6078_ = lean_unsigned_to_nat(2u);
v___x_6079_ = lean_mk_empty_array_with_capacity(v___x_6078_);
v___x_6080_ = lean_array_push(v___x_6079_, v___x_6076_);
v___x_6081_ = lean_array_push(v___x_6080_, v___x_6077_);
v___x_6082_ = l_Lean_Meta_mkAppOptM(v___x_6075_, v___x_6081_, v_a_6070_, v_a_6071_, v_a_6072_, v_a_6073_);
return v___x_6082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfNonempty___boxed(lean_object* v_00_u03b1_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_){
_start:
{
lean_object* v_res_6089_; 
v_res_6089_ = l_Lean_Meta_mkOfNonempty(v_00_u03b1_6083_, v_a_6084_, v_a_6085_, v_a_6086_, v_a_6087_);
lean_dec(v_a_6087_);
lean_dec_ref(v_a_6086_);
lean_dec(v_a_6085_);
lean_dec_ref(v_a_6084_);
return v_res_6089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt(lean_object* v_h_6093_, lean_object* v_a_6094_, lean_object* v_a_6095_, lean_object* v_a_6096_, lean_object* v_a_6097_){
_start:
{
lean_object* v___x_6099_; lean_object* v___x_6100_; lean_object* v___x_6101_; lean_object* v___x_6102_; lean_object* v___x_6103_; 
v___x_6099_ = ((lean_object*)(l_Lean_Meta_mkFunExt___closed__1));
v___x_6100_ = lean_unsigned_to_nat(1u);
v___x_6101_ = lean_mk_empty_array_with_capacity(v___x_6100_);
v___x_6102_ = lean_array_push(v___x_6101_, v_h_6093_);
v___x_6103_ = l_Lean_Meta_mkAppM(v___x_6099_, v___x_6102_, v_a_6094_, v_a_6095_, v_a_6096_, v_a_6097_);
return v___x_6103_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkFunExt___boxed(lean_object* v_h_6104_, lean_object* v_a_6105_, lean_object* v_a_6106_, lean_object* v_a_6107_, lean_object* v_a_6108_, lean_object* v_a_6109_){
_start:
{
lean_object* v_res_6110_; 
v_res_6110_ = l_Lean_Meta_mkFunExt(v_h_6104_, v_a_6105_, v_a_6106_, v_a_6107_, v_a_6108_);
lean_dec(v_a_6108_);
lean_dec_ref(v_a_6107_);
lean_dec(v_a_6106_);
lean_dec_ref(v_a_6105_);
return v_res_6110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt(lean_object* v_h_6114_, lean_object* v_a_6115_, lean_object* v_a_6116_, lean_object* v_a_6117_, lean_object* v_a_6118_){
_start:
{
lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; 
v___x_6120_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6121_ = lean_unsigned_to_nat(1u);
v___x_6122_ = lean_mk_empty_array_with_capacity(v___x_6121_);
v___x_6123_ = lean_array_push(v___x_6122_, v_h_6114_);
v___x_6124_ = l_Lean_Meta_mkAppM(v___x_6120_, v___x_6123_, v_a_6115_, v_a_6116_, v_a_6117_, v_a_6118_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkPropExt___boxed(lean_object* v_h_6125_, lean_object* v_a_6126_, lean_object* v_a_6127_, lean_object* v_a_6128_, lean_object* v_a_6129_, lean_object* v_a_6130_){
_start:
{
lean_object* v_res_6131_; 
v_res_6131_ = l_Lean_Meta_mkPropExt(v_h_6125_, v_a_6126_, v_a_6127_, v_a_6128_, v_a_6129_);
lean_dec(v_a_6129_);
lean_dec_ref(v_a_6128_);
lean_dec(v_a_6127_);
lean_dec_ref(v_a_6126_);
return v_res_6131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr(lean_object* v_h_u2081_6135_, lean_object* v_h_u2082_6136_, lean_object* v_a_6137_, lean_object* v_a_6138_, lean_object* v_a_6139_, lean_object* v_a_6140_){
_start:
{
lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; 
v___x_6142_ = ((lean_object*)(l_Lean_Meta_mkLetCongr___closed__1));
v___x_6143_ = lean_unsigned_to_nat(2u);
v___x_6144_ = lean_mk_empty_array_with_capacity(v___x_6143_);
v___x_6145_ = lean_array_push(v___x_6144_, v_h_u2081_6135_);
v___x_6146_ = lean_array_push(v___x_6145_, v_h_u2082_6136_);
v___x_6147_ = l_Lean_Meta_mkAppM(v___x_6142_, v___x_6146_, v_a_6137_, v_a_6138_, v_a_6139_, v_a_6140_);
return v___x_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetCongr___boxed(lean_object* v_h_u2081_6148_, lean_object* v_h_u2082_6149_, lean_object* v_a_6150_, lean_object* v_a_6151_, lean_object* v_a_6152_, lean_object* v_a_6153_, lean_object* v_a_6154_){
_start:
{
lean_object* v_res_6155_; 
v_res_6155_ = l_Lean_Meta_mkLetCongr(v_h_u2081_6148_, v_h_u2082_6149_, v_a_6150_, v_a_6151_, v_a_6152_, v_a_6153_);
lean_dec(v_a_6153_);
lean_dec_ref(v_a_6152_);
lean_dec(v_a_6151_);
lean_dec_ref(v_a_6150_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr(lean_object* v_b_6159_, lean_object* v_h_6160_, lean_object* v_a_6161_, lean_object* v_a_6162_, lean_object* v_a_6163_, lean_object* v_a_6164_){
_start:
{
lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; 
v___x_6166_ = ((lean_object*)(l_Lean_Meta_mkLetValCongr___closed__1));
v___x_6167_ = lean_unsigned_to_nat(2u);
v___x_6168_ = lean_mk_empty_array_with_capacity(v___x_6167_);
v___x_6169_ = lean_array_push(v___x_6168_, v_b_6159_);
v___x_6170_ = lean_array_push(v___x_6169_, v_h_6160_);
v___x_6171_ = l_Lean_Meta_mkAppM(v___x_6166_, v___x_6170_, v_a_6161_, v_a_6162_, v_a_6163_, v_a_6164_);
return v___x_6171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetValCongr___boxed(lean_object* v_b_6172_, lean_object* v_h_6173_, lean_object* v_a_6174_, lean_object* v_a_6175_, lean_object* v_a_6176_, lean_object* v_a_6177_, lean_object* v_a_6178_){
_start:
{
lean_object* v_res_6179_; 
v_res_6179_ = l_Lean_Meta_mkLetValCongr(v_b_6172_, v_h_6173_, v_a_6174_, v_a_6175_, v_a_6176_, v_a_6177_);
lean_dec(v_a_6177_);
lean_dec_ref(v_a_6176_);
lean_dec(v_a_6175_);
lean_dec_ref(v_a_6174_);
return v_res_6179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr(lean_object* v_a_6183_, lean_object* v_h_6184_, lean_object* v_a_6185_, lean_object* v_a_6186_, lean_object* v_a_6187_, lean_object* v_a_6188_){
_start:
{
lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; lean_object* v___x_6194_; lean_object* v___x_6195_; 
v___x_6190_ = ((lean_object*)(l_Lean_Meta_mkLetBodyCongr___closed__1));
v___x_6191_ = lean_unsigned_to_nat(2u);
v___x_6192_ = lean_mk_empty_array_with_capacity(v___x_6191_);
v___x_6193_ = lean_array_push(v___x_6192_, v_a_6183_);
v___x_6194_ = lean_array_push(v___x_6193_, v_h_6184_);
v___x_6195_ = l_Lean_Meta_mkAppM(v___x_6190_, v___x_6194_, v_a_6185_, v_a_6186_, v_a_6187_, v_a_6188_);
return v___x_6195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLetBodyCongr___boxed(lean_object* v_a_6196_, lean_object* v_h_6197_, lean_object* v_a_6198_, lean_object* v_a_6199_, lean_object* v_a_6200_, lean_object* v_a_6201_, lean_object* v_a_6202_){
_start:
{
lean_object* v_res_6203_; 
v_res_6203_ = l_Lean_Meta_mkLetBodyCongr(v_a_6196_, v_h_6197_, v_a_6198_, v_a_6199_, v_a_6200_, v_a_6201_);
lean_dec(v_a_6201_);
lean_dec_ref(v_a_6200_);
lean_dec(v_a_6199_);
lean_dec_ref(v_a_6198_);
return v_res_6203_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqFalseCore___closed__2(void){
_start:
{
lean_object* v___x_6207_; lean_object* v___x_6208_; lean_object* v___x_6209_; 
v___x_6207_ = lean_box(0);
v___x_6208_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6209_ = l_Lean_mkConst(v___x_6208_, v___x_6207_);
return v___x_6209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object* v_p_6213_, lean_object* v_h_6214_){
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
v___x_6224_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
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
v___x_6216_ = lean_obj_once(&l_Lean_Meta_mkOfEqFalseCore___closed__2, &l_Lean_Meta_mkOfEqFalseCore___closed__2_once, _init_l_Lean_Meta_mkOfEqFalseCore___closed__2);
v___x_6217_ = l_Lean_mkAppB(v___x_6216_, v_p_6213_, v_h_6214_);
return v___x_6217_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse(lean_object* v_h_6226_, lean_object* v_a_6227_, lean_object* v_a_6228_, lean_object* v_a_6229_, lean_object* v_a_6230_){
_start:
{
lean_object* v___y_6233_; lean_object* v___y_6234_; lean_object* v___y_6235_; lean_object* v___y_6236_; lean_object* v___x_6242_; 
lean_inc_ref(v_h_6226_);
v___x_6242_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6226_, v_a_6228_);
if (lean_obj_tag(v___x_6242_) == 0)
{
lean_object* v_a_6243_; lean_object* v___x_6245_; uint8_t v_isShared_6246_; uint8_t v_isSharedCheck_6258_; 
v_a_6243_ = lean_ctor_get(v___x_6242_, 0);
v_isSharedCheck_6258_ = !lean_is_exclusive(v___x_6242_);
if (v_isSharedCheck_6258_ == 0)
{
v___x_6245_ = v___x_6242_;
v_isShared_6246_ = v_isSharedCheck_6258_;
goto v_resetjp_6244_;
}
else
{
lean_inc(v_a_6243_);
lean_dec(v___x_6242_);
v___x_6245_ = lean_box(0);
v_isShared_6246_ = v_isSharedCheck_6258_;
goto v_resetjp_6244_;
}
v_resetjp_6244_:
{
lean_object* v___x_6247_; uint8_t v___x_6248_; 
v___x_6247_ = l_Lean_Expr_cleanupAnnotations(v_a_6243_);
v___x_6248_ = l_Lean_Expr_isApp(v___x_6247_);
if (v___x_6248_ == 0)
{
lean_dec_ref(v___x_6247_);
lean_del_object(v___x_6245_);
v___y_6233_ = v_a_6227_;
v___y_6234_ = v_a_6228_;
v___y_6235_ = v_a_6229_;
v___y_6236_ = v_a_6230_;
goto v___jp_6232_;
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
lean_del_object(v___x_6245_);
v___y_6233_ = v_a_6227_;
v___y_6234_ = v_a_6228_;
v___y_6235_ = v_a_6229_;
v___y_6236_ = v_a_6230_;
goto v___jp_6232_;
}
else
{
lean_object* v___x_6252_; lean_object* v___x_6253_; uint8_t v___x_6254_; 
v___x_6252_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6250_);
v___x_6253_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6254_ = l_Lean_Expr_isConstOf(v___x_6252_, v___x_6253_);
lean_dec_ref(v___x_6252_);
if (v___x_6254_ == 0)
{
lean_dec_ref(v_arg_6249_);
lean_del_object(v___x_6245_);
v___y_6233_ = v_a_6227_;
v___y_6234_ = v_a_6228_;
v___y_6235_ = v_a_6229_;
v___y_6236_ = v_a_6230_;
goto v___jp_6232_;
}
else
{
lean_object* v___x_6256_; 
lean_dec_ref(v_h_6226_);
if (v_isShared_6246_ == 0)
{
lean_ctor_set(v___x_6245_, 0, v_arg_6249_);
v___x_6256_ = v___x_6245_;
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
}
}
else
{
lean_dec_ref(v_h_6226_);
return v___x_6242_;
}
v___jp_6232_:
{
lean_object* v___x_6237_; lean_object* v___x_6238_; lean_object* v___x_6239_; lean_object* v___x_6240_; lean_object* v___x_6241_; 
v___x_6237_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6238_ = lean_unsigned_to_nat(1u);
v___x_6239_ = lean_mk_empty_array_with_capacity(v___x_6238_);
v___x_6240_ = lean_array_push(v___x_6239_, v_h_6226_);
v___x_6241_ = l_Lean_Meta_mkAppM(v___x_6237_, v___x_6240_, v___y_6233_, v___y_6234_, v___y_6235_, v___y_6236_);
return v___x_6241_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqFalse___boxed(lean_object* v_h_6259_, lean_object* v_a_6260_, lean_object* v_a_6261_, lean_object* v_a_6262_, lean_object* v_a_6263_, lean_object* v_a_6264_){
_start:
{
lean_object* v_res_6265_; 
v_res_6265_ = l_Lean_Meta_mkOfEqFalse(v_h_6259_, v_a_6260_, v_a_6261_, v_a_6262_, v_a_6263_);
lean_dec(v_a_6263_);
lean_dec_ref(v_a_6262_);
lean_dec(v_a_6261_);
lean_dec_ref(v_a_6260_);
return v_res_6265_;
}
}
static lean_object* _init_l_Lean_Meta_mkOfEqTrueCore___closed__2(void){
_start:
{
lean_object* v___x_6269_; lean_object* v___x_6270_; lean_object* v___x_6271_; 
v___x_6269_ = lean_box(0);
v___x_6270_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6271_ = l_Lean_mkConst(v___x_6270_, v___x_6269_);
return v___x_6271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrueCore(lean_object* v_p_6275_, lean_object* v_h_6276_){
_start:
{
lean_object* v___x_6280_; uint8_t v___x_6281_; 
lean_inc_ref(v_h_6276_);
v___x_6280_ = l_Lean_Expr_cleanupAnnotations(v_h_6276_);
v___x_6281_ = l_Lean_Expr_isApp(v___x_6280_);
if (v___x_6281_ == 0)
{
lean_dec_ref(v___x_6280_);
goto v___jp_6277_;
}
else
{
lean_object* v_arg_6282_; lean_object* v___x_6283_; uint8_t v___x_6284_; 
v_arg_6282_ = lean_ctor_get(v___x_6280_, 1);
lean_inc_ref(v_arg_6282_);
v___x_6283_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6280_);
v___x_6284_ = l_Lean_Expr_isApp(v___x_6283_);
if (v___x_6284_ == 0)
{
lean_dec_ref(v___x_6283_);
lean_dec_ref(v_arg_6282_);
goto v___jp_6277_;
}
else
{
lean_object* v___x_6285_; lean_object* v___x_6286_; uint8_t v___x_6287_; 
v___x_6285_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6283_);
v___x_6286_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6287_ = l_Lean_Expr_isConstOf(v___x_6285_, v___x_6286_);
lean_dec_ref(v___x_6285_);
if (v___x_6287_ == 0)
{
lean_dec_ref(v_arg_6282_);
goto v___jp_6277_;
}
else
{
lean_dec_ref(v_h_6276_);
lean_dec_ref(v_p_6275_);
return v_arg_6282_;
}
}
}
v___jp_6277_:
{
lean_object* v___x_6278_; lean_object* v___x_6279_; 
v___x_6278_ = lean_obj_once(&l_Lean_Meta_mkOfEqTrueCore___closed__2, &l_Lean_Meta_mkOfEqTrueCore___closed__2_once, _init_l_Lean_Meta_mkOfEqTrueCore___closed__2);
v___x_6279_ = l_Lean_mkAppB(v___x_6278_, v_p_6275_, v_h_6276_);
return v___x_6279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue(lean_object* v_h_6288_, lean_object* v_a_6289_, lean_object* v_a_6290_, lean_object* v_a_6291_, lean_object* v_a_6292_){
_start:
{
lean_object* v___y_6295_; lean_object* v___y_6296_; lean_object* v___y_6297_; lean_object* v___y_6298_; lean_object* v___x_6304_; 
lean_inc_ref(v_h_6288_);
v___x_6304_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6288_, v_a_6290_);
if (lean_obj_tag(v___x_6304_) == 0)
{
lean_object* v_a_6305_; lean_object* v___x_6307_; uint8_t v_isShared_6308_; uint8_t v_isSharedCheck_6320_; 
v_a_6305_ = lean_ctor_get(v___x_6304_, 0);
v_isSharedCheck_6320_ = !lean_is_exclusive(v___x_6304_);
if (v_isSharedCheck_6320_ == 0)
{
v___x_6307_ = v___x_6304_;
v_isShared_6308_ = v_isSharedCheck_6320_;
goto v_resetjp_6306_;
}
else
{
lean_inc(v_a_6305_);
lean_dec(v___x_6304_);
v___x_6307_ = lean_box(0);
v_isShared_6308_ = v_isSharedCheck_6320_;
goto v_resetjp_6306_;
}
v_resetjp_6306_:
{
lean_object* v___x_6309_; uint8_t v___x_6310_; 
v___x_6309_ = l_Lean_Expr_cleanupAnnotations(v_a_6305_);
v___x_6310_ = l_Lean_Expr_isApp(v___x_6309_);
if (v___x_6310_ == 0)
{
lean_dec_ref(v___x_6309_);
lean_del_object(v___x_6307_);
v___y_6295_ = v_a_6289_;
v___y_6296_ = v_a_6290_;
v___y_6297_ = v_a_6291_;
v___y_6298_ = v_a_6292_;
goto v___jp_6294_;
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
lean_del_object(v___x_6307_);
v___y_6295_ = v_a_6289_;
v___y_6296_ = v_a_6290_;
v___y_6297_ = v_a_6291_;
v___y_6298_ = v_a_6292_;
goto v___jp_6294_;
}
else
{
lean_object* v___x_6314_; lean_object* v___x_6315_; uint8_t v___x_6316_; 
v___x_6314_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6312_);
v___x_6315_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6316_ = l_Lean_Expr_isConstOf(v___x_6314_, v___x_6315_);
lean_dec_ref(v___x_6314_);
if (v___x_6316_ == 0)
{
lean_dec_ref(v_arg_6311_);
lean_del_object(v___x_6307_);
v___y_6295_ = v_a_6289_;
v___y_6296_ = v_a_6290_;
v___y_6297_ = v_a_6291_;
v___y_6298_ = v_a_6292_;
goto v___jp_6294_;
}
else
{
lean_object* v___x_6318_; 
lean_dec_ref(v_h_6288_);
if (v_isShared_6308_ == 0)
{
lean_ctor_set(v___x_6307_, 0, v_arg_6311_);
v___x_6318_ = v___x_6307_;
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
}
}
else
{
lean_dec_ref(v_h_6288_);
return v___x_6304_;
}
v___jp_6294_:
{
lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; 
v___x_6299_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6300_ = lean_unsigned_to_nat(1u);
v___x_6301_ = lean_mk_empty_array_with_capacity(v___x_6300_);
v___x_6302_ = lean_array_push(v___x_6301_, v_h_6288_);
v___x_6303_ = l_Lean_Meta_mkAppM(v___x_6299_, v___x_6302_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_);
return v___x_6303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkOfEqTrue___boxed(lean_object* v_h_6321_, lean_object* v_a_6322_, lean_object* v_a_6323_, lean_object* v_a_6324_, lean_object* v_a_6325_, lean_object* v_a_6326_){
_start:
{
lean_object* v_res_6327_; 
v_res_6327_ = l_Lean_Meta_mkOfEqTrue(v_h_6321_, v_a_6322_, v_a_6323_, v_a_6324_, v_a_6325_);
lean_dec(v_a_6325_);
lean_dec_ref(v_a_6324_);
lean_dec(v_a_6323_);
lean_dec_ref(v_a_6322_);
return v_res_6327_;
}
}
static lean_object* _init_l_Lean_Meta_mkEqTrueCore___closed__0(void){
_start:
{
lean_object* v___x_6328_; lean_object* v___x_6329_; lean_object* v___x_6330_; 
v___x_6328_ = lean_box(0);
v___x_6329_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__4));
v___x_6330_ = l_Lean_mkConst(v___x_6329_, v___x_6328_);
return v___x_6330_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrueCore(lean_object* v_p_6331_, lean_object* v_h_6332_){
_start:
{
lean_object* v___x_6336_; uint8_t v___x_6337_; 
lean_inc_ref(v_h_6332_);
v___x_6336_ = l_Lean_Expr_cleanupAnnotations(v_h_6332_);
v___x_6337_ = l_Lean_Expr_isApp(v___x_6336_);
if (v___x_6337_ == 0)
{
lean_dec_ref(v___x_6336_);
goto v___jp_6333_;
}
else
{
lean_object* v_arg_6338_; lean_object* v___x_6339_; uint8_t v___x_6340_; 
v_arg_6338_ = lean_ctor_get(v___x_6336_, 1);
lean_inc_ref(v_arg_6338_);
v___x_6339_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6336_);
v___x_6340_ = l_Lean_Expr_isApp(v___x_6339_);
if (v___x_6340_ == 0)
{
lean_dec_ref(v___x_6339_);
lean_dec_ref(v_arg_6338_);
goto v___jp_6333_;
}
else
{
lean_object* v___x_6341_; lean_object* v___x_6342_; uint8_t v___x_6343_; 
v___x_6341_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6339_);
v___x_6342_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6343_ = l_Lean_Expr_isConstOf(v___x_6341_, v___x_6342_);
lean_dec_ref(v___x_6341_);
if (v___x_6343_ == 0)
{
lean_dec_ref(v_arg_6338_);
goto v___jp_6333_;
}
else
{
lean_dec_ref(v_h_6332_);
lean_dec_ref(v_p_6331_);
return v_arg_6338_;
}
}
}
v___jp_6333_:
{
lean_object* v___x_6334_; lean_object* v___x_6335_; 
v___x_6334_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6335_ = l_Lean_mkAppB(v___x_6334_, v_p_6331_, v_h_6332_);
return v___x_6335_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue(lean_object* v_h_6344_, lean_object* v_a_6345_, lean_object* v_a_6346_, lean_object* v_a_6347_, lean_object* v_a_6348_){
_start:
{
lean_object* v___y_6351_; lean_object* v___y_6352_; lean_object* v___y_6353_; lean_object* v___y_6354_; lean_object* v___x_6366_; 
lean_inc_ref(v_h_6344_);
v___x_6366_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_h_6344_, v_a_6346_);
if (lean_obj_tag(v___x_6366_) == 0)
{
lean_object* v_a_6367_; lean_object* v___x_6369_; uint8_t v_isShared_6370_; uint8_t v_isSharedCheck_6382_; 
v_a_6367_ = lean_ctor_get(v___x_6366_, 0);
v_isSharedCheck_6382_ = !lean_is_exclusive(v___x_6366_);
if (v_isSharedCheck_6382_ == 0)
{
v___x_6369_ = v___x_6366_;
v_isShared_6370_ = v_isSharedCheck_6382_;
goto v_resetjp_6368_;
}
else
{
lean_inc(v_a_6367_);
lean_dec(v___x_6366_);
v___x_6369_ = lean_box(0);
v_isShared_6370_ = v_isSharedCheck_6382_;
goto v_resetjp_6368_;
}
v_resetjp_6368_:
{
lean_object* v___x_6371_; uint8_t v___x_6372_; 
v___x_6371_ = l_Lean_Expr_cleanupAnnotations(v_a_6367_);
v___x_6372_ = l_Lean_Expr_isApp(v___x_6371_);
if (v___x_6372_ == 0)
{
lean_dec_ref(v___x_6371_);
lean_del_object(v___x_6369_);
v___y_6351_ = v_a_6345_;
v___y_6352_ = v_a_6346_;
v___y_6353_ = v_a_6347_;
v___y_6354_ = v_a_6348_;
goto v___jp_6350_;
}
else
{
lean_object* v_arg_6373_; lean_object* v___x_6374_; uint8_t v___x_6375_; 
v_arg_6373_ = lean_ctor_get(v___x_6371_, 1);
lean_inc_ref(v_arg_6373_);
v___x_6374_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6371_);
v___x_6375_ = l_Lean_Expr_isApp(v___x_6374_);
if (v___x_6375_ == 0)
{
lean_dec_ref(v___x_6374_);
lean_dec_ref(v_arg_6373_);
lean_del_object(v___x_6369_);
v___y_6351_ = v_a_6345_;
v___y_6352_ = v_a_6346_;
v___y_6353_ = v_a_6347_;
v___y_6354_ = v_a_6348_;
goto v___jp_6350_;
}
else
{
lean_object* v___x_6376_; lean_object* v___x_6377_; uint8_t v___x_6378_; 
v___x_6376_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6374_);
v___x_6377_ = ((lean_object*)(l_Lean_Meta_mkOfEqTrueCore___closed__1));
v___x_6378_ = l_Lean_Expr_isConstOf(v___x_6376_, v___x_6377_);
lean_dec_ref(v___x_6376_);
if (v___x_6378_ == 0)
{
lean_dec_ref(v_arg_6373_);
lean_del_object(v___x_6369_);
v___y_6351_ = v_a_6345_;
v___y_6352_ = v_a_6346_;
v___y_6353_ = v_a_6347_;
v___y_6354_ = v_a_6348_;
goto v___jp_6350_;
}
else
{
lean_object* v___x_6380_; 
lean_dec_ref(v_h_6344_);
if (v_isShared_6370_ == 0)
{
lean_ctor_set(v___x_6369_, 0, v_arg_6373_);
v___x_6380_ = v___x_6369_;
goto v_reusejp_6379_;
}
else
{
lean_object* v_reuseFailAlloc_6381_; 
v_reuseFailAlloc_6381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6381_, 0, v_arg_6373_);
v___x_6380_ = v_reuseFailAlloc_6381_;
goto v_reusejp_6379_;
}
v_reusejp_6379_:
{
return v___x_6380_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_h_6344_);
return v___x_6366_;
}
v___jp_6350_:
{
lean_object* v___x_6355_; 
lean_inc(v___y_6354_);
lean_inc_ref(v___y_6353_);
lean_inc(v___y_6352_);
lean_inc_ref(v___y_6351_);
lean_inc_ref(v_h_6344_);
v___x_6355_ = lean_infer_type(v_h_6344_, v___y_6351_, v___y_6352_, v___y_6353_, v___y_6354_);
if (lean_obj_tag(v___x_6355_) == 0)
{
lean_object* v_a_6356_; lean_object* v___x_6358_; uint8_t v_isShared_6359_; uint8_t v_isSharedCheck_6365_; 
v_a_6356_ = lean_ctor_get(v___x_6355_, 0);
v_isSharedCheck_6365_ = !lean_is_exclusive(v___x_6355_);
if (v_isSharedCheck_6365_ == 0)
{
v___x_6358_ = v___x_6355_;
v_isShared_6359_ = v_isSharedCheck_6365_;
goto v_resetjp_6357_;
}
else
{
lean_inc(v_a_6356_);
lean_dec(v___x_6355_);
v___x_6358_ = lean_box(0);
v_isShared_6359_ = v_isSharedCheck_6365_;
goto v_resetjp_6357_;
}
v_resetjp_6357_:
{
lean_object* v___x_6360_; lean_object* v___x_6361_; lean_object* v___x_6363_; 
v___x_6360_ = lean_obj_once(&l_Lean_Meta_mkEqTrueCore___closed__0, &l_Lean_Meta_mkEqTrueCore___closed__0_once, _init_l_Lean_Meta_mkEqTrueCore___closed__0);
v___x_6361_ = l_Lean_mkAppB(v___x_6360_, v_a_6356_, v_h_6344_);
if (v_isShared_6359_ == 0)
{
lean_ctor_set(v___x_6358_, 0, v___x_6361_);
v___x_6363_ = v___x_6358_;
goto v_reusejp_6362_;
}
else
{
lean_object* v_reuseFailAlloc_6364_; 
v_reuseFailAlloc_6364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6364_, 0, v___x_6361_);
v___x_6363_ = v_reuseFailAlloc_6364_;
goto v_reusejp_6362_;
}
v_reusejp_6362_:
{
return v___x_6363_;
}
}
}
else
{
lean_dec_ref(v_h_6344_);
return v___x_6355_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqTrue___boxed(lean_object* v_h_6383_, lean_object* v_a_6384_, lean_object* v_a_6385_, lean_object* v_a_6386_, lean_object* v_a_6387_, lean_object* v_a_6388_){
_start:
{
lean_object* v_res_6389_; 
v_res_6389_ = l_Lean_Meta_mkEqTrue(v_h_6383_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_);
lean_dec(v_a_6387_);
lean_dec_ref(v_a_6386_);
lean_dec(v_a_6385_);
lean_dec_ref(v_a_6384_);
return v_res_6389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse(lean_object* v_h_6390_, lean_object* v_a_6391_, lean_object* v_a_6392_, lean_object* v_a_6393_, lean_object* v_a_6394_){
_start:
{
lean_object* v___y_6397_; lean_object* v___y_6398_; lean_object* v___y_6399_; lean_object* v___y_6400_; lean_object* v___x_6406_; uint8_t v___x_6407_; 
lean_inc_ref(v_h_6390_);
v___x_6406_ = l_Lean_Expr_cleanupAnnotations(v_h_6390_);
v___x_6407_ = l_Lean_Expr_isApp(v___x_6406_);
if (v___x_6407_ == 0)
{
lean_dec_ref(v___x_6406_);
v___y_6397_ = v_a_6391_;
v___y_6398_ = v_a_6392_;
v___y_6399_ = v_a_6393_;
v___y_6400_ = v_a_6394_;
goto v___jp_6396_;
}
else
{
lean_object* v_arg_6408_; lean_object* v___x_6409_; uint8_t v___x_6410_; 
v_arg_6408_ = lean_ctor_get(v___x_6406_, 1);
lean_inc_ref(v_arg_6408_);
v___x_6409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6406_);
v___x_6410_ = l_Lean_Expr_isApp(v___x_6409_);
if (v___x_6410_ == 0)
{
lean_dec_ref(v___x_6409_);
lean_dec_ref(v_arg_6408_);
v___y_6397_ = v_a_6391_;
v___y_6398_ = v_a_6392_;
v___y_6399_ = v_a_6393_;
v___y_6400_ = v_a_6394_;
goto v___jp_6396_;
}
else
{
lean_object* v___x_6411_; lean_object* v___x_6412_; uint8_t v___x_6413_; 
v___x_6411_ = l_Lean_Expr_appFnCleanup___redArg(v___x_6409_);
v___x_6412_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__1));
v___x_6413_ = l_Lean_Expr_isConstOf(v___x_6411_, v___x_6412_);
lean_dec_ref(v___x_6411_);
if (v___x_6413_ == 0)
{
lean_dec_ref(v_arg_6408_);
v___y_6397_ = v_a_6391_;
v___y_6398_ = v_a_6392_;
v___y_6399_ = v_a_6393_;
v___y_6400_ = v_a_6394_;
goto v___jp_6396_;
}
else
{
lean_object* v___x_6414_; 
lean_dec_ref(v_h_6390_);
v___x_6414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6414_, 0, v_arg_6408_);
return v___x_6414_;
}
}
}
v___jp_6396_:
{
lean_object* v___x_6401_; lean_object* v___x_6402_; lean_object* v___x_6403_; lean_object* v___x_6404_; lean_object* v___x_6405_; 
v___x_6401_ = ((lean_object*)(l_Lean_Meta_mkOfEqFalseCore___closed__4));
v___x_6402_ = lean_unsigned_to_nat(1u);
v___x_6403_ = lean_mk_empty_array_with_capacity(v___x_6402_);
v___x_6404_ = lean_array_push(v___x_6403_, v_h_6390_);
v___x_6405_ = l_Lean_Meta_mkAppM(v___x_6401_, v___x_6404_, v___y_6397_, v___y_6398_, v___y_6399_, v___y_6400_);
return v___x_6405_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse___boxed(lean_object* v_h_6415_, lean_object* v_a_6416_, lean_object* v_a_6417_, lean_object* v_a_6418_, lean_object* v_a_6419_, lean_object* v_a_6420_){
_start:
{
lean_object* v_res_6421_; 
v_res_6421_ = l_Lean_Meta_mkEqFalse(v_h_6415_, v_a_6416_, v_a_6417_, v_a_6418_, v_a_6419_);
lean_dec(v_a_6419_);
lean_dec_ref(v_a_6418_);
lean_dec(v_a_6417_);
lean_dec_ref(v_a_6416_);
return v_res_6421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27(lean_object* v_h_6425_, lean_object* v_a_6426_, lean_object* v_a_6427_, lean_object* v_a_6428_, lean_object* v_a_6429_){
_start:
{
lean_object* v___x_6431_; lean_object* v___x_6432_; lean_object* v___x_6433_; lean_object* v___x_6434_; lean_object* v___x_6435_; 
v___x_6431_ = ((lean_object*)(l_Lean_Meta_mkEqFalse_x27___closed__1));
v___x_6432_ = lean_unsigned_to_nat(1u);
v___x_6433_ = lean_mk_empty_array_with_capacity(v___x_6432_);
v___x_6434_ = lean_array_push(v___x_6433_, v_h_6425_);
v___x_6435_ = l_Lean_Meta_mkAppM(v___x_6431_, v___x_6434_, v_a_6426_, v_a_6427_, v_a_6428_, v_a_6429_);
return v___x_6435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkEqFalse_x27___boxed(lean_object* v_h_6436_, lean_object* v_a_6437_, lean_object* v_a_6438_, lean_object* v_a_6439_, lean_object* v_a_6440_, lean_object* v_a_6441_){
_start:
{
lean_object* v_res_6442_; 
v_res_6442_ = l_Lean_Meta_mkEqFalse_x27(v_h_6436_, v_a_6437_, v_a_6438_, v_a_6439_, v_a_6440_);
lean_dec(v_a_6440_);
lean_dec_ref(v_a_6439_);
lean_dec(v_a_6438_);
lean_dec_ref(v_a_6437_);
return v_res_6442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr(lean_object* v_h_u2081_6446_, lean_object* v_h_u2082_6447_, lean_object* v_a_6448_, lean_object* v_a_6449_, lean_object* v_a_6450_, lean_object* v_a_6451_){
_start:
{
lean_object* v___x_6453_; lean_object* v___x_6454_; lean_object* v___x_6455_; lean_object* v___x_6456_; lean_object* v___x_6457_; lean_object* v___x_6458_; 
v___x_6453_ = ((lean_object*)(l_Lean_Meta_mkImpCongr___closed__1));
v___x_6454_ = lean_unsigned_to_nat(2u);
v___x_6455_ = lean_mk_empty_array_with_capacity(v___x_6454_);
v___x_6456_ = lean_array_push(v___x_6455_, v_h_u2081_6446_);
v___x_6457_ = lean_array_push(v___x_6456_, v_h_u2082_6447_);
v___x_6458_ = l_Lean_Meta_mkAppM(v___x_6453_, v___x_6457_, v_a_6448_, v_a_6449_, v_a_6450_, v_a_6451_);
return v___x_6458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongr___boxed(lean_object* v_h_u2081_6459_, lean_object* v_h_u2082_6460_, lean_object* v_a_6461_, lean_object* v_a_6462_, lean_object* v_a_6463_, lean_object* v_a_6464_, lean_object* v_a_6465_){
_start:
{
lean_object* v_res_6466_; 
v_res_6466_ = l_Lean_Meta_mkImpCongr(v_h_u2081_6459_, v_h_u2082_6460_, v_a_6461_, v_a_6462_, v_a_6463_, v_a_6464_);
lean_dec(v_a_6464_);
lean_dec_ref(v_a_6463_);
lean_dec(v_a_6462_);
lean_dec_ref(v_a_6461_);
return v_res_6466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx(lean_object* v_h_u2081_6470_, lean_object* v_h_u2082_6471_, lean_object* v_a_6472_, lean_object* v_a_6473_, lean_object* v_a_6474_, lean_object* v_a_6475_){
_start:
{
lean_object* v___x_6477_; lean_object* v___x_6478_; lean_object* v___x_6479_; lean_object* v___x_6480_; lean_object* v___x_6481_; lean_object* v___x_6482_; 
v___x_6477_ = ((lean_object*)(l_Lean_Meta_mkImpCongrCtx___closed__1));
v___x_6478_ = lean_unsigned_to_nat(2u);
v___x_6479_ = lean_mk_empty_array_with_capacity(v___x_6478_);
v___x_6480_ = lean_array_push(v___x_6479_, v_h_u2081_6470_);
v___x_6481_ = lean_array_push(v___x_6480_, v_h_u2082_6471_);
v___x_6482_ = l_Lean_Meta_mkAppM(v___x_6477_, v___x_6481_, v_a_6472_, v_a_6473_, v_a_6474_, v_a_6475_);
return v___x_6482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpCongrCtx___boxed(lean_object* v_h_u2081_6483_, lean_object* v_h_u2082_6484_, lean_object* v_a_6485_, lean_object* v_a_6486_, lean_object* v_a_6487_, lean_object* v_a_6488_, lean_object* v_a_6489_){
_start:
{
lean_object* v_res_6490_; 
v_res_6490_ = l_Lean_Meta_mkImpCongrCtx(v_h_u2081_6483_, v_h_u2082_6484_, v_a_6485_, v_a_6486_, v_a_6487_, v_a_6488_);
lean_dec(v_a_6488_);
lean_dec_ref(v_a_6487_);
lean_dec(v_a_6486_);
lean_dec_ref(v_a_6485_);
return v_res_6490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx(lean_object* v_h_u2081_6494_, lean_object* v_h_u2082_6495_, lean_object* v_a_6496_, lean_object* v_a_6497_, lean_object* v_a_6498_, lean_object* v_a_6499_){
_start:
{
lean_object* v___x_6501_; lean_object* v___x_6502_; lean_object* v___x_6503_; lean_object* v___x_6504_; lean_object* v___x_6505_; lean_object* v___x_6506_; 
v___x_6501_ = ((lean_object*)(l_Lean_Meta_mkImpDepCongrCtx___closed__1));
v___x_6502_ = lean_unsigned_to_nat(2u);
v___x_6503_ = lean_mk_empty_array_with_capacity(v___x_6502_);
v___x_6504_ = lean_array_push(v___x_6503_, v_h_u2081_6494_);
v___x_6505_ = lean_array_push(v___x_6504_, v_h_u2082_6495_);
v___x_6506_ = l_Lean_Meta_mkAppM(v___x_6501_, v___x_6505_, v_a_6496_, v_a_6497_, v_a_6498_, v_a_6499_);
return v___x_6506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkImpDepCongrCtx___boxed(lean_object* v_h_u2081_6507_, lean_object* v_h_u2082_6508_, lean_object* v_a_6509_, lean_object* v_a_6510_, lean_object* v_a_6511_, lean_object* v_a_6512_, lean_object* v_a_6513_){
_start:
{
lean_object* v_res_6514_; 
v_res_6514_ = l_Lean_Meta_mkImpDepCongrCtx(v_h_u2081_6507_, v_h_u2082_6508_, v_a_6509_, v_a_6510_, v_a_6511_, v_a_6512_);
lean_dec(v_a_6512_);
lean_dec_ref(v_a_6511_);
lean_dec(v_a_6510_);
lean_dec_ref(v_a_6509_);
return v_res_6514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr(lean_object* v_h_6518_, lean_object* v_a_6519_, lean_object* v_a_6520_, lean_object* v_a_6521_, lean_object* v_a_6522_){
_start:
{
lean_object* v___x_6524_; lean_object* v___x_6525_; lean_object* v___x_6526_; lean_object* v___x_6527_; lean_object* v___x_6528_; 
v___x_6524_ = ((lean_object*)(l_Lean_Meta_mkForallCongr___closed__1));
v___x_6525_ = lean_unsigned_to_nat(1u);
v___x_6526_ = lean_mk_empty_array_with_capacity(v___x_6525_);
v___x_6527_ = lean_array_push(v___x_6526_, v_h_6518_);
v___x_6528_ = l_Lean_Meta_mkAppM(v___x_6524_, v___x_6527_, v_a_6519_, v_a_6520_, v_a_6521_, v_a_6522_);
return v___x_6528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkForallCongr___boxed(lean_object* v_h_6529_, lean_object* v_a_6530_, lean_object* v_a_6531_, lean_object* v_a_6532_, lean_object* v_a_6533_, lean_object* v_a_6534_){
_start:
{
lean_object* v_res_6535_; 
v_res_6535_ = l_Lean_Meta_mkForallCongr(v_h_6529_, v_a_6530_, v_a_6531_, v_a_6532_, v_a_6533_);
lean_dec(v_a_6533_);
lean_dec_ref(v_a_6532_);
lean_dec(v_a_6531_);
lean_dec_ref(v_a_6530_);
return v_res_6535_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f(lean_object* v_m_6539_, lean_object* v_a_6540_, lean_object* v_a_6541_, lean_object* v_a_6542_, lean_object* v_a_6543_){
_start:
{
lean_object* v___y_6546_; uint8_t v___y_6547_; lean_object* v___y_6551_; lean_object* v_a_6552_; lean_object* v___x_6555_; lean_object* v___x_6556_; lean_object* v___x_6557_; lean_object* v___x_6558_; lean_object* v___x_6559_; 
v___x_6555_ = ((lean_object*)(l_Lean_Meta_isMonad_x3f___closed__1));
v___x_6556_ = lean_unsigned_to_nat(1u);
v___x_6557_ = lean_mk_empty_array_with_capacity(v___x_6556_);
v___x_6558_ = lean_array_push(v___x_6557_, v_m_6539_);
v___x_6559_ = l_Lean_Meta_mkAppM(v___x_6555_, v___x_6558_, v_a_6540_, v_a_6541_, v_a_6542_, v_a_6543_);
if (lean_obj_tag(v___x_6559_) == 0)
{
lean_object* v_a_6560_; lean_object* v___x_6561_; lean_object* v___x_6562_; 
v_a_6560_ = lean_ctor_get(v___x_6559_, 0);
lean_inc(v_a_6560_);
lean_dec_ref_known(v___x_6559_, 1);
v___x_6561_ = lean_box(0);
v___x_6562_ = l_Lean_Meta_trySynthInstance(v_a_6560_, v___x_6561_, v_a_6540_, v_a_6541_, v_a_6542_, v_a_6543_);
if (lean_obj_tag(v___x_6562_) == 0)
{
lean_object* v_a_6563_; lean_object* v___x_6565_; uint8_t v_isShared_6566_; uint8_t v_isSharedCheck_6581_; 
v_a_6563_ = lean_ctor_get(v___x_6562_, 0);
v_isSharedCheck_6581_ = !lean_is_exclusive(v___x_6562_);
if (v_isSharedCheck_6581_ == 0)
{
v___x_6565_ = v___x_6562_;
v_isShared_6566_ = v_isSharedCheck_6581_;
goto v_resetjp_6564_;
}
else
{
lean_inc(v_a_6563_);
lean_dec(v___x_6562_);
v___x_6565_ = lean_box(0);
v_isShared_6566_ = v_isSharedCheck_6581_;
goto v_resetjp_6564_;
}
v_resetjp_6564_:
{
if (lean_obj_tag(v_a_6563_) == 1)
{
lean_object* v_a_6567_; lean_object* v___x_6569_; uint8_t v_isShared_6570_; uint8_t v_isSharedCheck_6577_; 
v_a_6567_ = lean_ctor_get(v_a_6563_, 0);
v_isSharedCheck_6577_ = !lean_is_exclusive(v_a_6563_);
if (v_isSharedCheck_6577_ == 0)
{
v___x_6569_ = v_a_6563_;
v_isShared_6570_ = v_isSharedCheck_6577_;
goto v_resetjp_6568_;
}
else
{
lean_inc(v_a_6567_);
lean_dec(v_a_6563_);
v___x_6569_ = lean_box(0);
v_isShared_6570_ = v_isSharedCheck_6577_;
goto v_resetjp_6568_;
}
v_resetjp_6568_:
{
lean_object* v___x_6572_; 
if (v_isShared_6570_ == 0)
{
v___x_6572_ = v___x_6569_;
goto v_reusejp_6571_;
}
else
{
lean_object* v_reuseFailAlloc_6576_; 
v_reuseFailAlloc_6576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6576_, 0, v_a_6567_);
v___x_6572_ = v_reuseFailAlloc_6576_;
goto v_reusejp_6571_;
}
v_reusejp_6571_:
{
lean_object* v___x_6574_; 
if (v_isShared_6566_ == 0)
{
lean_ctor_set(v___x_6565_, 0, v___x_6572_);
v___x_6574_ = v___x_6565_;
goto v_reusejp_6573_;
}
else
{
lean_object* v_reuseFailAlloc_6575_; 
v_reuseFailAlloc_6575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6575_, 0, v___x_6572_);
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
else
{
lean_object* v___x_6579_; 
lean_dec(v_a_6563_);
if (v_isShared_6566_ == 0)
{
lean_ctor_set(v___x_6565_, 0, v___x_6561_);
v___x_6579_ = v___x_6565_;
goto v_reusejp_6578_;
}
else
{
lean_object* v_reuseFailAlloc_6580_; 
v_reuseFailAlloc_6580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6580_, 0, v___x_6561_);
v___x_6579_ = v_reuseFailAlloc_6580_;
goto v_reusejp_6578_;
}
v_reusejp_6578_:
{
return v___x_6579_;
}
}
}
}
else
{
lean_object* v_a_6582_; lean_object* v___x_6584_; uint8_t v_isShared_6585_; uint8_t v_isSharedCheck_6589_; 
v_a_6582_ = lean_ctor_get(v___x_6562_, 0);
v_isSharedCheck_6589_ = !lean_is_exclusive(v___x_6562_);
if (v_isSharedCheck_6589_ == 0)
{
v___x_6584_ = v___x_6562_;
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
else
{
lean_inc(v_a_6582_);
lean_dec(v___x_6562_);
v___x_6584_ = lean_box(0);
v_isShared_6585_ = v_isSharedCheck_6589_;
goto v_resetjp_6583_;
}
v_resetjp_6583_:
{
lean_object* v___x_6587_; 
lean_inc(v_a_6582_);
if (v_isShared_6585_ == 0)
{
v___x_6587_ = v___x_6584_;
goto v_reusejp_6586_;
}
else
{
lean_object* v_reuseFailAlloc_6588_; 
v_reuseFailAlloc_6588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6588_, 0, v_a_6582_);
v___x_6587_ = v_reuseFailAlloc_6588_;
goto v_reusejp_6586_;
}
v_reusejp_6586_:
{
v___y_6551_ = v___x_6587_;
v_a_6552_ = v_a_6582_;
goto v___jp_6550_;
}
}
}
}
else
{
lean_object* v_a_6590_; lean_object* v___x_6592_; uint8_t v_isShared_6593_; uint8_t v_isSharedCheck_6597_; 
v_a_6590_ = lean_ctor_get(v___x_6559_, 0);
v_isSharedCheck_6597_ = !lean_is_exclusive(v___x_6559_);
if (v_isSharedCheck_6597_ == 0)
{
v___x_6592_ = v___x_6559_;
v_isShared_6593_ = v_isSharedCheck_6597_;
goto v_resetjp_6591_;
}
else
{
lean_inc(v_a_6590_);
lean_dec(v___x_6559_);
v___x_6592_ = lean_box(0);
v_isShared_6593_ = v_isSharedCheck_6597_;
goto v_resetjp_6591_;
}
v_resetjp_6591_:
{
lean_object* v___x_6595_; 
lean_inc(v_a_6590_);
if (v_isShared_6593_ == 0)
{
v___x_6595_ = v___x_6592_;
goto v_reusejp_6594_;
}
else
{
lean_object* v_reuseFailAlloc_6596_; 
v_reuseFailAlloc_6596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6596_, 0, v_a_6590_);
v___x_6595_ = v_reuseFailAlloc_6596_;
goto v_reusejp_6594_;
}
v_reusejp_6594_:
{
v___y_6551_ = v___x_6595_;
v_a_6552_ = v_a_6590_;
goto v___jp_6550_;
}
}
}
v___jp_6545_:
{
if (v___y_6547_ == 0)
{
lean_object* v___x_6548_; lean_object* v___x_6549_; 
lean_dec_ref(v___y_6546_);
v___x_6548_ = lean_box(0);
v___x_6549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6549_, 0, v___x_6548_);
return v___x_6549_;
}
else
{
return v___y_6546_;
}
}
v___jp_6550_:
{
uint8_t v___x_6553_; 
v___x_6553_ = l_Lean_Exception_isInterrupt(v_a_6552_);
if (v___x_6553_ == 0)
{
uint8_t v___x_6554_; 
v___x_6554_ = l_Lean_Exception_isRuntime(v_a_6552_);
v___y_6546_ = v___y_6551_;
v___y_6547_ = v___x_6554_;
goto v___jp_6545_;
}
else
{
lean_dec_ref(v_a_6552_);
v___y_6546_ = v___y_6551_;
v___y_6547_ = v___x_6553_;
goto v___jp_6545_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isMonad_x3f___boxed(lean_object* v_m_6598_, lean_object* v_a_6599_, lean_object* v_a_6600_, lean_object* v_a_6601_, lean_object* v_a_6602_, lean_object* v_a_6603_){
_start:
{
lean_object* v_res_6604_; 
v_res_6604_ = l_Lean_Meta_isMonad_x3f(v_m_6598_, v_a_6599_, v_a_6600_, v_a_6601_, v_a_6602_);
lean_dec(v_a_6602_);
lean_dec_ref(v_a_6601_);
lean_dec(v_a_6600_);
lean_dec_ref(v_a_6599_);
return v_res_6604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral(lean_object* v_type_6612_, lean_object* v_n_6613_, lean_object* v_a_6614_, lean_object* v_a_6615_, lean_object* v_a_6616_, lean_object* v_a_6617_){
_start:
{
lean_object* v___x_6619_; 
lean_inc_ref(v_type_6612_);
v___x_6619_ = l_Lean_Meta_getDecLevel(v_type_6612_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_);
if (lean_obj_tag(v___x_6619_) == 0)
{
lean_object* v_a_6620_; lean_object* v___x_6621_; lean_object* v___x_6622_; lean_object* v___x_6623_; lean_object* v___x_6624_; lean_object* v___x_6625_; lean_object* v___x_6626_; lean_object* v___x_6627_; lean_object* v___x_6628_; 
v_a_6620_ = lean_ctor_get(v___x_6619_, 0);
lean_inc(v_a_6620_);
lean_dec_ref_known(v___x_6619_, 1);
v___x_6621_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__1));
v___x_6622_ = lean_box(0);
v___x_6623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6623_, 0, v_a_6620_);
lean_ctor_set(v___x_6623_, 1, v___x_6622_);
lean_inc_ref(v___x_6623_);
v___x_6624_ = l_Lean_mkConst(v___x_6621_, v___x_6623_);
v___x_6625_ = l_Lean_mkRawNatLit(v_n_6613_);
lean_inc_ref(v___x_6625_);
lean_inc_ref(v_type_6612_);
v___x_6626_ = l_Lean_mkAppB(v___x_6624_, v_type_6612_, v___x_6625_);
v___x_6627_ = lean_box(0);
v___x_6628_ = l_Lean_Meta_synthInstance(v___x_6626_, v___x_6627_, v_a_6614_, v_a_6615_, v_a_6616_, v_a_6617_);
if (lean_obj_tag(v___x_6628_) == 0)
{
lean_object* v_a_6629_; lean_object* v___x_6631_; uint8_t v_isShared_6632_; uint8_t v_isSharedCheck_6639_; 
v_a_6629_ = lean_ctor_get(v___x_6628_, 0);
v_isSharedCheck_6639_ = !lean_is_exclusive(v___x_6628_);
if (v_isSharedCheck_6639_ == 0)
{
v___x_6631_ = v___x_6628_;
v_isShared_6632_ = v_isSharedCheck_6639_;
goto v_resetjp_6630_;
}
else
{
lean_inc(v_a_6629_);
lean_dec(v___x_6628_);
v___x_6631_ = lean_box(0);
v_isShared_6632_ = v_isSharedCheck_6639_;
goto v_resetjp_6630_;
}
v_resetjp_6630_:
{
lean_object* v___x_6633_; lean_object* v___x_6634_; lean_object* v___x_6635_; lean_object* v___x_6637_; 
v___x_6633_ = ((lean_object*)(l_Lean_Meta_mkNumeral___closed__3));
v___x_6634_ = l_Lean_mkConst(v___x_6633_, v___x_6623_);
v___x_6635_ = l_Lean_mkApp3(v___x_6634_, v_type_6612_, v___x_6625_, v_a_6629_);
if (v_isShared_6632_ == 0)
{
lean_ctor_set(v___x_6631_, 0, v___x_6635_);
v___x_6637_ = v___x_6631_;
goto v_reusejp_6636_;
}
else
{
lean_object* v_reuseFailAlloc_6638_; 
v_reuseFailAlloc_6638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6638_, 0, v___x_6635_);
v___x_6637_ = v_reuseFailAlloc_6638_;
goto v_reusejp_6636_;
}
v_reusejp_6636_:
{
return v___x_6637_;
}
}
}
else
{
lean_dec_ref(v___x_6625_);
lean_dec_ref_known(v___x_6623_, 2);
lean_dec_ref(v_type_6612_);
return v___x_6628_;
}
}
else
{
lean_object* v_a_6640_; lean_object* v___x_6642_; uint8_t v_isShared_6643_; uint8_t v_isSharedCheck_6647_; 
lean_dec(v_n_6613_);
lean_dec_ref(v_type_6612_);
v_a_6640_ = lean_ctor_get(v___x_6619_, 0);
v_isSharedCheck_6647_ = !lean_is_exclusive(v___x_6619_);
if (v_isSharedCheck_6647_ == 0)
{
v___x_6642_ = v___x_6619_;
v_isShared_6643_ = v_isSharedCheck_6647_;
goto v_resetjp_6641_;
}
else
{
lean_inc(v_a_6640_);
lean_dec(v___x_6619_);
v___x_6642_ = lean_box(0);
v_isShared_6643_ = v_isSharedCheck_6647_;
goto v_resetjp_6641_;
}
v_resetjp_6641_:
{
lean_object* v___x_6645_; 
if (v_isShared_6643_ == 0)
{
v___x_6645_ = v___x_6642_;
goto v_reusejp_6644_;
}
else
{
lean_object* v_reuseFailAlloc_6646_; 
v_reuseFailAlloc_6646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6646_, 0, v_a_6640_);
v___x_6645_ = v_reuseFailAlloc_6646_;
goto v_reusejp_6644_;
}
v_reusejp_6644_:
{
return v___x_6645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkNumeral___boxed(lean_object* v_type_6648_, lean_object* v_n_6649_, lean_object* v_a_6650_, lean_object* v_a_6651_, lean_object* v_a_6652_, lean_object* v_a_6653_, lean_object* v_a_6654_){
_start:
{
lean_object* v_res_6655_; 
v_res_6655_ = l_Lean_Meta_mkNumeral(v_type_6648_, v_n_6649_, v_a_6650_, v_a_6651_, v_a_6652_, v_a_6653_);
lean_dec(v_a_6653_);
lean_dec_ref(v_a_6652_);
lean_dec(v_a_6651_);
lean_dec_ref(v_a_6650_);
return v_res_6655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(lean_object* v_className_6656_, lean_object* v_opName_6657_, lean_object* v_a_6658_, lean_object* v_b_6659_, lean_object* v_a_6660_, lean_object* v_a_6661_, lean_object* v_a_6662_, lean_object* v_a_6663_){
_start:
{
lean_object* v___x_6665_; 
lean_inc(v_a_6663_);
lean_inc_ref(v_a_6662_);
lean_inc(v_a_6661_);
lean_inc_ref(v_a_6660_);
lean_inc_ref(v_a_6658_);
v___x_6665_ = lean_infer_type(v_a_6658_, v_a_6660_, v_a_6661_, v_a_6662_, v_a_6663_);
if (lean_obj_tag(v___x_6665_) == 0)
{
lean_object* v_a_6666_; lean_object* v___x_6667_; 
v_a_6666_ = lean_ctor_get(v___x_6665_, 0);
lean_inc_n(v_a_6666_, 2);
lean_dec_ref_known(v___x_6665_, 1);
v___x_6667_ = l_Lean_Meta_getDecLevel(v_a_6666_, v_a_6660_, v_a_6661_, v_a_6662_, v_a_6663_);
if (lean_obj_tag(v___x_6667_) == 0)
{
lean_object* v_a_6668_; lean_object* v___x_6669_; lean_object* v___x_6670_; lean_object* v___x_6671_; lean_object* v___x_6672_; lean_object* v___x_6673_; lean_object* v___x_6674_; lean_object* v___x_6675_; lean_object* v___x_6676_; 
v_a_6668_ = lean_ctor_get(v___x_6667_, 0);
lean_inc_n(v_a_6668_, 3);
lean_dec_ref_known(v___x_6667_, 1);
v___x_6669_ = lean_box(0);
v___x_6670_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6670_, 0, v_a_6668_);
lean_ctor_set(v___x_6670_, 1, v___x_6669_);
v___x_6671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6671_, 0, v_a_6668_);
lean_ctor_set(v___x_6671_, 1, v___x_6670_);
v___x_6672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6672_, 0, v_a_6668_);
lean_ctor_set(v___x_6672_, 1, v___x_6671_);
lean_inc_ref(v___x_6672_);
v___x_6673_ = l_Lean_mkConst(v_className_6656_, v___x_6672_);
lean_inc_n(v_a_6666_, 3);
v___x_6674_ = l_Lean_mkApp3(v___x_6673_, v_a_6666_, v_a_6666_, v_a_6666_);
v___x_6675_ = lean_box(0);
v___x_6676_ = l_Lean_Meta_synthInstance(v___x_6674_, v___x_6675_, v_a_6660_, v_a_6661_, v_a_6662_, v_a_6663_);
if (lean_obj_tag(v___x_6676_) == 0)
{
lean_object* v_a_6677_; lean_object* v___x_6679_; uint8_t v_isShared_6680_; uint8_t v_isSharedCheck_6686_; 
v_a_6677_ = lean_ctor_get(v___x_6676_, 0);
v_isSharedCheck_6686_ = !lean_is_exclusive(v___x_6676_);
if (v_isSharedCheck_6686_ == 0)
{
v___x_6679_ = v___x_6676_;
v_isShared_6680_ = v_isSharedCheck_6686_;
goto v_resetjp_6678_;
}
else
{
lean_inc(v_a_6677_);
lean_dec(v___x_6676_);
v___x_6679_ = lean_box(0);
v_isShared_6680_ = v_isSharedCheck_6686_;
goto v_resetjp_6678_;
}
v_resetjp_6678_:
{
lean_object* v___x_6681_; lean_object* v___x_6682_; lean_object* v___x_6684_; 
v___x_6681_ = l_Lean_mkConst(v_opName_6657_, v___x_6672_);
lean_inc_n(v_a_6666_, 2);
v___x_6682_ = l_Lean_mkApp6(v___x_6681_, v_a_6666_, v_a_6666_, v_a_6666_, v_a_6677_, v_a_6658_, v_b_6659_);
if (v_isShared_6680_ == 0)
{
lean_ctor_set(v___x_6679_, 0, v___x_6682_);
v___x_6684_ = v___x_6679_;
goto v_reusejp_6683_;
}
else
{
lean_object* v_reuseFailAlloc_6685_; 
v_reuseFailAlloc_6685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6685_, 0, v___x_6682_);
v___x_6684_ = v_reuseFailAlloc_6685_;
goto v_reusejp_6683_;
}
v_reusejp_6683_:
{
return v___x_6684_;
}
}
}
else
{
lean_dec_ref_known(v___x_6672_, 2);
lean_dec(v_a_6666_);
lean_dec_ref(v_b_6659_);
lean_dec_ref(v_a_6658_);
lean_dec(v_opName_6657_);
return v___x_6676_;
}
}
else
{
lean_object* v_a_6687_; lean_object* v___x_6689_; uint8_t v_isShared_6690_; uint8_t v_isSharedCheck_6694_; 
lean_dec(v_a_6666_);
lean_dec_ref(v_b_6659_);
lean_dec_ref(v_a_6658_);
lean_dec(v_opName_6657_);
lean_dec(v_className_6656_);
v_a_6687_ = lean_ctor_get(v___x_6667_, 0);
v_isSharedCheck_6694_ = !lean_is_exclusive(v___x_6667_);
if (v_isSharedCheck_6694_ == 0)
{
v___x_6689_ = v___x_6667_;
v_isShared_6690_ = v_isSharedCheck_6694_;
goto v_resetjp_6688_;
}
else
{
lean_inc(v_a_6687_);
lean_dec(v___x_6667_);
v___x_6689_ = lean_box(0);
v_isShared_6690_ = v_isSharedCheck_6694_;
goto v_resetjp_6688_;
}
v_resetjp_6688_:
{
lean_object* v___x_6692_; 
if (v_isShared_6690_ == 0)
{
v___x_6692_ = v___x_6689_;
goto v_reusejp_6691_;
}
else
{
lean_object* v_reuseFailAlloc_6693_; 
v_reuseFailAlloc_6693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6693_, 0, v_a_6687_);
v___x_6692_ = v_reuseFailAlloc_6693_;
goto v_reusejp_6691_;
}
v_reusejp_6691_:
{
return v___x_6692_;
}
}
}
}
else
{
lean_dec_ref(v_b_6659_);
lean_dec_ref(v_a_6658_);
lean_dec(v_opName_6657_);
lean_dec(v_className_6656_);
return v___x_6665_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp___boxed(lean_object* v_className_6695_, lean_object* v_opName_6696_, lean_object* v_a_6697_, lean_object* v_b_6698_, lean_object* v_a_6699_, lean_object* v_a_6700_, lean_object* v_a_6701_, lean_object* v_a_6702_, lean_object* v_a_6703_){
_start:
{
lean_object* v_res_6704_; 
v_res_6704_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v_className_6695_, v_opName_6696_, v_a_6697_, v_b_6698_, v_a_6699_, v_a_6700_, v_a_6701_, v_a_6702_);
lean_dec(v_a_6702_);
lean_dec_ref(v_a_6701_);
lean_dec(v_a_6700_);
lean_dec_ref(v_a_6699_);
return v_res_6704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd(lean_object* v_a_6712_, lean_object* v_b_6713_, lean_object* v_a_6714_, lean_object* v_a_6715_, lean_object* v_a_6716_, lean_object* v_a_6717_){
_start:
{
lean_object* v___x_6719_; lean_object* v___x_6720_; lean_object* v___x_6721_; 
v___x_6719_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__1));
v___x_6720_ = ((lean_object*)(l_Lean_Meta_mkAdd___closed__3));
v___x_6721_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6719_, v___x_6720_, v_a_6712_, v_b_6713_, v_a_6714_, v_a_6715_, v_a_6716_, v_a_6717_);
return v___x_6721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAdd___boxed(lean_object* v_a_6722_, lean_object* v_b_6723_, lean_object* v_a_6724_, lean_object* v_a_6725_, lean_object* v_a_6726_, lean_object* v_a_6727_, lean_object* v_a_6728_){
_start:
{
lean_object* v_res_6729_; 
v_res_6729_ = l_Lean_Meta_mkAdd(v_a_6722_, v_b_6723_, v_a_6724_, v_a_6725_, v_a_6726_, v_a_6727_);
lean_dec(v_a_6727_);
lean_dec_ref(v_a_6726_);
lean_dec(v_a_6725_);
lean_dec_ref(v_a_6724_);
return v_res_6729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub(lean_object* v_a_6737_, lean_object* v_b_6738_, lean_object* v_a_6739_, lean_object* v_a_6740_, lean_object* v_a_6741_, lean_object* v_a_6742_){
_start:
{
lean_object* v___x_6744_; lean_object* v___x_6745_; lean_object* v___x_6746_; 
v___x_6744_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__1));
v___x_6745_ = ((lean_object*)(l_Lean_Meta_mkSub___closed__3));
v___x_6746_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6744_, v___x_6745_, v_a_6737_, v_b_6738_, v_a_6739_, v_a_6740_, v_a_6741_, v_a_6742_);
return v___x_6746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSub___boxed(lean_object* v_a_6747_, lean_object* v_b_6748_, lean_object* v_a_6749_, lean_object* v_a_6750_, lean_object* v_a_6751_, lean_object* v_a_6752_, lean_object* v_a_6753_){
_start:
{
lean_object* v_res_6754_; 
v_res_6754_ = l_Lean_Meta_mkSub(v_a_6747_, v_b_6748_, v_a_6749_, v_a_6750_, v_a_6751_, v_a_6752_);
lean_dec(v_a_6752_);
lean_dec_ref(v_a_6751_);
lean_dec(v_a_6750_);
lean_dec_ref(v_a_6749_);
return v_res_6754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul(lean_object* v_a_6762_, lean_object* v_b_6763_, lean_object* v_a_6764_, lean_object* v_a_6765_, lean_object* v_a_6766_, lean_object* v_a_6767_){
_start:
{
lean_object* v___x_6769_; lean_object* v___x_6770_; lean_object* v___x_6771_; 
v___x_6769_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__1));
v___x_6770_ = ((lean_object*)(l_Lean_Meta_mkMul___closed__3));
v___x_6771_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryOp(v___x_6769_, v___x_6770_, v_a_6762_, v_b_6763_, v_a_6764_, v_a_6765_, v_a_6766_, v_a_6767_);
return v___x_6771_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkMul___boxed(lean_object* v_a_6772_, lean_object* v_b_6773_, lean_object* v_a_6774_, lean_object* v_a_6775_, lean_object* v_a_6776_, lean_object* v_a_6777_, lean_object* v_a_6778_){
_start:
{
lean_object* v_res_6779_; 
v_res_6779_ = l_Lean_Meta_mkMul(v_a_6772_, v_b_6773_, v_a_6774_, v_a_6775_, v_a_6776_, v_a_6777_);
lean_dec(v_a_6777_);
lean_dec_ref(v_a_6776_);
lean_dec(v_a_6775_);
lean_dec_ref(v_a_6774_);
return v_res_6779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(lean_object* v_className_6780_, lean_object* v_rName_6781_, lean_object* v_a_6782_, lean_object* v_b_6783_, lean_object* v_a_6784_, lean_object* v_a_6785_, lean_object* v_a_6786_, lean_object* v_a_6787_){
_start:
{
lean_object* v___x_6789_; 
lean_inc(v_a_6787_);
lean_inc_ref(v_a_6786_);
lean_inc(v_a_6785_);
lean_inc_ref(v_a_6784_);
lean_inc_ref(v_a_6782_);
v___x_6789_ = lean_infer_type(v_a_6782_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_);
if (lean_obj_tag(v___x_6789_) == 0)
{
lean_object* v_a_6790_; lean_object* v___x_6791_; 
v_a_6790_ = lean_ctor_get(v___x_6789_, 0);
lean_inc_n(v_a_6790_, 2);
lean_dec_ref_known(v___x_6789_, 1);
v___x_6791_ = l_Lean_Meta_getDecLevel(v_a_6790_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_);
if (lean_obj_tag(v___x_6791_) == 0)
{
lean_object* v_a_6792_; lean_object* v___x_6793_; lean_object* v___x_6794_; lean_object* v___x_6795_; lean_object* v___x_6796_; lean_object* v___x_6797_; lean_object* v___x_6798_; 
v_a_6792_ = lean_ctor_get(v___x_6791_, 0);
lean_inc(v_a_6792_);
lean_dec_ref_known(v___x_6791_, 1);
v___x_6793_ = lean_box(0);
v___x_6794_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_6794_, 0, v_a_6792_);
lean_ctor_set(v___x_6794_, 1, v___x_6793_);
lean_inc_ref(v___x_6794_);
v___x_6795_ = l_Lean_mkConst(v_className_6780_, v___x_6794_);
lean_inc(v_a_6790_);
v___x_6796_ = l_Lean_Expr_app___override(v___x_6795_, v_a_6790_);
v___x_6797_ = lean_box(0);
v___x_6798_ = l_Lean_Meta_synthInstance(v___x_6796_, v___x_6797_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_);
if (lean_obj_tag(v___x_6798_) == 0)
{
lean_object* v_a_6799_; lean_object* v___x_6801_; uint8_t v_isShared_6802_; uint8_t v_isSharedCheck_6808_; 
v_a_6799_ = lean_ctor_get(v___x_6798_, 0);
v_isSharedCheck_6808_ = !lean_is_exclusive(v___x_6798_);
if (v_isSharedCheck_6808_ == 0)
{
v___x_6801_ = v___x_6798_;
v_isShared_6802_ = v_isSharedCheck_6808_;
goto v_resetjp_6800_;
}
else
{
lean_inc(v_a_6799_);
lean_dec(v___x_6798_);
v___x_6801_ = lean_box(0);
v_isShared_6802_ = v_isSharedCheck_6808_;
goto v_resetjp_6800_;
}
v_resetjp_6800_:
{
lean_object* v___x_6803_; lean_object* v___x_6804_; lean_object* v___x_6806_; 
v___x_6803_ = l_Lean_mkConst(v_rName_6781_, v___x_6794_);
v___x_6804_ = l_Lean_mkApp4(v___x_6803_, v_a_6790_, v_a_6799_, v_a_6782_, v_b_6783_);
if (v_isShared_6802_ == 0)
{
lean_ctor_set(v___x_6801_, 0, v___x_6804_);
v___x_6806_ = v___x_6801_;
goto v_reusejp_6805_;
}
else
{
lean_object* v_reuseFailAlloc_6807_; 
v_reuseFailAlloc_6807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6807_, 0, v___x_6804_);
v___x_6806_ = v_reuseFailAlloc_6807_;
goto v_reusejp_6805_;
}
v_reusejp_6805_:
{
return v___x_6806_;
}
}
}
else
{
lean_dec_ref_known(v___x_6794_, 2);
lean_dec(v_a_6790_);
lean_dec_ref(v_b_6783_);
lean_dec_ref(v_a_6782_);
lean_dec(v_rName_6781_);
return v___x_6798_;
}
}
else
{
lean_object* v_a_6809_; lean_object* v___x_6811_; uint8_t v_isShared_6812_; uint8_t v_isSharedCheck_6816_; 
lean_dec(v_a_6790_);
lean_dec_ref(v_b_6783_);
lean_dec_ref(v_a_6782_);
lean_dec(v_rName_6781_);
lean_dec(v_className_6780_);
v_a_6809_ = lean_ctor_get(v___x_6791_, 0);
v_isSharedCheck_6816_ = !lean_is_exclusive(v___x_6791_);
if (v_isSharedCheck_6816_ == 0)
{
v___x_6811_ = v___x_6791_;
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
else
{
lean_inc(v_a_6809_);
lean_dec(v___x_6791_);
v___x_6811_ = lean_box(0);
v_isShared_6812_ = v_isSharedCheck_6816_;
goto v_resetjp_6810_;
}
v_resetjp_6810_:
{
lean_object* v___x_6814_; 
if (v_isShared_6812_ == 0)
{
v___x_6814_ = v___x_6811_;
goto v_reusejp_6813_;
}
else
{
lean_object* v_reuseFailAlloc_6815_; 
v_reuseFailAlloc_6815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6815_, 0, v_a_6809_);
v___x_6814_ = v_reuseFailAlloc_6815_;
goto v_reusejp_6813_;
}
v_reusejp_6813_:
{
return v___x_6814_;
}
}
}
}
else
{
lean_dec_ref(v_b_6783_);
lean_dec_ref(v_a_6782_);
lean_dec(v_rName_6781_);
lean_dec(v_className_6780_);
return v___x_6789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel___boxed(lean_object* v_className_6817_, lean_object* v_rName_6818_, lean_object* v_a_6819_, lean_object* v_b_6820_, lean_object* v_a_6821_, lean_object* v_a_6822_, lean_object* v_a_6823_, lean_object* v_a_6824_, lean_object* v_a_6825_){
_start:
{
lean_object* v_res_6826_; 
v_res_6826_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v_className_6817_, v_rName_6818_, v_a_6819_, v_b_6820_, v_a_6821_, v_a_6822_, v_a_6823_, v_a_6824_);
lean_dec(v_a_6824_);
lean_dec_ref(v_a_6823_);
lean_dec(v_a_6822_);
lean_dec_ref(v_a_6821_);
return v_res_6826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE(lean_object* v_a_6829_, lean_object* v_b_6830_, lean_object* v_a_6831_, lean_object* v_a_6832_, lean_object* v_a_6833_, lean_object* v_a_6834_){
_start:
{
lean_object* v___x_6836_; lean_object* v___x_6837_; lean_object* v___x_6838_; 
v___x_6836_ = ((lean_object*)(l_Lean_Meta_mkLE___closed__0));
v___x_6837_ = ((lean_object*)(l_Lean_Meta_mkLe___closed__2));
v___x_6838_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6836_, v___x_6837_, v_a_6829_, v_b_6830_, v_a_6831_, v_a_6832_, v_a_6833_, v_a_6834_);
return v___x_6838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLE___boxed(lean_object* v_a_6839_, lean_object* v_b_6840_, lean_object* v_a_6841_, lean_object* v_a_6842_, lean_object* v_a_6843_, lean_object* v_a_6844_, lean_object* v_a_6845_){
_start:
{
lean_object* v_res_6846_; 
v_res_6846_ = l_Lean_Meta_mkLE(v_a_6839_, v_b_6840_, v_a_6841_, v_a_6842_, v_a_6843_, v_a_6844_);
lean_dec(v_a_6844_);
lean_dec_ref(v_a_6843_);
lean_dec(v_a_6842_);
lean_dec_ref(v_a_6841_);
return v_res_6846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT(lean_object* v_a_6849_, lean_object* v_b_6850_, lean_object* v_a_6851_, lean_object* v_a_6852_, lean_object* v_a_6853_, lean_object* v_a_6854_){
_start:
{
lean_object* v___x_6856_; lean_object* v___x_6857_; lean_object* v___x_6858_; 
v___x_6856_ = ((lean_object*)(l_Lean_Meta_mkLT___closed__0));
v___x_6857_ = ((lean_object*)(l_Lean_Meta_mkLt___closed__2));
v___x_6858_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkBinaryRel(v___x_6856_, v___x_6857_, v_a_6849_, v_b_6850_, v_a_6851_, v_a_6852_, v_a_6853_, v_a_6854_);
return v___x_6858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkLT___boxed(lean_object* v_a_6859_, lean_object* v_b_6860_, lean_object* v_a_6861_, lean_object* v_a_6862_, lean_object* v_a_6863_, lean_object* v_a_6864_, lean_object* v_a_6865_){
_start:
{
lean_object* v_res_6866_; 
v_res_6866_ = l_Lean_Meta_mkLT(v_a_6859_, v_b_6860_, v_a_6861_, v_a_6862_, v_a_6863_, v_a_6864_);
lean_dec(v_a_6864_);
lean_dec_ref(v_a_6863_);
lean_dec(v_a_6862_);
lean_dec_ref(v_a_6861_);
return v_res_6866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq(lean_object* v_h_6872_, lean_object* v_a_6873_, lean_object* v_a_6874_, lean_object* v_a_6875_, lean_object* v_a_6876_){
_start:
{
lean_object* v___x_6878_; lean_object* v___x_6879_; uint8_t v___x_6880_; 
v___x_6878_ = ((lean_object*)(l_Lean_Meta_mkPropExt___closed__1));
v___x_6879_ = lean_unsigned_to_nat(3u);
v___x_6880_ = l_Lean_Expr_isAppOfArity(v_h_6872_, v___x_6878_, v___x_6879_);
if (v___x_6880_ == 0)
{
lean_object* v___x_6881_; lean_object* v___x_6882_; lean_object* v___x_6883_; lean_object* v___x_6884_; lean_object* v___x_6885_; 
v___x_6881_ = ((lean_object*)(l_Lean_Meta_mkIffOfEq___closed__2));
v___x_6882_ = lean_unsigned_to_nat(1u);
v___x_6883_ = lean_mk_empty_array_with_capacity(v___x_6882_);
v___x_6884_ = lean_array_push(v___x_6883_, v_h_6872_);
v___x_6885_ = l_Lean_Meta_mkAppM(v___x_6881_, v___x_6884_, v_a_6873_, v_a_6874_, v_a_6875_, v_a_6876_);
return v___x_6885_;
}
else
{
lean_object* v___x_6886_; lean_object* v___x_6887_; 
v___x_6886_ = l_Lean_Expr_appArg_x21(v_h_6872_);
lean_dec_ref(v_h_6872_);
v___x_6887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6887_, 0, v___x_6886_);
return v___x_6887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkIffOfEq___boxed(lean_object* v_h_6888_, lean_object* v_a_6889_, lean_object* v_a_6890_, lean_object* v_a_6891_, lean_object* v_a_6892_, lean_object* v_a_6893_){
_start:
{
lean_object* v_res_6894_; 
v_res_6894_ = l_Lean_Meta_mkIffOfEq(v_h_6888_, v_a_6889_, v_a_6890_, v_a_6891_, v_a_6892_);
lean_dec(v_a_6892_);
lean_dec_ref(v_a_6891_);
lean_dec(v_a_6890_);
lean_dec_ref(v_a_6889_);
return v_res_6894_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3(void){
_start:
{
lean_object* v___x_6900_; lean_object* v___x_6901_; lean_object* v___x_6902_; 
v___x_6900_ = lean_box(0);
v___x_6901_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__2));
v___x_6902_ = l_Lean_mkConst(v___x_6901_, v___x_6900_);
return v___x_6902_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5(void){
_start:
{
lean_object* v___x_6905_; lean_object* v___x_6906_; lean_object* v___x_6907_; 
v___x_6905_ = lean_box(0);
v___x_6906_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__4));
v___x_6907_ = l_Lean_mkConst(v___x_6906_, v___x_6905_);
return v___x_6907_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6(void){
_start:
{
lean_object* v___x_6908_; lean_object* v___x_6909_; lean_object* v___x_6910_; 
v___x_6908_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__5);
v___x_6909_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__3);
v___x_6910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6910_, 0, v___x_6909_);
lean_ctor_set(v___x_6910_, 1, v___x_6908_);
return v___x_6910_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9(void){
_start:
{
lean_object* v___x_6915_; lean_object* v___x_6916_; lean_object* v___x_6917_; 
v___x_6915_ = lean_box(0);
v___x_6916_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__8));
v___x_6917_ = l_Lean_mkConst(v___x_6916_, v___x_6915_);
return v___x_6917_;
}
}
static lean_object* _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11(void){
_start:
{
lean_object* v___x_6920_; lean_object* v___x_6921_; lean_object* v___x_6922_; 
v___x_6920_ = lean_box(0);
v___x_6921_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__10));
v___x_6922_ = l_Lean_mkConst(v___x_6921_, v___x_6920_);
return v___x_6922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(lean_object* v_a_6923_, lean_object* v_a_6924_, lean_object* v_a_6925_, lean_object* v_a_6926_, lean_object* v_a_6927_){
_start:
{
if (lean_obj_tag(v_a_6923_) == 0)
{
lean_object* v___x_6929_; lean_object* v___x_6930_; 
v___x_6929_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__6);
v___x_6930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6930_, 0, v___x_6929_);
return v___x_6930_;
}
else
{
lean_object* v_tail_6931_; 
v_tail_6931_ = lean_ctor_get(v_a_6923_, 1);
if (lean_obj_tag(v_tail_6931_) == 0)
{
lean_object* v_head_6932_; lean_object* v___x_6934_; uint8_t v_isShared_6935_; uint8_t v_isSharedCheck_6956_; 
v_head_6932_ = lean_ctor_get(v_a_6923_, 0);
v_isSharedCheck_6956_ = !lean_is_exclusive(v_a_6923_);
if (v_isSharedCheck_6956_ == 0)
{
lean_object* v_unused_6957_; 
v_unused_6957_ = lean_ctor_get(v_a_6923_, 1);
lean_dec(v_unused_6957_);
v___x_6934_ = v_a_6923_;
v_isShared_6935_ = v_isSharedCheck_6956_;
goto v_resetjp_6933_;
}
else
{
lean_inc(v_head_6932_);
lean_dec(v_a_6923_);
v___x_6934_ = lean_box(0);
v_isShared_6935_ = v_isSharedCheck_6956_;
goto v_resetjp_6933_;
}
v_resetjp_6933_:
{
lean_object* v___x_6936_; 
lean_inc(v_a_6927_);
lean_inc_ref(v_a_6926_);
lean_inc(v_a_6925_);
lean_inc_ref(v_a_6924_);
lean_inc(v_head_6932_);
v___x_6936_ = lean_infer_type(v_head_6932_, v_a_6924_, v_a_6925_, v_a_6926_, v_a_6927_);
if (lean_obj_tag(v___x_6936_) == 0)
{
lean_object* v_a_6937_; lean_object* v___x_6939_; uint8_t v_isShared_6940_; uint8_t v_isSharedCheck_6947_; 
v_a_6937_ = lean_ctor_get(v___x_6936_, 0);
v_isSharedCheck_6947_ = !lean_is_exclusive(v___x_6936_);
if (v_isSharedCheck_6947_ == 0)
{
v___x_6939_ = v___x_6936_;
v_isShared_6940_ = v_isSharedCheck_6947_;
goto v_resetjp_6938_;
}
else
{
lean_inc(v_a_6937_);
lean_dec(v___x_6936_);
v___x_6939_ = lean_box(0);
v_isShared_6940_ = v_isSharedCheck_6947_;
goto v_resetjp_6938_;
}
v_resetjp_6938_:
{
lean_object* v___x_6942_; 
if (v_isShared_6935_ == 0)
{
lean_ctor_set_tag(v___x_6934_, 0);
lean_ctor_set(v___x_6934_, 1, v_a_6937_);
v___x_6942_ = v___x_6934_;
goto v_reusejp_6941_;
}
else
{
lean_object* v_reuseFailAlloc_6946_; 
v_reuseFailAlloc_6946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6946_, 0, v_head_6932_);
lean_ctor_set(v_reuseFailAlloc_6946_, 1, v_a_6937_);
v___x_6942_ = v_reuseFailAlloc_6946_;
goto v_reusejp_6941_;
}
v_reusejp_6941_:
{
lean_object* v___x_6944_; 
if (v_isShared_6940_ == 0)
{
lean_ctor_set(v___x_6939_, 0, v___x_6942_);
v___x_6944_ = v___x_6939_;
goto v_reusejp_6943_;
}
else
{
lean_object* v_reuseFailAlloc_6945_; 
v_reuseFailAlloc_6945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6945_, 0, v___x_6942_);
v___x_6944_ = v_reuseFailAlloc_6945_;
goto v_reusejp_6943_;
}
v_reusejp_6943_:
{
return v___x_6944_;
}
}
}
}
else
{
lean_object* v_a_6948_; lean_object* v___x_6950_; uint8_t v_isShared_6951_; uint8_t v_isSharedCheck_6955_; 
lean_del_object(v___x_6934_);
lean_dec(v_head_6932_);
v_a_6948_ = lean_ctor_get(v___x_6936_, 0);
v_isSharedCheck_6955_ = !lean_is_exclusive(v___x_6936_);
if (v_isSharedCheck_6955_ == 0)
{
v___x_6950_ = v___x_6936_;
v_isShared_6951_ = v_isSharedCheck_6955_;
goto v_resetjp_6949_;
}
else
{
lean_inc(v_a_6948_);
lean_dec(v___x_6936_);
v___x_6950_ = lean_box(0);
v_isShared_6951_ = v_isSharedCheck_6955_;
goto v_resetjp_6949_;
}
v_resetjp_6949_:
{
lean_object* v___x_6953_; 
if (v_isShared_6951_ == 0)
{
v___x_6953_ = v___x_6950_;
goto v_reusejp_6952_;
}
else
{
lean_object* v_reuseFailAlloc_6954_; 
v_reuseFailAlloc_6954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6954_, 0, v_a_6948_);
v___x_6953_ = v_reuseFailAlloc_6954_;
goto v_reusejp_6952_;
}
v_reusejp_6952_:
{
return v___x_6953_;
}
}
}
}
}
else
{
lean_object* v_head_6958_; lean_object* v___x_6959_; 
lean_inc(v_tail_6931_);
v_head_6958_ = lean_ctor_get(v_a_6923_, 0);
lean_inc(v_head_6958_);
lean_dec_ref_known(v_a_6923_, 2);
v___x_6959_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_tail_6931_, v_a_6924_, v_a_6925_, v_a_6926_, v_a_6927_);
if (lean_obj_tag(v___x_6959_) == 0)
{
lean_object* v_a_6960_; lean_object* v_fst_6961_; lean_object* v_snd_6962_; lean_object* v___x_6964_; uint8_t v_isShared_6965_; uint8_t v_isSharedCheck_6990_; 
v_a_6960_ = lean_ctor_get(v___x_6959_, 0);
lean_inc(v_a_6960_);
lean_dec_ref_known(v___x_6959_, 1);
v_fst_6961_ = lean_ctor_get(v_a_6960_, 0);
v_snd_6962_ = lean_ctor_get(v_a_6960_, 1);
v_isSharedCheck_6990_ = !lean_is_exclusive(v_a_6960_);
if (v_isSharedCheck_6990_ == 0)
{
v___x_6964_ = v_a_6960_;
v_isShared_6965_ = v_isSharedCheck_6990_;
goto v_resetjp_6963_;
}
else
{
lean_inc(v_snd_6962_);
lean_inc(v_fst_6961_);
lean_dec(v_a_6960_);
v___x_6964_ = lean_box(0);
v_isShared_6965_ = v_isSharedCheck_6990_;
goto v_resetjp_6963_;
}
v_resetjp_6963_:
{
lean_object* v___x_6966_; 
lean_inc(v_a_6927_);
lean_inc_ref(v_a_6926_);
lean_inc(v_a_6925_);
lean_inc_ref(v_a_6924_);
lean_inc(v_head_6958_);
v___x_6966_ = lean_infer_type(v_head_6958_, v_a_6924_, v_a_6925_, v_a_6926_, v_a_6927_);
if (lean_obj_tag(v___x_6966_) == 0)
{
lean_object* v_a_6967_; lean_object* v___x_6969_; uint8_t v_isShared_6970_; uint8_t v_isSharedCheck_6981_; 
v_a_6967_ = lean_ctor_get(v___x_6966_, 0);
v_isSharedCheck_6981_ = !lean_is_exclusive(v___x_6966_);
if (v_isSharedCheck_6981_ == 0)
{
v___x_6969_ = v___x_6966_;
v_isShared_6970_ = v_isSharedCheck_6981_;
goto v_resetjp_6968_;
}
else
{
lean_inc(v_a_6967_);
lean_dec(v___x_6966_);
v___x_6969_ = lean_box(0);
v_isShared_6970_ = v_isSharedCheck_6981_;
goto v_resetjp_6968_;
}
v_resetjp_6968_:
{
lean_object* v___x_6971_; lean_object* v___x_6972_; lean_object* v___x_6973_; lean_object* v___x_6974_; lean_object* v___x_6976_; 
v___x_6971_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__9);
lean_inc(v_snd_6962_);
lean_inc(v_a_6967_);
v___x_6972_ = l_Lean_mkApp4(v___x_6971_, v_a_6967_, v_snd_6962_, v_head_6958_, v_fst_6961_);
v___x_6973_ = lean_obj_once(&l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11, &l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11_once, _init_l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___closed__11);
v___x_6974_ = l_Lean_mkAppB(v___x_6973_, v_a_6967_, v_snd_6962_);
if (v_isShared_6965_ == 0)
{
lean_ctor_set(v___x_6964_, 1, v___x_6974_);
lean_ctor_set(v___x_6964_, 0, v___x_6972_);
v___x_6976_ = v___x_6964_;
goto v_reusejp_6975_;
}
else
{
lean_object* v_reuseFailAlloc_6980_; 
v_reuseFailAlloc_6980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6980_, 0, v___x_6972_);
lean_ctor_set(v_reuseFailAlloc_6980_, 1, v___x_6974_);
v___x_6976_ = v_reuseFailAlloc_6980_;
goto v_reusejp_6975_;
}
v_reusejp_6975_:
{
lean_object* v___x_6978_; 
if (v_isShared_6970_ == 0)
{
lean_ctor_set(v___x_6969_, 0, v___x_6976_);
v___x_6978_ = v___x_6969_;
goto v_reusejp_6977_;
}
else
{
lean_object* v_reuseFailAlloc_6979_; 
v_reuseFailAlloc_6979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6979_, 0, v___x_6976_);
v___x_6978_ = v_reuseFailAlloc_6979_;
goto v_reusejp_6977_;
}
v_reusejp_6977_:
{
return v___x_6978_;
}
}
}
}
else
{
lean_object* v_a_6982_; lean_object* v___x_6984_; uint8_t v_isShared_6985_; uint8_t v_isSharedCheck_6989_; 
lean_del_object(v___x_6964_);
lean_dec(v_snd_6962_);
lean_dec(v_fst_6961_);
lean_dec(v_head_6958_);
v_a_6982_ = lean_ctor_get(v___x_6966_, 0);
v_isSharedCheck_6989_ = !lean_is_exclusive(v___x_6966_);
if (v_isSharedCheck_6989_ == 0)
{
v___x_6984_ = v___x_6966_;
v_isShared_6985_ = v_isSharedCheck_6989_;
goto v_resetjp_6983_;
}
else
{
lean_inc(v_a_6982_);
lean_dec(v___x_6966_);
v___x_6984_ = lean_box(0);
v_isShared_6985_ = v_isSharedCheck_6989_;
goto v_resetjp_6983_;
}
v_resetjp_6983_:
{
lean_object* v___x_6987_; 
if (v_isShared_6985_ == 0)
{
v___x_6987_ = v___x_6984_;
goto v_reusejp_6986_;
}
else
{
lean_object* v_reuseFailAlloc_6988_; 
v_reuseFailAlloc_6988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6988_, 0, v_a_6982_);
v___x_6987_ = v_reuseFailAlloc_6988_;
goto v_reusejp_6986_;
}
v_reusejp_6986_:
{
return v___x_6987_;
}
}
}
}
}
else
{
lean_dec(v_head_6958_);
return v___x_6959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go___boxed(lean_object* v_a_6991_, lean_object* v_a_6992_, lean_object* v_a_6993_, lean_object* v_a_6994_, lean_object* v_a_6995_, lean_object* v_a_6996_){
_start:
{
lean_object* v_res_6997_; 
v_res_6997_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_a_6991_, v_a_6992_, v_a_6993_, v_a_6994_, v_a_6995_);
lean_dec(v_a_6995_);
lean_dec_ref(v_a_6994_);
lean_dec(v_a_6993_);
lean_dec_ref(v_a_6992_);
return v_res_6997_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN(lean_object* v_hs_6998_, lean_object* v_a_6999_, lean_object* v_a_7000_, lean_object* v_a_7001_, lean_object* v_a_7002_){
_start:
{
lean_object* v___x_7004_; 
v___x_7004_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_mkAndIntroN_go(v_hs_6998_, v_a_6999_, v_a_7000_, v_a_7001_, v_a_7002_);
if (lean_obj_tag(v___x_7004_) == 0)
{
lean_object* v_a_7005_; lean_object* v___x_7007_; uint8_t v_isShared_7008_; uint8_t v_isSharedCheck_7013_; 
v_a_7005_ = lean_ctor_get(v___x_7004_, 0);
v_isSharedCheck_7013_ = !lean_is_exclusive(v___x_7004_);
if (v_isSharedCheck_7013_ == 0)
{
v___x_7007_ = v___x_7004_;
v_isShared_7008_ = v_isSharedCheck_7013_;
goto v_resetjp_7006_;
}
else
{
lean_inc(v_a_7005_);
lean_dec(v___x_7004_);
v___x_7007_ = lean_box(0);
v_isShared_7008_ = v_isSharedCheck_7013_;
goto v_resetjp_7006_;
}
v_resetjp_7006_:
{
lean_object* v_fst_7009_; lean_object* v___x_7011_; 
v_fst_7009_ = lean_ctor_get(v_a_7005_, 0);
lean_inc(v_fst_7009_);
lean_dec(v_a_7005_);
if (v_isShared_7008_ == 0)
{
lean_ctor_set(v___x_7007_, 0, v_fst_7009_);
v___x_7011_ = v___x_7007_;
goto v_reusejp_7010_;
}
else
{
lean_object* v_reuseFailAlloc_7012_; 
v_reuseFailAlloc_7012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7012_, 0, v_fst_7009_);
v___x_7011_ = v_reuseFailAlloc_7012_;
goto v_reusejp_7010_;
}
v_reusejp_7010_:
{
return v___x_7011_;
}
}
}
else
{
lean_object* v_a_7014_; lean_object* v___x_7016_; uint8_t v_isShared_7017_; uint8_t v_isSharedCheck_7021_; 
v_a_7014_ = lean_ctor_get(v___x_7004_, 0);
v_isSharedCheck_7021_ = !lean_is_exclusive(v___x_7004_);
if (v_isSharedCheck_7021_ == 0)
{
v___x_7016_ = v___x_7004_;
v_isShared_7017_ = v_isSharedCheck_7021_;
goto v_resetjp_7015_;
}
else
{
lean_inc(v_a_7014_);
lean_dec(v___x_7004_);
v___x_7016_ = lean_box(0);
v_isShared_7017_ = v_isSharedCheck_7021_;
goto v_resetjp_7015_;
}
v_resetjp_7015_:
{
lean_object* v___x_7019_; 
if (v_isShared_7017_ == 0)
{
v___x_7019_ = v___x_7016_;
goto v_reusejp_7018_;
}
else
{
lean_object* v_reuseFailAlloc_7020_; 
v_reuseFailAlloc_7020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_7020_, 0, v_a_7014_);
v___x_7019_ = v_reuseFailAlloc_7020_;
goto v_reusejp_7018_;
}
v_reusejp_7018_:
{
return v___x_7019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkAndIntroN___boxed(lean_object* v_hs_7022_, lean_object* v_a_7023_, lean_object* v_a_7024_, lean_object* v_a_7025_, lean_object* v_a_7026_, lean_object* v_a_7027_){
_start:
{
lean_object* v_res_7028_; 
v_res_7028_ = l_Lean_Meta_mkAndIntroN(v_hs_7022_, v_a_7023_, v_a_7024_, v_a_7025_, v_a_7026_);
lean_dec(v_a_7026_);
lean_dec_ref(v_a_7025_);
lean_dec(v_a_7024_);
lean_dec_ref(v_a_7023_);
return v_res_7028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_7085_; uint8_t v___x_7086_; lean_object* v___x_7087_; lean_object* v___x_7088_; 
v___x_7085_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__27));
v___x_7086_ = 0;
v___x_7087_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_));
v___x_7088_ = l_Lean_registerTraceClass(v___x_7085_, v___x_7086_, v___x_7087_);
if (lean_obj_tag(v___x_7088_) == 0)
{
lean_object* v___x_7089_; uint8_t v___x_7090_; lean_object* v___x_7091_; 
lean_dec_ref_known(v___x_7088_, 1);
v___x_7089_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__32));
v___x_7090_ = 1;
v___x_7091_ = l_Lean_registerTraceClass(v___x_7089_, v___x_7090_, v___x_7087_);
if (lean_obj_tag(v___x_7091_) == 0)
{
lean_object* v___x_7092_; lean_object* v___x_7093_; 
lean_dec_ref_known(v___x_7091_, 1);
v___x_7092_ = ((lean_object*)(l___private_Lean_Meta_AppBuilder_0__Lean_Meta_withAppBuilderTrace___redArg___closed__22));
v___x_7093_ = l_Lean_registerTraceClass(v___x_7092_, v___x_7090_, v___x_7087_);
return v___x_7093_;
}
else
{
return v___x_7091_;
}
}
else
{
return v___x_7088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2____boxed(lean_object* v_a_7094_){
_start:
{
lean_object* v_res_7095_; 
v_res_7095_ = l___private_Lean_Meta_AppBuilder_0__Lean_Meta_initFn_00___x40_Lean_Meta_AppBuilder_902289040____hygCtx___hyg_2_();
return v_res_7095_;
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
