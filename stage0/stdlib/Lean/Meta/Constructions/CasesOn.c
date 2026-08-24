// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOn
// Imports: public import Lean.AddDecl public import Lean.Meta.Basic
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_markAuxRecursor(lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
lean_object* l_StateRefT_x27_instMonad___redArg(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_isPropFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_List_range(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_range(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_hasUnsafe(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_elab_environment_to_kernel_env(lean_object*);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_get_num_heartbeats();
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_mk_cases_on(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnImp___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__0 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__0_value;
static const lean_ctor_object l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__1 = (const lean_object*)&l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mkCasesOnViaProjs_x3f_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mkCasesOnViaProjs_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__3___boxed(lean_object**);
static lean_once_cell_t l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__1 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__2 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__3 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__4 = (const lean_object*)&l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__0 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "` is not a recursor"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__2 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__3;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__4 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__4_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Lean.isRec\?"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__5 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__5_value;
static const lean_string_object l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__6 = (const lean_object*)&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__6_value;
static lean_once_cell_t l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__7;
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "` is not a constructor"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__0 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__0_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__1;
static const lean_string_object l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__2 = (const lean_object*)&l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__2_value;
static lean_once_cell_t l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__3;
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkCasesOnViaProjs_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnViaProjs_x3f___closed__0;
static lean_once_cell_t l_Lean_mkCasesOnViaProjs_x3f___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnViaProjs_x3f___closed__1;
static lean_once_cell_t l_Lean_mkCasesOnViaProjs_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOnViaProjs_x3f___closed__2;
static const lean_array_object l_Lean_mkCasesOnViaProjs_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_mkCasesOnViaProjs_x3f___closed__3 = (const lean_object*)&l_Lean_mkCasesOnViaProjs_x3f___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg();
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_mkCasesOn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_mkCasesOn___closed__0 = (const lean_object*)&l_Lean_mkCasesOn___closed__0_value;
static const lean_string_object l_Lean_mkCasesOn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "mkCasesOn"};
static const lean_object* l_Lean_mkCasesOn___closed__1 = (const lean_object*)&l_Lean_mkCasesOn___closed__1_value;
static const lean_ctor_object l_Lean_mkCasesOn___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_mkCasesOn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_mkCasesOn___closed__2_value_aux_0),((lean_object*)&l_Lean_mkCasesOn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(210, 62, 169, 32, 175, 179, 252, 201)}};
static const lean_object* l_Lean_mkCasesOn___closed__2 = (const lean_object*)&l_Lean_mkCasesOn___closed__2_value;
static const lean_string_object l_Lean_mkCasesOn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_mkCasesOn___closed__3 = (const lean_object*)&l_Lean_mkCasesOn___closed__3_value;
static const lean_string_object l_Lean_mkCasesOn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_mkCasesOn___closed__4 = (const lean_object*)&l_Lean_mkCasesOn___closed__4_value;
static const lean_ctor_object l_Lean_mkCasesOn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_mkCasesOn___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_mkCasesOn___closed__5 = (const lean_object*)&l_Lean_mkCasesOn___closed__5_value;
static lean_once_cell_t l_Lean_mkCasesOn___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkCasesOn___closed__6;
static lean_once_cell_t l_Lean_mkCasesOn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_mkCasesOn___closed__7;
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__0_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__1_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__3_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l_Lean_mkCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Constructions"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__4_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(224, 107, 212, 234, 74, 49, 105, 87)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "CasesOn"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__6_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(169, 138, 163, 69, 218, 172, 3, 193)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__8_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(236, 93, 225, 44, 98, 194, 222, 198)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__9_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(237, 210, 255, 39, 71, 150, 217, 233)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__10_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__11_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(196, 108, 49, 213, 198, 16, 112, 74)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__12_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__13_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 136, 138, 61, 141, 154, 156, 94)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__14_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__2_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(56, 243, 213, 167, 134, 227, 5, 96)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__15_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l_Lean_mkCasesOn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(148, 216, 218, 215, 246, 206, 35, 172)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__16_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__5_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(50, 250, 31, 145, 63, 77, 70, 221)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__17_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__7_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 98, 44, 117, 252, 253, 129, 45)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__18_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)(((size_t)(989523109) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(33, 63, 231, 116, 95, 206, 102, 190)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__19_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__20_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(162, 168, 149, 82, 136, 252, 169, 218)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__21_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__22_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 82, 99, 185, 147, 204, 210, 220)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__23_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(191, 22, 202, 159, 104, 165, 236, 145)}};
static const lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkCasesOnImp___boxed(lean_object* v_env_3_, lean_object* v_declName_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = lean_mk_cases_on(v_env_3_, v_declName_4_);
lean_dec(v_declName_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1(lean_object* v_a_9_, lean_object* v_a_10_){
_start:
{
if (lean_obj_tag(v_a_9_) == 0)
{
lean_object* v___x_11_; 
v___x_11_ = l_List_reverse___redArg(v_a_10_);
return v___x_11_;
}
else
{
lean_object* v_head_12_; lean_object* v_tail_13_; lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_28_; 
v_head_12_ = lean_ctor_get(v_a_9_, 0);
v_tail_13_ = lean_ctor_get(v_a_9_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_a_9_);
if (v_isSharedCheck_28_ == 0)
{
v___x_15_ = v_a_9_;
v_isShared_16_ = v_isSharedCheck_28_;
goto v_resetjp_14_;
}
else
{
lean_inc(v_tail_13_);
lean_inc(v_head_12_);
lean_dec(v_a_9_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_28_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___y_18_; lean_object* v___x_23_; uint8_t v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_nat_dec_eq(v_head_12_, v___x_23_);
if (v___x_24_ == 0)
{
lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_25_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__1));
v___x_26_ = lean_name_append_index_after(v___x_25_, v_head_12_);
v___y_18_ = v___x_26_;
goto v___jp_17_;
}
else
{
lean_object* v___x_27_; 
lean_dec(v_head_12_);
v___x_27_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__1));
v___y_18_ = v___x_27_;
goto v___jp_17_;
}
v___jp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 1, v_a_10_);
lean_ctor_set(v___x_15_, 0, v___y_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___y_18_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_a_10_);
v___x_20_ = v_reuseFailAlloc_22_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
v_a_9_ = v_tail_13_;
v_a_10_ = v___x_20_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__0(lean_object* v_a_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
uint8_t v___x_31_; 
v___x_31_ = 0;
return v___x_31_;
}
else
{
lean_object* v_head_32_; lean_object* v_tail_33_; uint8_t v___x_34_; 
v_head_32_ = lean_ctor_get(v_x_30_, 0);
v_tail_33_ = lean_ctor_get(v_x_30_, 1);
v___x_34_ = lean_name_eq(v_a_29_, v_head_32_);
if (v___x_34_ == 0)
{
v_x_30_ = v_tail_33_;
goto _start;
}
else
{
return v___x_34_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__0___boxed(lean_object* v_a_36_, lean_object* v_x_37_){
_start:
{
uint8_t v_res_38_; lean_object* v_r_39_; 
v_res_38_ = l_List_elem___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__0(v_a_36_, v_x_37_);
lean_dec(v_x_37_);
lean_dec(v_a_36_);
v_r_39_ = lean_box(v_res_38_);
return v_r_39_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__2(lean_object* v_lparams_40_, lean_object* v_x_41_){
_start:
{
if (lean_obj_tag(v_x_41_) == 0)
{
lean_object* v___x_42_; 
v___x_42_ = lean_box(0);
return v___x_42_;
}
else
{
lean_object* v_head_43_; lean_object* v_tail_44_; uint8_t v___x_45_; 
v_head_43_ = lean_ctor_get(v_x_41_, 0);
v_tail_44_ = lean_ctor_get(v_x_41_, 1);
v___x_45_ = l_List_elem___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__0(v_head_43_, v_lparams_40_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; 
lean_inc(v_head_43_);
v___x_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_46_, 0, v_head_43_);
return v___x_46_;
}
else
{
v_x_41_ = v_tail_44_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__2___boxed(lean_object* v_lparams_48_, lean_object* v_x_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_List_find_x3f___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__2(v_lparams_48_, v_x_49_);
lean_dec(v_x_49_);
lean_dec(v_lparams_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName(lean_object* v_lparams_51_){
_start:
{
lean_object* v___x_52_; lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v_cands_57_; lean_object* v___x_58_; 
v___x_52_ = l_List_lengthTR___redArg(v_lparams_51_);
v___x_53_ = lean_unsigned_to_nat(1u);
v___x_54_ = lean_nat_add(v___x_52_, v___x_53_);
lean_dec(v___x_52_);
v___x_55_ = l_List_range(v___x_54_);
v___x_56_ = lean_box(0);
v_cands_57_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1(v___x_55_, v___x_56_);
v___x_58_ = l_List_find_x3f___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__2(v_lparams_51_, v_cands_57_);
lean_dec(v_cands_57_);
if (lean_obj_tag(v___x_58_) == 0)
{
lean_object* v___x_59_; 
v___x_59_ = ((lean_object*)(l_List_mapTR_loop___at___00__private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName_spec__1___closed__1));
return v___x_59_;
}
else
{
lean_object* v_val_60_; 
v_val_60_ = lean_ctor_get(v___x_58_, 0);
lean_inc(v_val_60_);
lean_dec_ref_known(v___x_58_, 1);
return v_val_60_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName___boxed(lean_object* v_lparams_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName(v_lparams_61_);
lean_dec(v_lparams_61_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___redArg(lean_object* v_name_63_, lean_object* v_levelParams_64_, lean_object* v_type_65_, lean_object* v_value_66_, lean_object* v_hints_67_, lean_object* v___y_68_){
_start:
{
lean_object* v___x_70_; uint8_t v___y_72_; uint8_t v___y_79_; lean_object* v_env_82_; uint8_t v___x_83_; 
v___x_70_ = lean_st_ref_get(v___y_68_);
v_env_82_ = lean_ctor_get(v___x_70_, 0);
lean_inc_ref_n(v_env_82_, 2);
lean_dec(v___x_70_);
v___x_83_ = l_Lean_Environment_hasUnsafe(v_env_82_, v_type_65_);
if (v___x_83_ == 0)
{
uint8_t v___x_84_; 
v___x_84_ = l_Lean_Environment_hasUnsafe(v_env_82_, v_value_66_);
v___y_79_ = v___x_84_;
goto v___jp_78_;
}
else
{
lean_dec_ref(v_env_82_);
v___y_79_ = v___x_83_;
goto v___jp_78_;
}
v___jp_71_:
{
lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
lean_inc(v_name_63_);
v___x_73_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_73_, 0, v_name_63_);
lean_ctor_set(v___x_73_, 1, v_levelParams_64_);
lean_ctor_set(v___x_73_, 2, v_type_65_);
v___x_74_ = lean_box(0);
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v_name_63_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_76_, 0, v___x_73_);
lean_ctor_set(v___x_76_, 1, v_value_66_);
lean_ctor_set(v___x_76_, 2, v_hints_67_);
lean_ctor_set(v___x_76_, 3, v___x_75_);
lean_ctor_set_uint8(v___x_76_, sizeof(void*)*4, v___y_72_);
v___x_77_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
return v___x_77_;
}
v___jp_78_:
{
if (v___y_79_ == 0)
{
uint8_t v___x_80_; 
v___x_80_ = 1;
v___y_72_ = v___x_80_;
goto v___jp_71_;
}
else
{
uint8_t v___x_81_; 
v___x_81_ = 0;
v___y_72_ = v___x_81_;
goto v___jp_71_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___redArg___boxed(lean_object* v_name_85_, lean_object* v_levelParams_86_, lean_object* v_type_87_, lean_object* v_value_88_, lean_object* v_hints_89_, lean_object* v___y_90_, lean_object* v___y_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___redArg(v_name_85_, v_levelParams_86_, v_type_87_, v_value_88_, v_hints_89_, v___y_90_);
lean_dec(v___y_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4(lean_object* v_name_93_, lean_object* v_levelParams_94_, lean_object* v_type_95_, lean_object* v_value_96_, lean_object* v_hints_97_, lean_object* v___y_98_, lean_object* v___y_99_, lean_object* v___y_100_, lean_object* v___y_101_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___redArg(v_name_93_, v_levelParams_94_, v_type_95_, v_value_96_, v_hints_97_, v___y_101_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___boxed(lean_object* v_name_104_, lean_object* v_levelParams_105_, lean_object* v_type_106_, lean_object* v_value_107_, lean_object* v_hints_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_res_114_; 
v_res_114_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4(v_name_104_, v_levelParams_105_, v_type_106_, v_value_107_, v_hints_108_, v___y_109_, v___y_110_, v___y_111_, v___y_112_);
lean_dec(v___y_112_);
lean_dec_ref(v___y_111_);
lean_dec(v___y_110_);
lean_dec_ref(v___y_109_);
return v_res_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___lam__0(lean_object* v_k_115_, lean_object* v_b_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_){
_start:
{
lean_object* v___x_122_; 
lean_inc(v___y_120_);
lean_inc_ref(v___y_119_);
lean_inc(v___y_118_);
lean_inc_ref(v___y_117_);
v___x_122_ = lean_apply_6(v_k_115_, v_b_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_, lean_box(0));
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___lam__0___boxed(lean_object* v_k_123_, lean_object* v_b_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v_res_130_; 
v_res_130_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___lam__0(v_k_123_, v_b_124_, v___y_125_, v___y_126_, v___y_127_, v___y_128_);
lean_dec(v___y_128_);
lean_dec_ref(v___y_127_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
return v_res_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg(lean_object* v_name_131_, uint8_t v_bi_132_, lean_object* v_type_133_, lean_object* v_k_134_, uint8_t v_kind_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_){
_start:
{
lean_object* v___f_141_; lean_object* v___x_142_; 
v___f_141_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_141_, 0, v_k_134_);
v___x_142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_131_, v_bi_132_, v_type_133_, v___f_141_, v_kind_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_150_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_150_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_150_ == 0)
{
v___x_145_ = v___x_142_;
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_a_143_);
lean_dec(v___x_142_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_150_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_a_143_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
else
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_a_151_ = lean_ctor_get(v___x_142_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_142_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_142_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_142_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg___boxed(lean_object* v_name_159_, lean_object* v_bi_160_, lean_object* v_type_161_, lean_object* v_k_162_, lean_object* v_kind_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_){
_start:
{
uint8_t v_bi_boxed_169_; uint8_t v_kind_boxed_170_; lean_object* v_res_171_; 
v_bi_boxed_169_ = lean_unbox(v_bi_160_);
v_kind_boxed_170_ = lean_unbox(v_kind_163_);
v_res_171_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg(v_name_159_, v_bi_boxed_169_, v_type_161_, v_k_162_, v_kind_boxed_170_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
lean_dec(v___y_165_);
lean_dec_ref(v___y_164_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5(lean_object* v_00_u03b1_172_, lean_object* v_name_173_, uint8_t v_bi_174_, lean_object* v_type_175_, lean_object* v_k_176_, uint8_t v_kind_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg(v_name_173_, v_bi_174_, v_type_175_, v_k_176_, v_kind_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___boxed(lean_object* v_00_u03b1_184_, lean_object* v_name_185_, lean_object* v_bi_186_, lean_object* v_type_187_, lean_object* v_k_188_, lean_object* v_kind_189_, lean_object* v___y_190_, lean_object* v___y_191_, lean_object* v___y_192_, lean_object* v___y_193_, lean_object* v___y_194_){
_start:
{
uint8_t v_bi_boxed_195_; uint8_t v_kind_boxed_196_; lean_object* v_res_197_; 
v_bi_boxed_195_ = lean_unbox(v_bi_186_);
v_kind_boxed_196_ = lean_unbox(v_kind_189_);
v_res_197_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5(v_00_u03b1_184_, v_name_185_, v_bi_boxed_195_, v_type_187_, v_k_188_, v_kind_boxed_196_, v___y_190_, v___y_191_, v___y_192_, v___y_193_);
lean_dec(v___y_193_);
lean_dec_ref(v___y_192_);
lean_dec(v___y_191_);
lean_dec_ref(v___y_190_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___lam__0(lean_object* v_k_198_, lean_object* v_b_199_, lean_object* v_c_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v___x_206_; 
lean_inc(v___y_204_);
lean_inc_ref(v___y_203_);
lean_inc(v___y_202_);
lean_inc_ref(v___y_201_);
v___x_206_ = lean_apply_7(v_k_198_, v_b_199_, v_c_200_, v___y_201_, v___y_202_, v___y_203_, v___y_204_, lean_box(0));
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___lam__0___boxed(lean_object* v_k_207_, lean_object* v_b_208_, lean_object* v_c_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___lam__0(v_k_207_, v_b_208_, v_c_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg(lean_object* v_type_216_, lean_object* v_maxFVars_x3f_217_, lean_object* v_k_218_, uint8_t v_cleanupAnnotations_219_, uint8_t v_whnfType_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___f_226_; lean_object* v___x_227_; 
v___f_226_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_226_, 0, v_k_218_);
v___x_227_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), v_type_216_, v_maxFVars_x3f_217_, v___f_226_, v_cleanupAnnotations_219_, v_whnfType_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_243_; 
v_a_236_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_243_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_243_ == 0)
{
v___x_238_ = v___x_227_;
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_227_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_243_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_241_; 
if (v_isShared_239_ == 0)
{
v___x_241_ = v___x_238_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v_a_236_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg___boxed(lean_object* v_type_244_, lean_object* v_maxFVars_x3f_245_, lean_object* v_k_246_, lean_object* v_cleanupAnnotations_247_, lean_object* v_whnfType_248_, lean_object* v___y_249_, lean_object* v___y_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_254_; uint8_t v_whnfType_boxed_255_; lean_object* v_res_256_; 
v_cleanupAnnotations_boxed_254_ = lean_unbox(v_cleanupAnnotations_247_);
v_whnfType_boxed_255_ = lean_unbox(v_whnfType_248_);
v_res_256_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg(v_type_244_, v_maxFVars_x3f_245_, v_k_246_, v_cleanupAnnotations_boxed_254_, v_whnfType_boxed_255_, v___y_249_, v___y_250_, v___y_251_, v___y_252_);
lean_dec(v___y_252_);
lean_dec_ref(v___y_251_);
lean_dec(v___y_250_);
lean_dec_ref(v___y_249_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6(lean_object* v_00_u03b1_257_, lean_object* v_type_258_, lean_object* v_maxFVars_x3f_259_, lean_object* v_k_260_, uint8_t v_cleanupAnnotations_261_, uint8_t v_whnfType_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___redArg(v_type_258_, v_maxFVars_x3f_259_, v_k_260_, v_cleanupAnnotations_261_, v_whnfType_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___boxed(lean_object* v_00_u03b1_269_, lean_object* v_type_270_, lean_object* v_maxFVars_x3f_271_, lean_object* v_k_272_, lean_object* v_cleanupAnnotations_273_, lean_object* v_whnfType_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_280_; uint8_t v_whnfType_boxed_281_; lean_object* v_res_282_; 
v_cleanupAnnotations_boxed_280_ = lean_unbox(v_cleanupAnnotations_273_);
v_whnfType_boxed_281_ = lean_unbox(v_whnfType_274_);
v_res_282_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6(v_00_u03b1_269_, v_type_270_, v_maxFVars_x3f_271_, v_k_272_, v_cleanupAnnotations_boxed_280_, v_whnfType_boxed_281_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
lean_dec(v___y_278_);
lean_dec_ref(v___y_277_);
lean_dec(v___y_276_);
lean_dec_ref(v___y_275_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___redArg(lean_object* v_lctx_283_, lean_object* v_localInsts_284_, lean_object* v_x_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_283_, v_localInsts_284_, v_x_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_);
if (lean_obj_tag(v___x_291_) == 0)
{
lean_object* v_a_292_; lean_object* v___x_294_; uint8_t v_isShared_295_; uint8_t v_isSharedCheck_299_; 
v_a_292_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_299_ == 0)
{
v___x_294_ = v___x_291_;
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
else
{
lean_inc(v_a_292_);
lean_dec(v___x_291_);
v___x_294_ = lean_box(0);
v_isShared_295_ = v_isSharedCheck_299_;
goto v_resetjp_293_;
}
v_resetjp_293_:
{
lean_object* v___x_297_; 
if (v_isShared_295_ == 0)
{
v___x_297_ = v___x_294_;
goto v_reusejp_296_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
v___x_297_ = v_reuseFailAlloc_298_;
goto v_reusejp_296_;
}
v_reusejp_296_:
{
return v___x_297_;
}
}
}
else
{
lean_object* v_a_300_; lean_object* v___x_302_; uint8_t v_isShared_303_; uint8_t v_isSharedCheck_307_; 
v_a_300_ = lean_ctor_get(v___x_291_, 0);
v_isSharedCheck_307_ = !lean_is_exclusive(v___x_291_);
if (v_isSharedCheck_307_ == 0)
{
v___x_302_ = v___x_291_;
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
else
{
lean_inc(v_a_300_);
lean_dec(v___x_291_);
v___x_302_ = lean_box(0);
v_isShared_303_ = v_isSharedCheck_307_;
goto v_resetjp_301_;
}
v_resetjp_301_:
{
lean_object* v___x_305_; 
if (v_isShared_303_ == 0)
{
v___x_305_ = v___x_302_;
goto v_reusejp_304_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v_a_300_);
v___x_305_ = v_reuseFailAlloc_306_;
goto v_reusejp_304_;
}
v_reusejp_304_:
{
return v___x_305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___redArg___boxed(lean_object* v_lctx_308_, lean_object* v_localInsts_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v_res_316_; 
v_res_316_ = l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___redArg(v_lctx_308_, v_localInsts_309_, v_x_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
lean_dec(v___y_314_);
lean_dec_ref(v___y_313_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
return v_res_316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7(lean_object* v_00_u03b1_317_, lean_object* v_lctx_318_, lean_object* v_localInsts_319_, lean_object* v_x_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___redArg(v_lctx_318_, v_localInsts_319_, v_x_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___boxed(lean_object* v_00_u03b1_327_, lean_object* v_lctx_328_, lean_object* v_localInsts_329_, lean_object* v_x_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7(v_00_u03b1_327_, v_lctx_328_, v_localInsts_329_, v_x_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_);
lean_dec(v___y_334_);
lean_dec_ref(v___y_333_);
lean_dec(v___y_332_);
lean_dec_ref(v___y_331_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mkCasesOnViaProjs_x3f_spec__3(lean_object* v_declName_337_, lean_object* v_major_338_, size_t v_sz_339_, size_t v_i_340_, lean_object* v_bs_341_){
_start:
{
uint8_t v___x_342_; 
v___x_342_ = lean_usize_dec_lt(v_i_340_, v_sz_339_);
if (v___x_342_ == 0)
{
lean_dec_ref(v_major_338_);
lean_dec(v_declName_337_);
return v_bs_341_;
}
else
{
lean_object* v_v_343_; lean_object* v___x_344_; lean_object* v_bs_x27_345_; lean_object* v___x_346_; size_t v___x_347_; size_t v___x_348_; lean_object* v___x_349_; 
v_v_343_ = lean_array_uget(v_bs_341_, v_i_340_);
v___x_344_ = lean_unsigned_to_nat(0u);
v_bs_x27_345_ = lean_array_uset(v_bs_341_, v_i_340_, v___x_344_);
lean_inc_ref(v_major_338_);
lean_inc(v_declName_337_);
v___x_346_ = l_Lean_Expr_proj___override(v_declName_337_, v_v_343_, v_major_338_);
v___x_347_ = ((size_t)1ULL);
v___x_348_ = lean_usize_add(v_i_340_, v___x_347_);
v___x_349_ = lean_array_uset(v_bs_x27_345_, v_i_340_, v___x_346_);
v_i_340_ = v___x_348_;
v_bs_341_ = v___x_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mkCasesOnViaProjs_x3f_spec__3___boxed(lean_object* v_declName_351_, lean_object* v_major_352_, lean_object* v_sz_353_, lean_object* v_i_354_, lean_object* v_bs_355_){
_start:
{
size_t v_sz_boxed_356_; size_t v_i_boxed_357_; lean_object* v_res_358_; 
v_sz_boxed_356_ = lean_unbox_usize(v_sz_353_);
lean_dec(v_sz_353_);
v_i_boxed_357_ = lean_unbox_usize(v_i_354_);
lean_dec(v_i_354_);
v_res_358_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mkCasesOnViaProjs_x3f_spec__3(v_declName_351_, v_major_352_, v_sz_boxed_356_, v_i_boxed_357_, v_bs_355_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__0(lean_object* v_a_359_, lean_object* v_motive_360_, lean_object* v_minor_361_, lean_object* v___x_362_, uint8_t v_a_363_, uint8_t v___x_364_, lean_object* v_declName_365_, lean_object* v___x_366_, lean_object* v_levelParams_367_, lean_object* v_elimName_368_, lean_object* v_major_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_numFields_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; uint8_t v___x_383_; lean_object* v___x_384_; 
v_numFields_375_ = lean_ctor_get(v_a_359_, 4);
lean_inc(v_numFields_375_);
lean_dec_ref(v_a_359_);
v___x_376_ = lean_unsigned_to_nat(3u);
v___x_377_ = lean_mk_empty_array_with_capacity(v___x_376_);
lean_inc_ref(v_motive_360_);
v___x_378_ = lean_array_push(v___x_377_, v_motive_360_);
lean_inc_ref_n(v_major_369_, 2);
v___x_379_ = lean_array_push(v___x_378_, v_major_369_);
lean_inc_ref(v_minor_361_);
v___x_380_ = lean_array_push(v___x_379_, v_minor_361_);
v___x_381_ = l_Array_append___redArg(v___x_362_, v___x_380_);
lean_dec_ref(v___x_380_);
v___x_382_ = l_Lean_Expr_app___override(v_motive_360_, v_major_369_);
v___x_383_ = 1;
v___x_384_ = l_Lean_Meta_mkForallFVars(v___x_381_, v___x_382_, v_a_363_, v___x_364_, v___x_364_, v___x_383_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
if (lean_obj_tag(v___x_384_) == 0)
{
lean_object* v_a_385_; lean_object* v___x_386_; size_t v_sz_387_; size_t v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
v_a_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_a_385_);
lean_dec_ref_known(v___x_384_, 1);
v___x_386_ = l_Array_range(v_numFields_375_);
v_sz_387_ = lean_array_size(v___x_386_);
v___x_388_ = ((size_t)0ULL);
v___x_389_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_mkCasesOnViaProjs_x3f_spec__3(v_declName_365_, v_major_369_, v_sz_387_, v___x_388_, v___x_386_);
v___x_390_ = l_Lean_mkAppN(v_minor_361_, v___x_389_);
lean_dec_ref(v___x_389_);
v___x_391_ = l_Lean_Meta_mkLambdaFVars(v___x_381_, v___x_390_, v_a_363_, v___x_364_, v_a_363_, v___x_364_, v___x_383_, v___y_370_, v___y_371_, v___y_372_, v___y_373_);
lean_dec_ref(v___x_381_);
if (lean_obj_tag(v___x_391_) == 0)
{
lean_object* v_a_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v_a_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_404_; 
v_a_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_a_392_);
lean_dec_ref_known(v___x_391_, 1);
v___x_393_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_366_);
lean_ctor_set(v___x_393_, 1, v_levelParams_367_);
v___x_394_ = lean_box(1);
v___x_395_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnViaProjs_x3f_spec__4___redArg(v_elimName_368_, v___x_393_, v_a_385_, v_a_392_, v___x_394_, v___y_373_);
v_a_396_ = lean_ctor_get(v___x_395_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_395_);
if (v_isSharedCheck_404_ == 0)
{
v___x_398_ = v___x_395_;
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_a_396_);
lean_dec(v___x_395_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_404_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___x_400_; lean_object* v___x_402_; 
v___x_400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_400_, 0, v_a_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 0, v___x_400_);
v___x_402_ = v___x_398_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v___x_400_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
else
{
lean_object* v_a_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_412_; 
lean_dec(v_a_385_);
lean_dec(v_elimName_368_);
lean_dec(v_levelParams_367_);
lean_dec(v___x_366_);
v_a_405_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_412_ == 0)
{
v___x_407_ = v___x_391_;
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
else
{
lean_inc(v_a_405_);
lean_dec(v___x_391_);
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_412_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
lean_object* v___x_410_; 
if (v_isShared_408_ == 0)
{
v___x_410_ = v___x_407_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_a_405_);
v___x_410_ = v_reuseFailAlloc_411_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
return v___x_410_;
}
}
}
}
else
{
lean_object* v_a_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_420_; 
lean_dec_ref(v___x_381_);
lean_dec(v_numFields_375_);
lean_dec_ref(v_major_369_);
lean_dec(v_elimName_368_);
lean_dec(v_levelParams_367_);
lean_dec(v___x_366_);
lean_dec(v_declName_365_);
lean_dec_ref(v_minor_361_);
v_a_413_ = lean_ctor_get(v___x_384_, 0);
v_isSharedCheck_420_ = !lean_is_exclusive(v___x_384_);
if (v_isSharedCheck_420_ == 0)
{
v___x_415_ = v___x_384_;
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_a_413_);
lean_dec(v___x_384_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_420_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_418_; 
if (v_isShared_416_ == 0)
{
v___x_418_ = v___x_415_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v_a_413_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__0___boxed(lean_object* v_a_421_, lean_object* v_motive_422_, lean_object* v_minor_423_, lean_object* v___x_424_, lean_object* v_a_425_, lean_object* v___x_426_, lean_object* v_declName_427_, lean_object* v___x_428_, lean_object* v_levelParams_429_, lean_object* v_elimName_430_, lean_object* v_major_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
uint8_t v_a_10239__boxed_437_; uint8_t v___x_10240__boxed_438_; lean_object* v_res_439_; 
v_a_10239__boxed_437_ = lean_unbox(v_a_425_);
v___x_10240__boxed_438_ = lean_unbox(v___x_426_);
v_res_439_ = l_Lean_mkCasesOnViaProjs_x3f___lam__0(v_a_421_, v_motive_422_, v_minor_423_, v___x_424_, v_a_10239__boxed_437_, v___x_10240__boxed_438_, v_declName_427_, v___x_428_, v_levelParams_429_, v_elimName_430_, v_major_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec(v___y_435_);
lean_dec_ref(v___y_434_);
lean_dec(v___y_433_);
lean_dec_ref(v___y_432_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__1(lean_object* v_a_440_, lean_object* v_motive_441_, lean_object* v___x_442_, uint8_t v_a_443_, uint8_t v___x_444_, lean_object* v_declName_445_, lean_object* v___x_446_, lean_object* v_levelParams_447_, lean_object* v_elimName_448_, lean_object* v_binderName_449_, uint8_t v_binderInfo_450_, lean_object* v_binderType_451_, lean_object* v_minor_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___f_460_; uint8_t v___x_461_; lean_object* v___x_462_; 
v___x_458_ = lean_box(v_a_443_);
v___x_459_ = lean_box(v___x_444_);
v___f_460_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnViaProjs_x3f___lam__0___boxed), 16, 10);
lean_closure_set(v___f_460_, 0, v_a_440_);
lean_closure_set(v___f_460_, 1, v_motive_441_);
lean_closure_set(v___f_460_, 2, v_minor_452_);
lean_closure_set(v___f_460_, 3, v___x_442_);
lean_closure_set(v___f_460_, 4, v___x_458_);
lean_closure_set(v___f_460_, 5, v___x_459_);
lean_closure_set(v___f_460_, 6, v_declName_445_);
lean_closure_set(v___f_460_, 7, v___x_446_);
lean_closure_set(v___f_460_, 8, v_levelParams_447_);
lean_closure_set(v___f_460_, 9, v_elimName_448_);
v___x_461_ = 0;
v___x_462_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg(v_binderName_449_, v_binderInfo_450_, v_binderType_451_, v___f_460_, v___x_461_, v___y_453_, v___y_454_, v___y_455_, v___y_456_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__1___boxed(lean_object** _args){
lean_object* v_a_463_ = _args[0];
lean_object* v_motive_464_ = _args[1];
lean_object* v___x_465_ = _args[2];
lean_object* v_a_466_ = _args[3];
lean_object* v___x_467_ = _args[4];
lean_object* v_declName_468_ = _args[5];
lean_object* v___x_469_ = _args[6];
lean_object* v_levelParams_470_ = _args[7];
lean_object* v_elimName_471_ = _args[8];
lean_object* v_binderName_472_ = _args[9];
lean_object* v_binderInfo_473_ = _args[10];
lean_object* v_binderType_474_ = _args[11];
lean_object* v_minor_475_ = _args[12];
lean_object* v___y_476_ = _args[13];
lean_object* v___y_477_ = _args[14];
lean_object* v___y_478_ = _args[15];
lean_object* v___y_479_ = _args[16];
lean_object* v___y_480_ = _args[17];
_start:
{
uint8_t v_a_10358__boxed_481_; uint8_t v___x_10359__boxed_482_; uint8_t v_binderInfo_10362__boxed_483_; lean_object* v_res_484_; 
v_a_10358__boxed_481_ = lean_unbox(v_a_466_);
v___x_10359__boxed_482_ = lean_unbox(v___x_467_);
v_binderInfo_10362__boxed_483_ = lean_unbox(v_binderInfo_473_);
v_res_484_ = l_Lean_mkCasesOnViaProjs_x3f___lam__1(v_a_463_, v_motive_464_, v___x_465_, v_a_10358__boxed_481_, v___x_10359__boxed_482_, v_declName_468_, v___x_469_, v_levelParams_470_, v_elimName_471_, v_binderName_472_, v_binderInfo_10362__boxed_483_, v_binderType_474_, v_minor_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
lean_dec(v___y_479_);
lean_dec_ref(v___y_478_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__2(lean_object* v_a_485_, lean_object* v___x_486_, uint8_t v_a_487_, uint8_t v___x_488_, lean_object* v_declName_489_, lean_object* v___x_490_, lean_object* v_levelParams_491_, lean_object* v_elimName_492_, lean_object* v_binderName_493_, uint8_t v_binderInfo_494_, lean_object* v_binderType_495_, lean_object* v_a_496_, lean_object* v_a_497_, lean_object* v_motive_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___f_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; uint8_t v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; 
v___x_504_ = lean_box(v_a_487_);
v___x_505_ = lean_box(v___x_488_);
v___x_506_ = lean_box(v_binderInfo_494_);
lean_inc_ref(v_motive_498_);
v___f_507_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnViaProjs_x3f___lam__1___boxed), 18, 12);
lean_closure_set(v___f_507_, 0, v_a_485_);
lean_closure_set(v___f_507_, 1, v_motive_498_);
lean_closure_set(v___f_507_, 2, v___x_486_);
lean_closure_set(v___f_507_, 3, v___x_504_);
lean_closure_set(v___f_507_, 4, v___x_505_);
lean_closure_set(v___f_507_, 5, v_declName_489_);
lean_closure_set(v___f_507_, 6, v___x_490_);
lean_closure_set(v___f_507_, 7, v_levelParams_491_);
lean_closure_set(v___f_507_, 8, v_elimName_492_);
lean_closure_set(v___f_507_, 9, v_binderName_493_);
lean_closure_set(v___f_507_, 10, v___x_506_);
lean_closure_set(v___f_507_, 11, v_binderType_495_);
v___x_508_ = l_Lean_LocalDecl_type(v_a_496_);
v___x_509_ = l_Lean_LocalDecl_toExpr(v_a_497_);
v___x_510_ = l_Lean_Expr_replaceFVar(v___x_508_, v___x_509_, v_motive_498_);
lean_dec_ref(v_motive_498_);
lean_dec_ref(v___x_508_);
v___x_511_ = l_Lean_LocalDecl_userName(v_a_496_);
v___x_512_ = l_Lean_LocalDecl_binderInfo(v_a_496_);
v___x_513_ = 0;
v___x_514_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg(v___x_511_, v___x_512_, v___x_510_, v___f_507_, v___x_513_, v___y_499_, v___y_500_, v___y_501_, v___y_502_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__2___boxed(lean_object** _args){
lean_object* v_a_515_ = _args[0];
lean_object* v___x_516_ = _args[1];
lean_object* v_a_517_ = _args[2];
lean_object* v___x_518_ = _args[3];
lean_object* v_declName_519_ = _args[4];
lean_object* v___x_520_ = _args[5];
lean_object* v_levelParams_521_ = _args[6];
lean_object* v_elimName_522_ = _args[7];
lean_object* v_binderName_523_ = _args[8];
lean_object* v_binderInfo_524_ = _args[9];
lean_object* v_binderType_525_ = _args[10];
lean_object* v_a_526_ = _args[11];
lean_object* v_a_527_ = _args[12];
lean_object* v_motive_528_ = _args[13];
lean_object* v___y_529_ = _args[14];
lean_object* v___y_530_ = _args[15];
lean_object* v___y_531_ = _args[16];
lean_object* v___y_532_ = _args[17];
lean_object* v___y_533_ = _args[18];
_start:
{
uint8_t v_a_10407__boxed_534_; uint8_t v___x_10408__boxed_535_; uint8_t v_binderInfo_10411__boxed_536_; lean_object* v_res_537_; 
v_a_10407__boxed_534_ = lean_unbox(v_a_517_);
v___x_10408__boxed_535_ = lean_unbox(v___x_518_);
v_binderInfo_10411__boxed_536_ = lean_unbox(v_binderInfo_524_);
v_res_537_ = l_Lean_mkCasesOnViaProjs_x3f___lam__2(v_a_515_, v___x_516_, v_a_10407__boxed_534_, v___x_10408__boxed_535_, v_declName_519_, v___x_520_, v_levelParams_521_, v_elimName_522_, v_binderName_523_, v_binderInfo_10411__boxed_536_, v_binderType_525_, v_a_526_, v_a_527_, v_motive_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec_ref(v_a_526_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__3(lean_object* v___x_538_, lean_object* v_numParams_539_, lean_object* v___x_540_, lean_object* v___x_541_, lean_object* v___x_542_, lean_object* v_a_543_, uint8_t v_a_544_, uint8_t v___x_545_, lean_object* v_declName_546_, lean_object* v_levelParams_547_, lean_object* v_elimName_548_, lean_object* v_xs_549_, lean_object* v_majorType_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_556_ = lean_array_get_borrowed(v___x_538_, v_xs_549_, v_numParams_539_);
v___x_557_ = l_Lean_Expr_fvarId_x21(v___x_556_);
v___x_558_ = l_Lean_FVarId_getDecl___redArg(v___x_557_, v___y_551_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_560_ = lean_nat_add(v_numParams_539_, v___x_540_);
v___x_561_ = lean_array_get_borrowed(v___x_538_, v_xs_549_, v___x_560_);
lean_dec(v___x_560_);
v___x_562_ = l_Lean_Expr_fvarId_x21(v___x_561_);
v___x_563_ = l_Lean_FVarId_getDecl___redArg(v___x_562_, v___y_551_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_563_) == 0)
{
if (lean_obj_tag(v_majorType_550_) == 7)
{
lean_object* v_a_564_; lean_object* v_binderName_565_; lean_object* v_binderType_566_; uint8_t v_binderInfo_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_a_564_ = lean_ctor_get(v___x_563_, 0);
lean_inc(v_a_564_);
lean_dec_ref_known(v___x_563_, 1);
v_binderName_565_ = lean_ctor_get(v_majorType_550_, 0);
lean_inc(v_binderName_565_);
v_binderType_566_ = lean_ctor_get(v_majorType_550_, 1);
lean_inc_ref_n(v_binderType_566_, 2);
v_binderInfo_567_ = lean_ctor_get_uint8(v_majorType_550_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_majorType_550_, 3);
lean_inc(v___x_541_);
v___x_568_ = l_Lean_Level_param___override(v___x_541_);
v___x_569_ = l_Lean_Expr_sort___override(v___x_568_);
v___x_570_ = l_Lean_mkArrow(v_binderType_566_, v___x_569_, v___y_553_, v___y_554_);
if (lean_obj_tag(v___x_570_) == 0)
{
lean_object* v_a_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___f_576_; lean_object* v___x_577_; uint8_t v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; 
v_a_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc(v_a_571_);
lean_dec_ref_known(v___x_570_, 1);
v___x_572_ = l_Array_extract___redArg(v_xs_549_, v___x_542_, v_numParams_539_);
v___x_573_ = lean_box(v_a_544_);
v___x_574_ = lean_box(v___x_545_);
v___x_575_ = lean_box(v_binderInfo_567_);
lean_inc(v_a_559_);
v___f_576_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnViaProjs_x3f___lam__2___boxed), 19, 13);
lean_closure_set(v___f_576_, 0, v_a_543_);
lean_closure_set(v___f_576_, 1, v___x_572_);
lean_closure_set(v___f_576_, 2, v___x_573_);
lean_closure_set(v___f_576_, 3, v___x_574_);
lean_closure_set(v___f_576_, 4, v_declName_546_);
lean_closure_set(v___f_576_, 5, v___x_541_);
lean_closure_set(v___f_576_, 6, v_levelParams_547_);
lean_closure_set(v___f_576_, 7, v_elimName_548_);
lean_closure_set(v___f_576_, 8, v_binderName_565_);
lean_closure_set(v___f_576_, 9, v___x_575_);
lean_closure_set(v___f_576_, 10, v_binderType_566_);
lean_closure_set(v___f_576_, 11, v_a_564_);
lean_closure_set(v___f_576_, 12, v_a_559_);
v___x_577_ = l_Lean_LocalDecl_userName(v_a_559_);
v___x_578_ = l_Lean_LocalDecl_binderInfo(v_a_559_);
lean_dec(v_a_559_);
v___x_579_ = 0;
v___x_580_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnViaProjs_x3f_spec__5___redArg(v___x_577_, v___x_578_, v_a_571_, v___f_576_, v___x_579_, v___y_551_, v___y_552_, v___y_553_, v___y_554_);
return v___x_580_;
}
else
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v_binderType_566_);
lean_dec(v_binderName_565_);
lean_dec(v_a_564_);
lean_dec(v_a_559_);
lean_dec(v_elimName_548_);
lean_dec(v_levelParams_547_);
lean_dec(v_declName_546_);
lean_dec_ref(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_numParams_539_);
v_a_581_ = lean_ctor_get(v___x_570_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_570_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_570_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_570_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
}
else
{
lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_596_; 
lean_dec(v_a_559_);
lean_dec_ref(v_majorType_550_);
lean_dec(v_elimName_548_);
lean_dec(v_levelParams_547_);
lean_dec(v_declName_546_);
lean_dec_ref(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_numParams_539_);
v_isSharedCheck_596_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_596_ == 0)
{
lean_object* v_unused_597_; 
v_unused_597_ = lean_ctor_get(v___x_563_, 0);
lean_dec(v_unused_597_);
v___x_590_ = v___x_563_;
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
else
{
lean_dec(v___x_563_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_596_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_592_ = lean_box(0);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 0, v___x_592_);
v___x_594_ = v___x_590_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v___x_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
else
{
lean_object* v_a_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_605_; 
lean_dec(v_a_559_);
lean_dec_ref(v_majorType_550_);
lean_dec(v_elimName_548_);
lean_dec(v_levelParams_547_);
lean_dec(v_declName_546_);
lean_dec_ref(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_numParams_539_);
v_a_598_ = lean_ctor_get(v___x_563_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_563_);
if (v_isSharedCheck_605_ == 0)
{
v___x_600_ = v___x_563_;
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_a_598_);
lean_dec(v___x_563_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_605_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v___x_603_; 
if (v_isShared_601_ == 0)
{
v___x_603_ = v___x_600_;
goto v_reusejp_602_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_a_598_);
v___x_603_ = v_reuseFailAlloc_604_;
goto v_reusejp_602_;
}
v_reusejp_602_:
{
return v___x_603_;
}
}
}
}
else
{
lean_object* v_a_606_; lean_object* v___x_608_; uint8_t v_isShared_609_; uint8_t v_isSharedCheck_613_; 
lean_dec_ref(v_majorType_550_);
lean_dec(v_elimName_548_);
lean_dec(v_levelParams_547_);
lean_dec(v_declName_546_);
lean_dec_ref(v_a_543_);
lean_dec(v___x_542_);
lean_dec(v___x_541_);
lean_dec(v_numParams_539_);
v_a_606_ = lean_ctor_get(v___x_558_, 0);
v_isSharedCheck_613_ = !lean_is_exclusive(v___x_558_);
if (v_isSharedCheck_613_ == 0)
{
v___x_608_ = v___x_558_;
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
else
{
lean_inc(v_a_606_);
lean_dec(v___x_558_);
v___x_608_ = lean_box(0);
v_isShared_609_ = v_isSharedCheck_613_;
goto v_resetjp_607_;
}
v_resetjp_607_:
{
lean_object* v___x_611_; 
if (v_isShared_609_ == 0)
{
v___x_611_ = v___x_608_;
goto v_reusejp_610_;
}
else
{
lean_object* v_reuseFailAlloc_612_; 
v_reuseFailAlloc_612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_612_, 0, v_a_606_);
v___x_611_ = v_reuseFailAlloc_612_;
goto v_reusejp_610_;
}
v_reusejp_610_:
{
return v___x_611_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___lam__3___boxed(lean_object** _args){
lean_object* v___x_614_ = _args[0];
lean_object* v_numParams_615_ = _args[1];
lean_object* v___x_616_ = _args[2];
lean_object* v___x_617_ = _args[3];
lean_object* v___x_618_ = _args[4];
lean_object* v_a_619_ = _args[5];
lean_object* v_a_620_ = _args[6];
lean_object* v___x_621_ = _args[7];
lean_object* v_declName_622_ = _args[8];
lean_object* v_levelParams_623_ = _args[9];
lean_object* v_elimName_624_ = _args[10];
lean_object* v_xs_625_ = _args[11];
lean_object* v_majorType_626_ = _args[12];
lean_object* v___y_627_ = _args[13];
lean_object* v___y_628_ = _args[14];
lean_object* v___y_629_ = _args[15];
lean_object* v___y_630_ = _args[16];
lean_object* v___y_631_ = _args[17];
_start:
{
uint8_t v_a_10477__boxed_632_; uint8_t v___x_10478__boxed_633_; lean_object* v_res_634_; 
v_a_10477__boxed_632_ = lean_unbox(v_a_620_);
v___x_10478__boxed_633_ = lean_unbox(v___x_621_);
v_res_634_ = l_Lean_mkCasesOnViaProjs_x3f___lam__3(v___x_614_, v_numParams_615_, v___x_616_, v___x_617_, v___x_618_, v_a_619_, v_a_10477__boxed_632_, v___x_10478__boxed_633_, v_declName_622_, v_levelParams_623_, v_elimName_624_, v_xs_625_, v_majorType_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec_ref(v_xs_625_);
lean_dec(v___x_616_);
lean_dec_ref(v___x_614_);
return v_res_634_;
}
}
static lean_object* _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0(void){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_instMonadEIO(lean_box(0));
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3(lean_object* v_msg_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_toApplicative_648_; lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_709_; 
v___x_646_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0);
v___x_647_ = l_StateRefT_x27_instMonad___redArg(v___x_646_);
v_toApplicative_648_ = lean_ctor_get(v___x_647_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_647_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; 
v_unused_710_ = lean_ctor_get(v___x_647_, 1);
lean_dec(v_unused_710_);
v___x_650_ = v___x_647_;
v_isShared_651_ = v_isSharedCheck_709_;
goto v_resetjp_649_;
}
else
{
lean_inc(v_toApplicative_648_);
lean_dec(v___x_647_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_709_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
lean_object* v_toFunctor_652_; lean_object* v_toSeq_653_; lean_object* v_toSeqLeft_654_; lean_object* v_toSeqRight_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_707_; 
v_toFunctor_652_ = lean_ctor_get(v_toApplicative_648_, 0);
v_toSeq_653_ = lean_ctor_get(v_toApplicative_648_, 2);
v_toSeqLeft_654_ = lean_ctor_get(v_toApplicative_648_, 3);
v_toSeqRight_655_ = lean_ctor_get(v_toApplicative_648_, 4);
v_isSharedCheck_707_ = !lean_is_exclusive(v_toApplicative_648_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_toApplicative_648_, 1);
lean_dec(v_unused_708_);
v___x_657_ = v_toApplicative_648_;
v_isShared_658_ = v_isSharedCheck_707_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_toSeqRight_655_);
lean_inc(v_toSeqLeft_654_);
lean_inc(v_toSeq_653_);
lean_inc(v_toFunctor_652_);
lean_dec(v_toApplicative_648_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_707_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___f_659_; lean_object* v___f_660_; lean_object* v___f_661_; lean_object* v___f_662_; lean_object* v___x_663_; lean_object* v___f_664_; lean_object* v___f_665_; lean_object* v___f_666_; lean_object* v___x_668_; 
v___f_659_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__1));
v___f_660_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__2));
lean_inc_ref(v_toFunctor_652_);
v___f_661_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_661_, 0, v_toFunctor_652_);
v___f_662_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_662_, 0, v_toFunctor_652_);
v___x_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_663_, 0, v___f_661_);
lean_ctor_set(v___x_663_, 1, v___f_662_);
v___f_664_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_664_, 0, v_toSeqRight_655_);
v___f_665_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_665_, 0, v_toSeqLeft_654_);
v___f_666_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_666_, 0, v_toSeq_653_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 4, v___f_664_);
lean_ctor_set(v___x_657_, 3, v___f_665_);
lean_ctor_set(v___x_657_, 2, v___f_666_);
lean_ctor_set(v___x_657_, 1, v___f_659_);
lean_ctor_set(v___x_657_, 0, v___x_663_);
v___x_668_ = v___x_657_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v___x_663_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v___f_659_);
lean_ctor_set(v_reuseFailAlloc_706_, 2, v___f_666_);
lean_ctor_set(v_reuseFailAlloc_706_, 3, v___f_665_);
lean_ctor_set(v_reuseFailAlloc_706_, 4, v___f_664_);
v___x_668_ = v_reuseFailAlloc_706_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_670_; 
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 1, v___f_660_);
lean_ctor_set(v___x_650_, 0, v___x_668_);
v___x_670_ = v___x_650_;
goto v_reusejp_669_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_668_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v___f_660_);
v___x_670_ = v_reuseFailAlloc_705_;
goto v_reusejp_669_;
}
v_reusejp_669_:
{
lean_object* v___x_671_; lean_object* v_toApplicative_672_; lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_703_; 
v___x_671_ = l_StateRefT_x27_instMonad___redArg(v___x_670_);
v_toApplicative_672_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; 
v_unused_704_ = lean_ctor_get(v___x_671_, 1);
lean_dec(v_unused_704_);
v___x_674_ = v___x_671_;
v_isShared_675_ = v_isSharedCheck_703_;
goto v_resetjp_673_;
}
else
{
lean_inc(v_toApplicative_672_);
lean_dec(v___x_671_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_703_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_toFunctor_676_; lean_object* v_toSeq_677_; lean_object* v_toSeqLeft_678_; lean_object* v_toSeqRight_679_; lean_object* v___x_681_; uint8_t v_isShared_682_; uint8_t v_isSharedCheck_701_; 
v_toFunctor_676_ = lean_ctor_get(v_toApplicative_672_, 0);
v_toSeq_677_ = lean_ctor_get(v_toApplicative_672_, 2);
v_toSeqLeft_678_ = lean_ctor_get(v_toApplicative_672_, 3);
v_toSeqRight_679_ = lean_ctor_get(v_toApplicative_672_, 4);
v_isSharedCheck_701_ = !lean_is_exclusive(v_toApplicative_672_);
if (v_isSharedCheck_701_ == 0)
{
lean_object* v_unused_702_; 
v_unused_702_ = lean_ctor_get(v_toApplicative_672_, 1);
lean_dec(v_unused_702_);
v___x_681_ = v_toApplicative_672_;
v_isShared_682_ = v_isSharedCheck_701_;
goto v_resetjp_680_;
}
else
{
lean_inc(v_toSeqRight_679_);
lean_inc(v_toSeqLeft_678_);
lean_inc(v_toSeq_677_);
lean_inc(v_toFunctor_676_);
lean_dec(v_toApplicative_672_);
v___x_681_ = lean_box(0);
v_isShared_682_ = v_isSharedCheck_701_;
goto v_resetjp_680_;
}
v_resetjp_680_:
{
lean_object* v___f_683_; lean_object* v___f_684_; lean_object* v___f_685_; lean_object* v___f_686_; lean_object* v___x_687_; lean_object* v___f_688_; lean_object* v___f_689_; lean_object* v___f_690_; lean_object* v___x_692_; 
v___f_683_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__3));
v___f_684_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__4));
lean_inc_ref(v_toFunctor_676_);
v___f_685_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_685_, 0, v_toFunctor_676_);
v___f_686_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_686_, 0, v_toFunctor_676_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___f_685_);
lean_ctor_set(v___x_687_, 1, v___f_686_);
v___f_688_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_688_, 0, v_toSeqRight_679_);
v___f_689_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_689_, 0, v_toSeqLeft_678_);
v___f_690_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_690_, 0, v_toSeq_677_);
if (v_isShared_682_ == 0)
{
lean_ctor_set(v___x_681_, 4, v___f_688_);
lean_ctor_set(v___x_681_, 3, v___f_689_);
lean_ctor_set(v___x_681_, 2, v___f_690_);
lean_ctor_set(v___x_681_, 1, v___f_683_);
lean_ctor_set(v___x_681_, 0, v___x_687_);
v___x_692_ = v___x_681_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v___f_683_);
lean_ctor_set(v_reuseFailAlloc_700_, 2, v___f_690_);
lean_ctor_set(v_reuseFailAlloc_700_, 3, v___f_689_);
lean_ctor_set(v_reuseFailAlloc_700_, 4, v___f_688_);
v___x_692_ = v_reuseFailAlloc_700_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
lean_object* v___x_694_; 
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 1, v___f_684_);
lean_ctor_set(v___x_674_, 0, v___x_692_);
v___x_694_ = v___x_674_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_692_);
lean_ctor_set(v_reuseFailAlloc_699_, 1, v___f_684_);
v___x_694_ = v_reuseFailAlloc_699_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_7629__overap_697_; lean_object* v___x_698_; 
v___x_695_ = lean_box(0);
v___x_696_ = l_instInhabitedOfMonad___redArg(v___x_694_, v___x_695_);
v___x_7629__overap_697_ = lean_panic_fn_borrowed(v___x_696_, v_msg_640_);
lean_dec(v___x_696_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
v___x_698_ = lean_apply_5(v___x_7629__overap_697_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, lean_box(0));
return v___x_698_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___boxed(lean_object* v_msg_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3(v_msg_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2_spec__8(lean_object* v_msgData_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_){
_start:
{
lean_object* v___x_724_; lean_object* v_env_725_; lean_object* v___x_726_; lean_object* v_mctx_727_; lean_object* v_lctx_728_; lean_object* v_options_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_724_ = lean_st_ref_get(v___y_722_);
v_env_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc_ref(v_env_725_);
lean_dec(v___x_724_);
v___x_726_ = lean_st_ref_get(v___y_720_);
v_mctx_727_ = lean_ctor_get(v___x_726_, 0);
lean_inc_ref(v_mctx_727_);
lean_dec(v___x_726_);
v_lctx_728_ = lean_ctor_get(v___y_719_, 2);
v_options_729_ = lean_ctor_get(v___y_721_, 2);
lean_inc_ref(v_options_729_);
lean_inc_ref(v_lctx_728_);
v___x_730_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_730_, 0, v_env_725_);
lean_ctor_set(v___x_730_, 1, v_mctx_727_);
lean_ctor_set(v___x_730_, 2, v_lctx_728_);
lean_ctor_set(v___x_730_, 3, v_options_729_);
v___x_731_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_730_);
lean_ctor_set(v___x_731_, 1, v_msgData_718_);
v___x_732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_732_, 0, v___x_731_);
return v___x_732_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2_spec__8___boxed(lean_object* v_msgData_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2_spec__8(v_msgData_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(lean_object* v_msg_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v_ref_746_; lean_object* v___x_747_; lean_object* v_a_748_; lean_object* v___x_750_; uint8_t v_isShared_751_; uint8_t v_isSharedCheck_756_; 
v_ref_746_ = lean_ctor_get(v___y_743_, 5);
v___x_747_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2_spec__8(v_msg_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
v_a_748_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_756_ == 0)
{
v___x_750_ = v___x_747_;
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
else
{
lean_inc(v_a_748_);
lean_dec(v___x_747_);
v___x_750_ = lean_box(0);
v_isShared_751_ = v_isSharedCheck_756_;
goto v_resetjp_749_;
}
v_resetjp_749_:
{
lean_object* v___x_752_; lean_object* v___x_754_; 
lean_inc(v_ref_746_);
v___x_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_752_, 0, v_ref_746_);
lean_ctor_set(v___x_752_, 1, v_a_748_);
if (v_isShared_751_ == 0)
{
lean_ctor_set_tag(v___x_750_, 1);
lean_ctor_set(v___x_750_, 0, v___x_752_);
v___x_754_ = v___x_750_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v___x_752_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg___boxed(lean_object* v_msg_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v_res_763_; 
v_res_763_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(v_msg_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_763_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__0));
v___x_766_ = l_Lean_stringToMessageData(v___x_765_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__3(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_768_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__2));
v___x_769_ = l_Lean_stringToMessageData(v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__7(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; 
v___x_773_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__6));
v___x_774_ = lean_unsigned_to_nat(11u);
v___x_775_ = lean_unsigned_to_nat(129u);
v___x_776_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__5));
v___x_777_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__4));
v___x_778_ = l_mkPanicMessageWithDecl(v___x_777_, v___x_776_, v___x_775_, v___x_774_, v___x_773_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1(lean_object* v_constName_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_){
_start:
{
lean_object* v___x_793_; lean_object* v_env_794_; uint8_t v___x_795_; lean_object* v___x_796_; 
v___x_793_ = lean_st_ref_get(v___y_783_);
v_env_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_ref(v_env_794_);
lean_dec(v___x_793_);
v___x_795_ = 0;
lean_inc(v_constName_779_);
v___x_796_ = l_Lean_Environment_findAsync_x3f(v_env_794_, v_constName_779_, v___x_795_);
if (lean_obj_tag(v___x_796_) == 1)
{
lean_object* v_val_797_; uint8_t v_kind_798_; 
v_val_797_ = lean_ctor_get(v___x_796_, 0);
lean_inc(v_val_797_);
lean_dec_ref_known(v___x_796_, 1);
v_kind_798_ = lean_ctor_get_uint8(v_val_797_, sizeof(void*)*3);
if (v_kind_798_ == 7)
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_797_);
if (lean_obj_tag(v___x_799_) == 7)
{
lean_object* v_val_800_; lean_object* v___x_802_; uint8_t v_isShared_803_; uint8_t v_isSharedCheck_807_; 
lean_dec(v_constName_779_);
v_val_800_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_807_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_807_ == 0)
{
v___x_802_ = v___x_799_;
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
else
{
lean_inc(v_val_800_);
lean_dec(v___x_799_);
v___x_802_ = lean_box(0);
v_isShared_803_ = v_isSharedCheck_807_;
goto v_resetjp_801_;
}
v_resetjp_801_:
{
lean_object* v___x_805_; 
if (v_isShared_803_ == 0)
{
lean_ctor_set_tag(v___x_802_, 0);
v___x_805_ = v___x_802_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v_val_800_);
v___x_805_ = v_reuseFailAlloc_806_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
return v___x_805_;
}
}
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec_ref(v___x_799_);
v___x_808_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__7, &l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__7_once, _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__7);
v___x_809_ = l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3(v___x_808_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_818_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_818_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_818_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
if (lean_obj_tag(v_a_810_) == 0)
{
lean_del_object(v___x_812_);
goto v___jp_785_;
}
else
{
lean_object* v_val_814_; lean_object* v___x_816_; 
lean_dec(v_constName_779_);
v_val_814_ = lean_ctor_get(v_a_810_, 0);
lean_inc(v_val_814_);
lean_dec_ref_known(v_a_810_, 1);
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 0, v_val_814_);
v___x_816_ = v___x_812_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_val_814_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_constName_779_);
v_a_819_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_809_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_809_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
lean_object* v___x_824_; 
if (v_isShared_822_ == 0)
{
v___x_824_ = v___x_821_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_825_; 
v_reuseFailAlloc_825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_825_, 0, v_a_819_);
v___x_824_ = v_reuseFailAlloc_825_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
return v___x_824_;
}
}
}
}
}
else
{
lean_dec(v_val_797_);
goto v___jp_785_;
}
}
else
{
lean_dec(v___x_796_);
goto v___jp_785_;
}
v___jp_785_:
{
lean_object* v___x_786_; uint8_t v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_786_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1, &l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1);
v___x_787_ = 0;
v___x_788_ = l_Lean_MessageData_ofConstName(v_constName_779_, v___x_787_);
v___x_789_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_786_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__3, &l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__3_once, _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__3);
v___x_791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_791_, 0, v___x_789_);
lean_ctor_set(v___x_791_, 1, v___x_790_);
v___x_792_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(v___x_791_, v___y_780_, v___y_781_, v___y_782_, v___y_783_);
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___boxed(lean_object* v_constName_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1(v_constName_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2_spec__5(lean_object* v_msg_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v_toApplicative_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_903_; 
v___x_840_ = lean_obj_once(&l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0, &l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0_once, _init_l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__0);
v___x_841_ = l_StateRefT_x27_instMonad___redArg(v___x_840_);
v_toApplicative_842_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_903_ == 0)
{
lean_object* v_unused_904_; 
v_unused_904_ = lean_ctor_get(v___x_841_, 1);
lean_dec(v_unused_904_);
v___x_844_ = v___x_841_;
v_isShared_845_ = v_isSharedCheck_903_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_toApplicative_842_);
lean_dec(v___x_841_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_903_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_toFunctor_846_; lean_object* v_toSeq_847_; lean_object* v_toSeqLeft_848_; lean_object* v_toSeqRight_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_901_; 
v_toFunctor_846_ = lean_ctor_get(v_toApplicative_842_, 0);
v_toSeq_847_ = lean_ctor_get(v_toApplicative_842_, 2);
v_toSeqLeft_848_ = lean_ctor_get(v_toApplicative_842_, 3);
v_toSeqRight_849_ = lean_ctor_get(v_toApplicative_842_, 4);
v_isSharedCheck_901_ = !lean_is_exclusive(v_toApplicative_842_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_toApplicative_842_, 1);
lean_dec(v_unused_902_);
v___x_851_ = v_toApplicative_842_;
v_isShared_852_ = v_isSharedCheck_901_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_toSeqRight_849_);
lean_inc(v_toSeqLeft_848_);
lean_inc(v_toSeq_847_);
lean_inc(v_toFunctor_846_);
lean_dec(v_toApplicative_842_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_901_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___f_853_; lean_object* v___f_854_; lean_object* v___f_855_; lean_object* v___f_856_; lean_object* v___x_857_; lean_object* v___f_858_; lean_object* v___f_859_; lean_object* v___f_860_; lean_object* v___x_862_; 
v___f_853_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__1));
v___f_854_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__2));
lean_inc_ref(v_toFunctor_846_);
v___f_855_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_855_, 0, v_toFunctor_846_);
v___f_856_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_856_, 0, v_toFunctor_846_);
v___x_857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_857_, 0, v___f_855_);
lean_ctor_set(v___x_857_, 1, v___f_856_);
v___f_858_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_858_, 0, v_toSeqRight_849_);
v___f_859_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_859_, 0, v_toSeqLeft_848_);
v___f_860_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_860_, 0, v_toSeq_847_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 4, v___f_858_);
lean_ctor_set(v___x_851_, 3, v___f_859_);
lean_ctor_set(v___x_851_, 2, v___f_860_);
lean_ctor_set(v___x_851_, 1, v___f_853_);
lean_ctor_set(v___x_851_, 0, v___x_857_);
v___x_862_ = v___x_851_;
goto v_reusejp_861_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v___f_853_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v___f_860_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v___f_859_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v___f_858_);
v___x_862_ = v_reuseFailAlloc_900_;
goto v_reusejp_861_;
}
v_reusejp_861_:
{
lean_object* v___x_864_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v___f_854_);
lean_ctor_set(v___x_844_, 0, v___x_862_);
v___x_864_ = v___x_844_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_899_; 
v_reuseFailAlloc_899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_899_, 0, v___x_862_);
lean_ctor_set(v_reuseFailAlloc_899_, 1, v___f_854_);
v___x_864_ = v_reuseFailAlloc_899_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_865_; lean_object* v_toApplicative_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_897_; 
v___x_865_ = l_StateRefT_x27_instMonad___redArg(v___x_864_);
v_toApplicative_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_897_ == 0)
{
lean_object* v_unused_898_; 
v_unused_898_ = lean_ctor_get(v___x_865_, 1);
lean_dec(v_unused_898_);
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_897_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_toApplicative_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_897_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_toFunctor_870_; lean_object* v_toSeq_871_; lean_object* v_toSeqLeft_872_; lean_object* v_toSeqRight_873_; lean_object* v___x_875_; uint8_t v_isShared_876_; uint8_t v_isSharedCheck_895_; 
v_toFunctor_870_ = lean_ctor_get(v_toApplicative_866_, 0);
v_toSeq_871_ = lean_ctor_get(v_toApplicative_866_, 2);
v_toSeqLeft_872_ = lean_ctor_get(v_toApplicative_866_, 3);
v_toSeqRight_873_ = lean_ctor_get(v_toApplicative_866_, 4);
v_isSharedCheck_895_ = !lean_is_exclusive(v_toApplicative_866_);
if (v_isSharedCheck_895_ == 0)
{
lean_object* v_unused_896_; 
v_unused_896_ = lean_ctor_get(v_toApplicative_866_, 1);
lean_dec(v_unused_896_);
v___x_875_ = v_toApplicative_866_;
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
else
{
lean_inc(v_toSeqRight_873_);
lean_inc(v_toSeqLeft_872_);
lean_inc(v_toSeq_871_);
lean_inc(v_toFunctor_870_);
lean_dec(v_toApplicative_866_);
v___x_875_ = lean_box(0);
v_isShared_876_ = v_isSharedCheck_895_;
goto v_resetjp_874_;
}
v_resetjp_874_:
{
lean_object* v___f_877_; lean_object* v___f_878_; lean_object* v___f_879_; lean_object* v___f_880_; lean_object* v___x_881_; lean_object* v___f_882_; lean_object* v___f_883_; lean_object* v___f_884_; lean_object* v___x_886_; 
v___f_877_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__3));
v___f_878_ = ((lean_object*)(l_panic___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__3___closed__4));
lean_inc_ref(v_toFunctor_870_);
v___f_879_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_879_, 0, v_toFunctor_870_);
v___f_880_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_880_, 0, v_toFunctor_870_);
v___x_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_881_, 0, v___f_879_);
lean_ctor_set(v___x_881_, 1, v___f_880_);
v___f_882_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_882_, 0, v_toSeqRight_873_);
v___f_883_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_883_, 0, v_toSeqLeft_872_);
v___f_884_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_884_, 0, v_toSeq_871_);
if (v_isShared_876_ == 0)
{
lean_ctor_set(v___x_875_, 4, v___f_882_);
lean_ctor_set(v___x_875_, 3, v___f_883_);
lean_ctor_set(v___x_875_, 2, v___f_884_);
lean_ctor_set(v___x_875_, 1, v___f_877_);
lean_ctor_set(v___x_875_, 0, v___x_881_);
v___x_886_ = v___x_875_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v___x_881_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v___f_877_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v___f_884_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v___f_883_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v___f_882_);
v___x_886_ = v_reuseFailAlloc_894_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_888_; 
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 1, v___f_878_);
lean_ctor_set(v___x_868_, 0, v___x_886_);
v___x_888_ = v___x_868_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_893_; 
v_reuseFailAlloc_893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_893_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_893_, 1, v___f_878_);
v___x_888_ = v_reuseFailAlloc_893_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_7641__overap_891_; lean_object* v___x_892_; 
v___x_889_ = lean_box(0);
v___x_890_ = l_instInhabitedOfMonad___redArg(v___x_888_, v___x_889_);
v___x_7641__overap_891_ = lean_panic_fn_borrowed(v___x_890_, v_msg_834_);
lean_dec(v___x_890_);
lean_inc(v___y_838_);
lean_inc_ref(v___y_837_);
lean_inc(v___y_836_);
lean_inc_ref(v___y_835_);
v___x_892_ = lean_apply_5(v___x_7641__overap_891_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, lean_box(0));
return v___x_892_;
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2_spec__5___boxed(lean_object* v_msg_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2_spec__5(v_msg_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
return v_res_911_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__1(void){
_start:
{
lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_913_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__0));
v___x_914_ = l_Lean_stringToMessageData(v___x_913_);
return v___x_914_;
}
}
static lean_object* _init_l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__3(void){
_start:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_916_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__6));
v___x_917_ = lean_unsigned_to_nat(11u);
v___x_918_ = lean_unsigned_to_nat(122u);
v___x_919_ = ((lean_object*)(l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__2));
v___x_920_ = ((lean_object*)(l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__4));
v___x_921_ = l_mkPanicMessageWithDecl(v___x_920_, v___x_919_, v___x_918_, v___x_917_, v___x_916_);
return v___x_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2(lean_object* v_constName_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_936_; lean_object* v_env_937_; uint8_t v___x_938_; lean_object* v___x_939_; 
v___x_936_ = lean_st_ref_get(v___y_926_);
v_env_937_ = lean_ctor_get(v___x_936_, 0);
lean_inc_ref(v_env_937_);
lean_dec(v___x_936_);
v___x_938_ = 0;
lean_inc(v_constName_922_);
v___x_939_ = l_Lean_Environment_findAsync_x3f(v_env_937_, v_constName_922_, v___x_938_);
if (lean_obj_tag(v___x_939_) == 1)
{
lean_object* v_val_940_; uint8_t v_kind_941_; 
v_val_940_ = lean_ctor_get(v___x_939_, 0);
lean_inc(v_val_940_);
lean_dec_ref_known(v___x_939_, 1);
v_kind_941_ = lean_ctor_get_uint8(v_val_940_, sizeof(void*)*3);
if (v_kind_941_ == 6)
{
lean_object* v___x_942_; 
v___x_942_ = l_Lean_AsyncConstantInfo_toConstantInfo(v_val_940_);
if (lean_obj_tag(v___x_942_) == 6)
{
lean_object* v_val_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_constName_922_);
v_val_943_ = lean_ctor_get(v___x_942_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_942_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_942_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_val_943_);
lean_dec(v___x_942_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
lean_ctor_set_tag(v___x_945_, 0);
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_val_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
lean_dec_ref(v___x_942_);
v___x_951_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__3, &l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__3_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__3);
v___x_952_ = l_panic___at___00Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2_spec__5(v___x_951_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_961_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_961_ == 0)
{
v___x_955_ = v___x_952_;
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_952_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_961_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
if (lean_obj_tag(v_a_953_) == 0)
{
lean_del_object(v___x_955_);
goto v___jp_928_;
}
else
{
lean_object* v_val_957_; lean_object* v___x_959_; 
lean_dec(v_constName_922_);
v_val_957_ = lean_ctor_get(v_a_953_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_a_953_, 1);
if (v_isShared_956_ == 0)
{
lean_ctor_set(v___x_955_, 0, v_val_957_);
v___x_959_ = v___x_955_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_val_957_);
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
else
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_969_; 
lean_dec(v_constName_922_);
v_a_962_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_969_ == 0)
{
v___x_964_ = v___x_952_;
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_952_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_969_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_967_; 
if (v_isShared_965_ == 0)
{
v___x_967_ = v___x_964_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v_a_962_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
}
else
{
lean_dec(v_val_940_);
goto v___jp_928_;
}
}
else
{
lean_dec(v___x_939_);
goto v___jp_928_;
}
v___jp_928_:
{
lean_object* v___x_929_; uint8_t v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_929_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1, &l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1);
v___x_930_ = 0;
v___x_931_ = l_Lean_MessageData_ofConstName(v_constName_922_, v___x_930_);
v___x_932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_932_, 0, v___x_929_);
lean_ctor_set(v___x_932_, 1, v___x_931_);
v___x_933_ = lean_obj_once(&l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__1, &l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__1_once, _init_l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___closed__1);
v___x_934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_932_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(v___x_934_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_935_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2___boxed(lean_object* v_constName_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2(v_constName_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___redArg(lean_object* v_ref_977_, lean_object* v_msg_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_fileName_984_; lean_object* v_fileMap_985_; lean_object* v_options_986_; lean_object* v_currRecDepth_987_; lean_object* v_maxRecDepth_988_; lean_object* v_ref_989_; lean_object* v_currNamespace_990_; lean_object* v_openDecls_991_; lean_object* v_initHeartbeats_992_; lean_object* v_maxHeartbeats_993_; lean_object* v_quotContext_994_; lean_object* v_currMacroScope_995_; uint8_t v_diag_996_; lean_object* v_cancelTk_x3f_997_; uint8_t v_suppressElabErrors_998_; lean_object* v_inheritedTraceOptions_999_; lean_object* v_ref_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v_fileName_984_ = lean_ctor_get(v___y_981_, 0);
v_fileMap_985_ = lean_ctor_get(v___y_981_, 1);
v_options_986_ = lean_ctor_get(v___y_981_, 2);
v_currRecDepth_987_ = lean_ctor_get(v___y_981_, 3);
v_maxRecDepth_988_ = lean_ctor_get(v___y_981_, 4);
v_ref_989_ = lean_ctor_get(v___y_981_, 5);
v_currNamespace_990_ = lean_ctor_get(v___y_981_, 6);
v_openDecls_991_ = lean_ctor_get(v___y_981_, 7);
v_initHeartbeats_992_ = lean_ctor_get(v___y_981_, 8);
v_maxHeartbeats_993_ = lean_ctor_get(v___y_981_, 9);
v_quotContext_994_ = lean_ctor_get(v___y_981_, 10);
v_currMacroScope_995_ = lean_ctor_get(v___y_981_, 11);
v_diag_996_ = lean_ctor_get_uint8(v___y_981_, sizeof(void*)*14);
v_cancelTk_x3f_997_ = lean_ctor_get(v___y_981_, 12);
v_suppressElabErrors_998_ = lean_ctor_get_uint8(v___y_981_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_999_ = lean_ctor_get(v___y_981_, 13);
v_ref_1000_ = l_Lean_replaceRef(v_ref_977_, v_ref_989_);
lean_inc_ref(v_inheritedTraceOptions_999_);
lean_inc(v_cancelTk_x3f_997_);
lean_inc(v_currMacroScope_995_);
lean_inc(v_quotContext_994_);
lean_inc(v_maxHeartbeats_993_);
lean_inc(v_initHeartbeats_992_);
lean_inc(v_openDecls_991_);
lean_inc(v_currNamespace_990_);
lean_inc(v_maxRecDepth_988_);
lean_inc(v_currRecDepth_987_);
lean_inc_ref(v_options_986_);
lean_inc_ref(v_fileMap_985_);
lean_inc_ref(v_fileName_984_);
v___x_1001_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1001_, 0, v_fileName_984_);
lean_ctor_set(v___x_1001_, 1, v_fileMap_985_);
lean_ctor_set(v___x_1001_, 2, v_options_986_);
lean_ctor_set(v___x_1001_, 3, v_currRecDepth_987_);
lean_ctor_set(v___x_1001_, 4, v_maxRecDepth_988_);
lean_ctor_set(v___x_1001_, 5, v_ref_1000_);
lean_ctor_set(v___x_1001_, 6, v_currNamespace_990_);
lean_ctor_set(v___x_1001_, 7, v_openDecls_991_);
lean_ctor_set(v___x_1001_, 8, v_initHeartbeats_992_);
lean_ctor_set(v___x_1001_, 9, v_maxHeartbeats_993_);
lean_ctor_set(v___x_1001_, 10, v_quotContext_994_);
lean_ctor_set(v___x_1001_, 11, v_currMacroScope_995_);
lean_ctor_set(v___x_1001_, 12, v_cancelTk_x3f_997_);
lean_ctor_set(v___x_1001_, 13, v_inheritedTraceOptions_999_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*14, v_diag_996_);
lean_ctor_set_uint8(v___x_1001_, sizeof(void*)*14 + 1, v_suppressElabErrors_998_);
v___x_1002_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(v_msg_978_, v___y_979_, v___y_980_, v___x_1001_, v___y_982_);
lean_dec_ref_known(v___x_1001_, 14);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___redArg___boxed(lean_object* v_ref_1003_, lean_object* v_msg_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___redArg(v_ref_1003_, v_msg_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
lean_dec(v___y_1008_);
lean_dec_ref(v___y_1007_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v_ref_1003_);
return v_res_1010_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__0(void){
_start:
{
lean_object* v___x_1011_; 
v___x_1011_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1011_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1(void){
_start:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__0);
v___x_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
return v___x_1013_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__2(void){
_start:
{
lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; 
v___x_1014_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1);
v___x_1015_ = lean_unsigned_to_nat(0u);
v___x_1016_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1016_, 0, v___x_1015_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_ctor_set(v___x_1016_, 2, v___x_1015_);
lean_ctor_set(v___x_1016_, 3, v___x_1015_);
lean_ctor_set(v___x_1016_, 4, v___x_1014_);
lean_ctor_set(v___x_1016_, 5, v___x_1014_);
lean_ctor_set(v___x_1016_, 6, v___x_1014_);
lean_ctor_set(v___x_1016_, 7, v___x_1014_);
lean_ctor_set(v___x_1016_, 8, v___x_1014_);
lean_ctor_set(v___x_1016_, 9, v___x_1014_);
lean_ctor_set(v___x_1016_, 10, v___x_1014_);
return v___x_1016_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__3(void){
_start:
{
lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1017_ = lean_unsigned_to_nat(32u);
v___x_1018_ = lean_mk_empty_array_with_capacity(v___x_1017_);
v___x_1019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1019_, 0, v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4(void){
_start:
{
size_t v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1020_ = ((size_t)5ULL);
v___x_1021_ = lean_unsigned_to_nat(0u);
v___x_1022_ = lean_unsigned_to_nat(32u);
v___x_1023_ = lean_mk_empty_array_with_capacity(v___x_1022_);
v___x_1024_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__3);
v___x_1025_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1025_, 0, v___x_1024_);
lean_ctor_set(v___x_1025_, 1, v___x_1023_);
lean_ctor_set(v___x_1025_, 2, v___x_1021_);
lean_ctor_set(v___x_1025_, 3, v___x_1021_);
lean_ctor_set_usize(v___x_1025_, 4, v___x_1020_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__5(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1026_ = lean_box(1);
v___x_1027_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4);
v___x_1028_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__1);
v___x_1029_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
lean_ctor_set(v___x_1029_, 1, v___x_1027_);
lean_ctor_set(v___x_1029_, 2, v___x_1026_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__6));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__9(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__8));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__11(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__10));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__13(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__12));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__15(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__14));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__17(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__16));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__19(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__18));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg(lean_object* v_msg_1051_, lean_object* v_declHint_1052_, lean_object* v___y_1053_){
_start:
{
lean_object* v___x_1055_; lean_object* v_env_1056_; uint8_t v___x_1057_; 
v___x_1055_ = lean_st_ref_get(v___y_1053_);
v_env_1056_ = lean_ctor_get(v___x_1055_, 0);
lean_inc_ref(v_env_1056_);
lean_dec(v___x_1055_);
v___x_1057_ = l_Lean_Name_isAnonymous(v_declHint_1052_);
if (v___x_1057_ == 0)
{
uint8_t v_isExporting_1058_; 
v_isExporting_1058_ = lean_ctor_get_uint8(v_env_1056_, sizeof(void*)*8);
if (v_isExporting_1058_ == 0)
{
lean_object* v___x_1059_; 
lean_dec_ref(v_env_1056_);
lean_dec(v_declHint_1052_);
v___x_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1059_, 0, v_msg_1051_);
return v___x_1059_;
}
else
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
lean_inc_ref(v_env_1056_);
v___x_1060_ = l_Lean_Environment_setExporting(v_env_1056_, v___x_1057_);
lean_inc(v_declHint_1052_);
lean_inc_ref(v___x_1060_);
v___x_1061_ = l_Lean_Environment_contains(v___x_1060_, v_declHint_1052_, v_isExporting_1058_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_dec_ref(v___x_1060_);
lean_dec_ref(v_env_1056_);
lean_dec(v_declHint_1052_);
v___x_1062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1062_, 0, v_msg_1051_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v_c_1068_; lean_object* v___x_1069_; 
v___x_1063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__2);
v___x_1064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__5);
v___x_1065_ = l_Lean_Options_empty;
v___x_1066_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1060_);
lean_ctor_set(v___x_1066_, 1, v___x_1063_);
lean_ctor_set(v___x_1066_, 2, v___x_1064_);
lean_ctor_set(v___x_1066_, 3, v___x_1065_);
lean_inc(v_declHint_1052_);
v___x_1067_ = l_Lean_MessageData_ofConstName(v_declHint_1052_, v___x_1057_);
v_c_1068_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1068_, 0, v___x_1066_);
lean_ctor_set(v_c_1068_, 1, v___x_1067_);
v___x_1069_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1056_, v_declHint_1052_);
if (lean_obj_tag(v___x_1069_) == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
lean_dec_ref(v_env_1056_);
lean_dec(v_declHint_1052_);
v___x_1070_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7);
v___x_1071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_c_1068_);
v___x_1072_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__9);
v___x_1073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1071_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = l_Lean_MessageData_note(v___x_1073_);
v___x_1075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1075_, 0, v_msg_1051_);
lean_ctor_set(v___x_1075_, 1, v___x_1074_);
v___x_1076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1076_, 0, v___x_1075_);
return v___x_1076_;
}
else
{
lean_object* v_val_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1112_; 
v_val_1077_ = lean_ctor_get(v___x_1069_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1069_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1079_ = v___x_1069_;
v_isShared_1080_ = v_isSharedCheck_1112_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_val_1077_);
lean_dec(v___x_1069_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1112_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v_mod_1084_; uint8_t v___x_1085_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Lean_Environment_header(v_env_1056_);
lean_dec_ref(v_env_1056_);
v___x_1083_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1082_);
v_mod_1084_ = lean_array_get(v___x_1081_, v___x_1083_, v_val_1077_);
lean_dec(v_val_1077_);
lean_dec_ref(v___x_1083_);
v___x_1085_ = l_Lean_isPrivateName(v_declHint_1052_);
lean_dec(v_declHint_1052_);
if (v___x_1085_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1086_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__11);
v___x_1087_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_c_1068_);
v___x_1088_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__13);
v___x_1089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1087_);
lean_ctor_set(v___x_1089_, 1, v___x_1088_);
v___x_1090_ = l_Lean_MessageData_ofName(v_mod_1084_);
v___x_1091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1089_);
lean_ctor_set(v___x_1091_, 1, v___x_1090_);
v___x_1092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__15);
v___x_1093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1091_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_MessageData_note(v___x_1093_);
v___x_1095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_msg_1051_);
lean_ctor_set(v___x_1095_, 1, v___x_1094_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1095_);
v___x_1097_ = v___x_1079_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
else
{
lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__7);
v___x_1100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1100_, 0, v___x_1099_);
lean_ctor_set(v___x_1100_, 1, v_c_1068_);
v___x_1101_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__17);
v___x_1102_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1100_);
lean_ctor_set(v___x_1102_, 1, v___x_1101_);
v___x_1103_ = l_Lean_MessageData_ofName(v_mod_1084_);
v___x_1104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
v___x_1105_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__19);
v___x_1106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1104_);
lean_ctor_set(v___x_1106_, 1, v___x_1105_);
v___x_1107_ = l_Lean_MessageData_note(v___x_1106_);
v___x_1108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1108_, 0, v_msg_1051_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
if (v_isShared_1080_ == 0)
{
lean_ctor_set_tag(v___x_1079_, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1108_);
v___x_1110_ = v___x_1079_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1113_; 
lean_dec_ref(v_env_1056_);
lean_dec(v_declHint_1052_);
v___x_1113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1113_, 0, v_msg_1051_);
return v___x_1113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___boxed(lean_object* v_msg_1114_, lean_object* v_declHint_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_){
_start:
{
lean_object* v_res_1118_; 
v_res_1118_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg(v_msg_1114_, v_declHint_1115_, v___y_1116_);
lean_dec(v___y_1116_);
return v_res_1118_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14(lean_object* v_msg_1119_, lean_object* v_declHint_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_, lean_object* v___y_1124_){
_start:
{
lean_object* v___x_1126_; lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1136_; 
v___x_1126_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg(v_msg_1119_, v_declHint_1120_, v___y_1124_);
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1136_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v___x_1131_ = l_Lean_unknownIdentifierMessageTag;
v___x_1132_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
lean_ctor_set(v___x_1132_, 1, v_a_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v___x_1132_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14___boxed(lean_object* v_msg_1137_, lean_object* v_declHint_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14(v_msg_1137_, v_declHint_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___redArg(lean_object* v_ref_1145_, lean_object* v_msg_1146_, lean_object* v_declHint_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_, lean_object* v___y_1151_){
_start:
{
lean_object* v___x_1153_; lean_object* v_a_1154_; lean_object* v___x_1155_; 
v___x_1153_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14(v_msg_1146_, v_declHint_1147_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
v_a_1154_ = lean_ctor_get(v___x_1153_, 0);
lean_inc(v_a_1154_);
lean_dec_ref(v___x_1153_);
v___x_1155_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___redArg(v_ref_1145_, v_a_1154_, v___y_1148_, v___y_1149_, v___y_1150_, v___y_1151_);
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___redArg___boxed(lean_object* v_ref_1156_, lean_object* v_msg_1157_, lean_object* v_declHint_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___redArg(v_ref_1156_, v_msg_1157_, v_declHint_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v_ref_1156_);
return v_res_1164_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; 
v___x_1166_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__0));
v___x_1167_ = l_Lean_stringToMessageData(v___x_1166_);
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg(lean_object* v_ref_1168_, lean_object* v_constName_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v___x_1175_; uint8_t v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1175_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___closed__1);
v___x_1176_ = 0;
lean_inc(v_constName_1169_);
v___x_1177_ = l_Lean_MessageData_ofConstName(v_constName_1169_, v___x_1176_);
v___x_1178_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1175_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = lean_obj_once(&l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1, &l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1_once, _init_l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1___closed__1);
v___x_1180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1178_);
lean_ctor_set(v___x_1180_, 1, v___x_1179_);
v___x_1181_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___redArg(v_ref_1168_, v___x_1180_, v_constName_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_ref_1182_, lean_object* v_constName_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg(v_ref_1182_, v_constName_1183_, v___y_1184_, v___y_1185_, v___y_1186_, v___y_1187_);
lean_dec(v___y_1187_);
lean_dec_ref(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec_ref(v___y_1184_);
lean_dec(v_ref_1182_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___redArg(lean_object* v_constName_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_){
_start:
{
lean_object* v_ref_1196_; lean_object* v___x_1197_; 
v_ref_1196_ = lean_ctor_get(v___y_1193_, 5);
v___x_1197_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg(v_ref_1196_, v_constName_1190_, v___y_1191_, v___y_1192_, v___y_1193_, v___y_1194_);
return v___x_1197_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_, lean_object* v___y_1202_, lean_object* v___y_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___redArg(v_constName_1198_, v___y_1199_, v___y_1200_, v___y_1201_, v___y_1202_);
lean_dec(v___y_1202_);
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0(lean_object* v_constName_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_, lean_object* v___y_1209_){
_start:
{
lean_object* v___x_1211_; lean_object* v_env_1212_; uint8_t v___x_1213_; lean_object* v___x_1214_; 
v___x_1211_ = lean_st_ref_get(v___y_1209_);
v_env_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc_ref(v_env_1212_);
lean_dec(v___x_1211_);
v___x_1213_ = 0;
lean_inc(v_constName_1205_);
v___x_1214_ = l_Lean_Environment_find_x3f(v_env_1212_, v_constName_1205_, v___x_1213_);
if (lean_obj_tag(v___x_1214_) == 0)
{
lean_object* v___x_1215_; 
v___x_1215_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___redArg(v_constName_1205_, v___y_1206_, v___y_1207_, v___y_1208_, v___y_1209_);
return v___x_1215_;
}
else
{
lean_object* v_val_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_constName_1205_);
v_val_1216_ = lean_ctor_get(v___x_1214_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1214_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1214_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_val_1216_);
lean_dec(v___x_1214_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1221_; 
if (v_isShared_1219_ == 0)
{
lean_ctor_set_tag(v___x_1218_, 0);
v___x_1221_ = v___x_1218_;
goto v_reusejp_1220_;
}
else
{
lean_object* v_reuseFailAlloc_1222_; 
v_reuseFailAlloc_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1222_, 0, v_val_1216_);
v___x_1221_ = v_reuseFailAlloc_1222_;
goto v_reusejp_1220_;
}
v_reusejp_1220_:
{
return v___x_1221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0___boxed(lean_object* v_constName_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0(v_constName_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
static lean_object* _init_l_Lean_mkCasesOnViaProjs_x3f___closed__0(void){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1231_;
}
}
static lean_object* _init_l_Lean_mkCasesOnViaProjs_x3f___closed__1(void){
_start:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; 
v___x_1232_ = lean_obj_once(&l_Lean_mkCasesOnViaProjs_x3f___closed__0, &l_Lean_mkCasesOnViaProjs_x3f___closed__0_once, _init_l_Lean_mkCasesOnViaProjs_x3f___closed__0);
v___x_1233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1232_);
return v___x_1233_;
}
}
static lean_object* _init_l_Lean_mkCasesOnViaProjs_x3f___closed__2(void){
_start:
{
lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; 
v___x_1234_ = lean_box(1);
v___x_1235_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg___closed__4);
v___x_1236_ = lean_obj_once(&l_Lean_mkCasesOnViaProjs_x3f___closed__1, &l_Lean_mkCasesOnViaProjs_x3f___closed__1_once, _init_l_Lean_mkCasesOnViaProjs_x3f___closed__1);
v___x_1237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1236_);
lean_ctor_set(v___x_1237_, 1, v___x_1235_);
lean_ctor_set(v___x_1237_, 2, v___x_1234_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f(lean_object* v_declName_1240_, lean_object* v_elimName_1241_, lean_object* v_a_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_, lean_object* v_a_1245_){
_start:
{
lean_object* v___x_1247_; 
lean_inc(v_declName_1240_);
v___x_1247_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0(v_declName_1240_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; lean_object* v___x_1250_; uint8_t v_isShared_1251_; uint8_t v_isSharedCheck_1345_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1250_ = v___x_1247_;
v_isShared_1251_ = v_isSharedCheck_1345_;
goto v_resetjp_1249_;
}
else
{
lean_inc(v_a_1248_);
lean_dec(v___x_1247_);
v___x_1250_ = lean_box(0);
v_isShared_1251_ = v_isSharedCheck_1345_;
goto v_resetjp_1249_;
}
v_resetjp_1249_:
{
if (lean_obj_tag(v_a_1248_) == 5)
{
lean_object* v_val_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1342_; 
v_val_1257_ = lean_ctor_get(v_a_1248_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v_a_1248_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1259_ = v_a_1248_;
v_isShared_1260_ = v_isSharedCheck_1342_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_val_1257_);
lean_dec(v_a_1248_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1342_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; uint8_t v___x_1263_; 
v___x_1261_ = l_Lean_InductiveVal_numCtors(v_val_1257_);
v___x_1262_ = lean_unsigned_to_nat(1u);
v___x_1263_ = lean_nat_dec_eq(v___x_1261_, v___x_1262_);
lean_dec(v___x_1261_);
if (v___x_1263_ == 0)
{
lean_del_object(v___x_1259_);
lean_dec_ref(v_val_1257_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
goto v___jp_1252_;
}
else
{
lean_object* v_toConstantVal_1264_; lean_object* v_numParams_1265_; lean_object* v_numIndices_1266_; lean_object* v_ctors_1267_; uint8_t v_isRec_1268_; lean_object* v___x_1269_; uint8_t v___x_1270_; 
v_toConstantVal_1264_ = lean_ctor_get(v_val_1257_, 0);
lean_inc_ref(v_toConstantVal_1264_);
v_numParams_1265_ = lean_ctor_get(v_val_1257_, 1);
lean_inc(v_numParams_1265_);
v_numIndices_1266_ = lean_ctor_get(v_val_1257_, 2);
lean_inc(v_numIndices_1266_);
v_ctors_1267_ = lean_ctor_get(v_val_1257_, 4);
lean_inc(v_ctors_1267_);
v_isRec_1268_ = lean_ctor_get_uint8(v_val_1257_, sizeof(void*)*6);
lean_dec_ref(v_val_1257_);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_nat_dec_eq(v_numIndices_1266_, v___x_1269_);
lean_dec(v_numIndices_1266_);
if (v___x_1270_ == 0)
{
lean_dec(v_ctors_1267_);
lean_dec(v_numParams_1265_);
lean_dec_ref(v_toConstantVal_1264_);
lean_del_object(v___x_1259_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
goto v___jp_1252_;
}
else
{
if (v_isRec_1268_ == 0)
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
lean_del_object(v___x_1250_);
lean_inc(v_declName_1240_);
v___x_1271_ = l_Lean_mkRecName(v_declName_1240_);
v___x_1272_ = l_Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1(v___x_1271_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; lean_object* v___x_1275_; uint8_t v_isShared_1276_; uint8_t v_isSharedCheck_1333_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1275_ = v___x_1272_;
v_isShared_1276_ = v_isSharedCheck_1333_;
goto v_resetjp_1274_;
}
else
{
lean_inc(v_a_1273_);
lean_dec(v___x_1272_);
v___x_1275_ = lean_box(0);
v_isShared_1276_ = v_isSharedCheck_1333_;
goto v_resetjp_1274_;
}
v_resetjp_1274_:
{
lean_object* v_toConstantVal_1277_; lean_object* v_levelParams_1278_; lean_object* v_type_1279_; lean_object* v_levelParams_1280_; lean_object* v_type_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; 
v_toConstantVal_1277_ = lean_ctor_get(v_a_1273_, 0);
lean_inc_ref(v_toConstantVal_1277_);
lean_dec(v_a_1273_);
v_levelParams_1278_ = lean_ctor_get(v_toConstantVal_1277_, 1);
lean_inc(v_levelParams_1278_);
v_type_1279_ = lean_ctor_get(v_toConstantVal_1277_, 2);
lean_inc_ref(v_type_1279_);
lean_dec_ref(v_toConstantVal_1277_);
v_levelParams_1280_ = lean_ctor_get(v_toConstantVal_1264_, 1);
lean_inc(v_levelParams_1280_);
v_type_1281_ = lean_ctor_get(v_toConstantVal_1264_, 2);
lean_inc_ref(v_type_1281_);
lean_dec_ref(v_toConstantVal_1264_);
v___x_1282_ = l_List_lengthTR___redArg(v_levelParams_1278_);
lean_dec(v_levelParams_1278_);
v___x_1283_ = l_List_lengthTR___redArg(v_levelParams_1280_);
v___x_1284_ = lean_nat_dec_eq(v___x_1282_, v___x_1283_);
lean_dec(v___x_1283_);
lean_dec(v___x_1282_);
if (v___x_1284_ == 0)
{
lean_object* v___x_1285_; lean_object* v___x_1287_; 
lean_dec_ref(v_type_1281_);
lean_dec(v_levelParams_1280_);
lean_dec_ref(v_type_1279_);
lean_dec(v_ctors_1267_);
lean_dec(v_numParams_1265_);
lean_del_object(v___x_1259_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
v___x_1285_ = lean_box(0);
if (v_isShared_1276_ == 0)
{
lean_ctor_set(v___x_1275_, 0, v___x_1285_);
v___x_1287_ = v___x_1275_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v___x_1285_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
else
{
lean_object* v___x_1289_; 
lean_del_object(v___x_1275_);
v___x_1289_ = l_Lean_Meta_isPropFormerType(v_type_1281_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1324_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1292_ = v___x_1289_;
v_isShared_1293_ = v_isSharedCheck_1324_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1289_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1324_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
uint8_t v___x_1294_; 
v___x_1294_ = lean_unbox(v_a_1290_);
if (v___x_1294_ == 0)
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_del_object(v___x_1292_);
v___x_1295_ = lean_box(0);
v___x_1296_ = l_List_head_x21___redArg(v___x_1295_, v_ctors_1267_);
lean_dec(v_ctors_1267_);
v___x_1297_ = l_Lean_getConstInfoCtor___at___00Lean_mkCasesOnViaProjs_x3f_spec__2(v___x_1296_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v_a_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1308_; 
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
lean_inc(v_a_1298_);
lean_dec_ref_known(v___x_1297_, 1);
v___x_1299_ = l_Lean_instInhabitedExpr;
v___x_1300_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_mkUnusedLevelParamName(v_levelParams_1280_);
v___x_1301_ = lean_box(v___x_1270_);
lean_inc(v_a_1290_);
lean_inc(v_numParams_1265_);
v___f_1302_ = lean_alloc_closure((void*)(l_Lean_mkCasesOnViaProjs_x3f___lam__3___boxed), 18, 11);
lean_closure_set(v___f_1302_, 0, v___x_1299_);
lean_closure_set(v___f_1302_, 1, v_numParams_1265_);
lean_closure_set(v___f_1302_, 2, v___x_1262_);
lean_closure_set(v___f_1302_, 3, v___x_1300_);
lean_closure_set(v___f_1302_, 4, v___x_1269_);
lean_closure_set(v___f_1302_, 5, v_a_1298_);
lean_closure_set(v___f_1302_, 6, v_a_1290_);
lean_closure_set(v___f_1302_, 7, v___x_1301_);
lean_closure_set(v___f_1302_, 8, v_declName_1240_);
lean_closure_set(v___f_1302_, 9, v_levelParams_1280_);
lean_closure_set(v___f_1302_, 10, v_elimName_1241_);
v___x_1303_ = lean_obj_once(&l_Lean_mkCasesOnViaProjs_x3f___closed__2, &l_Lean_mkCasesOnViaProjs_x3f___closed__2_once, _init_l_Lean_mkCasesOnViaProjs_x3f___closed__2);
v___x_1304_ = ((lean_object*)(l_Lean_mkCasesOnViaProjs_x3f___closed__3));
v___x_1305_ = lean_unsigned_to_nat(2u);
v___x_1306_ = lean_nat_add(v_numParams_1265_, v___x_1305_);
lean_dec(v_numParams_1265_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set_tag(v___x_1259_, 1);
lean_ctor_set(v___x_1259_, 0, v___x_1306_);
v___x_1308_ = v___x_1259_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1311_; 
v_reuseFailAlloc_1311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1311_, 0, v___x_1306_);
v___x_1308_ = v_reuseFailAlloc_1311_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
lean_inc(v_a_1290_);
v___x_1309_ = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnViaProjs_x3f_spec__6___boxed), 11, 6);
lean_closure_set(v___x_1309_, 0, lean_box(0));
lean_closure_set(v___x_1309_, 1, v_type_1279_);
lean_closure_set(v___x_1309_, 2, v___x_1308_);
lean_closure_set(v___x_1309_, 3, v___f_1302_);
lean_closure_set(v___x_1309_, 4, v_a_1290_);
lean_closure_set(v___x_1309_, 5, v_a_1290_);
v___x_1310_ = l_Lean_Meta_withLCtx___at___00Lean_mkCasesOnViaProjs_x3f_spec__7___redArg(v___x_1303_, v___x_1304_, v___x_1309_, v_a_1242_, v_a_1243_, v_a_1244_, v_a_1245_);
return v___x_1310_;
}
}
else
{
lean_object* v_a_1312_; lean_object* v___x_1314_; uint8_t v_isShared_1315_; uint8_t v_isSharedCheck_1319_; 
lean_dec(v_a_1290_);
lean_dec(v_levelParams_1280_);
lean_dec_ref(v_type_1279_);
lean_dec(v_numParams_1265_);
lean_del_object(v___x_1259_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
v_a_1312_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1319_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1314_ = v___x_1297_;
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
else
{
lean_inc(v_a_1312_);
lean_dec(v___x_1297_);
v___x_1314_ = lean_box(0);
v_isShared_1315_ = v_isSharedCheck_1319_;
goto v_resetjp_1313_;
}
v_resetjp_1313_:
{
lean_object* v___x_1317_; 
if (v_isShared_1315_ == 0)
{
v___x_1317_ = v___x_1314_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1318_; 
v_reuseFailAlloc_1318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1318_, 0, v_a_1312_);
v___x_1317_ = v_reuseFailAlloc_1318_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
return v___x_1317_;
}
}
}
}
else
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_dec(v_a_1290_);
lean_dec(v_levelParams_1280_);
lean_dec_ref(v_type_1279_);
lean_dec(v_ctors_1267_);
lean_dec(v_numParams_1265_);
lean_del_object(v___x_1259_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
v___x_1320_ = lean_box(0);
if (v_isShared_1293_ == 0)
{
lean_ctor_set(v___x_1292_, 0, v___x_1320_);
v___x_1322_ = v___x_1292_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
else
{
lean_object* v_a_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
lean_dec(v_levelParams_1280_);
lean_dec_ref(v_type_1279_);
lean_dec(v_ctors_1267_);
lean_dec(v_numParams_1265_);
lean_del_object(v___x_1259_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
v_a_1325_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1327_ = v___x_1289_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_a_1325_);
lean_dec(v___x_1289_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1325_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
lean_dec(v_ctors_1267_);
lean_dec(v_numParams_1265_);
lean_dec_ref(v_toConstantVal_1264_);
lean_del_object(v___x_1259_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
v_a_1334_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1272_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1272_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
else
{
lean_dec(v_ctors_1267_);
lean_dec(v_numParams_1265_);
lean_dec_ref(v_toConstantVal_1264_);
lean_del_object(v___x_1259_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
goto v___jp_1252_;
}
}
}
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; 
lean_del_object(v___x_1250_);
lean_dec(v_a_1248_);
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
v___x_1343_ = lean_box(0);
v___x_1344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1344_, 0, v___x_1343_);
return v___x_1344_;
}
v___jp_1252_:
{
lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1253_ = lean_box(0);
if (v_isShared_1251_ == 0)
{
lean_ctor_set(v___x_1250_, 0, v___x_1253_);
v___x_1255_ = v___x_1250_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
else
{
lean_object* v_a_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1353_; 
lean_dec(v_elimName_1241_);
lean_dec(v_declName_1240_);
v_a_1346_ = lean_ctor_get(v___x_1247_, 0);
v_isSharedCheck_1353_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1348_ = v___x_1247_;
v_isShared_1349_ = v_isSharedCheck_1353_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_a_1346_);
lean_dec(v___x_1247_);
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
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOnViaProjs_x3f___boxed(lean_object* v_declName_1354_, lean_object* v_elimName_1355_, lean_object* v_a_1356_, lean_object* v_a_1357_, lean_object* v_a_1358_, lean_object* v_a_1359_, lean_object* v_a_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_mkCasesOnViaProjs_x3f(v_declName_1354_, v_elimName_1355_, v_a_1356_, v_a_1357_, v_a_1358_, v_a_1359_);
lean_dec(v_a_1359_);
lean_dec_ref(v_a_1358_);
lean_dec(v_a_1357_);
lean_dec_ref(v_a_1356_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0(lean_object* v_00_u03b1_1362_, lean_object* v_constName_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_){
_start:
{
lean_object* v___x_1369_; 
v___x_1369_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___redArg(v_constName_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1370_, lean_object* v_constName_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0(v_00_u03b1_1370_, v_constName_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2(lean_object* v_00_u03b1_1378_, lean_object* v_msg_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
lean_object* v___x_1385_; 
v___x_1385_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(v_msg_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
return v___x_1385_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___boxed(lean_object* v_00_u03b1_1386_, lean_object* v_msg_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v_res_1393_; 
v_res_1393_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2(v_00_u03b1_1386_, v_msg_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_1394_, lean_object* v_ref_1395_, lean_object* v_constName_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___redArg(v_ref_1395_, v_constName_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_ref_1404_, lean_object* v_constName_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5(v_00_u03b1_1403_, v_ref_1404_, v_constName_1405_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v_ref_1404_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11(lean_object* v_00_u03b1_1412_, lean_object* v_ref_1413_, lean_object* v_msg_1414_, lean_object* v_declHint_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___redArg(v_ref_1413_, v_msg_1414_, v_declHint_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11___boxed(lean_object* v_00_u03b1_1422_, lean_object* v_ref_1423_, lean_object* v_msg_1424_, lean_object* v_declHint_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11(v_00_u03b1_1422_, v_ref_1423_, v_msg_1424_, v_declHint_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v_ref_1423_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15(lean_object* v_msg_1432_, lean_object* v_declHint_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___x_1439_; 
v___x_1439_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___redArg(v_msg_1432_, v_declHint_1433_, v___y_1437_);
return v___x_1439_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15___boxed(lean_object* v_msg_1440_, lean_object* v_declHint_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__14_spec__15(v_msg_1440_, v_declHint_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
lean_dec_ref(v___y_1442_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15(lean_object* v_00_u03b1_1448_, lean_object* v_ref_1449_, lean_object* v_msg_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___redArg(v_ref_1449_, v_msg_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_);
return v___x_1456_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15___boxed(lean_object* v_00_u03b1_1457_, lean_object* v_ref_1458_, lean_object* v_msg_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnViaProjs_x3f_spec__0_spec__0_spec__5_spec__11_spec__15(v_00_u03b1_1457_, v_ref_1458_, v_msg_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v_ref_1458_);
return v_res_1465_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1466_ = lean_unsigned_to_nat(32u);
v___x_1467_ = lean_mk_empty_array_with_capacity(v___x_1466_);
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
return v___x_1468_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1469_ = ((size_t)5ULL);
v___x_1470_ = lean_unsigned_to_nat(0u);
v___x_1471_ = lean_unsigned_to_nat(32u);
v___x_1472_ = lean_mk_empty_array_with_capacity(v___x_1471_);
v___x_1473_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__0);
v___x_1474_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1472_);
lean_ctor_set(v___x_1474_, 2, v___x_1470_);
lean_ctor_set(v___x_1474_, 3, v___x_1470_);
lean_ctor_set_usize(v___x_1474_, 4, v___x_1469_);
return v___x_1474_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(lean_object* v___y_1475_){
_start:
{
lean_object* v___x_1477_; lean_object* v_traceState_1478_; lean_object* v_traces_1479_; lean_object* v___x_1480_; lean_object* v_traceState_1481_; lean_object* v_env_1482_; lean_object* v_nextMacroScope_1483_; lean_object* v_ngen_1484_; lean_object* v_auxDeclNGen_1485_; lean_object* v_cache_1486_; lean_object* v_messages_1487_; lean_object* v_infoState_1488_; lean_object* v_snapshotTasks_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1508_; 
v___x_1477_ = lean_st_ref_get(v___y_1475_);
v_traceState_1478_ = lean_ctor_get(v___x_1477_, 4);
lean_inc_ref(v_traceState_1478_);
lean_dec(v___x_1477_);
v_traces_1479_ = lean_ctor_get(v_traceState_1478_, 0);
lean_inc_ref(v_traces_1479_);
lean_dec_ref(v_traceState_1478_);
v___x_1480_ = lean_st_ref_take(v___y_1475_);
v_traceState_1481_ = lean_ctor_get(v___x_1480_, 4);
v_env_1482_ = lean_ctor_get(v___x_1480_, 0);
v_nextMacroScope_1483_ = lean_ctor_get(v___x_1480_, 1);
v_ngen_1484_ = lean_ctor_get(v___x_1480_, 2);
v_auxDeclNGen_1485_ = lean_ctor_get(v___x_1480_, 3);
v_cache_1486_ = lean_ctor_get(v___x_1480_, 5);
v_messages_1487_ = lean_ctor_get(v___x_1480_, 6);
v_infoState_1488_ = lean_ctor_get(v___x_1480_, 7);
v_snapshotTasks_1489_ = lean_ctor_get(v___x_1480_, 8);
v_isSharedCheck_1508_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1508_ == 0)
{
v___x_1491_ = v___x_1480_;
v_isShared_1492_ = v_isSharedCheck_1508_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_snapshotTasks_1489_);
lean_inc(v_infoState_1488_);
lean_inc(v_messages_1487_);
lean_inc(v_cache_1486_);
lean_inc(v_traceState_1481_);
lean_inc(v_auxDeclNGen_1485_);
lean_inc(v_ngen_1484_);
lean_inc(v_nextMacroScope_1483_);
lean_inc(v_env_1482_);
lean_dec(v___x_1480_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1508_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
uint64_t v_tid_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1506_; 
v_tid_1493_ = lean_ctor_get_uint64(v_traceState_1481_, sizeof(void*)*1);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_traceState_1481_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_traceState_1481_, 0);
lean_dec(v_unused_1507_);
v___x_1495_ = v_traceState_1481_;
v_isShared_1496_ = v_isSharedCheck_1506_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v_traceState_1481_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1506_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1497_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___closed__1);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 0, v___x_1497_);
v___x_1499_ = v___x_1495_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v___x_1497_);
lean_ctor_set_uint64(v_reuseFailAlloc_1505_, sizeof(void*)*1, v_tid_1493_);
v___x_1499_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1501_; 
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 4, v___x_1499_);
v___x_1501_ = v___x_1491_;
goto v_reusejp_1500_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_env_1482_);
lean_ctor_set(v_reuseFailAlloc_1504_, 1, v_nextMacroScope_1483_);
lean_ctor_set(v_reuseFailAlloc_1504_, 2, v_ngen_1484_);
lean_ctor_set(v_reuseFailAlloc_1504_, 3, v_auxDeclNGen_1485_);
lean_ctor_set(v_reuseFailAlloc_1504_, 4, v___x_1499_);
lean_ctor_set(v_reuseFailAlloc_1504_, 5, v_cache_1486_);
lean_ctor_set(v_reuseFailAlloc_1504_, 6, v_messages_1487_);
lean_ctor_set(v_reuseFailAlloc_1504_, 7, v_infoState_1488_);
lean_ctor_set(v_reuseFailAlloc_1504_, 8, v_snapshotTasks_1489_);
v___x_1501_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1500_;
}
v_reusejp_1500_:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = lean_st_ref_put(v___y_1475_, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1503_, 0, v_traces_1479_);
return v___x_1503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg___boxed(lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v___y_1509_);
lean_dec(v___y_1509_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v___x_1517_; 
v___x_1517_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v___y_1515_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___boxed(lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_){
_start:
{
lean_object* v_res_1523_; 
v_res_1523_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2(v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_);
lean_dec(v___y_1521_);
lean_dec_ref(v___y_1520_);
lean_dec(v___y_1519_);
lean_dec_ref(v___y_1518_);
return v_res_1523_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(lean_object* v_opts_1524_, lean_object* v_opt_1525_){
_start:
{
lean_object* v_name_1526_; lean_object* v_defValue_1527_; lean_object* v_map_1528_; lean_object* v___x_1529_; 
v_name_1526_ = lean_ctor_get(v_opt_1525_, 0);
v_defValue_1527_ = lean_ctor_get(v_opt_1525_, 1);
v_map_1528_ = lean_ctor_get(v_opts_1524_, 0);
v___x_1529_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1528_, v_name_1526_);
if (lean_obj_tag(v___x_1529_) == 0)
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_unbox(v_defValue_1527_);
return v___x_1530_;
}
else
{
lean_object* v_val_1531_; 
v_val_1531_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v___x_1529_, 1);
if (lean_obj_tag(v_val_1531_) == 1)
{
uint8_t v_v_1532_; 
v_v_1532_ = lean_ctor_get_uint8(v_val_1531_, 0);
lean_dec_ref_known(v_val_1531_, 0);
return v_v_1532_;
}
else
{
uint8_t v___x_1533_; 
lean_dec(v_val_1531_);
v___x_1533_ = lean_unbox(v_defValue_1527_);
return v___x_1533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3___boxed(lean_object* v_opts_1534_, lean_object* v_opt_1535_){
_start:
{
uint8_t v_res_1536_; lean_object* v_r_1537_; 
v_res_1536_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_1534_, v_opt_1535_);
lean_dec_ref(v_opt_1535_);
lean_dec_ref(v_opts_1534_);
v_r_1537_ = lean_box(v_res_1536_);
return v_r_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0(lean_object* v_declName_1538_, lean_object* v_x_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = l_Lean_MessageData_ofName(v_declName_1538_);
v___x_1546_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1546_, 0, v___x_1545_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__0___boxed(lean_object* v_declName_1547_, lean_object* v_x_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v_res_1554_; 
v_res_1554_ = l_Lean_mkCasesOn___lam__0(v_declName_1547_, v_x_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
lean_dec(v___y_1550_);
lean_dec_ref(v___y_1549_);
lean_dec_ref(v_x_1548_);
return v_res_1554_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1555_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__0);
v___x_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1);
v___x_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
lean_ctor_set(v___x_1559_, 1, v___x_1558_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1560_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__1);
v___x_1561_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
lean_ctor_set(v___x_1561_, 2, v___x_1560_);
lean_ctor_set(v___x_1561_, 3, v___x_1560_);
lean_ctor_set(v___x_1561_, 4, v___x_1560_);
lean_ctor_set(v___x_1561_, 5, v___x_1560_);
return v___x_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(lean_object* v_declName_1562_, uint8_t v_s_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; lean_object* v_env_1568_; lean_object* v_nextMacroScope_1569_; lean_object* v_ngen_1570_; lean_object* v_auxDeclNGen_1571_; lean_object* v_traceState_1572_; lean_object* v_messages_1573_; lean_object* v_infoState_1574_; lean_object* v_snapshotTasks_1575_; lean_object* v___x_1577_; uint8_t v_isShared_1578_; uint8_t v_isSharedCheck_1604_; 
v___x_1567_ = lean_st_ref_take(v___y_1565_);
v_env_1568_ = lean_ctor_get(v___x_1567_, 0);
v_nextMacroScope_1569_ = lean_ctor_get(v___x_1567_, 1);
v_ngen_1570_ = lean_ctor_get(v___x_1567_, 2);
v_auxDeclNGen_1571_ = lean_ctor_get(v___x_1567_, 3);
v_traceState_1572_ = lean_ctor_get(v___x_1567_, 4);
v_messages_1573_ = lean_ctor_get(v___x_1567_, 6);
v_infoState_1574_ = lean_ctor_get(v___x_1567_, 7);
v_snapshotTasks_1575_ = lean_ctor_get(v___x_1567_, 8);
v_isSharedCheck_1604_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v___x_1567_, 5);
lean_dec(v_unused_1605_);
v___x_1577_ = v___x_1567_;
v_isShared_1578_ = v_isSharedCheck_1604_;
goto v_resetjp_1576_;
}
else
{
lean_inc(v_snapshotTasks_1575_);
lean_inc(v_infoState_1574_);
lean_inc(v_messages_1573_);
lean_inc(v_traceState_1572_);
lean_inc(v_auxDeclNGen_1571_);
lean_inc(v_ngen_1570_);
lean_inc(v_nextMacroScope_1569_);
lean_inc(v_env_1568_);
lean_dec(v___x_1567_);
v___x_1577_ = lean_box(0);
v_isShared_1578_ = v_isSharedCheck_1604_;
goto v_resetjp_1576_;
}
v_resetjp_1576_:
{
uint8_t v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1579_ = 0;
v___x_1580_ = lean_box(0);
v___x_1581_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_1568_, v_declName_1562_, v_s_1563_, v___x_1579_, v___x_1580_);
v___x_1582_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
if (v_isShared_1578_ == 0)
{
lean_ctor_set(v___x_1577_, 5, v___x_1582_);
lean_ctor_set(v___x_1577_, 0, v___x_1581_);
v___x_1584_ = v___x_1577_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_nextMacroScope_1569_);
lean_ctor_set(v_reuseFailAlloc_1603_, 2, v_ngen_1570_);
lean_ctor_set(v_reuseFailAlloc_1603_, 3, v_auxDeclNGen_1571_);
lean_ctor_set(v_reuseFailAlloc_1603_, 4, v_traceState_1572_);
lean_ctor_set(v_reuseFailAlloc_1603_, 5, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1603_, 6, v_messages_1573_);
lean_ctor_set(v_reuseFailAlloc_1603_, 7, v_infoState_1574_);
lean_ctor_set(v_reuseFailAlloc_1603_, 8, v_snapshotTasks_1575_);
v___x_1584_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v_mctx_1587_; lean_object* v_zetaDeltaFVarIds_1588_; lean_object* v_postponed_1589_; lean_object* v_diag_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1601_; 
v___x_1585_ = lean_st_ref_put(v___y_1565_, v___x_1584_);
v___x_1586_ = lean_st_ref_take(v___y_1564_);
v_mctx_1587_ = lean_ctor_get(v___x_1586_, 0);
v_zetaDeltaFVarIds_1588_ = lean_ctor_get(v___x_1586_, 2);
v_postponed_1589_ = lean_ctor_get(v___x_1586_, 3);
v_diag_1590_ = lean_ctor_get(v___x_1586_, 4);
v_isSharedCheck_1601_ = !lean_is_exclusive(v___x_1586_);
if (v_isSharedCheck_1601_ == 0)
{
lean_object* v_unused_1602_; 
v_unused_1602_ = lean_ctor_get(v___x_1586_, 1);
lean_dec(v_unused_1602_);
v___x_1592_ = v___x_1586_;
v_isShared_1593_ = v_isSharedCheck_1601_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_diag_1590_);
lean_inc(v_postponed_1589_);
lean_inc(v_zetaDeltaFVarIds_1588_);
lean_inc(v_mctx_1587_);
lean_dec(v___x_1586_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1601_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1596_; 
v___x_1594_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
if (v_isShared_1593_ == 0)
{
lean_ctor_set(v___x_1592_, 1, v___x_1594_);
v___x_1596_ = v___x_1592_;
goto v_reusejp_1595_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v_mctx_1587_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v___x_1594_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_zetaDeltaFVarIds_1588_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_postponed_1589_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_diag_1590_);
v___x_1596_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1595_;
}
v_reusejp_1595_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_st_ref_put(v___y_1564_, v___x_1596_);
v___x_1598_ = lean_box(0);
v___x_1599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1598_);
return v___x_1599_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___boxed(lean_object* v_declName_1606_, lean_object* v_s_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
uint8_t v_s_boxed_1611_; lean_object* v_res_1612_; 
v_s_boxed_1611_ = lean_unbox(v_s_1607_);
v_res_1612_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_1606_, v_s_boxed_1611_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec(v___y_1608_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(lean_object* v_declName_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
uint8_t v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = 0;
v___x_1620_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_1613_, v___x_1619_, v___y_1615_, v___y_1617_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0___boxed(lean_object* v_declName_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(v_declName_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__1(lean_object* v_name_1628_, lean_object* v_decl_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_, lean_object* v___y_1633_){
_start:
{
uint8_t v___x_1635_; lean_object* v___x_1636_; 
v___x_1635_ = 0;
v___x_1636_ = l_Lean_addDecl(v_decl_1629_, v___x_1635_, v___y_1632_, v___y_1633_);
if (lean_obj_tag(v___x_1636_) == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_env_1639_; lean_object* v_nextMacroScope_1640_; lean_object* v_ngen_1641_; lean_object* v_auxDeclNGen_1642_; lean_object* v_traceState_1643_; lean_object* v_messages_1644_; lean_object* v_infoState_1645_; lean_object* v_snapshotTasks_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1672_; 
lean_dec_ref_known(v___x_1636_, 1);
lean_inc(v_name_1628_);
v___x_1637_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(v_name_1628_, v___y_1630_, v___y_1631_, v___y_1632_, v___y_1633_);
lean_dec_ref(v___x_1637_);
v___x_1638_ = lean_st_ref_take(v___y_1633_);
v_env_1639_ = lean_ctor_get(v___x_1638_, 0);
v_nextMacroScope_1640_ = lean_ctor_get(v___x_1638_, 1);
v_ngen_1641_ = lean_ctor_get(v___x_1638_, 2);
v_auxDeclNGen_1642_ = lean_ctor_get(v___x_1638_, 3);
v_traceState_1643_ = lean_ctor_get(v___x_1638_, 4);
v_messages_1644_ = lean_ctor_get(v___x_1638_, 6);
v_infoState_1645_ = lean_ctor_get(v___x_1638_, 7);
v_snapshotTasks_1646_ = lean_ctor_get(v___x_1638_, 8);
v_isSharedCheck_1672_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1672_ == 0)
{
lean_object* v_unused_1673_; 
v_unused_1673_ = lean_ctor_get(v___x_1638_, 5);
lean_dec(v_unused_1673_);
v___x_1648_ = v___x_1638_;
v_isShared_1649_ = v_isSharedCheck_1672_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_snapshotTasks_1646_);
lean_inc(v_infoState_1645_);
lean_inc(v_messages_1644_);
lean_inc(v_traceState_1643_);
lean_inc(v_auxDeclNGen_1642_);
lean_inc(v_ngen_1641_);
lean_inc(v_nextMacroScope_1640_);
lean_inc(v_env_1639_);
lean_dec(v___x_1638_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1672_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; 
lean_inc(v_name_1628_);
v___x_1650_ = l_Lean_markAuxRecursor(v_env_1639_, v_name_1628_);
v___x_1651_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
if (v_isShared_1649_ == 0)
{
lean_ctor_set(v___x_1648_, 5, v___x_1651_);
lean_ctor_set(v___x_1648_, 0, v___x_1650_);
v___x_1653_ = v___x_1648_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1671_; 
v_reuseFailAlloc_1671_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1671_, 0, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1671_, 1, v_nextMacroScope_1640_);
lean_ctor_set(v_reuseFailAlloc_1671_, 2, v_ngen_1641_);
lean_ctor_set(v_reuseFailAlloc_1671_, 3, v_auxDeclNGen_1642_);
lean_ctor_set(v_reuseFailAlloc_1671_, 4, v_traceState_1643_);
lean_ctor_set(v_reuseFailAlloc_1671_, 5, v___x_1651_);
lean_ctor_set(v_reuseFailAlloc_1671_, 6, v_messages_1644_);
lean_ctor_set(v_reuseFailAlloc_1671_, 7, v_infoState_1645_);
lean_ctor_set(v_reuseFailAlloc_1671_, 8, v_snapshotTasks_1646_);
v___x_1653_ = v_reuseFailAlloc_1671_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v_mctx_1656_; lean_object* v_zetaDeltaFVarIds_1657_; lean_object* v_postponed_1658_; lean_object* v_diag_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1669_; 
v___x_1654_ = lean_st_ref_put(v___y_1633_, v___x_1653_);
v___x_1655_ = lean_st_ref_take(v___y_1631_);
v_mctx_1656_ = lean_ctor_get(v___x_1655_, 0);
v_zetaDeltaFVarIds_1657_ = lean_ctor_get(v___x_1655_, 2);
v_postponed_1658_ = lean_ctor_get(v___x_1655_, 3);
v_diag_1659_ = lean_ctor_get(v___x_1655_, 4);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1655_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; 
v_unused_1670_ = lean_ctor_get(v___x_1655_, 1);
lean_dec(v_unused_1670_);
v___x_1661_ = v___x_1655_;
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_diag_1659_);
lean_inc(v_postponed_1658_);
lean_inc(v_zetaDeltaFVarIds_1657_);
lean_inc(v_mctx_1656_);
lean_dec(v___x_1655_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1663_; lean_object* v___x_1665_; 
v___x_1663_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 1, v___x_1663_);
v___x_1665_ = v___x_1661_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_mctx_1656_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v___x_1663_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v_zetaDeltaFVarIds_1657_);
lean_ctor_set(v_reuseFailAlloc_1668_, 3, v_postponed_1658_);
lean_ctor_set(v_reuseFailAlloc_1668_, 4, v_diag_1659_);
v___x_1665_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1666_ = lean_st_ref_put(v___y_1631_, v___x_1665_);
v___x_1667_ = l_Lean_enableRealizationsForConst(v_name_1628_, v___y_1632_, v___y_1633_);
return v___x_1667_;
}
}
}
}
}
else
{
lean_dec(v_name_1628_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__1___boxed(lean_object* v_name_1674_, lean_object* v_decl_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v_res_1681_; 
v_res_1681_ = l_Lean_mkCasesOn___lam__1(v_name_1674_, v_decl_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
lean_dec(v___y_1679_);
lean_dec_ref(v___y_1678_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__2(uint8_t v___x_1682_, lean_object* v_name_1683_, lean_object* v_decl_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_addDecl(v_decl_1684_, v___x_1682_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v___x_1691_; lean_object* v___x_1692_; lean_object* v_env_1693_; lean_object* v_nextMacroScope_1694_; lean_object* v_ngen_1695_; lean_object* v_auxDeclNGen_1696_; lean_object* v_traceState_1697_; lean_object* v_messages_1698_; lean_object* v_infoState_1699_; lean_object* v_snapshotTasks_1700_; lean_object* v___x_1702_; uint8_t v_isShared_1703_; uint8_t v_isSharedCheck_1726_; 
lean_dec_ref_known(v___x_1690_, 1);
lean_inc(v_name_1683_);
v___x_1691_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(v_name_1683_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec_ref(v___x_1691_);
v___x_1692_ = lean_st_ref_take(v___y_1688_);
v_env_1693_ = lean_ctor_get(v___x_1692_, 0);
v_nextMacroScope_1694_ = lean_ctor_get(v___x_1692_, 1);
v_ngen_1695_ = lean_ctor_get(v___x_1692_, 2);
v_auxDeclNGen_1696_ = lean_ctor_get(v___x_1692_, 3);
v_traceState_1697_ = lean_ctor_get(v___x_1692_, 4);
v_messages_1698_ = lean_ctor_get(v___x_1692_, 6);
v_infoState_1699_ = lean_ctor_get(v___x_1692_, 7);
v_snapshotTasks_1700_ = lean_ctor_get(v___x_1692_, 8);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1726_ == 0)
{
lean_object* v_unused_1727_; 
v_unused_1727_ = lean_ctor_get(v___x_1692_, 5);
lean_dec(v_unused_1727_);
v___x_1702_ = v___x_1692_;
v_isShared_1703_ = v_isSharedCheck_1726_;
goto v_resetjp_1701_;
}
else
{
lean_inc(v_snapshotTasks_1700_);
lean_inc(v_infoState_1699_);
lean_inc(v_messages_1698_);
lean_inc(v_traceState_1697_);
lean_inc(v_auxDeclNGen_1696_);
lean_inc(v_ngen_1695_);
lean_inc(v_nextMacroScope_1694_);
lean_inc(v_env_1693_);
lean_dec(v___x_1692_);
v___x_1702_ = lean_box(0);
v_isShared_1703_ = v_isSharedCheck_1726_;
goto v_resetjp_1701_;
}
v_resetjp_1701_:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_inc(v_name_1683_);
v___x_1704_ = l_Lean_markAuxRecursor(v_env_1693_, v_name_1683_);
v___x_1705_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
if (v_isShared_1703_ == 0)
{
lean_ctor_set(v___x_1702_, 5, v___x_1705_);
lean_ctor_set(v___x_1702_, 0, v___x_1704_);
v___x_1707_ = v___x_1702_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1704_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_nextMacroScope_1694_);
lean_ctor_set(v_reuseFailAlloc_1725_, 2, v_ngen_1695_);
lean_ctor_set(v_reuseFailAlloc_1725_, 3, v_auxDeclNGen_1696_);
lean_ctor_set(v_reuseFailAlloc_1725_, 4, v_traceState_1697_);
lean_ctor_set(v_reuseFailAlloc_1725_, 5, v___x_1705_);
lean_ctor_set(v_reuseFailAlloc_1725_, 6, v_messages_1698_);
lean_ctor_set(v_reuseFailAlloc_1725_, 7, v_infoState_1699_);
lean_ctor_set(v_reuseFailAlloc_1725_, 8, v_snapshotTasks_1700_);
v___x_1707_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v_mctx_1710_; lean_object* v_zetaDeltaFVarIds_1711_; lean_object* v_postponed_1712_; lean_object* v_diag_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1723_; 
v___x_1708_ = lean_st_ref_put(v___y_1688_, v___x_1707_);
v___x_1709_ = lean_st_ref_take(v___y_1686_);
v_mctx_1710_ = lean_ctor_get(v___x_1709_, 0);
v_zetaDeltaFVarIds_1711_ = lean_ctor_get(v___x_1709_, 2);
v_postponed_1712_ = lean_ctor_get(v___x_1709_, 3);
v_diag_1713_ = lean_ctor_get(v___x_1709_, 4);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1723_ == 0)
{
lean_object* v_unused_1724_; 
v_unused_1724_ = lean_ctor_get(v___x_1709_, 1);
lean_dec(v_unused_1724_);
v___x_1715_ = v___x_1709_;
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_diag_1713_);
lean_inc(v_postponed_1712_);
lean_inc(v_zetaDeltaFVarIds_1711_);
lean_inc(v_mctx_1710_);
lean_dec(v___x_1709_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1723_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
lean_object* v___x_1717_; lean_object* v___x_1719_; 
v___x_1717_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 1, v___x_1717_);
v___x_1719_ = v___x_1715_;
goto v_reusejp_1718_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_mctx_1710_);
lean_ctor_set(v_reuseFailAlloc_1722_, 1, v___x_1717_);
lean_ctor_set(v_reuseFailAlloc_1722_, 2, v_zetaDeltaFVarIds_1711_);
lean_ctor_set(v_reuseFailAlloc_1722_, 3, v_postponed_1712_);
lean_ctor_set(v_reuseFailAlloc_1722_, 4, v_diag_1713_);
v___x_1719_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1718_;
}
v_reusejp_1718_:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
v___x_1720_ = lean_st_ref_put(v___y_1686_, v___x_1719_);
v___x_1721_ = l_Lean_enableRealizationsForConst(v_name_1683_, v___y_1687_, v___y_1688_);
return v___x_1721_;
}
}
}
}
}
else
{
lean_dec(v_name_1683_);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___lam__2___boxed(lean_object* v___x_1728_, lean_object* v_name_1729_, lean_object* v_decl_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_){
_start:
{
uint8_t v___x_13334__boxed_1736_; lean_object* v_res_1737_; 
v___x_13334__boxed_1736_ = lean_unbox(v___x_1728_);
v_res_1737_ = l_Lean_mkCasesOn___lam__2(v___x_13334__boxed_1736_, v_name_1729_, v_decl_1730_, v___y_1731_, v___y_1732_, v___y_1733_, v___y_1734_);
lean_dec(v___y_1734_);
lean_dec_ref(v___y_1733_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
return v_res_1737_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(lean_object* v_e_1738_){
_start:
{
if (lean_obj_tag(v_e_1738_) == 0)
{
uint8_t v___x_1739_; 
v___x_1739_ = 2;
return v___x_1739_;
}
else
{
uint8_t v___x_1740_; 
v___x_1740_ = 0;
return v___x_1740_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8___boxed(lean_object* v_e_1741_){
_start:
{
uint8_t v_res_1742_; lean_object* v_r_1743_; 
v_res_1742_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(v_e_1741_);
lean_dec_ref(v_e_1741_);
v_r_1743_ = lean_box(v_res_1742_);
return v_r_1743_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(lean_object* v_x_1744_){
_start:
{
if (lean_obj_tag(v_x_1744_) == 0)
{
lean_object* v_a_1746_; lean_object* v___x_1748_; uint8_t v_isShared_1749_; uint8_t v_isSharedCheck_1753_; 
v_a_1746_ = lean_ctor_get(v_x_1744_, 0);
v_isSharedCheck_1753_ = !lean_is_exclusive(v_x_1744_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1748_ = v_x_1744_;
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
else
{
lean_inc(v_a_1746_);
lean_dec(v_x_1744_);
v___x_1748_ = lean_box(0);
v_isShared_1749_ = v_isSharedCheck_1753_;
goto v_resetjp_1747_;
}
v_resetjp_1747_:
{
lean_object* v___x_1751_; 
if (v_isShared_1749_ == 0)
{
lean_ctor_set_tag(v___x_1748_, 1);
v___x_1751_ = v___x_1748_;
goto v_reusejp_1750_;
}
else
{
lean_object* v_reuseFailAlloc_1752_; 
v_reuseFailAlloc_1752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1752_, 0, v_a_1746_);
v___x_1751_ = v_reuseFailAlloc_1752_;
goto v_reusejp_1750_;
}
v_reusejp_1750_:
{
return v___x_1751_;
}
}
}
else
{
lean_object* v_a_1754_; lean_object* v___x_1756_; uint8_t v_isShared_1757_; uint8_t v_isSharedCheck_1761_; 
v_a_1754_ = lean_ctor_get(v_x_1744_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v_x_1744_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1756_ = v_x_1744_;
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
else
{
lean_inc(v_a_1754_);
lean_dec(v_x_1744_);
v___x_1756_ = lean_box(0);
v_isShared_1757_ = v_isSharedCheck_1761_;
goto v_resetjp_1755_;
}
v_resetjp_1755_:
{
lean_object* v___x_1759_; 
if (v_isShared_1757_ == 0)
{
lean_ctor_set_tag(v___x_1756_, 0);
v___x_1759_ = v___x_1756_;
goto v_reusejp_1758_;
}
else
{
lean_object* v_reuseFailAlloc_1760_; 
v_reuseFailAlloc_1760_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg___boxed(lean_object* v_x_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_x_1762_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__8(size_t v_sz_1765_, size_t v_i_1766_, lean_object* v_bs_1767_){
_start:
{
uint8_t v___x_1768_; 
v___x_1768_ = lean_usize_dec_lt(v_i_1766_, v_sz_1765_);
if (v___x_1768_ == 0)
{
return v_bs_1767_;
}
else
{
lean_object* v_v_1769_; lean_object* v_msg_1770_; lean_object* v___x_1771_; lean_object* v_bs_x27_1772_; size_t v___x_1773_; size_t v___x_1774_; lean_object* v___x_1775_; 
v_v_1769_ = lean_array_uget_borrowed(v_bs_1767_, v_i_1766_);
v_msg_1770_ = lean_ctor_get(v_v_1769_, 1);
lean_inc_ref(v_msg_1770_);
v___x_1771_ = lean_unsigned_to_nat(0u);
v_bs_x27_1772_ = lean_array_uset(v_bs_1767_, v_i_1766_, v___x_1771_);
v___x_1773_ = ((size_t)1ULL);
v___x_1774_ = lean_usize_add(v_i_1766_, v___x_1773_);
v___x_1775_ = lean_array_uset(v_bs_x27_1772_, v_i_1766_, v_msg_1770_);
v_i_1766_ = v___x_1774_;
v_bs_1767_ = v___x_1775_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__8___boxed(lean_object* v_sz_1777_, lean_object* v_i_1778_, lean_object* v_bs_1779_){
_start:
{
size_t v_sz_boxed_1780_; size_t v_i_boxed_1781_; lean_object* v_res_1782_; 
v_sz_boxed_1780_ = lean_unbox_usize(v_sz_1777_);
lean_dec(v_sz_1777_);
v_i_boxed_1781_ = lean_unbox_usize(v_i_1778_);
lean_dec(v_i_1778_);
v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__8(v_sz_boxed_1780_, v_i_boxed_1781_, v_bs_1779_);
return v_res_1782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(lean_object* v_oldTraces_1783_, lean_object* v_data_1784_, lean_object* v_ref_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_fileName_1792_; lean_object* v_fileMap_1793_; lean_object* v_options_1794_; lean_object* v_currRecDepth_1795_; lean_object* v_maxRecDepth_1796_; lean_object* v_ref_1797_; lean_object* v_currNamespace_1798_; lean_object* v_openDecls_1799_; lean_object* v_initHeartbeats_1800_; lean_object* v_maxHeartbeats_1801_; lean_object* v_quotContext_1802_; lean_object* v_currMacroScope_1803_; uint8_t v_diag_1804_; lean_object* v_cancelTk_x3f_1805_; uint8_t v_suppressElabErrors_1806_; lean_object* v_inheritedTraceOptions_1807_; lean_object* v___x_1808_; lean_object* v_traceState_1809_; lean_object* v_traces_1810_; lean_object* v_ref_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; size_t v_sz_1814_; size_t v___x_1815_; lean_object* v___x_1816_; lean_object* v_msg_1817_; lean_object* v___x_1818_; lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1856_; 
v_fileName_1792_ = lean_ctor_get(v___y_1789_, 0);
v_fileMap_1793_ = lean_ctor_get(v___y_1789_, 1);
v_options_1794_ = lean_ctor_get(v___y_1789_, 2);
v_currRecDepth_1795_ = lean_ctor_get(v___y_1789_, 3);
v_maxRecDepth_1796_ = lean_ctor_get(v___y_1789_, 4);
v_ref_1797_ = lean_ctor_get(v___y_1789_, 5);
v_currNamespace_1798_ = lean_ctor_get(v___y_1789_, 6);
v_openDecls_1799_ = lean_ctor_get(v___y_1789_, 7);
v_initHeartbeats_1800_ = lean_ctor_get(v___y_1789_, 8);
v_maxHeartbeats_1801_ = lean_ctor_get(v___y_1789_, 9);
v_quotContext_1802_ = lean_ctor_get(v___y_1789_, 10);
v_currMacroScope_1803_ = lean_ctor_get(v___y_1789_, 11);
v_diag_1804_ = lean_ctor_get_uint8(v___y_1789_, sizeof(void*)*14);
v_cancelTk_x3f_1805_ = lean_ctor_get(v___y_1789_, 12);
v_suppressElabErrors_1806_ = lean_ctor_get_uint8(v___y_1789_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1807_ = lean_ctor_get(v___y_1789_, 13);
v___x_1808_ = lean_st_ref_get(v___y_1790_);
v_traceState_1809_ = lean_ctor_get(v___x_1808_, 4);
lean_inc_ref(v_traceState_1809_);
lean_dec(v___x_1808_);
v_traces_1810_ = lean_ctor_get(v_traceState_1809_, 0);
lean_inc_ref(v_traces_1810_);
lean_dec_ref(v_traceState_1809_);
v_ref_1811_ = l_Lean_replaceRef(v_ref_1785_, v_ref_1797_);
lean_inc_ref(v_inheritedTraceOptions_1807_);
lean_inc(v_cancelTk_x3f_1805_);
lean_inc(v_currMacroScope_1803_);
lean_inc(v_quotContext_1802_);
lean_inc(v_maxHeartbeats_1801_);
lean_inc(v_initHeartbeats_1800_);
lean_inc(v_openDecls_1799_);
lean_inc(v_currNamespace_1798_);
lean_inc(v_maxRecDepth_1796_);
lean_inc(v_currRecDepth_1795_);
lean_inc_ref(v_options_1794_);
lean_inc_ref(v_fileMap_1793_);
lean_inc_ref(v_fileName_1792_);
v___x_1812_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1812_, 0, v_fileName_1792_);
lean_ctor_set(v___x_1812_, 1, v_fileMap_1793_);
lean_ctor_set(v___x_1812_, 2, v_options_1794_);
lean_ctor_set(v___x_1812_, 3, v_currRecDepth_1795_);
lean_ctor_set(v___x_1812_, 4, v_maxRecDepth_1796_);
lean_ctor_set(v___x_1812_, 5, v_ref_1811_);
lean_ctor_set(v___x_1812_, 6, v_currNamespace_1798_);
lean_ctor_set(v___x_1812_, 7, v_openDecls_1799_);
lean_ctor_set(v___x_1812_, 8, v_initHeartbeats_1800_);
lean_ctor_set(v___x_1812_, 9, v_maxHeartbeats_1801_);
lean_ctor_set(v___x_1812_, 10, v_quotContext_1802_);
lean_ctor_set(v___x_1812_, 11, v_currMacroScope_1803_);
lean_ctor_set(v___x_1812_, 12, v_cancelTk_x3f_1805_);
lean_ctor_set(v___x_1812_, 13, v_inheritedTraceOptions_1807_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*14, v_diag_1804_);
lean_ctor_set_uint8(v___x_1812_, sizeof(void*)*14 + 1, v_suppressElabErrors_1806_);
v___x_1813_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1810_);
lean_dec_ref(v_traces_1810_);
v_sz_1814_ = lean_array_size(v___x_1813_);
v___x_1815_ = ((size_t)0ULL);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6_spec__8(v_sz_1814_, v___x_1815_, v___x_1813_);
v_msg_1817_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1817_, 0, v_data_1784_);
lean_ctor_set(v_msg_1817_, 1, v_msg_1786_);
lean_ctor_set(v_msg_1817_, 2, v___x_1816_);
v___x_1818_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2_spec__8(v_msg_1817_, v___y_1787_, v___y_1788_, v___x_1812_, v___y_1790_);
lean_dec_ref_known(v___x_1812_, 14);
v_a_1819_ = lean_ctor_get(v___x_1818_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1821_ = v___x_1818_;
v_isShared_1822_ = v_isSharedCheck_1856_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1818_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1856_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v_traceState_1824_; lean_object* v_env_1825_; lean_object* v_nextMacroScope_1826_; lean_object* v_ngen_1827_; lean_object* v_auxDeclNGen_1828_; lean_object* v_cache_1829_; lean_object* v_messages_1830_; lean_object* v_infoState_1831_; lean_object* v_snapshotTasks_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1855_; 
v___x_1823_ = lean_st_ref_take(v___y_1790_);
v_traceState_1824_ = lean_ctor_get(v___x_1823_, 4);
v_env_1825_ = lean_ctor_get(v___x_1823_, 0);
v_nextMacroScope_1826_ = lean_ctor_get(v___x_1823_, 1);
v_ngen_1827_ = lean_ctor_get(v___x_1823_, 2);
v_auxDeclNGen_1828_ = lean_ctor_get(v___x_1823_, 3);
v_cache_1829_ = lean_ctor_get(v___x_1823_, 5);
v_messages_1830_ = lean_ctor_get(v___x_1823_, 6);
v_infoState_1831_ = lean_ctor_get(v___x_1823_, 7);
v_snapshotTasks_1832_ = lean_ctor_get(v___x_1823_, 8);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1823_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1834_ = v___x_1823_;
v_isShared_1835_ = v_isSharedCheck_1855_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_snapshotTasks_1832_);
lean_inc(v_infoState_1831_);
lean_inc(v_messages_1830_);
lean_inc(v_cache_1829_);
lean_inc(v_traceState_1824_);
lean_inc(v_auxDeclNGen_1828_);
lean_inc(v_ngen_1827_);
lean_inc(v_nextMacroScope_1826_);
lean_inc(v_env_1825_);
lean_dec(v___x_1823_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1855_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
uint64_t v_tid_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1853_; 
v_tid_1836_ = lean_ctor_get_uint64(v_traceState_1824_, sizeof(void*)*1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_traceState_1824_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_traceState_1824_, 0);
lean_dec(v_unused_1854_);
v___x_1838_ = v_traceState_1824_;
v_isShared_1839_ = v_isSharedCheck_1853_;
goto v_resetjp_1837_;
}
else
{
lean_dec(v_traceState_1824_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1853_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1843_; 
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_ref_1785_);
lean_ctor_set(v___x_1840_, 1, v_a_1819_);
v___x_1841_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1783_, v___x_1840_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1841_);
v___x_1843_ = v___x_1838_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1841_);
lean_ctor_set_uint64(v_reuseFailAlloc_1852_, sizeof(void*)*1, v_tid_1836_);
v___x_1843_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
lean_object* v___x_1845_; 
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 4, v___x_1843_);
v___x_1845_ = v___x_1834_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1851_; 
v_reuseFailAlloc_1851_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1851_, 0, v_env_1825_);
lean_ctor_set(v_reuseFailAlloc_1851_, 1, v_nextMacroScope_1826_);
lean_ctor_set(v_reuseFailAlloc_1851_, 2, v_ngen_1827_);
lean_ctor_set(v_reuseFailAlloc_1851_, 3, v_auxDeclNGen_1828_);
lean_ctor_set(v_reuseFailAlloc_1851_, 4, v___x_1843_);
lean_ctor_set(v_reuseFailAlloc_1851_, 5, v_cache_1829_);
lean_ctor_set(v_reuseFailAlloc_1851_, 6, v_messages_1830_);
lean_ctor_set(v_reuseFailAlloc_1851_, 7, v_infoState_1831_);
lean_ctor_set(v_reuseFailAlloc_1851_, 8, v_snapshotTasks_1832_);
v___x_1845_ = v_reuseFailAlloc_1851_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1846_ = lean_st_ref_put(v___y_1790_, v___x_1845_);
v___x_1847_ = lean_box(0);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 0, v___x_1847_);
v___x_1849_ = v___x_1821_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1850_; 
v_reuseFailAlloc_1850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1850_, 0, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1850_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
return v___x_1849_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6___boxed(lean_object* v_oldTraces_1857_, lean_object* v_data_1858_, lean_object* v_ref_1859_, lean_object* v_msg_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_oldTraces_1857_, v_data_1858_, v_ref_1859_, v_msg_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(lean_object* v_opts_1867_, lean_object* v_opt_1868_){
_start:
{
lean_object* v_name_1869_; lean_object* v_defValue_1870_; lean_object* v_map_1871_; lean_object* v___x_1872_; 
v_name_1869_ = lean_ctor_get(v_opt_1868_, 0);
v_defValue_1870_ = lean_ctor_get(v_opt_1868_, 1);
v_map_1871_ = lean_ctor_get(v_opts_1867_, 0);
v___x_1872_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1871_, v_name_1869_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_inc(v_defValue_1870_);
return v_defValue_1870_;
}
else
{
lean_object* v_val_1873_; 
v_val_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_val_1873_);
lean_dec_ref_known(v___x_1872_, 1);
if (lean_obj_tag(v_val_1873_) == 3)
{
lean_object* v_v_1874_; 
v_v_1874_ = lean_ctor_get(v_val_1873_, 0);
lean_inc(v_v_1874_);
lean_dec_ref_known(v_val_1873_, 1);
return v_v_1874_;
}
else
{
lean_dec(v_val_1873_);
lean_inc(v_defValue_1870_);
return v_defValue_1870_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9___boxed(lean_object* v_opts_1875_, lean_object* v_opt_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_1875_, v_opt_1876_);
lean_dec_ref(v_opt_1876_);
lean_dec_ref(v_opts_1875_);
return v_res_1877_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0(void){
_start:
{
lean_object* v___x_1878_; double v___x_1879_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
v___x_1879_ = lean_float_of_nat(v___x_1878_);
return v___x_1879_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1881_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__1));
v___x_1882_ = l_Lean_stringToMessageData(v___x_1881_);
return v___x_1882_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3(void){
_start:
{
lean_object* v___x_1883_; double v___x_1884_; 
v___x_1883_ = lean_unsigned_to_nat(1000u);
v___x_1884_ = lean_float_of_nat(v___x_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(lean_object* v_cls_1885_, uint8_t v_collapsed_1886_, lean_object* v_tag_1887_, lean_object* v_opts_1888_, uint8_t v_clsEnabled_1889_, lean_object* v_oldTraces_1890_, lean_object* v_msg_1891_, lean_object* v_resStartStop_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_fst_1898_; lean_object* v_snd_1899_; lean_object* v___y_1901_; lean_object* v___y_1902_; lean_object* v_data_1903_; lean_object* v_fst_1906_; lean_object* v_snd_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; lean_object* v___y_1911_; lean_object* v_a_1912_; uint8_t v___y_1927_; double v___y_1958_; 
v_fst_1898_ = lean_ctor_get(v_resStartStop_1892_, 0);
lean_inc(v_fst_1898_);
v_snd_1899_ = lean_ctor_get(v_resStartStop_1892_, 1);
lean_inc(v_snd_1899_);
lean_dec_ref(v_resStartStop_1892_);
v_fst_1906_ = lean_ctor_get(v_snd_1899_, 0);
lean_inc(v_fst_1906_);
v_snd_1907_ = lean_ctor_get(v_snd_1899_, 1);
lean_inc(v_snd_1907_);
lean_dec(v_snd_1899_);
v___x_1908_ = l_Lean_trace_profiler;
v___x_1909_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_1888_, v___x_1908_);
if (v___x_1909_ == 0)
{
v___y_1927_ = v___x_1909_;
goto v___jp_1926_;
}
else
{
lean_object* v___x_1963_; uint8_t v___x_1964_; 
v___x_1963_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1964_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_opts_1888_, v___x_1963_);
if (v___x_1964_ == 0)
{
lean_object* v___x_1965_; lean_object* v___x_1966_; double v___x_1967_; double v___x_1968_; double v___x_1969_; 
v___x_1965_ = l_Lean_trace_profiler_threshold;
v___x_1966_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_1888_, v___x_1965_);
v___x_1967_ = lean_float_of_nat(v___x_1966_);
v___x_1968_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__3);
v___x_1969_ = lean_float_div(v___x_1967_, v___x_1968_);
v___y_1958_ = v___x_1969_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_1970_; lean_object* v___x_1971_; double v___x_1972_; 
v___x_1970_ = l_Lean_trace_profiler_threshold;
v___x_1971_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__9(v_opts_1888_, v___x_1970_);
v___x_1972_ = lean_float_of_nat(v___x_1971_);
v___y_1958_ = v___x_1972_;
goto v___jp_1957_;
}
}
v___jp_1900_:
{
lean_object* v___x_1904_; 
lean_inc(v___y_1902_);
v___x_1904_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__6(v_oldTraces_1890_, v_data_1903_, v___y_1902_, v___y_1901_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_object* v___x_1905_; 
lean_dec_ref_known(v___x_1904_, 1);
v___x_1905_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_fst_1898_);
return v___x_1905_;
}
else
{
lean_dec(v_fst_1898_);
return v___x_1904_;
}
}
v___jp_1910_:
{
uint8_t v_result_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; double v___x_1916_; lean_object* v_data_1917_; 
v_result_1913_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__8(v_fst_1898_);
v___x_1914_ = lean_box(v_result_1913_);
v___x_1915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1915_, 0, v___x_1914_);
v___x_1916_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__0);
lean_inc_ref(v_tag_1887_);
lean_inc_ref(v___x_1915_);
lean_inc(v_cls_1885_);
v_data_1917_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1917_, 0, v_cls_1885_);
lean_ctor_set(v_data_1917_, 1, v___x_1915_);
lean_ctor_set(v_data_1917_, 2, v_tag_1887_);
lean_ctor_set_float(v_data_1917_, sizeof(void*)*3, v___x_1916_);
lean_ctor_set_float(v_data_1917_, sizeof(void*)*3 + 8, v___x_1916_);
lean_ctor_set_uint8(v_data_1917_, sizeof(void*)*3 + 16, v_collapsed_1886_);
if (v___x_1909_ == 0)
{
lean_dec_ref_known(v___x_1915_, 1);
lean_dec(v_snd_1907_);
lean_dec(v_fst_1906_);
lean_dec_ref(v_tag_1887_);
lean_dec(v_cls_1885_);
v___y_1901_ = v_a_1912_;
v___y_1902_ = v___y_1911_;
v_data_1903_ = v_data_1917_;
goto v___jp_1900_;
}
else
{
lean_object* v_data_1918_; double v___x_1919_; double v___x_1920_; 
lean_dec_ref_known(v_data_1917_, 3);
v_data_1918_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1918_, 0, v_cls_1885_);
lean_ctor_set(v_data_1918_, 1, v___x_1915_);
lean_ctor_set(v_data_1918_, 2, v_tag_1887_);
v___x_1919_ = lean_unbox_float(v_fst_1906_);
lean_dec(v_fst_1906_);
lean_ctor_set_float(v_data_1918_, sizeof(void*)*3, v___x_1919_);
v___x_1920_ = lean_unbox_float(v_snd_1907_);
lean_dec(v_snd_1907_);
lean_ctor_set_float(v_data_1918_, sizeof(void*)*3 + 8, v___x_1920_);
lean_ctor_set_uint8(v_data_1918_, sizeof(void*)*3 + 16, v_collapsed_1886_);
v___y_1901_ = v_a_1912_;
v___y_1902_ = v___y_1911_;
v_data_1903_ = v_data_1918_;
goto v___jp_1900_;
}
}
v___jp_1921_:
{
lean_object* v_ref_1922_; lean_object* v___x_1923_; 
v_ref_1922_ = lean_ctor_get(v___y_1895_, 5);
lean_inc(v___y_1896_);
lean_inc_ref(v___y_1895_);
lean_inc(v___y_1894_);
lean_inc_ref(v___y_1893_);
lean_inc(v_fst_1898_);
v___x_1923_ = lean_apply_6(v_msg_1891_, v_fst_1898_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, lean_box(0));
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref_known(v___x_1923_, 1);
v___y_1911_ = v_ref_1922_;
v_a_1912_ = v_a_1924_;
goto v___jp_1910_;
}
else
{
lean_object* v___x_1925_; 
lean_dec_ref_known(v___x_1923_, 1);
v___x_1925_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___closed__2);
v___y_1911_ = v_ref_1922_;
v_a_1912_ = v___x_1925_;
goto v___jp_1910_;
}
}
v___jp_1926_:
{
if (v_clsEnabled_1889_ == 0)
{
if (v___y_1927_ == 0)
{
lean_object* v___x_1928_; lean_object* v_traceState_1929_; lean_object* v_env_1930_; lean_object* v_nextMacroScope_1931_; lean_object* v_ngen_1932_; lean_object* v_auxDeclNGen_1933_; lean_object* v_cache_1934_; lean_object* v_messages_1935_; lean_object* v_infoState_1936_; lean_object* v_snapshotTasks_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1956_; 
lean_dec(v_snd_1907_);
lean_dec(v_fst_1906_);
lean_dec_ref(v_msg_1891_);
lean_dec_ref(v_tag_1887_);
lean_dec(v_cls_1885_);
v___x_1928_ = lean_st_ref_take(v___y_1896_);
v_traceState_1929_ = lean_ctor_get(v___x_1928_, 4);
v_env_1930_ = lean_ctor_get(v___x_1928_, 0);
v_nextMacroScope_1931_ = lean_ctor_get(v___x_1928_, 1);
v_ngen_1932_ = lean_ctor_get(v___x_1928_, 2);
v_auxDeclNGen_1933_ = lean_ctor_get(v___x_1928_, 3);
v_cache_1934_ = lean_ctor_get(v___x_1928_, 5);
v_messages_1935_ = lean_ctor_get(v___x_1928_, 6);
v_infoState_1936_ = lean_ctor_get(v___x_1928_, 7);
v_snapshotTasks_1937_ = lean_ctor_get(v___x_1928_, 8);
v_isSharedCheck_1956_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1956_ == 0)
{
v___x_1939_ = v___x_1928_;
v_isShared_1940_ = v_isSharedCheck_1956_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_snapshotTasks_1937_);
lean_inc(v_infoState_1936_);
lean_inc(v_messages_1935_);
lean_inc(v_cache_1934_);
lean_inc(v_traceState_1929_);
lean_inc(v_auxDeclNGen_1933_);
lean_inc(v_ngen_1932_);
lean_inc(v_nextMacroScope_1931_);
lean_inc(v_env_1930_);
lean_dec(v___x_1928_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1956_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
uint64_t v_tid_1941_; lean_object* v_traces_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1955_; 
v_tid_1941_ = lean_ctor_get_uint64(v_traceState_1929_, sizeof(void*)*1);
v_traces_1942_ = lean_ctor_get(v_traceState_1929_, 0);
v_isSharedCheck_1955_ = !lean_is_exclusive(v_traceState_1929_);
if (v_isSharedCheck_1955_ == 0)
{
v___x_1944_ = v_traceState_1929_;
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_traces_1942_);
lean_dec(v_traceState_1929_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1955_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1946_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1890_, v_traces_1942_);
lean_dec_ref(v_traces_1942_);
if (v_isShared_1945_ == 0)
{
lean_ctor_set(v___x_1944_, 0, v___x_1946_);
v___x_1948_ = v___x_1944_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v___x_1946_);
lean_ctor_set_uint64(v_reuseFailAlloc_1954_, sizeof(void*)*1, v_tid_1941_);
v___x_1948_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1950_; 
if (v_isShared_1940_ == 0)
{
lean_ctor_set(v___x_1939_, 4, v___x_1948_);
v___x_1950_ = v___x_1939_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_env_1930_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v_nextMacroScope_1931_);
lean_ctor_set(v_reuseFailAlloc_1953_, 2, v_ngen_1932_);
lean_ctor_set(v_reuseFailAlloc_1953_, 3, v_auxDeclNGen_1933_);
lean_ctor_set(v_reuseFailAlloc_1953_, 4, v___x_1948_);
lean_ctor_set(v_reuseFailAlloc_1953_, 5, v_cache_1934_);
lean_ctor_set(v_reuseFailAlloc_1953_, 6, v_messages_1935_);
lean_ctor_set(v_reuseFailAlloc_1953_, 7, v_infoState_1936_);
lean_ctor_set(v_reuseFailAlloc_1953_, 8, v_snapshotTasks_1937_);
v___x_1950_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1951_ = lean_st_ref_put(v___y_1896_, v___x_1950_);
v___x_1952_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_fst_1898_);
return v___x_1952_;
}
}
}
}
}
else
{
goto v___jp_1921_;
}
}
else
{
goto v___jp_1921_;
}
}
v___jp_1957_:
{
double v___x_1959_; double v___x_1960_; double v___x_1961_; uint8_t v___x_1962_; 
v___x_1959_ = lean_unbox_float(v_snd_1907_);
v___x_1960_ = lean_unbox_float(v_fst_1906_);
v___x_1961_ = lean_float_sub(v___x_1959_, v___x_1960_);
v___x_1962_ = lean_float_decLt(v___y_1958_, v___x_1961_);
v___y_1927_ = v___x_1962_;
goto v___jp_1926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4___boxed(lean_object* v_cls_1973_, lean_object* v_collapsed_1974_, lean_object* v_tag_1975_, lean_object* v_opts_1976_, lean_object* v_clsEnabled_1977_, lean_object* v_oldTraces_1978_, lean_object* v_msg_1979_, lean_object* v_resStartStop_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_){
_start:
{
uint8_t v_collapsed_boxed_1986_; uint8_t v_clsEnabled_boxed_1987_; lean_object* v_res_1988_; 
v_collapsed_boxed_1986_ = lean_unbox(v_collapsed_1974_);
v_clsEnabled_boxed_1987_ = lean_unbox(v_clsEnabled_1977_);
v_res_1988_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v_cls_1973_, v_collapsed_boxed_1986_, v_tag_1975_, v_opts_1976_, v_clsEnabled_boxed_1987_, v_oldTraces_1978_, v_msg_1979_, v_resStartStop_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
lean_dec(v___y_1984_);
lean_dec_ref(v___y_1983_);
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec_ref(v_opts_1976_);
return v_res_1988_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1989_ = lean_box(0);
v___x_1990_ = l_Lean_interruptExceptionId;
v___x_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1990_);
lean_ctor_set(v___x_1991_, 1, v___x_1989_);
return v___x_1991_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg(){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___closed__0);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v___y_1995_){
_start:
{
lean_object* v_res_1996_; 
v_res_1996_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg();
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(lean_object* v_ex_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_){
_start:
{
lean_object* v___y_2004_; lean_object* v___y_2005_; lean_object* v___y_2006_; lean_object* v___y_2007_; 
if (lean_obj_tag(v_ex_1997_) == 16)
{
lean_object* v___x_2011_; lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v___x_2011_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg();
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2011_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2011_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
else
{
v___y_2004_ = v___y_1998_;
v___y_2005_ = v___y_1999_;
v___y_2006_ = v___y_2000_;
v___y_2007_ = v___y_2001_;
goto v___jp_2003_;
}
v___jp_2003_:
{
lean_object* v_options_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v_options_2008_ = lean_ctor_get(v___y_2006_, 2);
lean_inc_ref(v_options_2008_);
v___x_2009_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1997_, v_options_2008_);
v___x_2010_ = l_Lean_throwError___at___00Lean_getConstInfoRec___at___00Lean_mkCasesOnViaProjs_x3f_spec__1_spec__2___redArg(v___x_2009_, v___y_2004_, v___y_2005_, v___y_2006_, v___y_2007_);
return v___x_2010_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___redArg___boxed(lean_object* v_ex_2020_, lean_object* v___y_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_ex_2020_, v___y_2021_, v___y_2022_, v___y_2023_, v___y_2024_);
lean_dec(v___y_2024_);
lean_dec_ref(v___y_2023_);
lean_dec(v___y_2022_);
lean_dec_ref(v___y_2021_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(lean_object* v_x_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v_x_2027_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v_x_2027_, 1);
v___x_2034_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_a_2033_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_);
return v___x_2034_;
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
v_a_2035_ = lean_ctor_get(v_x_2027_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v_x_2027_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v_x_2027_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v_x_2027_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
lean_ctor_set_tag(v___x_2037_, 0);
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg___boxed(lean_object* v_x_2043_, lean_object* v___y_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
lean_object* v_res_2049_; 
v_res_2049_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(v_x_2043_, v___y_2044_, v___y_2045_, v___y_2046_, v___y_2047_);
lean_dec(v___y_2047_);
lean_dec_ref(v___y_2046_);
lean_dec(v___y_2045_);
lean_dec_ref(v___y_2044_);
return v_res_2049_;
}
}
static lean_object* _init_l_Lean_mkCasesOn___closed__6(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_2060_ = ((lean_object*)(l_Lean_mkCasesOn___closed__5));
v___x_2061_ = l_Lean_Name_append(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
static double _init_l_Lean_mkCasesOn___closed__7(void){
_start:
{
lean_object* v___x_2062_; double v___x_2063_; 
v___x_2062_ = lean_unsigned_to_nat(1000000000u);
v___x_2063_ = lean_float_of_nat(v___x_2062_);
return v___x_2063_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn(lean_object* v_declName_2064_, lean_object* v_a_2065_, lean_object* v_a_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_){
_start:
{
lean_object* v_options_2070_; lean_object* v_inheritedTraceOptions_2071_; uint8_t v_hasTrace_2072_; lean_object* v_name_2073_; lean_object* v_decl_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; 
v_options_2070_ = lean_ctor_get(v_a_2067_, 2);
v_inheritedTraceOptions_2071_ = lean_ctor_get(v_a_2067_, 13);
v_hasTrace_2072_ = lean_ctor_get_uint8(v_options_2070_, sizeof(void*)*1);
lean_inc(v_declName_2064_);
v_name_2073_ = l_Lean_mkCasesOnName(v_declName_2064_);
if (v_hasTrace_2072_ == 0)
{
lean_object* v___x_2118_; 
lean_inc(v_name_2073_);
lean_inc(v_declName_2064_);
v___x_2118_ = l_Lean_mkCasesOnViaProjs_x3f(v_declName_2064_, v_name_2073_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_a_2119_);
lean_dec_ref_known(v___x_2118_, 1);
if (lean_obj_tag(v_a_2119_) == 0)
{
lean_object* v___x_2120_; lean_object* v_env_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; 
v___x_2120_ = lean_st_ref_get(v_a_2068_);
v_env_2121_ = lean_ctor_get(v___x_2120_, 0);
lean_inc_ref(v_env_2121_);
lean_dec(v___x_2120_);
v___x_2122_ = lean_elab_environment_to_kernel_env(v_env_2121_);
v___x_2123_ = lean_mk_cases_on(v___x_2122_, v_declName_2064_);
lean_dec(v_declName_2064_);
v___x_2124_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(v___x_2123_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
lean_inc(v_a_2125_);
lean_dec_ref_known(v___x_2124_, 1);
v_decl_2075_ = v_a_2125_;
v___y_2076_ = v_a_2065_;
v___y_2077_ = v_a_2066_;
v___y_2078_ = v_a_2067_;
v___y_2079_ = v_a_2068_;
goto v___jp_2074_;
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
lean_dec(v_name_2073_);
v_a_2126_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2124_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2124_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
else
{
lean_object* v_val_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_declName_2064_);
v_val_2134_ = lean_ctor_get(v_a_2119_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v_a_2119_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v_a_2119_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_val_2134_);
lean_dec(v_a_2119_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_val_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v_decl_2075_ = v___x_2139_;
v___y_2076_ = v_a_2065_;
v___y_2077_ = v_a_2066_;
v___y_2078_ = v_a_2067_;
v___y_2079_ = v_a_2068_;
goto v___jp_2074_;
}
}
}
}
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_name_2073_);
lean_dec(v_declName_2064_);
v_a_2142_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2118_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2118_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
else
{
lean_object* v___f_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; uint8_t v___x_2154_; lean_object* v___y_2156_; lean_object* v___y_2157_; lean_object* v_a_2158_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v_a_2170_; lean_object* v___y_2173_; lean_object* v___y_2174_; lean_object* v___y_2175_; lean_object* v___y_2186_; lean_object* v___y_2187_; lean_object* v_a_2188_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v_a_2203_; lean_object* v___y_2206_; lean_object* v___y_2207_; lean_object* v___y_2208_; 
lean_inc(v_declName_2064_);
v___f_2150_ = lean_alloc_closure((void*)(l_Lean_mkCasesOn___lam__0___boxed), 7, 1);
lean_closure_set(v___f_2150_, 0, v_declName_2064_);
v___x_2151_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_2152_ = ((lean_object*)(l_Lean_mkCasesOn___closed__3));
v___x_2153_ = lean_obj_once(&l_Lean_mkCasesOn___closed__6, &l_Lean_mkCasesOn___closed__6_once, _init_l_Lean_mkCasesOn___closed__6);
v___x_2154_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2071_, v_options_2070_, v___x_2153_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2265_; uint8_t v___x_2266_; lean_object* v_decl_2268_; lean_object* v___y_2269_; lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; 
v___x_2265_ = l_Lean_trace_profiler;
v___x_2266_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_2070_, v___x_2265_);
if (v___x_2266_ == 0)
{
lean_object* v___x_2311_; 
lean_dec_ref(v___f_2150_);
lean_inc(v_name_2073_);
lean_inc(v_declName_2064_);
v___x_2311_ = l_Lean_mkCasesOnViaProjs_x3f(v_declName_2064_, v_name_2073_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; 
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2312_);
lean_dec_ref_known(v___x_2311_, 1);
if (lean_obj_tag(v_a_2312_) == 0)
{
lean_object* v___x_2313_; lean_object* v_env_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2313_ = lean_st_ref_get(v_a_2068_);
v_env_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc_ref(v_env_2314_);
lean_dec(v___x_2313_);
v___x_2315_ = lean_elab_environment_to_kernel_env(v_env_2314_);
v___x_2316_ = lean_mk_cases_on(v___x_2315_, v_declName_2064_);
lean_dec(v_declName_2064_);
v___x_2317_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(v___x_2316_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v_decl_2268_ = v_a_2318_;
v___y_2269_ = v_a_2065_;
v___y_2270_ = v_a_2066_;
v___y_2271_ = v_a_2067_;
v___y_2272_ = v_a_2068_;
goto v___jp_2267_;
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec(v_name_2073_);
v_a_2319_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2317_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
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
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
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
else
{
lean_object* v_val_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_declName_2064_);
v_val_2327_ = lean_ctor_get(v_a_2312_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v_a_2312_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v_a_2312_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_val_2327_);
lean_dec(v_a_2312_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_val_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
v_decl_2268_ = v___x_2332_;
v___y_2269_ = v_a_2065_;
v___y_2270_ = v_a_2066_;
v___y_2271_ = v_a_2067_;
v___y_2272_ = v_a_2068_;
goto v___jp_2267_;
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_name_2073_);
lean_dec(v_declName_2064_);
v_a_2335_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2311_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2311_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
else
{
goto v___jp_2218_;
}
v___jp_2267_:
{
lean_object* v___x_2273_; 
v___x_2273_ = l_Lean_addDecl(v_decl_2268_, v___x_2266_, v___y_2271_, v___y_2272_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v_env_2276_; lean_object* v_nextMacroScope_2277_; lean_object* v_ngen_2278_; lean_object* v_auxDeclNGen_2279_; lean_object* v_traceState_2280_; lean_object* v_messages_2281_; lean_object* v_infoState_2282_; lean_object* v_snapshotTasks_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2309_; 
lean_dec_ref_known(v___x_2273_, 1);
lean_inc(v_name_2073_);
v___x_2274_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(v_name_2073_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
lean_dec_ref(v___x_2274_);
v___x_2275_ = lean_st_ref_take(v___y_2272_);
v_env_2276_ = lean_ctor_get(v___x_2275_, 0);
v_nextMacroScope_2277_ = lean_ctor_get(v___x_2275_, 1);
v_ngen_2278_ = lean_ctor_get(v___x_2275_, 2);
v_auxDeclNGen_2279_ = lean_ctor_get(v___x_2275_, 3);
v_traceState_2280_ = lean_ctor_get(v___x_2275_, 4);
v_messages_2281_ = lean_ctor_get(v___x_2275_, 6);
v_infoState_2282_ = lean_ctor_get(v___x_2275_, 7);
v_snapshotTasks_2283_ = lean_ctor_get(v___x_2275_, 8);
v_isSharedCheck_2309_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2309_ == 0)
{
lean_object* v_unused_2310_; 
v_unused_2310_ = lean_ctor_get(v___x_2275_, 5);
lean_dec(v_unused_2310_);
v___x_2285_ = v___x_2275_;
v_isShared_2286_ = v_isSharedCheck_2309_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_snapshotTasks_2283_);
lean_inc(v_infoState_2282_);
lean_inc(v_messages_2281_);
lean_inc(v_traceState_2280_);
lean_inc(v_auxDeclNGen_2279_);
lean_inc(v_ngen_2278_);
lean_inc(v_nextMacroScope_2277_);
lean_inc(v_env_2276_);
lean_dec(v___x_2275_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2309_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2290_; 
lean_inc(v_name_2073_);
v___x_2287_ = l_Lean_markAuxRecursor(v_env_2276_, v_name_2073_);
v___x_2288_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 5, v___x_2288_);
lean_ctor_set(v___x_2285_, 0, v___x_2287_);
v___x_2290_ = v___x_2285_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v___x_2287_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_nextMacroScope_2277_);
lean_ctor_set(v_reuseFailAlloc_2308_, 2, v_ngen_2278_);
lean_ctor_set(v_reuseFailAlloc_2308_, 3, v_auxDeclNGen_2279_);
lean_ctor_set(v_reuseFailAlloc_2308_, 4, v_traceState_2280_);
lean_ctor_set(v_reuseFailAlloc_2308_, 5, v___x_2288_);
lean_ctor_set(v_reuseFailAlloc_2308_, 6, v_messages_2281_);
lean_ctor_set(v_reuseFailAlloc_2308_, 7, v_infoState_2282_);
lean_ctor_set(v_reuseFailAlloc_2308_, 8, v_snapshotTasks_2283_);
v___x_2290_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v_mctx_2293_; lean_object* v_zetaDeltaFVarIds_2294_; lean_object* v_postponed_2295_; lean_object* v_diag_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2306_; 
v___x_2291_ = lean_st_ref_put(v___y_2272_, v___x_2290_);
v___x_2292_ = lean_st_ref_take(v___y_2270_);
v_mctx_2293_ = lean_ctor_get(v___x_2292_, 0);
v_zetaDeltaFVarIds_2294_ = lean_ctor_get(v___x_2292_, 2);
v_postponed_2295_ = lean_ctor_get(v___x_2292_, 3);
v_diag_2296_ = lean_ctor_get(v___x_2292_, 4);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v___x_2292_, 1);
lean_dec(v_unused_2307_);
v___x_2298_ = v___x_2292_;
v_isShared_2299_ = v_isSharedCheck_2306_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_diag_2296_);
lean_inc(v_postponed_2295_);
lean_inc(v_zetaDeltaFVarIds_2294_);
lean_inc(v_mctx_2293_);
lean_dec(v___x_2292_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2306_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2300_; lean_object* v___x_2302_; 
v___x_2300_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 1, v___x_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_mctx_2293_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v___x_2300_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v_zetaDeltaFVarIds_2294_);
lean_ctor_set(v_reuseFailAlloc_2305_, 3, v_postponed_2295_);
lean_ctor_set(v_reuseFailAlloc_2305_, 4, v_diag_2296_);
v___x_2302_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2303_ = lean_st_ref_put(v___y_2270_, v___x_2302_);
v___x_2304_ = l_Lean_enableRealizationsForConst(v_name_2073_, v___y_2271_, v___y_2272_);
return v___x_2304_;
}
}
}
}
}
else
{
lean_dec(v_name_2073_);
return v___x_2273_;
}
}
}
else
{
goto v___jp_2218_;
}
v___jp_2155_:
{
lean_object* v___x_2159_; double v___x_2160_; double v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2159_ = lean_io_get_num_heartbeats();
v___x_2160_ = lean_float_of_nat(v___y_2157_);
v___x_2161_ = lean_float_of_nat(v___x_2159_);
v___x_2162_ = lean_box_float(v___x_2160_);
v___x_2163_ = lean_box_float(v___x_2161_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2162_);
lean_ctor_set(v___x_2164_, 1, v___x_2163_);
v___x_2165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2158_);
lean_ctor_set(v___x_2165_, 1, v___x_2164_);
v___x_2166_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_2151_, v_hasTrace_2072_, v___x_2152_, v_options_2070_, v___x_2154_, v___y_2156_, v___f_2150_, v___x_2165_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
return v___x_2166_;
}
v___jp_2167_:
{
lean_object* v___x_2171_; 
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_a_2170_);
v___y_2156_ = v___y_2168_;
v___y_2157_ = v___y_2169_;
v_a_2158_ = v___x_2171_;
goto v___jp_2155_;
}
v___jp_2172_:
{
if (lean_obj_tag(v___y_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2183_; 
v_a_2176_ = lean_ctor_get(v___y_2175_, 0);
v_isSharedCheck_2183_ = !lean_is_exclusive(v___y_2175_);
if (v_isSharedCheck_2183_ == 0)
{
v___x_2178_ = v___y_2175_;
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___y_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2183_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v___x_2181_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set_tag(v___x_2178_, 1);
v___x_2181_ = v___x_2178_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_a_2176_);
v___x_2181_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
v___y_2156_ = v___y_2173_;
v___y_2157_ = v___y_2174_;
v_a_2158_ = v___x_2181_;
goto v___jp_2155_;
}
}
}
else
{
lean_object* v_a_2184_; 
v_a_2184_ = lean_ctor_get(v___y_2175_, 0);
lean_inc(v_a_2184_);
lean_dec_ref_known(v___y_2175_, 1);
v___y_2168_ = v___y_2173_;
v___y_2169_ = v___y_2174_;
v_a_2170_ = v_a_2184_;
goto v___jp_2167_;
}
}
v___jp_2185_:
{
lean_object* v___x_2189_; double v___x_2190_; double v___x_2191_; double v___x_2192_; double v___x_2193_; double v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2189_ = lean_io_mono_nanos_now();
v___x_2190_ = lean_float_of_nat(v___y_2186_);
v___x_2191_ = lean_float_once(&l_Lean_mkCasesOn___closed__7, &l_Lean_mkCasesOn___closed__7_once, _init_l_Lean_mkCasesOn___closed__7);
v___x_2192_ = lean_float_div(v___x_2190_, v___x_2191_);
v___x_2193_ = lean_float_of_nat(v___x_2189_);
v___x_2194_ = lean_float_div(v___x_2193_, v___x_2191_);
v___x_2195_ = lean_box_float(v___x_2192_);
v___x_2196_ = lean_box_float(v___x_2194_);
v___x_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2198_, 0, v_a_2188_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4(v___x_2151_, v_hasTrace_2072_, v___x_2152_, v_options_2070_, v___x_2154_, v___y_2187_, v___f_2150_, v___x_2198_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
return v___x_2199_;
}
v___jp_2200_:
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2204_, 0, v_a_2203_);
v___y_2186_ = v___y_2201_;
v___y_2187_ = v___y_2202_;
v_a_2188_ = v___x_2204_;
goto v___jp_2185_;
}
v___jp_2205_:
{
if (lean_obj_tag(v___y_2208_) == 0)
{
lean_object* v_a_2209_; lean_object* v___x_2211_; uint8_t v_isShared_2212_; uint8_t v_isSharedCheck_2216_; 
v_a_2209_ = lean_ctor_get(v___y_2208_, 0);
v_isSharedCheck_2216_ = !lean_is_exclusive(v___y_2208_);
if (v_isSharedCheck_2216_ == 0)
{
v___x_2211_ = v___y_2208_;
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
else
{
lean_inc(v_a_2209_);
lean_dec(v___y_2208_);
v___x_2211_ = lean_box(0);
v_isShared_2212_ = v_isSharedCheck_2216_;
goto v_resetjp_2210_;
}
v_resetjp_2210_:
{
lean_object* v___x_2214_; 
if (v_isShared_2212_ == 0)
{
lean_ctor_set_tag(v___x_2211_, 1);
v___x_2214_ = v___x_2211_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2215_; 
v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
v___x_2214_ = v_reuseFailAlloc_2215_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
v___y_2186_ = v___y_2206_;
v___y_2187_ = v___y_2207_;
v_a_2188_ = v___x_2214_;
goto v___jp_2185_;
}
}
}
else
{
lean_object* v_a_2217_; 
v_a_2217_ = lean_ctor_get(v___y_2208_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v___y_2208_, 1);
v___y_2201_ = v___y_2206_;
v___y_2202_ = v___y_2207_;
v_a_2203_ = v_a_2217_;
goto v___jp_2200_;
}
}
v___jp_2218_:
{
lean_object* v___x_2219_; lean_object* v_a_2220_; lean_object* v___x_2221_; uint8_t v___x_2222_; 
v___x_2219_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_mkCasesOn_spec__2___redArg(v_a_2068_);
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref(v___x_2219_);
v___x_2221_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2222_ = l_Lean_Option_get___at___00Lean_mkCasesOn_spec__3(v_options_2070_, v___x_2221_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_io_mono_nanos_now();
lean_inc(v_name_2073_);
lean_inc(v_declName_2064_);
v___x_2224_ = l_Lean_mkCasesOnViaProjs_x3f(v_declName_2064_, v_name_2073_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
if (lean_obj_tag(v_a_2225_) == 0)
{
lean_object* v___x_2226_; lean_object* v_env_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2226_ = lean_st_ref_get(v_a_2068_);
v_env_2227_ = lean_ctor_get(v___x_2226_, 0);
lean_inc_ref(v_env_2227_);
lean_dec(v___x_2226_);
v___x_2228_ = lean_elab_environment_to_kernel_env(v_env_2227_);
v___x_2229_ = lean_mk_cases_on(v___x_2228_, v_declName_2064_);
lean_dec(v_declName_2064_);
v___x_2230_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(v___x_2229_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2230_) == 0)
{
lean_object* v_a_2231_; lean_object* v___x_2232_; 
v_a_2231_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2231_);
lean_dec_ref_known(v___x_2230_, 1);
v___x_2232_ = l_Lean_mkCasesOn___lam__2(v___x_2222_, v_name_2073_, v_a_2231_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
v___y_2206_ = v___x_2223_;
v___y_2207_ = v_a_2220_;
v___y_2208_ = v___x_2232_;
goto v___jp_2205_;
}
else
{
lean_object* v_a_2233_; 
lean_dec(v_name_2073_);
v_a_2233_ = lean_ctor_get(v___x_2230_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2230_, 1);
v___y_2201_ = v___x_2223_;
v___y_2202_ = v_a_2220_;
v_a_2203_ = v_a_2233_;
goto v___jp_2200_;
}
}
else
{
lean_object* v_val_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2242_; 
lean_dec(v_declName_2064_);
v_val_2234_ = lean_ctor_get(v_a_2225_, 0);
v_isSharedCheck_2242_ = !lean_is_exclusive(v_a_2225_);
if (v_isSharedCheck_2242_ == 0)
{
v___x_2236_ = v_a_2225_;
v_isShared_2237_ = v_isSharedCheck_2242_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_val_2234_);
lean_dec(v_a_2225_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2242_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v___x_2239_; 
if (v_isShared_2237_ == 0)
{
v___x_2239_ = v___x_2236_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_val_2234_);
v___x_2239_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_mkCasesOn___lam__2(v___x_2222_, v_name_2073_, v___x_2239_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
v___y_2206_ = v___x_2223_;
v___y_2207_ = v_a_2220_;
v___y_2208_ = v___x_2240_;
goto v___jp_2205_;
}
}
}
}
else
{
lean_object* v_a_2243_; 
lean_dec(v_name_2073_);
lean_dec(v_declName_2064_);
v_a_2243_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2243_);
lean_dec_ref_known(v___x_2224_, 1);
v___y_2201_ = v___x_2223_;
v___y_2202_ = v_a_2220_;
v_a_2203_ = v_a_2243_;
goto v___jp_2200_;
}
}
else
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = lean_io_get_num_heartbeats();
lean_inc(v_name_2073_);
lean_inc(v_declName_2064_);
v___x_2245_ = l_Lean_mkCasesOnViaProjs_x3f(v_declName_2064_, v_name_2073_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2246_);
lean_dec_ref_known(v___x_2245_, 1);
if (lean_obj_tag(v_a_2246_) == 0)
{
lean_object* v___x_2247_; lean_object* v_env_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2247_ = lean_st_ref_get(v_a_2068_);
v_env_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc_ref(v_env_2248_);
lean_dec(v___x_2247_);
v___x_2249_ = lean_elab_environment_to_kernel_env(v_env_2248_);
v___x_2250_ = lean_mk_cases_on(v___x_2249_, v_declName_2064_);
lean_dec(v_declName_2064_);
v___x_2251_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(v___x_2250_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2253_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = l_Lean_mkCasesOn___lam__1(v_name_2073_, v_a_2252_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
v___y_2173_ = v_a_2220_;
v___y_2174_ = v___x_2244_;
v___y_2175_ = v___x_2253_;
goto v___jp_2172_;
}
else
{
lean_object* v_a_2254_; 
lean_dec(v_name_2073_);
v_a_2254_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2251_, 1);
v___y_2168_ = v_a_2220_;
v___y_2169_ = v___x_2244_;
v_a_2170_ = v_a_2254_;
goto v___jp_2167_;
}
}
else
{
lean_object* v_val_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2263_; 
lean_dec(v_declName_2064_);
v_val_2255_ = lean_ctor_get(v_a_2246_, 0);
v_isSharedCheck_2263_ = !lean_is_exclusive(v_a_2246_);
if (v_isSharedCheck_2263_ == 0)
{
v___x_2257_ = v_a_2246_;
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_val_2255_);
lean_dec(v_a_2246_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2263_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2260_; 
if (v_isShared_2258_ == 0)
{
v___x_2260_ = v___x_2257_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_val_2255_);
v___x_2260_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
lean_object* v___x_2261_; 
v___x_2261_ = l_Lean_mkCasesOn___lam__1(v_name_2073_, v___x_2260_, v_a_2065_, v_a_2066_, v_a_2067_, v_a_2068_);
v___y_2173_ = v_a_2220_;
v___y_2174_ = v___x_2244_;
v___y_2175_ = v___x_2261_;
goto v___jp_2172_;
}
}
}
}
else
{
lean_object* v_a_2264_; 
lean_dec(v_name_2073_);
lean_dec(v_declName_2064_);
v_a_2264_ = lean_ctor_get(v___x_2245_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2245_, 1);
v___y_2168_ = v_a_2220_;
v___y_2169_ = v___x_2244_;
v_a_2170_ = v_a_2264_;
goto v___jp_2167_;
}
}
}
}
v___jp_2074_:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_addDecl(v_decl_2075_, v_hasTrace_2072_, v___y_2078_, v___y_2079_);
if (lean_obj_tag(v___x_2080_) == 0)
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v_env_2083_; lean_object* v_nextMacroScope_2084_; lean_object* v_ngen_2085_; lean_object* v_auxDeclNGen_2086_; lean_object* v_traceState_2087_; lean_object* v_messages_2088_; lean_object* v_infoState_2089_; lean_object* v_snapshotTasks_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2116_; 
lean_dec_ref_known(v___x_2080_, 1);
lean_inc(v_name_2073_);
v___x_2081_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0(v_name_2073_, v___y_2076_, v___y_2077_, v___y_2078_, v___y_2079_);
lean_dec_ref(v___x_2081_);
v___x_2082_ = lean_st_ref_take(v___y_2079_);
v_env_2083_ = lean_ctor_get(v___x_2082_, 0);
v_nextMacroScope_2084_ = lean_ctor_get(v___x_2082_, 1);
v_ngen_2085_ = lean_ctor_get(v___x_2082_, 2);
v_auxDeclNGen_2086_ = lean_ctor_get(v___x_2082_, 3);
v_traceState_2087_ = lean_ctor_get(v___x_2082_, 4);
v_messages_2088_ = lean_ctor_get(v___x_2082_, 6);
v_infoState_2089_ = lean_ctor_get(v___x_2082_, 7);
v_snapshotTasks_2090_ = lean_ctor_get(v___x_2082_, 8);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; 
v_unused_2117_ = lean_ctor_get(v___x_2082_, 5);
lean_dec(v_unused_2117_);
v___x_2092_ = v___x_2082_;
v_isShared_2093_ = v_isSharedCheck_2116_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_snapshotTasks_2090_);
lean_inc(v_infoState_2089_);
lean_inc(v_messages_2088_);
lean_inc(v_traceState_2087_);
lean_inc(v_auxDeclNGen_2086_);
lean_inc(v_ngen_2085_);
lean_inc(v_nextMacroScope_2084_);
lean_inc(v_env_2083_);
lean_dec(v___x_2082_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2116_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2097_; 
lean_inc(v_name_2073_);
v___x_2094_ = l_Lean_markAuxRecursor(v_env_2083_, v_name_2073_);
v___x_2095_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__2);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 5, v___x_2095_);
lean_ctor_set(v___x_2092_, 0, v___x_2094_);
v___x_2097_ = v___x_2092_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v_nextMacroScope_2084_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_ngen_2085_);
lean_ctor_set(v_reuseFailAlloc_2115_, 3, v_auxDeclNGen_2086_);
lean_ctor_set(v_reuseFailAlloc_2115_, 4, v_traceState_2087_);
lean_ctor_set(v_reuseFailAlloc_2115_, 5, v___x_2095_);
lean_ctor_set(v_reuseFailAlloc_2115_, 6, v_messages_2088_);
lean_ctor_set(v_reuseFailAlloc_2115_, 7, v_infoState_2089_);
lean_ctor_set(v_reuseFailAlloc_2115_, 8, v_snapshotTasks_2090_);
v___x_2097_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v_mctx_2100_; lean_object* v_zetaDeltaFVarIds_2101_; lean_object* v_postponed_2102_; lean_object* v_diag_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2113_; 
v___x_2098_ = lean_st_ref_put(v___y_2079_, v___x_2097_);
v___x_2099_ = lean_st_ref_take(v___y_2077_);
v_mctx_2100_ = lean_ctor_get(v___x_2099_, 0);
v_zetaDeltaFVarIds_2101_ = lean_ctor_get(v___x_2099_, 2);
v_postponed_2102_ = lean_ctor_get(v___x_2099_, 3);
v_diag_2103_ = lean_ctor_get(v___x_2099_, 4);
v_isSharedCheck_2113_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2113_ == 0)
{
lean_object* v_unused_2114_; 
v_unused_2114_ = lean_ctor_get(v___x_2099_, 1);
lean_dec(v_unused_2114_);
v___x_2105_ = v___x_2099_;
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_diag_2103_);
lean_inc(v_postponed_2102_);
lean_inc(v_zetaDeltaFVarIds_2101_);
lean_inc(v_mctx_2100_);
lean_dec(v___x_2099_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2113_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2107_; lean_object* v___x_2109_; 
v___x_2107_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg___closed__3);
if (v_isShared_2106_ == 0)
{
lean_ctor_set(v___x_2105_, 1, v___x_2107_);
v___x_2109_ = v___x_2105_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2112_; 
v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2112_, 0, v_mctx_2100_);
lean_ctor_set(v_reuseFailAlloc_2112_, 1, v___x_2107_);
lean_ctor_set(v_reuseFailAlloc_2112_, 2, v_zetaDeltaFVarIds_2101_);
lean_ctor_set(v_reuseFailAlloc_2112_, 3, v_postponed_2102_);
lean_ctor_set(v_reuseFailAlloc_2112_, 4, v_diag_2103_);
v___x_2109_ = v_reuseFailAlloc_2112_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2110_ = lean_st_ref_put(v___y_2077_, v___x_2109_);
v___x_2111_ = l_Lean_enableRealizationsForConst(v_name_2073_, v___y_2078_, v___y_2079_);
return v___x_2111_;
}
}
}
}
}
else
{
lean_dec(v_name_2073_);
return v___x_2080_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkCasesOn___boxed(lean_object* v_declName_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lean_mkCasesOn(v_declName_2343_, v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0(lean_object* v_declName_2350_, uint8_t v_s_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_){
_start:
{
lean_object* v___x_2357_; 
v___x_2357_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___redArg(v_declName_2350_, v_s_2351_, v___y_2353_, v___y_2355_);
return v___x_2357_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0___boxed(lean_object* v_declName_2358_, lean_object* v_s_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_){
_start:
{
uint8_t v_s_boxed_2365_; lean_object* v_res_2366_; 
v_s_boxed_2365_ = lean_unbox(v_s_2359_);
v_res_2366_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOn_spec__0_spec__0(v_declName_2358_, v_s_boxed_2365_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_);
lean_dec(v___y_2363_);
lean_dec_ref(v___y_2362_);
lean_dec(v___y_2361_);
lean_dec_ref(v___y_2360_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1(lean_object* v_00_u03b1_2367_, lean_object* v_x_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_){
_start:
{
lean_object* v___x_2374_; 
v___x_2374_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___redArg(v_x_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1___boxed(lean_object* v_00_u03b1_2375_, lean_object* v_x_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1(v_00_u03b1_2375_, v_x_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(lean_object* v_00_u03b1_2383_, lean_object* v_x_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
v___x_2390_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___redArg(v_x_2384_);
return v___x_2390_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7___boxed(lean_object* v_00_u03b1_2391_, lean_object* v_x_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_mkCasesOn_spec__4_spec__7(v_00_u03b1_2391_, v_x_2392_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5(lean_object* v_00_u03b1_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
lean_object* v___x_2405_; 
v___x_2405_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___redArg();
return v___x_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b1_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v_res_2412_; 
v_res_2412_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2_spec__5(v_00_u03b1_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v_res_2412_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2(lean_object* v_00_u03b1_2413_, lean_object* v_ex_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v___x_2420_; 
v___x_2420_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___redArg(v_ex_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2___boxed(lean_object* v_00_u03b1_2421_, lean_object* v_ex_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00Lean_mkCasesOn_spec__1_spec__2(v_00_u03b1_2421_, v_ex_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_2489_; uint8_t v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v___x_2489_ = ((lean_object*)(l_Lean_mkCasesOn___closed__2));
v___x_2490_ = 0;
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn___closed__24_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_));
v___x_2492_ = l_Lean_registerTraceClass(v___x_2489_, v___x_2490_, v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2____boxed(lean_object* v_a_2493_){
_start:
{
lean_object* v_res_2494_; 
v_res_2494_ = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
return v_res_2494_;
}
}
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Constructions_CasesOn_0__Lean_initFn_00___x40_Lean_Meta_Constructions_CasesOn_989523109____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Constructions_CasesOn(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Constructions_CasesOn(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Constructions_CasesOn(builtin);
}
#ifdef __cplusplus
}
#endif
