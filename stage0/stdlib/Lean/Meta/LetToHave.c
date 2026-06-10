// Lean compiler output
// Module: Lean.Meta.LetToHave
// Imports: public import Lean.Meta.Check public import Lean.ReservedNameAction public import Lean.AddDecl public import Lean.Meta.Transform public import Lean.Util.CollectFVars public import Lean.Util.CollectMVars import Init.Data.Range.Polymorphic.Iterators import Init.While
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
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_FVarId_throwUnknown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addZetaDeltaFVarId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVar_x21(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_collectFVars(lean_object*, lean_object*);
lean_object* lean_array_pop(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_isLetVar___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwUnknownMVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instantiateTypeLevelParams___redArg(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwAppTypeMismatch___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwFunctionExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
uint8_t l_Lean_Expr_isSort(lean_object*);
lean_object* l_Lean_Meta_throwTypeExpected___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
lean_object* l_Lean_mkLevelIMax_x27(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Literal_type(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkProj(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getZetaDeltaFVarIds___redArg(lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Meta_instDecidableEqProjReductionKind(uint8_t, uint8_t);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___closed__0_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__0 = (const lean_object*)&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__1 = (const lean_object*)&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__1_value;
static lean_once_cell_t l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2;
static lean_once_cell_t l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_LetToHave_instInhabitedResult_default;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___closed__0_value;
LEAN_EXPORT const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1;
static const lean_array_object l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3_value;
static const lean_closure_object l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instMonadMetaM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.LetToHave"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "_private.Lean.Meta.LetToHave.0.Lean.Meta.LetToHave.visitConst"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateApp!Impl"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "application expected"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.LetToHave.0.Lean.Meta.LetToHave.visitLambdaLet.finalize"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "letToHave"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "debug"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 3, 170, 90, 194, 179, 10, 17)}};
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3_value_aux_1),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__2_value),LEAN_SCALAR_PTR_LITERAL(86, 160, 73, 249, 166, 244, 47, 125)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4_value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "finalize "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__13 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__13_value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__13_value)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid projection"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "\nfrom type"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "visit (check := "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4_value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "invalid let declaration, term"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "unexpected bound variable "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "transformed "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " `let` expressions into `have` expressions"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "result:"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "result: (no change)"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "no `let` expressions"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 3, 170, 90, 194, 179, 10, 17)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2;
static lean_once_cell_t l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_letToHave___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "let-to-have transformation"};
static const lean_object* l_Lean_Meta_letToHave___closed__0 = (const lean_object*)&l_Lean_Meta_letToHave___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "LetToHave"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(116, 136, 50, 239, 0, 218, 22, 67)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(245, 192, 30, 32, 60, 3, 161, 57)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 162, 78, 225, 97, 193, 211, 154)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 52, 189, 140, 199, 100, 72, 251)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(57, 119, 103, 45, 179, 255, 212, 36)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(244, 238, 181, 178, 141, 48, 35, 162)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(245, 81, 38, 233, 242, 131, 79, 183)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(189, 23, 142, 14, 29, 68, 13, 149)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 77, 222, 212, 108, 104, 240, 20)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1606831773) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(188, 242, 27, 127, 244, 91, 156, 204)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(19, 47, 215, 48, 43, 169, 21, 43)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 14, 169, 133, 112, 139, 163, 217)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(86, 189, 43, 239, 62, 157, 143, 122)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 8)
{
uint8_t v_nondep_2_; 
v_nondep_2_ = lean_ctor_get_uint8(v_x_1_, sizeof(void*)*4 + 8);
if (v_nondep_2_ == 0)
{
uint8_t v___x_3_; 
v___x_3_ = 1;
return v___x_3_;
}
else
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
}
else
{
uint8_t v___x_5_; 
v___x_5_ = 0;
return v___x_5_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0___boxed(lean_object* v_x_6_){
_start:
{
uint8_t v_res_7_; lean_object* v_r_8_; 
v_res_7_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___lam__0(v_x_6_);
lean_dec_ref(v_x_6_);
v_r_8_ = lean_box(v_res_7_);
return v_r_8_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(lean_object* v_e_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; 
v___f_11_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___closed__0));
v___x_12_ = lean_find_expr(v___f_11_, v_e_10_);
if (lean_obj_tag(v___x_12_) == 0)
{
uint8_t v___x_13_; 
v___x_13_ = 0;
return v___x_13_;
}
else
{
uint8_t v___x_14_; 
lean_dec_ref_known(v___x_12_, 1);
v___x_14_ = 1;
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet___boxed(lean_object* v_e_15_){
_start:
{
uint8_t v_res_16_; lean_object* v_r_17_; 
v_res_16_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_15_);
lean_dec_ref(v_e_15_);
v_r_17_ = lean_box(v_res_16_);
return v_r_17_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(lean_object* v_e_18_, uint32_t v_maxDepth_19_){
_start:
{
uint8_t v___x_20_; 
v___x_20_ = l_Lean_Expr_hasFVar(v_e_18_);
if (v___x_20_ == 0)
{
uint8_t v___x_21_; 
v___x_21_ = l_Lean_Expr_hasExprMVar(v_e_18_);
if (v___x_21_ == 0)
{
uint32_t v___x_22_; uint8_t v___x_23_; 
v___x_22_ = l_Lean_Expr_approxDepth(v_e_18_);
v___x_23_ = lean_uint32_dec_le(v___x_22_, v_maxDepth_19_);
if (v___x_23_ == 0)
{
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_18_);
if (v___x_24_ == 0)
{
return v___x_23_;
}
else
{
return v___x_21_;
}
}
}
else
{
return v___x_20_;
}
}
else
{
uint8_t v___x_25_; 
v___x_25_ = 0;
return v___x_25_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip___boxed(lean_object* v_e_26_, lean_object* v_maxDepth_27_){
_start:
{
uint32_t v_maxDepth_boxed_28_; uint8_t v_res_29_; lean_object* v_r_30_; 
v_maxDepth_boxed_28_ = lean_unbox_uint32(v_maxDepth_27_);
lean_dec(v_maxDepth_27_);
v_res_29_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_26_, v_maxDepth_boxed_28_);
lean_dec_ref(v_e_26_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = ((lean_object*)(l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__1));
v___x_36_ = l_Lean_Expr_const___override(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3);
return v___x_40_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0(lean_object* v_self_42_){
_start:
{
lean_object* v_expr_43_; 
v_expr_43_ = lean_ctor_get(v_self_42_, 0);
lean_inc_ref(v_expr_43_);
return v_expr_43_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0___boxed(lean_object* v_self_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0(v_self_44_);
lean_dec_ref(v_self_44_);
return v_res_45_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(lean_object* v_a_48_, lean_object* v_b_49_, lean_object* v_x_50_){
_start:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_dec(v_b_49_);
lean_dec_ref(v_a_48_);
return v_x_50_;
}
else
{
lean_object* v_key_51_; lean_object* v_value_52_; lean_object* v_tail_53_; lean_object* v___x_55_; uint8_t v_isShared_56_; uint8_t v_isSharedCheck_65_; 
v_key_51_ = lean_ctor_get(v_x_50_, 0);
v_value_52_ = lean_ctor_get(v_x_50_, 1);
v_tail_53_ = lean_ctor_get(v_x_50_, 2);
v_isSharedCheck_65_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_65_ == 0)
{
v___x_55_ = v_x_50_;
v_isShared_56_ = v_isSharedCheck_65_;
goto v_resetjp_54_;
}
else
{
lean_inc(v_tail_53_);
lean_inc(v_value_52_);
lean_inc(v_key_51_);
lean_dec(v_x_50_);
v___x_55_ = lean_box(0);
v_isShared_56_ = v_isSharedCheck_65_;
goto v_resetjp_54_;
}
v_resetjp_54_:
{
uint8_t v___x_57_; 
v___x_57_ = l_Lean_ExprStructEq_beq(v_key_51_, v_a_48_);
if (v___x_57_ == 0)
{
lean_object* v___x_58_; lean_object* v___x_60_; 
v___x_58_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_48_, v_b_49_, v_tail_53_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 2, v___x_58_);
v___x_60_ = v___x_55_;
goto v_reusejp_59_;
}
else
{
lean_object* v_reuseFailAlloc_61_; 
v_reuseFailAlloc_61_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_61_, 0, v_key_51_);
lean_ctor_set(v_reuseFailAlloc_61_, 1, v_value_52_);
lean_ctor_set(v_reuseFailAlloc_61_, 2, v___x_58_);
v___x_60_ = v_reuseFailAlloc_61_;
goto v_reusejp_59_;
}
v_reusejp_59_:
{
return v___x_60_;
}
}
else
{
lean_object* v___x_63_; 
lean_dec(v_value_52_);
lean_dec(v_key_51_);
if (v_isShared_56_ == 0)
{
lean_ctor_set(v___x_55_, 1, v_b_49_);
lean_ctor_set(v___x_55_, 0, v_a_48_);
v___x_63_ = v___x_55_;
goto v_reusejp_62_;
}
else
{
lean_object* v_reuseFailAlloc_64_; 
v_reuseFailAlloc_64_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_64_, 0, v_a_48_);
lean_ctor_set(v_reuseFailAlloc_64_, 1, v_b_49_);
lean_ctor_set(v_reuseFailAlloc_64_, 2, v_tail_53_);
v___x_63_ = v_reuseFailAlloc_64_;
goto v_reusejp_62_;
}
v_reusejp_62_:
{
return v___x_63_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_66_, lean_object* v_x_67_){
_start:
{
if (lean_obj_tag(v_x_67_) == 0)
{
return v_x_66_;
}
else
{
lean_object* v_key_68_; lean_object* v_value_69_; lean_object* v_tail_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_93_; 
v_key_68_ = lean_ctor_get(v_x_67_, 0);
v_value_69_ = lean_ctor_get(v_x_67_, 1);
v_tail_70_ = lean_ctor_get(v_x_67_, 2);
v_isSharedCheck_93_ = !lean_is_exclusive(v_x_67_);
if (v_isSharedCheck_93_ == 0)
{
v___x_72_ = v_x_67_;
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_tail_70_);
lean_inc(v_value_69_);
lean_inc(v_key_68_);
lean_dec(v_x_67_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_93_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_74_; uint64_t v___x_75_; uint64_t v___x_76_; uint64_t v___x_77_; uint64_t v_fold_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; size_t v___x_82_; size_t v___x_83_; size_t v___x_84_; size_t v___x_85_; size_t v___x_86_; lean_object* v___x_87_; lean_object* v___x_89_; 
v___x_74_ = lean_array_get_size(v_x_66_);
v___x_75_ = l_Lean_ExprStructEq_hash(v_key_68_);
v___x_76_ = 32ULL;
v___x_77_ = lean_uint64_shift_right(v___x_75_, v___x_76_);
v_fold_78_ = lean_uint64_xor(v___x_75_, v___x_77_);
v___x_79_ = 16ULL;
v___x_80_ = lean_uint64_shift_right(v_fold_78_, v___x_79_);
v___x_81_ = lean_uint64_xor(v_fold_78_, v___x_80_);
v___x_82_ = lean_uint64_to_usize(v___x_81_);
v___x_83_ = lean_usize_of_nat(v___x_74_);
v___x_84_ = ((size_t)1ULL);
v___x_85_ = lean_usize_sub(v___x_83_, v___x_84_);
v___x_86_ = lean_usize_land(v___x_82_, v___x_85_);
v___x_87_ = lean_array_uget_borrowed(v_x_66_, v___x_86_);
lean_inc(v___x_87_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 2, v___x_87_);
v___x_89_ = v___x_72_;
goto v_reusejp_88_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_key_68_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_value_69_);
lean_ctor_set(v_reuseFailAlloc_92_, 2, v___x_87_);
v___x_89_ = v_reuseFailAlloc_92_;
goto v_reusejp_88_;
}
v_reusejp_88_:
{
lean_object* v___x_90_; 
v___x_90_ = lean_array_uset(v_x_66_, v___x_86_, v___x_89_);
v_x_66_ = v___x_90_;
v_x_67_ = v_tail_70_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(lean_object* v_i_94_, lean_object* v_source_95_, lean_object* v_target_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = lean_array_get_size(v_source_95_);
v___x_98_ = lean_nat_dec_lt(v_i_94_, v___x_97_);
if (v___x_98_ == 0)
{
lean_dec_ref(v_source_95_);
lean_dec(v_i_94_);
return v_target_96_;
}
else
{
lean_object* v_es_99_; lean_object* v___x_100_; lean_object* v_source_101_; lean_object* v_target_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_es_99_ = lean_array_fget(v_source_95_, v_i_94_);
v___x_100_ = lean_box(0);
v_source_101_ = lean_array_fset(v_source_95_, v_i_94_, v___x_100_);
v_target_102_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(v_target_96_, v_es_99_);
v___x_103_ = lean_unsigned_to_nat(1u);
v___x_104_ = lean_nat_add(v_i_94_, v___x_103_);
lean_dec(v_i_94_);
v_i_94_ = v___x_104_;
v_source_95_ = v_source_101_;
v_target_96_ = v_target_102_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(lean_object* v_data_106_){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_nbuckets_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_107_ = lean_array_get_size(v_data_106_);
v___x_108_ = lean_unsigned_to_nat(2u);
v_nbuckets_109_ = lean_nat_mul(v___x_107_, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_box(0);
v___x_112_ = lean_mk_array(v_nbuckets_109_, v___x_111_);
v___x_113_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v___x_110_, v_data_106_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(lean_object* v_a_114_, lean_object* v_x_115_){
_start:
{
if (lean_obj_tag(v_x_115_) == 0)
{
uint8_t v___x_116_; 
v___x_116_ = 0;
return v___x_116_;
}
else
{
lean_object* v_key_117_; lean_object* v_tail_118_; uint8_t v___x_119_; 
v_key_117_ = lean_ctor_get(v_x_115_, 0);
v_tail_118_ = lean_ctor_get(v_x_115_, 2);
v___x_119_ = l_Lean_ExprStructEq_beq(v_key_117_, v_a_114_);
if (v___x_119_ == 0)
{
v_x_115_ = v_tail_118_;
goto _start;
}
else
{
return v___x_119_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg___boxed(lean_object* v_a_121_, lean_object* v_x_122_){
_start:
{
uint8_t v_res_123_; lean_object* v_r_124_; 
v_res_123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_121_, v_x_122_);
lean_dec(v_x_122_);
lean_dec_ref(v_a_121_);
v_r_124_ = lean_box(v_res_123_);
return v_r_124_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(lean_object* v_m_125_, lean_object* v_a_126_, lean_object* v_b_127_){
_start:
{
lean_object* v_size_128_; lean_object* v_buckets_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_172_; 
v_size_128_ = lean_ctor_get(v_m_125_, 0);
v_buckets_129_ = lean_ctor_get(v_m_125_, 1);
v_isSharedCheck_172_ = !lean_is_exclusive(v_m_125_);
if (v_isSharedCheck_172_ == 0)
{
v___x_131_ = v_m_125_;
v_isShared_132_ = v_isSharedCheck_172_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_buckets_129_);
lean_inc(v_size_128_);
lean_dec(v_m_125_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_172_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; uint64_t v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v_fold_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; size_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; lean_object* v_bkt_146_; uint8_t v___x_147_; 
v___x_133_ = lean_array_get_size(v_buckets_129_);
v___x_134_ = l_Lean_ExprStructEq_hash(v_a_126_);
v___x_135_ = 32ULL;
v___x_136_ = lean_uint64_shift_right(v___x_134_, v___x_135_);
v_fold_137_ = lean_uint64_xor(v___x_134_, v___x_136_);
v___x_138_ = 16ULL;
v___x_139_ = lean_uint64_shift_right(v_fold_137_, v___x_138_);
v___x_140_ = lean_uint64_xor(v_fold_137_, v___x_139_);
v___x_141_ = lean_uint64_to_usize(v___x_140_);
v___x_142_ = lean_usize_of_nat(v___x_133_);
v___x_143_ = ((size_t)1ULL);
v___x_144_ = lean_usize_sub(v___x_142_, v___x_143_);
v___x_145_ = lean_usize_land(v___x_141_, v___x_144_);
v_bkt_146_ = lean_array_uget_borrowed(v_buckets_129_, v___x_145_);
v___x_147_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_126_, v_bkt_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v_size_x27_149_; lean_object* v___x_150_; lean_object* v_buckets_x27_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_148_ = lean_unsigned_to_nat(1u);
v_size_x27_149_ = lean_nat_add(v_size_128_, v___x_148_);
lean_dec(v_size_128_);
lean_inc(v_bkt_146_);
v___x_150_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_150_, 0, v_a_126_);
lean_ctor_set(v___x_150_, 1, v_b_127_);
lean_ctor_set(v___x_150_, 2, v_bkt_146_);
v_buckets_x27_151_ = lean_array_uset(v_buckets_129_, v___x_145_, v___x_150_);
v___x_152_ = lean_unsigned_to_nat(4u);
v___x_153_ = lean_nat_mul(v_size_x27_149_, v___x_152_);
v___x_154_ = lean_unsigned_to_nat(3u);
v___x_155_ = lean_nat_div(v___x_153_, v___x_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_array_get_size(v_buckets_x27_151_);
v___x_157_ = lean_nat_dec_le(v___x_155_, v___x_156_);
lean_dec(v___x_155_);
if (v___x_157_ == 0)
{
lean_object* v_val_158_; lean_object* v___x_160_; 
v_val_158_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_buckets_x27_151_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_val_158_);
lean_ctor_set(v___x_131_, 0, v_size_x27_149_);
v___x_160_ = v___x_131_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_size_x27_149_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v_val_158_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
else
{
lean_object* v___x_163_; 
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v_buckets_x27_151_);
lean_ctor_set(v___x_131_, 0, v_size_x27_149_);
v___x_163_ = v___x_131_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_size_x27_149_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_buckets_x27_151_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
else
{
lean_object* v___x_165_; lean_object* v_buckets_x27_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
lean_inc(v_bkt_146_);
v___x_165_ = lean_box(0);
v_buckets_x27_166_ = lean_array_uset(v_buckets_129_, v___x_145_, v___x_165_);
v___x_167_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_126_, v_b_127_, v_bkt_146_);
v___x_168_ = lean_array_uset(v_buckets_x27_166_, v___x_145_, v___x_167_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 1, v___x_168_);
v___x_170_ = v___x_131_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_171_; 
v_reuseFailAlloc_171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_171_, 0, v_size_128_);
lean_ctor_set(v_reuseFailAlloc_171_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_171_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
return v___x_170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(lean_object* v_r_173_, lean_object* v_a_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v_type_x3f_180_; 
v_type_x3f_180_ = lean_ctor_get(v_r_173_, 1);
lean_inc(v_type_x3f_180_);
if (lean_obj_tag(v_type_x3f_180_) == 1)
{
lean_object* v_val_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_dec_ref(v_r_173_);
v_val_181_ = lean_ctor_get(v_type_x3f_180_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v_type_x3f_180_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v_type_x3f_180_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_val_181_);
lean_dec(v_type_x3f_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
lean_ctor_set_tag(v___x_183_, 0);
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_val_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
else
{
lean_object* v_expr_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_218_; 
lean_dec(v_type_x3f_180_);
v_expr_189_ = lean_ctor_get(v_r_173_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v_r_173_);
if (v_isSharedCheck_218_ == 0)
{
lean_object* v_unused_219_; 
v_unused_219_ = lean_ctor_get(v_r_173_, 1);
lean_dec(v_unused_219_);
v___x_191_ = v_r_173_;
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_expr_189_);
lean_dec(v_r_173_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_218_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; 
lean_inc(v_a_178_);
lean_inc_ref(v_a_177_);
lean_inc(v_a_176_);
lean_inc_ref(v_a_175_);
lean_inc_ref(v_expr_189_);
v___x_193_ = lean_infer_type(v_expr_189_, v_a_175_, v_a_176_, v_a_177_, v_a_178_);
if (lean_obj_tag(v___x_193_) == 0)
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_217_; 
v_a_194_ = lean_ctor_get(v___x_193_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_193_);
if (v_isSharedCheck_217_ == 0)
{
v___x_196_ = v___x_193_;
v_isShared_197_ = v_isSharedCheck_217_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_217_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_198_; lean_object* v_count_199_; lean_object* v_results_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_216_; 
v___x_198_ = lean_st_ref_take(v_a_174_);
v_count_199_ = lean_ctor_get(v___x_198_, 0);
v_results_200_ = lean_ctor_get(v___x_198_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_198_);
if (v_isSharedCheck_216_ == 0)
{
v___x_202_ = v___x_198_;
v_isShared_203_ = v_isSharedCheck_216_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_results_200_);
lean_inc(v_count_199_);
lean_dec(v___x_198_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_216_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
lean_inc(v_a_194_);
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v_a_194_);
lean_inc_ref(v_expr_189_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 1, v___x_204_);
v___x_206_ = v___x_191_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_expr_189_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_204_);
v___x_206_ = v_reuseFailAlloc_215_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_200_, v_expr_189_, v___x_206_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v___x_207_);
v___x_209_ = v___x_202_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_count_199_);
lean_ctor_set(v_reuseFailAlloc_214_, 1, v___x_207_);
v___x_209_ = v_reuseFailAlloc_214_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
lean_object* v___x_210_; lean_object* v___x_212_; 
v___x_210_ = lean_st_ref_set(v_a_174_, v___x_209_);
if (v_isShared_197_ == 0)
{
v___x_212_ = v___x_196_;
goto v_reusejp_211_;
}
else
{
lean_object* v_reuseFailAlloc_213_; 
v_reuseFailAlloc_213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_213_, 0, v_a_194_);
v___x_212_ = v_reuseFailAlloc_213_;
goto v_reusejp_211_;
}
v_reusejp_211_:
{
return v___x_212_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_191_);
lean_dec_ref(v_expr_189_);
return v___x_193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg___boxed(lean_object* v_r_220_, lean_object* v_a_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_220_, v_a_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_);
lean_dec(v_a_225_);
lean_dec_ref(v_a_224_);
lean_dec(v_a_223_);
lean_dec_ref(v_a_222_);
lean_dec(v_a_221_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(lean_object* v_r_228_, lean_object* v_a_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_){
_start:
{
lean_object* v___x_236_; 
v___x_236_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_228_, v_a_230_, v_a_231_, v_a_232_, v_a_233_, v_a_234_);
return v___x_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___boxed(lean_object* v_r_237_, lean_object* v_a_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(v_r_237_, v_a_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_);
lean_dec(v_a_243_);
lean_dec_ref(v_a_242_);
lean_dec(v_a_241_);
lean_dec_ref(v_a_240_);
lean_dec(v_a_239_);
lean_dec(v_a_238_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(lean_object* v_00_u03b2_246_, lean_object* v_m_247_, lean_object* v_a_248_, lean_object* v_b_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_m_247_, v_a_248_, v_b_249_);
return v___x_250_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_object* v_00_u03b2_251_, lean_object* v_a_252_, lean_object* v_x_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_252_, v_x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___boxed(lean_object* v_00_u03b2_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v_res_258_; lean_object* v_r_259_; 
v_res_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(v_00_u03b2_255_, v_a_256_, v_x_257_);
lean_dec(v_x_257_);
lean_dec_ref(v_a_256_);
v_r_259_ = lean_box(v_res_258_);
return v_r_259_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1(lean_object* v_00_u03b2_260_, lean_object* v_data_261_){
_start:
{
lean_object* v___x_262_; 
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_data_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2(lean_object* v_00_u03b2_263_, lean_object* v_a_264_, lean_object* v_b_265_, lean_object* v_x_266_){
_start:
{
lean_object* v___x_267_; 
v___x_267_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_264_, v_b_265_, v_x_266_);
return v___x_267_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_268_, lean_object* v_i_269_, lean_object* v_source_270_, lean_object* v_target_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v_i_269_, v_source_270_, v_target_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(v_x_274_, v_x_275_);
return v___x_276_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(lean_object* v_ctx_277_){
_start:
{
uint8_t v___x_278_; 
v___x_278_ = l_List_isEmpty___redArg(v_ctx_277_);
if (v___x_278_ == 0)
{
uint8_t v___x_279_; 
v___x_279_ = 1;
return v___x_279_;
}
else
{
uint8_t v___x_280_; 
v___x_280_ = 0;
return v___x_280_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check___boxed(lean_object* v_ctx_281_){
_start:
{
uint8_t v_res_282_; lean_object* v_r_283_; 
v_res_282_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_ctx_281_);
lean_dec(v_ctx_281_);
v_r_283_ = lean_box(v_res_282_);
return v_r_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(lean_object* v_e_284_, lean_object* v_m_285_, lean_object* v_a_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
uint8_t v___x_293_; 
v___x_293_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_286_);
if (v___x_293_ == 0)
{
lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
lean_dec_ref(v_m_285_);
v___x_294_ = lean_box(0);
v___x_295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_295_, 0, v_e_284_);
lean_ctor_set(v___x_295_, 1, v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
return v___x_296_;
}
else
{
lean_object* v___x_297_; 
lean_dec_ref(v_e_284_);
lean_inc(v_a_291_);
lean_inc_ref(v_a_290_);
lean_inc(v_a_289_);
lean_inc_ref(v_a_288_);
lean_inc(v_a_287_);
lean_inc(v_a_286_);
v___x_297_ = lean_apply_7(v_m_285_, v_a_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, lean_box(0));
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck___boxed(lean_object* v_e_298_, lean_object* v_m_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_298_, v_m_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_);
lean_dec(v_a_305_);
lean_dec_ref(v_a_304_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec(v_a_300_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(lean_object* v_fvars_308_, lean_object* v_m_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_){
_start:
{
lean_object* v___x_316_; 
lean_inc(v_a_314_);
lean_inc_ref(v_a_313_);
lean_inc(v_a_312_);
lean_inc_ref(v_a_311_);
lean_inc(v_a_310_);
v___x_316_ = lean_apply_7(v_m_309_, v_fvars_308_, v_a_310_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, lean_box(0));
return v___x_316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg___boxed(lean_object* v_fvars_317_, lean_object* v_m_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
lean_object* v_res_325_; 
v_res_325_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(v_fvars_317_, v_m_318_, v_a_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_);
lean_dec(v_a_323_);
lean_dec_ref(v_a_322_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
return v_res_325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(lean_object* v_00_u03b1_326_, lean_object* v_fvars_327_, lean_object* v_m_328_, lean_object* v_a_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_){
_start:
{
lean_object* v___x_336_; 
lean_inc(v_a_334_);
lean_inc_ref(v_a_333_);
lean_inc(v_a_332_);
lean_inc_ref(v_a_331_);
lean_inc(v_a_330_);
v___x_336_ = lean_apply_7(v_m_328_, v_fvars_327_, v_a_330_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, lean_box(0));
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed(lean_object* v_00_u03b1_337_, lean_object* v_fvars_338_, lean_object* v_m_339_, lean_object* v_a_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(v_00_u03b1_337_, v_fvars_338_, v_m_339_, v_a_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_);
lean_dec(v_a_345_);
lean_dec_ref(v_a_344_);
lean_dec(v_a_343_);
lean_dec_ref(v_a_342_);
lean_dec(v_a_341_);
lean_dec(v_a_340_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(lean_object* v_a_348_){
_start:
{
lean_object* v___x_350_; lean_object* v_count_351_; lean_object* v_results_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_364_; 
v___x_350_ = lean_st_ref_take(v_a_348_);
v_count_351_ = lean_ctor_get(v___x_350_, 0);
v_results_352_ = lean_ctor_get(v___x_350_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_364_ == 0)
{
v___x_354_ = v___x_350_;
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_results_352_);
lean_inc(v_count_351_);
lean_dec(v___x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_356_ = lean_unsigned_to_nat(1u);
v___x_357_ = lean_nat_add(v_count_351_, v___x_356_);
lean_dec(v_count_351_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_357_);
v___x_359_ = v___x_354_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_357_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v_results_352_);
v___x_359_ = v_reuseFailAlloc_363_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_360_ = lean_st_ref_set(v_a_348_, v___x_359_);
v___x_361_ = lean_box(0);
v___x_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_362_, 0, v___x_361_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg___boxed(lean_object* v_a_365_, lean_object* v_a_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_365_);
lean_dec(v_a_365_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(lean_object* v_a_368_, lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_375_; 
v___x_375_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_369_);
return v___x_375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___boxed(lean_object* v_a_376_, lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(v_a_376_, v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_);
lean_dec(v_a_381_);
lean_dec_ref(v_a_380_);
lean_dec(v_a_379_);
lean_dec_ref(v_a_378_);
lean_dec(v_a_377_);
lean_dec(v_a_376_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(lean_object* v_a_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 0)
{
lean_object* v___x_386_; 
v___x_386_ = lean_box(0);
return v___x_386_;
}
else
{
lean_object* v_key_387_; lean_object* v_value_388_; lean_object* v_tail_389_; uint8_t v___x_390_; 
v_key_387_ = lean_ctor_get(v_x_385_, 0);
v_value_388_ = lean_ctor_get(v_x_385_, 1);
v_tail_389_ = lean_ctor_get(v_x_385_, 2);
v___x_390_ = l_Lean_ExprStructEq_beq(v_key_387_, v_a_384_);
if (v___x_390_ == 0)
{
v_x_385_ = v_tail_389_;
goto _start;
}
else
{
lean_object* v___x_392_; 
lean_inc(v_value_388_);
v___x_392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_392_, 0, v_value_388_);
return v___x_392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_393_, lean_object* v_x_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_393_, v_x_394_);
lean_dec(v_x_394_);
lean_dec_ref(v_a_393_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(lean_object* v_m_396_, lean_object* v_a_397_){
_start:
{
lean_object* v_buckets_398_; lean_object* v___x_399_; uint64_t v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v_fold_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v___x_406_; size_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_buckets_398_ = lean_ctor_get(v_m_396_, 1);
v___x_399_ = lean_array_get_size(v_buckets_398_);
v___x_400_ = l_Lean_ExprStructEq_hash(v_a_397_);
v___x_401_ = 32ULL;
v___x_402_ = lean_uint64_shift_right(v___x_400_, v___x_401_);
v_fold_403_ = lean_uint64_xor(v___x_400_, v___x_402_);
v___x_404_ = 16ULL;
v___x_405_ = lean_uint64_shift_right(v_fold_403_, v___x_404_);
v___x_406_ = lean_uint64_xor(v_fold_403_, v___x_405_);
v___x_407_ = lean_uint64_to_usize(v___x_406_);
v___x_408_ = lean_usize_of_nat(v___x_399_);
v___x_409_ = ((size_t)1ULL);
v___x_410_ = lean_usize_sub(v___x_408_, v___x_409_);
v___x_411_ = lean_usize_land(v___x_407_, v___x_410_);
v___x_412_ = lean_array_uget_borrowed(v_buckets_398_, v___x_411_);
v___x_413_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_397_, v___x_412_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg___boxed(lean_object* v_m_414_, lean_object* v_a_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_414_, v_a_415_);
lean_dec_ref(v_a_415_);
lean_dec_ref(v_m_414_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(lean_object* v_e_417_, lean_object* v_a_418_){
_start:
{
lean_object* v___x_420_; lean_object* v_results_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_420_ = lean_st_ref_get(v_a_418_);
v_results_421_ = lean_ctor_get(v___x_420_, 1);
lean_inc_ref(v_results_421_);
lean_dec(v___x_420_);
v___x_422_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_results_421_, v_e_417_);
lean_dec_ref(v_results_421_);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg___boxed(lean_object* v_e_424_, lean_object* v_a_425_, lean_object* v_a_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_424_, v_a_425_);
lean_dec(v_a_425_);
lean_dec_ref(v_e_424_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(lean_object* v_e_428_, lean_object* v_a_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_){
_start:
{
lean_object* v___x_436_; 
v___x_436_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_428_, v_a_430_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___boxed(lean_object* v_e_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(v_e_437_, v_a_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_);
lean_dec(v_a_443_);
lean_dec_ref(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_a_440_);
lean_dec(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_e_437_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(lean_object* v_00_u03b2_446_, lean_object* v_m_447_, lean_object* v_a_448_){
_start:
{
lean_object* v___x_449_; 
v___x_449_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_447_, v_a_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___boxed(lean_object* v_00_u03b2_450_, lean_object* v_m_451_, lean_object* v_a_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(v_00_u03b2_450_, v_m_451_, v_a_452_);
lean_dec_ref(v_a_452_);
lean_dec_ref(v_m_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(lean_object* v_00_u03b2_454_, lean_object* v_a_455_, lean_object* v_x_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_455_, v_x_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_458_, lean_object* v_a_459_, lean_object* v_x_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(v_00_u03b2_458_, v_a_459_, v_x_460_);
lean_dec(v_x_460_);
lean_dec_ref(v_a_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(lean_object* v_e_462_, lean_object* v_m_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
lean_object* v_r_472_; lean_object* v___y_473_; lean_object* v___x_487_; lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_502_; 
v___x_487_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_462_, v_a_465_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_502_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_502_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_502_;
goto v_resetjp_489_;
}
v___jp_471_:
{
lean_object* v___x_474_; lean_object* v_count_475_; lean_object* v_results_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_486_; 
v___x_474_ = lean_st_ref_take(v___y_473_);
v_count_475_ = lean_ctor_get(v___x_474_, 0);
v_results_476_ = lean_ctor_get(v___x_474_, 1);
v_isSharedCheck_486_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_486_ == 0)
{
v___x_478_ = v___x_474_;
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_results_476_);
lean_inc(v_count_475_);
lean_dec(v___x_474_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_486_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_480_; lean_object* v___x_482_; 
lean_inc_ref(v_r_472_);
v___x_480_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_476_, v_e_462_, v_r_472_);
if (v_isShared_479_ == 0)
{
lean_ctor_set(v___x_478_, 1, v___x_480_);
v___x_482_ = v___x_478_;
goto v_reusejp_481_;
}
else
{
lean_object* v_reuseFailAlloc_485_; 
v_reuseFailAlloc_485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_485_, 0, v_count_475_);
lean_ctor_set(v_reuseFailAlloc_485_, 1, v___x_480_);
v___x_482_ = v_reuseFailAlloc_485_;
goto v_reusejp_481_;
}
v_reusejp_481_:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_st_ref_set(v___y_473_, v___x_482_);
v___x_484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_484_, 0, v_r_472_);
return v___x_484_;
}
}
}
v_resetjp_489_:
{
if (lean_obj_tag(v_a_488_) == 1)
{
lean_object* v_val_492_; lean_object* v___x_494_; 
lean_dec_ref(v_m_463_);
lean_dec_ref(v_e_462_);
v_val_492_ = lean_ctor_get(v_a_488_, 0);
lean_inc(v_val_492_);
lean_dec_ref_known(v_a_488_, 1);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v_val_492_);
v___x_494_ = v___x_490_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_val_492_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
uint32_t v___x_496_; uint8_t v___x_497_; 
lean_del_object(v___x_490_);
lean_dec(v_a_488_);
v___x_496_ = 2;
v___x_497_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_462_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; 
lean_inc(v_a_469_);
lean_inc_ref(v_a_468_);
lean_inc(v_a_467_);
lean_inc_ref(v_a_466_);
lean_inc(v_a_465_);
lean_inc(v_a_464_);
v___x_498_ = lean_apply_7(v_m_463_, v_a_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, lean_box(0));
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref_known(v___x_498_, 1);
v_r_472_ = v_a_499_;
v___y_473_ = v_a_465_;
goto v___jp_471_;
}
else
{
lean_dec_ref(v_e_462_);
return v___x_498_;
}
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; 
lean_dec_ref(v_m_463_);
v___x_500_ = lean_box(0);
lean_inc_ref(v_e_462_);
v___x_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_501_, 0, v_e_462_);
lean_ctor_set(v___x_501_, 1, v___x_500_);
v_r_472_ = v___x_501_;
v___y_473_ = v_a_465_;
goto v___jp_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache___boxed(lean_object* v_e_503_, lean_object* v_m_504_, lean_object* v_a_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_503_, v_m_504_, v_a_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_);
lean_dec(v_a_510_);
lean_dec_ref(v_a_509_);
lean_dec(v_a_508_);
lean_dec_ref(v_a_507_);
lean_dec(v_a_506_);
lean_dec(v_a_505_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(lean_object* v_e_513_, lean_object* v_a_514_){
_start:
{
uint8_t v___x_516_; 
v___x_516_ = l_Lean_Expr_hasLooseBVars(v_e_513_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; 
v___x_517_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_513_, v_a_514_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_box(0);
v___x_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg___boxed(lean_object* v_e_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_520_, v_a_521_);
lean_dec(v_a_521_);
lean_dec_ref(v_e_520_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(lean_object* v_e_524_, lean_object* v_a_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_){
_start:
{
lean_object* v___x_532_; 
v___x_532_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_524_, v_a_526_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___boxed(lean_object* v_e_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(v_e_533_, v_a_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_);
lean_dec(v_a_539_);
lean_dec_ref(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_a_536_);
lean_dec(v_a_535_);
lean_dec(v_a_534_);
lean_dec_ref(v_e_533_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(lean_object* v_e_542_, lean_object* v_a_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = l_Lean_Expr_fvarId_x21(v_e_542_);
lean_inc(v___x_547_);
v___x_548_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_547_, v_a_543_);
if (lean_obj_tag(v___x_548_) == 0)
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_567_; 
v_a_549_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_567_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_567_ == 0)
{
v___x_551_ = v___x_548_;
v_isShared_552_ = v_isSharedCheck_567_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_548_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_567_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
if (lean_obj_tag(v_a_549_) == 1)
{
lean_object* v_val_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_565_; 
lean_dec(v___x_547_);
v_val_553_ = lean_ctor_get(v_a_549_, 0);
v_isSharedCheck_565_ = !lean_is_exclusive(v_a_549_);
if (v_isSharedCheck_565_ == 0)
{
v___x_555_ = v_a_549_;
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_val_553_);
lean_dec(v_a_549_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_565_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_557_; lean_object* v___x_559_; 
v___x_557_ = l_Lean_LocalDecl_type(v_val_553_);
lean_dec(v_val_553_);
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v___x_557_);
v___x_559_ = v___x_555_;
goto v_reusejp_558_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_557_);
v___x_559_ = v_reuseFailAlloc_564_;
goto v_reusejp_558_;
}
v_reusejp_558_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_560_, 0, v_e_542_);
lean_ctor_set(v___x_560_, 1, v___x_559_);
if (v_isShared_552_ == 0)
{
lean_ctor_set(v___x_551_, 0, v___x_560_);
v___x_562_ = v___x_551_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
}
}
else
{
lean_object* v___x_566_; 
lean_del_object(v___x_551_);
lean_dec(v_a_549_);
lean_dec_ref(v_e_542_);
v___x_566_ = l_Lean_FVarId_throwUnknown___redArg(v___x_547_, v_a_544_, v_a_545_);
return v___x_566_;
}
}
}
else
{
lean_object* v_a_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec(v___x_547_);
lean_dec_ref(v_e_542_);
v_a_568_ = lean_ctor_get(v___x_548_, 0);
v_isSharedCheck_575_ = !lean_is_exclusive(v___x_548_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v___x_548_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_a_568_);
lean_dec(v___x_548_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_a_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
return v___x_573_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg___boxed(lean_object* v_e_576_, lean_object* v_a_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_576_, v_a_577_, v_a_578_, v_a_579_);
lean_dec(v_a_579_);
lean_dec_ref(v_a_578_);
lean_dec_ref(v_a_577_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(lean_object* v_e_582_, lean_object* v_a_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_582_, v_a_583_, v_a_585_, v_a_586_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___boxed(lean_object* v_e_589_, lean_object* v_a_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_){
_start:
{
lean_object* v_res_595_; 
v_res_595_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(v_e_589_, v_a_590_, v_a_591_, v_a_592_, v_a_593_);
lean_dec(v_a_593_);
lean_dec_ref(v_a_592_);
lean_dec(v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(lean_object* v_e_596_, lean_object* v___y_597_){
_start:
{
uint8_t v___x_599_; 
v___x_599_ = l_Lean_Expr_hasMVar(v_e_596_);
if (v___x_599_ == 0)
{
lean_object* v___x_600_; 
v___x_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_600_, 0, v_e_596_);
return v___x_600_;
}
else
{
lean_object* v___x_601_; lean_object* v_mctx_602_; lean_object* v___x_603_; lean_object* v_fst_604_; lean_object* v_snd_605_; lean_object* v___x_606_; lean_object* v_cache_607_; lean_object* v_zetaDeltaFVarIds_608_; lean_object* v_postponed_609_; lean_object* v_diag_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_619_; 
v___x_601_ = lean_st_ref_get(v___y_597_);
v_mctx_602_ = lean_ctor_get(v___x_601_, 0);
lean_inc_ref(v_mctx_602_);
lean_dec(v___x_601_);
v___x_603_ = l_Lean_instantiateMVarsCore(v_mctx_602_, v_e_596_);
v_fst_604_ = lean_ctor_get(v___x_603_, 0);
lean_inc(v_fst_604_);
v_snd_605_ = lean_ctor_get(v___x_603_, 1);
lean_inc(v_snd_605_);
lean_dec_ref(v___x_603_);
v___x_606_ = lean_st_ref_take(v___y_597_);
v_cache_607_ = lean_ctor_get(v___x_606_, 1);
v_zetaDeltaFVarIds_608_ = lean_ctor_get(v___x_606_, 2);
v_postponed_609_ = lean_ctor_get(v___x_606_, 3);
v_diag_610_ = lean_ctor_get(v___x_606_, 4);
v_isSharedCheck_619_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_619_ == 0)
{
lean_object* v_unused_620_; 
v_unused_620_ = lean_ctor_get(v___x_606_, 0);
lean_dec(v_unused_620_);
v___x_612_ = v___x_606_;
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_diag_610_);
lean_inc(v_postponed_609_);
lean_inc(v_zetaDeltaFVarIds_608_);
lean_inc(v_cache_607_);
lean_dec(v___x_606_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_619_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v___x_615_; 
if (v_isShared_613_ == 0)
{
lean_ctor_set(v___x_612_, 0, v_snd_605_);
v___x_615_ = v___x_612_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_618_; 
v_reuseFailAlloc_618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_618_, 0, v_snd_605_);
lean_ctor_set(v_reuseFailAlloc_618_, 1, v_cache_607_);
lean_ctor_set(v_reuseFailAlloc_618_, 2, v_zetaDeltaFVarIds_608_);
lean_ctor_set(v_reuseFailAlloc_618_, 3, v_postponed_609_);
lean_ctor_set(v_reuseFailAlloc_618_, 4, v_diag_610_);
v___x_615_ = v_reuseFailAlloc_618_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_st_ref_set(v___y_597_, v___x_615_);
v___x_617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_617_, 0, v_fst_604_);
return v___x_617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg___boxed(lean_object* v_e_621_, lean_object* v___y_622_, lean_object* v___y_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_621_, v___y_622_);
lean_dec(v___y_622_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(lean_object* v_e_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_625_, v___y_629_);
return v___x_633_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___boxed(lean_object* v_e_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(v_e_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec(v___y_635_);
return v_res_642_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(lean_object* v_k_643_, lean_object* v_t_644_){
_start:
{
if (lean_obj_tag(v_t_644_) == 0)
{
lean_object* v_k_645_; lean_object* v_l_646_; lean_object* v_r_647_; uint8_t v___x_648_; 
v_k_645_ = lean_ctor_get(v_t_644_, 1);
v_l_646_ = lean_ctor_get(v_t_644_, 3);
v_r_647_ = lean_ctor_get(v_t_644_, 4);
v___x_648_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_643_, v_k_645_);
switch(v___x_648_)
{
case 0:
{
v_t_644_ = v_l_646_;
goto _start;
}
case 1:
{
uint8_t v___x_650_; 
v___x_650_ = 1;
return v___x_650_;
}
default: 
{
v_t_644_ = v_r_647_;
goto _start;
}
}
}
else
{
uint8_t v___x_652_; 
v___x_652_ = 0;
return v___x_652_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg___boxed(lean_object* v_k_653_, lean_object* v_t_654_){
_start:
{
uint8_t v_res_655_; lean_object* v_r_656_; 
v_res_655_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_653_, v_t_654_);
lean_dec(v_t_654_);
lean_dec(v_k_653_);
v_r_656_ = lean_box(v_res_655_);
return v_r_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(lean_object* v_as_657_, size_t v_sz_658_, size_t v_i_659_, lean_object* v_b_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_){
_start:
{
lean_object* v_a_667_; uint8_t v___x_671_; 
v___x_671_ = lean_usize_dec_lt(v_i_659_, v_sz_658_);
if (v___x_671_ == 0)
{
lean_object* v___x_672_; 
v___x_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_672_, 0, v_b_660_);
return v___x_672_;
}
else
{
lean_object* v_fst_673_; lean_object* v_snd_674_; lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_722_; 
v_fst_673_ = lean_ctor_get(v_b_660_, 0);
v_snd_674_ = lean_ctor_get(v_b_660_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_b_660_);
if (v_isSharedCheck_722_ == 0)
{
v___x_676_ = v_b_660_;
v_isShared_677_ = v_isSharedCheck_722_;
goto v_resetjp_675_;
}
else
{
lean_inc(v_snd_674_);
lean_inc(v_fst_673_);
lean_dec(v_b_660_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_722_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_a_678_; uint8_t v___x_679_; 
v_a_678_ = lean_array_uget_borrowed(v_as_657_, v_i_659_);
v___x_679_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_a_678_, v_fst_673_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___x_699_; 
lean_inc_n(v_a_678_, 2);
v___x_680_ = l_Lean_FVarIdSet_insert(v_fst_673_, v_a_678_);
v___x_699_ = l_Lean_FVarId_isLetVar___redArg(v_a_678_, v___x_679_, v___y_661_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; uint8_t v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = lean_unbox(v_a_700_);
lean_dec(v_a_700_);
if (v___x_701_ == 0)
{
v___y_682_ = v___y_661_;
v___y_683_ = v___y_663_;
v___y_684_ = v___y_664_;
goto v___jp_681_;
}
else
{
lean_object* v___x_702_; 
lean_inc(v_a_678_);
v___x_702_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_a_678_, v___y_662_);
if (lean_obj_tag(v___x_702_) == 0)
{
lean_dec_ref_known(v___x_702_, 1);
v___y_682_ = v___y_661_;
v___y_683_ = v___y_663_;
v___y_684_ = v___y_664_;
goto v___jp_681_;
}
else
{
lean_object* v_a_703_; lean_object* v___x_705_; uint8_t v_isShared_706_; uint8_t v_isSharedCheck_710_; 
lean_dec(v___x_680_);
lean_del_object(v___x_676_);
lean_dec(v_snd_674_);
v_a_703_ = lean_ctor_get(v___x_702_, 0);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_710_ == 0)
{
v___x_705_ = v___x_702_;
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
else
{
lean_inc(v_a_703_);
lean_dec(v___x_702_);
v___x_705_ = lean_box(0);
v_isShared_706_ = v_isSharedCheck_710_;
goto v_resetjp_704_;
}
v_resetjp_704_:
{
lean_object* v___x_708_; 
if (v_isShared_706_ == 0)
{
v___x_708_ = v___x_705_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v_a_703_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
}
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v___x_680_);
lean_del_object(v___x_676_);
lean_dec(v_snd_674_);
v_a_711_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_699_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_699_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
}
}
}
v___jp_681_:
{
lean_object* v___x_685_; 
lean_inc(v_a_678_);
v___x_685_ = l_Lean_FVarId_getType___redArg(v_a_678_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_685_) == 0)
{
lean_object* v_a_686_; lean_object* v___x_687_; lean_object* v___x_689_; 
v_a_686_ = lean_ctor_get(v___x_685_, 0);
lean_inc(v_a_686_);
lean_dec_ref_known(v___x_685_, 1);
v___x_687_ = lean_array_push(v_snd_674_, v_a_686_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 1, v___x_687_);
lean_ctor_set(v___x_676_, 0, v___x_680_);
v___x_689_ = v___x_676_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_690_; 
v_reuseFailAlloc_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_690_, 0, v___x_680_);
lean_ctor_set(v_reuseFailAlloc_690_, 1, v___x_687_);
v___x_689_ = v_reuseFailAlloc_690_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
v_a_667_ = v___x_689_;
goto v___jp_666_;
}
}
else
{
lean_object* v_a_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_698_; 
lean_dec(v___x_680_);
lean_del_object(v___x_676_);
lean_dec(v_snd_674_);
v_a_691_ = lean_ctor_get(v___x_685_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_685_);
if (v_isSharedCheck_698_ == 0)
{
v___x_693_ = v___x_685_;
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_a_691_);
lean_dec(v___x_685_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_698_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_696_; 
if (v_isShared_694_ == 0)
{
v___x_696_ = v___x_693_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v_a_691_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
return v___x_696_;
}
}
}
}
}
else
{
lean_object* v___x_720_; 
if (v_isShared_677_ == 0)
{
v___x_720_ = v___x_676_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_fst_673_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_snd_674_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
v_a_667_ = v___x_720_;
goto v___jp_666_;
}
}
}
}
v___jp_666_:
{
size_t v___x_668_; size_t v___x_669_; 
v___x_668_ = ((size_t)1ULL);
v___x_669_ = lean_usize_add(v_i_659_, v___x_668_);
v_i_659_ = v___x_669_;
v_b_660_ = v_a_667_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg___boxed(lean_object* v_as_723_, lean_object* v_sz_724_, lean_object* v_i_725_, lean_object* v_b_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
size_t v_sz_boxed_732_; size_t v_i_boxed_733_; lean_object* v_res_734_; 
v_sz_boxed_732_ = lean_unbox_usize(v_sz_724_);
lean_dec(v_sz_724_);
v_i_boxed_733_ = lean_unbox_usize(v_i_725_);
lean_dec(v_i_725_);
v_res_734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_723_, v_sz_boxed_732_, v_i_boxed_733_, v_b_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_);
lean_dec(v___y_730_);
lean_dec_ref(v___y_729_);
lean_dec(v___y_728_);
lean_dec_ref(v___y_727_);
lean_dec_ref(v_as_723_);
return v_res_734_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v___x_736_ = lean_unsigned_to_nat(16u);
v___x_737_ = lean_mk_array(v___x_736_, v___x_735_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_743_; lean_object* v_visited_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = ((lean_object*)(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2));
v_visited_744_ = lean_box(1);
v___x_745_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_visited_744_);
lean_ctor_set(v___x_746_, 2, v___x_743_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object* v_a_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_802_; 
v_fst_755_ = lean_ctor_get(v_a_747_, 0);
v_snd_756_ = lean_ctor_get(v_a_747_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_a_747_);
if (v_isSharedCheck_802_ == 0)
{
v___x_758_ = v_a_747_;
v_isShared_759_ = v_isSharedCheck_802_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_inc(v_fst_755_);
lean_dec(v_a_747_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_802_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; lean_object* v___x_761_; uint8_t v___x_762_; 
v___x_760_ = lean_array_get_size(v_snd_756_);
v___x_761_ = lean_unsigned_to_nat(0u);
v___x_762_ = lean_nat_dec_eq(v___x_760_, v___x_761_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_763_ = l_Lean_instInhabitedExpr;
v___x_764_ = lean_unsigned_to_nat(1u);
v___x_765_ = lean_nat_sub(v___x_760_, v___x_764_);
v___x_766_ = lean_array_get_borrowed(v___x_763_, v_snd_756_, v___x_765_);
lean_dec(v___x_765_);
lean_inc(v___x_766_);
v___x_767_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v___x_766_, v___y_751_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v_fvarIds_771_; lean_object* v___x_772_; lean_object* v___x_774_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v___x_769_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3);
v___x_770_ = l_Lean_collectFVars(v___x_769_, v_a_768_);
v_fvarIds_771_ = lean_ctor_get(v___x_770_, 2);
lean_inc_ref(v_fvarIds_771_);
lean_dec_ref(v___x_770_);
v___x_772_ = lean_array_pop(v_snd_756_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v___x_772_);
v___x_774_ = v___x_758_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_fst_755_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v___x_772_);
v___x_774_ = v_reuseFailAlloc_789_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
size_t v_sz_775_; size_t v___x_776_; lean_object* v___x_777_; 
v_sz_775_ = lean_array_size(v_fvarIds_771_);
v___x_776_ = ((size_t)0ULL);
v___x_777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_fvarIds_771_, v_sz_775_, v___x_776_, v___x_774_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_fvarIds_771_);
if (lean_obj_tag(v___x_777_) == 0)
{
lean_object* v_a_778_; lean_object* v_fst_779_; lean_object* v_snd_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_788_; 
v_a_778_ = lean_ctor_get(v___x_777_, 0);
lean_inc(v_a_778_);
lean_dec_ref_known(v___x_777_, 1);
v_fst_779_ = lean_ctor_get(v_a_778_, 0);
v_snd_780_ = lean_ctor_get(v_a_778_, 1);
v_isSharedCheck_788_ = !lean_is_exclusive(v_a_778_);
if (v_isSharedCheck_788_ == 0)
{
v___x_782_ = v_a_778_;
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_snd_780_);
lean_inc(v_fst_779_);
lean_dec(v_a_778_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_788_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
if (v_isShared_783_ == 0)
{
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_fst_779_);
lean_ctor_set(v_reuseFailAlloc_787_, 1, v_snd_780_);
v___x_785_ = v_reuseFailAlloc_787_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
v_a_747_ = v___x_785_;
goto _start;
}
}
}
else
{
return v___x_777_;
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
lean_del_object(v___x_758_);
lean_dec(v_snd_756_);
lean_dec(v_fst_755_);
v_a_790_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_767_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_767_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
else
{
lean_object* v___x_799_; 
if (v_isShared_759_ == 0)
{
v___x_799_ = v___x_758_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_fst_755_);
lean_ctor_set(v_reuseFailAlloc_801_, 1, v_snd_756_);
v___x_799_ = v_reuseFailAlloc_801_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_800_; 
v___x_800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_799_);
return v___x_800_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object* v_a_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec(v___y_804_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object* v_e_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_){
_start:
{
lean_object* v_visited_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_worklist_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_visited_820_ = lean_box(1);
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_mk_empty_array_with_capacity(v___x_821_);
v_worklist_823_ = lean_array_push(v___x_822_, v_e_812_);
v___x_824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_824_, 0, v_visited_820_);
lean_ctor_set(v___x_824_, 1, v_worklist_823_);
v___x_825_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v___x_824_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
if (lean_obj_tag(v___x_825_) == 0)
{
lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_833_; 
v_isSharedCheck_833_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_833_ == 0)
{
lean_object* v_unused_834_; 
v_unused_834_ = lean_ctor_get(v___x_825_, 0);
lean_dec(v_unused_834_);
v___x_827_ = v___x_825_;
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
else
{
lean_dec(v___x_825_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_833_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v___x_829_; lean_object* v___x_831_; 
v___x_829_ = lean_box(0);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_829_);
v___x_831_ = v___x_827_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
v_a_835_ = lean_ctor_get(v___x_825_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_825_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_825_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_825_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object* v_e_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v_e_843_, v_a_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_);
lean_dec(v_a_849_);
lean_dec_ref(v_a_848_);
lean_dec(v_a_847_);
lean_dec_ref(v_a_846_);
lean_dec(v_a_845_);
lean_dec(v_a_844_);
return v_res_851_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object* v_00_u03b2_852_, lean_object* v_k_853_, lean_object* v_t_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_853_, v_t_854_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object* v_00_u03b2_856_, lean_object* v_k_857_, lean_object* v_t_858_){
_start:
{
uint8_t v_res_859_; lean_object* v_r_860_; 
v_res_859_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(v_00_u03b2_856_, v_k_857_, v_t_858_);
lean_dec(v_t_858_);
lean_dec(v_k_857_);
v_r_860_ = lean_box(v_res_859_);
return v_r_860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object* v_as_861_, size_t v_sz_862_, size_t v_i_863_, lean_object* v_b_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_861_, v_sz_862_, v_i_863_, v_b_864_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object* v_as_873_, lean_object* v_sz_874_, lean_object* v_i_875_, lean_object* v_b_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
size_t v_sz_boxed_884_; size_t v_i_boxed_885_; lean_object* v_res_886_; 
v_sz_boxed_884_ = lean_unbox_usize(v_sz_874_);
lean_dec(v_sz_874_);
v_i_boxed_885_ = lean_unbox_usize(v_i_875_);
lean_dec(v_i_875_);
v_res_886_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(v_as_873_, v_sz_boxed_884_, v_i_boxed_885_, v_b_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v_as_873_);
return v_res_886_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_inst_887_, lean_object* v_a_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_inst_897_, lean_object* v_a_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_inst_897_, v_a_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
lean_dec(v___y_904_);
lean_dec_ref(v___y_903_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_899_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object* v_mvarId_907_, lean_object* v___y_908_){
_start:
{
lean_object* v___x_910_; lean_object* v_mctx_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_910_ = lean_st_ref_get(v___y_908_);
v_mctx_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc_ref(v_mctx_911_);
lean_dec(v___x_910_);
v___x_912_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_911_, v_mvarId_907_);
lean_dec_ref(v_mctx_911_);
v___x_913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object* v_mvarId_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_914_, v___y_915_);
lean_dec(v___y_915_);
lean_dec(v_mvarId_914_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object* v_mvarId_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_){
_start:
{
lean_object* v___x_926_; 
v___x_926_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_918_, v___y_922_);
return v___x_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object* v_mvarId_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
lean_dec(v_mvarId_927_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object* v_a_936_, lean_object* v_as_937_, size_t v_sz_938_, size_t v_i_939_, lean_object* v_b_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_a_949_; uint8_t v___x_953_; 
v___x_953_ = lean_usize_dec_lt(v_i_939_, v_sz_938_);
if (v___x_953_ == 0)
{
lean_object* v___x_954_; 
lean_dec_ref(v_a_936_);
v___x_954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_954_, 0, v_b_940_);
return v___x_954_;
}
else
{
lean_object* v_array_955_; lean_object* v_start_956_; lean_object* v_stop_957_; uint8_t v___x_958_; 
v_array_955_ = lean_ctor_get(v_b_940_, 0);
v_start_956_ = lean_ctor_get(v_b_940_, 1);
v_stop_957_ = lean_ctor_get(v_b_940_, 2);
v___x_958_ = lean_nat_dec_lt(v_start_956_, v_stop_957_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v_a_936_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v_b_940_);
return v___x_959_;
}
else
{
lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_983_; 
lean_inc(v_stop_957_);
lean_inc(v_start_956_);
lean_inc_ref(v_array_955_);
v_isSharedCheck_983_ = !lean_is_exclusive(v_b_940_);
if (v_isSharedCheck_983_ == 0)
{
lean_object* v_unused_984_; lean_object* v_unused_985_; lean_object* v_unused_986_; 
v_unused_984_ = lean_ctor_get(v_b_940_, 2);
lean_dec(v_unused_984_);
v_unused_985_ = lean_ctor_get(v_b_940_, 1);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_b_940_, 0);
lean_dec(v_unused_986_);
v___x_961_ = v_b_940_;
v_isShared_962_ = v_isSharedCheck_983_;
goto v_resetjp_960_;
}
else
{
lean_dec(v_b_940_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_983_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
lean_object* v_lctx_963_; lean_object* v___x_964_; lean_object* v_a_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v_lctx_963_ = lean_ctor_get(v_a_936_, 1);
v___x_964_ = lean_array_fget(v_array_955_, v_start_956_);
v_a_965_ = lean_array_uget_borrowed(v_as_937_, v_i_939_);
v___x_966_ = lean_unsigned_to_nat(1u);
v___x_967_ = lean_nat_add(v_start_956_, v___x_966_);
lean_dec(v_start_956_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 1, v___x_967_);
v___x_969_ = v___x_961_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_982_; 
v_reuseFailAlloc_982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_982_, 0, v_array_955_);
lean_ctor_set(v_reuseFailAlloc_982_, 1, v___x_967_);
lean_ctor_set(v_reuseFailAlloc_982_, 2, v_stop_957_);
v___x_969_ = v_reuseFailAlloc_982_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
lean_object* v___x_970_; uint8_t v___x_971_; uint8_t v___x_972_; 
lean_inc_ref(v_lctx_963_);
v___x_970_ = l_Lean_LocalContext_getFVar_x21(v_lctx_963_, v_a_965_);
v___x_971_ = 0;
v___x_972_ = l_Lean_LocalDecl_isLet(v___x_970_, v___x_971_);
lean_dec_ref(v___x_970_);
if (v___x_972_ == 0)
{
lean_dec(v___x_964_);
v_a_949_ = v___x_969_;
goto v___jp_948_;
}
else
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v___x_964_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_);
if (lean_obj_tag(v___x_973_) == 0)
{
lean_dec_ref_known(v___x_973_, 1);
v_a_949_ = v___x_969_;
goto v___jp_948_;
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec_ref(v___x_969_);
lean_dec_ref(v_a_936_);
v_a_974_ = lean_ctor_get(v___x_973_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_973_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_973_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_973_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
}
}
}
v___jp_948_:
{
size_t v___x_950_; size_t v___x_951_; 
v___x_950_ = ((size_t)1ULL);
v___x_951_ = lean_usize_add(v_i_939_, v___x_950_);
v_i_939_ = v___x_951_;
v_b_940_ = v_a_949_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object* v_a_987_, lean_object* v_as_988_, lean_object* v_sz_989_, lean_object* v_i_990_, lean_object* v_b_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
size_t v_sz_boxed_999_; size_t v_i_boxed_1000_; lean_object* v_res_1001_; 
v_sz_boxed_999_ = lean_unbox_usize(v_sz_989_);
lean_dec(v_sz_989_);
v_i_boxed_1000_ = lean_unbox_usize(v_i_990_);
lean_dec(v_i_990_);
v_res_1001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_987_, v_as_988_, v_sz_boxed_999_, v_i_boxed_1000_, v_b_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v_as_988_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object* v_as_1002_, lean_object* v___y_1003_){
_start:
{
if (lean_obj_tag(v_as_1002_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1006_; 
v___x_1005_ = lean_box(0);
v___x_1006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1006_, 0, v___x_1005_);
return v___x_1006_;
}
else
{
lean_object* v_head_1007_; lean_object* v_tail_1008_; lean_object* v___x_1009_; 
v_head_1007_ = lean_ctor_get(v_as_1002_, 0);
lean_inc(v_head_1007_);
v_tail_1008_ = lean_ctor_get(v_as_1002_, 1);
lean_inc(v_tail_1008_);
lean_dec_ref_known(v_as_1002_, 2);
v___x_1009_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_head_1007_, v___y_1003_);
if (lean_obj_tag(v___x_1009_) == 0)
{
lean_dec_ref_known(v___x_1009_, 1);
v_as_1002_ = v_tail_1008_;
goto _start;
}
else
{
lean_dec(v_tail_1008_);
return v___x_1009_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object* v_as_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_){
_start:
{
lean_object* v_res_1014_; 
v_res_1014_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1011_, v___y_1012_);
lean_dec(v___y_1012_);
return v_res_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object* v_mvarId_1015_, lean_object* v_args_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_){
_start:
{
lean_object* v___x_1024_; lean_object* v_a_1025_; lean_object* v___x_1027_; uint8_t v_isShared_1028_; uint8_t v_isSharedCheck_1081_; 
v___x_1024_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1015_, v_a_1020_);
v_a_1025_ = lean_ctor_get(v___x_1024_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1024_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1027_ = v___x_1024_;
v_isShared_1028_ = v_isSharedCheck_1081_;
goto v_resetjp_1026_;
}
else
{
lean_inc(v_a_1025_);
lean_dec(v___x_1024_);
v___x_1027_ = lean_box(0);
v_isShared_1028_ = v_isSharedCheck_1081_;
goto v_resetjp_1026_;
}
v_resetjp_1026_:
{
if (lean_obj_tag(v_a_1025_) == 1)
{
lean_object* v_val_1029_; lean_object* v_fvars_1030_; lean_object* v_mvarIdPending_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; uint8_t v___x_1034_; 
lean_del_object(v___x_1027_);
v_val_1029_ = lean_ctor_get(v_a_1025_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v_a_1025_, 1);
v_fvars_1030_ = lean_ctor_get(v_val_1029_, 0);
lean_inc_ref(v_fvars_1030_);
v_mvarIdPending_1031_ = lean_ctor_get(v_val_1029_, 1);
lean_inc(v_mvarIdPending_1031_);
lean_dec(v_val_1029_);
v___x_1032_ = lean_array_get_size(v_fvars_1030_);
v___x_1033_ = lean_array_get_size(v_args_1016_);
v___x_1034_ = lean_nat_dec_le(v___x_1032_, v___x_1033_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec(v_mvarIdPending_1031_);
lean_dec_ref(v_fvars_1030_);
lean_dec_ref(v_args_1016_);
lean_inc(v_a_1017_);
v___x_1035_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_a_1017_, v_a_1020_);
if (lean_obj_tag(v___x_1035_) == 0)
{
lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1035_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v___x_1035_, 0);
lean_dec(v_unused_1044_);
v___x_1037_ = v___x_1035_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_dec(v___x_1035_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
v___x_1039_ = lean_box(0);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
else
{
return v___x_1035_;
}
}
else
{
lean_object* v___x_1045_; 
v___x_1045_ = l_Lean_MVarId_getDecl(v_mvarIdPending_1031_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
if (lean_obj_tag(v___x_1045_) == 0)
{
lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; size_t v_sz_1049_; size_t v___x_1050_; lean_object* v___x_1051_; 
v_a_1046_ = lean_ctor_get(v___x_1045_, 0);
lean_inc(v_a_1046_);
lean_dec_ref_known(v___x_1045_, 1);
v___x_1047_ = lean_unsigned_to_nat(0u);
v___x_1048_ = l_Array_toSubarray___redArg(v_args_1016_, v___x_1047_, v___x_1033_);
v_sz_1049_ = lean_array_size(v_fvars_1030_);
v___x_1050_ = ((size_t)0ULL);
v___x_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1046_, v_fvars_1030_, v_sz_1049_, v___x_1050_, v___x_1048_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec_ref(v_fvars_1030_);
if (lean_obj_tag(v___x_1051_) == 0)
{
lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1059_; 
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1051_, 0);
lean_dec(v_unused_1060_);
v___x_1053_ = v___x_1051_;
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
else
{
lean_dec(v___x_1051_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1059_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; lean_object* v___x_1057_; 
v___x_1055_ = lean_box(0);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1055_);
v___x_1057_ = v___x_1053_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
v_a_1061_ = lean_ctor_get(v___x_1051_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1051_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1051_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1051_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v_a_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1076_; 
lean_dec_ref(v_fvars_1030_);
lean_dec_ref(v_args_1016_);
v_a_1069_ = lean_ctor_get(v___x_1045_, 0);
v_isSharedCheck_1076_ = !lean_is_exclusive(v___x_1045_);
if (v_isSharedCheck_1076_ == 0)
{
v___x_1071_ = v___x_1045_;
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_a_1069_);
lean_dec(v___x_1045_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1076_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v___x_1074_; 
if (v_isShared_1072_ == 0)
{
v___x_1074_ = v___x_1071_;
goto v_reusejp_1073_;
}
else
{
lean_object* v_reuseFailAlloc_1075_; 
v_reuseFailAlloc_1075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1075_, 0, v_a_1069_);
v___x_1074_ = v_reuseFailAlloc_1075_;
goto v_reusejp_1073_;
}
v_reusejp_1073_:
{
return v___x_1074_;
}
}
}
}
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1079_; 
lean_dec(v_a_1025_);
lean_dec_ref(v_args_1016_);
v___x_1077_ = lean_box(0);
if (v_isShared_1028_ == 0)
{
lean_ctor_set(v___x_1027_, 0, v___x_1077_);
v___x_1079_ = v___x_1027_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v___x_1077_);
v___x_1079_ = v_reuseFailAlloc_1080_;
goto v_reusejp_1078_;
}
v_reusejp_1078_:
{
return v___x_1079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object* v_mvarId_1082_, lean_object* v_args_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1082_, v_args_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec(v_a_1084_);
lean_dec(v_mvarId_1082_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object* v_as_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1092_, v___y_1096_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object* v_as_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_);
lean_dec(v___y_1107_);
lean_dec_ref(v___y_1106_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object* v_e_1112_, lean_object* v_a_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = l_Lean_Expr_mvarId_x21(v_e_1112_);
v___x_1121_ = l_Lean_MVarId_findDecl_x3f___redArg(v___x_1120_, v_a_1116_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1152_; 
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1152_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1152_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
if (lean_obj_tag(v_a_1122_) == 1)
{
lean_object* v_val_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1150_; 
v_val_1126_ = lean_ctor_get(v_a_1122_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_a_1122_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1128_ = v_a_1122_;
v_isShared_1129_ = v_isSharedCheck_1150_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_val_1126_);
lean_dec(v_a_1122_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1150_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
uint8_t v___x_1139_; 
v___x_1139_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1113_);
if (v___x_1139_ == 0)
{
lean_dec(v___x_1120_);
goto v___jp_1130_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
v___x_1140_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_1141_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v___x_1120_, v___x_1140_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
lean_dec(v___x_1120_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_dec_ref_known(v___x_1141_, 1);
goto v___jp_1130_;
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1149_; 
lean_del_object(v___x_1128_);
lean_dec(v_val_1126_);
lean_del_object(v___x_1124_);
lean_dec_ref(v_e_1112_);
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1149_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1144_ = v___x_1141_;
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1141_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1149_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
lean_object* v___x_1147_; 
if (v_isShared_1145_ == 0)
{
v___x_1147_ = v___x_1144_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1142_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
v___jp_1130_:
{
lean_object* v_type_1131_; lean_object* v___x_1133_; 
v_type_1131_ = lean_ctor_get(v_val_1126_, 2);
lean_inc_ref(v_type_1131_);
lean_dec(v_val_1126_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 0, v_type_1131_);
v___x_1133_ = v___x_1128_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_type_1131_);
v___x_1133_ = v_reuseFailAlloc_1138_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
lean_object* v___x_1134_; lean_object* v___x_1136_; 
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v_e_1112_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
if (v_isShared_1125_ == 0)
{
lean_ctor_set(v___x_1124_, 0, v___x_1134_);
v___x_1136_ = v___x_1124_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v___x_1134_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
}
else
{
lean_object* v___x_1151_; 
lean_del_object(v___x_1124_);
lean_dec(v_a_1122_);
lean_dec_ref(v_e_1112_);
v___x_1151_ = l_Lean_Meta_throwUnknownMVar___redArg(v___x_1120_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_);
return v___x_1151_;
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v___x_1120_);
lean_dec_ref(v_e_1112_);
v_a_1153_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1121_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1121_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object* v_e_1161_, lean_object* v_a_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_){
_start:
{
lean_object* v_res_1169_; 
v_res_1169_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_);
lean_dec(v_a_1167_);
lean_dec_ref(v_a_1166_);
lean_dec(v_a_1165_);
lean_dec_ref(v_a_1164_);
lean_dec(v_a_1163_);
lean_dec(v_a_1162_);
return v_res_1169_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1170_; 
v___x_1170_ = l_instMonadEIO(lean_box(0));
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object* v_msg_1175_, lean_object* v___y_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v_toApplicative_1185_; lean_object* v___x_1187_; uint8_t v_isShared_1188_; uint8_t v_isSharedCheck_1248_; 
v___x_1183_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0);
v___x_1184_ = l_StateRefT_x27_instMonad___redArg(v___x_1183_);
v_toApplicative_1185_ = lean_ctor_get(v___x_1184_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1184_);
if (v_isSharedCheck_1248_ == 0)
{
lean_object* v_unused_1249_; 
v_unused_1249_ = lean_ctor_get(v___x_1184_, 1);
lean_dec(v_unused_1249_);
v___x_1187_ = v___x_1184_;
v_isShared_1188_ = v_isSharedCheck_1248_;
goto v_resetjp_1186_;
}
else
{
lean_inc(v_toApplicative_1185_);
lean_dec(v___x_1184_);
v___x_1187_ = lean_box(0);
v_isShared_1188_ = v_isSharedCheck_1248_;
goto v_resetjp_1186_;
}
v_resetjp_1186_:
{
lean_object* v_toFunctor_1189_; lean_object* v_toSeq_1190_; lean_object* v_toSeqLeft_1191_; lean_object* v_toSeqRight_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1246_; 
v_toFunctor_1189_ = lean_ctor_get(v_toApplicative_1185_, 0);
v_toSeq_1190_ = lean_ctor_get(v_toApplicative_1185_, 2);
v_toSeqLeft_1191_ = lean_ctor_get(v_toApplicative_1185_, 3);
v_toSeqRight_1192_ = lean_ctor_get(v_toApplicative_1185_, 4);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_toApplicative_1185_);
if (v_isSharedCheck_1246_ == 0)
{
lean_object* v_unused_1247_; 
v_unused_1247_ = lean_ctor_get(v_toApplicative_1185_, 1);
lean_dec(v_unused_1247_);
v___x_1194_ = v_toApplicative_1185_;
v_isShared_1195_ = v_isSharedCheck_1246_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_toSeqRight_1192_);
lean_inc(v_toSeqLeft_1191_);
lean_inc(v_toSeq_1190_);
lean_inc(v_toFunctor_1189_);
lean_dec(v_toApplicative_1185_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1246_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___f_1196_; lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___x_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___x_1205_; 
v___f_1196_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1));
v___f_1197_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1189_);
v___f_1198_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1198_, 0, v_toFunctor_1189_);
v___f_1199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1199_, 0, v_toFunctor_1189_);
v___x_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___f_1198_);
lean_ctor_set(v___x_1200_, 1, v___f_1199_);
v___f_1201_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1201_, 0, v_toSeqRight_1192_);
v___f_1202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1202_, 0, v_toSeqLeft_1191_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toSeq_1190_);
if (v_isShared_1195_ == 0)
{
lean_ctor_set(v___x_1194_, 4, v___f_1201_);
lean_ctor_set(v___x_1194_, 3, v___f_1202_);
lean_ctor_set(v___x_1194_, 2, v___f_1203_);
lean_ctor_set(v___x_1194_, 1, v___f_1196_);
lean_ctor_set(v___x_1194_, 0, v___x_1200_);
v___x_1205_ = v___x_1194_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1200_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___f_1196_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v___f_1203_);
lean_ctor_set(v_reuseFailAlloc_1245_, 3, v___f_1202_);
lean_ctor_set(v_reuseFailAlloc_1245_, 4, v___f_1201_);
v___x_1205_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1207_; 
if (v_isShared_1188_ == 0)
{
lean_ctor_set(v___x_1187_, 1, v___f_1197_);
lean_ctor_set(v___x_1187_, 0, v___x_1205_);
v___x_1207_ = v___x_1187_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___f_1197_);
v___x_1207_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
lean_object* v___x_1208_; lean_object* v_toApplicative_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1242_; 
v___x_1208_ = l_StateRefT_x27_instMonad___redArg(v___x_1207_);
v_toApplicative_1209_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1242_ == 0)
{
lean_object* v_unused_1243_; 
v_unused_1243_ = lean_ctor_get(v___x_1208_, 1);
lean_dec(v_unused_1243_);
v___x_1211_ = v___x_1208_;
v_isShared_1212_ = v_isSharedCheck_1242_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_toApplicative_1209_);
lean_dec(v___x_1208_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1242_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v_toFunctor_1213_; lean_object* v_toSeq_1214_; lean_object* v_toSeqLeft_1215_; lean_object* v_toSeqRight_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1240_; 
v_toFunctor_1213_ = lean_ctor_get(v_toApplicative_1209_, 0);
v_toSeq_1214_ = lean_ctor_get(v_toApplicative_1209_, 2);
v_toSeqLeft_1215_ = lean_ctor_get(v_toApplicative_1209_, 3);
v_toSeqRight_1216_ = lean_ctor_get(v_toApplicative_1209_, 4);
v_isSharedCheck_1240_ = !lean_is_exclusive(v_toApplicative_1209_);
if (v_isSharedCheck_1240_ == 0)
{
lean_object* v_unused_1241_; 
v_unused_1241_ = lean_ctor_get(v_toApplicative_1209_, 1);
lean_dec(v_unused_1241_);
v___x_1218_ = v_toApplicative_1209_;
v_isShared_1219_ = v_isSharedCheck_1240_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_toSeqRight_1216_);
lean_inc(v_toSeqLeft_1215_);
lean_inc(v_toSeq_1214_);
lean_inc(v_toFunctor_1213_);
lean_dec(v_toApplicative_1209_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1240_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___f_1220_; lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___x_1224_; lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___x_1229_; 
v___f_1220_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3));
v___f_1221_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1213_);
v___f_1222_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1222_, 0, v_toFunctor_1213_);
v___f_1223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1223_, 0, v_toFunctor_1213_);
v___x_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1224_, 0, v___f_1222_);
lean_ctor_set(v___x_1224_, 1, v___f_1223_);
v___f_1225_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1225_, 0, v_toSeqRight_1216_);
v___f_1226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1226_, 0, v_toSeqLeft_1215_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toSeq_1214_);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 4, v___f_1225_);
lean_ctor_set(v___x_1218_, 3, v___f_1226_);
lean_ctor_set(v___x_1218_, 2, v___f_1227_);
lean_ctor_set(v___x_1218_, 1, v___f_1220_);
lean_ctor_set(v___x_1218_, 0, v___x_1224_);
v___x_1229_ = v___x_1218_;
goto v_reusejp_1228_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1224_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___f_1220_);
lean_ctor_set(v_reuseFailAlloc_1239_, 2, v___f_1227_);
lean_ctor_set(v_reuseFailAlloc_1239_, 3, v___f_1226_);
lean_ctor_set(v_reuseFailAlloc_1239_, 4, v___f_1225_);
v___x_1229_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1228_;
}
v_reusejp_1228_:
{
lean_object* v___x_1231_; 
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___f_1221_);
lean_ctor_set(v___x_1211_, 0, v___x_1229_);
v___x_1231_ = v___x_1211_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1238_, 1, v___f_1221_);
v___x_1231_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___f_1235_; lean_object* v___x_1519__overap_1236_; lean_object* v___x_1237_; 
v___x_1232_ = l_StateRefT_x27_instMonad___redArg(v___x_1231_);
v___x_1233_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1234_ = l_instInhabitedOfMonad___redArg(v___x_1232_, v___x_1233_);
v___f_1235_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1235_, 0, v___x_1234_);
v___x_1519__overap_1236_ = lean_panic_fn_borrowed(v___f_1235_, v_msg_1175_);
lean_dec_ref(v___f_1235_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc(v___y_1177_);
lean_inc(v___y_1176_);
v___x_1237_ = lean_apply_7(v___x_1519__overap_1236_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, lean_box(0));
return v___x_1237_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object* v_msg_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
return v_res_1258_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1259_; 
v___x_1259_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
v___x_1260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1260_);
return v___x_1261_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1263_ = lean_unsigned_to_nat(0u);
v___x_1264_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v___x_1263_);
lean_ctor_set(v___x_1264_, 2, v___x_1263_);
lean_ctor_set(v___x_1264_, 3, v___x_1263_);
lean_ctor_set(v___x_1264_, 4, v___x_1262_);
lean_ctor_set(v___x_1264_, 5, v___x_1262_);
lean_ctor_set(v___x_1264_, 6, v___x_1262_);
lean_ctor_set(v___x_1264_, 7, v___x_1262_);
lean_ctor_set(v___x_1264_, 8, v___x_1262_);
lean_ctor_set(v___x_1264_, 9, v___x_1262_);
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1265_ = lean_unsigned_to_nat(32u);
v___x_1266_ = lean_mk_empty_array_with_capacity(v___x_1265_);
v___x_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1266_);
return v___x_1267_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1268_ = ((size_t)5ULL);
v___x_1269_ = lean_unsigned_to_nat(0u);
v___x_1270_ = lean_unsigned_to_nat(32u);
v___x_1271_ = lean_mk_empty_array_with_capacity(v___x_1270_);
v___x_1272_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1273_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1273_, 0, v___x_1272_);
lean_ctor_set(v___x_1273_, 1, v___x_1271_);
lean_ctor_set(v___x_1273_, 2, v___x_1269_);
lean_ctor_set(v___x_1273_, 3, v___x_1269_);
lean_ctor_set_usize(v___x_1273_, 4, v___x_1268_);
return v___x_1273_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1274_ = lean_box(1);
v___x_1275_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1277_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1277_, 0, v___x_1276_);
lean_ctor_set(v___x_1277_, 1, v___x_1275_);
lean_ctor_set(v___x_1277_, 2, v___x_1274_);
return v___x_1277_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1280_ = l_Lean_stringToMessageData(v___x_1279_);
return v___x_1280_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1283_ = l_Lean_stringToMessageData(v___x_1282_);
return v___x_1283_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1286_ = l_Lean_stringToMessageData(v___x_1285_);
return v___x_1286_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1289_ = l_Lean_stringToMessageData(v___x_1288_);
return v___x_1289_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1292_ = l_Lean_stringToMessageData(v___x_1291_);
return v___x_1292_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1294_; lean_object* v___x_1295_; 
v___x_1294_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1295_ = l_Lean_stringToMessageData(v___x_1294_);
return v___x_1295_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1298_ = l_Lean_stringToMessageData(v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1299_, lean_object* v_declHint_1300_, lean_object* v___y_1301_){
_start:
{
lean_object* v___x_1303_; lean_object* v_env_1304_; uint8_t v___x_1305_; 
v___x_1303_ = lean_st_ref_get(v___y_1301_);
v_env_1304_ = lean_ctor_get(v___x_1303_, 0);
lean_inc_ref(v_env_1304_);
lean_dec(v___x_1303_);
v___x_1305_ = l_Lean_Name_isAnonymous(v_declHint_1300_);
if (v___x_1305_ == 0)
{
uint8_t v_isExporting_1306_; 
v_isExporting_1306_ = lean_ctor_get_uint8(v_env_1304_, sizeof(void*)*8);
if (v_isExporting_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec_ref(v_env_1304_);
lean_dec(v_declHint_1300_);
v___x_1307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1307_, 0, v_msg_1299_);
return v___x_1307_;
}
else
{
lean_object* v___x_1308_; uint8_t v___x_1309_; 
lean_inc_ref(v_env_1304_);
v___x_1308_ = l_Lean_Environment_setExporting(v_env_1304_, v___x_1305_);
lean_inc(v_declHint_1300_);
lean_inc_ref(v___x_1308_);
v___x_1309_ = l_Lean_Environment_contains(v___x_1308_, v_declHint_1300_, v_isExporting_1306_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; 
lean_dec_ref(v___x_1308_);
lean_dec_ref(v_env_1304_);
lean_dec(v_declHint_1300_);
v___x_1310_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1310_, 0, v_msg_1299_);
return v___x_1310_;
}
else
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v_c_1316_; lean_object* v___x_1317_; 
v___x_1311_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1313_ = l_Lean_Options_empty;
v___x_1314_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1314_, 0, v___x_1308_);
lean_ctor_set(v___x_1314_, 1, v___x_1311_);
lean_ctor_set(v___x_1314_, 2, v___x_1312_);
lean_ctor_set(v___x_1314_, 3, v___x_1313_);
lean_inc(v_declHint_1300_);
v___x_1315_ = l_Lean_MessageData_ofConstName(v_declHint_1300_, v___x_1305_);
v_c_1316_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1316_, 0, v___x_1314_);
lean_ctor_set(v_c_1316_, 1, v___x_1315_);
v___x_1317_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1304_, v_declHint_1300_);
if (lean_obj_tag(v___x_1317_) == 0)
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec_ref(v_env_1304_);
lean_dec(v_declHint_1300_);
v___x_1318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1318_);
lean_ctor_set(v___x_1319_, 1, v_c_1316_);
v___x_1320_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = l_Lean_MessageData_note(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_msg_1299_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
else
{
lean_object* v_val_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1360_; 
v_val_1325_ = lean_ctor_get(v___x_1317_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1317_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1327_ = v___x_1317_;
v_isShared_1328_ = v_isSharedCheck_1360_;
goto v_resetjp_1326_;
}
else
{
lean_inc(v_val_1325_);
lean_dec(v___x_1317_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1360_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v_mod_1332_; uint8_t v___x_1333_; 
v___x_1329_ = lean_box(0);
v___x_1330_ = l_Lean_Environment_header(v_env_1304_);
lean_dec_ref(v_env_1304_);
v___x_1331_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1330_);
v_mod_1332_ = lean_array_get(v___x_1329_, v___x_1331_, v_val_1325_);
lean_dec(v_val_1325_);
lean_dec_ref(v___x_1331_);
v___x_1333_ = l_Lean_isPrivateName(v_declHint_1300_);
lean_dec(v_declHint_1300_);
if (v___x_1333_ == 0)
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1345_; 
v___x_1334_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1335_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1335_, 0, v___x_1334_);
lean_ctor_set(v___x_1335_, 1, v_c_1316_);
v___x_1336_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1337_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1337_, 0, v___x_1335_);
lean_ctor_set(v___x_1337_, 1, v___x_1336_);
v___x_1338_ = l_Lean_MessageData_ofName(v_mod_1332_);
v___x_1339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1339_, 0, v___x_1337_);
lean_ctor_set(v___x_1339_, 1, v___x_1338_);
v___x_1340_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1339_);
lean_ctor_set(v___x_1341_, 1, v___x_1340_);
v___x_1342_ = l_Lean_MessageData_note(v___x_1341_);
v___x_1343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1343_, 0, v_msg_1299_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1343_);
v___x_1345_ = v___x_1327_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v___x_1343_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
else
{
lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1347_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1347_);
lean_ctor_set(v___x_1348_, 1, v_c_1316_);
v___x_1349_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1348_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = l_Lean_MessageData_ofName(v_mod_1332_);
v___x_1352_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1352_, 0, v___x_1350_);
lean_ctor_set(v___x_1352_, 1, v___x_1351_);
v___x_1353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1352_);
lean_ctor_set(v___x_1354_, 1, v___x_1353_);
v___x_1355_ = l_Lean_MessageData_note(v___x_1354_);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v_msg_1299_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
if (v_isShared_1328_ == 0)
{
lean_ctor_set_tag(v___x_1327_, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1356_);
v___x_1358_ = v___x_1327_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1359_; 
v_reuseFailAlloc_1359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1359_, 0, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1359_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
return v___x_1358_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1361_; 
lean_dec_ref(v_env_1304_);
lean_dec(v_declHint_1300_);
v___x_1361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1361_, 0, v_msg_1299_);
return v___x_1361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1362_, lean_object* v_declHint_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1362_, v_declHint_1363_, v___y_1364_);
lean_dec(v___y_1364_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1367_, lean_object* v_declHint_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
lean_object* v___x_1376_; lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1386_; 
v___x_1376_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1367_, v_declHint_1368_, v___y_1374_);
v_a_1377_ = lean_ctor_get(v___x_1376_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1376_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1379_ = v___x_1376_;
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1376_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1386_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1384_; 
v___x_1381_ = l_Lean_unknownIdentifierMessageTag;
v___x_1382_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1382_, 0, v___x_1381_);
lean_ctor_set(v___x_1382_, 1, v_a_1377_);
if (v_isShared_1380_ == 0)
{
lean_ctor_set(v___x_1379_, 0, v___x_1382_);
v___x_1384_ = v___x_1379_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1387_, lean_object* v_declHint_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1387_, v_declHint_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec(v___y_1389_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
lean_object* v___x_1403_; lean_object* v_env_1404_; lean_object* v___x_1405_; lean_object* v_mctx_1406_; lean_object* v_lctx_1407_; lean_object* v_options_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
v___x_1403_ = lean_st_ref_get(v___y_1401_);
v_env_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref(v_env_1404_);
lean_dec(v___x_1403_);
v___x_1405_ = lean_st_ref_get(v___y_1399_);
v_mctx_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc_ref(v_mctx_1406_);
lean_dec(v___x_1405_);
v_lctx_1407_ = lean_ctor_get(v___y_1398_, 2);
v_options_1408_ = lean_ctor_get(v___y_1400_, 2);
lean_inc_ref(v_options_1408_);
lean_inc_ref(v_lctx_1407_);
v___x_1409_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1409_, 0, v_env_1404_);
lean_ctor_set(v___x_1409_, 1, v_mctx_1406_);
lean_ctor_set(v___x_1409_, 2, v_lctx_1407_);
lean_ctor_set(v___x_1409_, 3, v_options_1408_);
v___x_1410_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1409_);
lean_ctor_set(v___x_1410_, 1, v_msgData_1397_);
v___x_1411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_){
_start:
{
lean_object* v_ref_1425_; lean_object* v___x_1426_; lean_object* v_a_1427_; lean_object* v___x_1429_; uint8_t v_isShared_1430_; uint8_t v_isSharedCheck_1435_; 
v_ref_1425_ = lean_ctor_get(v___y_1422_, 5);
v___x_1426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
v_isSharedCheck_1435_ = !lean_is_exclusive(v___x_1426_);
if (v_isSharedCheck_1435_ == 0)
{
v___x_1429_ = v___x_1426_;
v_isShared_1430_ = v_isSharedCheck_1435_;
goto v_resetjp_1428_;
}
else
{
lean_inc(v_a_1427_);
lean_dec(v___x_1426_);
v___x_1429_ = lean_box(0);
v_isShared_1430_ = v_isSharedCheck_1435_;
goto v_resetjp_1428_;
}
v_resetjp_1428_:
{
lean_object* v___x_1431_; lean_object* v___x_1433_; 
lean_inc(v_ref_1425_);
v___x_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1431_, 0, v_ref_1425_);
lean_ctor_set(v___x_1431_, 1, v_a_1427_);
if (v_isShared_1430_ == 0)
{
lean_ctor_set_tag(v___x_1429_, 1);
lean_ctor_set(v___x_1429_, 0, v___x_1431_);
v___x_1433_ = v___x_1429_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1434_; 
v_reuseFailAlloc_1434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1434_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1434_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
return v___x_1433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
lean_dec(v___y_1438_);
lean_dec_ref(v___y_1437_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1443_, lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_){
_start:
{
lean_object* v_fileName_1452_; lean_object* v_fileMap_1453_; lean_object* v_options_1454_; lean_object* v_currRecDepth_1455_; lean_object* v_maxRecDepth_1456_; lean_object* v_ref_1457_; lean_object* v_currNamespace_1458_; lean_object* v_openDecls_1459_; lean_object* v_initHeartbeats_1460_; lean_object* v_maxHeartbeats_1461_; lean_object* v_quotContext_1462_; lean_object* v_currMacroScope_1463_; uint8_t v_diag_1464_; lean_object* v_cancelTk_x3f_1465_; uint8_t v_suppressElabErrors_1466_; lean_object* v_inheritedTraceOptions_1467_; lean_object* v_ref_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v_fileName_1452_ = lean_ctor_get(v___y_1449_, 0);
v_fileMap_1453_ = lean_ctor_get(v___y_1449_, 1);
v_options_1454_ = lean_ctor_get(v___y_1449_, 2);
v_currRecDepth_1455_ = lean_ctor_get(v___y_1449_, 3);
v_maxRecDepth_1456_ = lean_ctor_get(v___y_1449_, 4);
v_ref_1457_ = lean_ctor_get(v___y_1449_, 5);
v_currNamespace_1458_ = lean_ctor_get(v___y_1449_, 6);
v_openDecls_1459_ = lean_ctor_get(v___y_1449_, 7);
v_initHeartbeats_1460_ = lean_ctor_get(v___y_1449_, 8);
v_maxHeartbeats_1461_ = lean_ctor_get(v___y_1449_, 9);
v_quotContext_1462_ = lean_ctor_get(v___y_1449_, 10);
v_currMacroScope_1463_ = lean_ctor_get(v___y_1449_, 11);
v_diag_1464_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*14);
v_cancelTk_x3f_1465_ = lean_ctor_get(v___y_1449_, 12);
v_suppressElabErrors_1466_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1467_ = lean_ctor_get(v___y_1449_, 13);
v_ref_1468_ = l_Lean_replaceRef(v_ref_1443_, v_ref_1457_);
lean_inc_ref(v_inheritedTraceOptions_1467_);
lean_inc(v_cancelTk_x3f_1465_);
lean_inc(v_currMacroScope_1463_);
lean_inc(v_quotContext_1462_);
lean_inc(v_maxHeartbeats_1461_);
lean_inc(v_initHeartbeats_1460_);
lean_inc(v_openDecls_1459_);
lean_inc(v_currNamespace_1458_);
lean_inc(v_maxRecDepth_1456_);
lean_inc(v_currRecDepth_1455_);
lean_inc_ref(v_options_1454_);
lean_inc_ref(v_fileMap_1453_);
lean_inc_ref(v_fileName_1452_);
v___x_1469_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1469_, 0, v_fileName_1452_);
lean_ctor_set(v___x_1469_, 1, v_fileMap_1453_);
lean_ctor_set(v___x_1469_, 2, v_options_1454_);
lean_ctor_set(v___x_1469_, 3, v_currRecDepth_1455_);
lean_ctor_set(v___x_1469_, 4, v_maxRecDepth_1456_);
lean_ctor_set(v___x_1469_, 5, v_ref_1468_);
lean_ctor_set(v___x_1469_, 6, v_currNamespace_1458_);
lean_ctor_set(v___x_1469_, 7, v_openDecls_1459_);
lean_ctor_set(v___x_1469_, 8, v_initHeartbeats_1460_);
lean_ctor_set(v___x_1469_, 9, v_maxHeartbeats_1461_);
lean_ctor_set(v___x_1469_, 10, v_quotContext_1462_);
lean_ctor_set(v___x_1469_, 11, v_currMacroScope_1463_);
lean_ctor_set(v___x_1469_, 12, v_cancelTk_x3f_1465_);
lean_ctor_set(v___x_1469_, 13, v_inheritedTraceOptions_1467_);
lean_ctor_set_uint8(v___x_1469_, sizeof(void*)*14, v_diag_1464_);
lean_ctor_set_uint8(v___x_1469_, sizeof(void*)*14 + 1, v_suppressElabErrors_1466_);
v___x_1470_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1444_, v___y_1447_, v___y_1448_, v___x_1469_, v___y_1450_);
lean_dec_ref_known(v___x_1469_, 14);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1471_, lean_object* v_msg_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v_res_1480_; 
v_res_1480_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1471_, v_msg_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
lean_dec_ref(v___y_1475_);
lean_dec(v___y_1474_);
lean_dec(v___y_1473_);
lean_dec(v_ref_1471_);
return v_res_1480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1481_, lean_object* v_msg_1482_, lean_object* v_declHint_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v_a_1492_; lean_object* v___x_1493_; 
v___x_1491_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1482_, v_declHint_1483_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
v_a_1492_ = lean_ctor_get(v___x_1491_, 0);
lean_inc(v_a_1492_);
lean_dec_ref(v___x_1491_);
v___x_1493_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1481_, v_a_1492_, v___y_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1494_, lean_object* v_msg_1495_, lean_object* v_declHint_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_res_1504_; 
v_res_1504_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1494_, v_msg_1495_, v_declHint_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec(v_ref_1494_);
return v_res_1504_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1509_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
return v___x_1510_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1511_, lean_object* v_constName_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_, lean_object* v___y_1518_){
_start:
{
lean_object* v___x_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1520_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1521_ = 0;
lean_inc(v_constName_1512_);
v___x_1522_ = l_Lean_MessageData_ofConstName(v_constName_1512_, v___x_1521_);
v___x_1523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1520_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
v___x_1524_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1523_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
v___x_1526_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1511_, v___x_1525_, v_constName_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1527_, lean_object* v_constName_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1527_, v_constName_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
lean_dec(v___y_1534_);
lean_dec_ref(v___y_1533_);
lean_dec(v___y_1532_);
lean_dec_ref(v___y_1531_);
lean_dec(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v_ref_1527_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_ref_1545_; lean_object* v___x_1546_; 
v_ref_1545_ = lean_ctor_get(v___y_1542_, 5);
v___x_1546_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1545_, v_constName_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_);
return v___x_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v_res_1555_; 
v_res_1555_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
lean_dec(v___y_1553_);
lean_dec_ref(v___y_1552_);
lean_dec(v___y_1551_);
lean_dec_ref(v___y_1550_);
lean_dec(v___y_1549_);
lean_dec(v___y_1548_);
return v_res_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v___x_1564_; lean_object* v_env_1565_; uint8_t v___x_1566_; lean_object* v___x_1567_; 
v___x_1564_ = lean_st_ref_get(v___y_1562_);
v_env_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc_ref(v_env_1565_);
lean_dec(v___x_1564_);
v___x_1566_ = 0;
lean_inc(v_constName_1556_);
v___x_1567_ = l_Lean_Environment_findConstVal_x3f(v_env_1565_, v_constName_1556_, v___x_1566_);
if (lean_obj_tag(v___x_1567_) == 0)
{
lean_object* v___x_1568_; 
v___x_1568_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_);
return v___x_1568_;
}
else
{
lean_object* v_val_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_dec(v_constName_1556_);
v_val_1569_ = lean_ctor_get(v___x_1567_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1567_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1567_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_val_1569_);
lean_dec(v___x_1567_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
lean_ctor_set_tag(v___x_1571_, 0);
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_val_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec(v___y_1578_);
return v_res_1585_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1589_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1590_ = lean_unsigned_to_nat(35u);
v___x_1591_ = lean_unsigned_to_nat(203u);
v___x_1592_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1593_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1594_ = l_mkPanicMessageWithDecl(v___x_1593_, v___x_1592_, v___x_1591_, v___x_1590_, v___x_1589_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
if (lean_obj_tag(v_e_1595_) == 4)
{
lean_object* v_declName_1603_; lean_object* v_us_1604_; lean_object* v___x_1605_; 
v_declName_1603_ = lean_ctor_get(v_e_1595_, 0);
v_us_1604_ = lean_ctor_get(v_e_1595_, 1);
lean_inc(v_declName_1603_);
v___x_1605_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1603_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
if (lean_obj_tag(v___x_1605_) == 0)
{
lean_object* v_a_1606_; lean_object* v_levelParams_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; uint8_t v___x_1610_; 
v_a_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_a_1606_);
lean_dec_ref_known(v___x_1605_, 1);
v_levelParams_1607_ = lean_ctor_get(v_a_1606_, 1);
v___x_1608_ = l_List_lengthTR___redArg(v_levelParams_1607_);
v___x_1609_ = l_List_lengthTR___redArg(v_us_1604_);
v___x_1610_ = lean_nat_dec_eq(v___x_1608_, v___x_1609_);
lean_dec(v___x_1609_);
lean_dec(v___x_1608_);
if (v___x_1610_ == 0)
{
lean_object* v___x_1611_; 
lean_inc(v_us_1604_);
lean_inc(v_declName_1603_);
lean_dec(v_a_1606_);
lean_dec_ref_known(v_e_1595_, 2);
v___x_1611_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1603_, v_us_1604_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
return v___x_1611_;
}
else
{
lean_object* v___x_1612_; 
lean_inc(v_us_1604_);
v___x_1612_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1606_, v_us_1604_, v___y_1601_);
if (lean_obj_tag(v___x_1612_) == 0)
{
lean_object* v_a_1613_; lean_object* v___x_1615_; uint8_t v_isShared_1616_; uint8_t v_isSharedCheck_1622_; 
v_a_1613_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1615_ = v___x_1612_;
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
else
{
lean_inc(v_a_1613_);
lean_dec(v___x_1612_);
v___x_1615_ = lean_box(0);
v_isShared_1616_ = v_isSharedCheck_1622_;
goto v_resetjp_1614_;
}
v_resetjp_1614_:
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1620_; 
v___x_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1617_, 0, v_a_1613_);
v___x_1618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1618_, 0, v_e_1595_);
lean_ctor_set(v___x_1618_, 1, v___x_1617_);
if (v_isShared_1616_ == 0)
{
lean_ctor_set(v___x_1615_, 0, v___x_1618_);
v___x_1620_ = v___x_1615_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v___x_1618_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref_known(v_e_1595_, 2);
v_a_1623_ = lean_ctor_get(v___x_1612_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1612_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1612_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1612_);
v___x_1625_ = lean_box(0);
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
v_resetjp_1624_:
{
lean_object* v___x_1628_; 
if (v_isShared_1626_ == 0)
{
v___x_1628_ = v___x_1625_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref_known(v_e_1595_, 2);
v_a_1631_ = lean_ctor_get(v___x_1605_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1605_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1605_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1605_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v___x_1636_; 
if (v_isShared_1634_ == 0)
{
v___x_1636_ = v___x_1633_;
goto v_reusejp_1635_;
}
else
{
lean_object* v_reuseFailAlloc_1637_; 
v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1631_);
v___x_1636_ = v_reuseFailAlloc_1637_;
goto v_reusejp_1635_;
}
v_reusejp_1635_:
{
return v___x_1636_;
}
}
}
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; 
lean_dec_ref(v_e_1595_);
v___x_1639_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1640_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1639_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
return v___x_1640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_);
lean_dec(v___y_1647_);
lean_dec_ref(v___y_1646_);
lean_dec(v___y_1645_);
lean_dec_ref(v___y_1644_);
lean_dec(v___y_1643_);
lean_dec(v___y_1642_);
return v_res_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_){
_start:
{
lean_object* v___y_1658_; lean_object* v___x_1659_; 
lean_inc_ref(v_e_1650_);
v___y_1658_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1658_, 0, v_e_1650_);
v___x_1659_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1650_, v___y_1658_, v_a_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_, lean_object* v_a_1665_, lean_object* v_a_1666_, lean_object* v_a_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_, v_a_1665_, v_a_1666_);
lean_dec(v_a_1666_);
lean_dec_ref(v_a_1665_);
lean_dec(v_a_1664_);
lean_dec_ref(v_a_1663_);
lean_dec(v_a_1662_);
lean_dec(v_a_1661_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1669_, lean_object* v_constName_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1679_, lean_object* v_constName_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
lean_object* v_res_1688_; 
v_res_1688_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1679_, v_constName_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
return v_res_1688_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1689_, lean_object* v_ref_1690_, lean_object* v_constName_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1690_, v_constName_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_ref_1701_, lean_object* v_constName_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1700_, v_ref_1701_, v_constName_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
lean_dec(v___y_1708_);
lean_dec_ref(v___y_1707_);
lean_dec(v___y_1706_);
lean_dec_ref(v___y_1705_);
lean_dec(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec(v_ref_1701_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1711_, lean_object* v_ref_1712_, lean_object* v_msg_1713_, lean_object* v_declHint_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1712_, v_msg_1713_, v_declHint_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_, v___y_1720_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1723_, lean_object* v_ref_1724_, lean_object* v_msg_1725_, lean_object* v_declHint_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1723_, v_ref_1724_, v_msg_1725_, v_declHint_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec(v_ref_1724_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1735_, lean_object* v_declHint_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1735_, v_declHint_1736_, v___y_1742_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1745_, lean_object* v_declHint_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1745_, v_declHint_1746_, v___y_1747_, v___y_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec_ref(v___y_1749_);
lean_dec(v___y_1748_);
lean_dec(v___y_1747_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1755_, lean_object* v_ref_1756_, lean_object* v_msg_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
lean_object* v___x_1765_; 
v___x_1765_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1756_, v_msg_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_);
return v___x_1765_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1766_, lean_object* v_ref_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1766_, v_ref_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec(v___y_1769_);
lean_dec(v_ref_1767_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1777_, lean_object* v_msg_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_){
_start:
{
lean_object* v___x_1786_; 
v___x_1786_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1778_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_);
return v___x_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1787_, lean_object* v_msg_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1787_, v_msg_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_, v___y_1794_);
lean_dec(v___y_1794_);
lean_dec_ref(v___y_1793_);
lean_dec(v___y_1792_);
lean_dec_ref(v___y_1791_);
lean_dec(v___y_1790_);
lean_dec(v___y_1789_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
uint8_t v___x_1805_; 
v___x_1805_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1798_);
if (v___x_1805_ == 0)
{
lean_object* v___x_1806_; 
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v_r_1797_);
return v___x_1806_;
}
else
{
lean_object* v___x_1807_; 
lean_inc_ref(v_r_1797_);
v___x_1807_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1797_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
if (lean_obj_tag(v___x_1807_) == 0)
{
lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1860_; 
v_a_1808_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1810_ = v___x_1807_;
v_isShared_1811_ = v_isSharedCheck_1860_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_dec(v___x_1807_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1860_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v_expr_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1858_; 
v_expr_1812_ = lean_ctor_get(v_r_1797_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v_r_1797_);
if (v_isSharedCheck_1858_ == 0)
{
lean_object* v_unused_1859_; 
v_unused_1859_ = lean_ctor_get(v_r_1797_, 1);
lean_dec(v_unused_1859_);
v___x_1814_ = v_r_1797_;
v_isShared_1815_ = v_isSharedCheck_1858_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_expr_1812_);
lean_dec(v_r_1797_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1858_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
uint8_t v___x_1816_; 
v___x_1816_ = l_Lean_Expr_isSort(v_a_1808_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
lean_del_object(v___x_1810_);
lean_inc(v_a_1803_);
lean_inc_ref(v_a_1802_);
lean_inc(v_a_1801_);
lean_inc_ref(v_a_1800_);
v___x_1817_ = lean_whnf(v_a_1808_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
if (lean_obj_tag(v___x_1817_) == 0)
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1842_; 
v_a_1818_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1820_ = v___x_1817_;
v_isShared_1821_ = v_isSharedCheck_1842_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1817_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_1842_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
if (lean_obj_tag(v_a_1818_) == 3)
{
lean_object* v___x_1822_; lean_object* v_count_1823_; lean_object* v_results_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1840_; 
v___x_1822_ = lean_st_ref_take(v_a_1799_);
v_count_1823_ = lean_ctor_get(v___x_1822_, 0);
v_results_1824_ = lean_ctor_get(v___x_1822_, 1);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1822_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1826_ = v___x_1822_;
v_isShared_1827_ = v_isSharedCheck_1840_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_results_1824_);
lean_inc(v_count_1823_);
lean_dec(v___x_1822_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1840_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1828_; lean_object* v___x_1830_; 
v___x_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1828_, 0, v_a_1818_);
lean_inc_ref(v_expr_1812_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1828_);
v___x_1830_ = v___x_1814_;
goto v_reusejp_1829_;
}
else
{
lean_object* v_reuseFailAlloc_1839_; 
v_reuseFailAlloc_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1839_, 0, v_expr_1812_);
lean_ctor_set(v_reuseFailAlloc_1839_, 1, v___x_1828_);
v___x_1830_ = v_reuseFailAlloc_1839_;
goto v_reusejp_1829_;
}
v_reusejp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
lean_inc_ref(v___x_1830_);
v___x_1831_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1824_, v_expr_1812_, v___x_1830_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 1, v___x_1831_);
v___x_1833_ = v___x_1826_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_count_1823_);
lean_ctor_set(v_reuseFailAlloc_1838_, 1, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
v___x_1834_ = lean_st_ref_set(v_a_1799_, v___x_1833_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1830_);
v___x_1836_ = v___x_1820_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1830_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
}
else
{
lean_object* v___x_1841_; 
lean_del_object(v___x_1820_);
lean_dec(v_a_1818_);
lean_del_object(v___x_1814_);
v___x_1841_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1812_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
return v___x_1841_;
}
}
}
else
{
lean_object* v_a_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1850_; 
lean_del_object(v___x_1814_);
lean_dec_ref(v_expr_1812_);
v_a_1843_ = lean_ctor_get(v___x_1817_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1845_ = v___x_1817_;
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_a_1843_);
lean_dec(v___x_1817_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1850_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1848_; 
if (v_isShared_1846_ == 0)
{
v___x_1848_ = v___x_1845_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_a_1843_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
}
else
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_a_1808_);
if (v_isShared_1815_ == 0)
{
lean_ctor_set(v___x_1814_, 1, v___x_1851_);
v___x_1853_ = v___x_1814_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_expr_1812_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1855_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1853_);
v___x_1855_ = v___x_1810_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
return v___x_1855_;
}
}
}
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_dec_ref(v_r_1797_);
v_a_1861_ = lean_ctor_get(v___x_1807_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1807_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1807_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1807_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1869_, v_a_1870_, v_a_1871_, v_a_1872_, v_a_1873_, v_a_1874_, v_a_1875_);
lean_dec(v_a_1875_);
lean_dec_ref(v_a_1874_);
lean_dec(v_a_1873_);
lean_dec_ref(v_a_1872_);
lean_dec(v_a_1871_);
lean_dec(v_a_1870_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1878_){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = l_Lean_instInhabitedExpr;
v___x_1880_ = lean_panic_fn_borrowed(v___x_1879_, v_msg_1878_);
return v___x_1880_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v___x_1884_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1885_ = lean_unsigned_to_nat(18u);
v___x_1886_ = lean_unsigned_to_nat(1838u);
v___x_1887_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1888_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1889_ = l_mkPanicMessageWithDecl(v___x_1888_, v___x_1887_, v___x_1886_, v___x_1885_, v___x_1884_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1890_, lean_object* v_f_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_, lean_object* v_a_1895_, lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_){
_start:
{
lean_object* v___y_1901_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; uint8_t v___y_1917_; lean_object* v___y_1920_; lean_object* v_fType_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1938_; lean_object* v___y_1939_; lean_object* v___y_1940_; uint8_t v___x_1979_; 
v___x_1979_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1893_);
if (v___x_1979_ == 0)
{
lean_object* v_expr_1980_; lean_object* v_expr_1981_; uint8_t v___y_1983_; 
v_expr_1980_ = lean_ctor_get(v_f_1891_, 0);
lean_inc_ref(v_expr_1980_);
lean_dec_ref(v_f_1891_);
v_expr_1981_ = lean_ctor_get(v_a_1892_, 0);
lean_inc_ref(v_expr_1981_);
lean_dec_ref(v_a_1892_);
if (lean_obj_tag(v_e_1890_) == 5)
{
lean_object* v_fn_1985_; lean_object* v_arg_1986_; size_t v___x_1987_; size_t v___x_1988_; uint8_t v___x_1989_; 
v_fn_1985_ = lean_ctor_get(v_e_1890_, 0);
v_arg_1986_ = lean_ctor_get(v_e_1890_, 1);
v___x_1987_ = lean_ptr_addr(v_fn_1985_);
v___x_1988_ = lean_ptr_addr(v_expr_1980_);
v___x_1989_ = lean_usize_dec_eq(v___x_1987_, v___x_1988_);
if (v___x_1989_ == 0)
{
v___y_1983_ = v___x_1989_;
goto v___jp_1982_;
}
else
{
size_t v___x_1990_; size_t v___x_1991_; uint8_t v___x_1992_; 
v___x_1990_ = lean_ptr_addr(v_arg_1986_);
v___x_1991_ = lean_ptr_addr(v_expr_1981_);
v___x_1992_ = lean_usize_dec_eq(v___x_1990_, v___x_1991_);
v___y_1983_ = v___x_1992_;
goto v___jp_1982_;
}
}
else
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
lean_dec_ref(v_expr_1981_);
lean_dec_ref(v_expr_1980_);
lean_dec_ref(v_e_1890_);
v___x_1993_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1994_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1993_);
v___y_1901_ = v___x_1994_;
goto v___jp_1900_;
}
v___jp_1982_:
{
if (v___y_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_dec_ref(v_e_1890_);
v___x_1984_ = l_Lean_Expr_app___override(v_expr_1980_, v_expr_1981_);
v___y_1901_ = v___x_1984_;
goto v___jp_1900_;
}
else
{
lean_dec_ref(v_expr_1981_);
lean_dec_ref(v_expr_1980_);
v___y_1901_ = v_e_1890_;
goto v___jp_1900_;
}
}
}
else
{
lean_object* v___x_1995_; 
lean_inc_ref(v_f_1891_);
v___x_1995_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1891_, v_a_1894_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1995_) == 0)
{
lean_object* v_a_1996_; uint8_t v___x_1997_; 
v_a_1996_ = lean_ctor_get(v___x_1995_, 0);
lean_inc(v_a_1996_);
lean_dec_ref_known(v___x_1995_, 1);
v___x_1997_ = l_Lean_Expr_isForall(v_a_1996_);
if (v___x_1997_ == 0)
{
lean_object* v___x_1998_; 
lean_inc(v_a_1898_);
lean_inc_ref(v_a_1897_);
lean_inc(v_a_1896_);
lean_inc_ref(v_a_1895_);
v___x_1998_ = lean_whnf(v_a_1996_, v_a_1895_, v_a_1896_, v_a_1897_, v_a_1898_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v_fType_1935_ = v_a_1999_;
v___y_1936_ = v_a_1894_;
v___y_1937_ = v_a_1895_;
v___y_1938_ = v_a_1896_;
v___y_1939_ = v_a_1897_;
v___y_1940_ = v_a_1898_;
goto v___jp_1934_;
}
else
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2007_; 
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_f_1891_);
lean_dec_ref(v_e_1890_);
v_a_2000_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2007_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2007_ == 0)
{
v___x_2002_ = v___x_1998_;
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___x_1998_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2007_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
lean_object* v___x_2005_; 
if (v_isShared_2003_ == 0)
{
v___x_2005_ = v___x_2002_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2000_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
}
}
else
{
v_fType_1935_ = v_a_1996_;
v___y_1936_ = v_a_1894_;
v___y_1937_ = v_a_1895_;
v___y_1938_ = v_a_1896_;
v___y_1939_ = v_a_1897_;
v___y_1940_ = v_a_1898_;
goto v___jp_1934_;
}
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_f_1891_);
lean_dec_ref(v_e_1890_);
v_a_2008_ = lean_ctor_get(v___x_1995_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_1995_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_1995_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_1995_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
lean_object* v___x_2013_; 
if (v_isShared_2011_ == 0)
{
v___x_2013_ = v___x_2010_;
goto v_reusejp_2012_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_a_2008_);
v___x_2013_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2012_;
}
v_reusejp_2012_:
{
return v___x_2013_;
}
}
}
}
v___jp_1900_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_box(0);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1901_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
v___jp_1905_:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1909_ = lean_expr_instantiate1(v___y_1907_, v___y_1906_);
lean_dec_ref(v___y_1906_);
lean_dec_ref(v___y_1907_);
v___x_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1909_);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___y_1908_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
v___jp_1913_:
{
if (v___y_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref(v_e_1890_);
lean_inc_ref(v___y_1914_);
v___x_1918_ = l_Lean_Expr_app___override(v___y_1915_, v___y_1914_);
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___y_1916_;
v___y_1908_ = v___x_1918_;
goto v___jp_1905_;
}
else
{
lean_dec_ref(v___y_1915_);
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___y_1916_;
v___y_1908_ = v_e_1890_;
goto v___jp_1905_;
}
}
v___jp_1919_:
{
if (lean_obj_tag(v_e_1890_) == 5)
{
lean_object* v_expr_1921_; lean_object* v_expr_1922_; lean_object* v_fn_1923_; lean_object* v_arg_1924_; size_t v___x_1925_; size_t v___x_1926_; uint8_t v___x_1927_; 
v_expr_1921_ = lean_ctor_get(v_f_1891_, 0);
lean_inc_ref(v_expr_1921_);
lean_dec_ref(v_f_1891_);
v_expr_1922_ = lean_ctor_get(v_a_1892_, 0);
lean_inc_ref(v_expr_1922_);
lean_dec_ref(v_a_1892_);
v_fn_1923_ = lean_ctor_get(v_e_1890_, 0);
v_arg_1924_ = lean_ctor_get(v_e_1890_, 1);
v___x_1925_ = lean_ptr_addr(v_fn_1923_);
v___x_1926_ = lean_ptr_addr(v_expr_1921_);
v___x_1927_ = lean_usize_dec_eq(v___x_1925_, v___x_1926_);
if (v___x_1927_ == 0)
{
v___y_1914_ = v_expr_1922_;
v___y_1915_ = v_expr_1921_;
v___y_1916_ = v___y_1920_;
v___y_1917_ = v___x_1927_;
goto v___jp_1913_;
}
else
{
size_t v___x_1928_; size_t v___x_1929_; uint8_t v___x_1930_; 
v___x_1928_ = lean_ptr_addr(v_arg_1924_);
v___x_1929_ = lean_ptr_addr(v_expr_1922_);
v___x_1930_ = lean_usize_dec_eq(v___x_1928_, v___x_1929_);
v___y_1914_ = v_expr_1922_;
v___y_1915_ = v_expr_1921_;
v___y_1916_ = v___y_1920_;
v___y_1917_ = v___x_1930_;
goto v___jp_1913_;
}
}
else
{
lean_object* v_expr_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
lean_dec_ref(v_f_1891_);
lean_dec_ref(v_e_1890_);
v_expr_1931_ = lean_ctor_get(v_a_1892_, 0);
lean_inc_ref(v_expr_1931_);
lean_dec_ref(v_a_1892_);
v___x_1932_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1933_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1932_);
v___y_1906_ = v_expr_1931_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___x_1933_;
goto v___jp_1905_;
}
}
v___jp_1934_:
{
if (lean_obj_tag(v_fType_1935_) == 7)
{
lean_object* v_binderType_1941_; lean_object* v_body_1942_; lean_object* v___x_1943_; 
v_binderType_1941_ = lean_ctor_get(v_fType_1935_, 1);
lean_inc_ref(v_binderType_1941_);
v_body_1942_ = lean_ctor_get(v_fType_1935_, 2);
lean_inc_ref(v_body_1942_);
lean_dec_ref_known(v_fType_1935_, 3);
lean_inc_ref(v_a_1892_);
v___x_1943_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1892_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_object* v_a_1944_; lean_object* v___x_1945_; 
v_a_1944_ = lean_ctor_get(v___x_1943_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1943_, 1);
v___x_1945_ = l_Lean_Meta_isExprDefEq(v_binderType_1941_, v_a_1944_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1945_) == 0)
{
lean_object* v_a_1946_; uint8_t v___x_1947_; 
v_a_1946_ = lean_ctor_get(v___x_1945_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1945_, 1);
v___x_1947_ = lean_unbox(v_a_1946_);
lean_dec(v_a_1946_);
if (v___x_1947_ == 0)
{
lean_object* v_expr_1948_; lean_object* v_expr_1949_; lean_object* v___x_1950_; 
v_expr_1948_ = lean_ctor_get(v_f_1891_, 0);
v_expr_1949_ = lean_ctor_get(v_a_1892_, 0);
lean_inc_ref(v_expr_1949_);
lean_inc_ref(v_expr_1948_);
v___x_1950_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1948_, v_expr_1949_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
if (lean_obj_tag(v___x_1950_) == 0)
{
lean_dec_ref_known(v___x_1950_, 1);
v___y_1920_ = v_body_1942_;
goto v___jp_1919_;
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_body_1942_);
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_f_1891_);
lean_dec_ref(v_e_1890_);
v_a_1951_ = lean_ctor_get(v___x_1950_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1950_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1950_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1950_);
v___x_1953_ = lean_box(0);
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
v_resetjp_1952_:
{
lean_object* v___x_1956_; 
if (v_isShared_1954_ == 0)
{
v___x_1956_ = v___x_1953_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_a_1951_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
}
}
else
{
v___y_1920_ = v_body_1942_;
goto v___jp_1919_;
}
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v_body_1942_);
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_f_1891_);
lean_dec_ref(v_e_1890_);
v_a_1959_ = lean_ctor_get(v___x_1945_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1945_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1945_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1945_);
v___x_1961_ = lean_box(0);
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
v_resetjp_1960_:
{
lean_object* v___x_1964_; 
if (v_isShared_1962_ == 0)
{
v___x_1964_ = v___x_1961_;
goto v_reusejp_1963_;
}
else
{
lean_object* v_reuseFailAlloc_1965_; 
v_reuseFailAlloc_1965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1965_, 0, v_a_1959_);
v___x_1964_ = v_reuseFailAlloc_1965_;
goto v_reusejp_1963_;
}
v_reusejp_1963_:
{
return v___x_1964_;
}
}
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_body_1942_);
lean_dec_ref(v_binderType_1941_);
lean_dec_ref(v_a_1892_);
lean_dec_ref(v_f_1891_);
lean_dec_ref(v_e_1890_);
v_a_1967_ = lean_ctor_get(v___x_1943_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1943_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1943_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v___x_1972_; 
if (v_isShared_1970_ == 0)
{
v___x_1972_ = v___x_1969_;
goto v_reusejp_1971_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v_a_1967_);
v___x_1972_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1971_;
}
v_reusejp_1971_:
{
return v___x_1972_;
}
}
}
}
else
{
lean_object* v_expr_1975_; lean_object* v_expr_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
lean_dec_ref(v_fType_1935_);
lean_dec_ref(v_e_1890_);
v_expr_1975_ = lean_ctor_get(v_f_1891_, 0);
lean_inc_ref(v_expr_1975_);
lean_dec_ref(v_f_1891_);
v_expr_1976_ = lean_ctor_get(v_a_1892_, 0);
lean_inc_ref(v_expr_1976_);
lean_dec_ref(v_a_1892_);
v___x_1977_ = l_Lean_Expr_app___override(v_expr_1975_, v_expr_1976_);
v___x_1978_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1977_, v___y_1937_, v___y_1938_, v___y_1939_, v___y_1940_);
return v___x_1978_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2016_, lean_object* v_f_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2016_, v_f_2017_, v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_, v_a_2023_, v_a_2024_);
lean_dec(v_a_2024_);
lean_dec_ref(v_a_2023_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
lean_dec(v_a_2019_);
return v_res_2026_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2028_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2029_ = lean_unsigned_to_nat(37u);
v___x_2030_ = lean_unsigned_to_nat(345u);
v___x_2031_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2032_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2033_ = l_mkPanicMessageWithDecl(v___x_2032_, v___x_2031_, v___x_2030_, v___x_2029_, v___x_2028_);
return v___x_2033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2034_, lean_object* v_i_2035_, lean_object* v_a_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_){
_start:
{
lean_object* v_zero_2044_; uint8_t v_isZero_2045_; 
v_zero_2044_ = lean_unsigned_to_nat(0u);
v_isZero_2045_ = lean_nat_dec_eq(v_i_2035_, v_zero_2044_);
if (v_isZero_2045_ == 1)
{
lean_object* v___x_2046_; 
lean_dec(v_i_2035_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_a_2036_);
return v___x_2046_;
}
else
{
lean_object* v_one_2047_; lean_object* v_n_2048_; lean_object* v___y_2050_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2059_; lean_object* v___y_2060_; lean_object* v___x_2062_; 
v_one_2047_ = lean_unsigned_to_nat(1u);
v_n_2048_ = lean_nat_sub(v_i_2035_, v_one_2047_);
lean_dec(v_i_2035_);
v___x_2062_ = lean_array_fget_borrowed(v_fvars_2034_, v_n_2048_);
if (lean_obj_tag(v___x_2062_) == 1)
{
lean_object* v_fvarId_2063_; lean_object* v___x_2064_; 
v_fvarId_2063_ = lean_ctor_get(v___x_2062_, 0);
lean_inc(v_fvarId_2063_);
v___x_2064_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2063_, v___y_2039_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
if (lean_obj_tag(v_a_2065_) == 1)
{
lean_object* v_val_2066_; 
v_val_2066_ = lean_ctor_get(v_a_2065_, 0);
lean_inc(v_val_2066_);
lean_dec_ref_known(v_a_2065_, 1);
if (lean_obj_tag(v_val_2066_) == 0)
{
lean_object* v_userName_2067_; lean_object* v_type_2068_; uint8_t v_bi_2069_; lean_object* v_expr_2070_; lean_object* v_type_x3f_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2092_; 
v_userName_2067_ = lean_ctor_get(v_val_2066_, 2);
lean_inc(v_userName_2067_);
v_type_2068_ = lean_ctor_get(v_val_2066_, 3);
lean_inc_ref(v_type_2068_);
v_bi_2069_ = lean_ctor_get_uint8(v_val_2066_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2066_, 4);
v_expr_2070_ = lean_ctor_get(v_a_2036_, 0);
v_type_x3f_2071_ = lean_ctor_get(v_a_2036_, 1);
v_isSharedCheck_2092_ = !lean_is_exclusive(v_a_2036_);
if (v_isSharedCheck_2092_ == 0)
{
v___x_2073_ = v_a_2036_;
v_isShared_2074_ = v_isSharedCheck_2092_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_type_x3f_2071_);
lean_inc(v_expr_2070_);
lean_dec(v_a_2036_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2092_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___y_2078_; 
v___x_2075_ = lean_expr_abstract_range(v_type_2068_, v_n_2048_, v_fvars_2034_);
lean_dec_ref(v_type_2068_);
lean_inc_ref(v___x_2075_);
lean_inc(v_userName_2067_);
v___x_2076_ = l_Lean_Expr_lam___override(v_userName_2067_, v___x_2075_, v_expr_2070_, v_bi_2069_);
if (lean_obj_tag(v_type_x3f_2071_) == 0)
{
lean_dec_ref(v___x_2075_);
lean_dec(v_userName_2067_);
v___y_2078_ = v_type_x3f_2071_;
goto v___jp_2077_;
}
else
{
lean_object* v_val_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2091_; 
v_val_2083_ = lean_ctor_get(v_type_x3f_2071_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_type_x3f_2071_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2085_ = v_type_x3f_2071_;
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_val_2083_);
lean_dec(v_type_x3f_2071_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2091_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2087_ = l_Lean_Expr_forallE___override(v_userName_2067_, v___x_2075_, v_val_2083_, v_bi_2069_);
if (v_isShared_2086_ == 0)
{
lean_ctor_set(v___x_2085_, 0, v___x_2087_);
v___x_2089_ = v___x_2085_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
v___y_2078_ = v___x_2089_;
goto v___jp_2077_;
}
}
}
v___jp_2077_:
{
lean_object* v___x_2080_; 
if (v_isShared_2074_ == 0)
{
lean_ctor_set(v___x_2073_, 1, v___y_2078_);
lean_ctor_set(v___x_2073_, 0, v___x_2076_);
v___x_2080_ = v___x_2073_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2076_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v___y_2078_);
v___x_2080_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
v_i_2035_ = v_n_2048_;
v_a_2036_ = v___x_2080_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2093_; lean_object* v_type_2094_; lean_object* v_value_2095_; uint8_t v_nondep_2096_; uint8_t v_nondep_2098_; lean_object* v___x_2108_; 
v_userName_2093_ = lean_ctor_get(v_val_2066_, 2);
lean_inc(v_userName_2093_);
v_type_2094_ = lean_ctor_get(v_val_2066_, 3);
lean_inc_ref(v_type_2094_);
v_value_2095_ = lean_ctor_get(v_val_2066_, 4);
lean_inc_ref(v_value_2095_);
v_nondep_2096_ = lean_ctor_get_uint8(v_val_2066_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2066_, 5);
v___x_2108_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2040_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; uint8_t v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = 1;
if (v_nondep_2096_ == 0)
{
uint8_t v___x_2111_; 
v___x_2111_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2063_, v_a_2109_);
lean_dec(v_a_2109_);
if (v___x_2111_ == 0)
{
lean_object* v___x_2112_; 
v___x_2112_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2038_);
lean_dec_ref(v___x_2112_);
v_nondep_2098_ = v___x_2110_;
goto v___jp_2097_;
}
else
{
v_nondep_2098_ = v_nondep_2096_;
goto v___jp_2097_;
}
}
else
{
lean_dec(v_a_2109_);
v_nondep_2098_ = v___x_2110_;
goto v___jp_2097_;
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec_ref(v_value_2095_);
lean_dec_ref(v_type_2094_);
lean_dec(v_userName_2093_);
lean_dec(v_n_2048_);
lean_dec_ref(v_a_2036_);
v_a_2113_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2108_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2108_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v___x_2118_; 
if (v_isShared_2116_ == 0)
{
v___x_2118_ = v___x_2115_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v_a_2113_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
v___jp_2097_:
{
lean_object* v_expr_2099_; lean_object* v_type_x3f_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; 
v_expr_2099_ = lean_ctor_get(v_a_2036_, 0);
lean_inc_ref(v_expr_2099_);
v_type_x3f_2100_ = lean_ctor_get(v_a_2036_, 1);
lean_inc(v_type_x3f_2100_);
lean_dec_ref(v_a_2036_);
v___x_2101_ = lean_expr_abstract_range(v_type_2094_, v_n_2048_, v_fvars_2034_);
lean_dec_ref(v_type_2094_);
v___x_2102_ = lean_expr_abstract_range(v_value_2095_, v_n_2048_, v_fvars_2034_);
lean_dec_ref(v_value_2095_);
lean_inc_ref(v___x_2102_);
lean_inc_ref(v___x_2101_);
lean_inc(v_userName_2093_);
v___x_2103_ = l_Lean_Expr_letE___override(v_userName_2093_, v___x_2101_, v___x_2102_, v_expr_2099_, v_nondep_2098_);
if (lean_obj_tag(v_type_x3f_2100_) == 0)
{
lean_dec_ref(v___x_2102_);
lean_dec_ref(v___x_2101_);
lean_dec(v_userName_2093_);
v___y_2054_ = v___x_2103_;
v___y_2055_ = v_type_x3f_2100_;
goto v___jp_2053_;
}
else
{
lean_object* v_val_2104_; uint8_t v___x_2105_; 
v_val_2104_ = lean_ctor_get(v_type_x3f_2100_, 0);
lean_inc(v_val_2104_);
lean_dec_ref_known(v_type_x3f_2100_, 1);
v___x_2105_ = lean_expr_has_loose_bvar(v_val_2104_, v_zero_2044_);
if (v___x_2105_ == 0)
{
lean_object* v___x_2106_; 
lean_dec_ref(v___x_2102_);
lean_dec_ref(v___x_2101_);
lean_dec(v_userName_2093_);
v___x_2106_ = lean_expr_lower_loose_bvars(v_val_2104_, v_one_2047_, v_one_2047_);
lean_dec(v_val_2104_);
v___y_2059_ = v___x_2103_;
v___y_2060_ = v___x_2106_;
goto v___jp_2058_;
}
else
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_Expr_letE___override(v_userName_2093_, v___x_2101_, v___x_2102_, v_val_2104_, v_nondep_2098_);
v___y_2059_ = v___x_2103_;
v___y_2060_ = v___x_2107_;
goto v___jp_2058_;
}
}
}
}
}
else
{
lean_object* v___x_2121_; 
lean_dec(v_a_2065_);
lean_dec_ref(v_a_2036_);
lean_inc(v_fvarId_2063_);
v___x_2121_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2063_, v___y_2041_, v___y_2042_);
v___y_2050_ = v___x_2121_;
goto v___jp_2049_;
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec(v_n_2048_);
lean_dec_ref(v_a_2036_);
v_a_2122_ = lean_ctor_get(v___x_2064_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2064_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2064_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2064_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v___x_2130_; lean_object* v___x_2131_; 
lean_dec_ref(v_a_2036_);
v___x_2130_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2131_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2130_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
v___y_2050_ = v___x_2131_;
goto v___jp_2049_;
}
v___jp_2049_:
{
if (lean_obj_tag(v___y_2050_) == 0)
{
lean_object* v_a_2051_; 
v_a_2051_ = lean_ctor_get(v___y_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___y_2050_, 1);
v_i_2035_ = v_n_2048_;
v_a_2036_ = v_a_2051_;
goto _start;
}
else
{
lean_dec(v_n_2048_);
return v___y_2050_;
}
}
v___jp_2053_:
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2056_, 0, v___y_2054_);
lean_ctor_set(v___x_2056_, 1, v___y_2055_);
v_i_2035_ = v_n_2048_;
v_a_2036_ = v___x_2056_;
goto _start;
}
v___jp_2058_:
{
lean_object* v___x_2061_; 
v___x_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2061_, 0, v___y_2060_);
v___y_2054_ = v___y_2059_;
v___y_2055_ = v___x_2061_;
goto v___jp_2053_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2132_, lean_object* v_i_2133_, lean_object* v_a_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_){
_start:
{
lean_object* v_res_2142_; 
v_res_2142_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2132_, v_i_2133_, v_a_2134_, v___y_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_, v___y_2140_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
lean_dec(v___y_2136_);
lean_dec(v___y_2135_);
lean_dec_ref(v_fvars_2132_);
return v_res_2142_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
if (lean_obj_tag(v_a_2143_) == 0)
{
lean_object* v___x_2145_; 
v___x_2145_ = l_List_reverse___redArg(v_a_2144_);
return v___x_2145_;
}
else
{
lean_object* v_head_2146_; lean_object* v_tail_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2156_; 
v_head_2146_ = lean_ctor_get(v_a_2143_, 0);
v_tail_2147_ = lean_ctor_get(v_a_2143_, 1);
v_isSharedCheck_2156_ = !lean_is_exclusive(v_a_2143_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2149_ = v_a_2143_;
v_isShared_2150_ = v_isSharedCheck_2156_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_tail_2147_);
lean_inc(v_head_2146_);
lean_dec(v_a_2143_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2156_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2151_; lean_object* v___x_2153_; 
v___x_2151_ = l_Lean_MessageData_ofExpr(v_head_2146_);
if (v_isShared_2150_ == 0)
{
lean_ctor_set(v___x_2149_, 1, v_a_2144_);
lean_ctor_set(v___x_2149_, 0, v___x_2151_);
v___x_2153_ = v___x_2149_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v___x_2151_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_a_2144_);
v___x_2153_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
v_a_2143_ = v_tail_2147_;
v_a_2144_ = v___x_2153_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2157_; double v___x_2158_; 
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = lean_float_of_nat(v___x_2157_);
return v___x_2158_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2162_, lean_object* v_msg_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_ref_2169_; lean_object* v___x_2170_; lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2215_; 
v_ref_2169_ = lean_ctor_get(v___y_2166_, 5);
v___x_2170_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2163_, v___y_2164_, v___y_2165_, v___y_2166_, v___y_2167_);
v_a_2171_ = lean_ctor_get(v___x_2170_, 0);
v_isSharedCheck_2215_ = !lean_is_exclusive(v___x_2170_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2173_ = v___x_2170_;
v_isShared_2174_ = v_isSharedCheck_2215_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2170_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2215_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v_traceState_2176_; lean_object* v_env_2177_; lean_object* v_nextMacroScope_2178_; lean_object* v_ngen_2179_; lean_object* v_auxDeclNGen_2180_; lean_object* v_cache_2181_; lean_object* v_messages_2182_; lean_object* v_infoState_2183_; lean_object* v_snapshotTasks_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2214_; 
v___x_2175_ = lean_st_ref_take(v___y_2167_);
v_traceState_2176_ = lean_ctor_get(v___x_2175_, 4);
v_env_2177_ = lean_ctor_get(v___x_2175_, 0);
v_nextMacroScope_2178_ = lean_ctor_get(v___x_2175_, 1);
v_ngen_2179_ = lean_ctor_get(v___x_2175_, 2);
v_auxDeclNGen_2180_ = lean_ctor_get(v___x_2175_, 3);
v_cache_2181_ = lean_ctor_get(v___x_2175_, 5);
v_messages_2182_ = lean_ctor_get(v___x_2175_, 6);
v_infoState_2183_ = lean_ctor_get(v___x_2175_, 7);
v_snapshotTasks_2184_ = lean_ctor_get(v___x_2175_, 8);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2186_ = v___x_2175_;
v_isShared_2187_ = v_isSharedCheck_2214_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snapshotTasks_2184_);
lean_inc(v_infoState_2183_);
lean_inc(v_messages_2182_);
lean_inc(v_cache_2181_);
lean_inc(v_traceState_2176_);
lean_inc(v_auxDeclNGen_2180_);
lean_inc(v_ngen_2179_);
lean_inc(v_nextMacroScope_2178_);
lean_inc(v_env_2177_);
lean_dec(v___x_2175_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2214_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
uint64_t v_tid_2188_; lean_object* v_traces_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2213_; 
v_tid_2188_ = lean_ctor_get_uint64(v_traceState_2176_, sizeof(void*)*1);
v_traces_2189_ = lean_ctor_get(v_traceState_2176_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_traceState_2176_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2191_ = v_traceState_2176_;
v_isShared_2192_ = v_isSharedCheck_2213_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_traces_2189_);
lean_dec(v_traceState_2176_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2213_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; double v___x_2194_; uint8_t v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2203_; 
v___x_2193_ = lean_box(0);
v___x_2194_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2195_ = 0;
v___x_2196_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2197_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2197_, 0, v_cls_2162_);
lean_ctor_set(v___x_2197_, 1, v___x_2193_);
lean_ctor_set(v___x_2197_, 2, v___x_2196_);
lean_ctor_set_float(v___x_2197_, sizeof(void*)*3, v___x_2194_);
lean_ctor_set_float(v___x_2197_, sizeof(void*)*3 + 8, v___x_2194_);
lean_ctor_set_uint8(v___x_2197_, sizeof(void*)*3 + 16, v___x_2195_);
v___x_2198_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2199_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v_a_2171_);
lean_ctor_set(v___x_2199_, 2, v___x_2198_);
lean_inc(v_ref_2169_);
v___x_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2200_, 0, v_ref_2169_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
v___x_2201_ = l_Lean_PersistentArray_push___redArg(v_traces_2189_, v___x_2200_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2201_);
v___x_2203_ = v___x_2191_;
goto v_reusejp_2202_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v___x_2201_);
lean_ctor_set_uint64(v_reuseFailAlloc_2212_, sizeof(void*)*1, v_tid_2188_);
v___x_2203_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2202_;
}
v_reusejp_2202_:
{
lean_object* v___x_2205_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 4, v___x_2203_);
v___x_2205_ = v___x_2186_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_env_2177_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_nextMacroScope_2178_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_ngen_2179_);
lean_ctor_set(v_reuseFailAlloc_2211_, 3, v_auxDeclNGen_2180_);
lean_ctor_set(v_reuseFailAlloc_2211_, 4, v___x_2203_);
lean_ctor_set(v_reuseFailAlloc_2211_, 5, v_cache_2181_);
lean_ctor_set(v_reuseFailAlloc_2211_, 6, v_messages_2182_);
lean_ctor_set(v_reuseFailAlloc_2211_, 7, v_infoState_2183_);
lean_ctor_set(v_reuseFailAlloc_2211_, 8, v_snapshotTasks_2184_);
v___x_2205_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2209_; 
v___x_2206_ = lean_st_ref_set(v___y_2167_, v___x_2205_);
v___x_2207_ = lean_box(0);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2207_);
v___x_2209_ = v___x_2173_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2216_, lean_object* v_msg_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2216_, v_msg_2217_, v___y_2218_, v___y_2219_, v___y_2220_, v___y_2221_);
lean_dec(v___y_2221_);
lean_dec_ref(v___y_2220_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
return v_res_2223_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; 
v_cls_2234_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2236_ = l_Lean_Name_append(v___x_2235_, v_cls_2234_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2244_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2245_ = l_Lean_stringToMessageData(v___x_2244_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2250_ = l_Lean_MessageData_ofFormat(v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2251_, lean_object* v_body_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_, lean_object* v_a_2258_){
_start:
{
lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v_options_2291_; uint8_t v_hasTrace_2292_; 
v_options_2291_ = lean_ctor_get(v_a_2257_, 2);
v_hasTrace_2292_ = lean_ctor_get_uint8(v_options_2291_, sizeof(void*)*1);
if (v_hasTrace_2292_ == 0)
{
v___y_2273_ = v_a_2253_;
v___y_2274_ = v_a_2254_;
v___y_2275_ = v_a_2255_;
v___y_2276_ = v_a_2256_;
v___y_2277_ = v_a_2257_;
v___y_2278_ = v_a_2258_;
goto v___jp_2272_;
}
else
{
lean_object* v_inheritedTraceOptions_2293_; lean_object* v_cls_2294_; lean_object* v___x_2295_; uint8_t v___x_2296_; 
v_inheritedTraceOptions_2293_ = lean_ctor_get(v_a_2257_, 13);
v_cls_2294_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2295_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2296_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2293_, v_options_2291_, v___x_2295_);
if (v___x_2296_ == 0)
{
v___y_2273_ = v_a_2253_;
v___y_2274_ = v_a_2254_;
v___y_2275_ = v_a_2255_;
v___y_2276_ = v_a_2256_;
v___y_2277_ = v_a_2257_;
v___y_2278_ = v_a_2258_;
goto v___jp_2272_;
}
else
{
lean_object* v_expr_2297_; lean_object* v_type_x3f_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___y_2311_; 
v_expr_2297_ = lean_ctor_get(v_body_2252_, 0);
v_type_x3f_2298_ = lean_ctor_get(v_body_2252_, 1);
v___x_2299_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2251_);
v___x_2300_ = lean_array_to_list(v_fvars_2251_);
v___x_2301_ = lean_box(0);
v___x_2302_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2300_, v___x_2301_);
v___x_2303_ = l_Lean_MessageData_ofList(v___x_2302_);
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2299_);
lean_ctor_set(v___x_2304_, 1, v___x_2303_);
v___x_2305_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2304_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
lean_inc_ref(v_expr_2297_);
v___x_2307_ = l_Lean_MessageData_ofExpr(v_expr_2297_);
v___x_2308_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2307_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
if (lean_obj_tag(v_type_x3f_2298_) == 0)
{
lean_object* v___x_2324_; 
v___x_2324_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2311_ = v___x_2324_;
goto v___jp_2310_;
}
else
{
lean_object* v_val_2325_; lean_object* v___x_2326_; 
v_val_2325_ = lean_ctor_get(v_type_x3f_2298_, 0);
lean_inc(v_val_2325_);
v___x_2326_ = l_Lean_MessageData_ofExpr(v_val_2325_);
v___y_2311_ = v___x_2326_;
goto v___jp_2310_;
}
v___jp_2310_:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2309_);
lean_ctor_set(v___x_2312_, 1, v___y_2311_);
v___x_2313_ = l_Lean_indentD(v___x_2312_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2306_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2294_, v___x_2314_, v_a_2255_, v_a_2256_, v_a_2257_, v_a_2258_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_dec_ref_known(v___x_2315_, 1);
v___y_2273_ = v_a_2253_;
v___y_2274_ = v_a_2254_;
v___y_2275_ = v_a_2255_;
v___y_2276_ = v_a_2256_;
v___y_2277_ = v_a_2257_;
v___y_2278_ = v_a_2258_;
goto v___jp_2272_;
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec_ref(v_body_2252_);
lean_dec_ref(v_fvars_2251_);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
}
}
v___jp_2260_:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___y_2265_);
lean_ctor_set(v___x_2269_, 1, v___y_2268_);
v___x_2270_ = lean_array_get_size(v_fvars_2251_);
v___x_2271_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2251_, v___x_2270_, v___x_2269_, v___y_2264_, v___y_2263_, v___y_2261_, v___y_2266_, v___y_2262_, v___y_2267_);
lean_dec_ref(v_fvars_2251_);
return v___x_2271_;
}
v___jp_2272_:
{
lean_object* v_expr_2279_; lean_object* v_type_x3f_2280_; lean_object* v___x_2281_; 
v_expr_2279_ = lean_ctor_get(v_body_2252_, 0);
lean_inc_ref(v_expr_2279_);
v_type_x3f_2280_ = lean_ctor_get(v_body_2252_, 1);
lean_inc(v_type_x3f_2280_);
lean_dec_ref(v_body_2252_);
v___x_2281_ = lean_expr_abstract(v_expr_2279_, v_fvars_2251_);
lean_dec_ref(v_expr_2279_);
if (lean_obj_tag(v_type_x3f_2280_) == 0)
{
v___y_2261_ = v___y_2275_;
v___y_2262_ = v___y_2277_;
v___y_2263_ = v___y_2274_;
v___y_2264_ = v___y_2273_;
v___y_2265_ = v___x_2281_;
v___y_2266_ = v___y_2276_;
v___y_2267_ = v___y_2278_;
v___y_2268_ = v_type_x3f_2280_;
goto v___jp_2260_;
}
else
{
lean_object* v_val_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2290_; 
v_val_2282_ = lean_ctor_get(v_type_x3f_2280_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v_type_x3f_2280_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2284_ = v_type_x3f_2280_;
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_val_2282_);
lean_dec(v_type_x3f_2280_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2290_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; lean_object* v___x_2288_; 
v___x_2286_ = lean_expr_abstract(v_val_2282_, v_fvars_2251_);
lean_dec(v_val_2282_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2286_);
v___x_2288_ = v___x_2284_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v___x_2286_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
v___y_2261_ = v___y_2275_;
v___y_2262_ = v___y_2277_;
v___y_2263_ = v___y_2274_;
v___y_2264_ = v___y_2273_;
v___y_2265_ = v___x_2281_;
v___y_2266_ = v___y_2276_;
v___y_2267_ = v___y_2278_;
v___y_2268_ = v___x_2288_;
goto v___jp_2260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2327_, lean_object* v_body_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2327_, v_body_2328_, v_a_2329_, v_a_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
lean_dec(v_a_2330_);
lean_dec(v_a_2329_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2337_, lean_object* v_n_2338_, lean_object* v_i_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_){
_start:
{
lean_object* v___x_2349_; 
v___x_2349_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2337_, v_i_2339_, v_a_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
return v___x_2349_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2350_, lean_object* v_n_2351_, lean_object* v_i_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2350_, v_n_2351_, v_i_2352_, v_a_2353_, v_a_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec(v___y_2355_);
lean_dec(v_n_2351_);
lean_dec_ref(v_fvars_2350_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2363_, lean_object* v_msg_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2363_, v_msg_2364_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
return v___x_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2373_, lean_object* v_msg_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2373_, v_msg_2374_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec(v___y_2375_);
return v_res_2382_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; 
v___x_2384_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2385_ = l_Lean_stringToMessageData(v___x_2384_);
return v___x_2385_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; 
v___x_2387_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2388_ = l_Lean_stringToMessageData(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2389_, lean_object* v_structName_2390_, lean_object* v_idx_2391_, lean_object* v_a_2392_, lean_object* v_00_u03b1_2393_, lean_object* v_x_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_){
_start:
{
lean_object* v_expr_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2417_; 
v_expr_2402_ = lean_ctor_get(v_struct_2389_, 0);
v_isSharedCheck_2417_ = !lean_is_exclusive(v_struct_2389_);
if (v_isSharedCheck_2417_ == 0)
{
lean_object* v_unused_2418_; 
v_unused_2418_ = lean_ctor_get(v_struct_2389_, 1);
lean_dec(v_unused_2418_);
v___x_2404_ = v_struct_2389_;
v_isShared_2405_ = v_isSharedCheck_2417_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_expr_2402_);
lean_dec(v_struct_2389_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2417_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2406_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2407_ = l_Lean_mkProj(v_structName_2390_, v_idx_2391_, v_expr_2402_);
v___x_2408_ = l_Lean_indentExpr(v___x_2407_);
if (v_isShared_2405_ == 0)
{
lean_ctor_set_tag(v___x_2404_, 7);
lean_ctor_set(v___x_2404_, 1, v___x_2408_);
lean_ctor_set(v___x_2404_, 0, v___x_2406_);
v___x_2410_ = v___x_2404_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2416_; 
v_reuseFailAlloc_2416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2416_, 0, v___x_2406_);
lean_ctor_set(v_reuseFailAlloc_2416_, 1, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2416_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2411_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2410_);
lean_ctor_set(v___x_2412_, 1, v___x_2411_);
v___x_2413_ = l_Lean_indentExpr(v_a_2392_);
v___x_2414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2412_);
lean_ctor_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2414_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
return v___x_2415_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2419_, lean_object* v_structName_2420_, lean_object* v_idx_2421_, lean_object* v_a_2422_, lean_object* v_00_u03b1_2423_, lean_object* v_x_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2419_, v_structName_2420_, v_idx_2421_, v_a_2422_, v_00_u03b1_2423_, v_x_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v___y_2426_);
lean_dec(v___y_2425_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v_env_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = lean_st_ref_get(v___y_2439_);
v_env_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc_ref(v_env_2442_);
lean_dec(v___x_2441_);
v___x_2443_ = 0;
lean_inc(v_constName_2433_);
v___x_2444_ = l_Lean_Environment_find_x3f(v_env_2442_, v_constName_2433_, v___x_2443_);
if (lean_obj_tag(v___x_2444_) == 0)
{
lean_object* v___x_2445_; 
v___x_2445_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
return v___x_2445_;
}
else
{
lean_object* v_val_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_constName_2433_);
v_val_2446_ = lean_ctor_get(v___x_2444_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2444_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2444_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_val_2446_);
lean_dec(v___x_2444_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set_tag(v___x_2448_, 0);
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_val_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2454_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
lean_dec(v___y_2460_);
lean_dec_ref(v___y_2459_);
lean_dec(v___y_2458_);
lean_dec_ref(v___y_2457_);
lean_dec(v___y_2456_);
lean_dec(v___y_2455_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2463_, lean_object* v_structName_2464_, lean_object* v_idx_2465_, lean_object* v_a_2466_, lean_object* v_00_u03b1_2467_, lean_object* v_x_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_){
_start:
{
lean_object* v_expr_2476_; lean_object* v___x_2478_; uint8_t v_isShared_2479_; uint8_t v_isSharedCheck_2491_; 
v_expr_2476_ = lean_ctor_get(v_struct_2463_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v_struct_2463_);
if (v_isSharedCheck_2491_ == 0)
{
lean_object* v_unused_2492_; 
v_unused_2492_ = lean_ctor_get(v_struct_2463_, 1);
lean_dec(v_unused_2492_);
v___x_2478_ = v_struct_2463_;
v_isShared_2479_ = v_isSharedCheck_2491_;
goto v_resetjp_2477_;
}
else
{
lean_inc(v_expr_2476_);
lean_dec(v_struct_2463_);
v___x_2478_ = lean_box(0);
v_isShared_2479_ = v_isSharedCheck_2491_;
goto v_resetjp_2477_;
}
v_resetjp_2477_:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2484_; 
v___x_2480_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2481_ = l_Lean_mkProj(v_structName_2464_, v_idx_2465_, v_expr_2476_);
v___x_2482_ = l_Lean_indentExpr(v___x_2481_);
if (v_isShared_2479_ == 0)
{
lean_ctor_set_tag(v___x_2478_, 7);
lean_ctor_set(v___x_2478_, 1, v___x_2482_);
lean_ctor_set(v___x_2478_, 0, v___x_2480_);
v___x_2484_ = v___x_2478_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v___x_2480_);
lean_ctor_set(v_reuseFailAlloc_2490_, 1, v___x_2482_);
v___x_2484_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v___x_2485_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2484_);
lean_ctor_set(v___x_2486_, 1, v___x_2485_);
v___x_2487_ = l_Lean_indentExpr(v_a_2466_);
v___x_2488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2486_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2488_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
return v___x_2489_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2493_, lean_object* v_structName_2494_, lean_object* v_idx_2495_, lean_object* v_a_2496_, lean_object* v_00_u03b1_2497_, lean_object* v_x_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2493_, v_structName_2494_, v_idx_2495_, v_a_2496_, v_00_u03b1_2497_, v_x_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec(v___y_2499_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2507_, lean_object* v_fst_2508_, lean_object* v_struct_2509_, lean_object* v_structName_2510_, uint8_t v_a_2511_, lean_object* v___f_2512_, lean_object* v_snd_2513_, lean_object* v_____r_2514_, lean_object* v_ctorType_2515_, lean_object* v_j_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_){
_start:
{
if (lean_obj_tag(v_ctorType_2515_) == 7)
{
lean_object* v_binderType_2524_; lean_object* v_body_2525_; lean_object* v___x_2526_; 
lean_dec(v_snd_2513_);
v_binderType_2524_ = lean_ctor_get(v_ctorType_2515_, 1);
lean_inc_ref(v_binderType_2524_);
v_body_2525_ = lean_ctor_get(v_ctorType_2515_, 2);
lean_inc_ref(v_body_2525_);
lean_dec_ref_known(v_ctorType_2515_, 3);
v___x_2526_ = lean_expr_instantiate_rev_range(v_binderType_2524_, v_j_2516_, v_a_2507_, v_fst_2508_);
lean_dec_ref(v_binderType_2524_);
if (v_a_2511_ == 0)
{
lean_dec_ref(v___f_2512_);
goto v___jp_2527_;
}
else
{
lean_object* v___x_2543_; 
lean_inc_ref(v___x_2526_);
v___x_2543_ = l_Lean_Meta_isProp(v___x_2526_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v_a_2544_; uint8_t v___x_2545_; 
v_a_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2544_);
lean_dec_ref_known(v___x_2543_, 1);
v___x_2545_ = lean_unbox(v_a_2544_);
lean_dec(v_a_2544_);
if (v___x_2545_ == 0)
{
lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2546_ = lean_box(0);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc(v___y_2517_);
v___x_2547_ = lean_apply_9(v___f_2512_, lean_box(0), v___x_2546_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, lean_box(0));
if (lean_obj_tag(v___x_2547_) == 0)
{
lean_dec_ref_known(v___x_2547_, 1);
goto v___jp_2527_;
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref(v___x_2526_);
lean_dec_ref(v_body_2525_);
lean_dec(v_structName_2510_);
lean_dec_ref(v_struct_2509_);
lean_dec(v_fst_2508_);
lean_dec(v_a_2507_);
v_a_2548_ = lean_ctor_get(v___x_2547_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2547_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2547_);
v___x_2550_ = lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
v_resetjp_2549_:
{
lean_object* v___x_2553_; 
if (v_isShared_2551_ == 0)
{
v___x_2553_ = v___x_2550_;
goto v_reusejp_2552_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_a_2548_);
v___x_2553_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2552_;
}
v_reusejp_2552_:
{
return v___x_2553_;
}
}
}
}
else
{
lean_dec_ref(v___f_2512_);
goto v___jp_2527_;
}
}
else
{
lean_object* v_a_2556_; lean_object* v___x_2558_; uint8_t v_isShared_2559_; uint8_t v_isSharedCheck_2563_; 
lean_dec_ref(v___x_2526_);
lean_dec_ref(v_body_2525_);
lean_dec_ref(v___f_2512_);
lean_dec(v_structName_2510_);
lean_dec_ref(v_struct_2509_);
lean_dec(v_fst_2508_);
lean_dec(v_a_2507_);
v_a_2556_ = lean_ctor_get(v___x_2543_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2558_ = v___x_2543_;
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
else
{
lean_inc(v_a_2556_);
lean_dec(v___x_2543_);
v___x_2558_ = lean_box(0);
v_isShared_2559_ = v_isSharedCheck_2563_;
goto v_resetjp_2557_;
}
v_resetjp_2557_:
{
lean_object* v___x_2561_; 
if (v_isShared_2559_ == 0)
{
v___x_2561_ = v___x_2558_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
v___jp_2527_:
{
lean_object* v_expr_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2541_; 
v_expr_2528_ = lean_ctor_get(v_struct_2509_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_struct_2509_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v_struct_2509_, 1);
lean_dec(v_unused_2542_);
v___x_2530_ = v_struct_2509_;
v_isShared_2531_ = v_isSharedCheck_2541_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_expr_2528_);
lean_dec(v_struct_2509_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2541_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2535_; 
v___x_2532_ = l_Lean_Expr_proj___override(v_structName_2510_, v_a_2507_, v_expr_2528_);
v___x_2533_ = lean_array_push(v_fst_2508_, v___x_2532_);
lean_inc(v_j_2516_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 1, v___x_2526_);
lean_ctor_set(v___x_2530_, 0, v_j_2516_);
v___x_2535_ = v___x_2530_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_j_2516_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v___x_2526_);
v___x_2535_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2533_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
v___x_2537_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2537_, 0, v_body_2525_);
lean_ctor_set(v___x_2537_, 1, v___x_2536_);
v___x_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2538_, 0, v___x_2537_);
v___x_2539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2538_);
return v___x_2539_;
}
}
}
}
else
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
lean_dec(v_structName_2510_);
lean_dec_ref(v_struct_2509_);
lean_dec(v_a_2507_);
v___x_2564_ = lean_box(0);
lean_inc(v___y_2522_);
lean_inc_ref(v___y_2521_);
lean_inc(v___y_2520_);
lean_inc_ref(v___y_2519_);
lean_inc(v___y_2518_);
lean_inc(v___y_2517_);
v___x_2565_ = lean_apply_9(v___f_2512_, lean_box(0), v___x_2564_, v___y_2517_, v___y_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_, lean_box(0));
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2576_; 
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2576_ == 0)
{
lean_object* v_unused_2577_; 
v_unused_2577_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2577_);
v___x_2567_ = v___x_2565_;
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v___x_2565_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2576_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2574_; 
lean_inc(v_j_2516_);
v___x_2569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2569_, 0, v_j_2516_);
lean_ctor_set(v___x_2569_, 1, v_snd_2513_);
v___x_2570_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2570_, 0, v_fst_2508_);
lean_ctor_set(v___x_2570_, 1, v___x_2569_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v_ctorType_2515_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2572_, 0, v___x_2571_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set(v___x_2567_, 0, v___x_2572_);
v___x_2574_ = v___x_2567_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec_ref(v_ctorType_2515_);
lean_dec(v_snd_2513_);
lean_dec(v_fst_2508_);
v_a_2578_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2565_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2565_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2586_ = _args[0];
lean_object* v_fst_2587_ = _args[1];
lean_object* v_struct_2588_ = _args[2];
lean_object* v_structName_2589_ = _args[3];
lean_object* v_a_2590_ = _args[4];
lean_object* v___f_2591_ = _args[5];
lean_object* v_snd_2592_ = _args[6];
lean_object* v_____r_2593_ = _args[7];
lean_object* v_ctorType_2594_ = _args[8];
lean_object* v_j_2595_ = _args[9];
lean_object* v___y_2596_ = _args[10];
lean_object* v___y_2597_ = _args[11];
lean_object* v___y_2598_ = _args[12];
lean_object* v___y_2599_ = _args[13];
lean_object* v___y_2600_ = _args[14];
lean_object* v___y_2601_ = _args[15];
lean_object* v___y_2602_ = _args[16];
_start:
{
uint8_t v_a_23462__boxed_2603_; lean_object* v_res_2604_; 
v_a_23462__boxed_2603_ = lean_unbox(v_a_2590_);
v_res_2604_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2586_, v_fst_2587_, v_struct_2588_, v_structName_2589_, v_a_23462__boxed_2603_, v___f_2591_, v_snd_2592_, v_____r_2593_, v_ctorType_2594_, v_j_2595_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_);
lean_dec(v___y_2601_);
lean_dec_ref(v___y_2600_);
lean_dec(v___y_2599_);
lean_dec_ref(v___y_2598_);
lean_dec(v___y_2597_);
lean_dec(v___y_2596_);
lean_dec(v_j_2595_);
return v_res_2604_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2605_, lean_object* v_struct_2606_, lean_object* v_structName_2607_, uint8_t v_a_2608_, lean_object* v_idx_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_b_2612_, lean_object* v___y_2613_, lean_object* v___y_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___y_2621_; uint8_t v___x_2643_; 
v___x_2643_ = lean_nat_dec_le(v_a_2611_, v_upperBound_2605_);
if (v___x_2643_ == 0)
{
lean_object* v___x_2644_; 
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_idx_2609_);
lean_dec(v_structName_2607_);
lean_dec_ref(v_struct_2606_);
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v_b_2612_);
return v___x_2644_;
}
else
{
lean_object* v_snd_2645_; lean_object* v_snd_2646_; lean_object* v_fst_2647_; lean_object* v_fst_2648_; lean_object* v_fst_2649_; lean_object* v_snd_2650_; lean_object* v___f_2651_; uint8_t v___x_2652_; 
v_snd_2645_ = lean_ctor_get(v_b_2612_, 1);
lean_inc(v_snd_2645_);
v_snd_2646_ = lean_ctor_get(v_snd_2645_, 1);
lean_inc(v_snd_2646_);
v_fst_2647_ = lean_ctor_get(v_b_2612_, 0);
lean_inc(v_fst_2647_);
lean_dec_ref(v_b_2612_);
v_fst_2648_ = lean_ctor_get(v_snd_2645_, 0);
lean_inc(v_fst_2648_);
lean_dec(v_snd_2645_);
v_fst_2649_ = lean_ctor_get(v_snd_2646_, 0);
lean_inc(v_fst_2649_);
v_snd_2650_ = lean_ctor_get(v_snd_2646_, 1);
lean_inc(v_snd_2650_);
lean_dec(v_snd_2646_);
lean_inc_ref(v_a_2610_);
lean_inc(v_idx_2609_);
lean_inc(v_structName_2607_);
lean_inc_ref(v_struct_2606_);
v___f_2651_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2651_, 0, v_struct_2606_);
lean_closure_set(v___f_2651_, 1, v_structName_2607_);
lean_closure_set(v___f_2651_, 2, v_idx_2609_);
lean_closure_set(v___f_2651_, 3, v_a_2610_);
v___x_2652_ = l_Lean_Expr_isForall(v_fst_2647_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_expr_instantiate_rev_range(v_fst_2647_, v_fst_2649_, v_a_2611_, v_fst_2648_);
lean_dec(v_fst_2649_);
lean_dec(v_fst_2647_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
v___x_2654_ = lean_whnf(v___x_2653_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; 
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2656_ = lean_box(0);
lean_inc(v_structName_2607_);
lean_inc_ref(v_struct_2606_);
lean_inc(v_a_2611_);
v___x_2657_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2611_, v_fst_2648_, v_struct_2606_, v_structName_2607_, v_a_2608_, v___f_2651_, v_snd_2650_, v___x_2656_, v_a_2655_, v_a_2611_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
v___y_2621_ = v___x_2657_;
goto v___jp_2620_;
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec_ref(v___f_2651_);
lean_dec(v_snd_2650_);
lean_dec(v_fst_2648_);
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_idx_2609_);
lean_dec(v_structName_2607_);
lean_dec_ref(v_struct_2606_);
v_a_2658_ = lean_ctor_get(v___x_2654_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2654_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2654_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2654_);
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
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_box(0);
lean_inc(v_structName_2607_);
lean_inc_ref(v_struct_2606_);
lean_inc(v_a_2611_);
v___x_2667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2611_, v_fst_2648_, v_struct_2606_, v_structName_2607_, v_a_2608_, v___f_2651_, v_snd_2650_, v___x_2666_, v_fst_2647_, v_fst_2649_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
lean_dec(v_fst_2649_);
v___y_2621_ = v___x_2667_;
goto v___jp_2620_;
}
}
v___jp_2620_:
{
if (lean_obj_tag(v___y_2621_) == 0)
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2634_; 
v_a_2622_ = lean_ctor_get(v___y_2621_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___y_2621_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2624_ = v___y_2621_;
v_isShared_2625_ = v_isSharedCheck_2634_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___y_2621_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2634_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
if (lean_obj_tag(v_a_2622_) == 0)
{
lean_object* v_a_2626_; lean_object* v___x_2628_; 
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_idx_2609_);
lean_dec(v_structName_2607_);
lean_dec_ref(v_struct_2606_);
v_a_2626_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v_a_2622_, 1);
if (v_isShared_2625_ == 0)
{
lean_ctor_set(v___x_2624_, 0, v_a_2626_);
v___x_2628_ = v___x_2624_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2626_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
else
{
lean_object* v_a_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; 
lean_del_object(v___x_2624_);
v_a_2630_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_a_2630_);
lean_dec_ref_known(v_a_2622_, 1);
v___x_2631_ = lean_unsigned_to_nat(1u);
v___x_2632_ = lean_nat_add(v_a_2611_, v___x_2631_);
lean_dec(v_a_2611_);
v_a_2611_ = v___x_2632_;
v_b_2612_ = v_a_2630_;
goto _start;
}
}
}
else
{
lean_object* v_a_2635_; lean_object* v___x_2637_; uint8_t v_isShared_2638_; uint8_t v_isSharedCheck_2642_; 
lean_dec(v_a_2611_);
lean_dec_ref(v_a_2610_);
lean_dec(v_idx_2609_);
lean_dec(v_structName_2607_);
lean_dec_ref(v_struct_2606_);
v_a_2635_ = lean_ctor_get(v___y_2621_, 0);
v_isSharedCheck_2642_ = !lean_is_exclusive(v___y_2621_);
if (v_isSharedCheck_2642_ == 0)
{
v___x_2637_ = v___y_2621_;
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
else
{
lean_inc(v_a_2635_);
lean_dec(v___y_2621_);
v___x_2637_ = lean_box(0);
v_isShared_2638_ = v_isSharedCheck_2642_;
goto v_resetjp_2636_;
}
v_resetjp_2636_:
{
lean_object* v___x_2640_; 
if (v_isShared_2638_ == 0)
{
v___x_2640_ = v___x_2637_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2641_; 
v_reuseFailAlloc_2641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2641_, 0, v_a_2635_);
v___x_2640_ = v_reuseFailAlloc_2641_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
return v___x_2640_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2668_, lean_object* v_struct_2669_, lean_object* v_structName_2670_, lean_object* v_a_2671_, lean_object* v_idx_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_b_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
uint8_t v_a_23619__boxed_2683_; lean_object* v_res_2684_; 
v_a_23619__boxed_2683_ = lean_unbox(v_a_2671_);
v_res_2684_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2668_, v_struct_2669_, v_structName_2670_, v_a_23619__boxed_2683_, v_idx_2672_, v_a_2673_, v_a_2674_, v_b_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
lean_dec(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec(v_upperBound_2668_);
return v_res_2684_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2687_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2688_ = lean_unsigned_to_nat(18u);
v___x_2689_ = lean_unsigned_to_nat(1887u);
v___x_2690_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2691_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2692_ = l_mkPanicMessageWithDecl(v___x_2691_, v___x_2690_, v___x_2689_, v___x_2688_, v___x_2687_);
return v___x_2692_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2693_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2694_ = lean_unsigned_to_nat(0u);
v___x_2695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2695_, 0, v___x_2694_);
lean_ctor_set(v___x_2695_, 1, v___x_2693_);
return v___x_2695_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v___x_2696_);
return v___x_2698_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2699_; lean_object* v_dummy_2700_; 
v___x_2699_ = lean_box(0);
v_dummy_2700_ = l_Lean_Expr_sort___override(v___x_2699_);
return v_dummy_2700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2701_, lean_object* v_structName_2702_, lean_object* v_idx_2703_, lean_object* v_struct_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2719_; uint8_t v___x_2723_; 
v___x_2723_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2705_);
if (v___x_2723_ == 0)
{
lean_dec(v_idx_2703_);
lean_dec(v_structName_2702_);
if (lean_obj_tag(v_e_2701_) == 11)
{
lean_object* v_expr_2724_; lean_object* v_typeName_2725_; lean_object* v_idx_2726_; lean_object* v_struct_2727_; size_t v___x_2728_; size_t v___x_2729_; uint8_t v___x_2730_; 
v_expr_2724_ = lean_ctor_get(v_struct_2704_, 0);
lean_inc_ref(v_expr_2724_);
lean_dec_ref(v_struct_2704_);
v_typeName_2725_ = lean_ctor_get(v_e_2701_, 0);
v_idx_2726_ = lean_ctor_get(v_e_2701_, 1);
v_struct_2727_ = lean_ctor_get(v_e_2701_, 2);
v___x_2728_ = lean_ptr_addr(v_struct_2727_);
v___x_2729_ = lean_ptr_addr(v_expr_2724_);
v___x_2730_ = lean_usize_dec_eq(v___x_2728_, v___x_2729_);
if (v___x_2730_ == 0)
{
lean_object* v___x_2731_; 
lean_inc(v_idx_2726_);
lean_inc(v_typeName_2725_);
lean_dec_ref_known(v_e_2701_, 3);
v___x_2731_ = l_Lean_Expr_proj___override(v_typeName_2725_, v_idx_2726_, v_expr_2724_);
v___y_2719_ = v___x_2731_;
goto v___jp_2718_;
}
else
{
lean_dec_ref(v_expr_2724_);
v___y_2719_ = v_e_2701_;
goto v___jp_2718_;
}
}
else
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
lean_dec_ref(v_struct_2704_);
lean_dec_ref(v_e_2701_);
v___x_2732_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2733_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2732_);
v___y_2719_ = v___x_2733_;
goto v___jp_2718_;
}
}
else
{
lean_object* v___x_2734_; 
lean_inc_ref(v_struct_2704_);
v___x_2734_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2704_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v___x_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
lean_inc(v_a_2710_);
lean_inc_ref(v_a_2709_);
lean_inc(v_a_2708_);
lean_inc_ref(v_a_2707_);
v___x_2736_ = lean_whnf(v_a_2735_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc_n(v_a_2737_, 2);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = l_Lean_Meta_isProp(v_a_2737_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2740_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_a_2739_);
lean_dec_ref_known(v___x_2738_, 1);
v___x_2740_ = l_Lean_Expr_getAppFn(v_a_2737_);
if (lean_obj_tag(v___x_2740_) == 4)
{
lean_object* v_declName_2741_; lean_object* v_us_2742_; lean_object* v___x_2743_; lean_object* v_env_2747_; uint8_t v___x_2748_; lean_object* v___x_2749_; 
v_declName_2741_ = lean_ctor_get(v___x_2740_, 0);
lean_inc(v_declName_2741_);
v_us_2742_ = lean_ctor_get(v___x_2740_, 1);
lean_inc(v_us_2742_);
lean_dec_ref_known(v___x_2740_, 2);
v___x_2743_ = lean_st_ref_get(v_a_2710_);
v_env_2747_ = lean_ctor_get(v___x_2743_, 0);
lean_inc_ref(v_env_2747_);
lean_dec(v___x_2743_);
v___x_2748_ = 0;
v___x_2749_ = l_Lean_Environment_find_x3f(v_env_2747_, v_declName_2741_, v___x_2748_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
v___x_2750_ = lean_box(0);
v___x_2751_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2704_, v_structName_2702_, v_idx_2703_, v_a_2737_, lean_box(0), v___x_2750_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2751_;
}
else
{
lean_object* v_val_2752_; 
v_val_2752_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_val_2752_);
lean_dec_ref_known(v___x_2749_, 1);
if (lean_obj_tag(v_val_2752_) == 5)
{
lean_object* v_val_2753_; lean_object* v_ctors_2754_; 
v_val_2753_ = lean_ctor_get(v_val_2752_, 0);
lean_inc_ref(v_val_2753_);
lean_dec_ref_known(v_val_2752_, 1);
v_ctors_2754_ = lean_ctor_get(v_val_2753_, 4);
lean_inc(v_ctors_2754_);
if (lean_obj_tag(v_ctors_2754_) == 1)
{
lean_object* v_tail_2755_; 
v_tail_2755_ = lean_ctor_get(v_ctors_2754_, 1);
if (lean_obj_tag(v_tail_2755_) == 0)
{
lean_object* v_toConstantVal_2756_; lean_object* v_numParams_2757_; lean_object* v_numIndices_2758_; lean_object* v_head_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2868_; 
v_toConstantVal_2756_ = lean_ctor_get(v_val_2753_, 0);
lean_inc_ref(v_toConstantVal_2756_);
v_numParams_2757_ = lean_ctor_get(v_val_2753_, 1);
lean_inc(v_numParams_2757_);
v_numIndices_2758_ = lean_ctor_get(v_val_2753_, 2);
lean_inc(v_numIndices_2758_);
lean_dec_ref(v_val_2753_);
v_head_2759_ = lean_ctor_get(v_ctors_2754_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v_ctors_2754_);
if (v_isSharedCheck_2868_ == 0)
{
lean_object* v_unused_2869_; 
v_unused_2869_ = lean_ctor_get(v_ctors_2754_, 1);
lean_dec(v_unused_2869_);
v___x_2761_ = v_ctors_2754_;
v_isShared_2762_ = v_isSharedCheck_2868_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_head_2759_);
lean_dec(v_ctors_2754_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2868_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; 
v___x_2763_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2759_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
if (lean_obj_tag(v___x_2763_) == 0)
{
lean_object* v_a_2764_; 
v_a_2764_ = lean_ctor_get(v___x_2763_, 0);
lean_inc(v_a_2764_);
lean_dec_ref_known(v___x_2763_, 1);
if (lean_obj_tag(v_a_2764_) == 6)
{
lean_object* v_val_2765_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; lean_object* v___y_2772_; lean_object* v___y_2773_; lean_object* v___y_2821_; lean_object* v___y_2822_; lean_object* v___y_2823_; lean_object* v___y_2824_; lean_object* v___y_2825_; lean_object* v___y_2826_; lean_object* v_name_2846_; uint8_t v___x_2847_; 
v_val_2765_ = lean_ctor_get(v_a_2764_, 0);
lean_inc_ref(v_val_2765_);
lean_dec_ref_known(v_a_2764_, 1);
v_name_2846_ = lean_ctor_get(v_toConstantVal_2756_, 0);
lean_inc(v_name_2846_);
lean_dec_ref(v_toConstantVal_2756_);
v___x_2847_ = lean_name_eq(v_name_2846_, v_structName_2702_);
lean_dec(v_name_2846_);
if (v___x_2847_ == 0)
{
lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v_val_2765_);
lean_del_object(v___x_2761_);
lean_dec(v_numIndices_2758_);
lean_dec(v_numParams_2757_);
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
v___x_2848_ = lean_box(0);
v___x_2849_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2704_, v_structName_2702_, v_idx_2703_, v_a_2737_, lean_box(0), v___x_2848_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
v_a_2850_ = lean_ctor_get(v___x_2849_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2849_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2849_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2849_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
else
{
v___y_2821_ = v_a_2705_;
v___y_2822_ = v_a_2706_;
v___y_2823_ = v_a_2707_;
v___y_2824_ = v_a_2708_;
v___y_2825_ = v_a_2709_;
v___y_2826_ = v_a_2710_;
goto v___jp_2820_;
}
v___jp_2766_:
{
lean_object* v_toConstantVal_2774_; lean_object* v_name_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; 
v_toConstantVal_2774_ = lean_ctor_get(v_val_2765_, 0);
lean_inc_ref(v_toConstantVal_2774_);
lean_dec_ref(v_val_2765_);
v_name_2775_ = lean_ctor_get(v_toConstantVal_2774_, 0);
lean_inc(v_name_2775_);
lean_dec_ref(v_toConstantVal_2774_);
v___x_2776_ = l_Lean_mkConst(v_name_2775_, v_us_2742_);
v___x_2777_ = lean_unsigned_to_nat(0u);
v___x_2778_ = l_Array_toSubarray___redArg(v___y_2767_, v___x_2777_, v_numParams_2757_);
v___x_2779_ = l_Subarray_copy___redArg(v___x_2778_);
v___x_2780_ = l_Lean_mkAppN(v___x_2776_, v___x_2779_);
lean_dec_ref(v___x_2779_);
lean_inc(v___y_2773_);
lean_inc_ref(v___y_2772_);
lean_inc(v___y_2771_);
lean_inc_ref(v___y_2770_);
v___x_2781_ = lean_infer_type(v___x_2780_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2785_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
lean_inc(v_a_2782_);
lean_dec_ref_known(v___x_2781_, 1);
v___x_2783_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2762_ == 0)
{
lean_ctor_set_tag(v___x_2761_, 0);
lean_ctor_set(v___x_2761_, 1, v___x_2783_);
lean_ctor_set(v___x_2761_, 0, v_a_2782_);
v___x_2785_ = v___x_2761_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2782_);
lean_ctor_set(v_reuseFailAlloc_2811_, 1, v___x_2783_);
v___x_2785_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
uint8_t v___x_2786_; lean_object* v___x_2787_; 
v___x_2786_ = lean_unbox(v_a_2739_);
lean_dec(v_a_2739_);
lean_inc_ref(v_struct_2704_);
lean_inc(v_idx_2703_);
v___x_2787_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2703_, v_struct_2704_, v_structName_2702_, v___x_2786_, v_idx_2703_, v_a_2737_, v___x_2777_, v___x_2785_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_);
lean_dec(v_idx_2703_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v_a_2788_; lean_object* v_snd_2789_; lean_object* v_snd_2790_; lean_object* v_snd_2791_; lean_object* v_expr_2792_; lean_object* v___x_2793_; 
v_a_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_a_2788_);
lean_dec_ref_known(v___x_2787_, 1);
v_snd_2789_ = lean_ctor_get(v_a_2788_, 1);
lean_inc(v_snd_2789_);
lean_dec(v_a_2788_);
v_snd_2790_ = lean_ctor_get(v_snd_2789_, 1);
lean_inc(v_snd_2790_);
lean_dec(v_snd_2789_);
v_snd_2791_ = lean_ctor_get(v_snd_2790_, 1);
lean_inc(v_snd_2791_);
lean_dec(v_snd_2790_);
v_expr_2792_ = lean_ctor_get(v_struct_2704_, 0);
lean_inc_ref(v_expr_2792_);
lean_dec_ref(v_struct_2704_);
v___x_2793_ = l_Lean_Expr_cleanupAnnotations(v_snd_2791_);
if (lean_obj_tag(v_e_2701_) == 11)
{
lean_object* v_typeName_2794_; lean_object* v_idx_2795_; lean_object* v_struct_2796_; size_t v___x_2797_; size_t v___x_2798_; uint8_t v___x_2799_; 
v_typeName_2794_ = lean_ctor_get(v_e_2701_, 0);
v_idx_2795_ = lean_ctor_get(v_e_2701_, 1);
v_struct_2796_ = lean_ctor_get(v_e_2701_, 2);
v___x_2797_ = lean_ptr_addr(v_struct_2796_);
v___x_2798_ = lean_ptr_addr(v_expr_2792_);
v___x_2799_ = lean_usize_dec_eq(v___x_2797_, v___x_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
lean_inc(v_idx_2795_);
lean_inc(v_typeName_2794_);
lean_dec_ref_known(v_e_2701_, 3);
v___x_2800_ = l_Lean_Expr_proj___override(v_typeName_2794_, v_idx_2795_, v_expr_2792_);
v___y_2713_ = v___x_2793_;
v___y_2714_ = v___x_2800_;
goto v___jp_2712_;
}
else
{
lean_dec_ref(v_expr_2792_);
v___y_2713_ = v___x_2793_;
v___y_2714_ = v_e_2701_;
goto v___jp_2712_;
}
}
else
{
lean_object* v___x_2801_; lean_object* v___x_2802_; 
lean_dec_ref(v_expr_2792_);
lean_dec_ref(v_e_2701_);
v___x_2801_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2802_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2801_);
v___y_2713_ = v___x_2793_;
v___y_2714_ = v___x_2802_;
goto v___jp_2712_;
}
}
else
{
lean_object* v_a_2803_; lean_object* v___x_2805_; uint8_t v_isShared_2806_; uint8_t v_isSharedCheck_2810_; 
lean_dec_ref(v_struct_2704_);
lean_dec_ref(v_e_2701_);
v_a_2803_ = lean_ctor_get(v___x_2787_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2787_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2805_ = v___x_2787_;
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
else
{
lean_inc(v_a_2803_);
lean_dec(v___x_2787_);
v___x_2805_ = lean_box(0);
v_isShared_2806_ = v_isSharedCheck_2810_;
goto v_resetjp_2804_;
}
v_resetjp_2804_:
{
lean_object* v___x_2808_; 
if (v_isShared_2806_ == 0)
{
v___x_2808_ = v___x_2805_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_del_object(v___x_2761_);
lean_dec(v_a_2739_);
lean_dec(v_a_2737_);
lean_dec_ref(v_struct_2704_);
lean_dec(v_idx_2703_);
lean_dec(v_structName_2702_);
lean_dec_ref(v_e_2701_);
v_a_2812_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2781_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2781_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
v___jp_2820_:
{
lean_object* v_dummy_2827_; lean_object* v_nargs_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v_dummy_2827_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2828_ = l_Lean_Expr_getAppNumArgs(v_a_2737_);
lean_inc(v_nargs_2828_);
v___x_2829_ = lean_mk_array(v_nargs_2828_, v_dummy_2827_);
v___x_2830_ = lean_unsigned_to_nat(1u);
v___x_2831_ = lean_nat_sub(v_nargs_2828_, v___x_2830_);
lean_dec(v_nargs_2828_);
lean_inc(v_a_2737_);
v___x_2832_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2737_, v___x_2829_, v___x_2831_);
v___x_2833_ = lean_nat_add(v_numParams_2757_, v_numIndices_2758_);
lean_dec(v_numIndices_2758_);
v___x_2834_ = lean_array_get_size(v___x_2832_);
v___x_2835_ = lean_nat_dec_eq(v___x_2833_, v___x_2834_);
lean_dec(v___x_2833_);
if (v___x_2835_ == 0)
{
if (v___x_2723_ == 0)
{
v___y_2767_ = v___x_2832_;
v___y_2768_ = v___y_2821_;
v___y_2769_ = v___y_2822_;
v___y_2770_ = v___y_2823_;
v___y_2771_ = v___y_2824_;
v___y_2772_ = v___y_2825_;
v___y_2773_ = v___y_2826_;
goto v___jp_2766_;
}
else
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec_ref(v___x_2832_);
lean_dec_ref(v_val_2765_);
lean_del_object(v___x_2761_);
lean_dec(v_numParams_2757_);
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
v___x_2836_ = lean_box(0);
v___x_2837_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2704_, v_structName_2702_, v_idx_2703_, v_a_2737_, lean_box(0), v___x_2836_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
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
return v___x_2843_;
}
}
}
}
else
{
v___y_2767_ = v___x_2832_;
v___y_2768_ = v___y_2821_;
v___y_2769_ = v___y_2822_;
v___y_2770_ = v___y_2823_;
v___y_2771_ = v___y_2824_;
v___y_2772_ = v___y_2825_;
v___y_2773_ = v___y_2826_;
goto v___jp_2766_;
}
}
}
else
{
lean_object* v___x_2858_; lean_object* v___x_2859_; 
lean_dec(v_a_2764_);
lean_del_object(v___x_2761_);
lean_dec(v_numIndices_2758_);
lean_dec(v_numParams_2757_);
lean_dec_ref(v_toConstantVal_2756_);
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2704_, v_structName_2702_, v_idx_2703_, v_a_2737_, lean_box(0), v___x_2858_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2859_;
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_del_object(v___x_2761_);
lean_dec(v_numIndices_2758_);
lean_dec(v_numParams_2757_);
lean_dec_ref(v_toConstantVal_2756_);
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec(v_a_2737_);
lean_dec_ref(v_struct_2704_);
lean_dec(v_idx_2703_);
lean_dec(v_structName_2702_);
lean_dec_ref(v_e_2701_);
v_a_2860_ = lean_ctor_get(v___x_2763_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2763_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2763_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2754_, 2);
lean_dec_ref(v_val_2753_);
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
goto v___jp_2744_;
}
}
else
{
lean_dec(v_ctors_2754_);
lean_dec_ref(v_val_2753_);
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
goto v___jp_2744_;
}
}
else
{
lean_object* v___x_2870_; lean_object* v___x_2871_; 
lean_dec(v_val_2752_);
lean_dec(v_us_2742_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
v___x_2870_ = lean_box(0);
v___x_2871_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2704_, v_structName_2702_, v_idx_2703_, v_a_2737_, lean_box(0), v___x_2870_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2871_;
}
}
v___jp_2744_:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = lean_box(0);
v___x_2746_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2704_, v_structName_2702_, v_idx_2703_, v_a_2737_, lean_box(0), v___x_2745_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2746_;
}
}
else
{
lean_object* v___x_2872_; lean_object* v___x_2873_; 
lean_dec_ref(v___x_2740_);
lean_dec(v_a_2739_);
lean_dec_ref(v_e_2701_);
v___x_2872_ = lean_box(0);
v___x_2873_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2704_, v_structName_2702_, v_idx_2703_, v_a_2737_, lean_box(0), v___x_2872_, v_a_2705_, v_a_2706_, v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
return v___x_2873_;
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2737_);
lean_dec_ref(v_struct_2704_);
lean_dec(v_idx_2703_);
lean_dec(v_structName_2702_);
lean_dec_ref(v_e_2701_);
v_a_2874_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2738_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2738_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v_struct_2704_);
lean_dec(v_idx_2703_);
lean_dec(v_structName_2702_);
lean_dec_ref(v_e_2701_);
v_a_2882_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2736_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2736_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
else
{
lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec_ref(v_struct_2704_);
lean_dec(v_idx_2703_);
lean_dec(v_structName_2702_);
lean_dec_ref(v_e_2701_);
v_a_2890_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2734_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_dec(v___x_2734_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
v___jp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2715_, 0, v___y_2713_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___y_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2716_);
return v___x_2717_;
}
v___jp_2718_:
{
lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; 
v___x_2720_ = lean_box(0);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___y_2719_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2722_, 0, v___x_2721_);
return v___x_2722_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2898_, lean_object* v_structName_2899_, lean_object* v_idx_2900_, lean_object* v_struct_2901_, lean_object* v_a_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_, lean_object* v_a_2906_, lean_object* v_a_2907_, lean_object* v_a_2908_){
_start:
{
lean_object* v_res_2909_; 
v_res_2909_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2898_, v_structName_2899_, v_idx_2900_, v_struct_2901_, v_a_2902_, v_a_2903_, v_a_2904_, v_a_2905_, v_a_2906_, v_a_2907_);
lean_dec(v_a_2907_);
lean_dec_ref(v_a_2906_);
lean_dec(v_a_2905_);
lean_dec_ref(v_a_2904_);
lean_dec(v_a_2903_);
lean_dec(v_a_2902_);
return v_res_2909_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2910_, lean_object* v_struct_2911_, lean_object* v_structName_2912_, uint8_t v_a_2913_, lean_object* v_idx_2914_, lean_object* v_a_2915_, lean_object* v_inst_2916_, lean_object* v_R_2917_, lean_object* v_a_2918_, lean_object* v_b_2919_, lean_object* v_c_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_, lean_object* v___y_2923_, lean_object* v___y_2924_, lean_object* v___y_2925_, lean_object* v___y_2926_){
_start:
{
lean_object* v___x_2928_; 
v___x_2928_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2910_, v_struct_2911_, v_structName_2912_, v_a_2913_, v_idx_2914_, v_a_2915_, v_a_2918_, v_b_2919_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2929_ = _args[0];
lean_object* v_struct_2930_ = _args[1];
lean_object* v_structName_2931_ = _args[2];
lean_object* v_a_2932_ = _args[3];
lean_object* v_idx_2933_ = _args[4];
lean_object* v_a_2934_ = _args[5];
lean_object* v_inst_2935_ = _args[6];
lean_object* v_R_2936_ = _args[7];
lean_object* v_a_2937_ = _args[8];
lean_object* v_b_2938_ = _args[9];
lean_object* v_c_2939_ = _args[10];
lean_object* v___y_2940_ = _args[11];
lean_object* v___y_2941_ = _args[12];
lean_object* v___y_2942_ = _args[13];
lean_object* v___y_2943_ = _args[14];
lean_object* v___y_2944_ = _args[15];
lean_object* v___y_2945_ = _args[16];
lean_object* v___y_2946_ = _args[17];
_start:
{
uint8_t v_a_24143__boxed_2947_; lean_object* v_res_2948_; 
v_a_24143__boxed_2947_ = lean_unbox(v_a_2932_);
v_res_2948_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2929_, v_struct_2930_, v_structName_2931_, v_a_24143__boxed_2947_, v_idx_2933_, v_a_2934_, v_inst_2935_, v_R_2936_, v_a_2937_, v_b_2938_, v_c_2939_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
lean_dec(v___y_2945_);
lean_dec_ref(v___y_2944_);
lean_dec(v___y_2943_);
lean_dec_ref(v___y_2942_);
lean_dec(v___y_2941_);
lean_dec(v___y_2940_);
lean_dec(v_upperBound_2929_);
return v_res_2948_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2949_, size_t v_i_2950_, size_t v_stop_2951_, lean_object* v_b_2952_, lean_object* v___y_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_, lean_object* v___y_2956_, lean_object* v___y_2957_){
_start:
{
uint8_t v___x_2959_; 
v___x_2959_ = lean_usize_dec_eq(v_i_2950_, v_stop_2951_);
if (v___x_2959_ == 0)
{
size_t v___x_2960_; size_t v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2960_ = ((size_t)1ULL);
v___x_2961_ = lean_usize_sub(v_i_2950_, v___x_2960_);
v___x_2962_ = lean_array_uget_borrowed(v_as_2949_, v___x_2961_);
lean_inc(v___x_2962_);
v___x_2963_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2962_, v___y_2953_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v_a_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; 
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
lean_inc(v_a_2964_);
lean_dec_ref_known(v___x_2963_, 1);
v___x_2965_ = l_Lean_Expr_sortLevel_x21(v_a_2964_);
lean_dec(v_a_2964_);
v___x_2966_ = l_Lean_mkLevelIMax_x27(v___x_2965_, v_b_2952_);
v_i_2950_ = v___x_2961_;
v_b_2952_ = v___x_2966_;
goto _start;
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec(v_b_2952_);
v_a_2968_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2963_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2963_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_object* v___x_2976_; 
v___x_2976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2976_, 0, v_b_2952_);
return v___x_2976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_2977_, lean_object* v_i_2978_, lean_object* v_stop_2979_, lean_object* v_b_2980_, lean_object* v___y_2981_, lean_object* v___y_2982_, lean_object* v___y_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_){
_start:
{
size_t v_i_boxed_2987_; size_t v_stop_boxed_2988_; lean_object* v_res_2989_; 
v_i_boxed_2987_ = lean_unbox_usize(v_i_2978_);
lean_dec(v_i_2978_);
v_stop_boxed_2988_ = lean_unbox_usize(v_stop_2979_);
lean_dec(v_stop_2979_);
v_res_2989_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_2977_, v_i_boxed_2987_, v_stop_boxed_2988_, v_b_2980_, v___y_2981_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec(v___y_2983_);
lean_dec_ref(v___y_2982_);
lean_dec(v___y_2981_);
lean_dec_ref(v_as_2977_);
return v_res_2989_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2993_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_2994_ = lean_unsigned_to_nat(14u);
v___x_2995_ = lean_unsigned_to_nat(22u);
v___x_2996_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_2997_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_2998_ = l_mkPanicMessageWithDecl(v___x_2997_, v___x_2996_, v___x_2995_, v___x_2994_, v___x_2993_);
return v___x_2998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_2999_, lean_object* v_doms_3000_, lean_object* v_body_3001_, lean_object* v_a_3002_, lean_object* v_a_3003_, lean_object* v_a_3004_, lean_object* v_a_3005_, lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
lean_object* v_lctx_3009_; lean_object* v_expr_3010_; uint8_t v___x_3011_; uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v_a_3015_; uint8_t v___x_3020_; 
v_lctx_3009_ = lean_ctor_get(v_a_3004_, 2);
v_expr_3010_ = lean_ctor_get(v_body_3001_, 0);
v___x_3011_ = 1;
v___x_3012_ = 0;
lean_inc_ref(v_lctx_3009_);
v___x_3013_ = l_Lean_LocalContext_mkForall(v_lctx_3009_, v_fvars_2999_, v_expr_3010_, v___x_3011_, v___x_3012_);
v___x_3020_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3002_);
if (v___x_3020_ == 0)
{
lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3029_; 
v_isSharedCheck_3029_ = !lean_is_exclusive(v_body_3001_);
if (v_isSharedCheck_3029_ == 0)
{
lean_object* v_unused_3030_; lean_object* v_unused_3031_; 
v_unused_3030_ = lean_ctor_get(v_body_3001_, 1);
lean_dec(v_unused_3030_);
v_unused_3031_ = lean_ctor_get(v_body_3001_, 0);
lean_dec(v_unused_3031_);
v___x_3022_ = v_body_3001_;
v_isShared_3023_ = v_isSharedCheck_3029_;
goto v_resetjp_3021_;
}
else
{
lean_dec(v_body_3001_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3029_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
v___x_3024_ = lean_box(0);
if (v_isShared_3023_ == 0)
{
lean_ctor_set(v___x_3022_, 1, v___x_3024_);
lean_ctor_set(v___x_3022_, 0, v___x_3013_);
v___x_3026_ = v___x_3022_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v___x_3013_);
lean_ctor_set(v_reuseFailAlloc_3028_, 1, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; 
v___x_3027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
return v___x_3027_;
}
}
}
else
{
lean_object* v___x_3032_; 
v___x_3032_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_3001_, v_a_3002_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; lean_object* v___y_3035_; lean_object* v_type_x3f_3052_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v_type_x3f_3052_ = lean_ctor_get(v_a_3033_, 1);
lean_inc(v_type_x3f_3052_);
lean_dec(v_a_3033_);
if (lean_obj_tag(v_type_x3f_3052_) == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3054_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3053_);
v___y_3035_ = v___x_3054_;
goto v___jp_3034_;
}
else
{
lean_object* v_val_3055_; 
v_val_3055_ = lean_ctor_get(v_type_x3f_3052_, 0);
lean_inc(v_val_3055_);
lean_dec_ref_known(v_type_x3f_3052_, 1);
v___y_3035_ = v_val_3055_;
goto v___jp_3034_;
}
v___jp_3034_:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v___x_3036_ = l_Lean_Expr_sortLevel_x21(v___y_3035_);
lean_dec_ref(v___y_3035_);
v___x_3037_ = lean_array_get_size(v_doms_3000_);
v___x_3038_ = lean_unsigned_to_nat(0u);
v___x_3039_ = lean_nat_dec_lt(v___x_3038_, v___x_3037_);
if (v___x_3039_ == 0)
{
v_a_3015_ = v___x_3036_;
goto v___jp_3014_;
}
else
{
size_t v___x_3040_; size_t v___x_3041_; lean_object* v___x_3042_; 
v___x_3040_ = lean_usize_of_nat(v___x_3037_);
v___x_3041_ = ((size_t)0ULL);
v___x_3042_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_3000_, v___x_3040_, v___x_3041_, v___x_3036_, v_a_3003_, v_a_3004_, v_a_3005_, v_a_3006_, v_a_3007_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref_known(v___x_3042_, 1);
v_a_3015_ = v_a_3043_;
goto v___jp_3014_;
}
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref(v___x_3013_);
v_a_3044_ = lean_ctor_get(v___x_3042_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3042_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3042_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3042_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3013_);
return v___x_3032_;
}
}
v___jp_3014_:
{
lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3016_ = l_Lean_Expr_sort___override(v_a_3015_);
v___x_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3013_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3056_, lean_object* v_doms_3057_, lean_object* v_body_3058_, lean_object* v_a_3059_, lean_object* v_a_3060_, lean_object* v_a_3061_, lean_object* v_a_3062_, lean_object* v_a_3063_, lean_object* v_a_3064_, lean_object* v_a_3065_){
_start:
{
lean_object* v_res_3066_; 
v_res_3066_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3056_, v_doms_3057_, v_body_3058_, v_a_3059_, v_a_3060_, v_a_3061_, v_a_3062_, v_a_3063_, v_a_3064_);
lean_dec(v_a_3064_);
lean_dec_ref(v_a_3063_);
lean_dec(v_a_3062_);
lean_dec_ref(v_a_3061_);
lean_dec(v_a_3060_);
lean_dec(v_a_3059_);
lean_dec_ref(v_doms_3057_);
lean_dec_ref(v_fvars_3056_);
return v_res_3066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3067_, size_t v_i_3068_, size_t v_stop_3069_, lean_object* v_b_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3067_, v_i_3068_, v_stop_3069_, v_b_3070_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3079_, lean_object* v_i_3080_, lean_object* v_stop_3081_, lean_object* v_b_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_){
_start:
{
size_t v_i_boxed_3090_; size_t v_stop_boxed_3091_; lean_object* v_res_3092_; 
v_i_boxed_3090_ = lean_unbox_usize(v_i_3080_);
lean_dec(v_i_3080_);
v_stop_boxed_3091_ = lean_unbox_usize(v_stop_3081_);
lean_dec(v_stop_3081_);
v_res_3092_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3079_, v_i_boxed_3090_, v_stop_boxed_3091_, v_b_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_, v___y_3087_, v___y_3088_);
lean_dec(v___y_3088_);
lean_dec_ref(v___y_3087_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v_as_3079_);
return v_res_3092_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3093_, lean_object* v_opt_3094_){
_start:
{
lean_object* v_name_3095_; lean_object* v_defValue_3096_; lean_object* v_map_3097_; lean_object* v___x_3098_; 
v_name_3095_ = lean_ctor_get(v_opt_3094_, 0);
v_defValue_3096_ = lean_ctor_get(v_opt_3094_, 1);
v_map_3097_ = lean_ctor_get(v_opts_3093_, 0);
v___x_3098_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3097_, v_name_3095_);
if (lean_obj_tag(v___x_3098_) == 0)
{
uint8_t v___x_3099_; 
v___x_3099_ = lean_unbox(v_defValue_3096_);
return v___x_3099_;
}
else
{
lean_object* v_val_3100_; 
v_val_3100_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_val_3100_);
lean_dec_ref_known(v___x_3098_, 1);
if (lean_obj_tag(v_val_3100_) == 1)
{
uint8_t v_v_3101_; 
v_v_3101_ = lean_ctor_get_uint8(v_val_3100_, 0);
lean_dec_ref_known(v_val_3100_, 0);
return v_v_3101_;
}
else
{
uint8_t v___x_3102_; 
lean_dec(v_val_3100_);
v___x_3102_ = lean_unbox(v_defValue_3096_);
return v___x_3102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3103_, lean_object* v_opt_3104_){
_start:
{
uint8_t v_res_3105_; lean_object* v_r_3106_; 
v_res_3105_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3103_, v_opt_3104_);
lean_dec_ref(v_opt_3104_);
lean_dec_ref(v_opts_3103_);
v_r_3106_ = lean_box(v_res_3105_);
return v_r_3106_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_e_3107_){
_start:
{
if (lean_obj_tag(v_e_3107_) == 0)
{
uint8_t v___x_3108_; 
v___x_3108_ = 2;
return v___x_3108_;
}
else
{
uint8_t v___x_3109_; 
v___x_3109_ = 0;
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_e_3110_){
_start:
{
uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_e_3110_);
lean_dec_ref(v_e_3110_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(lean_object* v_x_3113_){
_start:
{
if (lean_obj_tag(v_x_3113_) == 0)
{
lean_object* v_a_3115_; lean_object* v___x_3117_; uint8_t v_isShared_3118_; uint8_t v_isSharedCheck_3122_; 
v_a_3115_ = lean_ctor_get(v_x_3113_, 0);
v_isSharedCheck_3122_ = !lean_is_exclusive(v_x_3113_);
if (v_isSharedCheck_3122_ == 0)
{
v___x_3117_ = v_x_3113_;
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
else
{
lean_inc(v_a_3115_);
lean_dec(v_x_3113_);
v___x_3117_ = lean_box(0);
v_isShared_3118_ = v_isSharedCheck_3122_;
goto v_resetjp_3116_;
}
v_resetjp_3116_:
{
lean_object* v___x_3120_; 
if (v_isShared_3118_ == 0)
{
lean_ctor_set_tag(v___x_3117_, 1);
v___x_3120_ = v___x_3117_;
goto v_reusejp_3119_;
}
else
{
lean_object* v_reuseFailAlloc_3121_; 
v_reuseFailAlloc_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3121_, 0, v_a_3115_);
v___x_3120_ = v_reuseFailAlloc_3121_;
goto v_reusejp_3119_;
}
v_reusejp_3119_:
{
return v___x_3120_;
}
}
}
else
{
lean_object* v_a_3123_; lean_object* v___x_3125_; uint8_t v_isShared_3126_; uint8_t v_isSharedCheck_3130_; 
v_a_3123_ = lean_ctor_get(v_x_3113_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v_x_3113_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3125_ = v_x_3113_;
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
else
{
lean_inc(v_a_3123_);
lean_dec(v_x_3113_);
v___x_3125_ = lean_box(0);
v_isShared_3126_ = v_isSharedCheck_3130_;
goto v_resetjp_3124_;
}
v_resetjp_3124_:
{
lean_object* v___x_3128_; 
if (v_isShared_3126_ == 0)
{
lean_ctor_set_tag(v___x_3125_, 0);
v___x_3128_ = v___x_3125_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v_a_3123_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg___boxed(lean_object* v_x_3131_, lean_object* v___y_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_x_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(size_t v_sz_3134_, size_t v_i_3135_, lean_object* v_bs_3136_){
_start:
{
uint8_t v___x_3137_; 
v___x_3137_ = lean_usize_dec_lt(v_i_3135_, v_sz_3134_);
if (v___x_3137_ == 0)
{
return v_bs_3136_;
}
else
{
lean_object* v_v_3138_; lean_object* v_msg_3139_; lean_object* v___x_3140_; lean_object* v_bs_x27_3141_; size_t v___x_3142_; size_t v___x_3143_; lean_object* v___x_3144_; 
v_v_3138_ = lean_array_uget_borrowed(v_bs_3136_, v_i_3135_);
v_msg_3139_ = lean_ctor_get(v_v_3138_, 1);
lean_inc_ref(v_msg_3139_);
v___x_3140_ = lean_unsigned_to_nat(0u);
v_bs_x27_3141_ = lean_array_uset(v_bs_3136_, v_i_3135_, v___x_3140_);
v___x_3142_ = ((size_t)1ULL);
v___x_3143_ = lean_usize_add(v_i_3135_, v___x_3142_);
v___x_3144_ = lean_array_uset(v_bs_x27_3141_, v_i_3135_, v_msg_3139_);
v_i_3135_ = v___x_3143_;
v_bs_3136_ = v___x_3144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16___boxed(lean_object* v_sz_3146_, lean_object* v_i_3147_, lean_object* v_bs_3148_){
_start:
{
size_t v_sz_boxed_3149_; size_t v_i_boxed_3150_; lean_object* v_res_3151_; 
v_sz_boxed_3149_ = lean_unbox_usize(v_sz_3146_);
lean_dec(v_sz_3146_);
v_i_boxed_3150_ = lean_unbox_usize(v_i_3147_);
lean_dec(v_i_3147_);
v_res_3151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(v_sz_boxed_3149_, v_i_boxed_3150_, v_bs_3148_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_oldTraces_3152_, lean_object* v_data_3153_, lean_object* v_ref_3154_, lean_object* v_msg_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_fileName_3161_; lean_object* v_fileMap_3162_; lean_object* v_options_3163_; lean_object* v_currRecDepth_3164_; lean_object* v_maxRecDepth_3165_; lean_object* v_ref_3166_; lean_object* v_currNamespace_3167_; lean_object* v_openDecls_3168_; lean_object* v_initHeartbeats_3169_; lean_object* v_maxHeartbeats_3170_; lean_object* v_quotContext_3171_; lean_object* v_currMacroScope_3172_; uint8_t v_diag_3173_; lean_object* v_cancelTk_x3f_3174_; uint8_t v_suppressElabErrors_3175_; lean_object* v_inheritedTraceOptions_3176_; lean_object* v___x_3177_; lean_object* v_traceState_3178_; lean_object* v_traces_3179_; lean_object* v_ref_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; size_t v_sz_3183_; size_t v___x_3184_; lean_object* v___x_3185_; lean_object* v_msg_3186_; lean_object* v___x_3187_; lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3225_; 
v_fileName_3161_ = lean_ctor_get(v___y_3158_, 0);
v_fileMap_3162_ = lean_ctor_get(v___y_3158_, 1);
v_options_3163_ = lean_ctor_get(v___y_3158_, 2);
v_currRecDepth_3164_ = lean_ctor_get(v___y_3158_, 3);
v_maxRecDepth_3165_ = lean_ctor_get(v___y_3158_, 4);
v_ref_3166_ = lean_ctor_get(v___y_3158_, 5);
v_currNamespace_3167_ = lean_ctor_get(v___y_3158_, 6);
v_openDecls_3168_ = lean_ctor_get(v___y_3158_, 7);
v_initHeartbeats_3169_ = lean_ctor_get(v___y_3158_, 8);
v_maxHeartbeats_3170_ = lean_ctor_get(v___y_3158_, 9);
v_quotContext_3171_ = lean_ctor_get(v___y_3158_, 10);
v_currMacroScope_3172_ = lean_ctor_get(v___y_3158_, 11);
v_diag_3173_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*14);
v_cancelTk_x3f_3174_ = lean_ctor_get(v___y_3158_, 12);
v_suppressElabErrors_3175_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3176_ = lean_ctor_get(v___y_3158_, 13);
v___x_3177_ = lean_st_ref_get(v___y_3159_);
v_traceState_3178_ = lean_ctor_get(v___x_3177_, 4);
lean_inc_ref(v_traceState_3178_);
lean_dec(v___x_3177_);
v_traces_3179_ = lean_ctor_get(v_traceState_3178_, 0);
lean_inc_ref(v_traces_3179_);
lean_dec_ref(v_traceState_3178_);
v_ref_3180_ = l_Lean_replaceRef(v_ref_3154_, v_ref_3166_);
lean_inc_ref(v_inheritedTraceOptions_3176_);
lean_inc(v_cancelTk_x3f_3174_);
lean_inc(v_currMacroScope_3172_);
lean_inc(v_quotContext_3171_);
lean_inc(v_maxHeartbeats_3170_);
lean_inc(v_initHeartbeats_3169_);
lean_inc(v_openDecls_3168_);
lean_inc(v_currNamespace_3167_);
lean_inc(v_maxRecDepth_3165_);
lean_inc(v_currRecDepth_3164_);
lean_inc_ref(v_options_3163_);
lean_inc_ref(v_fileMap_3162_);
lean_inc_ref(v_fileName_3161_);
v___x_3181_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3181_, 0, v_fileName_3161_);
lean_ctor_set(v___x_3181_, 1, v_fileMap_3162_);
lean_ctor_set(v___x_3181_, 2, v_options_3163_);
lean_ctor_set(v___x_3181_, 3, v_currRecDepth_3164_);
lean_ctor_set(v___x_3181_, 4, v_maxRecDepth_3165_);
lean_ctor_set(v___x_3181_, 5, v_ref_3180_);
lean_ctor_set(v___x_3181_, 6, v_currNamespace_3167_);
lean_ctor_set(v___x_3181_, 7, v_openDecls_3168_);
lean_ctor_set(v___x_3181_, 8, v_initHeartbeats_3169_);
lean_ctor_set(v___x_3181_, 9, v_maxHeartbeats_3170_);
lean_ctor_set(v___x_3181_, 10, v_quotContext_3171_);
lean_ctor_set(v___x_3181_, 11, v_currMacroScope_3172_);
lean_ctor_set(v___x_3181_, 12, v_cancelTk_x3f_3174_);
lean_ctor_set(v___x_3181_, 13, v_inheritedTraceOptions_3176_);
lean_ctor_set_uint8(v___x_3181_, sizeof(void*)*14, v_diag_3173_);
lean_ctor_set_uint8(v___x_3181_, sizeof(void*)*14 + 1, v_suppressElabErrors_3175_);
v___x_3182_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3179_);
lean_dec_ref(v_traces_3179_);
v_sz_3183_ = lean_array_size(v___x_3182_);
v___x_3184_ = ((size_t)0ULL);
v___x_3185_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(v_sz_3183_, v___x_3184_, v___x_3182_);
v_msg_3186_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3186_, 0, v_data_3153_);
lean_ctor_set(v_msg_3186_, 1, v_msg_3155_);
lean_ctor_set(v_msg_3186_, 2, v___x_3185_);
v___x_3187_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3186_, v___y_3156_, v___y_3157_, v___x_3181_, v___y_3159_);
lean_dec_ref_known(v___x_3181_, 14);
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3225_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3225_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3192_; lean_object* v_traceState_3193_; lean_object* v_env_3194_; lean_object* v_nextMacroScope_3195_; lean_object* v_ngen_3196_; lean_object* v_auxDeclNGen_3197_; lean_object* v_cache_3198_; lean_object* v_messages_3199_; lean_object* v_infoState_3200_; lean_object* v_snapshotTasks_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3224_; 
v___x_3192_ = lean_st_ref_take(v___y_3159_);
v_traceState_3193_ = lean_ctor_get(v___x_3192_, 4);
v_env_3194_ = lean_ctor_get(v___x_3192_, 0);
v_nextMacroScope_3195_ = lean_ctor_get(v___x_3192_, 1);
v_ngen_3196_ = lean_ctor_get(v___x_3192_, 2);
v_auxDeclNGen_3197_ = lean_ctor_get(v___x_3192_, 3);
v_cache_3198_ = lean_ctor_get(v___x_3192_, 5);
v_messages_3199_ = lean_ctor_get(v___x_3192_, 6);
v_infoState_3200_ = lean_ctor_get(v___x_3192_, 7);
v_snapshotTasks_3201_ = lean_ctor_get(v___x_3192_, 8);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3192_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3203_ = v___x_3192_;
v_isShared_3204_ = v_isSharedCheck_3224_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_snapshotTasks_3201_);
lean_inc(v_infoState_3200_);
lean_inc(v_messages_3199_);
lean_inc(v_cache_3198_);
lean_inc(v_traceState_3193_);
lean_inc(v_auxDeclNGen_3197_);
lean_inc(v_ngen_3196_);
lean_inc(v_nextMacroScope_3195_);
lean_inc(v_env_3194_);
lean_dec(v___x_3192_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3224_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
uint64_t v_tid_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3222_; 
v_tid_3205_ = lean_ctor_get_uint64(v_traceState_3193_, sizeof(void*)*1);
v_isSharedCheck_3222_ = !lean_is_exclusive(v_traceState_3193_);
if (v_isSharedCheck_3222_ == 0)
{
lean_object* v_unused_3223_; 
v_unused_3223_ = lean_ctor_get(v_traceState_3193_, 0);
lean_dec(v_unused_3223_);
v___x_3207_ = v_traceState_3193_;
v_isShared_3208_ = v_isSharedCheck_3222_;
goto v_resetjp_3206_;
}
else
{
lean_dec(v_traceState_3193_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3222_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; lean_object* v___x_3212_; 
v___x_3209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3209_, 0, v_ref_3154_);
lean_ctor_set(v___x_3209_, 1, v_a_3188_);
v___x_3210_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3152_, v___x_3209_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3210_);
v___x_3212_ = v___x_3207_;
goto v_reusejp_3211_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3210_);
lean_ctor_set_uint64(v_reuseFailAlloc_3221_, sizeof(void*)*1, v_tid_3205_);
v___x_3212_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3211_;
}
v_reusejp_3211_:
{
lean_object* v___x_3214_; 
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 4, v___x_3212_);
v___x_3214_ = v___x_3203_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_env_3194_);
lean_ctor_set(v_reuseFailAlloc_3220_, 1, v_nextMacroScope_3195_);
lean_ctor_set(v_reuseFailAlloc_3220_, 2, v_ngen_3196_);
lean_ctor_set(v_reuseFailAlloc_3220_, 3, v_auxDeclNGen_3197_);
lean_ctor_set(v_reuseFailAlloc_3220_, 4, v___x_3212_);
lean_ctor_set(v_reuseFailAlloc_3220_, 5, v_cache_3198_);
lean_ctor_set(v_reuseFailAlloc_3220_, 6, v_messages_3199_);
lean_ctor_set(v_reuseFailAlloc_3220_, 7, v_infoState_3200_);
lean_ctor_set(v_reuseFailAlloc_3220_, 8, v_snapshotTasks_3201_);
v___x_3214_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3218_; 
v___x_3215_ = lean_st_ref_set(v___y_3159_, v___x_3214_);
v___x_3216_ = lean_box(0);
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 0, v___x_3216_);
v___x_3218_ = v___x_3190_;
goto v_reusejp_3217_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v___x_3216_);
v___x_3218_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3217_;
}
v_reusejp_3217_:
{
return v___x_3218_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_oldTraces_3226_, lean_object* v_data_3227_, lean_object* v_ref_3228_, lean_object* v_msg_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v_res_3235_; 
v_res_3235_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_oldTraces_3226_, v_data_3227_, v_ref_3228_, v_msg_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
lean_dec(v___y_3233_);
lean_dec_ref(v___y_3232_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
return v_res_3235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3236_, lean_object* v_opt_3237_){
_start:
{
lean_object* v_name_3238_; lean_object* v_defValue_3239_; lean_object* v_map_3240_; lean_object* v___x_3241_; 
v_name_3238_ = lean_ctor_get(v_opt_3237_, 0);
v_defValue_3239_ = lean_ctor_get(v_opt_3237_, 1);
v_map_3240_ = lean_ctor_get(v_opts_3236_, 0);
v___x_3241_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3240_, v_name_3238_);
if (lean_obj_tag(v___x_3241_) == 0)
{
lean_inc(v_defValue_3239_);
return v_defValue_3239_;
}
else
{
lean_object* v_val_3242_; 
v_val_3242_ = lean_ctor_get(v___x_3241_, 0);
lean_inc(v_val_3242_);
lean_dec_ref_known(v___x_3241_, 1);
if (lean_obj_tag(v_val_3242_) == 3)
{
lean_object* v_v_3243_; 
v_v_3243_ = lean_ctor_get(v_val_3242_, 0);
lean_inc(v_v_3243_);
lean_dec_ref_known(v_val_3242_, 1);
return v_v_3243_;
}
else
{
lean_dec(v_val_3242_);
lean_inc(v_defValue_3239_);
return v_defValue_3239_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3244_, lean_object* v_opt_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3244_, v_opt_3245_);
lean_dec_ref(v_opt_3245_);
lean_dec_ref(v_opts_3244_);
return v_res_3246_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3248_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3249_ = l_Lean_stringToMessageData(v___x_3248_);
return v___x_3249_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4(void){
_start:
{
lean_object* v___x_3253_; double v___x_3254_; 
v___x_3253_ = lean_unsigned_to_nat(1000u);
v___x_3254_ = lean_float_of_nat(v___x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3255_, uint8_t v_collapsed_3256_, lean_object* v_tag_3257_, lean_object* v_opts_3258_, uint8_t v_clsEnabled_3259_, lean_object* v_oldTraces_3260_, lean_object* v_msg_3261_, lean_object* v_resStartStop_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_){
_start:
{
lean_object* v_fst_3270_; lean_object* v_snd_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3369_; 
v_fst_3270_ = lean_ctor_get(v_resStartStop_3262_, 0);
v_snd_3271_ = lean_ctor_get(v_resStartStop_3262_, 1);
v_isSharedCheck_3369_ = !lean_is_exclusive(v_resStartStop_3262_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3273_ = v_resStartStop_3262_;
v_isShared_3274_ = v_isSharedCheck_3369_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_snd_3271_);
lean_inc(v_fst_3270_);
lean_dec(v_resStartStop_3262_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3369_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v_data_3278_; lean_object* v_fst_3289_; lean_object* v_snd_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3368_; 
v_fst_3289_ = lean_ctor_get(v_snd_3271_, 0);
v_snd_3290_ = lean_ctor_get(v_snd_3271_, 1);
v_isSharedCheck_3368_ = !lean_is_exclusive(v_snd_3271_);
if (v_isSharedCheck_3368_ == 0)
{
v___x_3292_ = v_snd_3271_;
v_isShared_3293_ = v_isSharedCheck_3368_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_snd_3290_);
lean_inc(v_fst_3289_);
lean_dec(v_snd_3271_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3368_;
goto v_resetjp_3291_;
}
v___jp_3275_:
{
lean_object* v___x_3279_; 
lean_inc(v___y_3277_);
v___x_3279_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_oldTraces_3260_, v_data_3278_, v___y_3277_, v___y_3276_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_object* v___x_3280_; 
lean_dec_ref_known(v___x_3279_, 1);
v___x_3280_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_fst_3270_);
return v___x_3280_;
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_dec(v_fst_3270_);
v_a_3281_ = lean_ctor_get(v___x_3279_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3279_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3279_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3279_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
v_resetjp_3291_:
{
lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___y_3297_; lean_object* v_a_3298_; uint8_t v___y_3322_; double v___y_3353_; 
v___x_3294_ = l_Lean_trace_profiler;
v___x_3295_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3258_, v___x_3294_);
if (v___x_3295_ == 0)
{
v___y_3322_ = v___x_3295_;
goto v___jp_3321_;
}
else
{
lean_object* v___x_3358_; uint8_t v___x_3359_; 
v___x_3358_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3359_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3258_, v___x_3358_);
if (v___x_3359_ == 0)
{
lean_object* v___x_3360_; lean_object* v___x_3361_; double v___x_3362_; double v___x_3363_; double v___x_3364_; 
v___x_3360_ = l_Lean_trace_profiler_threshold;
v___x_3361_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3258_, v___x_3360_);
v___x_3362_ = lean_float_of_nat(v___x_3361_);
v___x_3363_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4);
v___x_3364_ = lean_float_div(v___x_3362_, v___x_3363_);
v___y_3353_ = v___x_3364_;
goto v___jp_3352_;
}
else
{
lean_object* v___x_3365_; lean_object* v___x_3366_; double v___x_3367_; 
v___x_3365_ = l_Lean_trace_profiler_threshold;
v___x_3366_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3258_, v___x_3365_);
v___x_3367_ = lean_float_of_nat(v___x_3366_);
v___y_3353_ = v___x_3367_;
goto v___jp_3352_;
}
}
v___jp_3296_:
{
uint8_t v_result_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3304_; 
v_result_3299_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_fst_3270_);
v___x_3300_ = l_Lean_TraceResult_toEmoji(v_result_3299_);
v___x_3301_ = l_Lean_stringToMessageData(v___x_3300_);
v___x_3302_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
if (v_isShared_3293_ == 0)
{
lean_ctor_set_tag(v___x_3292_, 7);
lean_ctor_set(v___x_3292_, 1, v___x_3302_);
lean_ctor_set(v___x_3292_, 0, v___x_3301_);
v___x_3304_ = v___x_3292_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___x_3302_);
v___x_3304_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
lean_object* v_m_3306_; 
if (v_isShared_3274_ == 0)
{
lean_ctor_set_tag(v___x_3273_, 7);
lean_ctor_set(v___x_3273_, 1, v_a_3298_);
lean_ctor_set(v___x_3273_, 0, v___x_3304_);
v_m_3306_ = v___x_3273_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3314_; 
v_reuseFailAlloc_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3314_, 0, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3314_, 1, v_a_3298_);
v_m_3306_ = v_reuseFailAlloc_3314_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; double v___x_3309_; lean_object* v_data_3310_; 
v___x_3307_ = lean_box(v_result_3299_);
v___x_3308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
v___x_3309_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3257_);
lean_inc_ref(v___x_3308_);
lean_inc(v_cls_3255_);
v_data_3310_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3310_, 0, v_cls_3255_);
lean_ctor_set(v_data_3310_, 1, v___x_3308_);
lean_ctor_set(v_data_3310_, 2, v_tag_3257_);
lean_ctor_set_float(v_data_3310_, sizeof(void*)*3, v___x_3309_);
lean_ctor_set_float(v_data_3310_, sizeof(void*)*3 + 8, v___x_3309_);
lean_ctor_set_uint8(v_data_3310_, sizeof(void*)*3 + 16, v_collapsed_3256_);
if (v___x_3295_ == 0)
{
lean_dec_ref_known(v___x_3308_, 1);
lean_dec(v_snd_3290_);
lean_dec(v_fst_3289_);
lean_dec_ref(v_tag_3257_);
lean_dec(v_cls_3255_);
v___y_3276_ = v_m_3306_;
v___y_3277_ = v___y_3297_;
v_data_3278_ = v_data_3310_;
goto v___jp_3275_;
}
else
{
lean_object* v_data_3311_; double v___x_3312_; double v___x_3313_; 
lean_dec_ref_known(v_data_3310_, 3);
v_data_3311_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3311_, 0, v_cls_3255_);
lean_ctor_set(v_data_3311_, 1, v___x_3308_);
lean_ctor_set(v_data_3311_, 2, v_tag_3257_);
v___x_3312_ = lean_unbox_float(v_fst_3289_);
lean_dec(v_fst_3289_);
lean_ctor_set_float(v_data_3311_, sizeof(void*)*3, v___x_3312_);
v___x_3313_ = lean_unbox_float(v_snd_3290_);
lean_dec(v_snd_3290_);
lean_ctor_set_float(v_data_3311_, sizeof(void*)*3 + 8, v___x_3313_);
lean_ctor_set_uint8(v_data_3311_, sizeof(void*)*3 + 16, v_collapsed_3256_);
v___y_3276_ = v_m_3306_;
v___y_3277_ = v___y_3297_;
v_data_3278_ = v_data_3311_;
goto v___jp_3275_;
}
}
}
}
v___jp_3316_:
{
lean_object* v_ref_3317_; lean_object* v___x_3318_; 
v_ref_3317_ = lean_ctor_get(v___y_3267_, 5);
lean_inc(v___y_3268_);
lean_inc_ref(v___y_3267_);
lean_inc(v___y_3266_);
lean_inc_ref(v___y_3265_);
lean_inc(v___y_3264_);
lean_inc(v___y_3263_);
lean_inc(v_fst_3270_);
v___x_3318_ = lean_apply_8(v_msg_3261_, v_fst_3270_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_, v___y_3268_, lean_box(0));
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
lean_inc(v_a_3319_);
lean_dec_ref_known(v___x_3318_, 1);
v___y_3297_ = v_ref_3317_;
v_a_3298_ = v_a_3319_;
goto v___jp_3296_;
}
else
{
lean_object* v___x_3320_; 
lean_dec_ref_known(v___x_3318_, 1);
v___x_3320_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3);
v___y_3297_ = v_ref_3317_;
v_a_3298_ = v___x_3320_;
goto v___jp_3296_;
}
}
v___jp_3321_:
{
if (v_clsEnabled_3259_ == 0)
{
if (v___y_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v_traceState_3324_; lean_object* v_env_3325_; lean_object* v_nextMacroScope_3326_; lean_object* v_ngen_3327_; lean_object* v_auxDeclNGen_3328_; lean_object* v_cache_3329_; lean_object* v_messages_3330_; lean_object* v_infoState_3331_; lean_object* v_snapshotTasks_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3351_; 
lean_del_object(v___x_3292_);
lean_dec(v_snd_3290_);
lean_dec(v_fst_3289_);
lean_del_object(v___x_3273_);
lean_dec_ref(v_msg_3261_);
lean_dec_ref(v_tag_3257_);
lean_dec(v_cls_3255_);
v___x_3323_ = lean_st_ref_take(v___y_3268_);
v_traceState_3324_ = lean_ctor_get(v___x_3323_, 4);
v_env_3325_ = lean_ctor_get(v___x_3323_, 0);
v_nextMacroScope_3326_ = lean_ctor_get(v___x_3323_, 1);
v_ngen_3327_ = lean_ctor_get(v___x_3323_, 2);
v_auxDeclNGen_3328_ = lean_ctor_get(v___x_3323_, 3);
v_cache_3329_ = lean_ctor_get(v___x_3323_, 5);
v_messages_3330_ = lean_ctor_get(v___x_3323_, 6);
v_infoState_3331_ = lean_ctor_get(v___x_3323_, 7);
v_snapshotTasks_3332_ = lean_ctor_get(v___x_3323_, 8);
v_isSharedCheck_3351_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3351_ == 0)
{
v___x_3334_ = v___x_3323_;
v_isShared_3335_ = v_isSharedCheck_3351_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_snapshotTasks_3332_);
lean_inc(v_infoState_3331_);
lean_inc(v_messages_3330_);
lean_inc(v_cache_3329_);
lean_inc(v_traceState_3324_);
lean_inc(v_auxDeclNGen_3328_);
lean_inc(v_ngen_3327_);
lean_inc(v_nextMacroScope_3326_);
lean_inc(v_env_3325_);
lean_dec(v___x_3323_);
v___x_3334_ = lean_box(0);
v_isShared_3335_ = v_isSharedCheck_3351_;
goto v_resetjp_3333_;
}
v_resetjp_3333_:
{
uint64_t v_tid_3336_; lean_object* v_traces_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3350_; 
v_tid_3336_ = lean_ctor_get_uint64(v_traceState_3324_, sizeof(void*)*1);
v_traces_3337_ = lean_ctor_get(v_traceState_3324_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v_traceState_3324_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3339_ = v_traceState_3324_;
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_traces_3337_);
lean_dec(v_traceState_3324_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3350_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3341_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3260_, v_traces_3337_);
lean_dec_ref(v_traces_3337_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3341_);
v___x_3343_ = v___x_3339_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v___x_3341_);
lean_ctor_set_uint64(v_reuseFailAlloc_3349_, sizeof(void*)*1, v_tid_3336_);
v___x_3343_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
lean_object* v___x_3345_; 
if (v_isShared_3335_ == 0)
{
lean_ctor_set(v___x_3334_, 4, v___x_3343_);
v___x_3345_ = v___x_3334_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_env_3325_);
lean_ctor_set(v_reuseFailAlloc_3348_, 1, v_nextMacroScope_3326_);
lean_ctor_set(v_reuseFailAlloc_3348_, 2, v_ngen_3327_);
lean_ctor_set(v_reuseFailAlloc_3348_, 3, v_auxDeclNGen_3328_);
lean_ctor_set(v_reuseFailAlloc_3348_, 4, v___x_3343_);
lean_ctor_set(v_reuseFailAlloc_3348_, 5, v_cache_3329_);
lean_ctor_set(v_reuseFailAlloc_3348_, 6, v_messages_3330_);
lean_ctor_set(v_reuseFailAlloc_3348_, 7, v_infoState_3331_);
lean_ctor_set(v_reuseFailAlloc_3348_, 8, v_snapshotTasks_3332_);
v___x_3345_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
lean_object* v___x_3346_; lean_object* v___x_3347_; 
v___x_3346_ = lean_st_ref_set(v___y_3268_, v___x_3345_);
v___x_3347_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_fst_3270_);
return v___x_3347_;
}
}
}
}
}
else
{
goto v___jp_3316_;
}
}
else
{
goto v___jp_3316_;
}
}
v___jp_3352_:
{
double v___x_3354_; double v___x_3355_; double v___x_3356_; uint8_t v___x_3357_; 
v___x_3354_ = lean_unbox_float(v_snd_3290_);
v___x_3355_ = lean_unbox_float(v_fst_3289_);
v___x_3356_ = lean_float_sub(v___x_3354_, v___x_3355_);
v___x_3357_ = lean_float_decLt(v___y_3353_, v___x_3356_);
v___y_3322_ = v___x_3357_;
goto v___jp_3321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3370_, lean_object* v_collapsed_3371_, lean_object* v_tag_3372_, lean_object* v_opts_3373_, lean_object* v_clsEnabled_3374_, lean_object* v_oldTraces_3375_, lean_object* v_msg_3376_, lean_object* v_resStartStop_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
uint8_t v_collapsed_boxed_3385_; uint8_t v_clsEnabled_boxed_3386_; lean_object* v_res_3387_; 
v_collapsed_boxed_3385_ = lean_unbox(v_collapsed_3371_);
v_clsEnabled_boxed_3386_ = lean_unbox(v_clsEnabled_3374_);
v_res_3387_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3370_, v_collapsed_boxed_3385_, v_tag_3372_, v_opts_3373_, v_clsEnabled_boxed_3386_, v_oldTraces_3375_, v_msg_3376_, v_resStartStop_3377_, v___y_3378_, v___y_3379_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
lean_dec(v___y_3381_);
lean_dec_ref(v___y_3380_);
lean_dec(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v_opts_3373_);
return v_res_3387_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3388_; lean_object* v___x_3389_; lean_object* v___x_3390_; 
v___x_3388_ = lean_unsigned_to_nat(32u);
v___x_3389_ = lean_mk_empty_array_with_capacity(v___x_3388_);
v___x_3390_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3390_, 0, v___x_3389_);
return v___x_3390_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3391_ = ((size_t)5ULL);
v___x_3392_ = lean_unsigned_to_nat(0u);
v___x_3393_ = lean_unsigned_to_nat(32u);
v___x_3394_ = lean_mk_empty_array_with_capacity(v___x_3393_);
v___x_3395_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3396_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
lean_ctor_set(v___x_3396_, 1, v___x_3394_);
lean_ctor_set(v___x_3396_, 2, v___x_3392_);
lean_ctor_set(v___x_3396_, 3, v___x_3392_);
lean_ctor_set_usize(v___x_3396_, 4, v___x_3391_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3397_){
_start:
{
lean_object* v___x_3399_; lean_object* v_traceState_3400_; lean_object* v_traces_3401_; lean_object* v___x_3402_; lean_object* v_traceState_3403_; lean_object* v_env_3404_; lean_object* v_nextMacroScope_3405_; lean_object* v_ngen_3406_; lean_object* v_auxDeclNGen_3407_; lean_object* v_cache_3408_; lean_object* v_messages_3409_; lean_object* v_infoState_3410_; lean_object* v_snapshotTasks_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3430_; 
v___x_3399_ = lean_st_ref_get(v___y_3397_);
v_traceState_3400_ = lean_ctor_get(v___x_3399_, 4);
lean_inc_ref(v_traceState_3400_);
lean_dec(v___x_3399_);
v_traces_3401_ = lean_ctor_get(v_traceState_3400_, 0);
lean_inc_ref(v_traces_3401_);
lean_dec_ref(v_traceState_3400_);
v___x_3402_ = lean_st_ref_take(v___y_3397_);
v_traceState_3403_ = lean_ctor_get(v___x_3402_, 4);
v_env_3404_ = lean_ctor_get(v___x_3402_, 0);
v_nextMacroScope_3405_ = lean_ctor_get(v___x_3402_, 1);
v_ngen_3406_ = lean_ctor_get(v___x_3402_, 2);
v_auxDeclNGen_3407_ = lean_ctor_get(v___x_3402_, 3);
v_cache_3408_ = lean_ctor_get(v___x_3402_, 5);
v_messages_3409_ = lean_ctor_get(v___x_3402_, 6);
v_infoState_3410_ = lean_ctor_get(v___x_3402_, 7);
v_snapshotTasks_3411_ = lean_ctor_get(v___x_3402_, 8);
v_isSharedCheck_3430_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3430_ == 0)
{
v___x_3413_ = v___x_3402_;
v_isShared_3414_ = v_isSharedCheck_3430_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_snapshotTasks_3411_);
lean_inc(v_infoState_3410_);
lean_inc(v_messages_3409_);
lean_inc(v_cache_3408_);
lean_inc(v_traceState_3403_);
lean_inc(v_auxDeclNGen_3407_);
lean_inc(v_ngen_3406_);
lean_inc(v_nextMacroScope_3405_);
lean_inc(v_env_3404_);
lean_dec(v___x_3402_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3430_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
uint64_t v_tid_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3428_; 
v_tid_3415_ = lean_ctor_get_uint64(v_traceState_3403_, sizeof(void*)*1);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_traceState_3403_);
if (v_isSharedCheck_3428_ == 0)
{
lean_object* v_unused_3429_; 
v_unused_3429_ = lean_ctor_get(v_traceState_3403_, 0);
lean_dec(v_unused_3429_);
v___x_3417_ = v_traceState_3403_;
v_isShared_3418_ = v_isSharedCheck_3428_;
goto v_resetjp_3416_;
}
else
{
lean_dec(v_traceState_3403_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3428_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3419_; lean_object* v___x_3421_; 
v___x_3419_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3418_ == 0)
{
lean_ctor_set(v___x_3417_, 0, v___x_3419_);
v___x_3421_ = v___x_3417_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3427_; 
v_reuseFailAlloc_3427_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3427_, 0, v___x_3419_);
lean_ctor_set_uint64(v_reuseFailAlloc_3427_, sizeof(void*)*1, v_tid_3415_);
v___x_3421_ = v_reuseFailAlloc_3427_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
lean_object* v___x_3423_; 
if (v_isShared_3414_ == 0)
{
lean_ctor_set(v___x_3413_, 4, v___x_3421_);
v___x_3423_ = v___x_3413_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_env_3404_);
lean_ctor_set(v_reuseFailAlloc_3426_, 1, v_nextMacroScope_3405_);
lean_ctor_set(v_reuseFailAlloc_3426_, 2, v_ngen_3406_);
lean_ctor_set(v_reuseFailAlloc_3426_, 3, v_auxDeclNGen_3407_);
lean_ctor_set(v_reuseFailAlloc_3426_, 4, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3426_, 5, v_cache_3408_);
lean_ctor_set(v_reuseFailAlloc_3426_, 6, v_messages_3409_);
lean_ctor_set(v_reuseFailAlloc_3426_, 7, v_infoState_3410_);
lean_ctor_set(v_reuseFailAlloc_3426_, 8, v_snapshotTasks_3411_);
v___x_3423_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
lean_object* v___x_3424_; lean_object* v___x_3425_; 
v___x_3424_ = lean_st_ref_set(v___y_3397_, v___x_3423_);
v___x_3425_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3425_, 0, v_traces_3401_);
return v___x_3425_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3431_, lean_object* v___y_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3431_);
lean_dec(v___y_3431_);
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___x_3442_; 
lean_inc(v___y_3436_);
lean_inc(v___y_3435_);
v___x_3442_ = lean_apply_7(v_x_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, lean_box(0));
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
lean_dec(v___y_3445_);
lean_dec(v___y_3444_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3452_, lean_object* v_localInsts_3453_, lean_object* v_x_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v___f_3462_; lean_object* v___x_3463_; 
lean_inc(v___y_3456_);
lean_inc(v___y_3455_);
v___f_3462_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3462_, 0, v_x_3454_);
lean_closure_set(v___f_3462_, 1, v___y_3455_);
lean_closure_set(v___f_3462_, 2, v___y_3456_);
v___x_3463_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3452_, v_localInsts_3453_, v___f_3462_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
if (lean_obj_tag(v___x_3463_) == 0)
{
return v___x_3463_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
v_a_3464_ = lean_ctor_get(v___x_3463_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3463_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3463_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3463_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3472_, lean_object* v_localInsts_3473_, lean_object* v_x_3474_, lean_object* v___y_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_){
_start:
{
lean_object* v_res_3482_; 
v_res_3482_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3472_, v_localInsts_3473_, v_x_3474_, v___y_3475_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
lean_dec(v___y_3480_);
lean_dec_ref(v___y_3479_);
lean_dec(v___y_3478_);
lean_dec_ref(v___y_3477_);
lean_dec(v___y_3476_);
lean_dec(v___y_3475_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3483_){
_start:
{
lean_object* v___x_3485_; lean_object* v_ngen_3486_; lean_object* v_namePrefix_3487_; lean_object* v_idx_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3517_; 
v___x_3485_ = lean_st_ref_get(v___y_3483_);
v_ngen_3486_ = lean_ctor_get(v___x_3485_, 2);
lean_inc_ref(v_ngen_3486_);
lean_dec(v___x_3485_);
v_namePrefix_3487_ = lean_ctor_get(v_ngen_3486_, 0);
v_idx_3488_ = lean_ctor_get(v_ngen_3486_, 1);
v_isSharedCheck_3517_ = !lean_is_exclusive(v_ngen_3486_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3490_ = v_ngen_3486_;
v_isShared_3491_ = v_isSharedCheck_3517_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_idx_3488_);
lean_inc(v_namePrefix_3487_);
lean_dec(v_ngen_3486_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3517_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3492_; lean_object* v_env_3493_; lean_object* v_nextMacroScope_3494_; lean_object* v_auxDeclNGen_3495_; lean_object* v_traceState_3496_; lean_object* v_cache_3497_; lean_object* v_messages_3498_; lean_object* v_infoState_3499_; lean_object* v_snapshotTasks_3500_; lean_object* v___x_3502_; uint8_t v_isShared_3503_; uint8_t v_isSharedCheck_3515_; 
v___x_3492_ = lean_st_ref_take(v___y_3483_);
v_env_3493_ = lean_ctor_get(v___x_3492_, 0);
v_nextMacroScope_3494_ = lean_ctor_get(v___x_3492_, 1);
v_auxDeclNGen_3495_ = lean_ctor_get(v___x_3492_, 3);
v_traceState_3496_ = lean_ctor_get(v___x_3492_, 4);
v_cache_3497_ = lean_ctor_get(v___x_3492_, 5);
v_messages_3498_ = lean_ctor_get(v___x_3492_, 6);
v_infoState_3499_ = lean_ctor_get(v___x_3492_, 7);
v_snapshotTasks_3500_ = lean_ctor_get(v___x_3492_, 8);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; 
v_unused_3516_ = lean_ctor_get(v___x_3492_, 2);
lean_dec(v_unused_3516_);
v___x_3502_ = v___x_3492_;
v_isShared_3503_ = v_isSharedCheck_3515_;
goto v_resetjp_3501_;
}
else
{
lean_inc(v_snapshotTasks_3500_);
lean_inc(v_infoState_3499_);
lean_inc(v_messages_3498_);
lean_inc(v_cache_3497_);
lean_inc(v_traceState_3496_);
lean_inc(v_auxDeclNGen_3495_);
lean_inc(v_nextMacroScope_3494_);
lean_inc(v_env_3493_);
lean_dec(v___x_3492_);
v___x_3502_ = lean_box(0);
v_isShared_3503_ = v_isSharedCheck_3515_;
goto v_resetjp_3501_;
}
v_resetjp_3501_:
{
lean_object* v_r_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___x_3508_; 
lean_inc(v_idx_3488_);
lean_inc(v_namePrefix_3487_);
v_r_3504_ = l_Lean_Name_num___override(v_namePrefix_3487_, v_idx_3488_);
v___x_3505_ = lean_unsigned_to_nat(1u);
v___x_3506_ = lean_nat_add(v_idx_3488_, v___x_3505_);
lean_dec(v_idx_3488_);
if (v_isShared_3491_ == 0)
{
lean_ctor_set(v___x_3490_, 1, v___x_3506_);
v___x_3508_ = v___x_3490_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v_namePrefix_3487_);
lean_ctor_set(v_reuseFailAlloc_3514_, 1, v___x_3506_);
v___x_3508_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
lean_object* v___x_3510_; 
if (v_isShared_3503_ == 0)
{
lean_ctor_set(v___x_3502_, 2, v___x_3508_);
v___x_3510_ = v___x_3502_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_env_3493_);
lean_ctor_set(v_reuseFailAlloc_3513_, 1, v_nextMacroScope_3494_);
lean_ctor_set(v_reuseFailAlloc_3513_, 2, v___x_3508_);
lean_ctor_set(v_reuseFailAlloc_3513_, 3, v_auxDeclNGen_3495_);
lean_ctor_set(v_reuseFailAlloc_3513_, 4, v_traceState_3496_);
lean_ctor_set(v_reuseFailAlloc_3513_, 5, v_cache_3497_);
lean_ctor_set(v_reuseFailAlloc_3513_, 6, v_messages_3498_);
lean_ctor_set(v_reuseFailAlloc_3513_, 7, v_infoState_3499_);
lean_ctor_set(v_reuseFailAlloc_3513_, 8, v_snapshotTasks_3500_);
v___x_3510_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3511_ = lean_st_ref_set(v___y_3483_, v___x_3510_);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v_r_3504_);
return v___x_3512_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3518_, lean_object* v___y_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3518_);
lean_dec(v___y_3518_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_){
_start:
{
lean_object* v___x_3528_; lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
v___x_3528_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3526_);
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
lean_object* v_res_3544_; 
v_res_3544_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3537_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
lean_dec(v___y_3538_);
lean_dec(v___y_3537_);
return v_res_3544_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; 
v___x_3546_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3547_ = l_Lean_stringToMessageData(v___x_3546_);
return v___x_3547_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; 
v___x_3549_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3550_ = l_Lean_stringToMessageData(v___x_3549_);
return v___x_3550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3553_, lean_object* v_x_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
lean_object* v___x_3562_; lean_object* v___y_3564_; uint8_t v___x_3573_; 
v___x_3562_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3573_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3555_);
if (v___x_3573_ == 0)
{
lean_object* v___x_3574_; 
v___x_3574_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3564_ = v___x_3574_;
goto v___jp_3563_;
}
else
{
lean_object* v___x_3575_; 
v___x_3575_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3564_ = v___x_3575_;
goto v___jp_3563_;
}
v___jp_3563_:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
lean_inc_ref(v___y_3564_);
v___x_3565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3565_, 0, v___y_3564_);
v___x_3566_ = l_Lean_MessageData_ofFormat(v___x_3565_);
v___x_3567_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3562_);
lean_ctor_set(v___x_3567_, 1, v___x_3566_);
v___x_3568_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3569_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3569_, 0, v___x_3567_);
lean_ctor_set(v___x_3569_, 1, v___x_3568_);
v___x_3570_ = l_Lean_indentExpr(v_e_3553_);
v___x_3571_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3571_, 0, v___x_3569_);
lean_ctor_set(v___x_3571_, 1, v___x_3570_);
v___x_3572_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3572_, 0, v___x_3571_);
return v___x_3572_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3576_, lean_object* v_x_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
lean_object* v_res_3585_; 
v_res_3585_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3576_, v_x_3577_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v___y_3579_);
lean_dec(v___y_3578_);
lean_dec_ref(v_x_3577_);
return v_res_3585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3586_, lean_object* v_x_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v_keyedConfig_3595_; uint8_t v_trackZetaDelta_3596_; lean_object* v_zetaDeltaSet_3597_; lean_object* v_localInstances_3598_; lean_object* v_defEqCtx_x3f_3599_; lean_object* v_synthPendingDepth_3600_; lean_object* v_canUnfold_x3f_3601_; uint8_t v_univApprox_3602_; uint8_t v_inTypeClassResolution_3603_; uint8_t v_cacheInferType_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v_keyedConfig_3595_ = lean_ctor_get(v___y_3590_, 0);
v_trackZetaDelta_3596_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7);
v_zetaDeltaSet_3597_ = lean_ctor_get(v___y_3590_, 1);
v_localInstances_3598_ = lean_ctor_get(v___y_3590_, 3);
v_defEqCtx_x3f_3599_ = lean_ctor_get(v___y_3590_, 4);
v_synthPendingDepth_3600_ = lean_ctor_get(v___y_3590_, 5);
v_canUnfold_x3f_3601_ = lean_ctor_get(v___y_3590_, 6);
v_univApprox_3602_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3603_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7 + 2);
v_cacheInferType_3604_ = lean_ctor_get_uint8(v___y_3590_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_3601_);
lean_inc(v_synthPendingDepth_3600_);
lean_inc(v_defEqCtx_x3f_3599_);
lean_inc_ref(v_localInstances_3598_);
lean_inc(v_zetaDeltaSet_3597_);
lean_inc_ref(v_keyedConfig_3595_);
v___x_3605_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3605_, 0, v_keyedConfig_3595_);
lean_ctor_set(v___x_3605_, 1, v_zetaDeltaSet_3597_);
lean_ctor_set(v___x_3605_, 2, v_lctx_3586_);
lean_ctor_set(v___x_3605_, 3, v_localInstances_3598_);
lean_ctor_set(v___x_3605_, 4, v_defEqCtx_x3f_3599_);
lean_ctor_set(v___x_3605_, 5, v_synthPendingDepth_3600_);
lean_ctor_set(v___x_3605_, 6, v_canUnfold_x3f_3601_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*7, v_trackZetaDelta_3596_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*7 + 1, v_univApprox_3602_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3603_);
lean_ctor_set_uint8(v___x_3605_, sizeof(void*)*7 + 3, v_cacheInferType_3604_);
lean_inc(v___y_3593_);
lean_inc_ref(v___y_3592_);
lean_inc(v___y_3591_);
lean_inc(v___y_3589_);
lean_inc(v___y_3588_);
v___x_3606_ = lean_apply_7(v_x_3587_, v___y_3588_, v___y_3589_, v___x_3605_, v___y_3591_, v___y_3592_, v___y_3593_, lean_box(0));
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3614_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3614_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3614_ == 0)
{
v___x_3609_ = v___x_3606_;
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_a_3607_);
lean_dec(v___x_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3614_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3612_; 
if (v_isShared_3610_ == 0)
{
v___x_3612_ = v___x_3609_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
else
{
return v___x_3606_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3615_, lean_object* v_x_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3615_, v_x_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec(v___y_3617_);
return v_res_3624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3627_, lean_object* v_letFVars_3628_, lean_object* v_lctx_3629_, lean_object* v_v_3630_, lean_object* v_e_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; 
v___x_3639_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3640_ = lean_expr_instantiate_rev(v_e_3631_, v_fvars_3627_);
v___x_3641_ = lean_apply_1(v_v_3630_, v___x_3640_);
v___x_3642_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3642_, 0, lean_box(0));
lean_closure_set(v___x_3642_, 1, v_letFVars_3628_);
lean_closure_set(v___x_3642_, 2, v___x_3641_);
v___x_3643_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3629_, v___x_3639_, v___x_3642_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
return v___x_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3644_, lean_object* v_letFVars_3645_, lean_object* v_lctx_3646_, lean_object* v_v_3647_, lean_object* v_e_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_){
_start:
{
lean_object* v_res_3656_; 
v_res_3656_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3644_, v_letFVars_3645_, v_lctx_3646_, v_v_3647_, v_e_3648_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
lean_dec(v___y_3654_);
lean_dec_ref(v___y_3653_);
lean_dec(v___y_3652_);
lean_dec_ref(v___y_3651_);
lean_dec(v___y_3650_);
lean_dec(v___y_3649_);
lean_dec_ref(v_e_3648_);
lean_dec_ref(v_fvars_3644_);
return v_res_3656_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3658_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3659_ = l_Lean_stringToMessageData(v___x_3658_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3660_, lean_object* v_a_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_){
_start:
{
lean_object* v___x_3669_; 
lean_inc_ref(v_a_3660_);
v___x_3669_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3660_, v___y_3663_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v_expr_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3721_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
v_expr_3671_ = lean_ctor_get(v_a_3661_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_a_3661_);
if (v_isSharedCheck_3721_ == 0)
{
lean_object* v_unused_3722_; 
v_unused_3722_ = lean_ctor_get(v_a_3661_, 1);
lean_dec(v_unused_3722_);
v___x_3673_ = v_a_3661_;
v_isShared_3674_ = v_isSharedCheck_3721_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_expr_3671_);
lean_dec(v_a_3661_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3721_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; 
lean_inc(v_a_3670_);
lean_inc_ref(v_expr_3671_);
v___x_3675_ = l_Lean_Meta_isExprDefEq(v_expr_3671_, v_a_3670_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3712_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3712_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3712_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
uint8_t v___x_3680_; 
v___x_3680_ = lean_unbox(v_a_3676_);
lean_dec(v_a_3676_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3683_; 
lean_del_object(v___x_3678_);
v___x_3681_ = lean_box(0);
v___x_3682_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3683_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3670_, v_expr_3671_, v___x_3681_, v___x_3682_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v_a_3684_; lean_object* v_expr_3685_; lean_object* v___x_3687_; uint8_t v_isShared_3688_; uint8_t v_isSharedCheck_3698_; 
v_a_3684_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_a_3684_);
lean_dec_ref_known(v___x_3683_, 1);
v_expr_3685_ = lean_ctor_get(v_a_3660_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v_a_3660_);
if (v_isSharedCheck_3698_ == 0)
{
lean_object* v_unused_3699_; 
v_unused_3699_ = lean_ctor_get(v_a_3660_, 1);
lean_dec(v_unused_3699_);
v___x_3687_ = v_a_3660_;
v_isShared_3688_ = v_isSharedCheck_3698_;
goto v_resetjp_3686_;
}
else
{
lean_inc(v_expr_3685_);
lean_dec(v_a_3660_);
v___x_3687_ = lean_box(0);
v_isShared_3688_ = v_isSharedCheck_3698_;
goto v_resetjp_3686_;
}
v_resetjp_3686_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3689_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3690_ = l_Lean_indentExpr(v_expr_3685_);
if (v_isShared_3688_ == 0)
{
lean_ctor_set_tag(v___x_3687_, 7);
lean_ctor_set(v___x_3687_, 1, v___x_3690_);
lean_ctor_set(v___x_3687_, 0, v___x_3689_);
v___x_3692_ = v___x_3687_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3697_, 1, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3694_; 
if (v_isShared_3674_ == 0)
{
lean_ctor_set_tag(v___x_3673_, 7);
lean_ctor_set(v___x_3673_, 1, v_a_3684_);
lean_ctor_set(v___x_3673_, 0, v___x_3692_);
v___x_3694_ = v___x_3673_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3692_);
lean_ctor_set(v_reuseFailAlloc_3696_, 1, v_a_3684_);
v___x_3694_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3694_, v___y_3664_, v___y_3665_, v___y_3666_, v___y_3667_);
return v___x_3695_;
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_del_object(v___x_3673_);
lean_dec_ref(v_a_3660_);
v_a_3700_ = lean_ctor_get(v___x_3683_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3683_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3683_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3683_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
else
{
lean_object* v___x_3708_; lean_object* v___x_3710_; 
lean_del_object(v___x_3673_);
lean_dec_ref(v_expr_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3660_);
v___x_3708_ = lean_box(0);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3708_);
v___x_3710_ = v___x_3678_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v___x_3708_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_del_object(v___x_3673_);
lean_dec_ref(v_expr_3671_);
lean_dec(v_a_3670_);
lean_dec_ref(v_a_3660_);
v_a_3713_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3675_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3675_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v_a_3661_);
lean_dec_ref(v_a_3660_);
v_a_3723_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3669_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3669_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3731_, lean_object* v_a_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_){
_start:
{
lean_object* v_res_3740_; 
v_res_3740_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3731_, v_a_3732_, v___y_3733_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_, v___y_3738_);
lean_dec(v___y_3738_);
lean_dec_ref(v___y_3737_);
lean_dec(v___y_3736_);
lean_dec_ref(v___y_3735_);
lean_dec(v___y_3734_);
lean_dec(v___y_3733_);
return v_res_3740_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3743_ = l_Lean_stringToMessageData(v___x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3744_, lean_object* v_a_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_, lean_object* v_a_3749_, lean_object* v_a_3750_){
_start:
{
if (lean_obj_tag(v_e_3744_) == 5)
{
lean_object* v_fn_3752_; lean_object* v_arg_3753_; lean_object* v___x_3754_; 
v_fn_3752_ = lean_ctor_get(v_e_3744_, 0);
v_arg_3753_ = lean_ctor_get(v_e_3744_, 1);
lean_inc_ref(v_fn_3752_);
v___x_3754_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3752_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
lean_inc_ref(v_arg_3753_);
v___x_3756_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3753_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3777_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3777_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3777_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_expr_3761_; uint8_t v___y_3763_; size_t v___x_3771_; size_t v___x_3772_; uint8_t v___x_3773_; 
v_expr_3761_ = lean_ctor_get(v_a_3757_, 0);
lean_inc_ref(v_expr_3761_);
lean_dec(v_a_3757_);
v___x_3771_ = lean_ptr_addr(v_fn_3752_);
v___x_3772_ = lean_ptr_addr(v_a_3755_);
v___x_3773_ = lean_usize_dec_eq(v___x_3771_, v___x_3772_);
if (v___x_3773_ == 0)
{
v___y_3763_ = v___x_3773_;
goto v___jp_3762_;
}
else
{
size_t v___x_3774_; size_t v___x_3775_; uint8_t v___x_3776_; 
v___x_3774_ = lean_ptr_addr(v_arg_3753_);
v___x_3775_ = lean_ptr_addr(v_expr_3761_);
v___x_3776_ = lean_usize_dec_eq(v___x_3774_, v___x_3775_);
v___y_3763_ = v___x_3776_;
goto v___jp_3762_;
}
v___jp_3762_:
{
if (v___y_3763_ == 0)
{
lean_object* v___x_3764_; lean_object* v___x_3766_; 
lean_dec_ref_known(v_e_3744_, 2);
v___x_3764_ = l_Lean_Expr_app___override(v_a_3755_, v_expr_3761_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3764_);
v___x_3766_ = v___x_3759_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
else
{
lean_object* v___x_3769_; 
lean_dec_ref(v_expr_3761_);
lean_dec(v_a_3755_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_e_3744_);
v___x_3769_ = v___x_3759_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_e_3744_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
}
else
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
lean_dec(v_a_3755_);
lean_dec_ref_known(v_e_3744_, 2);
v_a_3778_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3780_ = v___x_3756_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3756_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3778_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3744_, 2);
return v___x_3754_;
}
}
else
{
lean_object* v___x_3786_; 
v___x_3786_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3744_, v_a_3745_, v_a_3746_, v_a_3747_, v_a_3748_, v_a_3749_, v_a_3750_);
if (lean_obj_tag(v___x_3786_) == 0)
{
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3795_; 
v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3789_ = v___x_3786_;
v_isShared_3790_ = v_isSharedCheck_3795_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3795_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v_expr_3791_; lean_object* v___x_3793_; 
v_expr_3791_ = lean_ctor_get(v_a_3787_, 0);
lean_inc_ref(v_expr_3791_);
lean_dec(v_a_3787_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v_expr_3791_);
v___x_3793_ = v___x_3789_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_expr_3791_);
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
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
v_a_3796_ = lean_ctor_get(v___x_3786_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3786_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3786_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
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
return v___x_3801_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
lean_object* v_res_3812_; 
v_res_3812_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3804_, v_a_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_);
lean_dec(v_a_3810_);
lean_dec_ref(v_a_3809_);
lean_dec(v_a_3808_);
lean_dec_ref(v_a_3807_);
lean_dec(v_a_3806_);
lean_dec(v_a_3805_);
return v_res_3812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
if (lean_obj_tag(v_e_3813_) == 5)
{
lean_object* v_fn_3821_; lean_object* v_arg_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_fn_3821_ = lean_ctor_get(v_e_3813_, 0);
v_arg_3822_ = lean_ctor_get(v_e_3813_, 1);
lean_inc_ref_n(v_fn_3821_, 2);
v___x_3823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3823_, 0, v_fn_3821_);
v___x_3824_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3821_, v___x_3823_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v_a_3825_; lean_object* v___x_3826_; 
v_a_3825_ = lean_ctor_get(v___x_3824_, 0);
lean_inc(v_a_3825_);
lean_dec_ref_known(v___x_3824_, 1);
lean_inc_ref(v_arg_3822_);
v___x_3826_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3822_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3828_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v___x_3828_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3813_, v_a_3825_, v_a_3827_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
return v___x_3828_;
}
else
{
lean_dec(v_a_3825_);
lean_dec_ref_known(v_e_3813_, 2);
return v___x_3826_;
}
}
else
{
lean_dec_ref_known(v_e_3813_, 2);
return v___x_3824_;
}
}
else
{
lean_object* v___x_3829_; 
v___x_3829_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_);
return v___x_3829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3830_, lean_object* v_a_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_, lean_object* v_a_3836_){
_start:
{
uint8_t v___x_3838_; 
v___x_3838_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3831_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; 
v___x_3839_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
if (lean_obj_tag(v___x_3839_) == 0)
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3849_; 
v_a_3840_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3842_ = v___x_3839_;
v_isShared_3843_ = v_isSharedCheck_3849_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3839_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3849_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3844_ = lean_box(0);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v_a_3840_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3845_);
v___x_3847_ = v___x_3842_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
v_a_3850_ = lean_ctor_get(v___x_3839_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3839_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3839_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3839_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
else
{
lean_object* v___x_3858_; 
v___x_3858_ = l_Lean_Expr_getAppFn(v_e_3830_);
if (lean_obj_tag(v___x_3858_) == 2)
{
lean_object* v_mvarId_3859_; lean_object* v_dummy_3860_; lean_object* v_nargs_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; 
v_mvarId_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_mvarId_3859_);
lean_dec_ref_known(v___x_3858_, 1);
v_dummy_3860_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3861_ = l_Lean_Expr_getAppNumArgs(v_e_3830_);
lean_inc(v_nargs_3861_);
v___x_3862_ = lean_mk_array(v_nargs_3861_, v_dummy_3860_);
v___x_3863_ = lean_unsigned_to_nat(1u);
v___x_3864_ = lean_nat_sub(v_nargs_3861_, v___x_3863_);
lean_dec(v_nargs_3861_);
lean_inc_ref(v_e_3830_);
v___x_3865_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3830_, v___x_3862_, v___x_3864_);
v___x_3866_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3859_, v___x_3865_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
lean_dec(v_mvarId_3859_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v___x_3867_; 
lean_dec_ref_known(v___x_3866_, 1);
v___x_3867_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
return v___x_3867_;
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3875_; 
lean_dec_ref(v_e_3830_);
v_a_3868_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3875_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3875_ == 0)
{
v___x_3870_ = v___x_3866_;
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3866_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3875_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v___x_3873_; 
if (v_isShared_3871_ == 0)
{
v___x_3873_ = v___x_3870_;
goto v_reusejp_3872_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v_a_3868_);
v___x_3873_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3872_;
}
v_reusejp_3872_:
{
return v___x_3873_;
}
}
}
}
else
{
lean_object* v___x_3876_; 
lean_dec_ref(v___x_3858_);
v___x_3876_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3830_, v_a_3831_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_, v_a_3836_);
return v___x_3876_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec(v_a_3878_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3886_, lean_object* v_a_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3886_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3896_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___x_3896_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3895_, v_a_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_);
return v___x_3896_;
}
else
{
return v___x_3894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v_res_3905_; 
v_res_3905_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_);
lean_dec(v_a_3903_);
lean_dec_ref(v_a_3902_);
lean_dec(v_a_3901_);
lean_dec_ref(v_a_3900_);
lean_dec(v_a_3899_);
lean_dec(v_a_3898_);
return v_res_3905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3906_, lean_object* v_fvars_3907_, lean_object* v_doms_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v___x_3916_; 
v___x_3916_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3906_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3907_, v_doms_3908_, v_a_3917_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_);
return v___x_3918_;
}
else
{
return v___x_3916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3919_, lean_object* v_fvars_3920_, lean_object* v_doms_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v_res_3929_; 
v_res_3929_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3919_, v_fvars_3920_, v_doms_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_, v___y_3926_, v___y_3927_);
lean_dec(v___y_3927_);
lean_dec_ref(v___y_3926_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v_doms_3921_);
lean_dec_ref(v_fvars_3920_);
return v_res_3929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3930_, lean_object* v_fvars_3931_, lean_object* v_doms_3932_, lean_object* v_e_3933_, lean_object* v_a_3934_, lean_object* v_a_3935_, lean_object* v_a_3936_, lean_object* v_a_3937_, lean_object* v_a_3938_, lean_object* v_a_3939_){
_start:
{
lean_object* v___x_3941_; 
v___x_3941_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3933_, v_a_3935_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
lean_inc(v_a_3942_);
lean_dec_ref_known(v___x_3941_, 1);
if (lean_obj_tag(v_a_3942_) == 1)
{
lean_object* v_val_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_dec_ref(v_e_3933_);
v_val_3943_ = lean_ctor_get(v_a_3942_, 0);
lean_inc(v_val_3943_);
lean_dec_ref_known(v_a_3942_, 1);
v___x_3944_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3945_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3945_, 0, v_fvars_3931_);
lean_closure_set(v___x_3945_, 1, v_doms_3932_);
lean_closure_set(v___x_3945_, 2, v_val_3943_);
v___x_3946_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3930_, v___x_3944_, v___x_3945_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
return v___x_3946_;
}
else
{
lean_dec(v_a_3942_);
if (lean_obj_tag(v_e_3933_) == 7)
{
lean_object* v_binderName_3947_; lean_object* v_binderType_3948_; lean_object* v_body_3949_; uint8_t v_binderInfo_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_binderName_3947_ = lean_ctor_get(v_e_3933_, 0);
lean_inc(v_binderName_3947_);
v_binderType_3948_ = lean_ctor_get(v_e_3933_, 1);
lean_inc_ref(v_binderType_3948_);
v_body_3949_ = lean_ctor_get(v_e_3933_, 2);
lean_inc_ref(v_body_3949_);
v_binderInfo_3950_ = lean_ctor_get_uint8(v_e_3933_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3933_, 3);
v___x_3951_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3952_ = lean_expr_instantiate_rev(v_binderType_3948_, v_fvars_3931_);
lean_dec_ref(v_binderType_3948_);
v___x_3953_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3953_, 0, v___x_3952_);
lean_inc_ref(v_lctx_3930_);
v___x_3954_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3930_, v___x_3951_, v___x_3953_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
if (lean_obj_tag(v___x_3954_) == 0)
{
lean_object* v_a_3955_; lean_object* v___x_3956_; 
v_a_3955_ = lean_ctor_get(v___x_3954_, 0);
lean_inc(v_a_3955_);
lean_dec_ref_known(v___x_3954_, 1);
v___x_3956_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v_expr_3958_; uint8_t v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
lean_inc_n(v_a_3957_, 2);
lean_dec_ref_known(v___x_3956_, 1);
v_expr_3958_ = lean_ctor_get(v_a_3955_, 0);
v___x_3959_ = 0;
lean_inc_ref(v_expr_3958_);
v___x_3960_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3930_, v_a_3957_, v_binderName_3947_, v_expr_3958_, v_binderInfo_3950_, v___x_3959_);
v___x_3961_ = l_Lean_Expr_fvar___override(v_a_3957_);
v___x_3962_ = lean_array_push(v_fvars_3931_, v___x_3961_);
v___x_3963_ = lean_array_push(v_doms_3932_, v_a_3955_);
v_lctx_3930_ = v___x_3960_;
v_fvars_3931_ = v___x_3962_;
v_doms_3932_ = v___x_3963_;
v_e_3933_ = v_body_3949_;
goto _start;
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec(v_a_3955_);
lean_dec_ref(v_body_3949_);
lean_dec(v_binderName_3947_);
lean_dec_ref(v_doms_3932_);
lean_dec_ref(v_fvars_3931_);
lean_dec_ref(v_lctx_3930_);
v_a_3965_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3956_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3956_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
else
{
lean_dec_ref(v_body_3949_);
lean_dec(v_binderName_3947_);
lean_dec_ref(v_doms_3932_);
lean_dec_ref(v_fvars_3931_);
lean_dec_ref(v_lctx_3930_);
return v___x_3954_;
}
}
else
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___f_3975_; lean_object* v___x_3976_; 
v___x_3973_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3974_ = lean_expr_instantiate_rev(v_e_3933_, v_fvars_3931_);
lean_dec_ref(v_e_3933_);
v___f_3975_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3975_, 0, v___x_3974_);
lean_closure_set(v___f_3975_, 1, v_fvars_3931_);
lean_closure_set(v___f_3975_, 2, v_doms_3932_);
v___x_3976_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3930_, v___x_3973_, v___f_3975_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_);
return v___x_3976_;
}
}
}
else
{
lean_object* v_a_3977_; lean_object* v___x_3979_; uint8_t v_isShared_3980_; uint8_t v_isSharedCheck_3984_; 
lean_dec_ref(v_e_3933_);
lean_dec_ref(v_doms_3932_);
lean_dec_ref(v_fvars_3931_);
lean_dec_ref(v_lctx_3930_);
v_a_3977_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3984_ == 0)
{
v___x_3979_ = v___x_3941_;
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
else
{
lean_inc(v_a_3977_);
lean_dec(v___x_3941_);
v___x_3979_ = lean_box(0);
v_isShared_3980_ = v_isSharedCheck_3984_;
goto v_resetjp_3978_;
}
v_resetjp_3978_:
{
lean_object* v___x_3982_; 
if (v_isShared_3980_ == 0)
{
v___x_3982_ = v___x_3979_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v_a_3977_);
v___x_3982_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
return v___x_3982_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_){
_start:
{
uint32_t v___x_3993_; uint8_t v___x_3994_; 
v___x_3993_ = 5;
v___x_3994_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3985_, v___x_3993_);
if (v___x_3994_ == 0)
{
lean_object* v_lctx_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v_lctx_3995_ = lean_ctor_get(v_a_3988_, 2);
v___x_3996_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3995_);
v___x_3997_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3995_, v___x_3996_, v___x_3996_, v_e_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_);
return v___x_3997_;
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v___x_4000_; 
v___x_3998_ = lean_box(0);
v___x_3999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3999_, 0, v_e_3985_);
lean_ctor_set(v___x_3999_, 1, v___x_3998_);
v___x_4000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3999_);
return v___x_4000_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_4001_, lean_object* v_a_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_){
_start:
{
lean_object* v_res_4009_; 
v_res_4009_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
lean_dec(v_a_4007_);
lean_dec_ref(v_a_4006_);
lean_dec(v_a_4005_);
lean_dec_ref(v_a_4004_);
lean_dec(v_a_4003_);
lean_dec(v_a_4002_);
return v_res_4009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_4010_, lean_object* v_e_4011_, lean_object* v_typeName_4012_, lean_object* v_idx_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4010_, v_e_4011_, v_typeName_4012_, v_idx_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec(v___y_4017_);
lean_dec_ref(v___y_4016_);
lean_dec(v___y_4015_);
lean_dec(v___y_4014_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_);
lean_dec(v_a_4028_);
lean_dec_ref(v_a_4027_);
lean_dec(v_a_4026_);
lean_dec_ref(v_a_4025_);
lean_dec(v_a_4024_);
lean_dec(v_a_4023_);
return v_res_4030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_){
_start:
{
lean_object* v___x_4040_; 
v___x_4040_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v___x_4040_, 1);
v___x_4042_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4031_, v_a_4041_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_, v___y_4038_);
return v___x_4042_;
}
else
{
lean_dec_ref(v_fvars_4031_);
return v___x_4040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_res_4052_; 
v_res_4052_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_, v___y_4050_);
lean_dec(v___y_4050_);
lean_dec_ref(v___y_4049_);
lean_dec(v___y_4048_);
lean_dec_ref(v___y_4047_);
lean_dec(v___y_4046_);
lean_dec(v___y_4045_);
return v_res_4052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4053_, lean_object* v_fvars_4054_, lean_object* v_e_4055_, lean_object* v_letFVars_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
switch(lean_obj_tag(v_e_4055_))
{
case 6:
{
lean_object* v_binderName_4064_; lean_object* v_binderType_4065_; lean_object* v_body_4066_; uint8_t v_binderInfo_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_binderName_4064_ = lean_ctor_get(v_e_4055_, 0);
lean_inc(v_binderName_4064_);
v_binderType_4065_ = lean_ctor_get(v_e_4055_, 1);
lean_inc_ref(v_binderType_4065_);
v_body_4066_ = lean_ctor_get(v_e_4055_, 2);
lean_inc_ref(v_body_4066_);
v_binderInfo_4067_ = lean_ctor_get_uint8(v_e_4055_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4055_, 3);
v___x_4068_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4053_);
lean_inc(v_letFVars_4056_);
v___x_4069_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4054_, v_letFVars_4056_, v_lctx_4053_, v___x_4068_, v_binderType_4065_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
lean_dec_ref(v_binderType_4065_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_object* v_a_4070_; lean_object* v___x_4071_; 
v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4069_, 1);
v___x_4071_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v_expr_4073_; uint8_t v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc_n(v_a_4072_, 2);
lean_dec_ref_known(v___x_4071_, 1);
v_expr_4073_ = lean_ctor_get(v_a_4070_, 0);
lean_inc_ref(v_expr_4073_);
lean_dec(v_a_4070_);
v___x_4074_ = 0;
v___x_4075_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4053_, v_a_4072_, v_binderName_4064_, v_expr_4073_, v_binderInfo_4067_, v___x_4074_);
v___x_4076_ = l_Lean_Expr_fvar___override(v_a_4072_);
v___x_4077_ = lean_array_push(v_fvars_4054_, v___x_4076_);
v_lctx_4053_ = v___x_4075_;
v_fvars_4054_ = v___x_4077_;
v_e_4055_ = v_body_4066_;
goto _start;
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec(v_a_4070_);
lean_dec_ref(v_body_4066_);
lean_dec(v_binderName_4064_);
lean_dec(v_letFVars_4056_);
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_lctx_4053_);
v_a_4079_ = lean_ctor_get(v___x_4071_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4071_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_4071_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_4071_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
else
{
lean_dec_ref(v_body_4066_);
lean_dec(v_binderName_4064_);
lean_dec(v_letFVars_4056_);
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_lctx_4053_);
return v___x_4069_;
}
}
case 8:
{
lean_object* v_declName_4087_; lean_object* v_type_4088_; lean_object* v_value_4089_; lean_object* v_body_4090_; uint8_t v_nondep_4091_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; lean_object* v___y_4101_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v_declName_4087_ = lean_ctor_get(v_e_4055_, 0);
lean_inc(v_declName_4087_);
v_type_4088_ = lean_ctor_get(v_e_4055_, 1);
lean_inc_ref(v_type_4088_);
v_value_4089_ = lean_ctor_get(v_e_4055_, 2);
lean_inc_ref(v_value_4089_);
v_body_4090_ = lean_ctor_get(v_e_4055_, 3);
lean_inc_ref(v_body_4090_);
v_nondep_4091_ = lean_ctor_get_uint8(v_e_4055_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4055_, 4);
v___x_4105_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4053_);
lean_inc(v_letFVars_4056_);
v___x_4106_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4054_, v_letFVars_4056_, v_lctx_4053_, v___x_4105_, v_type_4088_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
lean_dec_ref(v_type_4088_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v_a_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref_known(v___x_4106_, 1);
v___x_4108_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4053_);
lean_inc(v_letFVars_4056_);
v___x_4109_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4054_, v_letFVars_4056_, v_lctx_4053_, v___x_4108_, v_value_4089_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
lean_dec_ref(v_value_4089_);
if (lean_obj_tag(v___x_4109_) == 0)
{
lean_object* v_a_4110_; lean_object* v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; uint8_t v___x_4140_; 
v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
lean_inc(v_a_4110_);
lean_dec_ref_known(v___x_4109_, 1);
v___x_4140_ = l_List_isEmpty___redArg(v_letFVars_4056_);
if (v___x_4140_ == 0)
{
lean_object* v___f_4141_; lean_object* v___x_4142_; 
lean_inc(v_a_4107_);
lean_inc(v_a_4110_);
v___f_4141_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4141_, 0, v_a_4110_);
lean_closure_set(v___f_4141_, 1, v_a_4107_);
lean_inc_ref(v_lctx_4053_);
v___x_4142_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4053_, v___f_4141_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_dec_ref_known(v___x_4142_, 1);
v___y_4112_ = v_a_4057_;
v___y_4113_ = v_a_4058_;
v___y_4114_ = v_a_4059_;
v___y_4115_ = v_a_4060_;
v___y_4116_ = v_a_4061_;
v___y_4117_ = v_a_4062_;
goto v___jp_4111_;
}
else
{
lean_object* v_a_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4150_; 
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_body_4090_);
lean_dec(v_declName_4087_);
lean_dec(v_letFVars_4056_);
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_lctx_4053_);
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4145_ = v___x_4142_;
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_a_4143_);
lean_dec(v___x_4142_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4150_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4148_; 
if (v_isShared_4146_ == 0)
{
v___x_4148_ = v___x_4145_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v_a_4143_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
else
{
v___y_4112_ = v_a_4057_;
v___y_4113_ = v_a_4058_;
v___y_4114_ = v_a_4059_;
v___y_4115_ = v_a_4060_;
v___y_4116_ = v_a_4061_;
v___y_4117_ = v_a_4062_;
goto v___jp_4111_;
}
v___jp_4111_:
{
lean_object* v___x_4118_; 
v___x_4118_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
if (lean_obj_tag(v___x_4118_) == 0)
{
lean_object* v_a_4119_; lean_object* v_expr_4120_; lean_object* v_expr_4121_; lean_object* v___x_4123_; uint8_t v_isShared_4124_; uint8_t v_isSharedCheck_4130_; 
v_a_4119_ = lean_ctor_get(v___x_4118_, 0);
lean_inc(v_a_4119_);
lean_dec_ref_known(v___x_4118_, 1);
v_expr_4120_ = lean_ctor_get(v_a_4107_, 0);
lean_inc_ref(v_expr_4120_);
lean_dec(v_a_4107_);
v_expr_4121_ = lean_ctor_get(v_a_4110_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v_a_4110_);
if (v_isSharedCheck_4130_ == 0)
{
lean_object* v_unused_4131_; 
v_unused_4131_ = lean_ctor_get(v_a_4110_, 1);
lean_dec(v_unused_4131_);
v___x_4123_ = v_a_4110_;
v_isShared_4124_ = v_isSharedCheck_4130_;
goto v_resetjp_4122_;
}
else
{
lean_inc(v_expr_4121_);
lean_dec(v_a_4110_);
v___x_4123_ = lean_box(0);
v_isShared_4124_ = v_isSharedCheck_4130_;
goto v_resetjp_4122_;
}
v_resetjp_4122_:
{
uint8_t v___x_4125_; lean_object* v___x_4126_; 
v___x_4125_ = 0;
lean_inc(v_a_4119_);
v___x_4126_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4053_, v_a_4119_, v_declName_4087_, v_expr_4120_, v_expr_4121_, v_nondep_4091_, v___x_4125_);
if (v_nondep_4091_ == 0)
{
lean_object* v___x_4128_; 
lean_inc(v_a_4119_);
if (v_isShared_4124_ == 0)
{
lean_ctor_set_tag(v___x_4123_, 1);
lean_ctor_set(v___x_4123_, 1, v_letFVars_4056_);
lean_ctor_set(v___x_4123_, 0, v_a_4119_);
v___x_4128_ = v___x_4123_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4119_);
lean_ctor_set(v_reuseFailAlloc_4129_, 1, v_letFVars_4056_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
v___y_4093_ = v___x_4126_;
v___y_4094_ = v___y_4115_;
v___y_4095_ = v___y_4116_;
v___y_4096_ = v___y_4113_;
v___y_4097_ = v___y_4112_;
v___y_4098_ = v___y_4114_;
v___y_4099_ = v_a_4119_;
v___y_4100_ = v___y_4117_;
v___y_4101_ = v___x_4128_;
goto v___jp_4092_;
}
}
else
{
lean_del_object(v___x_4123_);
v___y_4093_ = v___x_4126_;
v___y_4094_ = v___y_4115_;
v___y_4095_ = v___y_4116_;
v___y_4096_ = v___y_4113_;
v___y_4097_ = v___y_4112_;
v___y_4098_ = v___y_4114_;
v___y_4099_ = v_a_4119_;
v___y_4100_ = v___y_4117_;
v___y_4101_ = v_letFVars_4056_;
goto v___jp_4092_;
}
}
}
else
{
lean_object* v_a_4132_; lean_object* v___x_4134_; uint8_t v_isShared_4135_; uint8_t v_isSharedCheck_4139_; 
lean_dec(v_a_4110_);
lean_dec(v_a_4107_);
lean_dec_ref(v_body_4090_);
lean_dec(v_declName_4087_);
lean_dec(v_letFVars_4056_);
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_lctx_4053_);
v_a_4132_ = lean_ctor_get(v___x_4118_, 0);
v_isSharedCheck_4139_ = !lean_is_exclusive(v___x_4118_);
if (v_isSharedCheck_4139_ == 0)
{
v___x_4134_ = v___x_4118_;
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
else
{
lean_inc(v_a_4132_);
lean_dec(v___x_4118_);
v___x_4134_ = lean_box(0);
v_isShared_4135_ = v_isSharedCheck_4139_;
goto v_resetjp_4133_;
}
v_resetjp_4133_:
{
lean_object* v___x_4137_; 
if (v_isShared_4135_ == 0)
{
v___x_4137_ = v___x_4134_;
goto v_reusejp_4136_;
}
else
{
lean_object* v_reuseFailAlloc_4138_; 
v_reuseFailAlloc_4138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4138_, 0, v_a_4132_);
v___x_4137_ = v_reuseFailAlloc_4138_;
goto v_reusejp_4136_;
}
v_reusejp_4136_:
{
return v___x_4137_;
}
}
}
}
}
else
{
lean_dec(v_a_4107_);
lean_dec_ref(v_body_4090_);
lean_dec(v_declName_4087_);
lean_dec(v_letFVars_4056_);
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_lctx_4053_);
return v___x_4109_;
}
}
else
{
lean_dec_ref(v_body_4090_);
lean_dec_ref(v_value_4089_);
lean_dec(v_declName_4087_);
lean_dec(v_letFVars_4056_);
lean_dec_ref(v_fvars_4054_);
lean_dec_ref(v_lctx_4053_);
return v___x_4106_;
}
v___jp_4092_:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = l_Lean_Expr_fvar___override(v___y_4099_);
v___x_4103_ = lean_array_push(v_fvars_4054_, v___x_4102_);
v_lctx_4053_ = v___y_4093_;
v_fvars_4054_ = v___x_4103_;
v_e_4055_ = v_body_4090_;
v_letFVars_4056_ = v___y_4101_;
v_a_4057_ = v___y_4097_;
v_a_4058_ = v___y_4096_;
v_a_4059_ = v___y_4098_;
v_a_4060_ = v___y_4094_;
v_a_4061_ = v___y_4095_;
v_a_4062_ = v___y_4100_;
goto _start;
}
}
default: 
{
lean_object* v___f_4151_; lean_object* v___x_4152_; 
lean_inc_ref(v_fvars_4054_);
v___f_4151_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4151_, 0, v_fvars_4054_);
v___x_4152_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4054_, v_letFVars_4056_, v_lctx_4053_, v___f_4151_, v_e_4055_, v_a_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_);
lean_dec_ref(v_e_4055_);
lean_dec_ref(v_fvars_4054_);
return v___x_4152_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_){
_start:
{
uint32_t v___x_4161_; uint8_t v___x_4162_; 
v___x_4161_ = 5;
v___x_4162_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4153_, v___x_4161_);
if (v___x_4162_ == 0)
{
lean_object* v_lctx_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_lctx_4163_ = lean_ctor_get(v_a_4156_, 2);
v___x_4164_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4154_);
lean_inc_ref(v_lctx_4163_);
v___x_4165_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4163_, v___x_4164_, v_e_4153_, v_a_4154_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
return v___x_4165_;
}
else
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4166_ = lean_box(0);
v___x_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4167_, 0, v_e_4153_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
return v___x_4168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_){
_start:
{
lean_object* v_res_4177_; 
v_res_4177_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4169_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_, v_a_4175_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
lean_dec(v_a_4173_);
lean_dec_ref(v_a_4172_);
lean_dec(v_a_4171_);
lean_dec(v_a_4170_);
return v_res_4177_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_){
_start:
{
switch(lean_obj_tag(v_e_4178_))
{
case 0:
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4186_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4187_ = l_Lean_MessageData_ofExpr(v_e_4178_);
v___x_4188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4186_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
v___x_4189_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4188_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4189_;
}
case 1:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4178_, v___y_4181_, v___y_4183_, v___y_4184_);
return v___x_4190_;
}
case 2:
{
lean_object* v___x_4191_; 
v___x_4191_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4191_;
}
case 3:
{
lean_object* v_u_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v_u_4192_ = lean_ctor_get(v_e_4178_, 0);
lean_inc(v_u_4192_);
v___x_4193_ = l_Lean_Level_succ___override(v_u_4192_);
v___x_4194_ = l_Lean_Expr_sort___override(v___x_4193_);
v___x_4195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4194_);
v___x_4196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4196_, 0, v_e_4178_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
return v___x_4197_;
}
case 4:
{
lean_object* v___x_4198_; 
v___x_4198_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4178_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4198_;
}
case 5:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
lean_inc_ref(v_e_4178_);
v___x_4199_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4199_, 0, v_e_4178_);
v___x_4200_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4178_, v___x_4199_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4200_;
}
case 7:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
lean_inc_ref(v_e_4178_);
v___x_4201_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4201_, 0, v_e_4178_);
v___x_4202_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4178_, v___x_4201_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4202_;
}
case 9:
{
lean_object* v_a_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_a_4203_ = lean_ctor_get(v_e_4178_, 0);
v___x_4204_ = l_Lean_Literal_type(v_a_4203_);
v___x_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v_e_4178_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
case 10:
{
lean_object* v_data_4208_; lean_object* v_expr_4209_; lean_object* v___x_4210_; 
v_data_4208_ = lean_ctor_get(v_e_4178_, 0);
v_expr_4209_ = lean_ctor_get(v_e_4178_, 1);
lean_inc_ref(v_expr_4209_);
v___x_4210_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4209_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4233_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4213_ = v___x_4210_;
v_isShared_4214_ = v_isSharedCheck_4233_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4210_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4233_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v_expr_4215_; lean_object* v_type_x3f_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4232_; 
v_expr_4215_ = lean_ctor_get(v_a_4211_, 0);
v_type_x3f_4216_ = lean_ctor_get(v_a_4211_, 1);
v_isSharedCheck_4232_ = !lean_is_exclusive(v_a_4211_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4218_ = v_a_4211_;
v_isShared_4219_ = v_isSharedCheck_4232_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_type_x3f_4216_);
lean_inc(v_expr_4215_);
lean_dec(v_a_4211_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4232_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___y_4221_; size_t v___x_4228_; size_t v___x_4229_; uint8_t v___x_4230_; 
v___x_4228_ = lean_ptr_addr(v_expr_4209_);
v___x_4229_ = lean_ptr_addr(v_expr_4215_);
v___x_4230_ = lean_usize_dec_eq(v___x_4228_, v___x_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4231_; 
lean_inc(v_data_4208_);
lean_dec_ref_known(v_e_4178_, 2);
v___x_4231_ = l_Lean_Expr_mdata___override(v_data_4208_, v_expr_4215_);
v___y_4221_ = v___x_4231_;
goto v___jp_4220_;
}
else
{
lean_dec_ref(v_expr_4215_);
v___y_4221_ = v_e_4178_;
goto v___jp_4220_;
}
v___jp_4220_:
{
lean_object* v___x_4223_; 
if (v_isShared_4219_ == 0)
{
lean_ctor_set(v___x_4218_, 0, v___y_4221_);
v___x_4223_ = v___x_4218_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4227_; 
v_reuseFailAlloc_4227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4227_, 0, v___y_4221_);
lean_ctor_set(v_reuseFailAlloc_4227_, 1, v_type_x3f_4216_);
v___x_4223_ = v_reuseFailAlloc_4227_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
lean_object* v___x_4225_; 
if (v_isShared_4214_ == 0)
{
lean_ctor_set(v___x_4213_, 0, v___x_4223_);
v___x_4225_ = v___x_4213_;
goto v_reusejp_4224_;
}
else
{
lean_object* v_reuseFailAlloc_4226_; 
v_reuseFailAlloc_4226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4226_, 0, v___x_4223_);
v___x_4225_ = v_reuseFailAlloc_4226_;
goto v_reusejp_4224_;
}
v_reusejp_4224_:
{
return v___x_4225_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4178_, 2);
return v___x_4210_;
}
}
case 11:
{
lean_object* v_typeName_4234_; lean_object* v_idx_4235_; lean_object* v_struct_4236_; lean_object* v___f_4237_; lean_object* v___x_4238_; 
v_typeName_4234_ = lean_ctor_get(v_e_4178_, 0);
v_idx_4235_ = lean_ctor_get(v_e_4178_, 1);
v_struct_4236_ = lean_ctor_get(v_e_4178_, 2);
lean_inc(v_idx_4235_);
lean_inc(v_typeName_4234_);
lean_inc_ref(v_e_4178_);
lean_inc_ref(v_struct_4236_);
v___f_4237_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4237_, 0, v_struct_4236_);
lean_closure_set(v___f_4237_, 1, v_e_4178_);
lean_closure_set(v___f_4237_, 2, v_typeName_4234_);
lean_closure_set(v___f_4237_, 3, v_idx_4235_);
v___x_4238_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4178_, v___f_4237_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4238_;
}
default: 
{
lean_object* v___x_4239_; lean_object* v___x_4240_; 
lean_inc_ref(v_e_4178_);
v___x_4239_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4239_, 0, v_e_4178_);
v___x_4240_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4178_, v___x_4239_, v___y_4179_, v___y_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
return v___x_4240_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4241_; double v___x_4242_; 
v___x_4241_ = lean_unsigned_to_nat(1000000000u);
v___x_4242_ = lean_float_of_nat(v___x_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4243_, lean_object* v_a_4244_, lean_object* v_a_4245_, lean_object* v_a_4246_, lean_object* v_a_4247_, lean_object* v_a_4248_, lean_object* v_a_4249_){
_start:
{
lean_object* v_options_4251_; uint8_t v_hasTrace_4252_; 
v_options_4251_ = lean_ctor_get(v_a_4248_, 2);
v_hasTrace_4252_ = lean_ctor_get_uint8(v_options_4251_, sizeof(void*)*1);
if (v_hasTrace_4252_ == 0)
{
lean_object* v___x_4253_; 
v___x_4253_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4253_;
}
else
{
lean_object* v_inheritedTraceOptions_4254_; lean_object* v___f_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; uint8_t v___x_4259_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v_a_4263_; lean_object* v___y_4276_; lean_object* v___y_4277_; lean_object* v_a_4278_; 
v_inheritedTraceOptions_4254_ = lean_ctor_get(v_a_4248_, 13);
lean_inc_ref(v_e_4243_);
v___f_4255_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4255_, 0, v_e_4243_);
v___x_4256_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4257_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4258_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4259_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4254_, v_options_4251_, v___x_4258_);
if (v___x_4259_ == 0)
{
lean_object* v___x_4336_; uint8_t v___x_4337_; 
v___x_4336_ = l_Lean_trace_profiler;
v___x_4337_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4251_, v___x_4336_);
if (v___x_4337_ == 0)
{
lean_object* v___x_4338_; 
lean_dec_ref(v___f_4255_);
v___x_4338_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4338_;
}
else
{
goto v___jp_4287_;
}
}
else
{
goto v___jp_4287_;
}
v___jp_4260_:
{
lean_object* v___x_4264_; double v___x_4265_; double v___x_4266_; double v___x_4267_; double v___x_4268_; double v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; 
v___x_4264_ = lean_io_mono_nanos_now();
v___x_4265_ = lean_float_of_nat(v___y_4261_);
v___x_4266_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4267_ = lean_float_div(v___x_4265_, v___x_4266_);
v___x_4268_ = lean_float_of_nat(v___x_4264_);
v___x_4269_ = lean_float_div(v___x_4268_, v___x_4266_);
v___x_4270_ = lean_box_float(v___x_4267_);
v___x_4271_ = lean_box_float(v___x_4269_);
v___x_4272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4272_, 0, v___x_4270_);
lean_ctor_set(v___x_4272_, 1, v___x_4271_);
v___x_4273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4273_, 0, v_a_4263_);
lean_ctor_set(v___x_4273_, 1, v___x_4272_);
v___x_4274_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4256_, v_hasTrace_4252_, v___x_4257_, v_options_4251_, v___x_4259_, v___y_4262_, v___f_4255_, v___x_4273_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4274_;
}
v___jp_4275_:
{
lean_object* v___x_4279_; double v___x_4280_; double v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
v___x_4279_ = lean_io_get_num_heartbeats();
v___x_4280_ = lean_float_of_nat(v___y_4277_);
v___x_4281_ = lean_float_of_nat(v___x_4279_);
v___x_4282_ = lean_box_float(v___x_4280_);
v___x_4283_ = lean_box_float(v___x_4281_);
v___x_4284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4284_, 0, v___x_4282_);
lean_ctor_set(v___x_4284_, 1, v___x_4283_);
v___x_4285_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4285_, 0, v_a_4278_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4256_, v_hasTrace_4252_, v___x_4257_, v_options_4251_, v___x_4259_, v___y_4276_, v___f_4255_, v___x_4285_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
return v___x_4286_;
}
v___jp_4287_:
{
lean_object* v___x_4288_; 
v___x_4288_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4249_);
if (lean_obj_tag(v___x_4288_) == 0)
{
lean_object* v_a_4289_; lean_object* v___x_4290_; uint8_t v___x_4291_; 
v_a_4289_ = lean_ctor_get(v___x_4288_, 0);
lean_inc(v_a_4289_);
lean_dec_ref_known(v___x_4288_, 1);
v___x_4290_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4291_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4251_, v___x_4290_);
if (v___x_4291_ == 0)
{
lean_object* v___x_4292_; lean_object* v___x_4293_; 
v___x_4292_ = lean_io_mono_nanos_now();
v___x_4293_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4293_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4293_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 1);
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
v___y_4261_ = v___x_4292_;
v___y_4262_ = v_a_4289_;
v_a_4263_ = v___x_4299_;
goto v___jp_4260_;
}
}
}
else
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4309_; 
v_a_4302_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4309_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4309_ == 0)
{
v___x_4304_ = v___x_4293_;
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4293_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4309_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
lean_object* v___x_4307_; 
if (v_isShared_4305_ == 0)
{
lean_ctor_set_tag(v___x_4304_, 0);
v___x_4307_ = v___x_4304_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v_a_4302_);
v___x_4307_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
v___y_4261_ = v___x_4292_;
v___y_4262_ = v_a_4289_;
v_a_4263_ = v___x_4307_;
goto v___jp_4260_;
}
}
}
}
else
{
lean_object* v___x_4310_; lean_object* v___x_4311_; 
v___x_4310_ = lean_io_get_num_heartbeats();
v___x_4311_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4243_, v_a_4244_, v_a_4245_, v_a_4246_, v_a_4247_, v_a_4248_, v_a_4249_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 1);
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
v___y_4276_ = v_a_4289_;
v___y_4277_ = v___x_4310_;
v_a_4278_ = v___x_4317_;
goto v___jp_4275_;
}
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
v_a_4320_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4311_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4311_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set_tag(v___x_4322_, 0);
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
v___y_4276_ = v_a_4289_;
v___y_4277_ = v___x_4310_;
v_a_4278_ = v___x_4325_;
goto v___jp_4275_;
}
}
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v___f_4255_);
lean_dec_ref(v_e_4243_);
v_a_4328_ = lean_ctor_get(v___x_4288_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___x_4288_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___x_4288_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4288_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
return v___x_4333_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4339_, lean_object* v_e_4340_, lean_object* v_typeName_4341_, lean_object* v_idx_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_){
_start:
{
lean_object* v___x_4350_; 
v___x_4350_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4339_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4352_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4340_, v_typeName_4341_, v_idx_4342_, v_a_4351_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
return v___x_4352_;
}
else
{
lean_dec(v_idx_4342_);
lean_dec(v_typeName_4341_);
lean_dec_ref(v_e_4340_);
return v___x_4350_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v_res_4361_; 
v_res_4361_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
lean_dec(v_a_4359_);
lean_dec_ref(v_a_4358_);
lean_dec(v_a_4357_);
lean_dec_ref(v_a_4356_);
lean_dec(v_a_4355_);
lean_dec(v_a_4354_);
return v_res_4361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4362_, lean_object* v_fvars_4363_, lean_object* v_doms_4364_, lean_object* v_e_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_){
_start:
{
lean_object* v_res_4373_; 
v_res_4373_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4362_, v_fvars_4363_, v_doms_4364_, v_e_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_);
lean_dec(v_a_4371_);
lean_dec_ref(v_a_4370_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
lean_dec(v_a_4367_);
lean_dec(v_a_4366_);
return v_res_4373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_){
_start:
{
lean_object* v_res_4382_; 
v_res_4382_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4374_, v___y_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec_ref(v___y_4377_);
lean_dec(v___y_4376_);
lean_dec(v___y_4375_);
return v_res_4382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4383_, lean_object* v_fvars_4384_, lean_object* v_e_4385_, lean_object* v_letFVars_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_, lean_object* v_a_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4383_, v_fvars_4384_, v_e_4385_, v_letFVars_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_, v_a_4392_);
lean_dec(v_a_4392_);
lean_dec_ref(v_a_4391_);
lean_dec(v_a_4390_);
lean_dec_ref(v_a_4389_);
lean_dec(v_a_4388_);
lean_dec(v_a_4387_);
return v_res_4394_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4395_, lean_object* v_lctx_4396_, lean_object* v_localInsts_4397_, lean_object* v_x_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_){
_start:
{
lean_object* v___x_4406_; 
v___x_4406_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4396_, v_localInsts_4397_, v_x_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4407_, lean_object* v_lctx_4408_, lean_object* v_localInsts_4409_, lean_object* v_x_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v_res_4418_; 
v_res_4418_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4407_, v_lctx_4408_, v_localInsts_4409_, v_x_4410_, v___y_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec_ref(v___y_4413_);
lean_dec(v___y_4412_);
lean_dec(v___y_4411_);
return v_res_4418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4419_, lean_object* v_lctx_4420_, lean_object* v_x_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v___x_4429_; 
v___x_4429_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4420_, v_x_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_);
return v___x_4429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4430_, lean_object* v_lctx_4431_, lean_object* v_x_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v_res_4440_; 
v_res_4440_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4430_, v_lctx_4431_, v_x_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec(v___y_4433_);
return v_res_4440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4446_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_){
_start:
{
lean_object* v_res_4456_; 
v_res_4456_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec(v___y_4449_);
return v_res_4456_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v___x_4464_; 
v___x_4464_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4462_);
return v___x_4464_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec(v___y_4465_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_00_u03b1_4473_, lean_object* v_x_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_){
_start:
{
lean_object* v___x_4482_; 
v___x_4482_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_x_4474_);
return v___x_4482_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_00_u03b1_4483_, lean_object* v_x_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_00_u03b1_4483_, v_x_4484_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec(v___y_4485_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_oldTraces_4493_, lean_object* v_data_4494_, lean_object* v_ref_4495_, lean_object* v_msg_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v___x_4504_; 
v___x_4504_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_oldTraces_4493_, v_data_4494_, v_ref_4495_, v_msg_4496_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
return v___x_4504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_oldTraces_4505_, lean_object* v_data_4506_, lean_object* v_ref_4507_, lean_object* v_msg_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_oldTraces_4505_, v_data_4506_, v_ref_4507_, v_msg_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
lean_dec(v___y_4510_);
lean_dec(v___y_4509_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4517_){
_start:
{
lean_object* v___x_4519_; lean_object* v_traceState_4520_; lean_object* v_traces_4521_; lean_object* v___x_4522_; lean_object* v_traceState_4523_; lean_object* v_env_4524_; lean_object* v_nextMacroScope_4525_; lean_object* v_ngen_4526_; lean_object* v_auxDeclNGen_4527_; lean_object* v_cache_4528_; lean_object* v_messages_4529_; lean_object* v_infoState_4530_; lean_object* v_snapshotTasks_4531_; lean_object* v___x_4533_; uint8_t v_isShared_4534_; uint8_t v_isSharedCheck_4552_; 
v___x_4519_ = lean_st_ref_get(v___y_4517_);
v_traceState_4520_ = lean_ctor_get(v___x_4519_, 4);
lean_inc_ref(v_traceState_4520_);
lean_dec(v___x_4519_);
v_traces_4521_ = lean_ctor_get(v_traceState_4520_, 0);
lean_inc_ref(v_traces_4521_);
lean_dec_ref(v_traceState_4520_);
v___x_4522_ = lean_st_ref_take(v___y_4517_);
v_traceState_4523_ = lean_ctor_get(v___x_4522_, 4);
v_env_4524_ = lean_ctor_get(v___x_4522_, 0);
v_nextMacroScope_4525_ = lean_ctor_get(v___x_4522_, 1);
v_ngen_4526_ = lean_ctor_get(v___x_4522_, 2);
v_auxDeclNGen_4527_ = lean_ctor_get(v___x_4522_, 3);
v_cache_4528_ = lean_ctor_get(v___x_4522_, 5);
v_messages_4529_ = lean_ctor_get(v___x_4522_, 6);
v_infoState_4530_ = lean_ctor_get(v___x_4522_, 7);
v_snapshotTasks_4531_ = lean_ctor_get(v___x_4522_, 8);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4522_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4533_ = v___x_4522_;
v_isShared_4534_ = v_isSharedCheck_4552_;
goto v_resetjp_4532_;
}
else
{
lean_inc(v_snapshotTasks_4531_);
lean_inc(v_infoState_4530_);
lean_inc(v_messages_4529_);
lean_inc(v_cache_4528_);
lean_inc(v_traceState_4523_);
lean_inc(v_auxDeclNGen_4527_);
lean_inc(v_ngen_4526_);
lean_inc(v_nextMacroScope_4525_);
lean_inc(v_env_4524_);
lean_dec(v___x_4522_);
v___x_4533_ = lean_box(0);
v_isShared_4534_ = v_isSharedCheck_4552_;
goto v_resetjp_4532_;
}
v_resetjp_4532_:
{
uint64_t v_tid_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4550_; 
v_tid_4535_ = lean_ctor_get_uint64(v_traceState_4523_, sizeof(void*)*1);
v_isSharedCheck_4550_ = !lean_is_exclusive(v_traceState_4523_);
if (v_isSharedCheck_4550_ == 0)
{
lean_object* v_unused_4551_; 
v_unused_4551_ = lean_ctor_get(v_traceState_4523_, 0);
lean_dec(v_unused_4551_);
v___x_4537_ = v_traceState_4523_;
v_isShared_4538_ = v_isSharedCheck_4550_;
goto v_resetjp_4536_;
}
else
{
lean_dec(v_traceState_4523_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4550_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4543_; 
v___x_4539_ = lean_unsigned_to_nat(32u);
v___x_4540_ = lean_mk_empty_array_with_capacity(v___x_4539_);
lean_dec_ref(v___x_4540_);
v___x_4541_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 0, v___x_4541_);
v___x_4543_ = v___x_4537_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v___x_4541_);
lean_ctor_set_uint64(v_reuseFailAlloc_4549_, sizeof(void*)*1, v_tid_4535_);
v___x_4543_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
lean_object* v___x_4545_; 
if (v_isShared_4534_ == 0)
{
lean_ctor_set(v___x_4533_, 4, v___x_4543_);
v___x_4545_ = v___x_4533_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_env_4524_);
lean_ctor_set(v_reuseFailAlloc_4548_, 1, v_nextMacroScope_4525_);
lean_ctor_set(v_reuseFailAlloc_4548_, 2, v_ngen_4526_);
lean_ctor_set(v_reuseFailAlloc_4548_, 3, v_auxDeclNGen_4527_);
lean_ctor_set(v_reuseFailAlloc_4548_, 4, v___x_4543_);
lean_ctor_set(v_reuseFailAlloc_4548_, 5, v_cache_4528_);
lean_ctor_set(v_reuseFailAlloc_4548_, 6, v_messages_4529_);
lean_ctor_set(v_reuseFailAlloc_4548_, 7, v_infoState_4530_);
lean_ctor_set(v_reuseFailAlloc_4548_, 8, v_snapshotTasks_4531_);
v___x_4545_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
v___x_4546_ = lean_st_ref_set(v___y_4517_, v___x_4545_);
v___x_4547_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4547_, 0, v_traces_4521_);
return v___x_4547_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4553_, lean_object* v___y_4554_){
_start:
{
lean_object* v_res_4555_; 
v_res_4555_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4553_);
lean_dec(v___y_4553_);
return v_res_4555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4559_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4568_, lean_object* v_zetaDeltaFVarIds_4569_, lean_object* v_a_x3f_4570_){
_start:
{
lean_object* v___x_4572_; lean_object* v_mctx_4573_; lean_object* v_cache_4574_; lean_object* v_postponed_4575_; lean_object* v_diag_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4586_; 
v___x_4572_ = lean_st_ref_take(v___y_4568_);
v_mctx_4573_ = lean_ctor_get(v___x_4572_, 0);
v_cache_4574_ = lean_ctor_get(v___x_4572_, 1);
v_postponed_4575_ = lean_ctor_get(v___x_4572_, 3);
v_diag_4576_ = lean_ctor_get(v___x_4572_, 4);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4586_ == 0)
{
lean_object* v_unused_4587_; 
v_unused_4587_ = lean_ctor_get(v___x_4572_, 2);
lean_dec(v_unused_4587_);
v___x_4578_ = v___x_4572_;
v_isShared_4579_ = v_isSharedCheck_4586_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_diag_4576_);
lean_inc(v_postponed_4575_);
lean_inc(v_cache_4574_);
lean_inc(v_mctx_4573_);
lean_dec(v___x_4572_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4586_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 2, v_zetaDeltaFVarIds_4569_);
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_mctx_4573_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_cache_4574_);
lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_zetaDeltaFVarIds_4569_);
lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_postponed_4575_);
lean_ctor_set(v_reuseFailAlloc_4585_, 4, v_diag_4576_);
v___x_4581_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v___x_4584_; 
v___x_4582_ = lean_st_ref_set(v___y_4568_, v___x_4581_);
v___x_4583_ = lean_box(0);
v___x_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___x_4583_);
return v___x_4584_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4588_, lean_object* v_zetaDeltaFVarIds_4589_, lean_object* v_a_x3f_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4588_, v_zetaDeltaFVarIds_4589_, v_a_x3f_4590_);
lean_dec(v_a_x3f_4590_);
lean_dec(v___y_4588_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4593_, lean_object* v_msg_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_, lean_object* v___y_4598_){
_start:
{
lean_object* v_ref_4600_; lean_object* v___x_4601_; lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4646_; 
v_ref_4600_ = lean_ctor_get(v___y_4597_, 5);
v___x_4601_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4594_, v___y_4595_, v___y_4596_, v___y_4597_, v___y_4598_);
v_a_4602_ = lean_ctor_get(v___x_4601_, 0);
v_isSharedCheck_4646_ = !lean_is_exclusive(v___x_4601_);
if (v_isSharedCheck_4646_ == 0)
{
v___x_4604_ = v___x_4601_;
v_isShared_4605_ = v_isSharedCheck_4646_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4601_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4646_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4606_; lean_object* v_traceState_4607_; lean_object* v_env_4608_; lean_object* v_nextMacroScope_4609_; lean_object* v_ngen_4610_; lean_object* v_auxDeclNGen_4611_; lean_object* v_cache_4612_; lean_object* v_messages_4613_; lean_object* v_infoState_4614_; lean_object* v_snapshotTasks_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4645_; 
v___x_4606_ = lean_st_ref_take(v___y_4598_);
v_traceState_4607_ = lean_ctor_get(v___x_4606_, 4);
v_env_4608_ = lean_ctor_get(v___x_4606_, 0);
v_nextMacroScope_4609_ = lean_ctor_get(v___x_4606_, 1);
v_ngen_4610_ = lean_ctor_get(v___x_4606_, 2);
v_auxDeclNGen_4611_ = lean_ctor_get(v___x_4606_, 3);
v_cache_4612_ = lean_ctor_get(v___x_4606_, 5);
v_messages_4613_ = lean_ctor_get(v___x_4606_, 6);
v_infoState_4614_ = lean_ctor_get(v___x_4606_, 7);
v_snapshotTasks_4615_ = lean_ctor_get(v___x_4606_, 8);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4606_);
if (v_isSharedCheck_4645_ == 0)
{
v___x_4617_ = v___x_4606_;
v_isShared_4618_ = v_isSharedCheck_4645_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_snapshotTasks_4615_);
lean_inc(v_infoState_4614_);
lean_inc(v_messages_4613_);
lean_inc(v_cache_4612_);
lean_inc(v_traceState_4607_);
lean_inc(v_auxDeclNGen_4611_);
lean_inc(v_ngen_4610_);
lean_inc(v_nextMacroScope_4609_);
lean_inc(v_env_4608_);
lean_dec(v___x_4606_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4645_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
uint64_t v_tid_4619_; lean_object* v_traces_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4644_; 
v_tid_4619_ = lean_ctor_get_uint64(v_traceState_4607_, sizeof(void*)*1);
v_traces_4620_ = lean_ctor_get(v_traceState_4607_, 0);
v_isSharedCheck_4644_ = !lean_is_exclusive(v_traceState_4607_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4622_ = v_traceState_4607_;
v_isShared_4623_ = v_isSharedCheck_4644_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_traces_4620_);
lean_dec(v_traceState_4607_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4644_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4624_; double v___x_4625_; uint8_t v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4634_; 
v___x_4624_ = lean_box(0);
v___x_4625_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4626_ = 0;
v___x_4627_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4628_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4628_, 0, v_cls_4593_);
lean_ctor_set(v___x_4628_, 1, v___x_4624_);
lean_ctor_set(v___x_4628_, 2, v___x_4627_);
lean_ctor_set_float(v___x_4628_, sizeof(void*)*3, v___x_4625_);
lean_ctor_set_float(v___x_4628_, sizeof(void*)*3 + 8, v___x_4625_);
lean_ctor_set_uint8(v___x_4628_, sizeof(void*)*3 + 16, v___x_4626_);
v___x_4629_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4630_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4630_, 0, v___x_4628_);
lean_ctor_set(v___x_4630_, 1, v_a_4602_);
lean_ctor_set(v___x_4630_, 2, v___x_4629_);
lean_inc(v_ref_4600_);
v___x_4631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4631_, 0, v_ref_4600_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
v___x_4632_ = l_Lean_PersistentArray_push___redArg(v_traces_4620_, v___x_4631_);
if (v_isShared_4623_ == 0)
{
lean_ctor_set(v___x_4622_, 0, v___x_4632_);
v___x_4634_ = v___x_4622_;
goto v_reusejp_4633_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v___x_4632_);
lean_ctor_set_uint64(v_reuseFailAlloc_4643_, sizeof(void*)*1, v_tid_4619_);
v___x_4634_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4633_;
}
v_reusejp_4633_:
{
lean_object* v___x_4636_; 
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 4, v___x_4634_);
v___x_4636_ = v___x_4617_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_env_4608_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v_nextMacroScope_4609_);
lean_ctor_set(v_reuseFailAlloc_4642_, 2, v_ngen_4610_);
lean_ctor_set(v_reuseFailAlloc_4642_, 3, v_auxDeclNGen_4611_);
lean_ctor_set(v_reuseFailAlloc_4642_, 4, v___x_4634_);
lean_ctor_set(v_reuseFailAlloc_4642_, 5, v_cache_4612_);
lean_ctor_set(v_reuseFailAlloc_4642_, 6, v_messages_4613_);
lean_ctor_set(v_reuseFailAlloc_4642_, 7, v_infoState_4614_);
lean_ctor_set(v_reuseFailAlloc_4642_, 8, v_snapshotTasks_4615_);
v___x_4636_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4640_; 
v___x_4637_ = lean_st_ref_set(v___y_4598_, v___x_4636_);
v___x_4638_ = lean_box(0);
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 0, v___x_4638_);
v___x_4640_ = v___x_4604_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v___x_4638_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4647_, lean_object* v_msg_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4647_, v_msg_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
return v_res_4654_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4657_ = l_Lean_stringToMessageData(v___x_4656_);
return v___x_4657_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4660_ = l_Lean_stringToMessageData(v___x_4659_);
return v___x_4660_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4663_ = l_Lean_stringToMessageData(v___x_4662_);
return v___x_4663_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4666_ = l_Lean_stringToMessageData(v___x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4667_, lean_object* v_e_4668_, lean_object* v___x_4669_, lean_object* v___x_4670_, lean_object* v_cls_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v___x_4677_; lean_object* v___x_4678_; 
v___x_4677_ = lean_st_mk_ref(v___x_4667_);
v___x_4678_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4668_, v___x_4669_, v___x_4677_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4748_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4748_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4748_ == 0)
{
v___x_4681_ = v___x_4678_;
v_isShared_4682_ = v_isSharedCheck_4748_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4748_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v_count_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4746_; 
v___x_4683_ = lean_st_ref_get(v___x_4677_);
lean_dec(v___x_4677_);
v_count_4684_ = lean_ctor_get(v___x_4683_, 0);
v_isSharedCheck_4746_ = !lean_is_exclusive(v___x_4683_);
if (v_isSharedCheck_4746_ == 0)
{
lean_object* v_unused_4747_; 
v_unused_4747_ = lean_ctor_get(v___x_4683_, 1);
lean_dec(v_unused_4747_);
v___x_4686_ = v___x_4683_;
v_isShared_4687_ = v_isSharedCheck_4746_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_count_4684_);
lean_dec(v___x_4683_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4746_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
uint8_t v___x_4710_; 
v___x_4710_ = lean_nat_dec_eq(v_count_4684_, v___x_4670_);
if (v___x_4710_ == 0)
{
lean_object* v_options_4711_; uint8_t v_hasTrace_4712_; 
v_options_4711_ = lean_ctor_get(v___y_4674_, 2);
v_hasTrace_4712_ = lean_ctor_get_uint8(v_options_4711_, sizeof(void*)*1);
if (v_hasTrace_4712_ == 0)
{
lean_dec(v_cls_4671_);
goto v___jp_4688_;
}
else
{
lean_object* v_inheritedTraceOptions_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; uint8_t v___x_4716_; 
v_inheritedTraceOptions_4713_ = lean_ctor_get(v___y_4674_, 13);
v___x_4714_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4671_);
v___x_4715_ = l_Lean_Name_append(v___x_4714_, v_cls_4671_);
v___x_4716_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4713_, v_options_4711_, v___x_4715_);
lean_dec(v___x_4715_);
if (v___x_4716_ == 0)
{
lean_dec(v_cls_4671_);
goto v___jp_4688_;
}
else
{
lean_object* v_expr_4717_; lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4720_; lean_object* v___x_4721_; 
v_expr_4717_ = lean_ctor_get(v_a_4679_, 0);
v___x_4718_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4717_);
v___x_4719_ = l_Lean_indentExpr(v_expr_4717_);
v___x_4720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4720_, 0, v___x_4718_);
lean_ctor_set(v___x_4720_, 1, v___x_4719_);
v___x_4721_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4671_, v___x_4720_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
if (lean_obj_tag(v___x_4721_) == 0)
{
lean_dec_ref_known(v___x_4721_, 1);
goto v___jp_4688_;
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_del_object(v___x_4686_);
lean_dec(v_count_4684_);
lean_del_object(v___x_4681_);
lean_dec(v_a_4679_);
v_a_4722_ = lean_ctor_get(v___x_4721_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4721_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4721_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4721_);
v___x_4724_ = lean_box(0);
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
v_resetjp_4723_:
{
lean_object* v___x_4727_; 
if (v_isShared_4725_ == 0)
{
v___x_4727_ = v___x_4724_;
goto v_reusejp_4726_;
}
else
{
lean_object* v_reuseFailAlloc_4728_; 
v_reuseFailAlloc_4728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4728_, 0, v_a_4722_);
v___x_4727_ = v_reuseFailAlloc_4728_;
goto v_reusejp_4726_;
}
v_reusejp_4726_:
{
return v___x_4727_;
}
}
}
}
}
}
else
{
lean_object* v_options_4730_; uint8_t v_hasTrace_4731_; 
v_options_4730_ = lean_ctor_get(v___y_4674_, 2);
v_hasTrace_4731_ = lean_ctor_get_uint8(v_options_4730_, sizeof(void*)*1);
if (v_hasTrace_4731_ == 0)
{
lean_dec(v_cls_4671_);
goto v___jp_4688_;
}
else
{
lean_object* v_inheritedTraceOptions_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; uint8_t v___x_4735_; 
v_inheritedTraceOptions_4732_ = lean_ctor_get(v___y_4674_, 13);
v___x_4733_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4671_);
v___x_4734_ = l_Lean_Name_append(v___x_4733_, v_cls_4671_);
v___x_4735_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4732_, v_options_4730_, v___x_4734_);
lean_dec(v___x_4734_);
if (v___x_4735_ == 0)
{
lean_dec(v_cls_4671_);
goto v___jp_4688_;
}
else
{
lean_object* v___x_4736_; lean_object* v___x_4737_; 
v___x_4736_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4737_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4671_, v___x_4736_, v___y_4672_, v___y_4673_, v___y_4674_, v___y_4675_);
if (lean_obj_tag(v___x_4737_) == 0)
{
lean_dec_ref_known(v___x_4737_, 1);
goto v___jp_4688_;
}
else
{
lean_object* v_a_4738_; lean_object* v___x_4740_; uint8_t v_isShared_4741_; uint8_t v_isSharedCheck_4745_; 
lean_del_object(v___x_4686_);
lean_dec(v_count_4684_);
lean_del_object(v___x_4681_);
lean_dec(v_a_4679_);
v_a_4738_ = lean_ctor_get(v___x_4737_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4737_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4740_ = v___x_4737_;
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
else
{
lean_inc(v_a_4738_);
lean_dec(v___x_4737_);
v___x_4740_ = lean_box(0);
v_isShared_4741_ = v_isSharedCheck_4745_;
goto v_resetjp_4739_;
}
v_resetjp_4739_:
{
lean_object* v___x_4743_; 
if (v_isShared_4741_ == 0)
{
v___x_4743_ = v___x_4740_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v_a_4738_);
v___x_4743_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
return v___x_4743_;
}
}
}
}
}
}
v___jp_4688_:
{
lean_object* v_expr_4689_; lean_object* v___x_4691_; uint8_t v_isShared_4692_; uint8_t v_isSharedCheck_4708_; 
v_expr_4689_ = lean_ctor_get(v_a_4679_, 0);
v_isSharedCheck_4708_ = !lean_is_exclusive(v_a_4679_);
if (v_isSharedCheck_4708_ == 0)
{
lean_object* v_unused_4709_; 
v_unused_4709_ = lean_ctor_get(v_a_4679_, 1);
lean_dec(v_unused_4709_);
v___x_4691_ = v_a_4679_;
v_isShared_4692_ = v_isSharedCheck_4708_;
goto v_resetjp_4690_;
}
else
{
lean_inc(v_expr_4689_);
lean_dec(v_a_4679_);
v___x_4691_ = lean_box(0);
v_isShared_4692_ = v_isSharedCheck_4708_;
goto v_resetjp_4690_;
}
v_resetjp_4690_:
{
lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4698_; 
v___x_4693_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4694_ = l_Nat_reprFast(v_count_4684_);
v___x_4695_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
v___x_4696_ = l_Lean_MessageData_ofFormat(v___x_4695_);
if (v_isShared_4692_ == 0)
{
lean_ctor_set_tag(v___x_4691_, 7);
lean_ctor_set(v___x_4691_, 1, v___x_4696_);
lean_ctor_set(v___x_4691_, 0, v___x_4693_);
v___x_4698_ = v___x_4691_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4707_; 
v_reuseFailAlloc_4707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4707_, 0, v___x_4693_);
lean_ctor_set(v_reuseFailAlloc_4707_, 1, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4707_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
lean_object* v___x_4699_; lean_object* v___x_4701_; 
v___x_4699_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4687_ == 0)
{
lean_ctor_set_tag(v___x_4686_, 7);
lean_ctor_set(v___x_4686_, 1, v___x_4699_);
lean_ctor_set(v___x_4686_, 0, v___x_4698_);
v___x_4701_ = v___x_4686_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v___x_4698_);
lean_ctor_set(v_reuseFailAlloc_4706_, 1, v___x_4699_);
v___x_4701_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
lean_object* v___x_4702_; lean_object* v___x_4704_; 
v___x_4702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4702_, 0, v_expr_4689_);
lean_ctor_set(v___x_4702_, 1, v___x_4701_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set(v___x_4681_, 0, v___x_4702_);
v___x_4704_ = v___x_4681_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v___x_4702_);
v___x_4704_ = v_reuseFailAlloc_4705_;
goto v_reusejp_4703_;
}
v_reusejp_4703_:
{
return v___x_4704_;
}
}
}
}
}
}
}
}
else
{
lean_object* v_a_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4756_; 
lean_dec(v___x_4677_);
lean_dec(v_cls_4671_);
v_a_4749_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4751_ = v___x_4678_;
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_a_4749_);
lean_dec(v___x_4678_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4756_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v_a_4749_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4757_, lean_object* v_e_4758_, lean_object* v___x_4759_, lean_object* v___x_4760_, lean_object* v_cls_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_, lean_object* v___y_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_){
_start:
{
lean_object* v_res_4767_; 
v_res_4767_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4757_, v_e_4758_, v___x_4759_, v___x_4760_, v_cls_4761_, v___y_4762_, v___y_4763_, v___y_4764_, v___y_4765_);
lean_dec(v___y_4765_);
lean_dec_ref(v___y_4764_);
lean_dec(v___y_4763_);
lean_dec_ref(v___y_4762_);
lean_dec(v___x_4760_);
lean_dec(v___x_4759_);
return v_res_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4768_, lean_object* v_cache_4769_, lean_object* v_a_x3f_4770_){
_start:
{
lean_object* v___x_4772_; lean_object* v_mctx_4773_; lean_object* v_zetaDeltaFVarIds_4774_; lean_object* v_postponed_4775_; lean_object* v_diag_4776_; lean_object* v___x_4778_; uint8_t v_isShared_4779_; uint8_t v_isSharedCheck_4786_; 
v___x_4772_ = lean_st_ref_take(v___y_4768_);
v_mctx_4773_ = lean_ctor_get(v___x_4772_, 0);
v_zetaDeltaFVarIds_4774_ = lean_ctor_get(v___x_4772_, 2);
v_postponed_4775_ = lean_ctor_get(v___x_4772_, 3);
v_diag_4776_ = lean_ctor_get(v___x_4772_, 4);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4772_);
if (v_isSharedCheck_4786_ == 0)
{
lean_object* v_unused_4787_; 
v_unused_4787_ = lean_ctor_get(v___x_4772_, 1);
lean_dec(v_unused_4787_);
v___x_4778_ = v___x_4772_;
v_isShared_4779_ = v_isSharedCheck_4786_;
goto v_resetjp_4777_;
}
else
{
lean_inc(v_diag_4776_);
lean_inc(v_postponed_4775_);
lean_inc(v_zetaDeltaFVarIds_4774_);
lean_inc(v_mctx_4773_);
lean_dec(v___x_4772_);
v___x_4778_ = lean_box(0);
v_isShared_4779_ = v_isSharedCheck_4786_;
goto v_resetjp_4777_;
}
v_resetjp_4777_:
{
lean_object* v___x_4781_; 
if (v_isShared_4779_ == 0)
{
lean_ctor_set(v___x_4778_, 1, v_cache_4769_);
v___x_4781_ = v___x_4778_;
goto v_reusejp_4780_;
}
else
{
lean_object* v_reuseFailAlloc_4785_; 
v_reuseFailAlloc_4785_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4785_, 0, v_mctx_4773_);
lean_ctor_set(v_reuseFailAlloc_4785_, 1, v_cache_4769_);
lean_ctor_set(v_reuseFailAlloc_4785_, 2, v_zetaDeltaFVarIds_4774_);
lean_ctor_set(v_reuseFailAlloc_4785_, 3, v_postponed_4775_);
lean_ctor_set(v_reuseFailAlloc_4785_, 4, v_diag_4776_);
v___x_4781_ = v_reuseFailAlloc_4785_;
goto v_reusejp_4780_;
}
v_reusejp_4780_:
{
lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; 
v___x_4782_ = lean_st_ref_set(v___y_4768_, v___x_4781_);
v___x_4783_ = lean_box(0);
v___x_4784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4783_);
return v___x_4784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4788_, lean_object* v_cache_4789_, lean_object* v_a_x3f_4790_, lean_object* v___y_4791_){
_start:
{
lean_object* v_res_4792_; 
v_res_4792_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4788_, v_cache_4789_, v_a_x3f_4790_);
lean_dec(v_a_x3f_4790_);
lean_dec(v___y_4788_);
return v_res_4792_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1));
v___x_4797_ = l_Lean_MessageData_ofFormat(v___x_4796_);
return v___x_4797_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4798_; 
v___x_4798_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4798_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4(void){
_start:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; 
v___x_4799_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3);
v___x_4800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
return v___x_4800_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5(void){
_start:
{
lean_object* v___x_4801_; lean_object* v___x_4802_; 
v___x_4801_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4);
v___x_4802_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4802_, 0, v___x_4801_);
lean_ctor_set(v___x_4802_, 1, v___x_4801_);
lean_ctor_set(v___x_4802_, 2, v___x_4801_);
lean_ctor_set(v___x_4802_, 3, v___x_4801_);
lean_ctor_set(v___x_4802_, 4, v___x_4801_);
lean_ctor_set(v___x_4802_, 5, v___x_4801_);
return v___x_4802_;
}
}
static uint64_t _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6(void){
_start:
{
uint8_t v___x_4803_; uint64_t v___x_4804_; 
v___x_4803_ = 0;
v___x_4804_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4803_);
return v___x_4804_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7(void){
_start:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
v___x_4805_ = lean_obj_once(&l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__whileM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4806_ = lean_unsigned_to_nat(0u);
v___x_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4807_, 0, v___x_4806_);
lean_ctor_set(v___x_4807_, 1, v___x_4805_);
return v___x_4807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_4808_, lean_object* v_e_4809_, uint8_t v___x_4810_, lean_object* v_cls_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
if (v___x_4808_ == 0)
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
lean_dec(v_cls_4811_);
v___x_4817_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2);
v___x_4818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4818_, 0, v_e_4809_);
lean_ctor_set(v___x_4818_, 1, v___x_4817_);
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
return v___x_4819_;
}
else
{
lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v_mctx_4822_; lean_object* v_zetaDeltaFVarIds_4823_; lean_object* v_postponed_4824_; lean_object* v_diag_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_5013_; 
v___x_4820_ = lean_st_ref_get(v___y_4813_);
v___x_4821_ = lean_st_ref_take(v___y_4813_);
v_mctx_4822_ = lean_ctor_get(v___x_4821_, 0);
v_zetaDeltaFVarIds_4823_ = lean_ctor_get(v___x_4821_, 2);
v_postponed_4824_ = lean_ctor_get(v___x_4821_, 3);
v_diag_4825_ = lean_ctor_get(v___x_4821_, 4);
v_isSharedCheck_5013_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_5013_ == 0)
{
lean_object* v_unused_5014_; 
v_unused_5014_ = lean_ctor_get(v___x_4821_, 1);
lean_dec(v_unused_5014_);
v___x_4827_ = v___x_4821_;
v_isShared_4828_ = v_isSharedCheck_5013_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_diag_4825_);
lean_inc(v_postponed_4824_);
lean_inc(v_zetaDeltaFVarIds_4823_);
lean_inc(v_mctx_4822_);
lean_dec(v___x_4821_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_5013_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4829_; lean_object* v___x_4831_; 
v___x_4829_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5);
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 1, v___x_4829_);
v___x_4831_ = v___x_4827_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_5012_; 
v_reuseFailAlloc_5012_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5012_, 0, v_mctx_4822_);
lean_ctor_set(v_reuseFailAlloc_5012_, 1, v___x_4829_);
lean_ctor_set(v_reuseFailAlloc_5012_, 2, v_zetaDeltaFVarIds_4823_);
lean_ctor_set(v_reuseFailAlloc_5012_, 3, v_postponed_4824_);
lean_ctor_set(v_reuseFailAlloc_5012_, 4, v_diag_4825_);
v___x_4831_ = v_reuseFailAlloc_5012_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v_mctx_4834_; lean_object* v_cache_4835_; lean_object* v_zetaDeltaFVarIds_4836_; lean_object* v_postponed_4837_; lean_object* v_diag_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_5011_; 
v___x_4832_ = lean_st_ref_set(v___y_4813_, v___x_4831_);
v___x_4833_ = lean_st_ref_take(v___y_4813_);
v_mctx_4834_ = lean_ctor_get(v___x_4833_, 0);
v_cache_4835_ = lean_ctor_get(v___x_4833_, 1);
v_zetaDeltaFVarIds_4836_ = lean_ctor_get(v___x_4833_, 2);
v_postponed_4837_ = lean_ctor_get(v___x_4833_, 3);
v_diag_4838_ = lean_ctor_get(v___x_4833_, 4);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_4840_ = v___x_4833_;
v_isShared_4841_ = v_isSharedCheck_5011_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_diag_4838_);
lean_inc(v_postponed_4837_);
lean_inc(v_zetaDeltaFVarIds_4836_);
lean_inc(v_cache_4835_);
lean_inc(v_mctx_4834_);
lean_dec(v___x_4833_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_5011_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4842_; lean_object* v___x_4844_; 
v___x_4842_ = lean_box(1);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 2, v___x_4842_);
v___x_4844_ = v___x_4840_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_mctx_4834_);
lean_ctor_set(v_reuseFailAlloc_5010_, 1, v_cache_4835_);
lean_ctor_set(v_reuseFailAlloc_5010_, 2, v___x_4842_);
lean_ctor_set(v_reuseFailAlloc_5010_, 3, v_postponed_4837_);
lean_ctor_set(v_reuseFailAlloc_5010_, 4, v_diag_4838_);
v___x_4844_ = v_reuseFailAlloc_5010_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_object* v___x_4845_; lean_object* v_cache_4846_; lean_object* v_keyedConfig_4847_; lean_object* v_zetaDeltaSet_4848_; lean_object* v_lctx_4849_; lean_object* v_localInstances_4850_; lean_object* v_defEqCtx_x3f_4851_; lean_object* v_synthPendingDepth_4852_; lean_object* v_canUnfold_x3f_4853_; uint8_t v_univApprox_4854_; uint8_t v_inTypeClassResolution_4855_; uint8_t v_cacheInferType_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; uint8_t v_foApprox_4859_; uint8_t v_ctxApprox_4860_; uint8_t v_quasiPatternApprox_4861_; uint8_t v_constApprox_4862_; uint8_t v_isDefEqStuckEx_4863_; uint8_t v_unificationHints_4864_; uint8_t v_proofIrrelevance_4865_; uint8_t v_assignSyntheticOpaque_4866_; uint8_t v_offsetCnstrs_4867_; uint8_t v_etaStruct_4868_; uint8_t v_univApprox_4869_; uint8_t v_iota_4870_; uint8_t v_beta_4871_; uint8_t v_proj_4872_; uint8_t v_zeta_4873_; uint8_t v_zetaDelta_4874_; uint8_t v_zetaUnused_4875_; uint8_t v_zetaHave_4876_; lean_object* v___x_4878_; uint8_t v_isShared_4879_; uint8_t v_isSharedCheck_5009_; 
v___x_4845_ = lean_st_ref_set(v___y_4813_, v___x_4844_);
v_cache_4846_ = lean_ctor_get(v___x_4820_, 1);
lean_inc_ref(v_cache_4846_);
lean_dec(v___x_4820_);
v_keyedConfig_4847_ = lean_ctor_get(v___y_4812_, 0);
v_zetaDeltaSet_4848_ = lean_ctor_get(v___y_4812_, 1);
v_lctx_4849_ = lean_ctor_get(v___y_4812_, 2);
v_localInstances_4850_ = lean_ctor_get(v___y_4812_, 3);
v_defEqCtx_x3f_4851_ = lean_ctor_get(v___y_4812_, 4);
v_synthPendingDepth_4852_ = lean_ctor_get(v___y_4812_, 5);
v_canUnfold_x3f_4853_ = lean_ctor_get(v___y_4812_, 6);
v_univApprox_4854_ = lean_ctor_get_uint8(v___y_4812_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4855_ = lean_ctor_get_uint8(v___y_4812_, sizeof(void*)*7 + 2);
v_cacheInferType_4856_ = lean_ctor_get_uint8(v___y_4812_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_4853_);
lean_inc(v_synthPendingDepth_4852_);
lean_inc(v_defEqCtx_x3f_4851_);
lean_inc_ref(v_localInstances_4850_);
lean_inc_ref(v_lctx_4849_);
lean_inc(v_zetaDeltaSet_4848_);
lean_inc_ref(v_keyedConfig_4847_);
v___x_4857_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4857_, 0, v_keyedConfig_4847_);
lean_ctor_set(v___x_4857_, 1, v_zetaDeltaSet_4848_);
lean_ctor_set(v___x_4857_, 2, v_lctx_4849_);
lean_ctor_set(v___x_4857_, 3, v_localInstances_4850_);
lean_ctor_set(v___x_4857_, 4, v_defEqCtx_x3f_4851_);
lean_ctor_set(v___x_4857_, 5, v_synthPendingDepth_4852_);
lean_ctor_set(v___x_4857_, 6, v_canUnfold_x3f_4853_);
lean_ctor_set_uint8(v___x_4857_, sizeof(void*)*7, v___x_4810_);
lean_ctor_set_uint8(v___x_4857_, sizeof(void*)*7 + 1, v_univApprox_4854_);
lean_ctor_set_uint8(v___x_4857_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4855_);
lean_ctor_set_uint8(v___x_4857_, sizeof(void*)*7 + 3, v_cacheInferType_4856_);
v___x_4858_ = l_Lean_Meta_Context_config(v___x_4857_);
v_foApprox_4859_ = lean_ctor_get_uint8(v___x_4858_, 0);
v_ctxApprox_4860_ = lean_ctor_get_uint8(v___x_4858_, 1);
v_quasiPatternApprox_4861_ = lean_ctor_get_uint8(v___x_4858_, 2);
v_constApprox_4862_ = lean_ctor_get_uint8(v___x_4858_, 3);
v_isDefEqStuckEx_4863_ = lean_ctor_get_uint8(v___x_4858_, 4);
v_unificationHints_4864_ = lean_ctor_get_uint8(v___x_4858_, 5);
v_proofIrrelevance_4865_ = lean_ctor_get_uint8(v___x_4858_, 6);
v_assignSyntheticOpaque_4866_ = lean_ctor_get_uint8(v___x_4858_, 7);
v_offsetCnstrs_4867_ = lean_ctor_get_uint8(v___x_4858_, 8);
v_etaStruct_4868_ = lean_ctor_get_uint8(v___x_4858_, 10);
v_univApprox_4869_ = lean_ctor_get_uint8(v___x_4858_, 11);
v_iota_4870_ = lean_ctor_get_uint8(v___x_4858_, 12);
v_beta_4871_ = lean_ctor_get_uint8(v___x_4858_, 13);
v_proj_4872_ = lean_ctor_get_uint8(v___x_4858_, 14);
v_zeta_4873_ = lean_ctor_get_uint8(v___x_4858_, 15);
v_zetaDelta_4874_ = lean_ctor_get_uint8(v___x_4858_, 16);
v_zetaUnused_4875_ = lean_ctor_get_uint8(v___x_4858_, 17);
v_zetaHave_4876_ = lean_ctor_get_uint8(v___x_4858_, 18);
v_isSharedCheck_5009_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_4878_ = v___x_4858_;
v_isShared_4879_ = v_isSharedCheck_5009_;
goto v_resetjp_4877_;
}
else
{
lean_dec(v___x_4858_);
v___x_4878_ = lean_box(0);
v_isShared_4879_ = v_isSharedCheck_5009_;
goto v_resetjp_4877_;
}
v_resetjp_4877_:
{
uint8_t v___x_4880_; lean_object* v_config_4882_; 
v___x_4880_ = 0;
if (v_isShared_4879_ == 0)
{
v_config_4882_ = v___x_4878_;
goto v_reusejp_4881_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 0, v_foApprox_4859_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 1, v_ctxApprox_4860_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 2, v_quasiPatternApprox_4861_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 3, v_constApprox_4862_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 4, v_isDefEqStuckEx_4863_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 5, v_unificationHints_4864_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 6, v_proofIrrelevance_4865_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 7, v_assignSyntheticOpaque_4866_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 8, v_offsetCnstrs_4867_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 10, v_etaStruct_4868_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 11, v_univApprox_4869_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 12, v_iota_4870_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 13, v_beta_4871_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 14, v_proj_4872_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 15, v_zeta_4873_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 16, v_zetaDelta_4874_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 17, v_zetaUnused_4875_);
lean_ctor_set_uint8(v_reuseFailAlloc_5008_, 18, v_zetaHave_4876_);
v_config_4882_ = v_reuseFailAlloc_5008_;
goto v_reusejp_4881_;
}
v_reusejp_4881_:
{
uint64_t v___x_4883_; uint64_t v___x_4884_; uint64_t v___x_4885_; uint64_t v___x_4886_; uint64_t v___x_4887_; uint64_t v_key_4888_; lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; uint8_t v_transparency_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v_a_4897_; lean_object* v___y_4909_; lean_object* v___y_4932_; uint8_t v___y_4960_; uint8_t v___x_5006_; uint8_t v___x_5007_; 
lean_ctor_set_uint8(v_config_4882_, 9, v___x_4880_);
v___x_4883_ = l_Lean_Meta_Context_configKey(v___x_4857_);
lean_dec_ref_known(v___x_4857_, 7);
v___x_4884_ = 3ULL;
v___x_4885_ = lean_uint64_shift_right(v___x_4883_, v___x_4884_);
v___x_4886_ = lean_uint64_shift_left(v___x_4885_, v___x_4884_);
v___x_4887_ = lean_uint64_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6);
v_key_4888_ = lean_uint64_lor(v___x_4886_, v___x_4887_);
v___x_4889_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4889_, 0, v_config_4882_);
lean_ctor_set_uint64(v___x_4889_, sizeof(void*)*1, v_key_4888_);
lean_inc(v_canUnfold_x3f_4853_);
lean_inc(v_synthPendingDepth_4852_);
lean_inc(v_defEqCtx_x3f_4851_);
lean_inc_ref(v_localInstances_4850_);
lean_inc_ref(v_lctx_4849_);
lean_inc(v_zetaDeltaSet_4848_);
v___x_4890_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4890_, 0, v___x_4889_);
lean_ctor_set(v___x_4890_, 1, v_zetaDeltaSet_4848_);
lean_ctor_set(v___x_4890_, 2, v_lctx_4849_);
lean_ctor_set(v___x_4890_, 3, v_localInstances_4850_);
lean_ctor_set(v___x_4890_, 4, v_defEqCtx_x3f_4851_);
lean_ctor_set(v___x_4890_, 5, v_synthPendingDepth_4852_);
lean_ctor_set(v___x_4890_, 6, v_canUnfold_x3f_4853_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*7, v___x_4810_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*7 + 1, v_univApprox_4854_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4855_);
lean_ctor_set_uint8(v___x_4890_, sizeof(void*)*7 + 3, v_cacheInferType_4856_);
v___x_4891_ = l_Lean_Meta_Context_config(v___x_4890_);
v_transparency_4892_ = lean_ctor_get_uint8(v___x_4891_, 9);
v___x_4893_ = lean_unsigned_to_nat(0u);
v___x_4894_ = lean_box(0);
v___x_4895_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7);
v___x_5006_ = 1;
v___x_5007_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4892_, v___x_5006_);
if (v___x_5007_ == 0)
{
v___y_4960_ = v_transparency_4892_;
goto v___jp_4959_;
}
else
{
v___y_4960_ = v___x_5006_;
goto v___jp_4959_;
}
v___jp_4896_:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
v___x_4898_ = lean_box(0);
v___x_4899_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4813_, v_cache_4846_, v___x_4898_);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4906_ == 0)
{
lean_object* v_unused_4907_; 
v_unused_4907_ = lean_ctor_get(v___x_4899_, 0);
lean_dec(v_unused_4907_);
v___x_4901_ = v___x_4899_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_dec(v___x_4899_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
lean_ctor_set_tag(v___x_4901_, 1);
lean_ctor_set(v___x_4901_, 0, v_a_4897_);
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4897_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
v___jp_4908_:
{
if (lean_obj_tag(v___y_4909_) == 0)
{
lean_object* v_a_4910_; lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4927_; 
v_a_4910_ = lean_ctor_get(v___y_4909_, 0);
v_isSharedCheck_4927_ = !lean_is_exclusive(v___y_4909_);
if (v_isSharedCheck_4927_ == 0)
{
v___x_4912_ = v___y_4909_;
v_isShared_4913_ = v_isSharedCheck_4927_;
goto v_resetjp_4911_;
}
else
{
lean_inc(v_a_4910_);
lean_dec(v___y_4909_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4927_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4915_; 
lean_inc(v_a_4910_);
if (v_isShared_4913_ == 0)
{
lean_ctor_set_tag(v___x_4912_, 1);
v___x_4915_ = v___x_4912_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4926_; 
v_reuseFailAlloc_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4926_, 0, v_a_4910_);
v___x_4915_ = v_reuseFailAlloc_4926_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4919_; uint8_t v_isShared_4920_; uint8_t v_isSharedCheck_4924_; 
v___x_4916_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4813_, v_zetaDeltaFVarIds_4836_, v___x_4915_);
lean_dec_ref(v___x_4916_);
v___x_4917_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4813_, v_cache_4846_, v___x_4915_);
lean_dec_ref(v___x_4915_);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___x_4917_);
if (v_isSharedCheck_4924_ == 0)
{
lean_object* v_unused_4925_; 
v_unused_4925_ = lean_ctor_get(v___x_4917_, 0);
lean_dec(v_unused_4925_);
v___x_4919_ = v___x_4917_;
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
else
{
lean_dec(v___x_4917_);
v___x_4919_ = lean_box(0);
v_isShared_4920_ = v_isSharedCheck_4924_;
goto v_resetjp_4918_;
}
v_resetjp_4918_:
{
lean_object* v___x_4922_; 
if (v_isShared_4920_ == 0)
{
lean_ctor_set(v___x_4919_, 0, v_a_4910_);
v___x_4922_ = v___x_4919_;
goto v_reusejp_4921_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4910_);
v___x_4922_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4921_;
}
v_reusejp_4921_:
{
return v___x_4922_;
}
}
}
}
}
else
{
lean_object* v_a_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; 
v_a_4928_ = lean_ctor_get(v___y_4909_, 0);
lean_inc(v_a_4928_);
lean_dec_ref_known(v___y_4909_, 1);
v___x_4929_ = lean_box(0);
v___x_4930_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4813_, v_zetaDeltaFVarIds_4836_, v___x_4929_);
lean_dec_ref(v___x_4930_);
v_a_4897_ = v_a_4928_;
goto v___jp_4896_;
}
}
v___jp_4931_:
{
lean_object* v___x_4933_; uint8_t v_foApprox_4934_; uint8_t v_ctxApprox_4935_; uint8_t v_quasiPatternApprox_4936_; uint8_t v_constApprox_4937_; uint8_t v_isDefEqStuckEx_4938_; uint8_t v_unificationHints_4939_; uint8_t v_proofIrrelevance_4940_; uint8_t v_assignSyntheticOpaque_4941_; uint8_t v_offsetCnstrs_4942_; uint8_t v_transparency_4943_; uint8_t v_univApprox_4944_; uint8_t v_zetaUnused_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4958_; 
v___x_4933_ = l_Lean_Meta_Context_config(v___y_4932_);
lean_dec_ref(v___y_4932_);
v_foApprox_4934_ = lean_ctor_get_uint8(v___x_4933_, 0);
v_ctxApprox_4935_ = lean_ctor_get_uint8(v___x_4933_, 1);
v_quasiPatternApprox_4936_ = lean_ctor_get_uint8(v___x_4933_, 2);
v_constApprox_4937_ = lean_ctor_get_uint8(v___x_4933_, 3);
v_isDefEqStuckEx_4938_ = lean_ctor_get_uint8(v___x_4933_, 4);
v_unificationHints_4939_ = lean_ctor_get_uint8(v___x_4933_, 5);
v_proofIrrelevance_4940_ = lean_ctor_get_uint8(v___x_4933_, 6);
v_assignSyntheticOpaque_4941_ = lean_ctor_get_uint8(v___x_4933_, 7);
v_offsetCnstrs_4942_ = lean_ctor_get_uint8(v___x_4933_, 8);
v_transparency_4943_ = lean_ctor_get_uint8(v___x_4933_, 9);
v_univApprox_4944_ = lean_ctor_get_uint8(v___x_4933_, 11);
v_zetaUnused_4945_ = lean_ctor_get_uint8(v___x_4933_, 17);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4933_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4947_ = v___x_4933_;
v_isShared_4948_ = v_isSharedCheck_4958_;
goto v_resetjp_4946_;
}
else
{
lean_dec(v___x_4933_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4958_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
uint8_t v___x_4949_; uint8_t v___x_4950_; lean_object* v___x_4952_; 
v___x_4949_ = 0;
v___x_4950_ = 2;
if (v_isShared_4948_ == 0)
{
v___x_4952_ = v___x_4947_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4957_; 
v_reuseFailAlloc_4957_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 0, v_foApprox_4934_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 1, v_ctxApprox_4935_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 2, v_quasiPatternApprox_4936_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 3, v_constApprox_4937_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 4, v_isDefEqStuckEx_4938_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 5, v_unificationHints_4939_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 6, v_proofIrrelevance_4940_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 7, v_assignSyntheticOpaque_4941_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 8, v_offsetCnstrs_4942_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 9, v_transparency_4943_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 11, v_univApprox_4944_);
lean_ctor_set_uint8(v_reuseFailAlloc_4957_, 17, v_zetaUnused_4945_);
v___x_4952_ = v_reuseFailAlloc_4957_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
uint64_t v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; lean_object* v___x_4956_; 
lean_ctor_set_uint8(v___x_4952_, 10, v___x_4949_);
lean_ctor_set_uint8(v___x_4952_, 12, v___x_4810_);
lean_ctor_set_uint8(v___x_4952_, 13, v___x_4810_);
lean_ctor_set_uint8(v___x_4952_, 14, v___x_4950_);
lean_ctor_set_uint8(v___x_4952_, 15, v___x_4810_);
lean_ctor_set_uint8(v___x_4952_, 16, v___x_4810_);
lean_ctor_set_uint8(v___x_4952_, 18, v___x_4810_);
v___x_4953_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4952_);
v___x_4954_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4954_, 0, v___x_4952_);
lean_ctor_set_uint64(v___x_4954_, sizeof(void*)*1, v___x_4953_);
lean_inc(v_canUnfold_x3f_4853_);
lean_inc(v_synthPendingDepth_4852_);
lean_inc(v_defEqCtx_x3f_4851_);
lean_inc_ref(v_localInstances_4850_);
lean_inc_ref(v_lctx_4849_);
lean_inc(v_zetaDeltaSet_4848_);
v___x_4955_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4955_, 0, v___x_4954_);
lean_ctor_set(v___x_4955_, 1, v_zetaDeltaSet_4848_);
lean_ctor_set(v___x_4955_, 2, v_lctx_4849_);
lean_ctor_set(v___x_4955_, 3, v_localInstances_4850_);
lean_ctor_set(v___x_4955_, 4, v_defEqCtx_x3f_4851_);
lean_ctor_set(v___x_4955_, 5, v_synthPendingDepth_4852_);
lean_ctor_set(v___x_4955_, 6, v_canUnfold_x3f_4853_);
lean_ctor_set_uint8(v___x_4955_, sizeof(void*)*7, v___x_4810_);
lean_ctor_set_uint8(v___x_4955_, sizeof(void*)*7 + 1, v_univApprox_4854_);
lean_ctor_set_uint8(v___x_4955_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4855_);
lean_ctor_set_uint8(v___x_4955_, sizeof(void*)*7 + 3, v_cacheInferType_4856_);
v___x_4956_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4895_, v_e_4809_, v___x_4894_, v___x_4893_, v_cls_4811_, v___x_4955_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec_ref_known(v___x_4955_, 7);
v___y_4909_ = v___x_4956_;
goto v___jp_4908_;
}
}
}
v___jp_4959_:
{
uint8_t v_foApprox_4961_; uint8_t v_ctxApprox_4962_; uint8_t v_quasiPatternApprox_4963_; uint8_t v_constApprox_4964_; uint8_t v_isDefEqStuckEx_4965_; uint8_t v_unificationHints_4966_; uint8_t v_proofIrrelevance_4967_; uint8_t v_assignSyntheticOpaque_4968_; uint8_t v_offsetCnstrs_4969_; uint8_t v_etaStruct_4970_; uint8_t v_univApprox_4971_; uint8_t v_iota_4972_; uint8_t v_beta_4973_; uint8_t v_proj_4974_; uint8_t v_zeta_4975_; uint8_t v_zetaDelta_4976_; uint8_t v_zetaUnused_4977_; uint8_t v_zetaHave_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_5005_; 
v_foApprox_4961_ = lean_ctor_get_uint8(v___x_4891_, 0);
v_ctxApprox_4962_ = lean_ctor_get_uint8(v___x_4891_, 1);
v_quasiPatternApprox_4963_ = lean_ctor_get_uint8(v___x_4891_, 2);
v_constApprox_4964_ = lean_ctor_get_uint8(v___x_4891_, 3);
v_isDefEqStuckEx_4965_ = lean_ctor_get_uint8(v___x_4891_, 4);
v_unificationHints_4966_ = lean_ctor_get_uint8(v___x_4891_, 5);
v_proofIrrelevance_4967_ = lean_ctor_get_uint8(v___x_4891_, 6);
v_assignSyntheticOpaque_4968_ = lean_ctor_get_uint8(v___x_4891_, 7);
v_offsetCnstrs_4969_ = lean_ctor_get_uint8(v___x_4891_, 8);
v_etaStruct_4970_ = lean_ctor_get_uint8(v___x_4891_, 10);
v_univApprox_4971_ = lean_ctor_get_uint8(v___x_4891_, 11);
v_iota_4972_ = lean_ctor_get_uint8(v___x_4891_, 12);
v_beta_4973_ = lean_ctor_get_uint8(v___x_4891_, 13);
v_proj_4974_ = lean_ctor_get_uint8(v___x_4891_, 14);
v_zeta_4975_ = lean_ctor_get_uint8(v___x_4891_, 15);
v_zetaDelta_4976_ = lean_ctor_get_uint8(v___x_4891_, 16);
v_zetaUnused_4977_ = lean_ctor_get_uint8(v___x_4891_, 17);
v_zetaHave_4978_ = lean_ctor_get_uint8(v___x_4891_, 18);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4891_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4980_ = v___x_4891_;
v_isShared_4981_ = v_isSharedCheck_5005_;
goto v_resetjp_4979_;
}
else
{
lean_dec(v___x_4891_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_5005_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v_config_4983_; 
if (v_isShared_4981_ == 0)
{
v_config_4983_ = v___x_4980_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 0, v_foApprox_4961_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 1, v_ctxApprox_4962_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 2, v_quasiPatternApprox_4963_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 3, v_constApprox_4964_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 4, v_isDefEqStuckEx_4965_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 5, v_unificationHints_4966_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 6, v_proofIrrelevance_4967_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 7, v_assignSyntheticOpaque_4968_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 8, v_offsetCnstrs_4969_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 10, v_etaStruct_4970_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 11, v_univApprox_4971_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 12, v_iota_4972_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 13, v_beta_4973_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 14, v_proj_4974_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 15, v_zeta_4975_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 16, v_zetaDelta_4976_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 17, v_zetaUnused_4977_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 18, v_zetaHave_4978_);
v_config_4983_ = v_reuseFailAlloc_5004_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
uint64_t v___x_4984_; uint64_t v___x_4985_; uint64_t v___x_4986_; uint64_t v___x_4987_; uint64_t v_key_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; uint8_t v_beta_4992_; 
lean_ctor_set_uint8(v_config_4983_, 9, v___y_4960_);
v___x_4984_ = l_Lean_Meta_Context_configKey(v___x_4890_);
lean_dec_ref_known(v___x_4890_, 7);
v___x_4985_ = lean_uint64_shift_right(v___x_4984_, v___x_4884_);
v___x_4986_ = lean_uint64_shift_left(v___x_4985_, v___x_4884_);
v___x_4987_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_4960_);
v_key_4988_ = lean_uint64_lor(v___x_4986_, v___x_4987_);
v___x_4989_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4989_, 0, v_config_4983_);
lean_ctor_set_uint64(v___x_4989_, sizeof(void*)*1, v_key_4988_);
lean_inc(v_canUnfold_x3f_4853_);
lean_inc(v_synthPendingDepth_4852_);
lean_inc(v_defEqCtx_x3f_4851_);
lean_inc_ref(v_localInstances_4850_);
lean_inc_ref(v_lctx_4849_);
lean_inc(v_zetaDeltaSet_4848_);
v___x_4990_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4990_, 0, v___x_4989_);
lean_ctor_set(v___x_4990_, 1, v_zetaDeltaSet_4848_);
lean_ctor_set(v___x_4990_, 2, v_lctx_4849_);
lean_ctor_set(v___x_4990_, 3, v_localInstances_4850_);
lean_ctor_set(v___x_4990_, 4, v_defEqCtx_x3f_4851_);
lean_ctor_set(v___x_4990_, 5, v_synthPendingDepth_4852_);
lean_ctor_set(v___x_4990_, 6, v_canUnfold_x3f_4853_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7, v___x_4810_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7 + 1, v_univApprox_4854_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4855_);
lean_ctor_set_uint8(v___x_4990_, sizeof(void*)*7 + 3, v_cacheInferType_4856_);
v___x_4991_ = l_Lean_Meta_Context_config(v___x_4990_);
v_beta_4992_ = lean_ctor_get_uint8(v___x_4991_, 13);
if (v_beta_4992_ == 0)
{
lean_dec_ref(v___x_4991_);
v___y_4932_ = v___x_4990_;
goto v___jp_4931_;
}
else
{
uint8_t v_iota_4993_; 
v_iota_4993_ = lean_ctor_get_uint8(v___x_4991_, 12);
if (v_iota_4993_ == 0)
{
lean_dec_ref(v___x_4991_);
v___y_4932_ = v___x_4990_;
goto v___jp_4931_;
}
else
{
uint8_t v_zeta_4994_; 
v_zeta_4994_ = lean_ctor_get_uint8(v___x_4991_, 15);
if (v_zeta_4994_ == 0)
{
lean_dec_ref(v___x_4991_);
v___y_4932_ = v___x_4990_;
goto v___jp_4931_;
}
else
{
uint8_t v_zetaHave_4995_; 
v_zetaHave_4995_ = lean_ctor_get_uint8(v___x_4991_, 18);
if (v_zetaHave_4995_ == 0)
{
lean_dec_ref(v___x_4991_);
v___y_4932_ = v___x_4990_;
goto v___jp_4931_;
}
else
{
uint8_t v_zetaDelta_4996_; 
v_zetaDelta_4996_ = lean_ctor_get_uint8(v___x_4991_, 16);
if (v_zetaDelta_4996_ == 0)
{
lean_dec_ref(v___x_4991_);
v___y_4932_ = v___x_4990_;
goto v___jp_4931_;
}
else
{
uint8_t v_etaStruct_4997_; uint8_t v_proj_4998_; uint8_t v___x_4999_; uint8_t v___x_5000_; 
v_etaStruct_4997_ = lean_ctor_get_uint8(v___x_4991_, 10);
v_proj_4998_ = lean_ctor_get_uint8(v___x_4991_, 14);
lean_dec_ref(v___x_4991_);
v___x_4999_ = 2;
v___x_5000_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_4998_, v___x_4999_);
if (v___x_5000_ == 0)
{
v___y_4932_ = v___x_4990_;
goto v___jp_4931_;
}
else
{
uint8_t v___x_5001_; uint8_t v___x_5002_; 
v___x_5001_ = 0;
v___x_5002_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4997_, v___x_5001_);
if (v___x_5002_ == 0)
{
v___y_4932_ = v___x_4990_;
goto v___jp_4931_;
}
else
{
lean_object* v___x_5003_; 
v___x_5003_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4895_, v_e_4809_, v___x_4894_, v___x_4893_, v_cls_4811_, v___x_4990_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec_ref_known(v___x_4990_, 7);
v___y_4909_ = v___x_5003_;
goto v___jp_4908_;
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
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_5015_, lean_object* v_e_5016_, lean_object* v___x_5017_, lean_object* v_cls_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_, lean_object* v___y_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_){
_start:
{
uint8_t v___x_14683__boxed_5024_; uint8_t v___x_14684__boxed_5025_; lean_object* v_res_5026_; 
v___x_14683__boxed_5024_ = lean_unbox(v___x_5015_);
v___x_14684__boxed_5025_ = lean_unbox(v___x_5017_);
v_res_5026_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_14683__boxed_5024_, v_e_5016_, v___x_14684__boxed_5025_, v_cls_5018_, v___y_5019_, v___y_5020_, v___y_5021_, v___y_5022_);
lean_dec(v___y_5022_);
lean_dec_ref(v___y_5021_);
lean_dec(v___y_5020_);
lean_dec_ref(v___y_5019_);
return v_res_5026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_, lean_object* v___y_5031_){
_start:
{
if (lean_obj_tag(v_x_5027_) == 0)
{
lean_object* v_a_5033_; lean_object* v___x_5035_; uint8_t v_isShared_5036_; uint8_t v_isSharedCheck_5041_; 
v_a_5033_ = lean_ctor_get(v_x_5027_, 0);
v_isSharedCheck_5041_ = !lean_is_exclusive(v_x_5027_);
if (v_isSharedCheck_5041_ == 0)
{
v___x_5035_ = v_x_5027_;
v_isShared_5036_ = v_isSharedCheck_5041_;
goto v_resetjp_5034_;
}
else
{
lean_inc(v_a_5033_);
lean_dec(v_x_5027_);
v___x_5035_ = lean_box(0);
v_isShared_5036_ = v_isSharedCheck_5041_;
goto v_resetjp_5034_;
}
v_resetjp_5034_:
{
lean_object* v___x_5037_; lean_object* v___x_5039_; 
v___x_5037_ = l_Lean_Exception_toMessageData(v_a_5033_);
if (v_isShared_5036_ == 0)
{
lean_ctor_set(v___x_5035_, 0, v___x_5037_);
v___x_5039_ = v___x_5035_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5040_; 
v_reuseFailAlloc_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5040_, 0, v___x_5037_);
v___x_5039_ = v_reuseFailAlloc_5040_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
return v___x_5039_;
}
}
}
else
{
lean_object* v_a_5042_; lean_object* v___x_5044_; uint8_t v_isShared_5045_; uint8_t v_isSharedCheck_5050_; 
v_a_5042_ = lean_ctor_get(v_x_5027_, 0);
v_isSharedCheck_5050_ = !lean_is_exclusive(v_x_5027_);
if (v_isSharedCheck_5050_ == 0)
{
v___x_5044_ = v_x_5027_;
v_isShared_5045_ = v_isSharedCheck_5050_;
goto v_resetjp_5043_;
}
else
{
lean_inc(v_a_5042_);
lean_dec(v_x_5027_);
v___x_5044_ = lean_box(0);
v_isShared_5045_ = v_isSharedCheck_5050_;
goto v_resetjp_5043_;
}
v_resetjp_5043_:
{
lean_object* v_snd_5046_; lean_object* v___x_5048_; 
v_snd_5046_ = lean_ctor_get(v_a_5042_, 1);
lean_inc(v_snd_5046_);
lean_dec(v_a_5042_);
if (v_isShared_5045_ == 0)
{
lean_ctor_set_tag(v___x_5044_, 0);
lean_ctor_set(v___x_5044_, 0, v_snd_5046_);
v___x_5048_ = v___x_5044_;
goto v_reusejp_5047_;
}
else
{
lean_object* v_reuseFailAlloc_5049_; 
v_reuseFailAlloc_5049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5049_, 0, v_snd_5046_);
v___x_5048_ = v_reuseFailAlloc_5049_;
goto v_reusejp_5047_;
}
v_reusejp_5047_:
{
return v___x_5048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec_ref(v___y_5054_);
lean_dec(v___y_5053_);
lean_dec_ref(v___y_5052_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_oldTraces_5058_, lean_object* v_data_5059_, lean_object* v_ref_5060_, lean_object* v_msg_5061_, lean_object* v___y_5062_, lean_object* v___y_5063_, lean_object* v___y_5064_, lean_object* v___y_5065_){
_start:
{
lean_object* v_fileName_5067_; lean_object* v_fileMap_5068_; lean_object* v_options_5069_; lean_object* v_currRecDepth_5070_; lean_object* v_maxRecDepth_5071_; lean_object* v_ref_5072_; lean_object* v_currNamespace_5073_; lean_object* v_openDecls_5074_; lean_object* v_initHeartbeats_5075_; lean_object* v_maxHeartbeats_5076_; lean_object* v_quotContext_5077_; lean_object* v_currMacroScope_5078_; uint8_t v_diag_5079_; lean_object* v_cancelTk_x3f_5080_; uint8_t v_suppressElabErrors_5081_; lean_object* v_inheritedTraceOptions_5082_; lean_object* v___x_5083_; lean_object* v_traceState_5084_; lean_object* v_traces_5085_; lean_object* v_ref_5086_; lean_object* v___x_5087_; lean_object* v___x_5088_; size_t v_sz_5089_; size_t v___x_5090_; lean_object* v___x_5091_; lean_object* v_msg_5092_; lean_object* v___x_5093_; lean_object* v_a_5094_; lean_object* v___x_5096_; uint8_t v_isShared_5097_; uint8_t v_isSharedCheck_5131_; 
v_fileName_5067_ = lean_ctor_get(v___y_5064_, 0);
v_fileMap_5068_ = lean_ctor_get(v___y_5064_, 1);
v_options_5069_ = lean_ctor_get(v___y_5064_, 2);
v_currRecDepth_5070_ = lean_ctor_get(v___y_5064_, 3);
v_maxRecDepth_5071_ = lean_ctor_get(v___y_5064_, 4);
v_ref_5072_ = lean_ctor_get(v___y_5064_, 5);
v_currNamespace_5073_ = lean_ctor_get(v___y_5064_, 6);
v_openDecls_5074_ = lean_ctor_get(v___y_5064_, 7);
v_initHeartbeats_5075_ = lean_ctor_get(v___y_5064_, 8);
v_maxHeartbeats_5076_ = lean_ctor_get(v___y_5064_, 9);
v_quotContext_5077_ = lean_ctor_get(v___y_5064_, 10);
v_currMacroScope_5078_ = lean_ctor_get(v___y_5064_, 11);
v_diag_5079_ = lean_ctor_get_uint8(v___y_5064_, sizeof(void*)*14);
v_cancelTk_x3f_5080_ = lean_ctor_get(v___y_5064_, 12);
v_suppressElabErrors_5081_ = lean_ctor_get_uint8(v___y_5064_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5082_ = lean_ctor_get(v___y_5064_, 13);
v___x_5083_ = lean_st_ref_get(v___y_5065_);
v_traceState_5084_ = lean_ctor_get(v___x_5083_, 4);
lean_inc_ref(v_traceState_5084_);
lean_dec(v___x_5083_);
v_traces_5085_ = lean_ctor_get(v_traceState_5084_, 0);
lean_inc_ref(v_traces_5085_);
lean_dec_ref(v_traceState_5084_);
v_ref_5086_ = l_Lean_replaceRef(v_ref_5060_, v_ref_5072_);
lean_inc_ref(v_inheritedTraceOptions_5082_);
lean_inc(v_cancelTk_x3f_5080_);
lean_inc(v_currMacroScope_5078_);
lean_inc(v_quotContext_5077_);
lean_inc(v_maxHeartbeats_5076_);
lean_inc(v_initHeartbeats_5075_);
lean_inc(v_openDecls_5074_);
lean_inc(v_currNamespace_5073_);
lean_inc(v_maxRecDepth_5071_);
lean_inc(v_currRecDepth_5070_);
lean_inc_ref(v_options_5069_);
lean_inc_ref(v_fileMap_5068_);
lean_inc_ref(v_fileName_5067_);
v___x_5087_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5087_, 0, v_fileName_5067_);
lean_ctor_set(v___x_5087_, 1, v_fileMap_5068_);
lean_ctor_set(v___x_5087_, 2, v_options_5069_);
lean_ctor_set(v___x_5087_, 3, v_currRecDepth_5070_);
lean_ctor_set(v___x_5087_, 4, v_maxRecDepth_5071_);
lean_ctor_set(v___x_5087_, 5, v_ref_5086_);
lean_ctor_set(v___x_5087_, 6, v_currNamespace_5073_);
lean_ctor_set(v___x_5087_, 7, v_openDecls_5074_);
lean_ctor_set(v___x_5087_, 8, v_initHeartbeats_5075_);
lean_ctor_set(v___x_5087_, 9, v_maxHeartbeats_5076_);
lean_ctor_set(v___x_5087_, 10, v_quotContext_5077_);
lean_ctor_set(v___x_5087_, 11, v_currMacroScope_5078_);
lean_ctor_set(v___x_5087_, 12, v_cancelTk_x3f_5080_);
lean_ctor_set(v___x_5087_, 13, v_inheritedTraceOptions_5082_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*14, v_diag_5079_);
lean_ctor_set_uint8(v___x_5087_, sizeof(void*)*14 + 1, v_suppressElabErrors_5081_);
v___x_5088_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5085_);
lean_dec_ref(v_traces_5085_);
v_sz_5089_ = lean_array_size(v___x_5088_);
v___x_5090_ = ((size_t)0ULL);
v___x_5091_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(v_sz_5089_, v___x_5090_, v___x_5088_);
v_msg_5092_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5092_, 0, v_data_5059_);
lean_ctor_set(v_msg_5092_, 1, v_msg_5061_);
lean_ctor_set(v_msg_5092_, 2, v___x_5091_);
v___x_5093_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5092_, v___y_5062_, v___y_5063_, v___x_5087_, v___y_5065_);
lean_dec_ref_known(v___x_5087_, 14);
v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
v_isSharedCheck_5131_ = !lean_is_exclusive(v___x_5093_);
if (v_isSharedCheck_5131_ == 0)
{
v___x_5096_ = v___x_5093_;
v_isShared_5097_ = v_isSharedCheck_5131_;
goto v_resetjp_5095_;
}
else
{
lean_inc(v_a_5094_);
lean_dec(v___x_5093_);
v___x_5096_ = lean_box(0);
v_isShared_5097_ = v_isSharedCheck_5131_;
goto v_resetjp_5095_;
}
v_resetjp_5095_:
{
lean_object* v___x_5098_; lean_object* v_traceState_5099_; lean_object* v_env_5100_; lean_object* v_nextMacroScope_5101_; lean_object* v_ngen_5102_; lean_object* v_auxDeclNGen_5103_; lean_object* v_cache_5104_; lean_object* v_messages_5105_; lean_object* v_infoState_5106_; lean_object* v_snapshotTasks_5107_; lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5130_; 
v___x_5098_ = lean_st_ref_take(v___y_5065_);
v_traceState_5099_ = lean_ctor_get(v___x_5098_, 4);
v_env_5100_ = lean_ctor_get(v___x_5098_, 0);
v_nextMacroScope_5101_ = lean_ctor_get(v___x_5098_, 1);
v_ngen_5102_ = lean_ctor_get(v___x_5098_, 2);
v_auxDeclNGen_5103_ = lean_ctor_get(v___x_5098_, 3);
v_cache_5104_ = lean_ctor_get(v___x_5098_, 5);
v_messages_5105_ = lean_ctor_get(v___x_5098_, 6);
v_infoState_5106_ = lean_ctor_get(v___x_5098_, 7);
v_snapshotTasks_5107_ = lean_ctor_get(v___x_5098_, 8);
v_isSharedCheck_5130_ = !lean_is_exclusive(v___x_5098_);
if (v_isSharedCheck_5130_ == 0)
{
v___x_5109_ = v___x_5098_;
v_isShared_5110_ = v_isSharedCheck_5130_;
goto v_resetjp_5108_;
}
else
{
lean_inc(v_snapshotTasks_5107_);
lean_inc(v_infoState_5106_);
lean_inc(v_messages_5105_);
lean_inc(v_cache_5104_);
lean_inc(v_traceState_5099_);
lean_inc(v_auxDeclNGen_5103_);
lean_inc(v_ngen_5102_);
lean_inc(v_nextMacroScope_5101_);
lean_inc(v_env_5100_);
lean_dec(v___x_5098_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5130_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
uint64_t v_tid_5111_; lean_object* v___x_5113_; uint8_t v_isShared_5114_; uint8_t v_isSharedCheck_5128_; 
v_tid_5111_ = lean_ctor_get_uint64(v_traceState_5099_, sizeof(void*)*1);
v_isSharedCheck_5128_ = !lean_is_exclusive(v_traceState_5099_);
if (v_isSharedCheck_5128_ == 0)
{
lean_object* v_unused_5129_; 
v_unused_5129_ = lean_ctor_get(v_traceState_5099_, 0);
lean_dec(v_unused_5129_);
v___x_5113_ = v_traceState_5099_;
v_isShared_5114_ = v_isSharedCheck_5128_;
goto v_resetjp_5112_;
}
else
{
lean_dec(v_traceState_5099_);
v___x_5113_ = lean_box(0);
v_isShared_5114_ = v_isSharedCheck_5128_;
goto v_resetjp_5112_;
}
v_resetjp_5112_:
{
lean_object* v___x_5115_; lean_object* v___x_5116_; lean_object* v___x_5118_; 
v___x_5115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5115_, 0, v_ref_5060_);
lean_ctor_set(v___x_5115_, 1, v_a_5094_);
v___x_5116_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5058_, v___x_5115_);
if (v_isShared_5114_ == 0)
{
lean_ctor_set(v___x_5113_, 0, v___x_5116_);
v___x_5118_ = v___x_5113_;
goto v_reusejp_5117_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v___x_5116_);
lean_ctor_set_uint64(v_reuseFailAlloc_5127_, sizeof(void*)*1, v_tid_5111_);
v___x_5118_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5117_;
}
v_reusejp_5117_:
{
lean_object* v___x_5120_; 
if (v_isShared_5110_ == 0)
{
lean_ctor_set(v___x_5109_, 4, v___x_5118_);
v___x_5120_ = v___x_5109_;
goto v_reusejp_5119_;
}
else
{
lean_object* v_reuseFailAlloc_5126_; 
v_reuseFailAlloc_5126_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5126_, 0, v_env_5100_);
lean_ctor_set(v_reuseFailAlloc_5126_, 1, v_nextMacroScope_5101_);
lean_ctor_set(v_reuseFailAlloc_5126_, 2, v_ngen_5102_);
lean_ctor_set(v_reuseFailAlloc_5126_, 3, v_auxDeclNGen_5103_);
lean_ctor_set(v_reuseFailAlloc_5126_, 4, v___x_5118_);
lean_ctor_set(v_reuseFailAlloc_5126_, 5, v_cache_5104_);
lean_ctor_set(v_reuseFailAlloc_5126_, 6, v_messages_5105_);
lean_ctor_set(v_reuseFailAlloc_5126_, 7, v_infoState_5106_);
lean_ctor_set(v_reuseFailAlloc_5126_, 8, v_snapshotTasks_5107_);
v___x_5120_ = v_reuseFailAlloc_5126_;
goto v_reusejp_5119_;
}
v_reusejp_5119_:
{
lean_object* v___x_5121_; lean_object* v___x_5122_; lean_object* v___x_5124_; 
v___x_5121_ = lean_st_ref_set(v___y_5065_, v___x_5120_);
v___x_5122_ = lean_box(0);
if (v_isShared_5097_ == 0)
{
lean_ctor_set(v___x_5096_, 0, v___x_5122_);
v___x_5124_ = v___x_5096_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v___x_5122_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_oldTraces_5132_, lean_object* v_data_5133_, lean_object* v_ref_5134_, lean_object* v_msg_5135_, lean_object* v___y_5136_, lean_object* v___y_5137_, lean_object* v___y_5138_, lean_object* v___y_5139_, lean_object* v___y_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_oldTraces_5132_, v_data_5133_, v_ref_5134_, v_msg_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_);
lean_dec(v___y_5139_);
lean_dec_ref(v___y_5138_);
lean_dec(v___y_5137_);
lean_dec_ref(v___y_5136_);
return v_res_5141_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_e_5142_){
_start:
{
if (lean_obj_tag(v_e_5142_) == 0)
{
uint8_t v___x_5143_; 
v___x_5143_ = 2;
return v___x_5143_;
}
else
{
uint8_t v___x_5144_; 
v___x_5144_ = 0;
return v___x_5144_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_e_5145_){
_start:
{
uint8_t v_res_5146_; lean_object* v_r_5147_; 
v_res_5146_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_e_5145_);
lean_dec_ref(v_e_5145_);
v_r_5147_ = lean_box(v_res_5146_);
return v_r_5147_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg(lean_object* v_x_5148_){
_start:
{
if (lean_obj_tag(v_x_5148_) == 0)
{
lean_object* v_a_5150_; lean_object* v___x_5152_; uint8_t v_isShared_5153_; uint8_t v_isSharedCheck_5157_; 
v_a_5150_ = lean_ctor_get(v_x_5148_, 0);
v_isSharedCheck_5157_ = !lean_is_exclusive(v_x_5148_);
if (v_isSharedCheck_5157_ == 0)
{
v___x_5152_ = v_x_5148_;
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
else
{
lean_inc(v_a_5150_);
lean_dec(v_x_5148_);
v___x_5152_ = lean_box(0);
v_isShared_5153_ = v_isSharedCheck_5157_;
goto v_resetjp_5151_;
}
v_resetjp_5151_:
{
lean_object* v___x_5155_; 
if (v_isShared_5153_ == 0)
{
lean_ctor_set_tag(v___x_5152_, 1);
v___x_5155_ = v___x_5152_;
goto v_reusejp_5154_;
}
else
{
lean_object* v_reuseFailAlloc_5156_; 
v_reuseFailAlloc_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5156_, 0, v_a_5150_);
v___x_5155_ = v_reuseFailAlloc_5156_;
goto v_reusejp_5154_;
}
v_reusejp_5154_:
{
return v___x_5155_;
}
}
}
else
{
lean_object* v_a_5158_; lean_object* v___x_5160_; uint8_t v_isShared_5161_; uint8_t v_isSharedCheck_5165_; 
v_a_5158_ = lean_ctor_get(v_x_5148_, 0);
v_isSharedCheck_5165_ = !lean_is_exclusive(v_x_5148_);
if (v_isSharedCheck_5165_ == 0)
{
v___x_5160_ = v_x_5148_;
v_isShared_5161_ = v_isSharedCheck_5165_;
goto v_resetjp_5159_;
}
else
{
lean_inc(v_a_5158_);
lean_dec(v_x_5148_);
v___x_5160_ = lean_box(0);
v_isShared_5161_ = v_isSharedCheck_5165_;
goto v_resetjp_5159_;
}
v_resetjp_5159_:
{
lean_object* v___x_5163_; 
if (v_isShared_5161_ == 0)
{
lean_ctor_set_tag(v___x_5160_, 0);
v___x_5163_ = v___x_5160_;
goto v_reusejp_5162_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_a_5158_);
v___x_5163_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5162_;
}
v_reusejp_5162_:
{
return v___x_5163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg___boxed(lean_object* v_x_5166_, lean_object* v___y_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg(v_x_5166_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5169_, uint8_t v_collapsed_5170_, lean_object* v_tag_5171_, lean_object* v_opts_5172_, uint8_t v_clsEnabled_5173_, lean_object* v_oldTraces_5174_, lean_object* v_msg_5175_, lean_object* v_resStartStop_5176_, lean_object* v___y_5177_, lean_object* v___y_5178_, lean_object* v___y_5179_, lean_object* v___y_5180_){
_start:
{
lean_object* v_fst_5182_; lean_object* v_snd_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5281_; 
v_fst_5182_ = lean_ctor_get(v_resStartStop_5176_, 0);
v_snd_5183_ = lean_ctor_get(v_resStartStop_5176_, 1);
v_isSharedCheck_5281_ = !lean_is_exclusive(v_resStartStop_5176_);
if (v_isSharedCheck_5281_ == 0)
{
v___x_5185_ = v_resStartStop_5176_;
v_isShared_5186_ = v_isSharedCheck_5281_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_snd_5183_);
lean_inc(v_fst_5182_);
lean_dec(v_resStartStop_5176_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5281_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
lean_object* v___y_5188_; lean_object* v___y_5189_; lean_object* v_data_5190_; lean_object* v_fst_5201_; lean_object* v_snd_5202_; lean_object* v___x_5204_; uint8_t v_isShared_5205_; uint8_t v_isSharedCheck_5280_; 
v_fst_5201_ = lean_ctor_get(v_snd_5183_, 0);
v_snd_5202_ = lean_ctor_get(v_snd_5183_, 1);
v_isSharedCheck_5280_ = !lean_is_exclusive(v_snd_5183_);
if (v_isSharedCheck_5280_ == 0)
{
v___x_5204_ = v_snd_5183_;
v_isShared_5205_ = v_isSharedCheck_5280_;
goto v_resetjp_5203_;
}
else
{
lean_inc(v_snd_5202_);
lean_inc(v_fst_5201_);
lean_dec(v_snd_5183_);
v___x_5204_ = lean_box(0);
v_isShared_5205_ = v_isSharedCheck_5280_;
goto v_resetjp_5203_;
}
v___jp_5187_:
{
lean_object* v___x_5191_; 
lean_inc(v___y_5188_);
v___x_5191_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_oldTraces_5174_, v_data_5190_, v___y_5188_, v___y_5189_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_);
if (lean_obj_tag(v___x_5191_) == 0)
{
lean_object* v___x_5192_; 
lean_dec_ref_known(v___x_5191_, 1);
v___x_5192_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg(v_fst_5182_);
return v___x_5192_;
}
else
{
lean_object* v_a_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5200_; 
lean_dec(v_fst_5182_);
v_a_5193_ = lean_ctor_get(v___x_5191_, 0);
v_isSharedCheck_5200_ = !lean_is_exclusive(v___x_5191_);
if (v_isSharedCheck_5200_ == 0)
{
v___x_5195_ = v___x_5191_;
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_a_5193_);
lean_dec(v___x_5191_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5200_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v___x_5198_; 
if (v_isShared_5196_ == 0)
{
v___x_5198_ = v___x_5195_;
goto v_reusejp_5197_;
}
else
{
lean_object* v_reuseFailAlloc_5199_; 
v_reuseFailAlloc_5199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5199_, 0, v_a_5193_);
v___x_5198_ = v_reuseFailAlloc_5199_;
goto v_reusejp_5197_;
}
v_reusejp_5197_:
{
return v___x_5198_;
}
}
}
}
v_resetjp_5203_:
{
lean_object* v___x_5206_; uint8_t v___x_5207_; lean_object* v___y_5209_; lean_object* v_a_5210_; uint8_t v___y_5234_; double v___y_5265_; 
v___x_5206_ = l_Lean_trace_profiler;
v___x_5207_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5172_, v___x_5206_);
if (v___x_5207_ == 0)
{
v___y_5234_ = v___x_5207_;
goto v___jp_5233_;
}
else
{
lean_object* v___x_5270_; uint8_t v___x_5271_; 
v___x_5270_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5271_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5172_, v___x_5270_);
if (v___x_5271_ == 0)
{
lean_object* v___x_5272_; lean_object* v___x_5273_; double v___x_5274_; double v___x_5275_; double v___x_5276_; 
v___x_5272_ = l_Lean_trace_profiler_threshold;
v___x_5273_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5172_, v___x_5272_);
v___x_5274_ = lean_float_of_nat(v___x_5273_);
v___x_5275_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4);
v___x_5276_ = lean_float_div(v___x_5274_, v___x_5275_);
v___y_5265_ = v___x_5276_;
goto v___jp_5264_;
}
else
{
lean_object* v___x_5277_; lean_object* v___x_5278_; double v___x_5279_; 
v___x_5277_ = l_Lean_trace_profiler_threshold;
v___x_5278_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5172_, v___x_5277_);
v___x_5279_ = lean_float_of_nat(v___x_5278_);
v___y_5265_ = v___x_5279_;
goto v___jp_5264_;
}
}
v___jp_5208_:
{
uint8_t v_result_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5216_; 
v_result_5211_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_fst_5182_);
v___x_5212_ = l_Lean_TraceResult_toEmoji(v_result_5211_);
v___x_5213_ = l_Lean_stringToMessageData(v___x_5212_);
v___x_5214_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
if (v_isShared_5205_ == 0)
{
lean_ctor_set_tag(v___x_5204_, 7);
lean_ctor_set(v___x_5204_, 1, v___x_5214_);
lean_ctor_set(v___x_5204_, 0, v___x_5213_);
v___x_5216_ = v___x_5204_;
goto v_reusejp_5215_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v___x_5213_);
lean_ctor_set(v_reuseFailAlloc_5227_, 1, v___x_5214_);
v___x_5216_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5215_;
}
v_reusejp_5215_:
{
lean_object* v_m_5218_; 
if (v_isShared_5186_ == 0)
{
lean_ctor_set_tag(v___x_5185_, 7);
lean_ctor_set(v___x_5185_, 1, v_a_5210_);
lean_ctor_set(v___x_5185_, 0, v___x_5216_);
v_m_5218_ = v___x_5185_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5216_);
lean_ctor_set(v_reuseFailAlloc_5226_, 1, v_a_5210_);
v_m_5218_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
lean_object* v___x_5219_; lean_object* v___x_5220_; double v___x_5221_; lean_object* v_data_5222_; 
v___x_5219_ = lean_box(v_result_5211_);
v___x_5220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5219_);
v___x_5221_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5171_);
lean_inc_ref(v___x_5220_);
lean_inc(v_cls_5169_);
v_data_5222_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5222_, 0, v_cls_5169_);
lean_ctor_set(v_data_5222_, 1, v___x_5220_);
lean_ctor_set(v_data_5222_, 2, v_tag_5171_);
lean_ctor_set_float(v_data_5222_, sizeof(void*)*3, v___x_5221_);
lean_ctor_set_float(v_data_5222_, sizeof(void*)*3 + 8, v___x_5221_);
lean_ctor_set_uint8(v_data_5222_, sizeof(void*)*3 + 16, v_collapsed_5170_);
if (v___x_5207_ == 0)
{
lean_dec_ref_known(v___x_5220_, 1);
lean_dec(v_snd_5202_);
lean_dec(v_fst_5201_);
lean_dec_ref(v_tag_5171_);
lean_dec(v_cls_5169_);
v___y_5188_ = v___y_5209_;
v___y_5189_ = v_m_5218_;
v_data_5190_ = v_data_5222_;
goto v___jp_5187_;
}
else
{
lean_object* v_data_5223_; double v___x_5224_; double v___x_5225_; 
lean_dec_ref_known(v_data_5222_, 3);
v_data_5223_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5223_, 0, v_cls_5169_);
lean_ctor_set(v_data_5223_, 1, v___x_5220_);
lean_ctor_set(v_data_5223_, 2, v_tag_5171_);
v___x_5224_ = lean_unbox_float(v_fst_5201_);
lean_dec(v_fst_5201_);
lean_ctor_set_float(v_data_5223_, sizeof(void*)*3, v___x_5224_);
v___x_5225_ = lean_unbox_float(v_snd_5202_);
lean_dec(v_snd_5202_);
lean_ctor_set_float(v_data_5223_, sizeof(void*)*3 + 8, v___x_5225_);
lean_ctor_set_uint8(v_data_5223_, sizeof(void*)*3 + 16, v_collapsed_5170_);
v___y_5188_ = v___y_5209_;
v___y_5189_ = v_m_5218_;
v_data_5190_ = v_data_5223_;
goto v___jp_5187_;
}
}
}
}
v___jp_5228_:
{
lean_object* v_ref_5229_; lean_object* v___x_5230_; 
v_ref_5229_ = lean_ctor_get(v___y_5179_, 5);
lean_inc(v___y_5180_);
lean_inc_ref(v___y_5179_);
lean_inc(v___y_5178_);
lean_inc_ref(v___y_5177_);
lean_inc(v_fst_5182_);
v___x_5230_ = lean_apply_6(v_msg_5175_, v_fst_5182_, v___y_5177_, v___y_5178_, v___y_5179_, v___y_5180_, lean_box(0));
if (lean_obj_tag(v___x_5230_) == 0)
{
lean_object* v_a_5231_; 
v_a_5231_ = lean_ctor_get(v___x_5230_, 0);
lean_inc(v_a_5231_);
lean_dec_ref_known(v___x_5230_, 1);
v___y_5209_ = v_ref_5229_;
v_a_5210_ = v_a_5231_;
goto v___jp_5208_;
}
else
{
lean_object* v___x_5232_; 
lean_dec_ref_known(v___x_5230_, 1);
v___x_5232_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3);
v___y_5209_ = v_ref_5229_;
v_a_5210_ = v___x_5232_;
goto v___jp_5208_;
}
}
v___jp_5233_:
{
if (v_clsEnabled_5173_ == 0)
{
if (v___y_5234_ == 0)
{
lean_object* v___x_5235_; lean_object* v_traceState_5236_; lean_object* v_env_5237_; lean_object* v_nextMacroScope_5238_; lean_object* v_ngen_5239_; lean_object* v_auxDeclNGen_5240_; lean_object* v_cache_5241_; lean_object* v_messages_5242_; lean_object* v_infoState_5243_; lean_object* v_snapshotTasks_5244_; lean_object* v___x_5246_; uint8_t v_isShared_5247_; uint8_t v_isSharedCheck_5263_; 
lean_del_object(v___x_5204_);
lean_dec(v_snd_5202_);
lean_dec(v_fst_5201_);
lean_del_object(v___x_5185_);
lean_dec_ref(v_msg_5175_);
lean_dec_ref(v_tag_5171_);
lean_dec(v_cls_5169_);
v___x_5235_ = lean_st_ref_take(v___y_5180_);
v_traceState_5236_ = lean_ctor_get(v___x_5235_, 4);
v_env_5237_ = lean_ctor_get(v___x_5235_, 0);
v_nextMacroScope_5238_ = lean_ctor_get(v___x_5235_, 1);
v_ngen_5239_ = lean_ctor_get(v___x_5235_, 2);
v_auxDeclNGen_5240_ = lean_ctor_get(v___x_5235_, 3);
v_cache_5241_ = lean_ctor_get(v___x_5235_, 5);
v_messages_5242_ = lean_ctor_get(v___x_5235_, 6);
v_infoState_5243_ = lean_ctor_get(v___x_5235_, 7);
v_snapshotTasks_5244_ = lean_ctor_get(v___x_5235_, 8);
v_isSharedCheck_5263_ = !lean_is_exclusive(v___x_5235_);
if (v_isSharedCheck_5263_ == 0)
{
v___x_5246_ = v___x_5235_;
v_isShared_5247_ = v_isSharedCheck_5263_;
goto v_resetjp_5245_;
}
else
{
lean_inc(v_snapshotTasks_5244_);
lean_inc(v_infoState_5243_);
lean_inc(v_messages_5242_);
lean_inc(v_cache_5241_);
lean_inc(v_traceState_5236_);
lean_inc(v_auxDeclNGen_5240_);
lean_inc(v_ngen_5239_);
lean_inc(v_nextMacroScope_5238_);
lean_inc(v_env_5237_);
lean_dec(v___x_5235_);
v___x_5246_ = lean_box(0);
v_isShared_5247_ = v_isSharedCheck_5263_;
goto v_resetjp_5245_;
}
v_resetjp_5245_:
{
uint64_t v_tid_5248_; lean_object* v_traces_5249_; lean_object* v___x_5251_; uint8_t v_isShared_5252_; uint8_t v_isSharedCheck_5262_; 
v_tid_5248_ = lean_ctor_get_uint64(v_traceState_5236_, sizeof(void*)*1);
v_traces_5249_ = lean_ctor_get(v_traceState_5236_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v_traceState_5236_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5251_ = v_traceState_5236_;
v_isShared_5252_ = v_isSharedCheck_5262_;
goto v_resetjp_5250_;
}
else
{
lean_inc(v_traces_5249_);
lean_dec(v_traceState_5236_);
v___x_5251_ = lean_box(0);
v_isShared_5252_ = v_isSharedCheck_5262_;
goto v_resetjp_5250_;
}
v_resetjp_5250_:
{
lean_object* v___x_5253_; lean_object* v___x_5255_; 
v___x_5253_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5174_, v_traces_5249_);
lean_dec_ref(v_traces_5249_);
if (v_isShared_5252_ == 0)
{
lean_ctor_set(v___x_5251_, 0, v___x_5253_);
v___x_5255_ = v___x_5251_;
goto v_reusejp_5254_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v___x_5253_);
lean_ctor_set_uint64(v_reuseFailAlloc_5261_, sizeof(void*)*1, v_tid_5248_);
v___x_5255_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5254_;
}
v_reusejp_5254_:
{
lean_object* v___x_5257_; 
if (v_isShared_5247_ == 0)
{
lean_ctor_set(v___x_5246_, 4, v___x_5255_);
v___x_5257_ = v___x_5246_;
goto v_reusejp_5256_;
}
else
{
lean_object* v_reuseFailAlloc_5260_; 
v_reuseFailAlloc_5260_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5260_, 0, v_env_5237_);
lean_ctor_set(v_reuseFailAlloc_5260_, 1, v_nextMacroScope_5238_);
lean_ctor_set(v_reuseFailAlloc_5260_, 2, v_ngen_5239_);
lean_ctor_set(v_reuseFailAlloc_5260_, 3, v_auxDeclNGen_5240_);
lean_ctor_set(v_reuseFailAlloc_5260_, 4, v___x_5255_);
lean_ctor_set(v_reuseFailAlloc_5260_, 5, v_cache_5241_);
lean_ctor_set(v_reuseFailAlloc_5260_, 6, v_messages_5242_);
lean_ctor_set(v_reuseFailAlloc_5260_, 7, v_infoState_5243_);
lean_ctor_set(v_reuseFailAlloc_5260_, 8, v_snapshotTasks_5244_);
v___x_5257_ = v_reuseFailAlloc_5260_;
goto v_reusejp_5256_;
}
v_reusejp_5256_:
{
lean_object* v___x_5258_; lean_object* v___x_5259_; 
v___x_5258_ = lean_st_ref_set(v___y_5180_, v___x_5257_);
v___x_5259_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg(v_fst_5182_);
return v___x_5259_;
}
}
}
}
}
else
{
goto v___jp_5228_;
}
}
else
{
goto v___jp_5228_;
}
}
v___jp_5264_:
{
double v___x_5266_; double v___x_5267_; double v___x_5268_; uint8_t v___x_5269_; 
v___x_5266_ = lean_unbox_float(v_snd_5202_);
v___x_5267_ = lean_unbox_float(v_fst_5201_);
v___x_5268_ = lean_float_sub(v___x_5266_, v___x_5267_);
v___x_5269_ = lean_float_decLt(v___y_5265_, v___x_5268_);
v___y_5234_ = v___x_5269_;
goto v___jp_5233_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5282_, lean_object* v_collapsed_5283_, lean_object* v_tag_5284_, lean_object* v_opts_5285_, lean_object* v_clsEnabled_5286_, lean_object* v_oldTraces_5287_, lean_object* v_msg_5288_, lean_object* v_resStartStop_5289_, lean_object* v___y_5290_, lean_object* v___y_5291_, lean_object* v___y_5292_, lean_object* v___y_5293_, lean_object* v___y_5294_){
_start:
{
uint8_t v_collapsed_boxed_5295_; uint8_t v_clsEnabled_boxed_5296_; lean_object* v_res_5297_; 
v_collapsed_boxed_5295_ = lean_unbox(v_collapsed_5283_);
v_clsEnabled_boxed_5296_ = lean_unbox(v_clsEnabled_5286_);
v_res_5297_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5282_, v_collapsed_boxed_5295_, v_tag_5284_, v_opts_5285_, v_clsEnabled_boxed_5296_, v_oldTraces_5287_, v_msg_5288_, v_resStartStop_5289_, v___y_5290_, v___y_5291_, v___y_5292_, v___y_5293_);
lean_dec(v___y_5293_);
lean_dec_ref(v___y_5292_);
lean_dec(v___y_5291_);
lean_dec_ref(v___y_5290_);
lean_dec_ref(v_opts_5285_);
return v_res_5297_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5302_; lean_object* v___x_5303_; lean_object* v___x_5304_; 
v_cls_5302_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5303_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5304_ = l_Lean_Name_append(v___x_5303_, v_cls_5302_);
return v___x_5304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5305_, lean_object* v_a_5306_, lean_object* v_a_5307_, lean_object* v_a_5308_, lean_object* v_a_5309_){
_start:
{
lean_object* v___y_5312_; lean_object* v_options_5330_; lean_object* v_inheritedTraceOptions_5331_; uint8_t v_hasTrace_5332_; lean_object* v_cls_5333_; uint8_t v___x_5334_; uint8_t v___x_5335_; 
v_options_5330_ = lean_ctor_get(v_a_5308_, 2);
v_inheritedTraceOptions_5331_ = lean_ctor_get(v_a_5308_, 13);
v_hasTrace_5332_ = lean_ctor_get_uint8(v_options_5330_, sizeof(void*)*1);
v_cls_5333_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5334_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5305_);
v___x_5335_ = 1;
if (v_hasTrace_5332_ == 0)
{
lean_object* v___x_5336_; 
v___x_5336_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5334_, v_e_5305_, v___x_5335_, v_cls_5333_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
v___y_5312_ = v___x_5336_;
goto v___jp_5311_;
}
else
{
lean_object* v___f_5337_; lean_object* v___x_5338_; lean_object* v___x_5339_; uint8_t v___x_5340_; lean_object* v___y_5342_; lean_object* v___y_5343_; lean_object* v_a_5344_; lean_object* v___y_5357_; lean_object* v___y_5358_; lean_object* v_a_5359_; 
v___f_5337_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5338_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5339_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5340_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5331_, v_options_5330_, v___x_5339_);
if (v___x_5340_ == 0)
{
lean_object* v___x_5409_; uint8_t v___x_5410_; 
v___x_5409_ = l_Lean_trace_profiler;
v___x_5410_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5330_, v___x_5409_);
if (v___x_5410_ == 0)
{
lean_object* v___x_5411_; 
v___x_5411_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5334_, v_e_5305_, v___x_5335_, v_cls_5333_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
v___y_5312_ = v___x_5411_;
goto v___jp_5311_;
}
else
{
goto v___jp_5368_;
}
}
else
{
goto v___jp_5368_;
}
v___jp_5341_:
{
lean_object* v___x_5345_; double v___x_5346_; double v___x_5347_; double v___x_5348_; double v___x_5349_; double v___x_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5345_ = lean_io_mono_nanos_now();
v___x_5346_ = lean_float_of_nat(v___y_5342_);
v___x_5347_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5348_ = lean_float_div(v___x_5346_, v___x_5347_);
v___x_5349_ = lean_float_of_nat(v___x_5345_);
v___x_5350_ = lean_float_div(v___x_5349_, v___x_5347_);
v___x_5351_ = lean_box_float(v___x_5348_);
v___x_5352_ = lean_box_float(v___x_5350_);
v___x_5353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5353_, 0, v___x_5351_);
lean_ctor_set(v___x_5353_, 1, v___x_5352_);
v___x_5354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5354_, 0, v_a_5344_);
lean_ctor_set(v___x_5354_, 1, v___x_5353_);
v___x_5355_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5333_, v___x_5335_, v___x_5338_, v_options_5330_, v___x_5340_, v___y_5343_, v___f_5337_, v___x_5354_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
v___y_5312_ = v___x_5355_;
goto v___jp_5311_;
}
v___jp_5356_:
{
lean_object* v___x_5360_; double v___x_5361_; double v___x_5362_; lean_object* v___x_5363_; lean_object* v___x_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; lean_object* v___x_5367_; 
v___x_5360_ = lean_io_get_num_heartbeats();
v___x_5361_ = lean_float_of_nat(v___y_5357_);
v___x_5362_ = lean_float_of_nat(v___x_5360_);
v___x_5363_ = lean_box_float(v___x_5361_);
v___x_5364_ = lean_box_float(v___x_5362_);
v___x_5365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5365_, 0, v___x_5363_);
lean_ctor_set(v___x_5365_, 1, v___x_5364_);
v___x_5366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5366_, 0, v_a_5359_);
lean_ctor_set(v___x_5366_, 1, v___x_5365_);
v___x_5367_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5333_, v___x_5335_, v___x_5338_, v_options_5330_, v___x_5340_, v___y_5358_, v___f_5337_, v___x_5366_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
v___y_5312_ = v___x_5367_;
goto v___jp_5311_;
}
v___jp_5368_:
{
lean_object* v___x_5369_; lean_object* v_a_5370_; lean_object* v___x_5371_; uint8_t v___x_5372_; 
v___x_5369_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5309_);
v_a_5370_ = lean_ctor_get(v___x_5369_, 0);
lean_inc(v_a_5370_);
lean_dec_ref(v___x_5369_);
v___x_5371_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5372_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5330_, v___x_5371_);
if (v___x_5372_ == 0)
{
lean_object* v___x_5373_; lean_object* v___x_5374_; 
v___x_5373_ = lean_io_mono_nanos_now();
v___x_5374_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5334_, v_e_5305_, v___x_5335_, v_cls_5333_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
if (lean_obj_tag(v___x_5374_) == 0)
{
lean_object* v_a_5375_; lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5382_; 
v_a_5375_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5382_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5382_ == 0)
{
v___x_5377_ = v___x_5374_;
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
else
{
lean_inc(v_a_5375_);
lean_dec(v___x_5374_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5380_; 
if (v_isShared_5378_ == 0)
{
lean_ctor_set_tag(v___x_5377_, 1);
v___x_5380_ = v___x_5377_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v_a_5375_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
v___y_5342_ = v___x_5373_;
v___y_5343_ = v_a_5370_;
v_a_5344_ = v___x_5380_;
goto v___jp_5341_;
}
}
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
v_a_5383_ = lean_ctor_get(v___x_5374_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5374_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5374_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5374_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
lean_ctor_set_tag(v___x_5385_, 0);
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
v___y_5342_ = v___x_5373_;
v___y_5343_ = v_a_5370_;
v_a_5344_ = v___x_5388_;
goto v___jp_5341_;
}
}
}
}
else
{
lean_object* v___x_5391_; lean_object* v___x_5392_; 
v___x_5391_ = lean_io_get_num_heartbeats();
v___x_5392_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5334_, v_e_5305_, v___x_5335_, v_cls_5333_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
if (lean_obj_tag(v___x_5392_) == 0)
{
lean_object* v_a_5393_; lean_object* v___x_5395_; uint8_t v_isShared_5396_; uint8_t v_isSharedCheck_5400_; 
v_a_5393_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5395_ = v___x_5392_;
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
else
{
lean_inc(v_a_5393_);
lean_dec(v___x_5392_);
v___x_5395_ = lean_box(0);
v_isShared_5396_ = v_isSharedCheck_5400_;
goto v_resetjp_5394_;
}
v_resetjp_5394_:
{
lean_object* v___x_5398_; 
if (v_isShared_5396_ == 0)
{
lean_ctor_set_tag(v___x_5395_, 1);
v___x_5398_ = v___x_5395_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
v___y_5357_ = v___x_5391_;
v___y_5358_ = v_a_5370_;
v_a_5359_ = v___x_5398_;
goto v___jp_5356_;
}
}
}
else
{
lean_object* v_a_5401_; lean_object* v___x_5403_; uint8_t v_isShared_5404_; uint8_t v_isSharedCheck_5408_; 
v_a_5401_ = lean_ctor_get(v___x_5392_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5392_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5403_ = v___x_5392_;
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
else
{
lean_inc(v_a_5401_);
lean_dec(v___x_5392_);
v___x_5403_ = lean_box(0);
v_isShared_5404_ = v_isSharedCheck_5408_;
goto v_resetjp_5402_;
}
v_resetjp_5402_:
{
lean_object* v___x_5406_; 
if (v_isShared_5404_ == 0)
{
lean_ctor_set_tag(v___x_5403_, 0);
v___x_5406_ = v___x_5403_;
goto v_reusejp_5405_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v_a_5401_);
v___x_5406_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5405_;
}
v_reusejp_5405_:
{
v___y_5357_ = v___x_5391_;
v___y_5358_ = v_a_5370_;
v_a_5359_ = v___x_5406_;
goto v___jp_5356_;
}
}
}
}
}
}
v___jp_5311_:
{
if (lean_obj_tag(v___y_5312_) == 0)
{
lean_object* v_a_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5321_; 
v_a_5313_ = lean_ctor_get(v___y_5312_, 0);
v_isSharedCheck_5321_ = !lean_is_exclusive(v___y_5312_);
if (v_isSharedCheck_5321_ == 0)
{
v___x_5315_ = v___y_5312_;
v_isShared_5316_ = v_isSharedCheck_5321_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_a_5313_);
lean_dec(v___y_5312_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5321_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
lean_object* v_fst_5317_; lean_object* v___x_5319_; 
v_fst_5317_ = lean_ctor_get(v_a_5313_, 0);
lean_inc(v_fst_5317_);
lean_dec(v_a_5313_);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v_fst_5317_);
v___x_5319_ = v___x_5315_;
goto v_reusejp_5318_;
}
else
{
lean_object* v_reuseFailAlloc_5320_; 
v_reuseFailAlloc_5320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5320_, 0, v_fst_5317_);
v___x_5319_ = v_reuseFailAlloc_5320_;
goto v_reusejp_5318_;
}
v_reusejp_5318_:
{
return v___x_5319_;
}
}
}
else
{
lean_object* v_a_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5329_; 
v_a_5322_ = lean_ctor_get(v___y_5312_, 0);
v_isSharedCheck_5329_ = !lean_is_exclusive(v___y_5312_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5324_ = v___y_5312_;
v_isShared_5325_ = v_isSharedCheck_5329_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_a_5322_);
lean_dec(v___y_5312_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5412_, lean_object* v_a_5413_, lean_object* v_a_5414_, lean_object* v_a_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v_res_5418_; 
v_res_5418_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5412_, v_a_5413_, v_a_5414_, v_a_5415_, v_a_5416_);
lean_dec(v_a_5416_);
lean_dec_ref(v_a_5415_);
lean_dec(v_a_5414_);
lean_dec_ref(v_a_5413_);
return v_res_5418_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_00_u03b1_5419_, lean_object* v_x_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_, lean_object* v___y_5423_, lean_object* v___y_5424_){
_start:
{
lean_object* v___x_5426_; 
v___x_5426_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___redArg(v_x_5420_);
return v___x_5426_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_00_u03b1_5427_, lean_object* v_x_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_00_u03b1_5427_, v_x_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5435_, lean_object* v___y_5436_){
_start:
{
uint8_t v___x_5438_; 
v___x_5438_ = l_Lean_Expr_hasMVar(v_e_5435_);
if (v___x_5438_ == 0)
{
lean_object* v___x_5439_; 
v___x_5439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5439_, 0, v_e_5435_);
return v___x_5439_;
}
else
{
lean_object* v___x_5440_; lean_object* v_mctx_5441_; lean_object* v___x_5442_; lean_object* v_fst_5443_; lean_object* v_snd_5444_; lean_object* v___x_5445_; lean_object* v_cache_5446_; lean_object* v_zetaDeltaFVarIds_5447_; lean_object* v_postponed_5448_; lean_object* v_diag_5449_; lean_object* v___x_5451_; uint8_t v_isShared_5452_; uint8_t v_isSharedCheck_5458_; 
v___x_5440_ = lean_st_ref_get(v___y_5436_);
v_mctx_5441_ = lean_ctor_get(v___x_5440_, 0);
lean_inc_ref(v_mctx_5441_);
lean_dec(v___x_5440_);
v___x_5442_ = l_Lean_instantiateMVarsCore(v_mctx_5441_, v_e_5435_);
v_fst_5443_ = lean_ctor_get(v___x_5442_, 0);
lean_inc(v_fst_5443_);
v_snd_5444_ = lean_ctor_get(v___x_5442_, 1);
lean_inc(v_snd_5444_);
lean_dec_ref(v___x_5442_);
v___x_5445_ = lean_st_ref_take(v___y_5436_);
v_cache_5446_ = lean_ctor_get(v___x_5445_, 1);
v_zetaDeltaFVarIds_5447_ = lean_ctor_get(v___x_5445_, 2);
v_postponed_5448_ = lean_ctor_get(v___x_5445_, 3);
v_diag_5449_ = lean_ctor_get(v___x_5445_, 4);
v_isSharedCheck_5458_ = !lean_is_exclusive(v___x_5445_);
if (v_isSharedCheck_5458_ == 0)
{
lean_object* v_unused_5459_; 
v_unused_5459_ = lean_ctor_get(v___x_5445_, 0);
lean_dec(v_unused_5459_);
v___x_5451_ = v___x_5445_;
v_isShared_5452_ = v_isSharedCheck_5458_;
goto v_resetjp_5450_;
}
else
{
lean_inc(v_diag_5449_);
lean_inc(v_postponed_5448_);
lean_inc(v_zetaDeltaFVarIds_5447_);
lean_inc(v_cache_5446_);
lean_dec(v___x_5445_);
v___x_5451_ = lean_box(0);
v_isShared_5452_ = v_isSharedCheck_5458_;
goto v_resetjp_5450_;
}
v_resetjp_5450_:
{
lean_object* v___x_5454_; 
if (v_isShared_5452_ == 0)
{
lean_ctor_set(v___x_5451_, 0, v_snd_5444_);
v___x_5454_ = v___x_5451_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v_snd_5444_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_cache_5446_);
lean_ctor_set(v_reuseFailAlloc_5457_, 2, v_zetaDeltaFVarIds_5447_);
lean_ctor_set(v_reuseFailAlloc_5457_, 3, v_postponed_5448_);
lean_ctor_set(v_reuseFailAlloc_5457_, 4, v_diag_5449_);
v___x_5454_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
lean_object* v___x_5455_; lean_object* v___x_5456_; 
v___x_5455_ = lean_st_ref_set(v___y_5436_, v___x_5454_);
v___x_5456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5456_, 0, v_fst_5443_);
return v___x_5456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_){
_start:
{
lean_object* v_res_5463_; 
v_res_5463_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5460_, v___y_5461_);
lean_dec(v___y_5461_);
return v_res_5463_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5464_, lean_object* v___y_5465_, lean_object* v___y_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_){
_start:
{
lean_object* v___x_5470_; 
v___x_5470_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5464_, v___y_5466_);
return v___x_5470_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_, lean_object* v___y_5476_){
_start:
{
lean_object* v_res_5477_; 
v_res_5477_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5471_, v___y_5472_, v___y_5473_, v___y_5474_, v___y_5475_);
lean_dec(v___y_5475_);
lean_dec_ref(v___y_5474_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
return v_res_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5478_, lean_object* v_opts_5479_, lean_object* v_act_5480_, lean_object* v_decl_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_, lean_object* v___y_5485_){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; 
lean_inc(v___y_5485_);
lean_inc_ref(v___y_5484_);
lean_inc(v___y_5483_);
lean_inc_ref(v___y_5482_);
v___x_5487_ = lean_apply_4(v_act_5480_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_);
v___x_5488_ = l_Lean_profileitIOUnsafe___redArg(v_category_5478_, v_opts_5479_, v___x_5487_, v_decl_5481_);
return v___x_5488_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5489_, lean_object* v_opts_5490_, lean_object* v_act_5491_, lean_object* v_decl_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_){
_start:
{
lean_object* v_res_5498_; 
v_res_5498_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5489_, v_opts_5490_, v_act_5491_, v_decl_5492_, v___y_5493_, v___y_5494_, v___y_5495_, v___y_5496_);
lean_dec(v___y_5496_);
lean_dec_ref(v___y_5495_);
lean_dec(v___y_5494_);
lean_dec_ref(v___y_5493_);
lean_dec_ref(v_opts_5490_);
lean_dec_ref(v_category_5489_);
return v_res_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5499_, lean_object* v_category_5500_, lean_object* v_opts_5501_, lean_object* v_act_5502_, lean_object* v_decl_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_){
_start:
{
lean_object* v___x_5509_; 
v___x_5509_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5500_, v_opts_5501_, v_act_5502_, v_decl_5503_, v___y_5504_, v___y_5505_, v___y_5506_, v___y_5507_);
return v___x_5509_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5510_, lean_object* v_category_5511_, lean_object* v_opts_5512_, lean_object* v_act_5513_, lean_object* v_decl_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_, lean_object* v___y_5518_, lean_object* v___y_5519_){
_start:
{
lean_object* v_res_5520_; 
v_res_5520_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5510_, v_category_5511_, v_opts_5512_, v_act_5513_, v_decl_5514_, v___y_5515_, v___y_5516_, v___y_5517_, v___y_5518_);
lean_dec(v___y_5518_);
lean_dec_ref(v___y_5517_);
lean_dec(v___y_5516_);
lean_dec_ref(v___y_5515_);
lean_dec_ref(v_opts_5512_);
lean_dec_ref(v_category_5511_);
return v_res_5520_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5521_, uint8_t v_isExporting_5522_, lean_object* v___x_5523_, lean_object* v___y_5524_, lean_object* v___x_5525_, lean_object* v_a_x3f_5526_){
_start:
{
lean_object* v___x_5528_; lean_object* v_env_5529_; lean_object* v_nextMacroScope_5530_; lean_object* v_ngen_5531_; lean_object* v_auxDeclNGen_5532_; lean_object* v_traceState_5533_; lean_object* v_messages_5534_; lean_object* v_infoState_5535_; lean_object* v_snapshotTasks_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5561_; 
v___x_5528_ = lean_st_ref_take(v___y_5521_);
v_env_5529_ = lean_ctor_get(v___x_5528_, 0);
v_nextMacroScope_5530_ = lean_ctor_get(v___x_5528_, 1);
v_ngen_5531_ = lean_ctor_get(v___x_5528_, 2);
v_auxDeclNGen_5532_ = lean_ctor_get(v___x_5528_, 3);
v_traceState_5533_ = lean_ctor_get(v___x_5528_, 4);
v_messages_5534_ = lean_ctor_get(v___x_5528_, 6);
v_infoState_5535_ = lean_ctor_get(v___x_5528_, 7);
v_snapshotTasks_5536_ = lean_ctor_get(v___x_5528_, 8);
v_isSharedCheck_5561_ = !lean_is_exclusive(v___x_5528_);
if (v_isSharedCheck_5561_ == 0)
{
lean_object* v_unused_5562_; 
v_unused_5562_ = lean_ctor_get(v___x_5528_, 5);
lean_dec(v_unused_5562_);
v___x_5538_ = v___x_5528_;
v_isShared_5539_ = v_isSharedCheck_5561_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_snapshotTasks_5536_);
lean_inc(v_infoState_5535_);
lean_inc(v_messages_5534_);
lean_inc(v_traceState_5533_);
lean_inc(v_auxDeclNGen_5532_);
lean_inc(v_ngen_5531_);
lean_inc(v_nextMacroScope_5530_);
lean_inc(v_env_5529_);
lean_dec(v___x_5528_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5561_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5540_; lean_object* v___x_5542_; 
v___x_5540_ = l_Lean_Environment_setExporting(v_env_5529_, v_isExporting_5522_);
if (v_isShared_5539_ == 0)
{
lean_ctor_set(v___x_5538_, 5, v___x_5523_);
lean_ctor_set(v___x_5538_, 0, v___x_5540_);
v___x_5542_ = v___x_5538_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5560_; 
v_reuseFailAlloc_5560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5560_, 0, v___x_5540_);
lean_ctor_set(v_reuseFailAlloc_5560_, 1, v_nextMacroScope_5530_);
lean_ctor_set(v_reuseFailAlloc_5560_, 2, v_ngen_5531_);
lean_ctor_set(v_reuseFailAlloc_5560_, 3, v_auxDeclNGen_5532_);
lean_ctor_set(v_reuseFailAlloc_5560_, 4, v_traceState_5533_);
lean_ctor_set(v_reuseFailAlloc_5560_, 5, v___x_5523_);
lean_ctor_set(v_reuseFailAlloc_5560_, 6, v_messages_5534_);
lean_ctor_set(v_reuseFailAlloc_5560_, 7, v_infoState_5535_);
lean_ctor_set(v_reuseFailAlloc_5560_, 8, v_snapshotTasks_5536_);
v___x_5542_ = v_reuseFailAlloc_5560_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5543_; lean_object* v___x_5544_; lean_object* v_mctx_5545_; lean_object* v_zetaDeltaFVarIds_5546_; lean_object* v_postponed_5547_; lean_object* v_diag_5548_; lean_object* v___x_5550_; uint8_t v_isShared_5551_; uint8_t v_isSharedCheck_5558_; 
v___x_5543_ = lean_st_ref_set(v___y_5521_, v___x_5542_);
v___x_5544_ = lean_st_ref_take(v___y_5524_);
v_mctx_5545_ = lean_ctor_get(v___x_5544_, 0);
v_zetaDeltaFVarIds_5546_ = lean_ctor_get(v___x_5544_, 2);
v_postponed_5547_ = lean_ctor_get(v___x_5544_, 3);
v_diag_5548_ = lean_ctor_get(v___x_5544_, 4);
v_isSharedCheck_5558_ = !lean_is_exclusive(v___x_5544_);
if (v_isSharedCheck_5558_ == 0)
{
lean_object* v_unused_5559_; 
v_unused_5559_ = lean_ctor_get(v___x_5544_, 1);
lean_dec(v_unused_5559_);
v___x_5550_ = v___x_5544_;
v_isShared_5551_ = v_isSharedCheck_5558_;
goto v_resetjp_5549_;
}
else
{
lean_inc(v_diag_5548_);
lean_inc(v_postponed_5547_);
lean_inc(v_zetaDeltaFVarIds_5546_);
lean_inc(v_mctx_5545_);
lean_dec(v___x_5544_);
v___x_5550_ = lean_box(0);
v_isShared_5551_ = v_isSharedCheck_5558_;
goto v_resetjp_5549_;
}
v_resetjp_5549_:
{
lean_object* v___x_5553_; 
if (v_isShared_5551_ == 0)
{
lean_ctor_set(v___x_5550_, 1, v___x_5525_);
v___x_5553_ = v___x_5550_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5557_; 
v_reuseFailAlloc_5557_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5557_, 0, v_mctx_5545_);
lean_ctor_set(v_reuseFailAlloc_5557_, 1, v___x_5525_);
lean_ctor_set(v_reuseFailAlloc_5557_, 2, v_zetaDeltaFVarIds_5546_);
lean_ctor_set(v_reuseFailAlloc_5557_, 3, v_postponed_5547_);
lean_ctor_set(v_reuseFailAlloc_5557_, 4, v_diag_5548_);
v___x_5553_ = v_reuseFailAlloc_5557_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; 
v___x_5554_ = lean_st_ref_set(v___y_5524_, v___x_5553_);
v___x_5555_ = lean_box(0);
v___x_5556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5556_, 0, v___x_5555_);
return v___x_5556_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5563_, lean_object* v_isExporting_5564_, lean_object* v___x_5565_, lean_object* v___y_5566_, lean_object* v___x_5567_, lean_object* v_a_x3f_5568_, lean_object* v___y_5569_){
_start:
{
uint8_t v_isExporting_boxed_5570_; lean_object* v_res_5571_; 
v_isExporting_boxed_5570_ = lean_unbox(v_isExporting_5564_);
v_res_5571_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5563_, v_isExporting_boxed_5570_, v___x_5565_, v___y_5566_, v___x_5567_, v_a_x3f_5568_);
lean_dec(v_a_x3f_5568_);
lean_dec(v___y_5566_);
lean_dec(v___y_5563_);
return v_res_5571_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5572_; 
v___x_5572_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5572_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5573_; lean_object* v___x_5574_; 
v___x_5573_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5574_, 0, v___x_5573_);
return v___x_5574_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5575_; lean_object* v___x_5576_; 
v___x_5575_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5576_, 0, v___x_5575_);
lean_ctor_set(v___x_5576_, 1, v___x_5575_);
return v___x_5576_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5577_; lean_object* v___x_5578_; 
v___x_5577_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5578_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5578_, 0, v___x_5577_);
lean_ctor_set(v___x_5578_, 1, v___x_5577_);
lean_ctor_set(v___x_5578_, 2, v___x_5577_);
lean_ctor_set(v___x_5578_, 3, v___x_5577_);
lean_ctor_set(v___x_5578_, 4, v___x_5577_);
lean_ctor_set(v___x_5578_, 5, v___x_5577_);
return v___x_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5579_, uint8_t v_isExporting_5580_, lean_object* v___y_5581_, lean_object* v___y_5582_, lean_object* v___y_5583_, lean_object* v___y_5584_){
_start:
{
lean_object* v___x_5586_; lean_object* v_env_5587_; uint8_t v_isExporting_5588_; lean_object* v___x_5589_; lean_object* v_env_5590_; lean_object* v_nextMacroScope_5591_; lean_object* v_ngen_5592_; lean_object* v_auxDeclNGen_5593_; lean_object* v_traceState_5594_; lean_object* v_messages_5595_; lean_object* v_infoState_5596_; lean_object* v_snapshotTasks_5597_; lean_object* v___x_5599_; uint8_t v_isShared_5600_; uint8_t v_isSharedCheck_5651_; 
v___x_5586_ = lean_st_ref_get(v___y_5584_);
v_env_5587_ = lean_ctor_get(v___x_5586_, 0);
lean_inc_ref(v_env_5587_);
lean_dec(v___x_5586_);
v_isExporting_5588_ = lean_ctor_get_uint8(v_env_5587_, sizeof(void*)*8);
lean_dec_ref(v_env_5587_);
v___x_5589_ = lean_st_ref_take(v___y_5584_);
v_env_5590_ = lean_ctor_get(v___x_5589_, 0);
v_nextMacroScope_5591_ = lean_ctor_get(v___x_5589_, 1);
v_ngen_5592_ = lean_ctor_get(v___x_5589_, 2);
v_auxDeclNGen_5593_ = lean_ctor_get(v___x_5589_, 3);
v_traceState_5594_ = lean_ctor_get(v___x_5589_, 4);
v_messages_5595_ = lean_ctor_get(v___x_5589_, 6);
v_infoState_5596_ = lean_ctor_get(v___x_5589_, 7);
v_snapshotTasks_5597_ = lean_ctor_get(v___x_5589_, 8);
v_isSharedCheck_5651_ = !lean_is_exclusive(v___x_5589_);
if (v_isSharedCheck_5651_ == 0)
{
lean_object* v_unused_5652_; 
v_unused_5652_ = lean_ctor_get(v___x_5589_, 5);
lean_dec(v_unused_5652_);
v___x_5599_ = v___x_5589_;
v_isShared_5600_ = v_isSharedCheck_5651_;
goto v_resetjp_5598_;
}
else
{
lean_inc(v_snapshotTasks_5597_);
lean_inc(v_infoState_5596_);
lean_inc(v_messages_5595_);
lean_inc(v_traceState_5594_);
lean_inc(v_auxDeclNGen_5593_);
lean_inc(v_ngen_5592_);
lean_inc(v_nextMacroScope_5591_);
lean_inc(v_env_5590_);
lean_dec(v___x_5589_);
v___x_5599_ = lean_box(0);
v_isShared_5600_ = v_isSharedCheck_5651_;
goto v_resetjp_5598_;
}
v_resetjp_5598_:
{
lean_object* v___x_5601_; lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5601_ = l_Lean_Environment_setExporting(v_env_5590_, v_isExporting_5580_);
v___x_5602_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5600_ == 0)
{
lean_ctor_set(v___x_5599_, 5, v___x_5602_);
lean_ctor_set(v___x_5599_, 0, v___x_5601_);
v___x_5604_ = v___x_5599_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5650_; 
v_reuseFailAlloc_5650_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5650_, 0, v___x_5601_);
lean_ctor_set(v_reuseFailAlloc_5650_, 1, v_nextMacroScope_5591_);
lean_ctor_set(v_reuseFailAlloc_5650_, 2, v_ngen_5592_);
lean_ctor_set(v_reuseFailAlloc_5650_, 3, v_auxDeclNGen_5593_);
lean_ctor_set(v_reuseFailAlloc_5650_, 4, v_traceState_5594_);
lean_ctor_set(v_reuseFailAlloc_5650_, 5, v___x_5602_);
lean_ctor_set(v_reuseFailAlloc_5650_, 6, v_messages_5595_);
lean_ctor_set(v_reuseFailAlloc_5650_, 7, v_infoState_5596_);
lean_ctor_set(v_reuseFailAlloc_5650_, 8, v_snapshotTasks_5597_);
v___x_5604_ = v_reuseFailAlloc_5650_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
lean_object* v___x_5605_; lean_object* v___x_5606_; lean_object* v_mctx_5607_; lean_object* v_zetaDeltaFVarIds_5608_; lean_object* v_postponed_5609_; lean_object* v_diag_5610_; lean_object* v___x_5612_; uint8_t v_isShared_5613_; uint8_t v_isSharedCheck_5648_; 
v___x_5605_ = lean_st_ref_set(v___y_5584_, v___x_5604_);
v___x_5606_ = lean_st_ref_take(v___y_5582_);
v_mctx_5607_ = lean_ctor_get(v___x_5606_, 0);
v_zetaDeltaFVarIds_5608_ = lean_ctor_get(v___x_5606_, 2);
v_postponed_5609_ = lean_ctor_get(v___x_5606_, 3);
v_diag_5610_ = lean_ctor_get(v___x_5606_, 4);
v_isSharedCheck_5648_ = !lean_is_exclusive(v___x_5606_);
if (v_isSharedCheck_5648_ == 0)
{
lean_object* v_unused_5649_; 
v_unused_5649_ = lean_ctor_get(v___x_5606_, 1);
lean_dec(v_unused_5649_);
v___x_5612_ = v___x_5606_;
v_isShared_5613_ = v_isSharedCheck_5648_;
goto v_resetjp_5611_;
}
else
{
lean_inc(v_diag_5610_);
lean_inc(v_postponed_5609_);
lean_inc(v_zetaDeltaFVarIds_5608_);
lean_inc(v_mctx_5607_);
lean_dec(v___x_5606_);
v___x_5612_ = lean_box(0);
v_isShared_5613_ = v_isSharedCheck_5648_;
goto v_resetjp_5611_;
}
v_resetjp_5611_:
{
lean_object* v___x_5614_; lean_object* v___x_5616_; 
v___x_5614_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5613_ == 0)
{
lean_ctor_set(v___x_5612_, 1, v___x_5614_);
v___x_5616_ = v___x_5612_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5647_; 
v_reuseFailAlloc_5647_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5647_, 0, v_mctx_5607_);
lean_ctor_set(v_reuseFailAlloc_5647_, 1, v___x_5614_);
lean_ctor_set(v_reuseFailAlloc_5647_, 2, v_zetaDeltaFVarIds_5608_);
lean_ctor_set(v_reuseFailAlloc_5647_, 3, v_postponed_5609_);
lean_ctor_set(v_reuseFailAlloc_5647_, 4, v_diag_5610_);
v___x_5616_ = v_reuseFailAlloc_5647_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
lean_object* v___x_5617_; lean_object* v_r_5618_; 
v___x_5617_ = lean_st_ref_set(v___y_5582_, v___x_5616_);
lean_inc(v___y_5584_);
lean_inc_ref(v___y_5583_);
lean_inc(v___y_5582_);
lean_inc_ref(v___y_5581_);
v_r_5618_ = lean_apply_5(v_x_5579_, v___y_5581_, v___y_5582_, v___y_5583_, v___y_5584_, lean_box(0));
if (lean_obj_tag(v_r_5618_) == 0)
{
lean_object* v_a_5619_; lean_object* v___x_5621_; uint8_t v_isShared_5622_; uint8_t v_isSharedCheck_5635_; 
v_a_5619_ = lean_ctor_get(v_r_5618_, 0);
v_isSharedCheck_5635_ = !lean_is_exclusive(v_r_5618_);
if (v_isSharedCheck_5635_ == 0)
{
v___x_5621_ = v_r_5618_;
v_isShared_5622_ = v_isSharedCheck_5635_;
goto v_resetjp_5620_;
}
else
{
lean_inc(v_a_5619_);
lean_dec(v_r_5618_);
v___x_5621_ = lean_box(0);
v_isShared_5622_ = v_isSharedCheck_5635_;
goto v_resetjp_5620_;
}
v_resetjp_5620_:
{
lean_object* v___x_5624_; 
lean_inc(v_a_5619_);
if (v_isShared_5622_ == 0)
{
lean_ctor_set_tag(v___x_5621_, 1);
v___x_5624_ = v___x_5621_;
goto v_reusejp_5623_;
}
else
{
lean_object* v_reuseFailAlloc_5634_; 
v_reuseFailAlloc_5634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5634_, 0, v_a_5619_);
v___x_5624_ = v_reuseFailAlloc_5634_;
goto v_reusejp_5623_;
}
v_reusejp_5623_:
{
lean_object* v___x_5625_; lean_object* v___x_5627_; uint8_t v_isShared_5628_; uint8_t v_isSharedCheck_5632_; 
v___x_5625_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5584_, v_isExporting_5588_, v___x_5602_, v___y_5582_, v___x_5614_, v___x_5624_);
lean_dec_ref(v___x_5624_);
v_isSharedCheck_5632_ = !lean_is_exclusive(v___x_5625_);
if (v_isSharedCheck_5632_ == 0)
{
lean_object* v_unused_5633_; 
v_unused_5633_ = lean_ctor_get(v___x_5625_, 0);
lean_dec(v_unused_5633_);
v___x_5627_ = v___x_5625_;
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
else
{
lean_dec(v___x_5625_);
v___x_5627_ = lean_box(0);
v_isShared_5628_ = v_isSharedCheck_5632_;
goto v_resetjp_5626_;
}
v_resetjp_5626_:
{
lean_object* v___x_5630_; 
if (v_isShared_5628_ == 0)
{
lean_ctor_set(v___x_5627_, 0, v_a_5619_);
v___x_5630_ = v___x_5627_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v_a_5619_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
}
}
else
{
lean_object* v_a_5636_; lean_object* v___x_5637_; lean_object* v___x_5638_; lean_object* v___x_5640_; uint8_t v_isShared_5641_; uint8_t v_isSharedCheck_5645_; 
v_a_5636_ = lean_ctor_get(v_r_5618_, 0);
lean_inc(v_a_5636_);
lean_dec_ref_known(v_r_5618_, 1);
v___x_5637_ = lean_box(0);
v___x_5638_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5584_, v_isExporting_5588_, v___x_5602_, v___y_5582_, v___x_5614_, v___x_5637_);
v_isSharedCheck_5645_ = !lean_is_exclusive(v___x_5638_);
if (v_isSharedCheck_5645_ == 0)
{
lean_object* v_unused_5646_; 
v_unused_5646_ = lean_ctor_get(v___x_5638_, 0);
lean_dec(v_unused_5646_);
v___x_5640_ = v___x_5638_;
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
else
{
lean_dec(v___x_5638_);
v___x_5640_ = lean_box(0);
v_isShared_5641_ = v_isSharedCheck_5645_;
goto v_resetjp_5639_;
}
v_resetjp_5639_:
{
lean_object* v___x_5643_; 
if (v_isShared_5641_ == 0)
{
lean_ctor_set_tag(v___x_5640_, 1);
lean_ctor_set(v___x_5640_, 0, v_a_5636_);
v___x_5643_ = v___x_5640_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5644_; 
v_reuseFailAlloc_5644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5644_, 0, v_a_5636_);
v___x_5643_ = v_reuseFailAlloc_5644_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
return v___x_5643_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5653_, lean_object* v_isExporting_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_){
_start:
{
uint8_t v_isExporting_boxed_5660_; lean_object* v_res_5661_; 
v_isExporting_boxed_5660_ = lean_unbox(v_isExporting_5654_);
v_res_5661_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5653_, v_isExporting_boxed_5660_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_);
lean_dec(v___y_5658_);
lean_dec_ref(v___y_5657_);
lean_dec(v___y_5656_);
lean_dec_ref(v___y_5655_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5662_, uint8_t v_when_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_, lean_object* v___y_5667_){
_start:
{
if (v_when_5663_ == 0)
{
lean_object* v___x_5669_; 
lean_inc(v___y_5667_);
lean_inc_ref(v___y_5666_);
lean_inc(v___y_5665_);
lean_inc_ref(v___y_5664_);
v___x_5669_ = lean_apply_5(v_x_5662_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_, lean_box(0));
return v___x_5669_;
}
else
{
uint8_t v___x_5670_; lean_object* v___x_5671_; 
v___x_5670_ = 0;
v___x_5671_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5662_, v___x_5670_, v___y_5664_, v___y_5665_, v___y_5666_, v___y_5667_);
return v___x_5671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5672_, lean_object* v_when_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_){
_start:
{
uint8_t v_when_boxed_5679_; lean_object* v_res_5680_; 
v_when_boxed_5679_ = lean_unbox(v_when_5673_);
v_res_5680_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5672_, v_when_boxed_5679_, v___y_5674_, v___y_5675_, v___y_5676_, v___y_5677_);
lean_dec(v___y_5677_);
lean_dec_ref(v___y_5676_);
lean_dec(v___y_5675_);
lean_dec_ref(v___y_5674_);
return v_res_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
lean_object* v___x_5687_; lean_object* v_a_5688_; lean_object* v___x_5689_; uint8_t v___x_5690_; lean_object* v___x_5691_; 
v___x_5687_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5681_, v___y_5683_);
v_a_5688_ = lean_ctor_get(v___x_5687_, 0);
lean_inc(v_a_5688_);
lean_dec_ref(v___x_5687_);
v___x_5689_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5689_, 0, v_a_5688_);
v___x_5690_ = 1;
v___x_5691_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5689_, v___x_5690_, v___y_5682_, v___y_5683_, v___y_5684_, v___y_5685_);
return v___x_5691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_){
_start:
{
lean_object* v_res_5698_; 
v_res_5698_ = l_Lean_Meta_letToHave___lam__0(v_e_5692_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
lean_dec(v___y_5696_);
lean_dec_ref(v___y_5695_);
lean_dec(v___y_5694_);
lean_dec_ref(v___y_5693_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5700_, lean_object* v_a_5701_, lean_object* v_a_5702_, lean_object* v_a_5703_, lean_object* v_a_5704_){
_start:
{
lean_object* v_options_5706_; lean_object* v___f_5707_; lean_object* v___x_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; 
v_options_5706_ = lean_ctor_get(v_a_5703_, 2);
v___f_5707_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5707_, 0, v_e_5700_);
v___x_5708_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5709_ = lean_box(0);
v___x_5710_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5708_, v_options_5706_, v___f_5707_, v___x_5709_, v_a_5701_, v_a_5702_, v_a_5703_, v_a_5704_);
return v___x_5710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5711_, lean_object* v_a_5712_, lean_object* v_a_5713_, lean_object* v_a_5714_, lean_object* v_a_5715_, lean_object* v_a_5716_){
_start:
{
lean_object* v_res_5717_; 
v_res_5717_ = l_Lean_Meta_letToHave(v_e_5711_, v_a_5712_, v_a_5713_, v_a_5714_, v_a_5715_);
lean_dec(v_a_5715_);
lean_dec_ref(v_a_5714_);
lean_dec(v_a_5713_);
lean_dec_ref(v_a_5712_);
return v_res_5717_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5718_, lean_object* v_x_5719_, uint8_t v_isExporting_5720_, lean_object* v___y_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_){
_start:
{
lean_object* v___x_5726_; 
v___x_5726_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5719_, v_isExporting_5720_, v___y_5721_, v___y_5722_, v___y_5723_, v___y_5724_);
return v___x_5726_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5727_, lean_object* v_x_5728_, lean_object* v_isExporting_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_, lean_object* v___y_5734_){
_start:
{
uint8_t v_isExporting_boxed_5735_; lean_object* v_res_5736_; 
v_isExporting_boxed_5735_ = lean_unbox(v_isExporting_5729_);
v_res_5736_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5727_, v_x_5728_, v_isExporting_boxed_5735_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
lean_dec(v___y_5733_);
lean_dec_ref(v___y_5732_);
lean_dec(v___y_5731_);
lean_dec_ref(v___y_5730_);
return v_res_5736_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5737_, lean_object* v_x_5738_, uint8_t v_when_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_){
_start:
{
lean_object* v___x_5745_; 
v___x_5745_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5738_, v_when_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_);
return v___x_5745_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5746_, lean_object* v_x_5747_, lean_object* v_when_5748_, lean_object* v___y_5749_, lean_object* v___y_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_){
_start:
{
uint8_t v_when_boxed_5754_; lean_object* v_res_5755_; 
v_when_boxed_5754_ = lean_unbox(v_when_5748_);
v_res_5755_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5746_, v_x_5747_, v_when_boxed_5754_, v___y_5749_, v___y_5750_, v___y_5751_, v___y_5752_);
lean_dec(v___y_5752_);
lean_dec_ref(v___y_5751_);
lean_dec(v___y_5750_);
lean_dec_ref(v___y_5749_);
return v_res_5755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5812_; uint8_t v___x_5813_; lean_object* v___x_5814_; lean_object* v___x_5815_; 
v___x_5812_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5813_ = 0;
v___x_5814_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5815_ = l_Lean_registerTraceClass(v___x_5812_, v___x_5813_, v___x_5814_);
if (lean_obj_tag(v___x_5815_) == 0)
{
lean_object* v___x_5816_; lean_object* v___x_5817_; 
lean_dec_ref_known(v___x_5815_, 1);
v___x_5816_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5817_ = l_Lean_registerTraceClass(v___x_5816_, v___x_5813_, v___x_5814_);
return v___x_5817_;
}
else
{
return v___x_5815_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5818_){
_start:
{
lean_object* v_res_5819_; 
v_res_5819_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5819_;
}
}
lean_object* runtime_initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* runtime_initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* runtime_initialize_Lean_AddDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_While(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_LetToHave_instInhabitedResult_default = _init_l_Lean_Meta_LetToHave_instInhabitedResult_default();
lean_mark_persistent(l_Lean_Meta_LetToHave_instInhabitedResult_default);
l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult = _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult();
lean_mark_persistent(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult);
res = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin);
lean_object* initialize_Lean_ReservedNameAction(uint8_t builtin);
lean_object* initialize_Lean_AddDecl(uint8_t builtin);
lean_object* initialize_Lean_Meta_Transform(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin);
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_While(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ReservedNameAction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_AddDecl(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Transform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectMVars(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_While(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_LetToHave(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_LetToHave(builtin);
}
#ifdef __cplusplus
}
#endif
