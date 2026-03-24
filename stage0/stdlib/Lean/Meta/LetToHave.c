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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
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
lean_object* lean_panic_fn(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
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
lean_object* l_Lean_Meta_getConfig___redArg(lean_object*);
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
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default;
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
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__0;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1;
static const lean_array_object l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__2 = (const lean_object*)&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "_private.Lean.Meta.LetToHave.0.Lean.Meta.LetToHave.visitLambdaLet.finalize"};
static const lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "finalize "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = " : "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "<not-available>"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_value)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__3___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__1_value),LEAN_SCALAR_PTR_LITERAL(77, 3, 170, 90, 194, 179, 10, 17)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0_value;
static const lean_closure_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref(v___x_12_);
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
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2(void){
_start:
{
lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_34_ = lean_box(0);
v___x_35_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__1));
v___x_36_ = l_Lean_Expr_const___override(v___x_35_, v___x_34_);
return v___x_36_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__3(void){
_start:
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = lean_box(0);
v___x_38_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___x_37_);
return v___x_39_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__3);
return v___x_40_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult(void){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default;
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
lean_dec_ref(v_a_488_);
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
lean_dec_ref(v___x_498_);
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
lean_inc_ref(v_a_543_);
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
lean_inc(v_a_678_);
v___x_680_ = l_Lean_FVarIdSet_insert(v_fst_673_, v_a_678_);
lean_inc(v_a_678_);
v___x_699_ = l_Lean_FVarId_isLetVar___redArg(v_a_678_, v___x_679_, v___y_661_, v___y_663_, v___y_664_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; uint8_t v___x_701_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
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
lean_dec_ref(v___x_702_);
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
lean_dec_ref(v___x_685_);
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
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v___x_736_ = lean_unsigned_to_nat(16u);
v___x_737_ = lean_mk_array(v___x_736_, v___x_735_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__0, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__0_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__0);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__3(void){
_start:
{
lean_object* v___x_743_; lean_object* v_visited_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = ((lean_object*)(l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__2));
v_visited_744_ = lean_box(1);
v___x_745_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_visited_744_);
lean_ctor_set(v___x_746_, 2, v___x_743_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_b_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_fst_755_; lean_object* v_snd_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_802_; 
v_fst_755_ = lean_ctor_get(v_b_747_, 0);
v_snd_756_ = lean_ctor_get(v_b_747_, 1);
v_isSharedCheck_802_ = !lean_is_exclusive(v_b_747_);
if (v_isSharedCheck_802_ == 0)
{
v___x_758_ = v_b_747_;
v_isShared_759_ = v_isSharedCheck_802_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_snd_756_);
lean_inc(v_fst_755_);
lean_dec(v_b_747_);
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
lean_dec_ref(v___x_767_);
v___x_769_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__3, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__3_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__3);
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
lean_dec_ref(v___x_777_);
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
v_b_747_ = v___x_785_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_b_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_b_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
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
v___x_825_ = l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v___x_824_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
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
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object* v_mvarId_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_mctx_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = lean_st_ref_get(v___y_888_);
v_mctx_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc_ref(v_mctx_891_);
lean_dec(v___x_890_);
v___x_892_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_891_, v_mvarId_887_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object* v_mvarId_894_, lean_object* v___y_895_, lean_object* v___y_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_894_, v___y_895_);
lean_dec(v___y_895_);
lean_dec(v_mvarId_894_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object* v_mvarId_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_898_, v___y_902_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object* v_mvarId_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_);
lean_dec(v___y_913_);
lean_dec_ref(v___y_912_);
lean_dec(v___y_911_);
lean_dec_ref(v___y_910_);
lean_dec(v___y_909_);
lean_dec(v___y_908_);
lean_dec(v_mvarId_907_);
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object* v_a_916_, lean_object* v_as_917_, size_t v_sz_918_, size_t v_i_919_, lean_object* v_b_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v_a_929_; uint8_t v___x_933_; 
v___x_933_ = lean_usize_dec_lt(v_i_919_, v_sz_918_);
if (v___x_933_ == 0)
{
lean_object* v___x_934_; 
lean_dec_ref(v_a_916_);
v___x_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_934_, 0, v_b_920_);
return v___x_934_;
}
else
{
lean_object* v_array_935_; lean_object* v_start_936_; lean_object* v_stop_937_; uint8_t v___x_938_; 
v_array_935_ = lean_ctor_get(v_b_920_, 0);
v_start_936_ = lean_ctor_get(v_b_920_, 1);
v_stop_937_ = lean_ctor_get(v_b_920_, 2);
v___x_938_ = lean_nat_dec_lt(v_start_936_, v_stop_937_);
if (v___x_938_ == 0)
{
lean_object* v___x_939_; 
lean_dec_ref(v_a_916_);
v___x_939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_939_, 0, v_b_920_);
return v___x_939_;
}
else
{
lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_963_; 
lean_inc(v_stop_937_);
lean_inc(v_start_936_);
lean_inc_ref(v_array_935_);
v_isSharedCheck_963_ = !lean_is_exclusive(v_b_920_);
if (v_isSharedCheck_963_ == 0)
{
lean_object* v_unused_964_; lean_object* v_unused_965_; lean_object* v_unused_966_; 
v_unused_964_ = lean_ctor_get(v_b_920_, 2);
lean_dec(v_unused_964_);
v_unused_965_ = lean_ctor_get(v_b_920_, 1);
lean_dec(v_unused_965_);
v_unused_966_ = lean_ctor_get(v_b_920_, 0);
lean_dec(v_unused_966_);
v___x_941_ = v_b_920_;
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
else
{
lean_dec(v_b_920_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_963_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v_lctx_943_; lean_object* v___x_944_; lean_object* v_a_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
v_lctx_943_ = lean_ctor_get(v_a_916_, 1);
v___x_944_ = lean_array_fget(v_array_935_, v_start_936_);
v_a_945_ = lean_array_uget_borrowed(v_as_917_, v_i_919_);
v___x_946_ = lean_unsigned_to_nat(1u);
v___x_947_ = lean_nat_add(v_start_936_, v___x_946_);
lean_dec(v_start_936_);
if (v_isShared_942_ == 0)
{
lean_ctor_set(v___x_941_, 1, v___x_947_);
v___x_949_ = v___x_941_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_962_; 
v_reuseFailAlloc_962_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_962_, 0, v_array_935_);
lean_ctor_set(v_reuseFailAlloc_962_, 1, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_962_, 2, v_stop_937_);
v___x_949_ = v_reuseFailAlloc_962_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
lean_object* v___x_950_; uint8_t v___x_951_; uint8_t v___x_952_; 
lean_inc_ref(v_lctx_943_);
v___x_950_ = l_Lean_LocalContext_getFVar_x21(v_lctx_943_, v_a_945_);
v___x_951_ = 0;
v___x_952_ = l_Lean_LocalDecl_isLet(v___x_950_, v___x_951_);
lean_dec_ref(v___x_950_);
if (v___x_952_ == 0)
{
lean_dec(v___x_944_);
v_a_929_ = v___x_949_;
goto v___jp_928_;
}
else
{
lean_object* v___x_953_; 
v___x_953_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v___x_944_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_dec_ref(v___x_953_);
v_a_929_ = v___x_949_;
goto v___jp_928_;
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec_ref(v___x_949_);
lean_dec_ref(v_a_916_);
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
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
}
}
}
}
v___jp_928_:
{
size_t v___x_930_; size_t v___x_931_; 
v___x_930_ = ((size_t)1ULL);
v___x_931_ = lean_usize_add(v_i_919_, v___x_930_);
v_i_919_ = v___x_931_;
v_b_920_ = v_a_929_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object* v_a_967_, lean_object* v_as_968_, lean_object* v_sz_969_, lean_object* v_i_970_, lean_object* v_b_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
size_t v_sz_boxed_979_; size_t v_i_boxed_980_; lean_object* v_res_981_; 
v_sz_boxed_979_ = lean_unbox_usize(v_sz_969_);
lean_dec(v_sz_969_);
v_i_boxed_980_ = lean_unbox_usize(v_i_970_);
lean_dec(v_i_970_);
v_res_981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_967_, v_as_968_, v_sz_boxed_979_, v_i_boxed_980_, v_b_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v_as_968_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object* v_as_982_, lean_object* v___y_983_){
_start:
{
if (lean_obj_tag(v_as_982_) == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; 
v___x_985_ = lean_box(0);
v___x_986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_986_, 0, v___x_985_);
return v___x_986_;
}
else
{
lean_object* v_head_987_; lean_object* v_tail_988_; lean_object* v___x_989_; 
v_head_987_ = lean_ctor_get(v_as_982_, 0);
lean_inc(v_head_987_);
v_tail_988_ = lean_ctor_get(v_as_982_, 1);
lean_inc(v_tail_988_);
lean_dec_ref(v_as_982_);
v___x_989_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_head_987_, v___y_983_);
if (lean_obj_tag(v___x_989_) == 0)
{
lean_dec_ref(v___x_989_);
v_as_982_ = v_tail_988_;
goto _start;
}
else
{
lean_dec(v_tail_988_);
return v___x_989_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object* v_as_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v_res_994_; 
v_res_994_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_991_, v___y_992_);
lean_dec(v___y_992_);
return v_res_994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object* v_mvarId_995_, lean_object* v_args_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_){
_start:
{
lean_object* v___x_1004_; lean_object* v_a_1005_; lean_object* v___x_1007_; uint8_t v_isShared_1008_; uint8_t v_isSharedCheck_1061_; 
v___x_1004_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_995_, v_a_1000_);
v_a_1005_ = lean_ctor_get(v___x_1004_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v___x_1004_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1007_ = v___x_1004_;
v_isShared_1008_ = v_isSharedCheck_1061_;
goto v_resetjp_1006_;
}
else
{
lean_inc(v_a_1005_);
lean_dec(v___x_1004_);
v___x_1007_ = lean_box(0);
v_isShared_1008_ = v_isSharedCheck_1061_;
goto v_resetjp_1006_;
}
v_resetjp_1006_:
{
if (lean_obj_tag(v_a_1005_) == 1)
{
lean_object* v_val_1009_; lean_object* v_fvars_1010_; lean_object* v_mvarIdPending_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; uint8_t v___x_1014_; 
lean_del_object(v___x_1007_);
v_val_1009_ = lean_ctor_get(v_a_1005_, 0);
lean_inc(v_val_1009_);
lean_dec_ref(v_a_1005_);
v_fvars_1010_ = lean_ctor_get(v_val_1009_, 0);
lean_inc_ref(v_fvars_1010_);
v_mvarIdPending_1011_ = lean_ctor_get(v_val_1009_, 1);
lean_inc(v_mvarIdPending_1011_);
lean_dec(v_val_1009_);
v___x_1012_ = lean_array_get_size(v_fvars_1010_);
v___x_1013_ = lean_array_get_size(v_args_996_);
v___x_1014_ = lean_nat_dec_le(v___x_1012_, v___x_1013_);
if (v___x_1014_ == 0)
{
lean_object* v___x_1015_; 
lean_dec(v_mvarIdPending_1011_);
lean_dec_ref(v_fvars_1010_);
lean_dec_ref(v_args_996_);
lean_inc(v_a_997_);
v___x_1015_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_a_997_, v_a_1000_);
if (lean_obj_tag(v___x_1015_) == 0)
{
lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1023_; 
v_isSharedCheck_1023_ = !lean_is_exclusive(v___x_1015_);
if (v_isSharedCheck_1023_ == 0)
{
lean_object* v_unused_1024_; 
v_unused_1024_ = lean_ctor_get(v___x_1015_, 0);
lean_dec(v_unused_1024_);
v___x_1017_ = v___x_1015_;
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
else
{
lean_dec(v___x_1015_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1023_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1019_; lean_object* v___x_1021_; 
v___x_1019_ = lean_box(0);
if (v_isShared_1018_ == 0)
{
lean_ctor_set(v___x_1017_, 0, v___x_1019_);
v___x_1021_ = v___x_1017_;
goto v_reusejp_1020_;
}
else
{
lean_object* v_reuseFailAlloc_1022_; 
v_reuseFailAlloc_1022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1022_, 0, v___x_1019_);
v___x_1021_ = v_reuseFailAlloc_1022_;
goto v_reusejp_1020_;
}
v_reusejp_1020_:
{
return v___x_1021_;
}
}
}
else
{
return v___x_1015_;
}
}
else
{
lean_object* v___x_1025_; 
v___x_1025_ = l_Lean_MVarId_getDecl(v_mvarIdPending_1011_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; size_t v_sz_1029_; size_t v___x_1030_; lean_object* v___x_1031_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref(v___x_1025_);
v___x_1027_ = lean_unsigned_to_nat(0u);
v___x_1028_ = l_Array_toSubarray___redArg(v_args_996_, v___x_1027_, v___x_1013_);
v_sz_1029_ = lean_array_size(v_fvars_1010_);
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1026_, v_fvars_1010_, v_sz_1029_, v___x_1030_, v___x_1028_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_);
lean_dec_ref(v_fvars_1010_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1039_; 
v_isSharedCheck_1039_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1039_ == 0)
{
lean_object* v_unused_1040_; 
v_unused_1040_ = lean_ctor_get(v___x_1031_, 0);
lean_dec(v_unused_1040_);
v___x_1033_ = v___x_1031_;
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
else
{
lean_dec(v___x_1031_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1039_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1035_; lean_object* v___x_1037_; 
v___x_1035_ = lean_box(0);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1035_);
v___x_1037_ = v___x_1033_;
goto v_reusejp_1036_;
}
else
{
lean_object* v_reuseFailAlloc_1038_; 
v_reuseFailAlloc_1038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1038_, 0, v___x_1035_);
v___x_1037_ = v_reuseFailAlloc_1038_;
goto v_reusejp_1036_;
}
v_reusejp_1036_:
{
return v___x_1037_;
}
}
}
else
{
lean_object* v_a_1041_; lean_object* v___x_1043_; uint8_t v_isShared_1044_; uint8_t v_isSharedCheck_1048_; 
v_a_1041_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1048_ == 0)
{
v___x_1043_ = v___x_1031_;
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
else
{
lean_inc(v_a_1041_);
lean_dec(v___x_1031_);
v___x_1043_ = lean_box(0);
v_isShared_1044_ = v_isSharedCheck_1048_;
goto v_resetjp_1042_;
}
v_resetjp_1042_:
{
lean_object* v___x_1046_; 
if (v_isShared_1044_ == 0)
{
v___x_1046_ = v___x_1043_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v_a_1041_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
}
else
{
lean_object* v_a_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1056_; 
lean_dec_ref(v_fvars_1010_);
lean_dec_ref(v_args_996_);
v_a_1049_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1056_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1056_ == 0)
{
v___x_1051_ = v___x_1025_;
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_a_1049_);
lean_dec(v___x_1025_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1056_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1054_; 
if (v_isShared_1052_ == 0)
{
v___x_1054_ = v___x_1051_;
goto v_reusejp_1053_;
}
else
{
lean_object* v_reuseFailAlloc_1055_; 
v_reuseFailAlloc_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1055_, 0, v_a_1049_);
v___x_1054_ = v_reuseFailAlloc_1055_;
goto v_reusejp_1053_;
}
v_reusejp_1053_:
{
return v___x_1054_;
}
}
}
}
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1059_; 
lean_dec(v_a_1005_);
lean_dec_ref(v_args_996_);
v___x_1057_ = lean_box(0);
if (v_isShared_1008_ == 0)
{
lean_ctor_set(v___x_1007_, 0, v___x_1057_);
v___x_1059_ = v___x_1007_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object* v_mvarId_1062_, lean_object* v_args_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1062_, v_args_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec(v_a_1064_);
lean_dec(v_mvarId_1062_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object* v_as_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1072_, v___y_1076_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object* v_as_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v_res_1089_; 
v_res_1089_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, v___y_1087_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec(v___y_1082_);
return v_res_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object* v_e_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_, lean_object* v_a_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
v___x_1100_ = l_Lean_Expr_mvarId_x21(v_e_1092_);
v___x_1101_ = l_Lean_MVarId_findDecl_x3f___redArg(v___x_1100_, v_a_1096_);
if (lean_obj_tag(v___x_1101_) == 0)
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1132_; 
v_a_1102_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1132_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1132_ == 0)
{
v___x_1104_ = v___x_1101_;
v_isShared_1105_ = v_isSharedCheck_1132_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1101_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1132_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
if (lean_obj_tag(v_a_1102_) == 1)
{
lean_object* v_val_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1130_; 
v_val_1106_ = lean_ctor_get(v_a_1102_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v_a_1102_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1108_ = v_a_1102_;
v_isShared_1109_ = v_isSharedCheck_1130_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_val_1106_);
lean_dec(v_a_1102_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1130_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
uint8_t v___x_1119_; 
v___x_1119_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1093_);
if (v___x_1119_ == 0)
{
lean_dec(v___x_1100_);
goto v___jp_1110_;
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_1121_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v___x_1100_, v___x_1120_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
lean_dec(v___x_1100_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_dec_ref(v___x_1121_);
goto v___jp_1110_;
}
else
{
lean_object* v_a_1122_; lean_object* v___x_1124_; uint8_t v_isShared_1125_; uint8_t v_isSharedCheck_1129_; 
lean_del_object(v___x_1108_);
lean_dec(v_val_1106_);
lean_del_object(v___x_1104_);
lean_dec_ref(v_e_1092_);
v_a_1122_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1124_ = v___x_1121_;
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
else
{
lean_inc(v_a_1122_);
lean_dec(v___x_1121_);
v___x_1124_ = lean_box(0);
v_isShared_1125_ = v_isSharedCheck_1129_;
goto v_resetjp_1123_;
}
v_resetjp_1123_:
{
lean_object* v___x_1127_; 
if (v_isShared_1125_ == 0)
{
v___x_1127_ = v___x_1124_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1128_; 
v_reuseFailAlloc_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
v___x_1127_ = v_reuseFailAlloc_1128_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
return v___x_1127_;
}
}
}
}
v___jp_1110_:
{
lean_object* v_type_1111_; lean_object* v___x_1113_; 
v_type_1111_ = lean_ctor_get(v_val_1106_, 2);
lean_inc_ref(v_type_1111_);
lean_dec(v_val_1106_);
if (v_isShared_1109_ == 0)
{
lean_ctor_set(v___x_1108_, 0, v_type_1111_);
v___x_1113_ = v___x_1108_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_type_1111_);
v___x_1113_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
lean_object* v___x_1114_; lean_object* v___x_1116_; 
v___x_1114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1114_, 0, v_e_1092_);
lean_ctor_set(v___x_1114_, 1, v___x_1113_);
if (v_isShared_1105_ == 0)
{
lean_ctor_set(v___x_1104_, 0, v___x_1114_);
v___x_1116_ = v___x_1104_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v___x_1114_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
}
}
else
{
lean_object* v___x_1131_; 
lean_del_object(v___x_1104_);
lean_dec(v_a_1102_);
lean_dec_ref(v_e_1092_);
v___x_1131_ = l_Lean_Meta_throwUnknownMVar___redArg(v___x_1100_, v_a_1095_, v_a_1096_, v_a_1097_, v_a_1098_);
return v___x_1131_;
}
}
}
else
{
lean_object* v_a_1133_; lean_object* v___x_1135_; uint8_t v_isShared_1136_; uint8_t v_isSharedCheck_1140_; 
lean_dec(v___x_1100_);
lean_dec_ref(v_e_1092_);
v_a_1133_ = lean_ctor_get(v___x_1101_, 0);
v_isSharedCheck_1140_ = !lean_is_exclusive(v___x_1101_);
if (v_isSharedCheck_1140_ == 0)
{
v___x_1135_ = v___x_1101_;
v_isShared_1136_ = v_isSharedCheck_1140_;
goto v_resetjp_1134_;
}
else
{
lean_inc(v_a_1133_);
lean_dec(v___x_1101_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object* v_e_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_, lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1141_, v_a_1142_, v_a_1143_, v_a_1144_, v_a_1145_, v_a_1146_, v_a_1147_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
lean_dec(v_a_1145_);
lean_dec_ref(v_a_1144_);
lean_dec(v_a_1143_);
lean_dec(v_a_1142_);
return v_res_1149_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_instMonadEIO(lean_box(0));
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object* v_msg_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_toApplicative_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1228_; 
v___x_1163_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0);
v___x_1164_ = l_StateRefT_x27_instMonad___redArg(v___x_1163_);
v_toApplicative_1165_ = lean_ctor_get(v___x_1164_, 0);
v_isSharedCheck_1228_ = !lean_is_exclusive(v___x_1164_);
if (v_isSharedCheck_1228_ == 0)
{
lean_object* v_unused_1229_; 
v_unused_1229_ = lean_ctor_get(v___x_1164_, 1);
lean_dec(v_unused_1229_);
v___x_1167_ = v___x_1164_;
v_isShared_1168_ = v_isSharedCheck_1228_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_toApplicative_1165_);
lean_dec(v___x_1164_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1228_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v_toFunctor_1169_; lean_object* v_toSeq_1170_; lean_object* v_toSeqLeft_1171_; lean_object* v_toSeqRight_1172_; lean_object* v___x_1174_; uint8_t v_isShared_1175_; uint8_t v_isSharedCheck_1226_; 
v_toFunctor_1169_ = lean_ctor_get(v_toApplicative_1165_, 0);
v_toSeq_1170_ = lean_ctor_get(v_toApplicative_1165_, 2);
v_toSeqLeft_1171_ = lean_ctor_get(v_toApplicative_1165_, 3);
v_toSeqRight_1172_ = lean_ctor_get(v_toApplicative_1165_, 4);
v_isSharedCheck_1226_ = !lean_is_exclusive(v_toApplicative_1165_);
if (v_isSharedCheck_1226_ == 0)
{
lean_object* v_unused_1227_; 
v_unused_1227_ = lean_ctor_get(v_toApplicative_1165_, 1);
lean_dec(v_unused_1227_);
v___x_1174_ = v_toApplicative_1165_;
v_isShared_1175_ = v_isSharedCheck_1226_;
goto v_resetjp_1173_;
}
else
{
lean_inc(v_toSeqRight_1172_);
lean_inc(v_toSeqLeft_1171_);
lean_inc(v_toSeq_1170_);
lean_inc(v_toFunctor_1169_);
lean_dec(v_toApplicative_1165_);
v___x_1174_ = lean_box(0);
v_isShared_1175_ = v_isSharedCheck_1226_;
goto v_resetjp_1173_;
}
v_resetjp_1173_:
{
lean_object* v___f_1176_; lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___x_1185_; 
v___f_1176_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1));
v___f_1177_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1169_);
v___f_1178_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1178_, 0, v_toFunctor_1169_);
v___f_1179_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1179_, 0, v_toFunctor_1169_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___f_1178_);
lean_ctor_set(v___x_1180_, 1, v___f_1179_);
v___f_1181_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1181_, 0, v_toSeqRight_1172_);
v___f_1182_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1182_, 0, v_toSeqLeft_1171_);
v___f_1183_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1183_, 0, v_toSeq_1170_);
if (v_isShared_1175_ == 0)
{
lean_ctor_set(v___x_1174_, 4, v___f_1181_);
lean_ctor_set(v___x_1174_, 3, v___f_1182_);
lean_ctor_set(v___x_1174_, 2, v___f_1183_);
lean_ctor_set(v___x_1174_, 1, v___f_1176_);
lean_ctor_set(v___x_1174_, 0, v___x_1180_);
v___x_1185_ = v___x_1174_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1225_; 
v_reuseFailAlloc_1225_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1225_, 0, v___x_1180_);
lean_ctor_set(v_reuseFailAlloc_1225_, 1, v___f_1176_);
lean_ctor_set(v_reuseFailAlloc_1225_, 2, v___f_1183_);
lean_ctor_set(v_reuseFailAlloc_1225_, 3, v___f_1182_);
lean_ctor_set(v_reuseFailAlloc_1225_, 4, v___f_1181_);
v___x_1185_ = v_reuseFailAlloc_1225_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
lean_object* v___x_1187_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___f_1177_);
lean_ctor_set(v___x_1167_, 0, v___x_1185_);
v___x_1187_ = v___x_1167_;
goto v_reusejp_1186_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1185_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v___f_1177_);
v___x_1187_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1186_;
}
v_reusejp_1186_:
{
lean_object* v___x_1188_; lean_object* v_toApplicative_1189_; lean_object* v___x_1191_; uint8_t v_isShared_1192_; uint8_t v_isSharedCheck_1222_; 
v___x_1188_ = l_StateRefT_x27_instMonad___redArg(v___x_1187_);
v_toApplicative_1189_ = lean_ctor_get(v___x_1188_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1188_);
if (v_isSharedCheck_1222_ == 0)
{
lean_object* v_unused_1223_; 
v_unused_1223_ = lean_ctor_get(v___x_1188_, 1);
lean_dec(v_unused_1223_);
v___x_1191_ = v___x_1188_;
v_isShared_1192_ = v_isSharedCheck_1222_;
goto v_resetjp_1190_;
}
else
{
lean_inc(v_toApplicative_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_box(0);
v_isShared_1192_ = v_isSharedCheck_1222_;
goto v_resetjp_1190_;
}
v_resetjp_1190_:
{
lean_object* v_toFunctor_1193_; lean_object* v_toSeq_1194_; lean_object* v_toSeqLeft_1195_; lean_object* v_toSeqRight_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1220_; 
v_toFunctor_1193_ = lean_ctor_get(v_toApplicative_1189_, 0);
v_toSeq_1194_ = lean_ctor_get(v_toApplicative_1189_, 2);
v_toSeqLeft_1195_ = lean_ctor_get(v_toApplicative_1189_, 3);
v_toSeqRight_1196_ = lean_ctor_get(v_toApplicative_1189_, 4);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_toApplicative_1189_);
if (v_isSharedCheck_1220_ == 0)
{
lean_object* v_unused_1221_; 
v_unused_1221_ = lean_ctor_get(v_toApplicative_1189_, 1);
lean_dec(v_unused_1221_);
v___x_1198_ = v_toApplicative_1189_;
v_isShared_1199_ = v_isSharedCheck_1220_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_toSeqRight_1196_);
lean_inc(v_toSeqLeft_1195_);
lean_inc(v_toSeq_1194_);
lean_inc(v_toFunctor_1193_);
lean_dec(v_toApplicative_1189_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1220_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___f_1200_; lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; lean_object* v___f_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___x_1209_; 
v___f_1200_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3));
v___f_1201_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1193_);
v___f_1202_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1202_, 0, v_toFunctor_1193_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toFunctor_1193_);
v___x_1204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1204_, 0, v___f_1202_);
lean_ctor_set(v___x_1204_, 1, v___f_1203_);
v___f_1205_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1205_, 0, v_toSeqRight_1196_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeqLeft_1195_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toSeq_1194_);
if (v_isShared_1199_ == 0)
{
lean_ctor_set(v___x_1198_, 4, v___f_1205_);
lean_ctor_set(v___x_1198_, 3, v___f_1206_);
lean_ctor_set(v___x_1198_, 2, v___f_1207_);
lean_ctor_set(v___x_1198_, 1, v___f_1200_);
lean_ctor_set(v___x_1198_, 0, v___x_1204_);
v___x_1209_ = v___x_1198_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v___x_1204_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___f_1200_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v___f_1207_);
lean_ctor_set(v_reuseFailAlloc_1219_, 3, v___f_1206_);
lean_ctor_set(v_reuseFailAlloc_1219_, 4, v___f_1205_);
v___x_1209_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
lean_object* v___x_1211_; 
if (v_isShared_1192_ == 0)
{
lean_ctor_set(v___x_1191_, 1, v___f_1201_);
lean_ctor_set(v___x_1191_, 0, v___x_1209_);
v___x_1211_ = v___x_1191_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1218_; 
v_reuseFailAlloc_1218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1218_, 0, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1218_, 1, v___f_1201_);
v___x_1211_ = v_reuseFailAlloc_1218_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___x_1519__overap_1216_; lean_object* v___x_1217_; 
v___x_1212_ = l_StateRefT_x27_instMonad___redArg(v___x_1211_);
v___x_1213_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1214_ = l_instInhabitedOfMonad___redArg(v___x_1212_, v___x_1213_);
v___f_1215_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1215_, 0, v___x_1214_);
v___x_1519__overap_1216_ = lean_panic_fn(v___f_1215_, v_msg_1155_);
lean_inc(v___y_1161_);
lean_inc_ref(v___y_1160_);
lean_inc(v___y_1159_);
lean_inc_ref(v___y_1158_);
lean_inc(v___y_1157_);
lean_inc(v___y_1156_);
v___x_1217_ = lean_apply_7(v___x_1519__overap_1216_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, lean_box(0));
return v___x_1217_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object* v_msg_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1230_, v___y_1231_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1231_);
return v_res_1238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1243_ = lean_unsigned_to_nat(0u);
v___x_1244_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_1244_, 0, v___x_1243_);
lean_ctor_set(v___x_1244_, 1, v___x_1243_);
lean_ctor_set(v___x_1244_, 2, v___x_1243_);
lean_ctor_set(v___x_1244_, 3, v___x_1242_);
lean_ctor_set(v___x_1244_, 4, v___x_1242_);
lean_ctor_set(v___x_1244_, 5, v___x_1242_);
lean_ctor_set(v___x_1244_, 6, v___x_1242_);
lean_ctor_set(v___x_1244_, 7, v___x_1242_);
lean_ctor_set(v___x_1244_, 8, v___x_1242_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = lean_unsigned_to_nat(32u);
v___x_1246_ = lean_mk_empty_array_with_capacity(v___x_1245_);
v___x_1247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1248_ = ((size_t)5ULL);
v___x_1249_ = lean_unsigned_to_nat(0u);
v___x_1250_ = lean_unsigned_to_nat(32u);
v___x_1251_ = lean_mk_empty_array_with_capacity(v___x_1250_);
v___x_1252_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1253_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1253_, 0, v___x_1252_);
lean_ctor_set(v___x_1253_, 1, v___x_1251_);
lean_ctor_set(v___x_1253_, 2, v___x_1249_);
lean_ctor_set(v___x_1253_, 3, v___x_1249_);
lean_ctor_set_usize(v___x_1253_, 4, v___x_1248_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
v___x_1254_ = lean_box(1);
v___x_1255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1256_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1257_, 0, v___x_1256_);
lean_ctor_set(v___x_1257_, 1, v___x_1255_);
lean_ctor_set(v___x_1257_, 2, v___x_1254_);
return v___x_1257_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1260_ = l_Lean_stringToMessageData(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
v___x_1262_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1263_ = l_Lean_stringToMessageData(v___x_1262_);
return v___x_1263_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1266_ = l_Lean_stringToMessageData(v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1269_ = l_Lean_stringToMessageData(v___x_1268_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1272_ = l_Lean_stringToMessageData(v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1275_ = l_Lean_stringToMessageData(v___x_1274_);
return v___x_1275_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1278_ = l_Lean_stringToMessageData(v___x_1277_);
return v___x_1278_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1279_, lean_object* v_declHint_1280_, lean_object* v___y_1281_){
_start:
{
lean_object* v___x_1283_; lean_object* v_env_1284_; uint8_t v___x_1285_; 
v___x_1283_ = lean_st_ref_get(v___y_1281_);
v_env_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc_ref(v_env_1284_);
lean_dec(v___x_1283_);
v___x_1285_ = l_Lean_Name_isAnonymous(v_declHint_1280_);
if (v___x_1285_ == 0)
{
uint8_t v_isExporting_1286_; 
v_isExporting_1286_ = lean_ctor_get_uint8(v_env_1284_, sizeof(void*)*8);
if (v_isExporting_1286_ == 0)
{
lean_object* v___x_1287_; 
lean_dec_ref(v_env_1284_);
lean_dec(v_declHint_1280_);
v___x_1287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1287_, 0, v_msg_1279_);
return v___x_1287_;
}
else
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
lean_inc_ref(v_env_1284_);
v___x_1288_ = l_Lean_Environment_setExporting(v_env_1284_, v___x_1285_);
lean_inc(v_declHint_1280_);
lean_inc_ref(v___x_1288_);
v___x_1289_ = l_Lean_Environment_contains(v___x_1288_, v_declHint_1280_, v_isExporting_1286_);
if (v___x_1289_ == 0)
{
lean_object* v___x_1290_; 
lean_dec_ref(v___x_1288_);
lean_dec_ref(v_env_1284_);
lean_dec(v_declHint_1280_);
v___x_1290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1290_, 0, v_msg_1279_);
return v___x_1290_;
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1295_; lean_object* v_c_1296_; lean_object* v___x_1297_; 
v___x_1291_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1292_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1293_ = l_Lean_Options_empty;
v___x_1294_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1288_);
lean_ctor_set(v___x_1294_, 1, v___x_1291_);
lean_ctor_set(v___x_1294_, 2, v___x_1292_);
lean_ctor_set(v___x_1294_, 3, v___x_1293_);
lean_inc(v_declHint_1280_);
v___x_1295_ = l_Lean_MessageData_ofConstName(v_declHint_1280_, v___x_1285_);
v_c_1296_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1296_, 0, v___x_1294_);
lean_ctor_set(v_c_1296_, 1, v___x_1295_);
v___x_1297_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1284_, v_declHint_1280_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
lean_dec_ref(v_env_1284_);
lean_dec(v_declHint_1280_);
v___x_1298_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1299_, 0, v___x_1298_);
lean_ctor_set(v___x_1299_, 1, v_c_1296_);
v___x_1300_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1299_);
lean_ctor_set(v___x_1301_, 1, v___x_1300_);
v___x_1302_ = l_Lean_MessageData_note(v___x_1301_);
v___x_1303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1303_, 0, v_msg_1279_);
lean_ctor_set(v___x_1303_, 1, v___x_1302_);
v___x_1304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
return v___x_1304_;
}
else
{
lean_object* v_val_1305_; lean_object* v___x_1307_; uint8_t v_isShared_1308_; uint8_t v_isSharedCheck_1340_; 
v_val_1305_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1307_ = v___x_1297_;
v_isShared_1308_ = v_isSharedCheck_1340_;
goto v_resetjp_1306_;
}
else
{
lean_inc(v_val_1305_);
lean_dec(v___x_1297_);
v___x_1307_ = lean_box(0);
v_isShared_1308_ = v_isSharedCheck_1340_;
goto v_resetjp_1306_;
}
v_resetjp_1306_:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_mod_1312_; uint8_t v___x_1313_; 
v___x_1309_ = lean_box(0);
v___x_1310_ = l_Lean_Environment_header(v_env_1284_);
lean_dec_ref(v_env_1284_);
v___x_1311_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1310_);
v_mod_1312_ = lean_array_get(v___x_1309_, v___x_1311_, v_val_1305_);
lean_dec(v_val_1305_);
lean_dec_ref(v___x_1311_);
v___x_1313_ = l_Lean_isPrivateName(v_declHint_1280_);
lean_dec(v_declHint_1280_);
if (v___x_1313_ == 0)
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1314_);
lean_ctor_set(v___x_1315_, 1, v_c_1296_);
v___x_1316_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1315_);
lean_ctor_set(v___x_1317_, 1, v___x_1316_);
v___x_1318_ = l_Lean_MessageData_ofName(v_mod_1312_);
v___x_1319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1319_, 0, v___x_1317_);
lean_ctor_set(v___x_1319_, 1, v___x_1318_);
v___x_1320_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1319_);
lean_ctor_set(v___x_1321_, 1, v___x_1320_);
v___x_1322_ = l_Lean_MessageData_note(v___x_1321_);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v_msg_1279_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1323_);
v___x_1325_ = v___x_1307_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1338_; 
v___x_1327_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1327_);
lean_ctor_set(v___x_1328_, 1, v_c_1296_);
v___x_1329_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1328_);
lean_ctor_set(v___x_1330_, 1, v___x_1329_);
v___x_1331_ = l_Lean_MessageData_ofName(v_mod_1312_);
v___x_1332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1332_, 0, v___x_1330_);
lean_ctor_set(v___x_1332_, 1, v___x_1331_);
v___x_1333_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1332_);
lean_ctor_set(v___x_1334_, 1, v___x_1333_);
v___x_1335_ = l_Lean_MessageData_note(v___x_1334_);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v_msg_1279_);
lean_ctor_set(v___x_1336_, 1, v___x_1335_);
if (v_isShared_1308_ == 0)
{
lean_ctor_set_tag(v___x_1307_, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1336_);
v___x_1338_ = v___x_1307_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v___x_1336_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1341_; 
lean_dec_ref(v_env_1284_);
lean_dec(v_declHint_1280_);
v___x_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1341_, 0, v_msg_1279_);
return v___x_1341_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1342_, lean_object* v_declHint_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1342_, v_declHint_1343_, v___y_1344_);
lean_dec(v___y_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1347_, lean_object* v_declHint_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
lean_object* v___x_1356_; lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1366_; 
v___x_1356_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1347_, v_declHint_1348_, v___y_1354_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1366_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1361_ = l_Lean_unknownIdentifierMessageTag;
v___x_1362_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
lean_ctor_set(v___x_1362_, 1, v_a_1357_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 0, v___x_1362_);
v___x_1364_ = v___x_1359_;
goto v_reusejp_1363_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1362_);
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
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1367_, lean_object* v_declHint_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v_res_1376_; 
v_res_1376_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1367_, v_declHint_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_);
lean_dec(v___y_1374_);
lean_dec_ref(v___y_1373_);
lean_dec(v___y_1372_);
lean_dec_ref(v___y_1371_);
lean_dec(v___y_1370_);
lean_dec(v___y_1369_);
return v_res_1376_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
lean_object* v___x_1383_; lean_object* v_env_1384_; lean_object* v___x_1385_; lean_object* v_mctx_1386_; lean_object* v_lctx_1387_; lean_object* v_options_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1383_ = lean_st_ref_get(v___y_1381_);
v_env_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc_ref(v_env_1384_);
lean_dec(v___x_1383_);
v___x_1385_ = lean_st_ref_get(v___y_1379_);
v_mctx_1386_ = lean_ctor_get(v___x_1385_, 0);
lean_inc_ref(v_mctx_1386_);
lean_dec(v___x_1385_);
v_lctx_1387_ = lean_ctor_get(v___y_1378_, 2);
v_options_1388_ = lean_ctor_get(v___y_1380_, 2);
lean_inc_ref(v_options_1388_);
lean_inc_ref(v_lctx_1387_);
v___x_1389_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1389_, 0, v_env_1384_);
lean_ctor_set(v___x_1389_, 1, v_mctx_1386_);
lean_ctor_set(v___x_1389_, 2, v_lctx_1387_);
lean_ctor_set(v___x_1389_, 3, v_options_1388_);
v___x_1390_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v_msgData_1377_);
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v___x_1390_);
return v___x_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
lean_object* v_res_1398_; 
v_res_1398_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_ref_1405_; lean_object* v___x_1406_; lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1415_; 
v_ref_1405_ = lean_ctor_get(v___y_1402_, 5);
v___x_1406_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
v___x_1409_ = lean_box(0);
v_isShared_1410_ = v_isSharedCheck_1415_;
goto v_resetjp_1408_;
}
v_resetjp_1408_:
{
lean_object* v___x_1411_; lean_object* v___x_1413_; 
lean_inc(v_ref_1405_);
v___x_1411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1411_, 0, v_ref_1405_);
lean_ctor_set(v___x_1411_, 1, v_a_1407_);
if (v_isShared_1410_ == 0)
{
lean_ctor_set_tag(v___x_1409_, 1);
lean_ctor_set(v___x_1409_, 0, v___x_1411_);
v___x_1413_ = v___x_1409_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1411_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
lean_dec(v___y_1420_);
lean_dec_ref(v___y_1419_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1423_, lean_object* v_msg_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_fileName_1432_; lean_object* v_fileMap_1433_; lean_object* v_options_1434_; lean_object* v_currRecDepth_1435_; lean_object* v_maxRecDepth_1436_; lean_object* v_ref_1437_; lean_object* v_currNamespace_1438_; lean_object* v_openDecls_1439_; lean_object* v_initHeartbeats_1440_; lean_object* v_maxHeartbeats_1441_; lean_object* v_quotContext_1442_; lean_object* v_currMacroScope_1443_; uint8_t v_diag_1444_; lean_object* v_cancelTk_x3f_1445_; uint8_t v_suppressElabErrors_1446_; lean_object* v_inheritedTraceOptions_1447_; lean_object* v_ref_1448_; lean_object* v___x_1449_; lean_object* v___x_1450_; 
v_fileName_1432_ = lean_ctor_get(v___y_1429_, 0);
v_fileMap_1433_ = lean_ctor_get(v___y_1429_, 1);
v_options_1434_ = lean_ctor_get(v___y_1429_, 2);
v_currRecDepth_1435_ = lean_ctor_get(v___y_1429_, 3);
v_maxRecDepth_1436_ = lean_ctor_get(v___y_1429_, 4);
v_ref_1437_ = lean_ctor_get(v___y_1429_, 5);
v_currNamespace_1438_ = lean_ctor_get(v___y_1429_, 6);
v_openDecls_1439_ = lean_ctor_get(v___y_1429_, 7);
v_initHeartbeats_1440_ = lean_ctor_get(v___y_1429_, 8);
v_maxHeartbeats_1441_ = lean_ctor_get(v___y_1429_, 9);
v_quotContext_1442_ = lean_ctor_get(v___y_1429_, 10);
v_currMacroScope_1443_ = lean_ctor_get(v___y_1429_, 11);
v_diag_1444_ = lean_ctor_get_uint8(v___y_1429_, sizeof(void*)*14);
v_cancelTk_x3f_1445_ = lean_ctor_get(v___y_1429_, 12);
v_suppressElabErrors_1446_ = lean_ctor_get_uint8(v___y_1429_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1447_ = lean_ctor_get(v___y_1429_, 13);
v_ref_1448_ = l_Lean_replaceRef(v_ref_1423_, v_ref_1437_);
lean_inc_ref(v_inheritedTraceOptions_1447_);
lean_inc(v_cancelTk_x3f_1445_);
lean_inc(v_currMacroScope_1443_);
lean_inc(v_quotContext_1442_);
lean_inc(v_maxHeartbeats_1441_);
lean_inc(v_initHeartbeats_1440_);
lean_inc(v_openDecls_1439_);
lean_inc(v_currNamespace_1438_);
lean_inc(v_maxRecDepth_1436_);
lean_inc(v_currRecDepth_1435_);
lean_inc_ref(v_options_1434_);
lean_inc_ref(v_fileMap_1433_);
lean_inc_ref(v_fileName_1432_);
v___x_1449_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1449_, 0, v_fileName_1432_);
lean_ctor_set(v___x_1449_, 1, v_fileMap_1433_);
lean_ctor_set(v___x_1449_, 2, v_options_1434_);
lean_ctor_set(v___x_1449_, 3, v_currRecDepth_1435_);
lean_ctor_set(v___x_1449_, 4, v_maxRecDepth_1436_);
lean_ctor_set(v___x_1449_, 5, v_ref_1448_);
lean_ctor_set(v___x_1449_, 6, v_currNamespace_1438_);
lean_ctor_set(v___x_1449_, 7, v_openDecls_1439_);
lean_ctor_set(v___x_1449_, 8, v_initHeartbeats_1440_);
lean_ctor_set(v___x_1449_, 9, v_maxHeartbeats_1441_);
lean_ctor_set(v___x_1449_, 10, v_quotContext_1442_);
lean_ctor_set(v___x_1449_, 11, v_currMacroScope_1443_);
lean_ctor_set(v___x_1449_, 12, v_cancelTk_x3f_1445_);
lean_ctor_set(v___x_1449_, 13, v_inheritedTraceOptions_1447_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*14, v_diag_1444_);
lean_ctor_set_uint8(v___x_1449_, sizeof(void*)*14 + 1, v_suppressElabErrors_1446_);
v___x_1450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1424_, v___y_1427_, v___y_1428_, v___x_1449_, v___y_1430_);
lean_dec_ref(v___x_1449_);
return v___x_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1451_, v_msg_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
lean_dec(v___y_1458_);
lean_dec_ref(v___y_1457_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec(v_ref_1451_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1461_, lean_object* v_msg_1462_, lean_object* v_declHint_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_){
_start:
{
lean_object* v___x_1471_; lean_object* v_a_1472_; lean_object* v___x_1473_; 
v___x_1471_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1462_, v_declHint_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1461_, v_a_1472_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1474_, lean_object* v_msg_1475_, lean_object* v_declHint_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1474_, v_msg_1475_, v_declHint_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec(v___y_1477_);
lean_dec(v_ref_1474_);
return v_res_1484_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; 
v___x_1486_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1487_ = l_Lean_stringToMessageData(v___x_1486_);
return v___x_1487_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1490_ = l_Lean_stringToMessageData(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1491_, lean_object* v_constName_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; uint8_t v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1500_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1501_ = 0;
lean_inc(v_constName_1492_);
v___x_1502_ = l_Lean_MessageData_ofConstName(v_constName_1492_, v___x_1501_);
v___x_1503_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1503_, 0, v___x_1500_);
lean_ctor_set(v___x_1503_, 1, v___x_1502_);
v___x_1504_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1505_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1503_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1491_, v___x_1505_, v_constName_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1507_, lean_object* v_constName_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1507_, v_constName_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
lean_dec_ref(v___y_1511_);
lean_dec(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec(v_ref_1507_);
return v_res_1516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1517_, lean_object* v___y_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
lean_object* v_ref_1525_; lean_object* v___x_1526_; 
v_ref_1525_ = lean_ctor_get(v___y_1522_, 5);
v___x_1526_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1525_, v_constName_1517_, v___y_1518_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_res_1535_; 
v_res_1535_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1527_, v___y_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_);
lean_dec(v___y_1533_);
lean_dec_ref(v___y_1532_);
lean_dec(v___y_1531_);
lean_dec_ref(v___y_1530_);
lean_dec(v___y_1529_);
lean_dec(v___y_1528_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v___x_1544_; lean_object* v_env_1545_; uint8_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1544_ = lean_st_ref_get(v___y_1542_);
v_env_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc_ref(v_env_1545_);
lean_dec(v___x_1544_);
v___x_1546_ = 0;
lean_inc(v_constName_1536_);
v___x_1547_ = l_Lean_Environment_findConstVal_x3f(v_env_1545_, v_constName_1536_, v___x_1546_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1551_; uint8_t v_isShared_1552_; uint8_t v_isSharedCheck_1556_; 
lean_dec(v_constName_1536_);
v_val_1549_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1556_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1556_ == 0)
{
v___x_1551_ = v___x_1547_;
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
else
{
lean_inc(v_val_1549_);
lean_dec(v___x_1547_);
v___x_1551_ = lean_box(0);
v_isShared_1552_ = v_isSharedCheck_1556_;
goto v_resetjp_1550_;
}
v_resetjp_1550_:
{
lean_object* v___x_1554_; 
if (v_isShared_1552_ == 0)
{
lean_ctor_set_tag(v___x_1551_, 0);
v___x_1554_ = v___x_1551_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_val_1549_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec(v___y_1558_);
return v_res_1565_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1569_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1570_ = lean_unsigned_to_nat(35u);
v___x_1571_ = lean_unsigned_to_nat(203u);
v___x_1572_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1573_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1574_ = l_mkPanicMessageWithDecl(v___x_1573_, v___x_1572_, v___x_1571_, v___x_1570_, v___x_1569_);
return v___x_1574_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_){
_start:
{
if (lean_obj_tag(v_e_1575_) == 4)
{
lean_object* v_declName_1583_; lean_object* v_us_1584_; lean_object* v___x_1585_; 
v_declName_1583_ = lean_ctor_get(v_e_1575_, 0);
v_us_1584_ = lean_ctor_get(v_e_1575_, 1);
lean_inc(v_declName_1583_);
v___x_1585_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1583_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v_a_1586_; lean_object* v_levelParams_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; uint8_t v___x_1590_; 
v_a_1586_ = lean_ctor_get(v___x_1585_, 0);
lean_inc(v_a_1586_);
lean_dec_ref(v___x_1585_);
v_levelParams_1587_ = lean_ctor_get(v_a_1586_, 1);
v___x_1588_ = l_List_lengthTR___redArg(v_levelParams_1587_);
v___x_1589_ = l_List_lengthTR___redArg(v_us_1584_);
v___x_1590_ = lean_nat_dec_eq(v___x_1588_, v___x_1589_);
lean_dec(v___x_1589_);
lean_dec(v___x_1588_);
if (v___x_1590_ == 0)
{
lean_object* v___x_1591_; 
lean_inc(v_us_1584_);
lean_inc(v_declName_1583_);
lean_dec(v_a_1586_);
lean_dec_ref(v_e_1575_);
v___x_1591_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1583_, v_us_1584_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
return v___x_1591_;
}
else
{
lean_object* v___x_1592_; 
lean_inc(v_us_1584_);
v___x_1592_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1586_, v_us_1584_, v___y_1581_);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v_a_1593_; lean_object* v___x_1595_; uint8_t v_isShared_1596_; uint8_t v_isSharedCheck_1602_; 
v_a_1593_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1602_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1602_ == 0)
{
v___x_1595_ = v___x_1592_;
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
else
{
lean_inc(v_a_1593_);
lean_dec(v___x_1592_);
v___x_1595_ = lean_box(0);
v_isShared_1596_ = v_isSharedCheck_1602_;
goto v_resetjp_1594_;
}
v_resetjp_1594_:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v___x_1597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1597_, 0, v_a_1593_);
v___x_1598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1598_, 0, v_e_1575_);
lean_ctor_set(v___x_1598_, 1, v___x_1597_);
if (v_isShared_1596_ == 0)
{
lean_ctor_set(v___x_1595_, 0, v___x_1598_);
v___x_1600_ = v___x_1595_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1601_; 
v_reuseFailAlloc_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1601_, 0, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1601_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
return v___x_1600_;
}
}
}
else
{
lean_object* v_a_1603_; lean_object* v___x_1605_; uint8_t v_isShared_1606_; uint8_t v_isSharedCheck_1610_; 
lean_dec_ref(v_e_1575_);
v_a_1603_ = lean_ctor_get(v___x_1592_, 0);
v_isSharedCheck_1610_ = !lean_is_exclusive(v___x_1592_);
if (v_isSharedCheck_1610_ == 0)
{
v___x_1605_ = v___x_1592_;
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
else
{
lean_inc(v_a_1603_);
lean_dec(v___x_1592_);
v___x_1605_ = lean_box(0);
v_isShared_1606_ = v_isSharedCheck_1610_;
goto v_resetjp_1604_;
}
v_resetjp_1604_:
{
lean_object* v___x_1608_; 
if (v_isShared_1606_ == 0)
{
v___x_1608_ = v___x_1605_;
goto v_reusejp_1607_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v_a_1603_);
v___x_1608_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1607_;
}
v_reusejp_1607_:
{
return v___x_1608_;
}
}
}
}
}
else
{
lean_object* v_a_1611_; lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1618_; 
lean_dec_ref(v_e_1575_);
v_a_1611_ = lean_ctor_get(v___x_1585_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1585_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1613_ = v___x_1585_;
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
else
{
lean_inc(v_a_1611_);
lean_dec(v___x_1585_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1618_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v___x_1616_; 
if (v_isShared_1614_ == 0)
{
v___x_1616_ = v___x_1613_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
}
else
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
lean_dec_ref(v_e_1575_);
v___x_1619_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1620_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1619_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
return v___x_1620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec(v___y_1622_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1630_, lean_object* v_a_1631_, lean_object* v_a_1632_, lean_object* v_a_1633_, lean_object* v_a_1634_, lean_object* v_a_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v___y_1638_; lean_object* v___x_1639_; 
lean_inc_ref(v_e_1630_);
v___y_1638_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1638_, 0, v_e_1630_);
v___x_1639_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1630_, v___y_1638_, v_a_1631_, v_a_1632_, v_a_1633_, v_a_1634_, v_a_1635_, v_a_1636_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1640_, lean_object* v_a_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v_res_1648_; 
v_res_1648_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1640_, v_a_1641_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_);
lean_dec(v_a_1646_);
lean_dec_ref(v_a_1645_);
lean_dec(v_a_1644_);
lean_dec_ref(v_a_1643_);
lean_dec(v_a_1642_);
lean_dec(v_a_1641_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1649_, lean_object* v_constName_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1659_, lean_object* v_constName_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v_res_1668_; 
v_res_1668_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1659_, v_constName_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
lean_dec(v___y_1666_);
lean_dec_ref(v___y_1665_);
lean_dec(v___y_1664_);
lean_dec_ref(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v___y_1661_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1669_, lean_object* v_ref_1670_, lean_object* v_constName_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1670_, v_constName_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1680_, lean_object* v_ref_1681_, lean_object* v_constName_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v_res_1690_; 
v_res_1690_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1680_, v_ref_1681_, v_constName_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec(v_ref_1681_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1691_, lean_object* v_ref_1692_, lean_object* v_msg_1693_, lean_object* v_declHint_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1692_, v_msg_1693_, v_declHint_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1703_, lean_object* v_ref_1704_, lean_object* v_msg_1705_, lean_object* v_declHint_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v_res_1714_; 
v_res_1714_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1703_, v_ref_1704_, v_msg_1705_, v_declHint_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec(v_ref_1704_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1715_, lean_object* v_declHint_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v___x_1724_; 
v___x_1724_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1715_, v_declHint_1716_, v___y_1722_);
return v___x_1724_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1725_, lean_object* v_declHint_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v_res_1734_; 
v_res_1734_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1725_, v_declHint_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_, v___y_1732_);
lean_dec(v___y_1732_);
lean_dec_ref(v___y_1731_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec(v___y_1727_);
return v_res_1734_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1735_, lean_object* v_ref_1736_, lean_object* v_msg_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_){
_start:
{
lean_object* v___x_1745_; 
v___x_1745_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1736_, v_msg_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
return v___x_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1746_, lean_object* v_ref_1747_, lean_object* v_msg_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v_res_1756_; 
v_res_1756_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1746_, v_ref_1747_, v_msg_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v___y_1752_);
lean_dec_ref(v___y_1751_);
lean_dec(v___y_1750_);
lean_dec(v___y_1749_);
lean_dec(v_ref_1747_);
return v_res_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1757_, lean_object* v_msg_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
lean_object* v___x_1766_; 
v___x_1766_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1758_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1767_, lean_object* v_msg_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v_res_1776_; 
v_res_1776_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1767_, v_msg_1768_, v___y_1769_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
lean_dec(v___y_1774_);
lean_dec_ref(v___y_1773_);
lean_dec(v___y_1772_);
lean_dec_ref(v___y_1771_);
lean_dec(v___y_1770_);
lean_dec(v___y_1769_);
return v_res_1776_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_){
_start:
{
uint8_t v___x_1785_; 
v___x_1785_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1778_);
if (v___x_1785_ == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1786_, 0, v_r_1777_);
return v___x_1786_;
}
else
{
lean_object* v___x_1787_; 
lean_inc_ref(v_r_1777_);
v___x_1787_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1777_, v_a_1779_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1787_) == 0)
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1840_; 
v_a_1788_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1840_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1840_ == 0)
{
v___x_1790_ = v___x_1787_;
v_isShared_1791_ = v_isSharedCheck_1840_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1787_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1840_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v_expr_1792_; lean_object* v___x_1794_; uint8_t v_isShared_1795_; uint8_t v_isSharedCheck_1838_; 
v_expr_1792_ = lean_ctor_get(v_r_1777_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v_r_1777_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v_r_1777_, 1);
lean_dec(v_unused_1839_);
v___x_1794_ = v_r_1777_;
v_isShared_1795_ = v_isSharedCheck_1838_;
goto v_resetjp_1793_;
}
else
{
lean_inc(v_expr_1792_);
lean_dec(v_r_1777_);
v___x_1794_ = lean_box(0);
v_isShared_1795_ = v_isSharedCheck_1838_;
goto v_resetjp_1793_;
}
v_resetjp_1793_:
{
uint8_t v___x_1796_; 
v___x_1796_ = l_Lean_Expr_isSort(v_a_1788_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
lean_del_object(v___x_1790_);
lean_inc(v_a_1783_);
lean_inc_ref(v_a_1782_);
lean_inc(v_a_1781_);
lean_inc_ref(v_a_1780_);
v___x_1797_ = lean_whnf(v_a_1788_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
if (lean_obj_tag(v___x_1797_) == 0)
{
lean_object* v_a_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1822_; 
v_a_1798_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1822_ == 0)
{
v___x_1800_ = v___x_1797_;
v_isShared_1801_ = v_isSharedCheck_1822_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_a_1798_);
lean_dec(v___x_1797_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1822_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
if (lean_obj_tag(v_a_1798_) == 3)
{
lean_object* v___x_1802_; lean_object* v_count_1803_; lean_object* v_results_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1820_; 
v___x_1802_ = lean_st_ref_take(v_a_1779_);
v_count_1803_ = lean_ctor_get(v___x_1802_, 0);
v_results_1804_ = lean_ctor_get(v___x_1802_, 1);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1802_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1806_ = v___x_1802_;
v_isShared_1807_ = v_isSharedCheck_1820_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_results_1804_);
lean_inc(v_count_1803_);
lean_dec(v___x_1802_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1820_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1810_; 
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v_a_1798_);
lean_inc_ref(v_expr_1792_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___x_1808_);
v___x_1810_ = v___x_1794_;
goto v_reusejp_1809_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_expr_1792_);
lean_ctor_set(v_reuseFailAlloc_1819_, 1, v___x_1808_);
v___x_1810_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1809_;
}
v_reusejp_1809_:
{
lean_object* v___x_1811_; lean_object* v___x_1813_; 
lean_inc_ref(v___x_1810_);
v___x_1811_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1804_, v_expr_1792_, v___x_1810_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v___x_1811_);
v___x_1813_ = v___x_1806_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_count_1803_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1811_);
v___x_1813_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_st_ref_set(v_a_1779_, v___x_1813_);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 0, v___x_1810_);
v___x_1816_ = v___x_1800_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1810_);
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
lean_object* v___x_1821_; 
lean_del_object(v___x_1800_);
lean_dec(v_a_1798_);
lean_del_object(v___x_1794_);
v___x_1821_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1792_, v_a_1780_, v_a_1781_, v_a_1782_, v_a_1783_);
return v___x_1821_;
}
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_del_object(v___x_1794_);
lean_dec_ref(v_expr_1792_);
v_a_1823_ = lean_ctor_get(v___x_1797_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1797_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1797_);
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
else
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_a_1788_);
if (v_isShared_1795_ == 0)
{
lean_ctor_set(v___x_1794_, 1, v___x_1831_);
v___x_1833_ = v___x_1794_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_expr_1792_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v___x_1831_);
v___x_1833_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1835_; 
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 0, v___x_1833_);
v___x_1835_ = v___x_1790_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
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
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec_ref(v_r_1777_);
v_a_1841_ = lean_ctor_get(v___x_1787_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1787_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1787_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1849_, lean_object* v_a_1850_, lean_object* v_a_1851_, lean_object* v_a_1852_, lean_object* v_a_1853_, lean_object* v_a_1854_, lean_object* v_a_1855_, lean_object* v_a_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1849_, v_a_1850_, v_a_1851_, v_a_1852_, v_a_1853_, v_a_1854_, v_a_1855_);
lean_dec(v_a_1855_);
lean_dec_ref(v_a_1854_);
lean_dec(v_a_1853_);
lean_dec_ref(v_a_1852_);
lean_dec(v_a_1851_);
lean_dec(v_a_1850_);
return v_res_1857_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1858_){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; 
v___x_1859_ = l_Lean_instInhabitedExpr;
v___x_1860_ = lean_panic_fn(v___x_1859_, v_msg_1858_);
return v___x_1860_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1864_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1865_ = lean_unsigned_to_nat(18u);
v___x_1866_ = lean_unsigned_to_nat(1823u);
v___x_1867_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1868_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1869_ = l_mkPanicMessageWithDecl(v___x_1868_, v___x_1867_, v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1870_, lean_object* v_f_1871_, lean_object* v_a_1872_, lean_object* v_a_1873_, lean_object* v_a_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_, lean_object* v_a_1877_, lean_object* v_a_1878_){
_start:
{
lean_object* v___y_1881_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1888_; lean_object* v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; uint8_t v___y_1897_; lean_object* v___y_1900_; lean_object* v_fType_1915_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; uint8_t v___x_1959_; 
v___x_1959_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1873_);
if (v___x_1959_ == 0)
{
lean_object* v_expr_1960_; lean_object* v_expr_1961_; uint8_t v___y_1963_; 
v_expr_1960_ = lean_ctor_get(v_f_1871_, 0);
lean_inc_ref(v_expr_1960_);
lean_dec_ref(v_f_1871_);
v_expr_1961_ = lean_ctor_get(v_a_1872_, 0);
lean_inc_ref(v_expr_1961_);
lean_dec_ref(v_a_1872_);
if (lean_obj_tag(v_e_1870_) == 5)
{
lean_object* v_fn_1965_; lean_object* v_arg_1966_; size_t v___x_1967_; size_t v___x_1968_; uint8_t v___x_1969_; 
v_fn_1965_ = lean_ctor_get(v_e_1870_, 0);
v_arg_1966_ = lean_ctor_get(v_e_1870_, 1);
v___x_1967_ = lean_ptr_addr(v_fn_1965_);
v___x_1968_ = lean_ptr_addr(v_expr_1960_);
v___x_1969_ = lean_usize_dec_eq(v___x_1967_, v___x_1968_);
if (v___x_1969_ == 0)
{
v___y_1963_ = v___x_1969_;
goto v___jp_1962_;
}
else
{
size_t v___x_1970_; size_t v___x_1971_; uint8_t v___x_1972_; 
v___x_1970_ = lean_ptr_addr(v_arg_1966_);
v___x_1971_ = lean_ptr_addr(v_expr_1961_);
v___x_1972_ = lean_usize_dec_eq(v___x_1970_, v___x_1971_);
v___y_1963_ = v___x_1972_;
goto v___jp_1962_;
}
}
else
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
lean_dec_ref(v_expr_1961_);
lean_dec_ref(v_expr_1960_);
lean_dec_ref(v_e_1870_);
v___x_1973_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1974_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1973_);
v___y_1881_ = v___x_1974_;
goto v___jp_1880_;
}
v___jp_1962_:
{
if (v___y_1963_ == 0)
{
lean_object* v___x_1964_; 
lean_dec_ref(v_e_1870_);
v___x_1964_ = l_Lean_Expr_app___override(v_expr_1960_, v_expr_1961_);
v___y_1881_ = v___x_1964_;
goto v___jp_1880_;
}
else
{
lean_dec_ref(v_expr_1961_);
lean_dec_ref(v_expr_1960_);
v___y_1881_ = v_e_1870_;
goto v___jp_1880_;
}
}
}
else
{
lean_object* v___x_1975_; 
lean_inc_ref(v_f_1871_);
v___x_1975_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1871_, v_a_1874_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1975_) == 0)
{
lean_object* v_a_1976_; uint8_t v___x_1977_; 
v_a_1976_ = lean_ctor_get(v___x_1975_, 0);
lean_inc(v_a_1976_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = l_Lean_Expr_isForall(v_a_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_inc(v_a_1878_);
lean_inc_ref(v_a_1877_);
lean_inc(v_a_1876_);
lean_inc_ref(v_a_1875_);
v___x_1978_ = lean_whnf(v_a_1976_, v_a_1875_, v_a_1876_, v_a_1877_, v_a_1878_);
if (lean_obj_tag(v___x_1978_) == 0)
{
lean_object* v_a_1979_; 
v_a_1979_ = lean_ctor_get(v___x_1978_, 0);
lean_inc(v_a_1979_);
lean_dec_ref(v___x_1978_);
v_fType_1915_ = v_a_1979_;
v___y_1916_ = v_a_1874_;
v___y_1917_ = v_a_1875_;
v___y_1918_ = v_a_1876_;
v___y_1919_ = v_a_1877_;
v___y_1920_ = v_a_1878_;
goto v___jp_1914_;
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
lean_dec_ref(v_a_1872_);
lean_dec_ref(v_f_1871_);
lean_dec_ref(v_e_1870_);
v_a_1980_ = lean_ctor_get(v___x_1978_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1978_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1978_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1978_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
else
{
v_fType_1915_ = v_a_1976_;
v___y_1916_ = v_a_1874_;
v___y_1917_ = v_a_1875_;
v___y_1918_ = v_a_1876_;
v___y_1919_ = v_a_1877_;
v___y_1920_ = v_a_1878_;
goto v___jp_1914_;
}
}
else
{
lean_object* v_a_1988_; lean_object* v___x_1990_; uint8_t v_isShared_1991_; uint8_t v_isSharedCheck_1995_; 
lean_dec_ref(v_a_1872_);
lean_dec_ref(v_f_1871_);
lean_dec_ref(v_e_1870_);
v_a_1988_ = lean_ctor_get(v___x_1975_, 0);
v_isSharedCheck_1995_ = !lean_is_exclusive(v___x_1975_);
if (v_isSharedCheck_1995_ == 0)
{
v___x_1990_ = v___x_1975_;
v_isShared_1991_ = v_isSharedCheck_1995_;
goto v_resetjp_1989_;
}
else
{
lean_inc(v_a_1988_);
lean_dec(v___x_1975_);
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
v___jp_1880_:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_box(0);
v___x_1883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1883_, 0, v___y_1881_);
lean_ctor_set(v___x_1883_, 1, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
return v___x_1884_;
}
v___jp_1885_:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = lean_expr_instantiate1(v___y_1886_, v___y_1887_);
lean_dec_ref(v___y_1887_);
lean_dec_ref(v___y_1886_);
v___x_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1889_);
v___x_1891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___y_1888_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
return v___x_1892_;
}
v___jp_1893_:
{
if (v___y_1897_ == 0)
{
lean_object* v___x_1898_; 
lean_dec_ref(v_e_1870_);
lean_inc_ref(v___y_1896_);
v___x_1898_ = l_Lean_Expr_app___override(v___y_1894_, v___y_1896_);
v___y_1886_ = v___y_1895_;
v___y_1887_ = v___y_1896_;
v___y_1888_ = v___x_1898_;
goto v___jp_1885_;
}
else
{
lean_dec_ref(v___y_1894_);
v___y_1886_ = v___y_1895_;
v___y_1887_ = v___y_1896_;
v___y_1888_ = v_e_1870_;
goto v___jp_1885_;
}
}
v___jp_1899_:
{
if (lean_obj_tag(v_e_1870_) == 5)
{
lean_object* v_expr_1901_; lean_object* v_expr_1902_; lean_object* v_fn_1903_; lean_object* v_arg_1904_; size_t v___x_1905_; size_t v___x_1906_; uint8_t v___x_1907_; 
v_expr_1901_ = lean_ctor_get(v_f_1871_, 0);
lean_inc_ref(v_expr_1901_);
lean_dec_ref(v_f_1871_);
v_expr_1902_ = lean_ctor_get(v_a_1872_, 0);
lean_inc_ref(v_expr_1902_);
lean_dec_ref(v_a_1872_);
v_fn_1903_ = lean_ctor_get(v_e_1870_, 0);
v_arg_1904_ = lean_ctor_get(v_e_1870_, 1);
v___x_1905_ = lean_ptr_addr(v_fn_1903_);
v___x_1906_ = lean_ptr_addr(v_expr_1901_);
v___x_1907_ = lean_usize_dec_eq(v___x_1905_, v___x_1906_);
if (v___x_1907_ == 0)
{
v___y_1894_ = v_expr_1901_;
v___y_1895_ = v___y_1900_;
v___y_1896_ = v_expr_1902_;
v___y_1897_ = v___x_1907_;
goto v___jp_1893_;
}
else
{
size_t v___x_1908_; size_t v___x_1909_; uint8_t v___x_1910_; 
v___x_1908_ = lean_ptr_addr(v_arg_1904_);
v___x_1909_ = lean_ptr_addr(v_expr_1902_);
v___x_1910_ = lean_usize_dec_eq(v___x_1908_, v___x_1909_);
v___y_1894_ = v_expr_1901_;
v___y_1895_ = v___y_1900_;
v___y_1896_ = v_expr_1902_;
v___y_1897_ = v___x_1910_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_expr_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; 
lean_dec_ref(v_f_1871_);
lean_dec_ref(v_e_1870_);
v_expr_1911_ = lean_ctor_get(v_a_1872_, 0);
lean_inc_ref(v_expr_1911_);
lean_dec_ref(v_a_1872_);
v___x_1912_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1913_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1912_);
v___y_1886_ = v___y_1900_;
v___y_1887_ = v_expr_1911_;
v___y_1888_ = v___x_1913_;
goto v___jp_1885_;
}
}
v___jp_1914_:
{
if (lean_obj_tag(v_fType_1915_) == 7)
{
lean_object* v_binderType_1921_; lean_object* v_body_1922_; lean_object* v___x_1923_; 
v_binderType_1921_ = lean_ctor_get(v_fType_1915_, 1);
lean_inc_ref(v_binderType_1921_);
v_body_1922_ = lean_ctor_get(v_fType_1915_, 2);
lean_inc_ref(v_body_1922_);
lean_dec_ref(v_fType_1915_);
lean_inc_ref(v_a_1872_);
v___x_1923_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1872_, v___y_1916_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1923_) == 0)
{
lean_object* v_a_1924_; lean_object* v___x_1925_; 
v_a_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_a_1924_);
lean_dec_ref(v___x_1923_);
v___x_1925_ = l_Lean_Meta_isExprDefEq(v_binderType_1921_, v_a_1924_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1925_) == 0)
{
lean_object* v_a_1926_; uint8_t v___x_1927_; 
v_a_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_a_1926_);
lean_dec_ref(v___x_1925_);
v___x_1927_ = lean_unbox(v_a_1926_);
lean_dec(v_a_1926_);
if (v___x_1927_ == 0)
{
lean_object* v_expr_1928_; lean_object* v_expr_1929_; lean_object* v___x_1930_; 
v_expr_1928_ = lean_ctor_get(v_f_1871_, 0);
v_expr_1929_ = lean_ctor_get(v_a_1872_, 0);
lean_inc_ref(v_expr_1929_);
lean_inc_ref(v_expr_1928_);
v___x_1930_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1928_, v_expr_1929_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_dec_ref(v___x_1930_);
v___y_1900_ = v_body_1922_;
goto v___jp_1899_;
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_dec_ref(v_body_1922_);
lean_dec_ref(v_a_1872_);
lean_dec_ref(v_f_1871_);
lean_dec_ref(v_e_1870_);
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1930_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1930_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
v___y_1900_ = v_body_1922_;
goto v___jp_1899_;
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_body_1922_);
lean_dec_ref(v_a_1872_);
lean_dec_ref(v_f_1871_);
lean_dec_ref(v_e_1870_);
v_a_1939_ = lean_ctor_get(v___x_1925_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1925_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1925_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_body_1922_);
lean_dec_ref(v_binderType_1921_);
lean_dec_ref(v_a_1872_);
lean_dec_ref(v_f_1871_);
lean_dec_ref(v_e_1870_);
v_a_1947_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1923_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1923_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
else
{
lean_object* v_expr_1955_; lean_object* v_expr_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
lean_dec_ref(v_fType_1915_);
lean_dec_ref(v_e_1870_);
v_expr_1955_ = lean_ctor_get(v_f_1871_, 0);
lean_inc_ref(v_expr_1955_);
lean_dec_ref(v_f_1871_);
v_expr_1956_ = lean_ctor_get(v_a_1872_, 0);
lean_inc_ref(v_expr_1956_);
lean_dec_ref(v_a_1872_);
v___x_1957_ = l_Lean_Expr_app___override(v_expr_1955_, v_expr_1956_);
v___x_1958_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1957_, v___y_1917_, v___y_1918_, v___y_1919_, v___y_1920_);
return v___x_1958_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_1996_, lean_object* v_f_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_, lean_object* v_a_2000_, lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_1996_, v_f_1997_, v_a_1998_, v_a_1999_, v_a_2000_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
lean_dec(v_a_2004_);
lean_dec_ref(v_a_2003_);
lean_dec(v_a_2002_);
lean_dec_ref(v_a_2001_);
lean_dec(v_a_2000_);
lean_dec(v_a_1999_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg(lean_object* v_cls_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_options_2013_; uint8_t v_hasTrace_2014_; 
v_options_2013_ = lean_ctor_get(v___y_2011_, 2);
v_hasTrace_2014_ = lean_ctor_get_uint8(v_options_2013_, sizeof(void*)*1);
if (v_hasTrace_2014_ == 0)
{
lean_object* v___x_2015_; lean_object* v___x_2016_; 
lean_dec(v_cls_2010_);
v___x_2015_ = lean_box(v_hasTrace_2014_);
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___x_2015_);
return v___x_2016_;
}
else
{
lean_object* v_inheritedTraceOptions_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v_inheritedTraceOptions_2017_ = lean_ctor_get(v___y_2011_, 13);
v___x_2018_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__1));
v___x_2019_ = l_Lean_Name_append(v___x_2018_, v_cls_2010_);
v___x_2020_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2017_, v_options_2013_, v___x_2019_);
lean_dec(v___x_2019_);
v___x_2021_ = lean_box(v___x_2020_);
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v___x_2021_);
return v___x_2022_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___boxed(lean_object* v_cls_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_){
_start:
{
lean_object* v_res_2026_; 
v_res_2026_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg(v_cls_2023_, v___y_2024_);
lean_dec_ref(v___y_2024_);
return v_res_2026_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_cls_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v___x_2035_; 
v___x_2035_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg(v_cls_2027_, v___y_2032_);
return v___x_2035_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___boxed(lean_object* v_cls_2036_, lean_object* v___y_2037_, lean_object* v___y_2038_, lean_object* v___y_2039_, lean_object* v___y_2040_, lean_object* v___y_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v_cls_2036_, v___y_2037_, v___y_2038_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
lean_dec(v___y_2042_);
lean_dec_ref(v___y_2041_);
lean_dec(v___y_2040_);
lean_dec_ref(v___y_2039_);
lean_dec(v___y_2038_);
lean_dec(v___y_2037_);
return v_res_2044_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v___x_2046_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2047_ = lean_unsigned_to_nat(37u);
v___x_2048_ = lean_unsigned_to_nat(345u);
v___x_2049_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2050_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2051_ = l_mkPanicMessageWithDecl(v___x_2050_, v___x_2049_, v___x_2048_, v___x_2047_, v___x_2046_);
return v___x_2051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2052_, lean_object* v_i_2053_, lean_object* v_a_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_){
_start:
{
lean_object* v_zero_2062_; uint8_t v_isZero_2063_; 
v_zero_2062_ = lean_unsigned_to_nat(0u);
v_isZero_2063_ = lean_nat_dec_eq(v_i_2053_, v_zero_2062_);
if (v_isZero_2063_ == 1)
{
lean_object* v___x_2064_; 
lean_dec(v_i_2053_);
v___x_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2064_, 0, v_a_2054_);
return v___x_2064_;
}
else
{
lean_object* v_one_2065_; lean_object* v_n_2066_; lean_object* v___y_2068_; lean_object* v___y_2072_; lean_object* v___y_2073_; lean_object* v___y_2077_; lean_object* v___y_2078_; lean_object* v___x_2080_; 
v_one_2065_ = lean_unsigned_to_nat(1u);
v_n_2066_ = lean_nat_sub(v_i_2053_, v_one_2065_);
lean_dec(v_i_2053_);
v___x_2080_ = lean_array_fget_borrowed(v_fvars_2052_, v_n_2066_);
if (lean_obj_tag(v___x_2080_) == 1)
{
lean_object* v_fvarId_2081_; lean_object* v___x_2082_; 
v_fvarId_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc_ref(v___y_2057_);
lean_inc(v_fvarId_2081_);
v___x_2082_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2081_, v___y_2057_);
if (lean_obj_tag(v___x_2082_) == 0)
{
lean_object* v_a_2083_; 
v_a_2083_ = lean_ctor_get(v___x_2082_, 0);
lean_inc(v_a_2083_);
lean_dec_ref(v___x_2082_);
if (lean_obj_tag(v_a_2083_) == 1)
{
lean_object* v_val_2084_; 
v_val_2084_ = lean_ctor_get(v_a_2083_, 0);
lean_inc(v_val_2084_);
lean_dec_ref(v_a_2083_);
if (lean_obj_tag(v_val_2084_) == 0)
{
lean_object* v_userName_2085_; lean_object* v_type_2086_; uint8_t v_bi_2087_; lean_object* v_expr_2088_; lean_object* v_type_x3f_2089_; lean_object* v___x_2091_; uint8_t v_isShared_2092_; uint8_t v_isSharedCheck_2110_; 
v_userName_2085_ = lean_ctor_get(v_val_2084_, 2);
lean_inc(v_userName_2085_);
v_type_2086_ = lean_ctor_get(v_val_2084_, 3);
lean_inc_ref(v_type_2086_);
v_bi_2087_ = lean_ctor_get_uint8(v_val_2084_, sizeof(void*)*4);
lean_dec_ref(v_val_2084_);
v_expr_2088_ = lean_ctor_get(v_a_2054_, 0);
v_type_x3f_2089_ = lean_ctor_get(v_a_2054_, 1);
v_isSharedCheck_2110_ = !lean_is_exclusive(v_a_2054_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2091_ = v_a_2054_;
v_isShared_2092_ = v_isSharedCheck_2110_;
goto v_resetjp_2090_;
}
else
{
lean_inc(v_type_x3f_2089_);
lean_inc(v_expr_2088_);
lean_dec(v_a_2054_);
v___x_2091_ = lean_box(0);
v_isShared_2092_ = v_isSharedCheck_2110_;
goto v_resetjp_2090_;
}
v_resetjp_2090_:
{
lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___y_2096_; 
v___x_2093_ = lean_expr_abstract_range(v_type_2086_, v_n_2066_, v_fvars_2052_);
lean_dec_ref(v_type_2086_);
lean_inc_ref(v___x_2093_);
lean_inc(v_userName_2085_);
v___x_2094_ = l_Lean_Expr_lam___override(v_userName_2085_, v___x_2093_, v_expr_2088_, v_bi_2087_);
if (lean_obj_tag(v_type_x3f_2089_) == 0)
{
lean_dec_ref(v___x_2093_);
lean_dec(v_userName_2085_);
v___y_2096_ = v_type_x3f_2089_;
goto v___jp_2095_;
}
else
{
lean_object* v_val_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2109_; 
v_val_2101_ = lean_ctor_get(v_type_x3f_2089_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v_type_x3f_2089_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2103_ = v_type_x3f_2089_;
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_val_2101_);
lean_dec(v_type_x3f_2089_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2109_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2105_; lean_object* v___x_2107_; 
v___x_2105_ = l_Lean_Expr_forallE___override(v_userName_2085_, v___x_2093_, v_val_2101_, v_bi_2087_);
if (v_isShared_2104_ == 0)
{
lean_ctor_set(v___x_2103_, 0, v___x_2105_);
v___x_2107_ = v___x_2103_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v___x_2105_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
v___y_2096_ = v___x_2107_;
goto v___jp_2095_;
}
}
}
v___jp_2095_:
{
lean_object* v___x_2098_; 
if (v_isShared_2092_ == 0)
{
lean_ctor_set(v___x_2091_, 1, v___y_2096_);
lean_ctor_set(v___x_2091_, 0, v___x_2094_);
v___x_2098_ = v___x_2091_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2100_; 
v_reuseFailAlloc_2100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2100_, 0, v___x_2094_);
lean_ctor_set(v_reuseFailAlloc_2100_, 1, v___y_2096_);
v___x_2098_ = v_reuseFailAlloc_2100_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
v_i_2053_ = v_n_2066_;
v_a_2054_ = v___x_2098_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2111_; lean_object* v_type_2112_; lean_object* v_value_2113_; uint8_t v_nondep_2114_; uint8_t v_nondep_2116_; lean_object* v___x_2126_; 
v_userName_2111_ = lean_ctor_get(v_val_2084_, 2);
lean_inc(v_userName_2111_);
v_type_2112_ = lean_ctor_get(v_val_2084_, 3);
lean_inc_ref(v_type_2112_);
v_value_2113_ = lean_ctor_get(v_val_2084_, 4);
lean_inc_ref(v_value_2113_);
v_nondep_2114_ = lean_ctor_get_uint8(v_val_2084_, sizeof(void*)*5);
lean_dec_ref(v_val_2084_);
v___x_2126_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2058_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; uint8_t v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref(v___x_2126_);
v___x_2128_ = 1;
if (v_nondep_2114_ == 0)
{
uint8_t v___x_2129_; 
v___x_2129_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2081_, v_a_2127_);
lean_dec(v_a_2127_);
if (v___x_2129_ == 0)
{
lean_object* v___x_2130_; 
v___x_2130_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2056_);
lean_dec_ref(v___x_2130_);
v_nondep_2116_ = v___x_2128_;
goto v___jp_2115_;
}
else
{
v_nondep_2116_ = v_nondep_2114_;
goto v___jp_2115_;
}
}
else
{
lean_dec(v_a_2127_);
v_nondep_2116_ = v___x_2128_;
goto v___jp_2115_;
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v_value_2113_);
lean_dec_ref(v_type_2112_);
lean_dec(v_userName_2111_);
lean_dec(v_n_2066_);
lean_dec_ref(v_a_2054_);
v_a_2131_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2126_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2126_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
v___jp_2115_:
{
lean_object* v_expr_2117_; lean_object* v_type_x3f_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; 
v_expr_2117_ = lean_ctor_get(v_a_2054_, 0);
lean_inc_ref(v_expr_2117_);
v_type_x3f_2118_ = lean_ctor_get(v_a_2054_, 1);
lean_inc(v_type_x3f_2118_);
lean_dec_ref(v_a_2054_);
v___x_2119_ = lean_expr_abstract_range(v_type_2112_, v_n_2066_, v_fvars_2052_);
lean_dec_ref(v_type_2112_);
v___x_2120_ = lean_expr_abstract_range(v_value_2113_, v_n_2066_, v_fvars_2052_);
lean_dec_ref(v_value_2113_);
lean_inc_ref(v___x_2120_);
lean_inc_ref(v___x_2119_);
lean_inc(v_userName_2111_);
v___x_2121_ = l_Lean_Expr_letE___override(v_userName_2111_, v___x_2119_, v___x_2120_, v_expr_2117_, v_nondep_2116_);
if (lean_obj_tag(v_type_x3f_2118_) == 0)
{
lean_dec_ref(v___x_2120_);
lean_dec_ref(v___x_2119_);
lean_dec(v_userName_2111_);
v___y_2072_ = v___x_2121_;
v___y_2073_ = v_type_x3f_2118_;
goto v___jp_2071_;
}
else
{
lean_object* v_val_2122_; uint8_t v___x_2123_; 
v_val_2122_ = lean_ctor_get(v_type_x3f_2118_, 0);
lean_inc(v_val_2122_);
lean_dec_ref(v_type_x3f_2118_);
v___x_2123_ = lean_expr_has_loose_bvar(v_val_2122_, v_zero_2062_);
if (v___x_2123_ == 0)
{
lean_object* v___x_2124_; 
lean_dec_ref(v___x_2120_);
lean_dec_ref(v___x_2119_);
lean_dec(v_userName_2111_);
v___x_2124_ = lean_expr_lower_loose_bvars(v_val_2122_, v_one_2065_, v_one_2065_);
lean_dec(v_val_2122_);
v___y_2077_ = v___x_2121_;
v___y_2078_ = v___x_2124_;
goto v___jp_2076_;
}
else
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Expr_letE___override(v_userName_2111_, v___x_2119_, v___x_2120_, v_val_2122_, v_nondep_2116_);
v___y_2077_ = v___x_2121_;
v___y_2078_ = v___x_2125_;
goto v___jp_2076_;
}
}
}
}
}
else
{
lean_object* v___x_2139_; 
lean_dec(v_a_2083_);
lean_dec_ref(v_a_2054_);
lean_inc(v_fvarId_2081_);
v___x_2139_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2081_, v___y_2059_, v___y_2060_);
v___y_2068_ = v___x_2139_;
goto v___jp_2067_;
}
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_dec(v_n_2066_);
lean_dec_ref(v_a_2054_);
v_a_2140_ = lean_ctor_get(v___x_2082_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2082_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2082_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2082_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec_ref(v_a_2054_);
v___x_2148_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2149_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2148_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
v___y_2068_ = v___x_2149_;
goto v___jp_2067_;
}
v___jp_2067_:
{
if (lean_obj_tag(v___y_2068_) == 0)
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___y_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref(v___y_2068_);
v_i_2053_ = v_n_2066_;
v_a_2054_ = v_a_2069_;
goto _start;
}
else
{
lean_dec(v_n_2066_);
return v___y_2068_;
}
}
v___jp_2071_:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2074_, 0, v___y_2072_);
lean_ctor_set(v___x_2074_, 1, v___y_2073_);
v_i_2053_ = v_n_2066_;
v_a_2054_ = v___x_2074_;
goto _start;
}
v___jp_2076_:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___y_2078_);
v___y_2072_ = v___y_2077_;
v___y_2073_ = v___x_2079_;
goto v___jp_2071_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2150_, lean_object* v_i_2151_, lean_object* v_a_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2150_, v_i_2151_, v_a_2152_, v___y_2153_, v___y_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v___y_2156_);
lean_dec_ref(v___y_2155_);
lean_dec(v___y_2154_);
lean_dec(v___y_2153_);
lean_dec_ref(v_fvars_2150_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_a_2161_, lean_object* v_a_2162_){
_start:
{
if (lean_obj_tag(v_a_2161_) == 0)
{
lean_object* v___x_2163_; 
v___x_2163_ = l_List_reverse___redArg(v_a_2162_);
return v___x_2163_;
}
else
{
lean_object* v_head_2164_; lean_object* v_tail_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2174_; 
v_head_2164_ = lean_ctor_get(v_a_2161_, 0);
v_tail_2165_ = lean_ctor_get(v_a_2161_, 1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_a_2161_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2167_ = v_a_2161_;
v_isShared_2168_ = v_isSharedCheck_2174_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_tail_2165_);
lean_inc(v_head_2164_);
lean_dec(v_a_2161_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2174_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2169_; lean_object* v___x_2171_; 
v___x_2169_ = l_Lean_MessageData_ofExpr(v_head_2164_);
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v_a_2162_);
lean_ctor_set(v___x_2167_, 0, v___x_2169_);
v___x_2171_ = v___x_2167_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2169_);
lean_ctor_set(v_reuseFailAlloc_2173_, 1, v_a_2162_);
v___x_2171_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
v_a_2161_ = v_tail_2165_;
v_a_2162_ = v___x_2171_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_2175_; double v___x_2176_; 
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_float_of_nat(v___x_2175_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg(lean_object* v_cls_2180_, lean_object* v_msg_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_){
_start:
{
lean_object* v_ref_2187_; lean_object* v___x_2188_; lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2233_; 
v_ref_2187_ = lean_ctor_get(v___y_2184_, 5);
v___x_2188_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
v_a_2189_ = lean_ctor_get(v___x_2188_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2188_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2191_ = v___x_2188_;
v_isShared_2192_ = v_isSharedCheck_2233_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2188_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2233_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; lean_object* v_traceState_2194_; lean_object* v_env_2195_; lean_object* v_nextMacroScope_2196_; lean_object* v_ngen_2197_; lean_object* v_auxDeclNGen_2198_; lean_object* v_cache_2199_; lean_object* v_messages_2200_; lean_object* v_infoState_2201_; lean_object* v_snapshotTasks_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2232_; 
v___x_2193_ = lean_st_ref_take(v___y_2185_);
v_traceState_2194_ = lean_ctor_get(v___x_2193_, 4);
v_env_2195_ = lean_ctor_get(v___x_2193_, 0);
v_nextMacroScope_2196_ = lean_ctor_get(v___x_2193_, 1);
v_ngen_2197_ = lean_ctor_get(v___x_2193_, 2);
v_auxDeclNGen_2198_ = lean_ctor_get(v___x_2193_, 3);
v_cache_2199_ = lean_ctor_get(v___x_2193_, 5);
v_messages_2200_ = lean_ctor_get(v___x_2193_, 6);
v_infoState_2201_ = lean_ctor_get(v___x_2193_, 7);
v_snapshotTasks_2202_ = lean_ctor_get(v___x_2193_, 8);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2193_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2204_ = v___x_2193_;
v_isShared_2205_ = v_isSharedCheck_2232_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_snapshotTasks_2202_);
lean_inc(v_infoState_2201_);
lean_inc(v_messages_2200_);
lean_inc(v_cache_2199_);
lean_inc(v_traceState_2194_);
lean_inc(v_auxDeclNGen_2198_);
lean_inc(v_ngen_2197_);
lean_inc(v_nextMacroScope_2196_);
lean_inc(v_env_2195_);
lean_dec(v___x_2193_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2232_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
uint64_t v_tid_2206_; lean_object* v_traces_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2231_; 
v_tid_2206_ = lean_ctor_get_uint64(v_traceState_2194_, sizeof(void*)*1);
v_traces_2207_ = lean_ctor_get(v_traceState_2194_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v_traceState_2194_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2209_ = v_traceState_2194_;
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_traces_2207_);
lean_dec(v_traceState_2194_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2231_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; double v___x_2212_; uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2211_ = lean_box(0);
v___x_2212_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0);
v___x_2213_ = 0;
v___x_2214_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__1));
v___x_2215_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2215_, 0, v_cls_2180_);
lean_ctor_set(v___x_2215_, 1, v___x_2211_);
lean_ctor_set(v___x_2215_, 2, v___x_2214_);
lean_ctor_set_float(v___x_2215_, sizeof(void*)*3, v___x_2212_);
lean_ctor_set_float(v___x_2215_, sizeof(void*)*3 + 8, v___x_2212_);
lean_ctor_set_uint8(v___x_2215_, sizeof(void*)*3 + 16, v___x_2213_);
v___x_2216_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__2));
v___x_2217_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2215_);
lean_ctor_set(v___x_2217_, 1, v_a_2189_);
lean_ctor_set(v___x_2217_, 2, v___x_2216_);
lean_inc(v_ref_2187_);
v___x_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2218_, 0, v_ref_2187_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = l_Lean_PersistentArray_push___redArg(v_traces_2207_, v___x_2218_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2219_);
v___x_2221_ = v___x_2209_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v___x_2219_);
lean_ctor_set_uint64(v_reuseFailAlloc_2230_, sizeof(void*)*1, v_tid_2206_);
v___x_2221_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
lean_object* v___x_2223_; 
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 4, v___x_2221_);
v___x_2223_ = v___x_2204_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_env_2195_);
lean_ctor_set(v_reuseFailAlloc_2229_, 1, v_nextMacroScope_2196_);
lean_ctor_set(v_reuseFailAlloc_2229_, 2, v_ngen_2197_);
lean_ctor_set(v_reuseFailAlloc_2229_, 3, v_auxDeclNGen_2198_);
lean_ctor_set(v_reuseFailAlloc_2229_, 4, v___x_2221_);
lean_ctor_set(v_reuseFailAlloc_2229_, 5, v_cache_2199_);
lean_ctor_set(v_reuseFailAlloc_2229_, 6, v_messages_2200_);
lean_ctor_set(v_reuseFailAlloc_2229_, 7, v_infoState_2201_);
lean_ctor_set(v_reuseFailAlloc_2229_, 8, v_snapshotTasks_2202_);
v___x_2223_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2227_; 
v___x_2224_ = lean_st_ref_set(v___y_2185_, v___x_2223_);
v___x_2225_ = lean_box(0);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 0, v___x_2225_);
v___x_2227_ = v___x_2191_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v___x_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___boxed(lean_object* v_cls_2234_, lean_object* v_msg_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg(v_cls_2234_, v_msg_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
return v_res_2241_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__4));
v___x_2251_ = l_Lean_stringToMessageData(v___x_2250_);
return v___x_2251_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6));
v___x_2254_ = l_Lean_stringToMessageData(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8));
v___x_2257_ = l_Lean_stringToMessageData(v___x_2256_);
return v___x_2257_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2262_ = l_Lean_MessageData_ofFormat(v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2263_, lean_object* v_body_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_){
_start:
{
lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v___y_2288_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v_cls_2303_; lean_object* v___x_2304_; lean_object* v_a_2305_; uint8_t v___x_2306_; 
v_cls_2303_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2304_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg(v_cls_2303_, v_a_2269_);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
lean_inc(v_a_2305_);
lean_dec_ref(v___x_2304_);
v___x_2306_ = lean_unbox(v_a_2305_);
lean_dec(v_a_2305_);
if (v___x_2306_ == 0)
{
v___y_2285_ = v_a_2265_;
v___y_2286_ = v_a_2266_;
v___y_2287_ = v_a_2267_;
v___y_2288_ = v_a_2268_;
v___y_2289_ = v_a_2269_;
v___y_2290_ = v_a_2270_;
goto v___jp_2284_;
}
else
{
lean_object* v_expr_2307_; lean_object* v_type_x3f_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___y_2321_; 
v_expr_2307_ = lean_ctor_get(v_body_2264_, 0);
v_type_x3f_2308_ = lean_ctor_get(v_body_2264_, 1);
v___x_2309_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5);
lean_inc_ref(v_fvars_2263_);
v___x_2310_ = lean_array_to_list(v_fvars_2263_);
v___x_2311_ = lean_box(0);
v___x_2312_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v___x_2310_, v___x_2311_);
v___x_2313_ = l_Lean_MessageData_ofList(v___x_2312_);
v___x_2314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2309_);
lean_ctor_set(v___x_2314_, 1, v___x_2313_);
v___x_2315_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7);
v___x_2316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2314_);
lean_ctor_set(v___x_2316_, 1, v___x_2315_);
lean_inc_ref(v_expr_2307_);
v___x_2317_ = l_Lean_MessageData_ofExpr(v_expr_2307_);
v___x_2318_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
if (lean_obj_tag(v_type_x3f_2308_) == 0)
{
lean_object* v___x_2334_; 
v___x_2334_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___y_2321_ = v___x_2334_;
goto v___jp_2320_;
}
else
{
lean_object* v_val_2335_; lean_object* v___x_2336_; 
v_val_2335_ = lean_ctor_get(v_type_x3f_2308_, 0);
lean_inc(v_val_2335_);
v___x_2336_ = l_Lean_MessageData_ofExpr(v_val_2335_);
v___y_2321_ = v___x_2336_;
goto v___jp_2320_;
}
v___jp_2320_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v___y_2321_);
v___x_2323_ = l_Lean_indentD(v___x_2322_);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2316_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg(v_cls_2303_, v___x_2324_, v_a_2267_, v_a_2268_, v_a_2269_, v_a_2270_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref(v___x_2325_);
v___y_2285_ = v_a_2265_;
v___y_2286_ = v_a_2266_;
v___y_2287_ = v_a_2267_;
v___y_2288_ = v_a_2268_;
v___y_2289_ = v_a_2269_;
v___y_2290_ = v_a_2270_;
goto v___jp_2284_;
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v_body_2264_);
lean_dec_ref(v_fvars_2263_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
v___jp_2272_:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; 
v___x_2281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2281_, 0, v___y_2274_);
lean_ctor_set(v___x_2281_, 1, v___y_2280_);
v___x_2282_ = lean_array_get_size(v_fvars_2263_);
v___x_2283_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2263_, v___x_2282_, v___x_2281_, v___y_2273_, v___y_2275_, v___y_2276_, v___y_2279_, v___y_2277_, v___y_2278_);
lean_dec_ref(v_fvars_2263_);
return v___x_2283_;
}
v___jp_2284_:
{
lean_object* v_expr_2291_; lean_object* v_type_x3f_2292_; lean_object* v___x_2293_; 
v_expr_2291_ = lean_ctor_get(v_body_2264_, 0);
lean_inc_ref(v_expr_2291_);
v_type_x3f_2292_ = lean_ctor_get(v_body_2264_, 1);
lean_inc(v_type_x3f_2292_);
lean_dec_ref(v_body_2264_);
v___x_2293_ = lean_expr_abstract(v_expr_2291_, v_fvars_2263_);
lean_dec_ref(v_expr_2291_);
if (lean_obj_tag(v_type_x3f_2292_) == 0)
{
v___y_2273_ = v___y_2285_;
v___y_2274_ = v___x_2293_;
v___y_2275_ = v___y_2286_;
v___y_2276_ = v___y_2287_;
v___y_2277_ = v___y_2289_;
v___y_2278_ = v___y_2290_;
v___y_2279_ = v___y_2288_;
v___y_2280_ = v_type_x3f_2292_;
goto v___jp_2272_;
}
else
{
lean_object* v_val_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_val_2294_ = lean_ctor_get(v_type_x3f_2292_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_type_x3f_2292_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v_type_x3f_2292_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_val_2294_);
lean_dec(v_type_x3f_2292_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v___x_2300_; 
v___x_2298_ = lean_expr_abstract(v_val_2294_, v_fvars_2263_);
lean_dec(v_val_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v___x_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
v___y_2273_ = v___y_2285_;
v___y_2274_ = v___x_2293_;
v___y_2275_ = v___y_2286_;
v___y_2276_ = v___y_2287_;
v___y_2277_ = v___y_2289_;
v___y_2278_ = v___y_2290_;
v___y_2279_ = v___y_2288_;
v___y_2280_ = v___x_2300_;
goto v___jp_2272_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2337_, lean_object* v_body_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2337_, v_body_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_, v_a_2344_);
lean_dec(v_a_2344_);
lean_dec_ref(v_a_2343_);
lean_dec(v_a_2342_);
lean_dec_ref(v_a_2341_);
lean_dec(v_a_2340_);
lean_dec(v_a_2339_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2347_, lean_object* v_n_2348_, lean_object* v_i_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2347_, v_i_2349_, v_a_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2360_, lean_object* v_n_2361_, lean_object* v_i_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2360_, v_n_2361_, v_i_2362_, v_a_2363_, v_a_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v_n_2361_);
lean_dec_ref(v_fvars_2360_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3(lean_object* v_cls_2373_, lean_object* v_msg_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_){
_start:
{
lean_object* v___x_2382_; 
v___x_2382_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg(v_cls_2373_, v_msg_2374_, v___y_2377_, v___y_2378_, v___y_2379_, v___y_2380_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___boxed(lean_object* v_cls_2383_, lean_object* v_msg_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3(v_cls_2383_, v_msg_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec(v___y_2385_);
return v_res_2392_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2394_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2395_ = l_Lean_stringToMessageData(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
return v___x_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2399_, lean_object* v_structName_2400_, lean_object* v_idx_2401_, lean_object* v_a_2402_, lean_object* v_00_u03b1_2403_, lean_object* v_x_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_expr_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2427_; 
v_expr_2412_ = lean_ctor_get(v_struct_2399_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v_struct_2399_);
if (v_isSharedCheck_2427_ == 0)
{
lean_object* v_unused_2428_; 
v_unused_2428_ = lean_ctor_get(v_struct_2399_, 1);
lean_dec(v_unused_2428_);
v___x_2414_ = v_struct_2399_;
v_isShared_2415_ = v_isSharedCheck_2427_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_expr_2412_);
lean_dec(v_struct_2399_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2427_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2420_; 
v___x_2416_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2417_ = l_Lean_mkProj(v_structName_2400_, v_idx_2401_, v_expr_2412_);
v___x_2418_ = l_Lean_indentExpr(v___x_2417_);
if (v_isShared_2415_ == 0)
{
lean_ctor_set_tag(v___x_2414_, 7);
lean_ctor_set(v___x_2414_, 1, v___x_2418_);
lean_ctor_set(v___x_2414_, 0, v___x_2416_);
v___x_2420_ = v___x_2414_;
goto v_reusejp_2419_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2416_);
lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2418_);
v___x_2420_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2419_;
}
v_reusejp_2419_:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v___x_2421_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2420_);
lean_ctor_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = l_Lean_indentExpr(v_a_2402_);
v___x_2424_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2422_);
lean_ctor_set(v___x_2424_, 1, v___x_2423_);
v___x_2425_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2424_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
return v___x_2425_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2429_, lean_object* v_structName_2430_, lean_object* v_idx_2431_, lean_object* v_a_2432_, lean_object* v_00_u03b1_2433_, lean_object* v_x_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_){
_start:
{
lean_object* v_res_2442_; 
v_res_2442_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2429_, v_structName_2430_, v_idx_2431_, v_a_2432_, v_00_u03b1_2433_, v_x_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v___y_2436_);
lean_dec(v___y_2435_);
return v_res_2442_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v___x_2451_; lean_object* v_env_2452_; uint8_t v___x_2453_; lean_object* v___x_2454_; 
v___x_2451_ = lean_st_ref_get(v___y_2449_);
v_env_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc_ref(v_env_2452_);
lean_dec(v___x_2451_);
v___x_2453_ = 0;
lean_inc(v_constName_2443_);
v___x_2454_ = l_Lean_Environment_find_x3f(v_env_2452_, v_constName_2443_, v___x_2453_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2455_; 
v___x_2455_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
return v___x_2455_;
}
else
{
lean_object* v_val_2456_; lean_object* v___x_2458_; uint8_t v_isShared_2459_; uint8_t v_isSharedCheck_2463_; 
lean_dec(v_constName_2443_);
v_val_2456_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2463_ == 0)
{
v___x_2458_ = v___x_2454_;
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
else
{
lean_inc(v_val_2456_);
lean_dec(v___x_2454_);
v___x_2458_ = lean_box(0);
v_isShared_2459_ = v_isSharedCheck_2463_;
goto v_resetjp_2457_;
}
v_resetjp_2457_:
{
lean_object* v___x_2461_; 
if (v_isShared_2459_ == 0)
{
lean_ctor_set_tag(v___x_2458_, 0);
v___x_2461_ = v___x_2458_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_val_2456_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_, lean_object* v___y_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_, v___y_2470_);
lean_dec(v___y_2470_);
lean_dec_ref(v___y_2469_);
lean_dec(v___y_2468_);
lean_dec_ref(v___y_2467_);
lean_dec(v___y_2466_);
lean_dec(v___y_2465_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2473_, lean_object* v_structName_2474_, lean_object* v_idx_2475_, lean_object* v_a_2476_, lean_object* v_00_u03b1_2477_, lean_object* v_x_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_){
_start:
{
lean_object* v_expr_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2501_; 
v_expr_2486_ = lean_ctor_get(v_struct_2473_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v_struct_2473_);
if (v_isSharedCheck_2501_ == 0)
{
lean_object* v_unused_2502_; 
v_unused_2502_ = lean_ctor_get(v_struct_2473_, 1);
lean_dec(v_unused_2502_);
v___x_2488_ = v_struct_2473_;
v_isShared_2489_ = v_isSharedCheck_2501_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_expr_2486_);
lean_dec(v_struct_2473_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2501_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
v___x_2490_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2491_ = l_Lean_mkProj(v_structName_2474_, v_idx_2475_, v_expr_2486_);
v___x_2492_ = l_Lean_indentExpr(v___x_2491_);
if (v_isShared_2489_ == 0)
{
lean_ctor_set_tag(v___x_2488_, 7);
lean_ctor_set(v___x_2488_, 1, v___x_2492_);
lean_ctor_set(v___x_2488_, 0, v___x_2490_);
v___x_2494_ = v___x_2488_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2500_, 1, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2495_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2496_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2494_);
lean_ctor_set(v___x_2496_, 1, v___x_2495_);
v___x_2497_ = l_Lean_indentExpr(v_a_2476_);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2498_, v___y_2481_, v___y_2482_, v___y_2483_, v___y_2484_);
return v___x_2499_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2503_, lean_object* v_structName_2504_, lean_object* v_idx_2505_, lean_object* v_a_2506_, lean_object* v_00_u03b1_2507_, lean_object* v_x_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_){
_start:
{
lean_object* v_res_2516_; 
v_res_2516_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2503_, v_structName_2504_, v_idx_2505_, v_a_2506_, v_00_u03b1_2507_, v_x_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
lean_dec(v___y_2514_);
lean_dec_ref(v___y_2513_);
lean_dec(v___y_2512_);
lean_dec_ref(v___y_2511_);
lean_dec(v___y_2510_);
lean_dec(v___y_2509_);
return v_res_2516_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2517_, lean_object* v_fst_2518_, lean_object* v_struct_2519_, lean_object* v_structName_2520_, uint8_t v_a_2521_, lean_object* v___f_2522_, lean_object* v_snd_2523_, lean_object* v_____r_2524_, lean_object* v_ctorType_2525_, lean_object* v_j_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
if (lean_obj_tag(v_ctorType_2525_) == 7)
{
lean_object* v_binderType_2534_; lean_object* v_body_2535_; lean_object* v___x_2536_; 
lean_dec(v_snd_2523_);
v_binderType_2534_ = lean_ctor_get(v_ctorType_2525_, 1);
lean_inc_ref(v_binderType_2534_);
v_body_2535_ = lean_ctor_get(v_ctorType_2525_, 2);
lean_inc_ref(v_body_2535_);
lean_dec_ref(v_ctorType_2525_);
v___x_2536_ = lean_expr_instantiate_rev_range(v_binderType_2534_, v_j_2526_, v_a_2517_, v_fst_2518_);
lean_dec_ref(v_binderType_2534_);
if (v_a_2521_ == 0)
{
lean_dec_ref(v___f_2522_);
goto v___jp_2537_;
}
else
{
lean_object* v___x_2553_; 
lean_inc_ref(v___x_2536_);
v___x_2553_ = l_Lean_Meta_isProp(v___x_2536_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_);
if (lean_obj_tag(v___x_2553_) == 0)
{
lean_object* v_a_2554_; uint8_t v___x_2555_; 
v_a_2554_ = lean_ctor_get(v___x_2553_, 0);
lean_inc(v_a_2554_);
lean_dec_ref(v___x_2553_);
v___x_2555_ = lean_unbox(v_a_2554_);
lean_dec(v_a_2554_);
if (v___x_2555_ == 0)
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
v___x_2556_ = lean_box(0);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc(v___y_2527_);
v___x_2557_ = lean_apply_9(v___f_2522_, lean_box(0), v___x_2556_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, lean_box(0));
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_dec_ref(v___x_2557_);
goto v___jp_2537_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec_ref(v___x_2536_);
lean_dec_ref(v_body_2535_);
lean_dec(v_structName_2520_);
lean_dec_ref(v_struct_2519_);
lean_dec(v_fst_2518_);
lean_dec(v_a_2517_);
v_a_2558_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2557_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2557_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
}
else
{
lean_dec_ref(v___f_2522_);
goto v___jp_2537_;
}
}
else
{
lean_object* v_a_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2573_; 
lean_dec_ref(v___x_2536_);
lean_dec_ref(v_body_2535_);
lean_dec_ref(v___f_2522_);
lean_dec(v_structName_2520_);
lean_dec_ref(v_struct_2519_);
lean_dec(v_fst_2518_);
lean_dec(v_a_2517_);
v_a_2566_ = lean_ctor_get(v___x_2553_, 0);
v_isSharedCheck_2573_ = !lean_is_exclusive(v___x_2553_);
if (v_isSharedCheck_2573_ == 0)
{
v___x_2568_ = v___x_2553_;
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_a_2566_);
lean_dec(v___x_2553_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2573_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2571_; 
if (v_isShared_2569_ == 0)
{
v___x_2571_ = v___x_2568_;
goto v_reusejp_2570_;
}
else
{
lean_object* v_reuseFailAlloc_2572_; 
v_reuseFailAlloc_2572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2572_, 0, v_a_2566_);
v___x_2571_ = v_reuseFailAlloc_2572_;
goto v_reusejp_2570_;
}
v_reusejp_2570_:
{
return v___x_2571_;
}
}
}
}
v___jp_2537_:
{
lean_object* v_expr_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2551_; 
v_expr_2538_ = lean_ctor_get(v_struct_2519_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_struct_2519_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; 
v_unused_2552_ = lean_ctor_get(v_struct_2519_, 1);
lean_dec(v_unused_2552_);
v___x_2540_ = v_struct_2519_;
v_isShared_2541_ = v_isSharedCheck_2551_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_expr_2538_);
lean_dec(v_struct_2519_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2551_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2545_; 
v___x_2542_ = l_Lean_Expr_proj___override(v_structName_2520_, v_a_2517_, v_expr_2538_);
v___x_2543_ = lean_array_push(v_fst_2518_, v___x_2542_);
lean_inc(v_j_2526_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 1, v___x_2536_);
lean_ctor_set(v___x_2540_, 0, v_j_2526_);
v___x_2545_ = v___x_2540_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_j_2526_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v___x_2536_);
v___x_2545_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; 
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v___x_2543_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2547_, 0, v_body_2535_);
lean_ctor_set(v___x_2547_, 1, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
v___x_2549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2548_);
return v___x_2549_;
}
}
}
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; 
lean_dec(v_structName_2520_);
lean_dec_ref(v_struct_2519_);
lean_dec(v_a_2517_);
v___x_2574_ = lean_box(0);
lean_inc(v___y_2532_);
lean_inc_ref(v___y_2531_);
lean_inc(v___y_2530_);
lean_inc_ref(v___y_2529_);
lean_inc(v___y_2528_);
lean_inc(v___y_2527_);
v___x_2575_ = lean_apply_9(v___f_2522_, lean_box(0), v___x_2574_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, lean_box(0));
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v___x_2577_; uint8_t v_isShared_2578_; uint8_t v_isSharedCheck_2586_; 
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2586_ == 0)
{
lean_object* v_unused_2587_; 
v_unused_2587_ = lean_ctor_get(v___x_2575_, 0);
lean_dec(v_unused_2587_);
v___x_2577_ = v___x_2575_;
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
else
{
lean_dec(v___x_2575_);
v___x_2577_ = lean_box(0);
v_isShared_2578_ = v_isSharedCheck_2586_;
goto v_resetjp_2576_;
}
v_resetjp_2576_:
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2584_; 
lean_inc(v_j_2526_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_j_2526_);
lean_ctor_set(v___x_2579_, 1, v_snd_2523_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_fst_2518_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v_ctorType_2525_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2582_, 0, v___x_2581_);
if (v_isShared_2578_ == 0)
{
lean_ctor_set(v___x_2577_, 0, v___x_2582_);
v___x_2584_ = v___x_2577_;
goto v_reusejp_2583_;
}
else
{
lean_object* v_reuseFailAlloc_2585_; 
v_reuseFailAlloc_2585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2585_, 0, v___x_2582_);
v___x_2584_ = v_reuseFailAlloc_2585_;
goto v_reusejp_2583_;
}
v_reusejp_2583_:
{
return v___x_2584_;
}
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec_ref(v_ctorType_2525_);
lean_dec(v_snd_2523_);
lean_dec(v_fst_2518_);
v_a_2588_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2575_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2575_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2596_ = _args[0];
lean_object* v_fst_2597_ = _args[1];
lean_object* v_struct_2598_ = _args[2];
lean_object* v_structName_2599_ = _args[3];
lean_object* v_a_2600_ = _args[4];
lean_object* v___f_2601_ = _args[5];
lean_object* v_snd_2602_ = _args[6];
lean_object* v_____r_2603_ = _args[7];
lean_object* v_ctorType_2604_ = _args[8];
lean_object* v_j_2605_ = _args[9];
lean_object* v___y_2606_ = _args[10];
lean_object* v___y_2607_ = _args[11];
lean_object* v___y_2608_ = _args[12];
lean_object* v___y_2609_ = _args[13];
lean_object* v___y_2610_ = _args[14];
lean_object* v___y_2611_ = _args[15];
lean_object* v___y_2612_ = _args[16];
_start:
{
uint8_t v_a_23457__boxed_2613_; lean_object* v_res_2614_; 
v_a_23457__boxed_2613_ = lean_unbox(v_a_2600_);
v_res_2614_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2596_, v_fst_2597_, v_struct_2598_, v_structName_2599_, v_a_23457__boxed_2613_, v___f_2601_, v_snd_2602_, v_____r_2603_, v_ctorType_2604_, v_j_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_, v___y_2611_);
lean_dec(v___y_2611_);
lean_dec_ref(v___y_2610_);
lean_dec(v___y_2609_);
lean_dec_ref(v___y_2608_);
lean_dec(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec(v_j_2605_);
return v_res_2614_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2615_, lean_object* v_struct_2616_, lean_object* v_structName_2617_, uint8_t v_a_2618_, lean_object* v_idx_2619_, lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_b_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_){
_start:
{
lean_object* v___y_2631_; uint8_t v___x_2653_; 
v___x_2653_ = lean_nat_dec_le(v_a_2621_, v_upperBound_2615_);
if (v___x_2653_ == 0)
{
lean_object* v___x_2654_; 
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_idx_2619_);
lean_dec(v_structName_2617_);
lean_dec_ref(v_struct_2616_);
v___x_2654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2654_, 0, v_b_2622_);
return v___x_2654_;
}
else
{
lean_object* v_snd_2655_; lean_object* v_snd_2656_; lean_object* v_fst_2657_; lean_object* v_fst_2658_; lean_object* v_fst_2659_; lean_object* v_snd_2660_; lean_object* v___f_2661_; uint8_t v___x_2662_; 
v_snd_2655_ = lean_ctor_get(v_b_2622_, 1);
lean_inc(v_snd_2655_);
v_snd_2656_ = lean_ctor_get(v_snd_2655_, 1);
lean_inc(v_snd_2656_);
v_fst_2657_ = lean_ctor_get(v_b_2622_, 0);
lean_inc(v_fst_2657_);
lean_dec_ref(v_b_2622_);
v_fst_2658_ = lean_ctor_get(v_snd_2655_, 0);
lean_inc(v_fst_2658_);
lean_dec(v_snd_2655_);
v_fst_2659_ = lean_ctor_get(v_snd_2656_, 0);
lean_inc(v_fst_2659_);
v_snd_2660_ = lean_ctor_get(v_snd_2656_, 1);
lean_inc(v_snd_2660_);
lean_dec(v_snd_2656_);
lean_inc_ref(v_a_2620_);
lean_inc(v_idx_2619_);
lean_inc(v_structName_2617_);
lean_inc_ref(v_struct_2616_);
v___f_2661_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2661_, 0, v_struct_2616_);
lean_closure_set(v___f_2661_, 1, v_structName_2617_);
lean_closure_set(v___f_2661_, 2, v_idx_2619_);
lean_closure_set(v___f_2661_, 3, v_a_2620_);
v___x_2662_ = l_Lean_Expr_isForall(v_fst_2657_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_expr_instantiate_rev_range(v_fst_2657_, v_fst_2659_, v_a_2621_, v_fst_2658_);
lean_dec(v_fst_2659_);
lean_dec(v_fst_2657_);
lean_inc(v___y_2628_);
lean_inc_ref(v___y_2627_);
lean_inc(v___y_2626_);
lean_inc_ref(v___y_2625_);
v___x_2664_ = lean_whnf(v___x_2663_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref(v___x_2664_);
v___x_2666_ = lean_box(0);
lean_inc(v_structName_2617_);
lean_inc_ref(v_struct_2616_);
lean_inc(v_a_2621_);
v___x_2667_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2621_, v_fst_2658_, v_struct_2616_, v_structName_2617_, v_a_2618_, v___f_2661_, v_snd_2660_, v___x_2666_, v_a_2665_, v_a_2621_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
v___y_2631_ = v___x_2667_;
goto v___jp_2630_;
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec_ref(v___f_2661_);
lean_dec(v_snd_2660_);
lean_dec(v_fst_2658_);
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_idx_2619_);
lean_dec(v_structName_2617_);
lean_dec_ref(v_struct_2616_);
v_a_2668_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2664_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2664_);
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
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2676_ = lean_box(0);
lean_inc(v_structName_2617_);
lean_inc_ref(v_struct_2616_);
lean_inc(v_a_2621_);
v___x_2677_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2621_, v_fst_2658_, v_struct_2616_, v_structName_2617_, v_a_2618_, v___f_2661_, v_snd_2660_, v___x_2676_, v_fst_2657_, v_fst_2659_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_, v___y_2628_);
lean_dec(v_fst_2659_);
v___y_2631_ = v___x_2677_;
goto v___jp_2630_;
}
}
v___jp_2630_:
{
if (lean_obj_tag(v___y_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2644_; 
v_a_2632_ = lean_ctor_get(v___y_2631_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___y_2631_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2634_ = v___y_2631_;
v_isShared_2635_ = v_isSharedCheck_2644_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___y_2631_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2644_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
if (lean_obj_tag(v_a_2632_) == 0)
{
lean_object* v_a_2636_; lean_object* v___x_2638_; 
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_idx_2619_);
lean_dec(v_structName_2617_);
lean_dec_ref(v_struct_2616_);
v_a_2636_ = lean_ctor_get(v_a_2632_, 0);
lean_inc(v_a_2636_);
lean_dec_ref(v_a_2632_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 0, v_a_2636_);
v___x_2638_ = v___x_2634_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2636_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_del_object(v___x_2634_);
v_a_2640_ = lean_ctor_get(v_a_2632_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v_a_2632_);
v___x_2641_ = lean_unsigned_to_nat(1u);
v___x_2642_ = lean_nat_add(v_a_2621_, v___x_2641_);
lean_dec(v_a_2621_);
v_a_2621_ = v___x_2642_;
v_b_2622_ = v_a_2640_;
goto _start;
}
}
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec(v_a_2621_);
lean_dec_ref(v_a_2620_);
lean_dec(v_idx_2619_);
lean_dec(v_structName_2617_);
lean_dec_ref(v_struct_2616_);
v_a_2645_ = lean_ctor_get(v___y_2631_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___y_2631_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___y_2631_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___y_2631_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2650_; 
if (v_isShared_2648_ == 0)
{
v___x_2650_ = v___x_2647_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v_a_2645_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
return v___x_2650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2678_, lean_object* v_struct_2679_, lean_object* v_structName_2680_, lean_object* v_a_2681_, lean_object* v_idx_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_, lean_object* v_b_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
uint8_t v_a_23614__boxed_2693_; lean_object* v_res_2694_; 
v_a_23614__boxed_2693_ = lean_unbox(v_a_2681_);
v_res_2694_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2678_, v_struct_2679_, v_structName_2680_, v_a_23614__boxed_2693_, v_idx_2682_, v_a_2683_, v_a_2684_, v_b_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v_upperBound_2678_);
return v_res_2694_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2697_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2698_ = lean_unsigned_to_nat(18u);
v___x_2699_ = lean_unsigned_to_nat(1872u);
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2701_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2702_ = l_mkPanicMessageWithDecl(v___x_2701_, v___x_2700_, v___x_2699_, v___x_2698_, v___x_2697_);
return v___x_2702_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2704_ = lean_unsigned_to_nat(0u);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___x_2703_);
return v___x_2705_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2707_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2707_);
lean_ctor_set(v___x_2708_, 1, v___x_2706_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2709_; lean_object* v_dummy_2710_; 
v___x_2709_ = lean_box(0);
v_dummy_2710_ = l_Lean_Expr_sort___override(v___x_2709_);
return v_dummy_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2711_, lean_object* v_structName_2712_, lean_object* v_idx_2713_, lean_object* v_struct_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2729_; uint8_t v___x_2733_; 
v___x_2733_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2715_);
if (v___x_2733_ == 0)
{
lean_dec(v_idx_2713_);
lean_dec(v_structName_2712_);
if (lean_obj_tag(v_e_2711_) == 11)
{
lean_object* v_expr_2734_; lean_object* v_typeName_2735_; lean_object* v_idx_2736_; lean_object* v_struct_2737_; size_t v___x_2738_; size_t v___x_2739_; uint8_t v___x_2740_; 
v_expr_2734_ = lean_ctor_get(v_struct_2714_, 0);
lean_inc_ref(v_expr_2734_);
lean_dec_ref(v_struct_2714_);
v_typeName_2735_ = lean_ctor_get(v_e_2711_, 0);
v_idx_2736_ = lean_ctor_get(v_e_2711_, 1);
v_struct_2737_ = lean_ctor_get(v_e_2711_, 2);
v___x_2738_ = lean_ptr_addr(v_struct_2737_);
v___x_2739_ = lean_ptr_addr(v_expr_2734_);
v___x_2740_ = lean_usize_dec_eq(v___x_2738_, v___x_2739_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_inc(v_idx_2736_);
lean_inc(v_typeName_2735_);
lean_dec_ref(v_e_2711_);
v___x_2741_ = l_Lean_Expr_proj___override(v_typeName_2735_, v_idx_2736_, v_expr_2734_);
v___y_2729_ = v___x_2741_;
goto v___jp_2728_;
}
else
{
lean_dec_ref(v_expr_2734_);
v___y_2729_ = v_e_2711_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec_ref(v_struct_2714_);
lean_dec_ref(v_e_2711_);
v___x_2742_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2743_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2742_);
v___y_2729_ = v___x_2743_;
goto v___jp_2728_;
}
}
else
{
lean_object* v___x_2744_; 
lean_inc_ref(v_struct_2714_);
v___x_2744_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2714_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
if (lean_obj_tag(v___x_2744_) == 0)
{
lean_object* v_a_2745_; lean_object* v___x_2746_; 
v_a_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc(v_a_2745_);
lean_dec_ref(v___x_2744_);
lean_inc(v_a_2720_);
lean_inc_ref(v_a_2719_);
lean_inc(v_a_2718_);
lean_inc_ref(v_a_2717_);
v___x_2746_ = lean_whnf(v_a_2745_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref(v___x_2746_);
lean_inc(v_a_2747_);
v___x_2748_ = l_Lean_Meta_isProp(v_a_2747_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref(v___x_2748_);
v___x_2750_ = l_Lean_Expr_getAppFn(v_a_2747_);
if (lean_obj_tag(v___x_2750_) == 4)
{
lean_object* v_declName_2751_; lean_object* v_us_2752_; lean_object* v___x_2753_; lean_object* v_env_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; 
v_declName_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_declName_2751_);
v_us_2752_ = lean_ctor_get(v___x_2750_, 1);
lean_inc(v_us_2752_);
lean_dec_ref(v___x_2750_);
v___x_2753_ = lean_st_ref_get(v_a_2720_);
v_env_2757_ = lean_ctor_get(v___x_2753_, 0);
lean_inc_ref(v_env_2757_);
lean_dec(v___x_2753_);
v___x_2758_ = 0;
v___x_2759_ = l_Lean_Environment_find_x3f(v_env_2757_, v_declName_2751_, v___x_2758_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
v___x_2760_ = lean_box(0);
v___x_2761_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2714_, v_structName_2712_, v_idx_2713_, v_a_2747_, lean_box(0), v___x_2760_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
return v___x_2761_;
}
else
{
lean_object* v_val_2762_; 
v_val_2762_ = lean_ctor_get(v___x_2759_, 0);
lean_inc(v_val_2762_);
lean_dec_ref(v___x_2759_);
if (lean_obj_tag(v_val_2762_) == 5)
{
lean_object* v_val_2763_; lean_object* v_ctors_2764_; 
v_val_2763_ = lean_ctor_get(v_val_2762_, 0);
lean_inc_ref(v_val_2763_);
lean_dec_ref(v_val_2762_);
v_ctors_2764_ = lean_ctor_get(v_val_2763_, 4);
lean_inc(v_ctors_2764_);
if (lean_obj_tag(v_ctors_2764_) == 1)
{
lean_object* v_tail_2765_; 
v_tail_2765_ = lean_ctor_get(v_ctors_2764_, 1);
if (lean_obj_tag(v_tail_2765_) == 0)
{
lean_object* v_toConstantVal_2766_; lean_object* v_numParams_2767_; lean_object* v_numIndices_2768_; lean_object* v_head_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2878_; 
v_toConstantVal_2766_ = lean_ctor_get(v_val_2763_, 0);
lean_inc_ref(v_toConstantVal_2766_);
v_numParams_2767_ = lean_ctor_get(v_val_2763_, 1);
lean_inc(v_numParams_2767_);
v_numIndices_2768_ = lean_ctor_get(v_val_2763_, 2);
lean_inc(v_numIndices_2768_);
lean_dec_ref(v_val_2763_);
v_head_2769_ = lean_ctor_get(v_ctors_2764_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_ctors_2764_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v_ctors_2764_, 1);
lean_dec(v_unused_2879_);
v___x_2771_ = v_ctors_2764_;
v_isShared_2772_ = v_isSharedCheck_2878_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_head_2769_);
lean_dec(v_ctors_2764_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2878_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; 
v___x_2773_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2769_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref(v___x_2773_);
if (lean_obj_tag(v_a_2774_) == 6)
{
lean_object* v_val_2775_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v___y_2836_; lean_object* v_name_2856_; uint8_t v___x_2857_; 
v_val_2775_ = lean_ctor_get(v_a_2774_, 0);
lean_inc_ref(v_val_2775_);
lean_dec_ref(v_a_2774_);
v_name_2856_ = lean_ctor_get(v_toConstantVal_2766_, 0);
lean_inc(v_name_2856_);
lean_dec_ref(v_toConstantVal_2766_);
v___x_2857_ = lean_name_eq(v_name_2856_, v_structName_2712_);
lean_dec(v_name_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_val_2775_);
lean_del_object(v___x_2771_);
lean_dec(v_numIndices_2768_);
lean_dec(v_numParams_2767_);
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2714_, v_structName_2712_, v_idx_2713_, v_a_2747_, lean_box(0), v___x_2858_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
v_a_2860_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2859_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2859_);
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
else
{
v___y_2831_ = v_a_2715_;
v___y_2832_ = v_a_2716_;
v___y_2833_ = v_a_2717_;
v___y_2834_ = v_a_2718_;
v___y_2835_ = v_a_2719_;
v___y_2836_ = v_a_2720_;
goto v___jp_2830_;
}
v___jp_2776_:
{
lean_object* v_toConstantVal_2784_; lean_object* v_name_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v_toConstantVal_2784_ = lean_ctor_get(v_val_2775_, 0);
lean_inc_ref(v_toConstantVal_2784_);
lean_dec_ref(v_val_2775_);
v_name_2785_ = lean_ctor_get(v_toConstantVal_2784_, 0);
lean_inc(v_name_2785_);
lean_dec_ref(v_toConstantVal_2784_);
v___x_2786_ = l_Lean_mkConst(v_name_2785_, v_us_2752_);
v___x_2787_ = lean_unsigned_to_nat(0u);
v___x_2788_ = l_Array_toSubarray___redArg(v___y_2777_, v___x_2787_, v_numParams_2767_);
v___x_2789_ = l_Subarray_copy___redArg(v___x_2788_);
v___x_2790_ = l_Lean_mkAppN(v___x_2786_, v___x_2789_);
lean_dec_ref(v___x_2789_);
lean_inc(v___y_2783_);
lean_inc_ref(v___y_2782_);
lean_inc(v___y_2781_);
lean_inc_ref(v___y_2780_);
v___x_2791_ = lean_infer_type(v___x_2790_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
if (lean_obj_tag(v___x_2791_) == 0)
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; 
v_a_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc(v_a_2792_);
lean_dec_ref(v___x_2791_);
v___x_2793_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2772_ == 0)
{
lean_ctor_set_tag(v___x_2771_, 0);
lean_ctor_set(v___x_2771_, 1, v___x_2793_);
lean_ctor_set(v___x_2771_, 0, v_a_2792_);
v___x_2795_ = v___x_2771_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2792_);
lean_ctor_set(v_reuseFailAlloc_2821_, 1, v___x_2793_);
v___x_2795_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
uint8_t v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = lean_unbox(v_a_2749_);
lean_dec(v_a_2749_);
lean_inc_ref(v_struct_2714_);
lean_inc(v_idx_2713_);
v___x_2797_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2713_, v_struct_2714_, v_structName_2712_, v___x_2796_, v_idx_2713_, v_a_2747_, v___x_2787_, v___x_2795_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v_idx_2713_);
if (lean_obj_tag(v___x_2797_) == 0)
{
lean_object* v_a_2798_; lean_object* v_snd_2799_; lean_object* v_snd_2800_; lean_object* v_snd_2801_; lean_object* v_expr_2802_; lean_object* v___x_2803_; 
v_a_2798_ = lean_ctor_get(v___x_2797_, 0);
lean_inc(v_a_2798_);
lean_dec_ref(v___x_2797_);
v_snd_2799_ = lean_ctor_get(v_a_2798_, 1);
lean_inc(v_snd_2799_);
lean_dec(v_a_2798_);
v_snd_2800_ = lean_ctor_get(v_snd_2799_, 1);
lean_inc(v_snd_2800_);
lean_dec(v_snd_2799_);
v_snd_2801_ = lean_ctor_get(v_snd_2800_, 1);
lean_inc(v_snd_2801_);
lean_dec(v_snd_2800_);
v_expr_2802_ = lean_ctor_get(v_struct_2714_, 0);
lean_inc_ref(v_expr_2802_);
lean_dec_ref(v_struct_2714_);
v___x_2803_ = l_Lean_Expr_cleanupAnnotations(v_snd_2801_);
if (lean_obj_tag(v_e_2711_) == 11)
{
lean_object* v_typeName_2804_; lean_object* v_idx_2805_; lean_object* v_struct_2806_; size_t v___x_2807_; size_t v___x_2808_; uint8_t v___x_2809_; 
v_typeName_2804_ = lean_ctor_get(v_e_2711_, 0);
v_idx_2805_ = lean_ctor_get(v_e_2711_, 1);
v_struct_2806_ = lean_ctor_get(v_e_2711_, 2);
v___x_2807_ = lean_ptr_addr(v_struct_2806_);
v___x_2808_ = lean_ptr_addr(v_expr_2802_);
v___x_2809_ = lean_usize_dec_eq(v___x_2807_, v___x_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2810_; 
lean_inc(v_idx_2805_);
lean_inc(v_typeName_2804_);
lean_dec_ref(v_e_2711_);
v___x_2810_ = l_Lean_Expr_proj___override(v_typeName_2804_, v_idx_2805_, v_expr_2802_);
v___y_2723_ = v___x_2803_;
v___y_2724_ = v___x_2810_;
goto v___jp_2722_;
}
else
{
lean_dec_ref(v_expr_2802_);
v___y_2723_ = v___x_2803_;
v___y_2724_ = v_e_2711_;
goto v___jp_2722_;
}
}
else
{
lean_object* v___x_2811_; lean_object* v___x_2812_; 
lean_dec_ref(v_expr_2802_);
lean_dec_ref(v_e_2711_);
v___x_2811_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2812_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2811_);
v___y_2723_ = v___x_2803_;
v___y_2724_ = v___x_2812_;
goto v___jp_2722_;
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_struct_2714_);
lean_dec_ref(v_e_2711_);
v_a_2813_ = lean_ctor_get(v___x_2797_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2797_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2797_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2797_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
else
{
lean_object* v_a_2822_; lean_object* v___x_2824_; uint8_t v_isShared_2825_; uint8_t v_isSharedCheck_2829_; 
lean_del_object(v___x_2771_);
lean_dec(v_a_2749_);
lean_dec(v_a_2747_);
lean_dec_ref(v_struct_2714_);
lean_dec(v_idx_2713_);
lean_dec(v_structName_2712_);
lean_dec_ref(v_e_2711_);
v_a_2822_ = lean_ctor_get(v___x_2791_, 0);
v_isSharedCheck_2829_ = !lean_is_exclusive(v___x_2791_);
if (v_isSharedCheck_2829_ == 0)
{
v___x_2824_ = v___x_2791_;
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
else
{
lean_inc(v_a_2822_);
lean_dec(v___x_2791_);
v___x_2824_ = lean_box(0);
v_isShared_2825_ = v_isSharedCheck_2829_;
goto v_resetjp_2823_;
}
v_resetjp_2823_:
{
lean_object* v___x_2827_; 
if (v_isShared_2825_ == 0)
{
v___x_2827_ = v___x_2824_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2822_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
v___jp_2830_:
{
lean_object* v_dummy_2837_; lean_object* v_nargs_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_dummy_2837_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2838_ = l_Lean_Expr_getAppNumArgs(v_a_2747_);
lean_inc(v_nargs_2838_);
v___x_2839_ = lean_mk_array(v_nargs_2838_, v_dummy_2837_);
v___x_2840_ = lean_unsigned_to_nat(1u);
v___x_2841_ = lean_nat_sub(v_nargs_2838_, v___x_2840_);
lean_dec(v_nargs_2838_);
lean_inc(v_a_2747_);
v___x_2842_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2747_, v___x_2839_, v___x_2841_);
v___x_2843_ = lean_nat_add(v_numParams_2767_, v_numIndices_2768_);
lean_dec(v_numIndices_2768_);
v___x_2844_ = lean_array_get_size(v___x_2842_);
v___x_2845_ = lean_nat_dec_eq(v___x_2843_, v___x_2844_);
lean_dec(v___x_2843_);
if (v___x_2845_ == 0)
{
if (v___x_2733_ == 0)
{
v___y_2777_ = v___x_2842_;
v___y_2778_ = v___y_2831_;
v___y_2779_ = v___y_2832_;
v___y_2780_ = v___y_2833_;
v___y_2781_ = v___y_2834_;
v___y_2782_ = v___y_2835_;
v___y_2783_ = v___y_2836_;
goto v___jp_2776_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v___x_2842_);
lean_dec_ref(v_val_2775_);
lean_del_object(v___x_2771_);
lean_dec(v_numParams_2767_);
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
v___x_2846_ = lean_box(0);
v___x_2847_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2714_, v_structName_2712_, v_idx_2713_, v_a_2747_, lean_box(0), v___x_2846_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2847_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2847_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
v___y_2777_ = v___x_2842_;
v___y_2778_ = v___y_2831_;
v___y_2779_ = v___y_2832_;
v___y_2780_ = v___y_2833_;
v___y_2781_ = v___y_2834_;
v___y_2782_ = v___y_2835_;
v___y_2783_ = v___y_2836_;
goto v___jp_2776_;
}
}
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec(v_a_2774_);
lean_del_object(v___x_2771_);
lean_dec(v_numIndices_2768_);
lean_dec(v_numParams_2767_);
lean_dec_ref(v_toConstantVal_2766_);
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
v___x_2868_ = lean_box(0);
v___x_2869_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2714_, v_structName_2712_, v_idx_2713_, v_a_2747_, lean_box(0), v___x_2868_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
return v___x_2869_;
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_del_object(v___x_2771_);
lean_dec(v_numIndices_2768_);
lean_dec(v_numParams_2767_);
lean_dec_ref(v_toConstantVal_2766_);
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec(v_a_2747_);
lean_dec_ref(v_struct_2714_);
lean_dec(v_idx_2713_);
lean_dec(v_structName_2712_);
lean_dec_ref(v_e_2711_);
v_a_2870_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2773_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2773_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
}
else
{
lean_dec_ref(v_ctors_2764_);
lean_dec_ref(v_val_2763_);
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
goto v___jp_2754_;
}
}
else
{
lean_dec(v_ctors_2764_);
lean_dec_ref(v_val_2763_);
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
goto v___jp_2754_;
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec(v_val_2762_);
lean_dec(v_us_2752_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
v___x_2880_ = lean_box(0);
v___x_2881_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2714_, v_structName_2712_, v_idx_2713_, v_a_2747_, lean_box(0), v___x_2880_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
return v___x_2881_;
}
}
v___jp_2754_:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = lean_box(0);
v___x_2756_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2714_, v_structName_2712_, v_idx_2713_, v_a_2747_, lean_box(0), v___x_2755_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
return v___x_2756_;
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec_ref(v___x_2750_);
lean_dec(v_a_2749_);
lean_dec_ref(v_e_2711_);
v___x_2882_ = lean_box(0);
v___x_2883_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2714_, v_structName_2712_, v_idx_2713_, v_a_2747_, lean_box(0), v___x_2882_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_);
return v___x_2883_;
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_a_2747_);
lean_dec_ref(v_struct_2714_);
lean_dec(v_idx_2713_);
lean_dec(v_structName_2712_);
lean_dec_ref(v_e_2711_);
v_a_2884_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2748_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2748_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec_ref(v_struct_2714_);
lean_dec(v_idx_2713_);
lean_dec(v_structName_2712_);
lean_dec_ref(v_e_2711_);
v_a_2892_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2746_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2746_);
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
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v_struct_2714_);
lean_dec(v_idx_2713_);
lean_dec(v_structName_2712_);
lean_dec_ref(v_e_2711_);
v_a_2900_ = lean_ctor_get(v___x_2744_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2744_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2744_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2744_);
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
v___jp_2722_:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2723_);
v___x_2726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2726_, 0, v___y_2724_);
lean_ctor_set(v___x_2726_, 1, v___x_2725_);
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v___x_2726_);
return v___x_2727_;
}
v___jp_2728_:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_box(0);
v___x_2731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2731_, 0, v___y_2729_);
lean_ctor_set(v___x_2731_, 1, v___x_2730_);
v___x_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
return v___x_2732_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2908_, lean_object* v_structName_2909_, lean_object* v_idx_2910_, lean_object* v_struct_2911_, lean_object* v_a_2912_, lean_object* v_a_2913_, lean_object* v_a_2914_, lean_object* v_a_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_, lean_object* v_a_2918_){
_start:
{
lean_object* v_res_2919_; 
v_res_2919_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2908_, v_structName_2909_, v_idx_2910_, v_struct_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_, v_a_2917_);
lean_dec(v_a_2917_);
lean_dec_ref(v_a_2916_);
lean_dec(v_a_2915_);
lean_dec_ref(v_a_2914_);
lean_dec(v_a_2913_);
lean_dec(v_a_2912_);
return v_res_2919_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2920_, lean_object* v_struct_2921_, lean_object* v_structName_2922_, uint8_t v_a_2923_, lean_object* v_idx_2924_, lean_object* v_a_2925_, lean_object* v_inst_2926_, lean_object* v_R_2927_, lean_object* v_a_2928_, lean_object* v_b_2929_, lean_object* v_c_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v___x_2938_; 
v___x_2938_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2920_, v_struct_2921_, v_structName_2922_, v_a_2923_, v_idx_2924_, v_a_2925_, v_a_2928_, v_b_2929_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2939_ = _args[0];
lean_object* v_struct_2940_ = _args[1];
lean_object* v_structName_2941_ = _args[2];
lean_object* v_a_2942_ = _args[3];
lean_object* v_idx_2943_ = _args[4];
lean_object* v_a_2944_ = _args[5];
lean_object* v_inst_2945_ = _args[6];
lean_object* v_R_2946_ = _args[7];
lean_object* v_a_2947_ = _args[8];
lean_object* v_b_2948_ = _args[9];
lean_object* v_c_2949_ = _args[10];
lean_object* v___y_2950_ = _args[11];
lean_object* v___y_2951_ = _args[12];
lean_object* v___y_2952_ = _args[13];
lean_object* v___y_2953_ = _args[14];
lean_object* v___y_2954_ = _args[15];
lean_object* v___y_2955_ = _args[16];
lean_object* v___y_2956_ = _args[17];
_start:
{
uint8_t v_a_24138__boxed_2957_; lean_object* v_res_2958_; 
v_a_24138__boxed_2957_ = lean_unbox(v_a_2942_);
v_res_2958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2939_, v_struct_2940_, v_structName_2941_, v_a_24138__boxed_2957_, v_idx_2943_, v_a_2944_, v_inst_2945_, v_R_2946_, v_a_2947_, v_b_2948_, v_c_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
lean_dec(v___y_2955_);
lean_dec_ref(v___y_2954_);
lean_dec(v___y_2953_);
lean_dec_ref(v___y_2952_);
lean_dec(v___y_2951_);
lean_dec(v___y_2950_);
lean_dec(v_upperBound_2939_);
return v_res_2958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2959_, size_t v_i_2960_, size_t v_stop_2961_, lean_object* v_b_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
uint8_t v___x_2969_; 
v___x_2969_ = lean_usize_dec_eq(v_i_2960_, v_stop_2961_);
if (v___x_2969_ == 0)
{
size_t v___x_2970_; size_t v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2970_ = ((size_t)1ULL);
v___x_2971_ = lean_usize_sub(v_i_2960_, v___x_2970_);
v___x_2972_ = lean_array_uget_borrowed(v_as_2959_, v___x_2971_);
lean_inc(v___x_2972_);
v___x_2973_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2972_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref(v___x_2973_);
v___x_2975_ = l_Lean_Expr_sortLevel_x21(v_a_2974_);
lean_dec(v_a_2974_);
v___x_2976_ = l_Lean_mkLevelIMax_x27(v___x_2975_, v_b_2962_);
v_i_2960_ = v___x_2971_;
v_b_2962_ = v___x_2976_;
goto _start;
}
else
{
lean_object* v_a_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_2985_; 
lean_dec(v_b_2962_);
v_a_2978_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_2985_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_2985_ == 0)
{
v___x_2980_ = v___x_2973_;
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_a_2978_);
lean_dec(v___x_2973_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_2985_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___x_2983_; 
if (v_isShared_2981_ == 0)
{
v___x_2983_ = v___x_2980_;
goto v_reusejp_2982_;
}
else
{
lean_object* v_reuseFailAlloc_2984_; 
v_reuseFailAlloc_2984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2984_, 0, v_a_2978_);
v___x_2983_ = v_reuseFailAlloc_2984_;
goto v_reusejp_2982_;
}
v_reusejp_2982_:
{
return v___x_2983_;
}
}
}
}
else
{
lean_object* v___x_2986_; 
v___x_2986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2986_, 0, v_b_2962_);
return v___x_2986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_2987_, lean_object* v_i_2988_, lean_object* v_stop_2989_, lean_object* v_b_2990_, lean_object* v___y_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_, lean_object* v___y_2996_){
_start:
{
size_t v_i_boxed_2997_; size_t v_stop_boxed_2998_; lean_object* v_res_2999_; 
v_i_boxed_2997_ = lean_unbox_usize(v_i_2988_);
lean_dec(v_i_2988_);
v_stop_boxed_2998_ = lean_unbox_usize(v_stop_2989_);
lean_dec(v_stop_2989_);
v_res_2999_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_2987_, v_i_boxed_2997_, v_stop_boxed_2998_, v_b_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v___y_2991_);
lean_dec_ref(v_as_2987_);
return v_res_2999_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3003_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_3004_ = lean_unsigned_to_nat(14u);
v___x_3005_ = lean_unsigned_to_nat(22u);
v___x_3006_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_3007_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_3008_ = l_mkPanicMessageWithDecl(v___x_3007_, v___x_3006_, v___x_3005_, v___x_3004_, v___x_3003_);
return v___x_3008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_3009_, lean_object* v_doms_3010_, lean_object* v_body_3011_, lean_object* v_a_3012_, lean_object* v_a_3013_, lean_object* v_a_3014_, lean_object* v_a_3015_, lean_object* v_a_3016_, lean_object* v_a_3017_){
_start:
{
lean_object* v_lctx_3019_; lean_object* v_expr_3020_; uint8_t v___x_3021_; uint8_t v___x_3022_; lean_object* v___x_3023_; lean_object* v_a_3025_; uint8_t v___x_3030_; 
v_lctx_3019_ = lean_ctor_get(v_a_3014_, 2);
v_expr_3020_ = lean_ctor_get(v_body_3011_, 0);
v___x_3021_ = 1;
v___x_3022_ = 0;
lean_inc_ref(v_lctx_3019_);
v___x_3023_ = l_Lean_LocalContext_mkForall(v_lctx_3019_, v_fvars_3009_, v_expr_3020_, v___x_3021_, v___x_3022_);
v___x_3030_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3012_);
if (v___x_3030_ == 0)
{
lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v_a_3014_);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_body_3011_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; lean_object* v_unused_3041_; 
v_unused_3040_ = lean_ctor_get(v_body_3011_, 1);
lean_dec(v_unused_3040_);
v_unused_3041_ = lean_ctor_get(v_body_3011_, 0);
lean_dec(v_unused_3041_);
v___x_3032_ = v_body_3011_;
v_isShared_3033_ = v_isSharedCheck_3039_;
goto v_resetjp_3031_;
}
else
{
lean_dec(v_body_3011_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3039_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3034_; lean_object* v___x_3036_; 
v___x_3034_ = lean_box(0);
if (v_isShared_3033_ == 0)
{
lean_ctor_set(v___x_3032_, 1, v___x_3034_);
lean_ctor_set(v___x_3032_, 0, v___x_3023_);
v___x_3036_ = v___x_3032_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3023_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3034_);
v___x_3036_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
lean_object* v___x_3037_; 
v___x_3037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
return v___x_3037_;
}
}
}
else
{
lean_object* v___x_3042_; 
v___x_3042_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_3011_, v_a_3012_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3042_) == 0)
{
lean_object* v_a_3043_; lean_object* v___y_3045_; lean_object* v_type_x3f_3062_; 
v_a_3043_ = lean_ctor_get(v___x_3042_, 0);
lean_inc(v_a_3043_);
lean_dec_ref(v___x_3042_);
v_type_x3f_3062_ = lean_ctor_get(v_a_3043_, 1);
lean_inc(v_type_x3f_3062_);
lean_dec(v_a_3043_);
if (lean_obj_tag(v_type_x3f_3062_) == 0)
{
lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3063_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3064_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3063_);
v___y_3045_ = v___x_3064_;
goto v___jp_3044_;
}
else
{
lean_object* v_val_3065_; 
v_val_3065_ = lean_ctor_get(v_type_x3f_3062_, 0);
lean_inc(v_val_3065_);
lean_dec_ref(v_type_x3f_3062_);
v___y_3045_ = v_val_3065_;
goto v___jp_3044_;
}
v___jp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint8_t v___x_3049_; 
v___x_3046_ = l_Lean_Expr_sortLevel_x21(v___y_3045_);
lean_dec_ref(v___y_3045_);
v___x_3047_ = lean_array_get_size(v_doms_3010_);
v___x_3048_ = lean_unsigned_to_nat(0u);
v___x_3049_ = lean_nat_dec_lt(v___x_3048_, v___x_3047_);
if (v___x_3049_ == 0)
{
lean_dec_ref(v_a_3014_);
v_a_3025_ = v___x_3046_;
goto v___jp_3024_;
}
else
{
size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_usize_of_nat(v___x_3047_);
v___x_3051_ = ((size_t)0ULL);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_3010_, v___x_3050_, v___x_3051_, v___x_3046_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
lean_dec_ref(v_a_3014_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref(v___x_3052_);
v_a_3025_ = v_a_3053_;
goto v___jp_3024_;
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___x_3023_);
v_a_3054_ = lean_ctor_get(v___x_3052_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3052_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3052_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3052_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3023_);
lean_dec_ref(v_a_3014_);
return v___x_3042_;
}
}
v___jp_3024_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3026_ = l_Lean_Expr_sort___override(v_a_3025_);
v___x_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3026_);
v___x_3028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3028_, 0, v___x_3023_);
lean_ctor_set(v___x_3028_, 1, v___x_3027_);
v___x_3029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3028_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3066_, lean_object* v_doms_3067_, lean_object* v_body_3068_, lean_object* v_a_3069_, lean_object* v_a_3070_, lean_object* v_a_3071_, lean_object* v_a_3072_, lean_object* v_a_3073_, lean_object* v_a_3074_, lean_object* v_a_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3066_, v_doms_3067_, v_body_3068_, v_a_3069_, v_a_3070_, v_a_3071_, v_a_3072_, v_a_3073_, v_a_3074_);
lean_dec(v_a_3074_);
lean_dec_ref(v_a_3073_);
lean_dec(v_a_3072_);
lean_dec(v_a_3070_);
lean_dec(v_a_3069_);
lean_dec_ref(v_doms_3067_);
lean_dec_ref(v_fvars_3066_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3077_, size_t v_i_3078_, size_t v_stop_3079_, lean_object* v_b_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v___x_3088_; 
v___x_3088_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3077_, v_i_3078_, v_stop_3079_, v_b_3080_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3089_, lean_object* v_i_3090_, lean_object* v_stop_3091_, lean_object* v_b_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_){
_start:
{
size_t v_i_boxed_3100_; size_t v_stop_boxed_3101_; lean_object* v_res_3102_; 
v_i_boxed_3100_ = lean_unbox_usize(v_i_3090_);
lean_dec(v_i_3090_);
v_stop_boxed_3101_ = lean_unbox_usize(v_stop_3091_);
lean_dec(v_stop_3091_);
v_res_3102_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3089_, v_i_boxed_3100_, v_stop_boxed_3101_, v_b_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec(v___y_3093_);
lean_dec_ref(v_as_3089_);
return v_res_3102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3103_, lean_object* v_opt_3104_){
_start:
{
lean_object* v_name_3105_; lean_object* v_defValue_3106_; lean_object* v_map_3107_; lean_object* v___x_3108_; 
v_name_3105_ = lean_ctor_get(v_opt_3104_, 0);
v_defValue_3106_ = lean_ctor_get(v_opt_3104_, 1);
v_map_3107_ = lean_ctor_get(v_opts_3103_, 0);
v___x_3108_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3107_, v_name_3105_);
if (lean_obj_tag(v___x_3108_) == 0)
{
uint8_t v___x_3109_; 
v___x_3109_ = lean_unbox(v_defValue_3106_);
return v___x_3109_;
}
else
{
lean_object* v_val_3110_; 
v_val_3110_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_val_3110_);
lean_dec_ref(v___x_3108_);
if (lean_obj_tag(v_val_3110_) == 1)
{
uint8_t v_v_3111_; 
v_v_3111_ = lean_ctor_get_uint8(v_val_3110_, 0);
lean_dec_ref(v_val_3110_);
return v_v_3111_;
}
else
{
uint8_t v___x_3112_; 
lean_dec(v_val_3110_);
v___x_3112_ = lean_unbox(v_defValue_3106_);
return v___x_3112_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3113_, lean_object* v_opt_3114_){
_start:
{
uint8_t v_res_3115_; lean_object* v_r_3116_; 
v_res_3115_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3113_, v_opt_3114_);
lean_dec_ref(v_opt_3114_);
lean_dec_ref(v_opts_3113_);
v_r_3116_ = lean_box(v_res_3115_);
return v_r_3116_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_e_3117_){
_start:
{
if (lean_obj_tag(v_e_3117_) == 0)
{
uint8_t v___x_3118_; 
v___x_3118_ = 2;
return v___x_3118_;
}
else
{
uint8_t v___x_3119_; 
v___x_3119_ = 0;
return v___x_3119_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_e_3120_){
_start:
{
uint8_t v_res_3121_; lean_object* v_r_3122_; 
v_res_3121_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_e_3120_);
lean_dec_ref(v_e_3120_);
v_r_3122_ = lean_box(v_res_3121_);
return v_r_3122_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(lean_object* v_x_3123_){
_start:
{
if (lean_obj_tag(v_x_3123_) == 0)
{
lean_object* v_a_3125_; lean_object* v___x_3127_; uint8_t v_isShared_3128_; uint8_t v_isSharedCheck_3132_; 
v_a_3125_ = lean_ctor_get(v_x_3123_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v_x_3123_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3127_ = v_x_3123_;
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
else
{
lean_inc(v_a_3125_);
lean_dec(v_x_3123_);
v___x_3127_ = lean_box(0);
v_isShared_3128_ = v_isSharedCheck_3132_;
goto v_resetjp_3126_;
}
v_resetjp_3126_:
{
lean_object* v___x_3130_; 
if (v_isShared_3128_ == 0)
{
lean_ctor_set_tag(v___x_3127_, 1);
v___x_3130_ = v___x_3127_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v_a_3125_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3133_ = lean_ctor_get(v_x_3123_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v_x_3123_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v_x_3123_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v_x_3123_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set_tag(v___x_3135_, 0);
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg___boxed(lean_object* v_x_3141_, lean_object* v___y_3142_){
_start:
{
lean_object* v_res_3143_; 
v_res_3143_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_x_3141_);
return v_res_3143_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(size_t v_sz_3144_, size_t v_i_3145_, lean_object* v_bs_3146_){
_start:
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_usize_dec_lt(v_i_3145_, v_sz_3144_);
if (v___x_3147_ == 0)
{
return v_bs_3146_;
}
else
{
lean_object* v_v_3148_; lean_object* v_msg_3149_; lean_object* v___x_3150_; lean_object* v_bs_x27_3151_; size_t v___x_3152_; size_t v___x_3153_; lean_object* v___x_3154_; 
v_v_3148_ = lean_array_uget_borrowed(v_bs_3146_, v_i_3145_);
v_msg_3149_ = lean_ctor_get(v_v_3148_, 1);
lean_inc_ref(v_msg_3149_);
v___x_3150_ = lean_unsigned_to_nat(0u);
v_bs_x27_3151_ = lean_array_uset(v_bs_3146_, v_i_3145_, v___x_3150_);
v___x_3152_ = ((size_t)1ULL);
v___x_3153_ = lean_usize_add(v_i_3145_, v___x_3152_);
v___x_3154_ = lean_array_uset(v_bs_x27_3151_, v_i_3145_, v_msg_3149_);
v_i_3145_ = v___x_3153_;
v_bs_3146_ = v___x_3154_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16___boxed(lean_object* v_sz_3156_, lean_object* v_i_3157_, lean_object* v_bs_3158_){
_start:
{
size_t v_sz_boxed_3159_; size_t v_i_boxed_3160_; lean_object* v_res_3161_; 
v_sz_boxed_3159_ = lean_unbox_usize(v_sz_3156_);
lean_dec(v_sz_3156_);
v_i_boxed_3160_ = lean_unbox_usize(v_i_3157_);
lean_dec(v_i_3157_);
v_res_3161_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(v_sz_boxed_3159_, v_i_boxed_3160_, v_bs_3158_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_oldTraces_3162_, lean_object* v_data_3163_, lean_object* v_ref_3164_, lean_object* v_msg_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
lean_object* v_fileName_3171_; lean_object* v_fileMap_3172_; lean_object* v_options_3173_; lean_object* v_currRecDepth_3174_; lean_object* v_maxRecDepth_3175_; lean_object* v_ref_3176_; lean_object* v_currNamespace_3177_; lean_object* v_openDecls_3178_; lean_object* v_initHeartbeats_3179_; lean_object* v_maxHeartbeats_3180_; lean_object* v_quotContext_3181_; lean_object* v_currMacroScope_3182_; uint8_t v_diag_3183_; lean_object* v_cancelTk_x3f_3184_; uint8_t v_suppressElabErrors_3185_; lean_object* v_inheritedTraceOptions_3186_; lean_object* v___x_3187_; lean_object* v_traceState_3188_; lean_object* v_traces_3189_; lean_object* v_ref_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; size_t v_sz_3193_; size_t v___x_3194_; lean_object* v___x_3195_; lean_object* v_msg_3196_; lean_object* v___x_3197_; lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3235_; 
v_fileName_3171_ = lean_ctor_get(v___y_3168_, 0);
v_fileMap_3172_ = lean_ctor_get(v___y_3168_, 1);
v_options_3173_ = lean_ctor_get(v___y_3168_, 2);
v_currRecDepth_3174_ = lean_ctor_get(v___y_3168_, 3);
v_maxRecDepth_3175_ = lean_ctor_get(v___y_3168_, 4);
v_ref_3176_ = lean_ctor_get(v___y_3168_, 5);
v_currNamespace_3177_ = lean_ctor_get(v___y_3168_, 6);
v_openDecls_3178_ = lean_ctor_get(v___y_3168_, 7);
v_initHeartbeats_3179_ = lean_ctor_get(v___y_3168_, 8);
v_maxHeartbeats_3180_ = lean_ctor_get(v___y_3168_, 9);
v_quotContext_3181_ = lean_ctor_get(v___y_3168_, 10);
v_currMacroScope_3182_ = lean_ctor_get(v___y_3168_, 11);
v_diag_3183_ = lean_ctor_get_uint8(v___y_3168_, sizeof(void*)*14);
v_cancelTk_x3f_3184_ = lean_ctor_get(v___y_3168_, 12);
v_suppressElabErrors_3185_ = lean_ctor_get_uint8(v___y_3168_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3186_ = lean_ctor_get(v___y_3168_, 13);
v___x_3187_ = lean_st_ref_get(v___y_3169_);
v_traceState_3188_ = lean_ctor_get(v___x_3187_, 4);
lean_inc_ref(v_traceState_3188_);
lean_dec(v___x_3187_);
v_traces_3189_ = lean_ctor_get(v_traceState_3188_, 0);
lean_inc_ref(v_traces_3189_);
lean_dec_ref(v_traceState_3188_);
v_ref_3190_ = l_Lean_replaceRef(v_ref_3164_, v_ref_3176_);
lean_inc_ref(v_inheritedTraceOptions_3186_);
lean_inc(v_cancelTk_x3f_3184_);
lean_inc(v_currMacroScope_3182_);
lean_inc(v_quotContext_3181_);
lean_inc(v_maxHeartbeats_3180_);
lean_inc(v_initHeartbeats_3179_);
lean_inc(v_openDecls_3178_);
lean_inc(v_currNamespace_3177_);
lean_inc(v_maxRecDepth_3175_);
lean_inc(v_currRecDepth_3174_);
lean_inc_ref(v_options_3173_);
lean_inc_ref(v_fileMap_3172_);
lean_inc_ref(v_fileName_3171_);
v___x_3191_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3191_, 0, v_fileName_3171_);
lean_ctor_set(v___x_3191_, 1, v_fileMap_3172_);
lean_ctor_set(v___x_3191_, 2, v_options_3173_);
lean_ctor_set(v___x_3191_, 3, v_currRecDepth_3174_);
lean_ctor_set(v___x_3191_, 4, v_maxRecDepth_3175_);
lean_ctor_set(v___x_3191_, 5, v_ref_3190_);
lean_ctor_set(v___x_3191_, 6, v_currNamespace_3177_);
lean_ctor_set(v___x_3191_, 7, v_openDecls_3178_);
lean_ctor_set(v___x_3191_, 8, v_initHeartbeats_3179_);
lean_ctor_set(v___x_3191_, 9, v_maxHeartbeats_3180_);
lean_ctor_set(v___x_3191_, 10, v_quotContext_3181_);
lean_ctor_set(v___x_3191_, 11, v_currMacroScope_3182_);
lean_ctor_set(v___x_3191_, 12, v_cancelTk_x3f_3184_);
lean_ctor_set(v___x_3191_, 13, v_inheritedTraceOptions_3186_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*14, v_diag_3183_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*14 + 1, v_suppressElabErrors_3185_);
v___x_3192_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3189_);
lean_dec_ref(v_traces_3189_);
v_sz_3193_ = lean_array_size(v___x_3192_);
v___x_3194_ = ((size_t)0ULL);
v___x_3195_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(v_sz_3193_, v___x_3194_, v___x_3192_);
v_msg_3196_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3196_, 0, v_data_3163_);
lean_ctor_set(v_msg_3196_, 1, v_msg_3165_);
lean_ctor_set(v_msg_3196_, 2, v___x_3195_);
v___x_3197_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3196_, v___y_3166_, v___y_3167_, v___x_3191_, v___y_3169_);
lean_dec_ref(v___x_3191_);
v_a_3198_ = lean_ctor_get(v___x_3197_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3197_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3200_ = v___x_3197_;
v_isShared_3201_ = v_isSharedCheck_3235_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3197_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3235_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3202_; lean_object* v_traceState_3203_; lean_object* v_env_3204_; lean_object* v_nextMacroScope_3205_; lean_object* v_ngen_3206_; lean_object* v_auxDeclNGen_3207_; lean_object* v_cache_3208_; lean_object* v_messages_3209_; lean_object* v_infoState_3210_; lean_object* v_snapshotTasks_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3234_; 
v___x_3202_ = lean_st_ref_take(v___y_3169_);
v_traceState_3203_ = lean_ctor_get(v___x_3202_, 4);
v_env_3204_ = lean_ctor_get(v___x_3202_, 0);
v_nextMacroScope_3205_ = lean_ctor_get(v___x_3202_, 1);
v_ngen_3206_ = lean_ctor_get(v___x_3202_, 2);
v_auxDeclNGen_3207_ = lean_ctor_get(v___x_3202_, 3);
v_cache_3208_ = lean_ctor_get(v___x_3202_, 5);
v_messages_3209_ = lean_ctor_get(v___x_3202_, 6);
v_infoState_3210_ = lean_ctor_get(v___x_3202_, 7);
v_snapshotTasks_3211_ = lean_ctor_get(v___x_3202_, 8);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3213_ = v___x_3202_;
v_isShared_3214_ = v_isSharedCheck_3234_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_snapshotTasks_3211_);
lean_inc(v_infoState_3210_);
lean_inc(v_messages_3209_);
lean_inc(v_cache_3208_);
lean_inc(v_traceState_3203_);
lean_inc(v_auxDeclNGen_3207_);
lean_inc(v_ngen_3206_);
lean_inc(v_nextMacroScope_3205_);
lean_inc(v_env_3204_);
lean_dec(v___x_3202_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3234_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
uint64_t v_tid_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3232_; 
v_tid_3215_ = lean_ctor_get_uint64(v_traceState_3203_, sizeof(void*)*1);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_traceState_3203_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; 
v_unused_3233_ = lean_ctor_get(v_traceState_3203_, 0);
lean_dec(v_unused_3233_);
v___x_3217_ = v_traceState_3203_;
v_isShared_3218_ = v_isSharedCheck_3232_;
goto v_resetjp_3216_;
}
else
{
lean_dec(v_traceState_3203_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3232_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3222_; 
v___x_3219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3219_, 0, v_ref_3164_);
lean_ctor_set(v___x_3219_, 1, v_a_3198_);
v___x_3220_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3162_, v___x_3219_);
if (v_isShared_3218_ == 0)
{
lean_ctor_set(v___x_3217_, 0, v___x_3220_);
v___x_3222_ = v___x_3217_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v___x_3220_);
lean_ctor_set_uint64(v_reuseFailAlloc_3231_, sizeof(void*)*1, v_tid_3215_);
v___x_3222_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3224_; 
if (v_isShared_3214_ == 0)
{
lean_ctor_set(v___x_3213_, 4, v___x_3222_);
v___x_3224_ = v___x_3213_;
goto v_reusejp_3223_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v_env_3204_);
lean_ctor_set(v_reuseFailAlloc_3230_, 1, v_nextMacroScope_3205_);
lean_ctor_set(v_reuseFailAlloc_3230_, 2, v_ngen_3206_);
lean_ctor_set(v_reuseFailAlloc_3230_, 3, v_auxDeclNGen_3207_);
lean_ctor_set(v_reuseFailAlloc_3230_, 4, v___x_3222_);
lean_ctor_set(v_reuseFailAlloc_3230_, 5, v_cache_3208_);
lean_ctor_set(v_reuseFailAlloc_3230_, 6, v_messages_3209_);
lean_ctor_set(v_reuseFailAlloc_3230_, 7, v_infoState_3210_);
lean_ctor_set(v_reuseFailAlloc_3230_, 8, v_snapshotTasks_3211_);
v___x_3224_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3223_;
}
v_reusejp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3228_; 
v___x_3225_ = lean_st_ref_set(v___y_3169_, v___x_3224_);
v___x_3226_ = lean_box(0);
if (v_isShared_3201_ == 0)
{
lean_ctor_set(v___x_3200_, 0, v___x_3226_);
v___x_3228_ = v___x_3200_;
goto v_reusejp_3227_;
}
else
{
lean_object* v_reuseFailAlloc_3229_; 
v_reuseFailAlloc_3229_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3229_, 0, v___x_3226_);
v___x_3228_ = v_reuseFailAlloc_3229_;
goto v_reusejp_3227_;
}
v_reusejp_3227_:
{
return v___x_3228_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_oldTraces_3236_, lean_object* v_data_3237_, lean_object* v_ref_3238_, lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_oldTraces_3236_, v_data_3237_, v_ref_3238_, v_msg_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3246_, lean_object* v_opt_3247_){
_start:
{
lean_object* v_name_3248_; lean_object* v_defValue_3249_; lean_object* v_map_3250_; lean_object* v___x_3251_; 
v_name_3248_ = lean_ctor_get(v_opt_3247_, 0);
v_defValue_3249_ = lean_ctor_get(v_opt_3247_, 1);
v_map_3250_ = lean_ctor_get(v_opts_3246_, 0);
v___x_3251_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3250_, v_name_3248_);
if (lean_obj_tag(v___x_3251_) == 0)
{
lean_inc(v_defValue_3249_);
return v_defValue_3249_;
}
else
{
lean_object* v_val_3252_; 
v_val_3252_ = lean_ctor_get(v___x_3251_, 0);
lean_inc(v_val_3252_);
lean_dec_ref(v___x_3251_);
if (lean_obj_tag(v_val_3252_) == 3)
{
lean_object* v_v_3253_; 
v_v_3253_ = lean_ctor_get(v_val_3252_, 0);
lean_inc(v_v_3253_);
lean_dec_ref(v_val_3252_);
return v_v_3253_;
}
else
{
lean_dec(v_val_3252_);
lean_inc(v_defValue_3249_);
return v_defValue_3249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3254_, lean_object* v_opt_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3254_, v_opt_3255_);
lean_dec_ref(v_opt_3255_);
lean_dec_ref(v_opts_3254_);
return v_res_3256_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3259_ = l_Lean_stringToMessageData(v___x_3258_);
return v___x_3259_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3(void){
_start:
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
v___x_3261_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2));
v___x_3262_ = l_Lean_stringToMessageData(v___x_3261_);
return v___x_3262_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4(void){
_start:
{
lean_object* v___x_3263_; double v___x_3264_; 
v___x_3263_ = lean_unsigned_to_nat(1000u);
v___x_3264_ = lean_float_of_nat(v___x_3263_);
return v___x_3264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3265_, uint8_t v_collapsed_3266_, lean_object* v_tag_3267_, lean_object* v_opts_3268_, uint8_t v_clsEnabled_3269_, lean_object* v_oldTraces_3270_, lean_object* v_msg_3271_, lean_object* v_resStartStop_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v_fst_3280_; lean_object* v_snd_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3379_; 
v_fst_3280_ = lean_ctor_get(v_resStartStop_3272_, 0);
v_snd_3281_ = lean_ctor_get(v_resStartStop_3272_, 1);
v_isSharedCheck_3379_ = !lean_is_exclusive(v_resStartStop_3272_);
if (v_isSharedCheck_3379_ == 0)
{
v___x_3283_ = v_resStartStop_3272_;
v_isShared_3284_ = v_isSharedCheck_3379_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_snd_3281_);
lean_inc(v_fst_3280_);
lean_dec(v_resStartStop_3272_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3379_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___y_3286_; lean_object* v___y_3287_; lean_object* v_data_3288_; lean_object* v_fst_3299_; lean_object* v_snd_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3378_; 
v_fst_3299_ = lean_ctor_get(v_snd_3281_, 0);
v_snd_3300_ = lean_ctor_get(v_snd_3281_, 1);
v_isSharedCheck_3378_ = !lean_is_exclusive(v_snd_3281_);
if (v_isSharedCheck_3378_ == 0)
{
v___x_3302_ = v_snd_3281_;
v_isShared_3303_ = v_isSharedCheck_3378_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_snd_3300_);
lean_inc(v_fst_3299_);
lean_dec(v_snd_3281_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3378_;
goto v_resetjp_3301_;
}
v___jp_3285_:
{
lean_object* v___x_3289_; 
lean_inc(v___y_3286_);
v___x_3289_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_oldTraces_3270_, v_data_3288_, v___y_3286_, v___y_3287_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; 
lean_dec_ref(v___x_3289_);
v___x_3290_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_fst_3280_);
return v___x_3290_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v_fst_3280_);
v_a_3291_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3289_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3289_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; uint8_t v___x_3305_; lean_object* v___y_3307_; lean_object* v_a_3308_; uint8_t v___y_3332_; double v___y_3363_; 
v___x_3304_ = l_Lean_trace_profiler;
v___x_3305_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3268_, v___x_3304_);
if (v___x_3305_ == 0)
{
v___y_3332_ = v___x_3305_;
goto v___jp_3331_;
}
else
{
lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3368_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3369_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3268_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; lean_object* v___x_3371_; double v___x_3372_; double v___x_3373_; double v___x_3374_; 
v___x_3370_ = l_Lean_trace_profiler_threshold;
v___x_3371_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3268_, v___x_3370_);
v___x_3372_ = lean_float_of_nat(v___x_3371_);
v___x_3373_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4);
v___x_3374_ = lean_float_div(v___x_3372_, v___x_3373_);
v___y_3363_ = v___x_3374_;
goto v___jp_3362_;
}
else
{
lean_object* v___x_3375_; lean_object* v___x_3376_; double v___x_3377_; 
v___x_3375_ = l_Lean_trace_profiler_threshold;
v___x_3376_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3268_, v___x_3375_);
v___x_3377_ = lean_float_of_nat(v___x_3376_);
v___y_3363_ = v___x_3377_;
goto v___jp_3362_;
}
}
v___jp_3306_:
{
uint8_t v_result_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3314_; 
v_result_3309_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_fst_3280_);
v___x_3310_ = l_Lean_TraceResult_toEmoji(v_result_3309_);
v___x_3311_ = l_Lean_stringToMessageData(v___x_3310_);
v___x_3312_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
if (v_isShared_3303_ == 0)
{
lean_ctor_set_tag(v___x_3302_, 7);
lean_ctor_set(v___x_3302_, 1, v___x_3312_);
lean_ctor_set(v___x_3302_, 0, v___x_3311_);
v___x_3314_ = v___x_3302_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v___x_3311_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v___x_3312_);
v___x_3314_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
lean_object* v_m_3316_; 
if (v_isShared_3284_ == 0)
{
lean_ctor_set_tag(v___x_3283_, 7);
lean_ctor_set(v___x_3283_, 1, v_a_3308_);
lean_ctor_set(v___x_3283_, 0, v___x_3314_);
v_m_3316_ = v___x_3283_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v_a_3308_);
v_m_3316_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; double v___x_3319_; lean_object* v_data_3320_; 
v___x_3317_ = lean_box(v_result_3309_);
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
v___x_3319_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_3267_);
lean_inc_ref(v___x_3318_);
lean_inc(v_cls_3265_);
v_data_3320_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3320_, 0, v_cls_3265_);
lean_ctor_set(v_data_3320_, 1, v___x_3318_);
lean_ctor_set(v_data_3320_, 2, v_tag_3267_);
lean_ctor_set_float(v_data_3320_, sizeof(void*)*3, v___x_3319_);
lean_ctor_set_float(v_data_3320_, sizeof(void*)*3 + 8, v___x_3319_);
lean_ctor_set_uint8(v_data_3320_, sizeof(void*)*3 + 16, v_collapsed_3266_);
if (v___x_3305_ == 0)
{
lean_dec_ref(v___x_3318_);
lean_dec(v_snd_3300_);
lean_dec(v_fst_3299_);
lean_dec_ref(v_tag_3267_);
lean_dec(v_cls_3265_);
v___y_3286_ = v___y_3307_;
v___y_3287_ = v_m_3316_;
v_data_3288_ = v_data_3320_;
goto v___jp_3285_;
}
else
{
lean_object* v_data_3321_; double v___x_3322_; double v___x_3323_; 
lean_dec_ref(v_data_3320_);
v_data_3321_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3321_, 0, v_cls_3265_);
lean_ctor_set(v_data_3321_, 1, v___x_3318_);
lean_ctor_set(v_data_3321_, 2, v_tag_3267_);
v___x_3322_ = lean_unbox_float(v_fst_3299_);
lean_dec(v_fst_3299_);
lean_ctor_set_float(v_data_3321_, sizeof(void*)*3, v___x_3322_);
v___x_3323_ = lean_unbox_float(v_snd_3300_);
lean_dec(v_snd_3300_);
lean_ctor_set_float(v_data_3321_, sizeof(void*)*3 + 8, v___x_3323_);
lean_ctor_set_uint8(v_data_3321_, sizeof(void*)*3 + 16, v_collapsed_3266_);
v___y_3286_ = v___y_3307_;
v___y_3287_ = v_m_3316_;
v_data_3288_ = v_data_3321_;
goto v___jp_3285_;
}
}
}
}
v___jp_3326_:
{
lean_object* v_ref_3327_; lean_object* v___x_3328_; 
v_ref_3327_ = lean_ctor_get(v___y_3277_, 5);
lean_inc(v___y_3278_);
lean_inc_ref(v___y_3277_);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3275_);
lean_inc(v___y_3274_);
lean_inc(v___y_3273_);
lean_inc(v_fst_3280_);
v___x_3328_ = lean_apply_8(v_msg_3271_, v_fst_3280_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, lean_box(0));
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3329_);
lean_dec_ref(v___x_3328_);
v___y_3307_ = v_ref_3327_;
v_a_3308_ = v_a_3329_;
goto v___jp_3306_;
}
else
{
lean_object* v___x_3330_; 
lean_dec_ref(v___x_3328_);
v___x_3330_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3);
v___y_3307_ = v_ref_3327_;
v_a_3308_ = v___x_3330_;
goto v___jp_3306_;
}
}
v___jp_3331_:
{
if (v_clsEnabled_3269_ == 0)
{
if (v___y_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v_traceState_3334_; lean_object* v_env_3335_; lean_object* v_nextMacroScope_3336_; lean_object* v_ngen_3337_; lean_object* v_auxDeclNGen_3338_; lean_object* v_cache_3339_; lean_object* v_messages_3340_; lean_object* v_infoState_3341_; lean_object* v_snapshotTasks_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3361_; 
lean_del_object(v___x_3302_);
lean_dec(v_snd_3300_);
lean_dec(v_fst_3299_);
lean_del_object(v___x_3283_);
lean_dec_ref(v_msg_3271_);
lean_dec_ref(v_tag_3267_);
lean_dec(v_cls_3265_);
v___x_3333_ = lean_st_ref_take(v___y_3278_);
v_traceState_3334_ = lean_ctor_get(v___x_3333_, 4);
v_env_3335_ = lean_ctor_get(v___x_3333_, 0);
v_nextMacroScope_3336_ = lean_ctor_get(v___x_3333_, 1);
v_ngen_3337_ = lean_ctor_get(v___x_3333_, 2);
v_auxDeclNGen_3338_ = lean_ctor_get(v___x_3333_, 3);
v_cache_3339_ = lean_ctor_get(v___x_3333_, 5);
v_messages_3340_ = lean_ctor_get(v___x_3333_, 6);
v_infoState_3341_ = lean_ctor_get(v___x_3333_, 7);
v_snapshotTasks_3342_ = lean_ctor_get(v___x_3333_, 8);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3344_ = v___x_3333_;
v_isShared_3345_ = v_isSharedCheck_3361_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_snapshotTasks_3342_);
lean_inc(v_infoState_3341_);
lean_inc(v_messages_3340_);
lean_inc(v_cache_3339_);
lean_inc(v_traceState_3334_);
lean_inc(v_auxDeclNGen_3338_);
lean_inc(v_ngen_3337_);
lean_inc(v_nextMacroScope_3336_);
lean_inc(v_env_3335_);
lean_dec(v___x_3333_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3361_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
uint64_t v_tid_3346_; lean_object* v_traces_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3360_; 
v_tid_3346_ = lean_ctor_get_uint64(v_traceState_3334_, sizeof(void*)*1);
v_traces_3347_ = lean_ctor_get(v_traceState_3334_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v_traceState_3334_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3349_ = v_traceState_3334_;
v_isShared_3350_ = v_isSharedCheck_3360_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_traces_3347_);
lean_dec(v_traceState_3334_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3360_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v___x_3351_; lean_object* v___x_3353_; 
v___x_3351_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3270_, v_traces_3347_);
lean_dec_ref(v_traces_3347_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3351_);
v___x_3353_ = v___x_3349_;
goto v_reusejp_3352_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3351_);
lean_ctor_set_uint64(v_reuseFailAlloc_3359_, sizeof(void*)*1, v_tid_3346_);
v___x_3353_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3352_;
}
v_reusejp_3352_:
{
lean_object* v___x_3355_; 
if (v_isShared_3345_ == 0)
{
lean_ctor_set(v___x_3344_, 4, v___x_3353_);
v___x_3355_ = v___x_3344_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3358_; 
v_reuseFailAlloc_3358_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3358_, 0, v_env_3335_);
lean_ctor_set(v_reuseFailAlloc_3358_, 1, v_nextMacroScope_3336_);
lean_ctor_set(v_reuseFailAlloc_3358_, 2, v_ngen_3337_);
lean_ctor_set(v_reuseFailAlloc_3358_, 3, v_auxDeclNGen_3338_);
lean_ctor_set(v_reuseFailAlloc_3358_, 4, v___x_3353_);
lean_ctor_set(v_reuseFailAlloc_3358_, 5, v_cache_3339_);
lean_ctor_set(v_reuseFailAlloc_3358_, 6, v_messages_3340_);
lean_ctor_set(v_reuseFailAlloc_3358_, 7, v_infoState_3341_);
lean_ctor_set(v_reuseFailAlloc_3358_, 8, v_snapshotTasks_3342_);
v___x_3355_ = v_reuseFailAlloc_3358_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3356_ = lean_st_ref_set(v___y_3278_, v___x_3355_);
v___x_3357_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_fst_3280_);
return v___x_3357_;
}
}
}
}
}
else
{
goto v___jp_3326_;
}
}
else
{
goto v___jp_3326_;
}
}
v___jp_3362_:
{
double v___x_3364_; double v___x_3365_; double v___x_3366_; uint8_t v___x_3367_; 
v___x_3364_ = lean_unbox_float(v_snd_3300_);
v___x_3365_ = lean_unbox_float(v_fst_3299_);
v___x_3366_ = lean_float_sub(v___x_3364_, v___x_3365_);
v___x_3367_ = lean_float_decLt(v___y_3363_, v___x_3366_);
v___y_3332_ = v___x_3367_;
goto v___jp_3331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3380_, lean_object* v_collapsed_3381_, lean_object* v_tag_3382_, lean_object* v_opts_3383_, lean_object* v_clsEnabled_3384_, lean_object* v_oldTraces_3385_, lean_object* v_msg_3386_, lean_object* v_resStartStop_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
uint8_t v_collapsed_boxed_3395_; uint8_t v_clsEnabled_boxed_3396_; lean_object* v_res_3397_; 
v_collapsed_boxed_3395_ = lean_unbox(v_collapsed_3381_);
v_clsEnabled_boxed_3396_ = lean_unbox(v_clsEnabled_3384_);
v_res_3397_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3380_, v_collapsed_boxed_3395_, v_tag_3382_, v_opts_3383_, v_clsEnabled_boxed_3396_, v_oldTraces_3385_, v_msg_3386_, v_resStartStop_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
lean_dec(v___y_3393_);
lean_dec_ref(v___y_3392_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec(v___y_3388_);
lean_dec_ref(v_opts_3383_);
return v_res_3397_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; lean_object* v___x_3400_; 
v___x_3398_ = lean_unsigned_to_nat(32u);
v___x_3399_ = lean_mk_empty_array_with_capacity(v___x_3398_);
v___x_3400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3400_, 0, v___x_3399_);
return v___x_3400_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3401_; lean_object* v___x_3402_; lean_object* v___x_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v___x_3401_ = ((size_t)5ULL);
v___x_3402_ = lean_unsigned_to_nat(0u);
v___x_3403_ = lean_unsigned_to_nat(32u);
v___x_3404_ = lean_mk_empty_array_with_capacity(v___x_3403_);
v___x_3405_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3406_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
lean_ctor_set(v___x_3406_, 1, v___x_3404_);
lean_ctor_set(v___x_3406_, 2, v___x_3402_);
lean_ctor_set(v___x_3406_, 3, v___x_3402_);
lean_ctor_set_usize(v___x_3406_, 4, v___x_3401_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; lean_object* v_traceState_3410_; lean_object* v_traces_3411_; lean_object* v___x_3412_; lean_object* v_traceState_3413_; lean_object* v_env_3414_; lean_object* v_nextMacroScope_3415_; lean_object* v_ngen_3416_; lean_object* v_auxDeclNGen_3417_; lean_object* v_cache_3418_; lean_object* v_messages_3419_; lean_object* v_infoState_3420_; lean_object* v_snapshotTasks_3421_; lean_object* v___x_3423_; uint8_t v_isShared_3424_; uint8_t v_isSharedCheck_3440_; 
v___x_3409_ = lean_st_ref_get(v___y_3407_);
v_traceState_3410_ = lean_ctor_get(v___x_3409_, 4);
lean_inc_ref(v_traceState_3410_);
lean_dec(v___x_3409_);
v_traces_3411_ = lean_ctor_get(v_traceState_3410_, 0);
lean_inc_ref(v_traces_3411_);
lean_dec_ref(v_traceState_3410_);
v___x_3412_ = lean_st_ref_take(v___y_3407_);
v_traceState_3413_ = lean_ctor_get(v___x_3412_, 4);
v_env_3414_ = lean_ctor_get(v___x_3412_, 0);
v_nextMacroScope_3415_ = lean_ctor_get(v___x_3412_, 1);
v_ngen_3416_ = lean_ctor_get(v___x_3412_, 2);
v_auxDeclNGen_3417_ = lean_ctor_get(v___x_3412_, 3);
v_cache_3418_ = lean_ctor_get(v___x_3412_, 5);
v_messages_3419_ = lean_ctor_get(v___x_3412_, 6);
v_infoState_3420_ = lean_ctor_get(v___x_3412_, 7);
v_snapshotTasks_3421_ = lean_ctor_get(v___x_3412_, 8);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3423_ = v___x_3412_;
v_isShared_3424_ = v_isSharedCheck_3440_;
goto v_resetjp_3422_;
}
else
{
lean_inc(v_snapshotTasks_3421_);
lean_inc(v_infoState_3420_);
lean_inc(v_messages_3419_);
lean_inc(v_cache_3418_);
lean_inc(v_traceState_3413_);
lean_inc(v_auxDeclNGen_3417_);
lean_inc(v_ngen_3416_);
lean_inc(v_nextMacroScope_3415_);
lean_inc(v_env_3414_);
lean_dec(v___x_3412_);
v___x_3423_ = lean_box(0);
v_isShared_3424_ = v_isSharedCheck_3440_;
goto v_resetjp_3422_;
}
v_resetjp_3422_:
{
uint64_t v_tid_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3438_; 
v_tid_3425_ = lean_ctor_get_uint64(v_traceState_3413_, sizeof(void*)*1);
v_isSharedCheck_3438_ = !lean_is_exclusive(v_traceState_3413_);
if (v_isSharedCheck_3438_ == 0)
{
lean_object* v_unused_3439_; 
v_unused_3439_ = lean_ctor_get(v_traceState_3413_, 0);
lean_dec(v_unused_3439_);
v___x_3427_ = v_traceState_3413_;
v_isShared_3428_ = v_isSharedCheck_3438_;
goto v_resetjp_3426_;
}
else
{
lean_dec(v_traceState_3413_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3438_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3431_; 
v___x_3429_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 0, v___x_3429_);
v___x_3431_ = v___x_3427_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v___x_3429_);
lean_ctor_set_uint64(v_reuseFailAlloc_3437_, sizeof(void*)*1, v_tid_3425_);
v___x_3431_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
lean_object* v___x_3433_; 
if (v_isShared_3424_ == 0)
{
lean_ctor_set(v___x_3423_, 4, v___x_3431_);
v___x_3433_ = v___x_3423_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_env_3414_);
lean_ctor_set(v_reuseFailAlloc_3436_, 1, v_nextMacroScope_3415_);
lean_ctor_set(v_reuseFailAlloc_3436_, 2, v_ngen_3416_);
lean_ctor_set(v_reuseFailAlloc_3436_, 3, v_auxDeclNGen_3417_);
lean_ctor_set(v_reuseFailAlloc_3436_, 4, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3436_, 5, v_cache_3418_);
lean_ctor_set(v_reuseFailAlloc_3436_, 6, v_messages_3419_);
lean_ctor_set(v_reuseFailAlloc_3436_, 7, v_infoState_3420_);
lean_ctor_set(v_reuseFailAlloc_3436_, 8, v_snapshotTasks_3421_);
v___x_3433_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; 
v___x_3434_ = lean_st_ref_set(v___y_3407_, v___x_3433_);
v___x_3435_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3435_, 0, v_traces_3411_);
return v___x_3435_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3441_, lean_object* v___y_3442_){
_start:
{
lean_object* v_res_3443_; 
v_res_3443_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3441_);
lean_dec(v___y_3441_);
return v_res_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; 
lean_inc(v___y_3446_);
lean_inc(v___y_3445_);
v___x_3452_ = lean_apply_7(v_x_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_, lean_box(0));
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3453_, v___y_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3455_);
lean_dec(v___y_3454_);
return v_res_3461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3462_, lean_object* v_localInsts_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_){
_start:
{
lean_object* v___f_3472_; lean_object* v___x_3473_; 
lean_inc(v___y_3466_);
lean_inc(v___y_3465_);
v___f_3472_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3472_, 0, v_x_3464_);
lean_closure_set(v___f_3472_, 1, v___y_3465_);
lean_closure_set(v___f_3472_, 2, v___y_3466_);
v___x_3473_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3462_, v_localInsts_3463_, v___f_3472_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
if (lean_obj_tag(v___x_3473_) == 0)
{
return v___x_3473_;
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
v_a_3474_ = lean_ctor_get(v___x_3473_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3473_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3473_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3473_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3482_, lean_object* v_localInsts_3483_, lean_object* v_x_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_){
_start:
{
lean_object* v_res_3492_; 
v_res_3492_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3482_, v_localInsts_3483_, v_x_3484_, v___y_3485_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
lean_dec(v___y_3490_);
lean_dec_ref(v___y_3489_);
lean_dec(v___y_3488_);
lean_dec_ref(v___y_3487_);
lean_dec(v___y_3486_);
lean_dec(v___y_3485_);
return v_res_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3493_){
_start:
{
lean_object* v___x_3495_; lean_object* v_ngen_3496_; lean_object* v_namePrefix_3497_; lean_object* v_idx_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3527_; 
v___x_3495_ = lean_st_ref_get(v___y_3493_);
v_ngen_3496_ = lean_ctor_get(v___x_3495_, 2);
lean_inc_ref(v_ngen_3496_);
lean_dec(v___x_3495_);
v_namePrefix_3497_ = lean_ctor_get(v_ngen_3496_, 0);
v_idx_3498_ = lean_ctor_get(v_ngen_3496_, 1);
v_isSharedCheck_3527_ = !lean_is_exclusive(v_ngen_3496_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3500_ = v_ngen_3496_;
v_isShared_3501_ = v_isSharedCheck_3527_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_idx_3498_);
lean_inc(v_namePrefix_3497_);
lean_dec(v_ngen_3496_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3527_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3502_; lean_object* v_env_3503_; lean_object* v_nextMacroScope_3504_; lean_object* v_auxDeclNGen_3505_; lean_object* v_traceState_3506_; lean_object* v_cache_3507_; lean_object* v_messages_3508_; lean_object* v_infoState_3509_; lean_object* v_snapshotTasks_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3525_; 
v___x_3502_ = lean_st_ref_take(v___y_3493_);
v_env_3503_ = lean_ctor_get(v___x_3502_, 0);
v_nextMacroScope_3504_ = lean_ctor_get(v___x_3502_, 1);
v_auxDeclNGen_3505_ = lean_ctor_get(v___x_3502_, 3);
v_traceState_3506_ = lean_ctor_get(v___x_3502_, 4);
v_cache_3507_ = lean_ctor_get(v___x_3502_, 5);
v_messages_3508_ = lean_ctor_get(v___x_3502_, 6);
v_infoState_3509_ = lean_ctor_get(v___x_3502_, 7);
v_snapshotTasks_3510_ = lean_ctor_get(v___x_3502_, 8);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3525_ == 0)
{
lean_object* v_unused_3526_; 
v_unused_3526_ = lean_ctor_get(v___x_3502_, 2);
lean_dec(v_unused_3526_);
v___x_3512_ = v___x_3502_;
v_isShared_3513_ = v_isSharedCheck_3525_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_snapshotTasks_3510_);
lean_inc(v_infoState_3509_);
lean_inc(v_messages_3508_);
lean_inc(v_cache_3507_);
lean_inc(v_traceState_3506_);
lean_inc(v_auxDeclNGen_3505_);
lean_inc(v_nextMacroScope_3504_);
lean_inc(v_env_3503_);
lean_dec(v___x_3502_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3525_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v_r_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_inc(v_idx_3498_);
lean_inc(v_namePrefix_3497_);
v_r_3514_ = l_Lean_Name_num___override(v_namePrefix_3497_, v_idx_3498_);
v___x_3515_ = lean_unsigned_to_nat(1u);
v___x_3516_ = lean_nat_add(v_idx_3498_, v___x_3515_);
lean_dec(v_idx_3498_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3516_);
v___x_3518_ = v___x_3500_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_namePrefix_3497_);
lean_ctor_set(v_reuseFailAlloc_3524_, 1, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 2, v___x_3518_);
v___x_3520_ = v___x_3512_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_env_3503_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_nextMacroScope_3504_);
lean_ctor_set(v_reuseFailAlloc_3523_, 2, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3523_, 3, v_auxDeclNGen_3505_);
lean_ctor_set(v_reuseFailAlloc_3523_, 4, v_traceState_3506_);
lean_ctor_set(v_reuseFailAlloc_3523_, 5, v_cache_3507_);
lean_ctor_set(v_reuseFailAlloc_3523_, 6, v_messages_3508_);
lean_ctor_set(v_reuseFailAlloc_3523_, 7, v_infoState_3509_);
lean_ctor_set(v_reuseFailAlloc_3523_, 8, v_snapshotTasks_3510_);
v___x_3520_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3521_ = lean_st_ref_set(v___y_3493_, v___x_3520_);
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v_r_3514_);
return v___x_3522_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3528_, lean_object* v___y_3529_){
_start:
{
lean_object* v_res_3530_; 
v_res_3530_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3528_);
lean_dec(v___y_3528_);
return v_res_3530_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
lean_object* v___x_3538_; lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
v___x_3538_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3536_);
v_a_3539_ = lean_ctor_get(v___x_3538_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3538_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3538_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3538_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v___y_3548_);
lean_dec(v___y_3547_);
return v_res_3554_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3556_; lean_object* v___x_3557_; 
v___x_3556_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3557_ = l_Lean_stringToMessageData(v___x_3556_);
return v___x_3557_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3559_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3560_ = l_Lean_stringToMessageData(v___x_3559_);
return v___x_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3563_, lean_object* v_x_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
lean_object* v___x_3572_; lean_object* v___y_3574_; uint8_t v___x_3583_; 
v___x_3572_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3583_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3565_);
if (v___x_3583_ == 0)
{
lean_object* v___x_3584_; 
v___x_3584_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3574_ = v___x_3584_;
goto v___jp_3573_;
}
else
{
lean_object* v___x_3585_; 
v___x_3585_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3574_ = v___x_3585_;
goto v___jp_3573_;
}
v___jp_3573_:
{
lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3575_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3575_, 0, v___y_3574_);
v___x_3576_ = l_Lean_MessageData_ofFormat(v___x_3575_);
v___x_3577_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3572_);
lean_ctor_set(v___x_3577_, 1, v___x_3576_);
v___x_3578_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3579_, 0, v___x_3577_);
lean_ctor_set(v___x_3579_, 1, v___x_3578_);
v___x_3580_ = l_Lean_indentExpr(v_e_3563_);
v___x_3581_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3579_);
lean_ctor_set(v___x_3581_, 1, v___x_3580_);
v___x_3582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
return v___x_3582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3586_, lean_object* v_x_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_res_3595_; 
v_res_3595_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3586_, v_x_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v_x_3587_);
return v_res_3595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3596_, lean_object* v_x_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_keyedConfig_3605_; uint8_t v_trackZetaDelta_3606_; lean_object* v_zetaDeltaSet_3607_; lean_object* v_localInstances_3608_; lean_object* v_defEqCtx_x3f_3609_; lean_object* v_synthPendingDepth_3610_; lean_object* v_canUnfold_x3f_3611_; uint8_t v_univApprox_3612_; uint8_t v_inTypeClassResolution_3613_; uint8_t v_cacheInferType_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v_keyedConfig_3605_ = lean_ctor_get(v___y_3600_, 0);
v_trackZetaDelta_3606_ = lean_ctor_get_uint8(v___y_3600_, sizeof(void*)*7);
v_zetaDeltaSet_3607_ = lean_ctor_get(v___y_3600_, 1);
v_localInstances_3608_ = lean_ctor_get(v___y_3600_, 3);
v_defEqCtx_x3f_3609_ = lean_ctor_get(v___y_3600_, 4);
v_synthPendingDepth_3610_ = lean_ctor_get(v___y_3600_, 5);
v_canUnfold_x3f_3611_ = lean_ctor_get(v___y_3600_, 6);
v_univApprox_3612_ = lean_ctor_get_uint8(v___y_3600_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3613_ = lean_ctor_get_uint8(v___y_3600_, sizeof(void*)*7 + 2);
v_cacheInferType_3614_ = lean_ctor_get_uint8(v___y_3600_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_3611_);
lean_inc(v_synthPendingDepth_3610_);
lean_inc(v_defEqCtx_x3f_3609_);
lean_inc_ref(v_localInstances_3608_);
lean_inc(v_zetaDeltaSet_3607_);
lean_inc_ref(v_keyedConfig_3605_);
v___x_3615_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3615_, 0, v_keyedConfig_3605_);
lean_ctor_set(v___x_3615_, 1, v_zetaDeltaSet_3607_);
lean_ctor_set(v___x_3615_, 2, v_lctx_3596_);
lean_ctor_set(v___x_3615_, 3, v_localInstances_3608_);
lean_ctor_set(v___x_3615_, 4, v_defEqCtx_x3f_3609_);
lean_ctor_set(v___x_3615_, 5, v_synthPendingDepth_3610_);
lean_ctor_set(v___x_3615_, 6, v_canUnfold_x3f_3611_);
lean_ctor_set_uint8(v___x_3615_, sizeof(void*)*7, v_trackZetaDelta_3606_);
lean_ctor_set_uint8(v___x_3615_, sizeof(void*)*7 + 1, v_univApprox_3612_);
lean_ctor_set_uint8(v___x_3615_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3613_);
lean_ctor_set_uint8(v___x_3615_, sizeof(void*)*7 + 3, v_cacheInferType_3614_);
lean_inc(v___y_3603_);
lean_inc_ref(v___y_3602_);
lean_inc(v___y_3601_);
lean_inc(v___y_3599_);
lean_inc(v___y_3598_);
v___x_3616_ = lean_apply_7(v_x_3597_, v___y_3598_, v___y_3599_, v___x_3615_, v___y_3601_, v___y_3602_, v___y_3603_, lean_box(0));
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3619_; uint8_t v_isShared_3620_; uint8_t v_isSharedCheck_3624_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3619_ = v___x_3616_;
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
else
{
lean_inc(v_a_3617_);
lean_dec(v___x_3616_);
v___x_3619_ = lean_box(0);
v_isShared_3620_ = v_isSharedCheck_3624_;
goto v_resetjp_3618_;
}
v_resetjp_3618_:
{
lean_object* v___x_3622_; 
if (v_isShared_3620_ == 0)
{
v___x_3622_ = v___x_3619_;
goto v_reusejp_3621_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v_a_3617_);
v___x_3622_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3621_;
}
v_reusejp_3621_:
{
return v___x_3622_;
}
}
}
else
{
return v___x_3616_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3625_, lean_object* v_x_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_res_3634_; 
v_res_3634_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3625_, v_x_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v___y_3628_);
lean_dec(v___y_3627_);
return v_res_3634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3637_, lean_object* v_letFVars_3638_, lean_object* v_lctx_3639_, lean_object* v_v_3640_, lean_object* v_e_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3650_ = lean_expr_instantiate_rev(v_e_3641_, v_fvars_3637_);
v___x_3651_ = lean_apply_1(v_v_3640_, v___x_3650_);
v___x_3652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3652_, 0, lean_box(0));
lean_closure_set(v___x_3652_, 1, v_letFVars_3638_);
lean_closure_set(v___x_3652_, 2, v___x_3651_);
v___x_3653_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3639_, v___x_3649_, v___x_3652_, v___y_3642_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3654_, lean_object* v_letFVars_3655_, lean_object* v_lctx_3656_, lean_object* v_v_3657_, lean_object* v_e_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v_res_3666_; 
v_res_3666_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3654_, v_letFVars_3655_, v_lctx_3656_, v_v_3657_, v_e_3658_, v___y_3659_, v___y_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec(v___y_3660_);
lean_dec(v___y_3659_);
lean_dec_ref(v_e_3658_);
lean_dec_ref(v_fvars_3654_);
return v_res_3666_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3669_ = l_Lean_stringToMessageData(v___x_3668_);
return v___x_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3670_, lean_object* v_a_3671_, lean_object* v___y_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
lean_object* v___x_3679_; 
lean_inc_ref(v_a_3670_);
v___x_3679_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3670_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v_a_3680_; lean_object* v_expr_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3731_; 
v_a_3680_ = lean_ctor_get(v___x_3679_, 0);
lean_inc(v_a_3680_);
lean_dec_ref(v___x_3679_);
v_expr_3681_ = lean_ctor_get(v_a_3671_, 0);
v_isSharedCheck_3731_ = !lean_is_exclusive(v_a_3671_);
if (v_isSharedCheck_3731_ == 0)
{
lean_object* v_unused_3732_; 
v_unused_3732_ = lean_ctor_get(v_a_3671_, 1);
lean_dec(v_unused_3732_);
v___x_3683_ = v_a_3671_;
v_isShared_3684_ = v_isSharedCheck_3731_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_expr_3681_);
lean_dec(v_a_3671_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3731_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3685_; 
lean_inc(v_a_3680_);
lean_inc_ref(v_expr_3681_);
v___x_3685_ = l_Lean_Meta_isExprDefEq(v_expr_3681_, v_a_3680_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3722_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3688_ = v___x_3685_;
v_isShared_3689_ = v_isSharedCheck_3722_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3685_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3722_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
uint8_t v___x_3690_; 
v___x_3690_ = lean_unbox(v_a_3686_);
lean_dec(v_a_3686_);
if (v___x_3690_ == 0)
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
lean_del_object(v___x_3688_);
v___x_3691_ = lean_box(0);
v___x_3692_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3693_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3680_, v_expr_3681_, v___x_3691_, v___x_3692_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_object* v_a_3694_; lean_object* v_expr_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3708_; 
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
lean_inc(v_a_3694_);
lean_dec_ref(v___x_3693_);
v_expr_3695_ = lean_ctor_get(v_a_3670_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_a_3670_);
if (v_isSharedCheck_3708_ == 0)
{
lean_object* v_unused_3709_; 
v_unused_3709_ = lean_ctor_get(v_a_3670_, 1);
lean_dec(v_unused_3709_);
v___x_3697_ = v_a_3670_;
v_isShared_3698_ = v_isSharedCheck_3708_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_expr_3695_);
lean_dec(v_a_3670_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3708_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3702_; 
v___x_3699_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3700_ = l_Lean_indentExpr(v_expr_3695_);
if (v_isShared_3698_ == 0)
{
lean_ctor_set_tag(v___x_3697_, 7);
lean_ctor_set(v___x_3697_, 1, v___x_3700_);
lean_ctor_set(v___x_3697_, 0, v___x_3699_);
v___x_3702_ = v___x_3697_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v___x_3699_);
lean_ctor_set(v_reuseFailAlloc_3707_, 1, v___x_3700_);
v___x_3702_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
lean_object* v___x_3704_; 
if (v_isShared_3684_ == 0)
{
lean_ctor_set_tag(v___x_3683_, 7);
lean_ctor_set(v___x_3683_, 1, v_a_3694_);
lean_ctor_set(v___x_3683_, 0, v___x_3702_);
v___x_3704_ = v___x_3683_;
goto v_reusejp_3703_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3706_, 1, v_a_3694_);
v___x_3704_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3703_;
}
v_reusejp_3703_:
{
lean_object* v___x_3705_; 
v___x_3705_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3704_, v___y_3674_, v___y_3675_, v___y_3676_, v___y_3677_);
return v___x_3705_;
}
}
}
}
else
{
lean_object* v_a_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3717_; 
lean_del_object(v___x_3683_);
lean_dec_ref(v_a_3670_);
v_a_3710_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3712_ = v___x_3693_;
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_a_3710_);
lean_dec(v___x_3693_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3717_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v___x_3715_; 
if (v_isShared_3713_ == 0)
{
v___x_3715_ = v___x_3712_;
goto v_reusejp_3714_;
}
else
{
lean_object* v_reuseFailAlloc_3716_; 
v_reuseFailAlloc_3716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3716_, 0, v_a_3710_);
v___x_3715_ = v_reuseFailAlloc_3716_;
goto v_reusejp_3714_;
}
v_reusejp_3714_:
{
return v___x_3715_;
}
}
}
}
else
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_del_object(v___x_3683_);
lean_dec_ref(v_expr_3681_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3670_);
v___x_3718_ = lean_box(0);
if (v_isShared_3689_ == 0)
{
lean_ctor_set(v___x_3688_, 0, v___x_3718_);
v___x_3720_ = v___x_3688_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
return v___x_3720_;
}
}
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_del_object(v___x_3683_);
lean_dec_ref(v_expr_3681_);
lean_dec(v_a_3680_);
lean_dec_ref(v_a_3670_);
v_a_3723_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3685_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3685_);
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
else
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3740_; 
lean_dec_ref(v_a_3671_);
lean_dec_ref(v_a_3670_);
v_a_3733_ = lean_ctor_get(v___x_3679_, 0);
v_isSharedCheck_3740_ = !lean_is_exclusive(v___x_3679_);
if (v_isSharedCheck_3740_ == 0)
{
v___x_3735_ = v___x_3679_;
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3679_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3740_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3738_; 
if (v_isShared_3736_ == 0)
{
v___x_3738_ = v___x_3735_;
goto v_reusejp_3737_;
}
else
{
lean_object* v_reuseFailAlloc_3739_; 
v_reuseFailAlloc_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3739_, 0, v_a_3733_);
v___x_3738_ = v_reuseFailAlloc_3739_;
goto v_reusejp_3737_;
}
v_reusejp_3737_:
{
return v___x_3738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3741_, lean_object* v_a_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3741_, v_a_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_, v___y_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec(v___y_3743_);
return v_res_3750_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; 
v___x_3752_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3753_ = l_Lean_stringToMessageData(v___x_3752_);
return v___x_3753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3754_, lean_object* v_a_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_){
_start:
{
if (lean_obj_tag(v_e_3754_) == 5)
{
lean_object* v_fn_3762_; lean_object* v_arg_3763_; lean_object* v___x_3764_; 
v_fn_3762_ = lean_ctor_get(v_e_3754_, 0);
v_arg_3763_ = lean_ctor_get(v_e_3754_, 1);
lean_inc_ref(v_fn_3762_);
v___x_3764_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3762_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3766_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
lean_inc(v_a_3765_);
lean_dec_ref(v___x_3764_);
lean_inc_ref(v_arg_3763_);
v___x_3766_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3763_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3787_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3787_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3787_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_expr_3771_; uint8_t v___y_3773_; size_t v___x_3781_; size_t v___x_3782_; uint8_t v___x_3783_; 
v_expr_3771_ = lean_ctor_get(v_a_3767_, 0);
lean_inc_ref(v_expr_3771_);
lean_dec(v_a_3767_);
v___x_3781_ = lean_ptr_addr(v_fn_3762_);
v___x_3782_ = lean_ptr_addr(v_a_3765_);
v___x_3783_ = lean_usize_dec_eq(v___x_3781_, v___x_3782_);
if (v___x_3783_ == 0)
{
v___y_3773_ = v___x_3783_;
goto v___jp_3772_;
}
else
{
size_t v___x_3784_; size_t v___x_3785_; uint8_t v___x_3786_; 
v___x_3784_ = lean_ptr_addr(v_arg_3763_);
v___x_3785_ = lean_ptr_addr(v_expr_3771_);
v___x_3786_ = lean_usize_dec_eq(v___x_3784_, v___x_3785_);
v___y_3773_ = v___x_3786_;
goto v___jp_3772_;
}
v___jp_3772_:
{
if (v___y_3773_ == 0)
{
lean_object* v___x_3774_; lean_object* v___x_3776_; 
lean_dec_ref(v_e_3754_);
v___x_3774_ = l_Lean_Expr_app___override(v_a_3765_, v_expr_3771_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v___x_3774_);
v___x_3776_ = v___x_3769_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
else
{
lean_object* v___x_3779_; 
lean_dec_ref(v_expr_3771_);
lean_dec(v_a_3765_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v_e_3754_);
v___x_3779_ = v___x_3769_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_e_3754_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_dec(v_a_3765_);
lean_dec_ref(v_e_3754_);
v_a_3788_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3766_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3766_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_dec_ref(v_e_3754_);
return v___x_3764_;
}
}
else
{
lean_object* v___x_3796_; 
v___x_3796_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3799_; uint8_t v_isShared_3800_; uint8_t v_isSharedCheck_3805_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3805_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3805_ == 0)
{
v___x_3799_ = v___x_3796_;
v_isShared_3800_ = v_isSharedCheck_3805_;
goto v_resetjp_3798_;
}
else
{
lean_inc(v_a_3797_);
lean_dec(v___x_3796_);
v___x_3799_ = lean_box(0);
v_isShared_3800_ = v_isSharedCheck_3805_;
goto v_resetjp_3798_;
}
v_resetjp_3798_:
{
lean_object* v_expr_3801_; lean_object* v___x_3803_; 
v_expr_3801_ = lean_ctor_get(v_a_3797_, 0);
lean_inc_ref(v_expr_3801_);
lean_dec(v_a_3797_);
if (v_isShared_3800_ == 0)
{
lean_ctor_set(v___x_3799_, 0, v_expr_3801_);
v___x_3803_ = v___x_3799_;
goto v_reusejp_3802_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v_expr_3801_);
v___x_3803_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3802_;
}
v_reusejp_3802_:
{
return v___x_3803_;
}
}
}
else
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3813_; 
v_a_3806_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3813_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3813_ == 0)
{
v___x_3808_ = v___x_3796_;
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3796_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3813_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v___x_3811_; 
if (v_isShared_3809_ == 0)
{
v___x_3811_ = v___x_3808_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v_a_3806_);
v___x_3811_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
return v___x_3811_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_, lean_object* v_a_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_, lean_object* v_a_3820_, lean_object* v_a_3821_){
_start:
{
lean_object* v_res_3822_; 
v_res_3822_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3814_, v_a_3815_, v_a_3816_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_);
lean_dec(v_a_3820_);
lean_dec_ref(v_a_3819_);
lean_dec(v_a_3818_);
lean_dec_ref(v_a_3817_);
lean_dec(v_a_3816_);
lean_dec(v_a_3815_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_, lean_object* v_a_3829_){
_start:
{
if (lean_obj_tag(v_e_3823_) == 5)
{
lean_object* v_fn_3831_; lean_object* v_arg_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v_fn_3831_ = lean_ctor_get(v_e_3823_, 0);
v_arg_3832_ = lean_ctor_get(v_e_3823_, 1);
lean_inc_ref(v_fn_3831_);
v___x_3833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3833_, 0, v_fn_3831_);
lean_inc_ref(v_fn_3831_);
v___x_3834_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3831_, v___x_3833_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v___x_3836_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref(v___x_3834_);
lean_inc_ref(v_arg_3832_);
v___x_3836_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3832_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref(v___x_3836_);
v___x_3838_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3823_, v_a_3835_, v_a_3837_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3838_;
}
else
{
lean_dec(v_a_3835_);
lean_dec_ref(v_e_3823_);
return v___x_3836_;
}
}
else
{
lean_dec_ref(v_e_3823_);
return v___x_3834_;
}
}
else
{
lean_object* v___x_3839_; 
v___x_3839_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_, v_a_3829_);
return v___x_3839_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_){
_start:
{
uint8_t v___x_3848_; 
v___x_3848_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3841_);
if (v___x_3848_ == 0)
{
lean_object* v___x_3849_; 
v___x_3849_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3859_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3852_ = v___x_3849_;
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3849_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3857_; 
v___x_3854_ = lean_box(0);
v___x_3855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3855_, 0, v_a_3850_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set(v___x_3852_, 0, v___x_3855_);
v___x_3857_ = v___x_3852_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v___x_3855_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
v_a_3860_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3849_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3849_);
v___x_3862_ = lean_box(0);
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
v_resetjp_3861_:
{
lean_object* v___x_3865_; 
if (v_isShared_3863_ == 0)
{
v___x_3865_ = v___x_3862_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3866_; 
v_reuseFailAlloc_3866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_a_3860_);
v___x_3865_ = v_reuseFailAlloc_3866_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
return v___x_3865_;
}
}
}
}
else
{
lean_object* v___x_3868_; 
v___x_3868_ = l_Lean_Expr_getAppFn(v_e_3840_);
if (lean_obj_tag(v___x_3868_) == 2)
{
lean_object* v_mvarId_3869_; lean_object* v_dummy_3870_; lean_object* v_nargs_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_mvarId_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_mvarId_3869_);
lean_dec_ref(v___x_3868_);
v_dummy_3870_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3871_ = l_Lean_Expr_getAppNumArgs(v_e_3840_);
lean_inc(v_nargs_3871_);
v___x_3872_ = lean_mk_array(v_nargs_3871_, v_dummy_3870_);
v___x_3873_ = lean_unsigned_to_nat(1u);
v___x_3874_ = lean_nat_sub(v_nargs_3871_, v___x_3873_);
lean_dec(v_nargs_3871_);
lean_inc_ref(v_e_3840_);
v___x_3875_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3840_, v___x_3872_, v___x_3874_);
v___x_3876_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3869_, v___x_3875_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
lean_dec(v_mvarId_3869_);
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_object* v___x_3877_; 
lean_dec_ref(v___x_3876_);
v___x_3877_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v_e_3840_);
v_a_3878_ = lean_ctor_get(v___x_3876_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3876_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3876_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3876_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
lean_object* v___x_3886_; 
lean_dec_ref(v___x_3868_);
v___x_3886_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_);
return v___x_3886_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3887_, lean_object* v_a_3888_, lean_object* v_a_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_){
_start:
{
lean_object* v_res_3895_; 
v_res_3895_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3887_, v_a_3888_, v_a_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec_ref(v_a_3890_);
lean_dec(v_a_3889_);
lean_dec(v_a_3888_);
return v_res_3895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3896_, lean_object* v_a_3897_, lean_object* v_a_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_){
_start:
{
lean_object* v___x_3904_; 
v___x_3904_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref(v___x_3904_);
v___x_3906_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3905_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
return v___x_3906_;
}
else
{
return v___x_3904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_, lean_object* v_a_3912_, lean_object* v_a_3913_, lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3907_, v_a_3908_, v_a_3909_, v_a_3910_, v_a_3911_, v_a_3912_, v_a_3913_);
lean_dec(v_a_3913_);
lean_dec_ref(v_a_3912_);
lean_dec(v_a_3911_);
lean_dec_ref(v_a_3910_);
lean_dec(v_a_3909_);
lean_dec(v_a_3908_);
return v_res_3915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3916_, lean_object* v_fvars_3917_, lean_object* v_doms_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3916_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v___x_3928_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc(v_a_3927_);
lean_dec_ref(v___x_3926_);
lean_inc_ref(v___y_3921_);
v___x_3928_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3917_, v_doms_3918_, v_a_3927_, v___y_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
return v___x_3928_;
}
else
{
return v___x_3926_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3929_, lean_object* v_fvars_3930_, lean_object* v_doms_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
lean_object* v_res_3939_; 
v_res_3939_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3929_, v_fvars_3930_, v_doms_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec(v___y_3932_);
lean_dec_ref(v_doms_3931_);
lean_dec_ref(v_fvars_3930_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3940_, lean_object* v_fvars_3941_, lean_object* v_doms_3942_, lean_object* v_e_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
lean_object* v___x_3951_; 
v___x_3951_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3943_, v_a_3945_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc(v_a_3952_);
lean_dec_ref(v___x_3951_);
if (lean_obj_tag(v_a_3952_) == 1)
{
lean_object* v_val_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
lean_dec_ref(v_e_3943_);
v_val_3953_ = lean_ctor_get(v_a_3952_, 0);
lean_inc(v_val_3953_);
lean_dec_ref(v_a_3952_);
v___x_3954_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3955_, 0, v_fvars_3941_);
lean_closure_set(v___x_3955_, 1, v_doms_3942_);
lean_closure_set(v___x_3955_, 2, v_val_3953_);
v___x_3956_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3940_, v___x_3954_, v___x_3955_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3956_;
}
else
{
lean_dec(v_a_3952_);
if (lean_obj_tag(v_e_3943_) == 7)
{
lean_object* v_binderName_3957_; lean_object* v_binderType_3958_; lean_object* v_body_3959_; uint8_t v_binderInfo_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
v_binderName_3957_ = lean_ctor_get(v_e_3943_, 0);
lean_inc(v_binderName_3957_);
v_binderType_3958_ = lean_ctor_get(v_e_3943_, 1);
lean_inc_ref(v_binderType_3958_);
v_body_3959_ = lean_ctor_get(v_e_3943_, 2);
lean_inc_ref(v_body_3959_);
v_binderInfo_3960_ = lean_ctor_get_uint8(v_e_3943_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3943_);
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3962_ = lean_expr_instantiate_rev(v_binderType_3958_, v_fvars_3941_);
lean_dec_ref(v_binderType_3958_);
v___x_3963_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3963_, 0, v___x_3962_);
lean_inc_ref(v_lctx_3940_);
v___x_3964_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3940_, v___x_3961_, v___x_3963_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref(v___x_3964_);
v___x_3966_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v_expr_3968_; uint8_t v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref(v___x_3966_);
v_expr_3968_ = lean_ctor_get(v_a_3965_, 0);
v___x_3969_ = 0;
lean_inc_ref(v_expr_3968_);
lean_inc(v_a_3967_);
v___x_3970_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3940_, v_a_3967_, v_binderName_3957_, v_expr_3968_, v_binderInfo_3960_, v___x_3969_);
v___x_3971_ = l_Lean_Expr_fvar___override(v_a_3967_);
v___x_3972_ = lean_array_push(v_fvars_3941_, v___x_3971_);
v___x_3973_ = lean_array_push(v_doms_3942_, v_a_3965_);
v_lctx_3940_ = v___x_3970_;
v_fvars_3941_ = v___x_3972_;
v_doms_3942_ = v___x_3973_;
v_e_3943_ = v_body_3959_;
goto _start;
}
else
{
lean_object* v_a_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_3982_; 
lean_dec(v_a_3965_);
lean_dec_ref(v_body_3959_);
lean_dec(v_binderName_3957_);
lean_dec_ref(v_doms_3942_);
lean_dec_ref(v_fvars_3941_);
lean_dec_ref(v_lctx_3940_);
v_a_3975_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3977_ = v___x_3966_;
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_a_3975_);
lean_dec(v___x_3966_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_3982_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3980_; 
if (v_isShared_3978_ == 0)
{
v___x_3980_ = v___x_3977_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v_a_3975_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
}
else
{
lean_dec_ref(v_body_3959_);
lean_dec(v_binderName_3957_);
lean_dec_ref(v_doms_3942_);
lean_dec_ref(v_fvars_3941_);
lean_dec_ref(v_lctx_3940_);
return v___x_3964_;
}
}
else
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v___f_3985_; lean_object* v___x_3986_; 
v___x_3983_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3984_ = lean_expr_instantiate_rev(v_e_3943_, v_fvars_3941_);
lean_dec_ref(v_e_3943_);
v___f_3985_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3985_, 0, v___x_3984_);
lean_closure_set(v___f_3985_, 1, v_fvars_3941_);
lean_closure_set(v___f_3985_, 2, v_doms_3942_);
v___x_3986_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3940_, v___x_3983_, v___f_3985_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3986_;
}
}
}
else
{
lean_object* v_a_3987_; lean_object* v___x_3989_; uint8_t v_isShared_3990_; uint8_t v_isSharedCheck_3994_; 
lean_dec_ref(v_e_3943_);
lean_dec_ref(v_doms_3942_);
lean_dec_ref(v_fvars_3941_);
lean_dec_ref(v_lctx_3940_);
v_a_3987_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3989_ = v___x_3951_;
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
else
{
lean_inc(v_a_3987_);
lean_dec(v___x_3951_);
v___x_3989_ = lean_box(0);
v_isShared_3990_ = v_isSharedCheck_3994_;
goto v_resetjp_3988_;
}
v_resetjp_3988_:
{
lean_object* v___x_3992_; 
if (v_isShared_3990_ == 0)
{
v___x_3992_ = v___x_3989_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v_a_3987_);
v___x_3992_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
return v___x_3992_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_, lean_object* v_a_4001_){
_start:
{
uint32_t v___x_4003_; uint8_t v___x_4004_; 
v___x_4003_ = 5;
v___x_4004_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3995_, v___x_4003_);
if (v___x_4004_ == 0)
{
lean_object* v_lctx_4005_; lean_object* v___x_4006_; lean_object* v___x_4007_; 
v_lctx_4005_ = lean_ctor_get(v_a_3998_, 2);
lean_inc_ref(v_lctx_4005_);
v___x_4006_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_4007_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4005_, v___x_4006_, v___x_4006_, v_e_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_);
lean_dec_ref(v_a_3998_);
return v___x_4007_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
lean_dec_ref(v_a_3998_);
v___x_4008_ = lean_box(0);
v___x_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4009_, 0, v_e_3995_);
lean_ctor_set(v___x_4009_, 1, v___x_4008_);
v___x_4010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
return v___x_4010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_4011_, lean_object* v_a_4012_, lean_object* v_a_4013_, lean_object* v_a_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_){
_start:
{
lean_object* v_res_4019_; 
v_res_4019_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_4011_, v_a_4012_, v_a_4013_, v_a_4014_, v_a_4015_, v_a_4016_, v_a_4017_);
lean_dec(v_a_4017_);
lean_dec_ref(v_a_4016_);
lean_dec(v_a_4015_);
lean_dec(v_a_4013_);
lean_dec(v_a_4012_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_4020_, lean_object* v_e_4021_, lean_object* v_typeName_4022_, lean_object* v_idx_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4020_, v_e_4021_, v_typeName_4022_, v_idx_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec(v___y_4024_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4032_, lean_object* v_a_4033_, lean_object* v_a_4034_, lean_object* v_a_4035_, lean_object* v_a_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4032_, v_a_4033_, v_a_4034_, v_a_4035_, v_a_4036_, v_a_4037_, v_a_4038_);
lean_dec(v_a_4038_);
lean_dec_ref(v_a_4037_);
lean_dec(v_a_4036_);
lean_dec_ref(v_a_4035_);
lean_dec(v_a_4034_);
lean_dec(v_a_4033_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v___x_4050_; 
v___x_4050_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4052_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4050_);
v___x_4052_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4041_, v_a_4051_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
return v___x_4052_;
}
else
{
lean_dec_ref(v_fvars_4041_);
return v___x_4050_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_){
_start:
{
lean_object* v_res_4062_; 
v_res_4062_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_, v___y_4058_, v___y_4059_, v___y_4060_);
lean_dec(v___y_4060_);
lean_dec_ref(v___y_4059_);
lean_dec(v___y_4058_);
lean_dec_ref(v___y_4057_);
lean_dec(v___y_4056_);
lean_dec(v___y_4055_);
return v_res_4062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4063_, lean_object* v_fvars_4064_, lean_object* v_e_4065_, lean_object* v_letFVars_4066_, lean_object* v_a_4067_, lean_object* v_a_4068_, lean_object* v_a_4069_, lean_object* v_a_4070_, lean_object* v_a_4071_, lean_object* v_a_4072_){
_start:
{
switch(lean_obj_tag(v_e_4065_))
{
case 6:
{
lean_object* v_binderName_4074_; lean_object* v_binderType_4075_; lean_object* v_body_4076_; uint8_t v_binderInfo_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_binderName_4074_ = lean_ctor_get(v_e_4065_, 0);
lean_inc(v_binderName_4074_);
v_binderType_4075_ = lean_ctor_get(v_e_4065_, 1);
lean_inc_ref(v_binderType_4075_);
v_body_4076_ = lean_ctor_get(v_e_4065_, 2);
lean_inc_ref(v_body_4076_);
v_binderInfo_4077_ = lean_ctor_get_uint8(v_e_4065_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_4065_);
v___x_4078_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4063_);
lean_inc(v_letFVars_4066_);
v___x_4079_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4064_, v_letFVars_4066_, v_lctx_4063_, v___x_4078_, v_binderType_4075_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec_ref(v_binderType_4075_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4081_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref(v___x_4079_);
v___x_4081_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4081_) == 0)
{
lean_object* v_a_4082_; lean_object* v_expr_4083_; uint8_t v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v_a_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc(v_a_4082_);
lean_dec_ref(v___x_4081_);
v_expr_4083_ = lean_ctor_get(v_a_4080_, 0);
lean_inc_ref(v_expr_4083_);
lean_dec(v_a_4080_);
v___x_4084_ = 0;
lean_inc(v_a_4082_);
v___x_4085_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4063_, v_a_4082_, v_binderName_4074_, v_expr_4083_, v_binderInfo_4077_, v___x_4084_);
v___x_4086_ = l_Lean_Expr_fvar___override(v_a_4082_);
v___x_4087_ = lean_array_push(v_fvars_4064_, v___x_4086_);
v_lctx_4063_ = v___x_4085_;
v_fvars_4064_ = v___x_4087_;
v_e_4065_ = v_body_4076_;
goto _start;
}
else
{
lean_object* v_a_4089_; lean_object* v___x_4091_; uint8_t v_isShared_4092_; uint8_t v_isSharedCheck_4096_; 
lean_dec(v_a_4080_);
lean_dec_ref(v_body_4076_);
lean_dec(v_binderName_4074_);
lean_dec(v_letFVars_4066_);
lean_dec_ref(v_fvars_4064_);
lean_dec_ref(v_lctx_4063_);
v_a_4089_ = lean_ctor_get(v___x_4081_, 0);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4081_);
if (v_isSharedCheck_4096_ == 0)
{
v___x_4091_ = v___x_4081_;
v_isShared_4092_ = v_isSharedCheck_4096_;
goto v_resetjp_4090_;
}
else
{
lean_inc(v_a_4089_);
lean_dec(v___x_4081_);
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
else
{
lean_dec_ref(v_body_4076_);
lean_dec(v_binderName_4074_);
lean_dec(v_letFVars_4066_);
lean_dec_ref(v_fvars_4064_);
lean_dec_ref(v_lctx_4063_);
return v___x_4079_;
}
}
case 8:
{
lean_object* v_declName_4097_; lean_object* v_type_4098_; lean_object* v_value_4099_; lean_object* v_body_4100_; uint8_t v_nondep_4101_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; lean_object* v___y_4111_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v_declName_4097_ = lean_ctor_get(v_e_4065_, 0);
lean_inc(v_declName_4097_);
v_type_4098_ = lean_ctor_get(v_e_4065_, 1);
lean_inc_ref(v_type_4098_);
v_value_4099_ = lean_ctor_get(v_e_4065_, 2);
lean_inc_ref(v_value_4099_);
v_body_4100_ = lean_ctor_get(v_e_4065_, 3);
lean_inc_ref(v_body_4100_);
v_nondep_4101_ = lean_ctor_get_uint8(v_e_4065_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_4065_);
v___x_4115_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4063_);
lean_inc(v_letFVars_4066_);
v___x_4116_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4064_, v_letFVars_4066_, v_lctx_4063_, v___x_4115_, v_type_4098_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec_ref(v_type_4098_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_object* v_a_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
lean_inc(v_a_4117_);
lean_dec_ref(v___x_4116_);
v___x_4118_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4063_);
lean_inc(v_letFVars_4066_);
v___x_4119_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4064_, v_letFVars_4066_, v_lctx_4063_, v___x_4118_, v_value_4099_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec_ref(v_value_4099_);
if (lean_obj_tag(v___x_4119_) == 0)
{
lean_object* v_a_4120_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; uint8_t v___x_4150_; 
v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
lean_inc(v_a_4120_);
lean_dec_ref(v___x_4119_);
v___x_4150_ = l_List_isEmpty___redArg(v_letFVars_4066_);
if (v___x_4150_ == 0)
{
lean_object* v___f_4151_; lean_object* v___x_4152_; 
lean_inc(v_a_4117_);
lean_inc(v_a_4120_);
v___f_4151_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4151_, 0, v_a_4120_);
lean_closure_set(v___f_4151_, 1, v_a_4117_);
lean_inc_ref(v_lctx_4063_);
v___x_4152_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4063_, v___f_4151_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_dec_ref(v___x_4152_);
v___y_4122_ = v_a_4067_;
v___y_4123_ = v_a_4068_;
v___y_4124_ = v_a_4069_;
v___y_4125_ = v_a_4070_;
v___y_4126_ = v_a_4071_;
v___y_4127_ = v_a_4072_;
goto v___jp_4121_;
}
else
{
lean_object* v_a_4153_; lean_object* v___x_4155_; uint8_t v_isShared_4156_; uint8_t v_isSharedCheck_4160_; 
lean_dec(v_a_4120_);
lean_dec(v_a_4117_);
lean_dec_ref(v_body_4100_);
lean_dec(v_declName_4097_);
lean_dec(v_letFVars_4066_);
lean_dec_ref(v_fvars_4064_);
lean_dec_ref(v_lctx_4063_);
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4160_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4160_ == 0)
{
v___x_4155_ = v___x_4152_;
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
else
{
lean_inc(v_a_4153_);
lean_dec(v___x_4152_);
v___x_4155_ = lean_box(0);
v_isShared_4156_ = v_isSharedCheck_4160_;
goto v_resetjp_4154_;
}
v_resetjp_4154_:
{
lean_object* v___x_4158_; 
if (v_isShared_4156_ == 0)
{
v___x_4158_ = v___x_4155_;
goto v_reusejp_4157_;
}
else
{
lean_object* v_reuseFailAlloc_4159_; 
v_reuseFailAlloc_4159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4159_, 0, v_a_4153_);
v___x_4158_ = v_reuseFailAlloc_4159_;
goto v_reusejp_4157_;
}
v_reusejp_4157_:
{
return v___x_4158_;
}
}
}
}
else
{
v___y_4122_ = v_a_4067_;
v___y_4123_ = v_a_4068_;
v___y_4124_ = v_a_4069_;
v___y_4125_ = v_a_4070_;
v___y_4126_ = v_a_4071_;
v___y_4127_ = v_a_4072_;
goto v___jp_4121_;
}
v___jp_4121_:
{
lean_object* v___x_4128_; 
v___x_4128_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
if (lean_obj_tag(v___x_4128_) == 0)
{
lean_object* v_a_4129_; lean_object* v_expr_4130_; lean_object* v_expr_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4140_; 
v_a_4129_ = lean_ctor_get(v___x_4128_, 0);
lean_inc(v_a_4129_);
lean_dec_ref(v___x_4128_);
v_expr_4130_ = lean_ctor_get(v_a_4117_, 0);
lean_inc_ref(v_expr_4130_);
lean_dec(v_a_4117_);
v_expr_4131_ = lean_ctor_get(v_a_4120_, 0);
v_isSharedCheck_4140_ = !lean_is_exclusive(v_a_4120_);
if (v_isSharedCheck_4140_ == 0)
{
lean_object* v_unused_4141_; 
v_unused_4141_ = lean_ctor_get(v_a_4120_, 1);
lean_dec(v_unused_4141_);
v___x_4133_ = v_a_4120_;
v_isShared_4134_ = v_isSharedCheck_4140_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_expr_4131_);
lean_dec(v_a_4120_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4140_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
uint8_t v___x_4135_; lean_object* v___x_4136_; 
v___x_4135_ = 0;
lean_inc(v_a_4129_);
v___x_4136_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4063_, v_a_4129_, v_declName_4097_, v_expr_4130_, v_expr_4131_, v_nondep_4101_, v___x_4135_);
if (v_nondep_4101_ == 0)
{
lean_object* v___x_4138_; 
lean_inc(v_a_4129_);
if (v_isShared_4134_ == 0)
{
lean_ctor_set_tag(v___x_4133_, 1);
lean_ctor_set(v___x_4133_, 1, v_letFVars_4066_);
lean_ctor_set(v___x_4133_, 0, v_a_4129_);
v___x_4138_ = v___x_4133_;
goto v_reusejp_4137_;
}
else
{
lean_object* v_reuseFailAlloc_4139_; 
v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4129_);
lean_ctor_set(v_reuseFailAlloc_4139_, 1, v_letFVars_4066_);
v___x_4138_ = v_reuseFailAlloc_4139_;
goto v_reusejp_4137_;
}
v_reusejp_4137_:
{
v___y_4103_ = v___y_4124_;
v___y_4104_ = v___y_4123_;
v___y_4105_ = v___y_4127_;
v___y_4106_ = v___y_4122_;
v___y_4107_ = v___y_4126_;
v___y_4108_ = v_a_4129_;
v___y_4109_ = v___x_4136_;
v___y_4110_ = v___y_4125_;
v___y_4111_ = v___x_4138_;
goto v___jp_4102_;
}
}
else
{
lean_del_object(v___x_4133_);
v___y_4103_ = v___y_4124_;
v___y_4104_ = v___y_4123_;
v___y_4105_ = v___y_4127_;
v___y_4106_ = v___y_4122_;
v___y_4107_ = v___y_4126_;
v___y_4108_ = v_a_4129_;
v___y_4109_ = v___x_4136_;
v___y_4110_ = v___y_4125_;
v___y_4111_ = v_letFVars_4066_;
goto v___jp_4102_;
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
lean_dec(v_a_4120_);
lean_dec(v_a_4117_);
lean_dec_ref(v_body_4100_);
lean_dec(v_declName_4097_);
lean_dec(v_letFVars_4066_);
lean_dec_ref(v_fvars_4064_);
lean_dec_ref(v_lctx_4063_);
v_a_4142_ = lean_ctor_get(v___x_4128_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4128_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___x_4128_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___x_4128_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
else
{
lean_dec(v_a_4117_);
lean_dec_ref(v_body_4100_);
lean_dec(v_declName_4097_);
lean_dec(v_letFVars_4066_);
lean_dec_ref(v_fvars_4064_);
lean_dec_ref(v_lctx_4063_);
return v___x_4119_;
}
}
else
{
lean_dec_ref(v_body_4100_);
lean_dec_ref(v_value_4099_);
lean_dec(v_declName_4097_);
lean_dec(v_letFVars_4066_);
lean_dec_ref(v_fvars_4064_);
lean_dec_ref(v_lctx_4063_);
return v___x_4116_;
}
v___jp_4102_:
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = l_Lean_Expr_fvar___override(v___y_4108_);
v___x_4113_ = lean_array_push(v_fvars_4064_, v___x_4112_);
v_lctx_4063_ = v___y_4109_;
v_fvars_4064_ = v___x_4113_;
v_e_4065_ = v_body_4100_;
v_letFVars_4066_ = v___y_4111_;
v_a_4067_ = v___y_4106_;
v_a_4068_ = v___y_4104_;
v_a_4069_ = v___y_4103_;
v_a_4070_ = v___y_4110_;
v_a_4071_ = v___y_4107_;
v_a_4072_ = v___y_4105_;
goto _start;
}
}
default: 
{
lean_object* v___f_4161_; lean_object* v___x_4162_; 
lean_inc_ref(v_fvars_4064_);
v___f_4161_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4161_, 0, v_fvars_4064_);
v___x_4162_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4064_, v_letFVars_4066_, v_lctx_4063_, v___f_4161_, v_e_4065_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_, v_a_4071_, v_a_4072_);
lean_dec_ref(v_e_4065_);
lean_dec_ref(v_fvars_4064_);
return v___x_4162_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
uint32_t v___x_4171_; uint8_t v___x_4172_; 
v___x_4171_ = 5;
v___x_4172_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4163_, v___x_4171_);
if (v___x_4172_ == 0)
{
lean_object* v_lctx_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v_lctx_4173_ = lean_ctor_get(v_a_4166_, 2);
lean_inc_ref(v_lctx_4173_);
v___x_4174_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4164_);
v___x_4175_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4173_, v___x_4174_, v_e_4163_, v_a_4164_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_, v_a_4169_);
lean_dec_ref(v_a_4166_);
return v___x_4175_;
}
else
{
lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
lean_dec_ref(v_a_4166_);
v___x_4176_ = lean_box(0);
v___x_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4177_, 0, v_e_4163_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v___x_4177_);
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_, lean_object* v_a_4183_, lean_object* v_a_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_){
_start:
{
lean_object* v_res_4187_; 
v_res_4187_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4179_, v_a_4180_, v_a_4181_, v_a_4182_, v_a_4183_, v_a_4184_, v_a_4185_);
lean_dec(v_a_4185_);
lean_dec_ref(v_a_4184_);
lean_dec(v_a_4183_);
lean_dec(v_a_4181_);
lean_dec(v_a_4180_);
return v_res_4187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_){
_start:
{
switch(lean_obj_tag(v_e_4188_))
{
case 0:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4196_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4197_ = l_Lean_MessageData_ofExpr(v_e_4188_);
v___x_4198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4196_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4198_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4199_;
}
case 1:
{
lean_object* v___x_4200_; 
v___x_4200_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4188_, v___y_4191_, v___y_4193_, v___y_4194_);
return v___x_4200_;
}
case 2:
{
lean_object* v___x_4201_; 
v___x_4201_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4201_;
}
case 3:
{
lean_object* v_u_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; lean_object* v___x_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_u_4202_ = lean_ctor_get(v_e_4188_, 0);
lean_inc(v_u_4202_);
v___x_4203_ = l_Lean_Level_succ___override(v_u_4202_);
v___x_4204_ = l_Lean_Expr_sort___override(v___x_4203_);
v___x_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4205_, 0, v___x_4204_);
v___x_4206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4206_, 0, v_e_4188_);
lean_ctor_set(v___x_4206_, 1, v___x_4205_);
v___x_4207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
return v___x_4207_;
}
case 4:
{
lean_object* v___x_4208_; 
v___x_4208_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4208_;
}
case 5:
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
lean_inc_ref(v_e_4188_);
v___x_4209_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4209_, 0, v_e_4188_);
v___x_4210_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4188_, v___x_4209_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4210_;
}
case 7:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_inc_ref(v_e_4188_);
v___x_4211_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4211_, 0, v_e_4188_);
v___x_4212_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4188_, v___x_4211_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4212_;
}
case 9:
{
lean_object* v_a_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v_a_4213_ = lean_ctor_get(v_e_4188_, 0);
v___x_4214_ = l_Lean_Literal_type(v_a_4213_);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v_e_4188_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4216_);
return v___x_4217_;
}
case 10:
{
lean_object* v_data_4218_; lean_object* v_expr_4219_; lean_object* v___x_4220_; 
v_data_4218_ = lean_ctor_get(v_e_4188_, 0);
v_expr_4219_ = lean_ctor_get(v_e_4188_, 1);
lean_inc_ref(v_expr_4219_);
v___x_4220_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4219_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4223_; uint8_t v_isShared_4224_; uint8_t v_isSharedCheck_4243_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
v_isSharedCheck_4243_ = !lean_is_exclusive(v___x_4220_);
if (v_isSharedCheck_4243_ == 0)
{
v___x_4223_ = v___x_4220_;
v_isShared_4224_ = v_isSharedCheck_4243_;
goto v_resetjp_4222_;
}
else
{
lean_inc(v_a_4221_);
lean_dec(v___x_4220_);
v___x_4223_ = lean_box(0);
v_isShared_4224_ = v_isSharedCheck_4243_;
goto v_resetjp_4222_;
}
v_resetjp_4222_:
{
lean_object* v_expr_4225_; lean_object* v_type_x3f_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4242_; 
v_expr_4225_ = lean_ctor_get(v_a_4221_, 0);
v_type_x3f_4226_ = lean_ctor_get(v_a_4221_, 1);
v_isSharedCheck_4242_ = !lean_is_exclusive(v_a_4221_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4228_ = v_a_4221_;
v_isShared_4229_ = v_isSharedCheck_4242_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_type_x3f_4226_);
lean_inc(v_expr_4225_);
lean_dec(v_a_4221_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4242_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___y_4231_; size_t v___x_4238_; size_t v___x_4239_; uint8_t v___x_4240_; 
v___x_4238_ = lean_ptr_addr(v_expr_4219_);
v___x_4239_ = lean_ptr_addr(v_expr_4225_);
v___x_4240_ = lean_usize_dec_eq(v___x_4238_, v___x_4239_);
if (v___x_4240_ == 0)
{
lean_object* v___x_4241_; 
lean_inc(v_data_4218_);
lean_dec_ref(v_e_4188_);
v___x_4241_ = l_Lean_Expr_mdata___override(v_data_4218_, v_expr_4225_);
v___y_4231_ = v___x_4241_;
goto v___jp_4230_;
}
else
{
lean_dec_ref(v_expr_4225_);
v___y_4231_ = v_e_4188_;
goto v___jp_4230_;
}
v___jp_4230_:
{
lean_object* v___x_4233_; 
if (v_isShared_4229_ == 0)
{
lean_ctor_set(v___x_4228_, 0, v___y_4231_);
v___x_4233_ = v___x_4228_;
goto v_reusejp_4232_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v___y_4231_);
lean_ctor_set(v_reuseFailAlloc_4237_, 1, v_type_x3f_4226_);
v___x_4233_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4232_;
}
v_reusejp_4232_:
{
lean_object* v___x_4235_; 
if (v_isShared_4224_ == 0)
{
lean_ctor_set(v___x_4223_, 0, v___x_4233_);
v___x_4235_ = v___x_4223_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
}
}
else
{
lean_dec_ref(v_e_4188_);
return v___x_4220_;
}
}
case 11:
{
lean_object* v_typeName_4244_; lean_object* v_idx_4245_; lean_object* v_struct_4246_; lean_object* v___f_4247_; lean_object* v___x_4248_; 
v_typeName_4244_ = lean_ctor_get(v_e_4188_, 0);
v_idx_4245_ = lean_ctor_get(v_e_4188_, 1);
v_struct_4246_ = lean_ctor_get(v_e_4188_, 2);
lean_inc(v_idx_4245_);
lean_inc(v_typeName_4244_);
lean_inc_ref(v_e_4188_);
lean_inc_ref(v_struct_4246_);
v___f_4247_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4247_, 0, v_struct_4246_);
lean_closure_set(v___f_4247_, 1, v_e_4188_);
lean_closure_set(v___f_4247_, 2, v_typeName_4244_);
lean_closure_set(v___f_4247_, 3, v_idx_4245_);
v___x_4248_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4188_, v___f_4247_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4248_;
}
default: 
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
lean_inc_ref(v_e_4188_);
v___x_4249_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4249_, 0, v_e_4188_);
v___x_4250_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4188_, v___x_4249_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
return v___x_4250_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4251_; double v___x_4252_; 
v___x_4251_ = lean_unsigned_to_nat(1000000000u);
v___x_4252_ = lean_float_of_nat(v___x_4251_);
return v___x_4252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4253_, lean_object* v_a_4254_, lean_object* v_a_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_, lean_object* v_a_4258_, lean_object* v_a_4259_){
_start:
{
lean_object* v_options_4261_; uint8_t v_hasTrace_4262_; 
v_options_4261_ = lean_ctor_get(v_a_4258_, 2);
v_hasTrace_4262_ = lean_ctor_get_uint8(v_options_4261_, sizeof(void*)*1);
if (v_hasTrace_4262_ == 0)
{
lean_object* v___x_4263_; 
v___x_4263_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4263_;
}
else
{
lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4264_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4265_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg(v___x_4264_, v_a_4258_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; lean_object* v___f_4267_; lean_object* v___x_4268_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v_a_4272_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v_a_4288_; uint8_t v___x_4347_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref(v___x_4265_);
lean_inc_ref(v_e_4253_);
v___f_4267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4267_, 0, v_e_4253_);
v___x_4268_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__1));
v___x_4347_ = lean_unbox(v_a_4266_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4348_; uint8_t v___x_4349_; 
v___x_4348_ = l_Lean_trace_profiler;
v___x_4349_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4261_, v___x_4348_);
if (v___x_4349_ == 0)
{
lean_object* v___x_4350_; 
lean_dec_ref(v___f_4267_);
lean_dec(v_a_4266_);
v___x_4350_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4350_;
}
else
{
goto v___jp_4298_;
}
}
else
{
goto v___jp_4298_;
}
v___jp_4269_:
{
lean_object* v___x_4273_; double v___x_4274_; double v___x_4275_; double v___x_4276_; double v___x_4277_; double v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; lean_object* v___x_4284_; 
v___x_4273_ = lean_io_mono_nanos_now();
v___x_4274_ = lean_float_of_nat(v___y_4270_);
v___x_4275_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4276_ = lean_float_div(v___x_4274_, v___x_4275_);
v___x_4277_ = lean_float_of_nat(v___x_4273_);
v___x_4278_ = lean_float_div(v___x_4277_, v___x_4275_);
v___x_4279_ = lean_box_float(v___x_4276_);
v___x_4280_ = lean_box_float(v___x_4278_);
v___x_4281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4279_);
lean_ctor_set(v___x_4281_, 1, v___x_4280_);
v___x_4282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4282_, 0, v_a_4272_);
lean_ctor_set(v___x_4282_, 1, v___x_4281_);
v___x_4283_ = lean_unbox(v_a_4266_);
lean_dec(v_a_4266_);
v___x_4284_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4264_, v_hasTrace_4262_, v___x_4268_, v_options_4261_, v___x_4283_, v___y_4271_, v___f_4267_, v___x_4282_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4284_;
}
v___jp_4285_:
{
lean_object* v___x_4289_; double v___x_4290_; double v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; lean_object* v___x_4297_; 
v___x_4289_ = lean_io_get_num_heartbeats();
v___x_4290_ = lean_float_of_nat(v___y_4287_);
v___x_4291_ = lean_float_of_nat(v___x_4289_);
v___x_4292_ = lean_box_float(v___x_4290_);
v___x_4293_ = lean_box_float(v___x_4291_);
v___x_4294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4292_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4295_, 0, v_a_4288_);
lean_ctor_set(v___x_4295_, 1, v___x_4294_);
v___x_4296_ = lean_unbox(v_a_4266_);
lean_dec(v_a_4266_);
v___x_4297_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4264_, v_hasTrace_4262_, v___x_4268_, v_options_4261_, v___x_4296_, v___y_4286_, v___f_4267_, v___x_4295_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
return v___x_4297_;
}
v___jp_4298_:
{
lean_object* v___x_4299_; 
v___x_4299_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4259_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4301_; uint8_t v___x_4302_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref(v___x_4299_);
v___x_4301_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4302_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4261_, v___x_4301_);
if (v___x_4302_ == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4304_; 
v___x_4303_ = lean_io_mono_nanos_now();
v___x_4304_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
v_a_4305_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4304_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4304_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
lean_ctor_set_tag(v___x_4307_, 1);
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
v___y_4270_ = v___x_4303_;
v___y_4271_ = v_a_4300_;
v_a_4272_ = v___x_4310_;
goto v___jp_4269_;
}
}
}
else
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4320_; 
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
lean_ctor_set_tag(v___x_4315_, 0);
v___x_4318_ = v___x_4315_;
goto v_reusejp_4317_;
}
else
{
lean_object* v_reuseFailAlloc_4319_; 
v_reuseFailAlloc_4319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4319_, 0, v_a_4313_);
v___x_4318_ = v_reuseFailAlloc_4319_;
goto v_reusejp_4317_;
}
v_reusejp_4317_:
{
v___y_4270_ = v___x_4303_;
v___y_4271_ = v_a_4300_;
v_a_4272_ = v___x_4318_;
goto v___jp_4269_;
}
}
}
}
else
{
lean_object* v___x_4321_; lean_object* v___x_4322_; 
v___x_4321_ = lean_io_get_num_heartbeats();
v___x_4322_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4253_, v_a_4254_, v_a_4255_, v_a_4256_, v_a_4257_, v_a_4258_, v_a_4259_);
if (lean_obj_tag(v___x_4322_) == 0)
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
v_a_4323_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4322_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4322_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
lean_ctor_set_tag(v___x_4325_, 1);
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
v___y_4286_ = v_a_4300_;
v___y_4287_ = v___x_4321_;
v_a_4288_ = v___x_4328_;
goto v___jp_4285_;
}
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
v_a_4331_ = lean_ctor_get(v___x_4322_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4322_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4322_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4322_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
lean_ctor_set_tag(v___x_4333_, 0);
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
v___y_4286_ = v_a_4300_;
v___y_4287_ = v___x_4321_;
v_a_4288_ = v___x_4336_;
goto v___jp_4285_;
}
}
}
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v___f_4267_);
lean_dec(v_a_4266_);
lean_dec_ref(v_e_4253_);
v_a_4339_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4299_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4299_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
}
else
{
lean_object* v_a_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4358_; 
lean_dec_ref(v_e_4253_);
v_a_4351_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4358_ == 0)
{
v___x_4353_ = v___x_4265_;
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_a_4351_);
lean_dec(v___x_4265_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4358_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4356_; 
if (v_isShared_4354_ == 0)
{
v___x_4356_ = v___x_4353_;
goto v_reusejp_4355_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_a_4351_);
v___x_4356_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4355_;
}
v_reusejp_4355_:
{
return v___x_4356_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4359_, lean_object* v_e_4360_, lean_object* v_typeName_4361_, lean_object* v_idx_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___x_4370_; 
v___x_4370_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4359_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v_a_4371_; lean_object* v___x_4372_; 
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc(v_a_4371_);
lean_dec_ref(v___x_4370_);
v___x_4372_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4360_, v_typeName_4361_, v_idx_4362_, v_a_4371_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
return v___x_4372_;
}
else
{
lean_dec(v_idx_4362_);
lean_dec(v_typeName_4361_);
lean_dec_ref(v_e_4360_);
return v___x_4370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4373_, lean_object* v_a_4374_, lean_object* v_a_4375_, lean_object* v_a_4376_, lean_object* v_a_4377_, lean_object* v_a_4378_, lean_object* v_a_4379_, lean_object* v_a_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4373_, v_a_4374_, v_a_4375_, v_a_4376_, v_a_4377_, v_a_4378_, v_a_4379_);
lean_dec(v_a_4379_);
lean_dec_ref(v_a_4378_);
lean_dec(v_a_4377_);
lean_dec_ref(v_a_4376_);
lean_dec(v_a_4375_);
lean_dec(v_a_4374_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4382_, lean_object* v_fvars_4383_, lean_object* v_doms_4384_, lean_object* v_e_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_, lean_object* v_a_4391_, lean_object* v_a_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4382_, v_fvars_4383_, v_doms_4384_, v_e_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_, v_a_4391_);
lean_dec(v_a_4391_);
lean_dec_ref(v_a_4390_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec(v_a_4386_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v_res_4402_; 
v_res_4402_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_);
lean_dec(v___y_4400_);
lean_dec_ref(v___y_4399_);
lean_dec(v___y_4398_);
lean_dec_ref(v___y_4397_);
lean_dec(v___y_4396_);
lean_dec(v___y_4395_);
return v_res_4402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4403_, lean_object* v_fvars_4404_, lean_object* v_e_4405_, lean_object* v_letFVars_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_, lean_object* v_a_4411_, lean_object* v_a_4412_, lean_object* v_a_4413_){
_start:
{
lean_object* v_res_4414_; 
v_res_4414_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4403_, v_fvars_4404_, v_e_4405_, v_letFVars_4406_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_, v_a_4411_, v_a_4412_);
lean_dec(v_a_4412_);
lean_dec_ref(v_a_4411_);
lean_dec(v_a_4410_);
lean_dec_ref(v_a_4409_);
lean_dec(v_a_4408_);
lean_dec(v_a_4407_);
return v_res_4414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4415_, lean_object* v_lctx_4416_, lean_object* v_localInsts_4417_, lean_object* v_x_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4416_, v_localInsts_4417_, v_x_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_lctx_4428_, lean_object* v_localInsts_4429_, lean_object* v_x_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4427_, v_lctx_4428_, v_localInsts_4429_, v_x_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec(v___y_4431_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4439_, lean_object* v_lctx_4440_, lean_object* v_x_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_){
_start:
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4440_, v_x_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4450_, lean_object* v_lctx_4451_, lean_object* v_x_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4450_, v_lctx_4451_, v_x_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec(v___y_4453_);
return v_res_4460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_){
_start:
{
lean_object* v___x_4468_; 
v___x_4468_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4466_);
return v___x_4468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v_res_4476_; 
v_res_4476_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_, v___y_4474_);
lean_dec(v___y_4474_);
lean_dec_ref(v___y_4473_);
lean_dec(v___y_4472_);
lean_dec_ref(v___y_4471_);
lean_dec(v___y_4470_);
lean_dec(v___y_4469_);
return v_res_4476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4482_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_){
_start:
{
lean_object* v_res_4492_; 
v_res_4492_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4489_);
lean_dec(v___y_4488_);
lean_dec_ref(v___y_4487_);
lean_dec(v___y_4486_);
lean_dec(v___y_4485_);
return v_res_4492_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_00_u03b1_4493_, lean_object* v_x_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_){
_start:
{
lean_object* v___x_4502_; 
v___x_4502_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___redArg(v_x_4494_);
return v___x_4502_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_00_u03b1_4503_, lean_object* v_x_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_00_u03b1_4503_, v_x_4504_, v___y_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec(v___y_4505_);
return v_res_4512_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_oldTraces_4513_, lean_object* v_data_4514_, lean_object* v_ref_4515_, lean_object* v_msg_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v___x_4524_; 
v___x_4524_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_oldTraces_4513_, v_data_4514_, v_ref_4515_, v_msg_4516_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
return v___x_4524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_oldTraces_4525_, lean_object* v_data_4526_, lean_object* v_ref_4527_, lean_object* v_msg_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v_res_4536_; 
v_res_4536_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_oldTraces_4525_, v_data_4526_, v_ref_4527_, v_msg_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec(v___y_4529_);
return v_res_4536_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg(lean_object* v_cls_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_options_4540_; uint8_t v_hasTrace_4541_; 
v_options_4540_ = lean_ctor_get(v___y_4538_, 2);
v_hasTrace_4541_ = lean_ctor_get_uint8(v_options_4540_, sizeof(void*)*1);
if (v_hasTrace_4541_ == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec(v_cls_4537_);
v___x_4542_ = lean_box(v_hasTrace_4541_);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
else
{
lean_object* v_inheritedTraceOptions_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; uint8_t v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v_inheritedTraceOptions_4544_ = lean_ctor_get(v___y_4538_, 13);
v___x_4545_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1___redArg___closed__1));
v___x_4546_ = l_Lean_Name_append(v___x_4545_, v_cls_4537_);
v___x_4547_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4544_, v_options_4540_, v___x_4546_);
lean_dec(v___x_4546_);
v___x_4548_ = lean_box(v___x_4547_);
v___x_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
return v___x_4549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg___boxed(lean_object* v_cls_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_){
_start:
{
lean_object* v_res_4553_; 
v_res_4553_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg(v_cls_4550_, v___y_4551_);
lean_dec_ref(v___y_4551_);
return v_res_4553_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; 
v___x_4560_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg(v_cls_4554_, v___y_4557_);
return v___x_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
lean_object* v_res_4567_; 
v_res_4567_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
return v_res_4567_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(lean_object* v___y_4568_){
_start:
{
lean_object* v___x_4570_; lean_object* v_traceState_4571_; lean_object* v_traces_4572_; lean_object* v___x_4573_; lean_object* v_traceState_4574_; lean_object* v_env_4575_; lean_object* v_nextMacroScope_4576_; lean_object* v_ngen_4577_; lean_object* v_auxDeclNGen_4578_; lean_object* v_cache_4579_; lean_object* v_messages_4580_; lean_object* v_infoState_4581_; lean_object* v_snapshotTasks_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4603_; 
v___x_4570_ = lean_st_ref_get(v___y_4568_);
v_traceState_4571_ = lean_ctor_get(v___x_4570_, 4);
lean_inc_ref(v_traceState_4571_);
lean_dec(v___x_4570_);
v_traces_4572_ = lean_ctor_get(v_traceState_4571_, 0);
lean_inc_ref(v_traces_4572_);
lean_dec_ref(v_traceState_4571_);
v___x_4573_ = lean_st_ref_take(v___y_4568_);
v_traceState_4574_ = lean_ctor_get(v___x_4573_, 4);
v_env_4575_ = lean_ctor_get(v___x_4573_, 0);
v_nextMacroScope_4576_ = lean_ctor_get(v___x_4573_, 1);
v_ngen_4577_ = lean_ctor_get(v___x_4573_, 2);
v_auxDeclNGen_4578_ = lean_ctor_get(v___x_4573_, 3);
v_cache_4579_ = lean_ctor_get(v___x_4573_, 5);
v_messages_4580_ = lean_ctor_get(v___x_4573_, 6);
v_infoState_4581_ = lean_ctor_get(v___x_4573_, 7);
v_snapshotTasks_4582_ = lean_ctor_get(v___x_4573_, 8);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4573_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4584_ = v___x_4573_;
v_isShared_4585_ = v_isSharedCheck_4603_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_snapshotTasks_4582_);
lean_inc(v_infoState_4581_);
lean_inc(v_messages_4580_);
lean_inc(v_cache_4579_);
lean_inc(v_traceState_4574_);
lean_inc(v_auxDeclNGen_4578_);
lean_inc(v_ngen_4577_);
lean_inc(v_nextMacroScope_4576_);
lean_inc(v_env_4575_);
lean_dec(v___x_4573_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4603_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
uint64_t v_tid_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4601_; 
v_tid_4586_ = lean_ctor_get_uint64(v_traceState_4574_, sizeof(void*)*1);
v_isSharedCheck_4601_ = !lean_is_exclusive(v_traceState_4574_);
if (v_isSharedCheck_4601_ == 0)
{
lean_object* v_unused_4602_; 
v_unused_4602_ = lean_ctor_get(v_traceState_4574_, 0);
lean_dec(v_unused_4602_);
v___x_4588_ = v_traceState_4574_;
v_isShared_4589_ = v_isSharedCheck_4601_;
goto v_resetjp_4587_;
}
else
{
lean_dec(v_traceState_4574_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4601_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v___x_4590_ = lean_unsigned_to_nat(32u);
v___x_4591_ = lean_mk_empty_array_with_capacity(v___x_4590_);
lean_dec_ref(v___x_4591_);
v___x_4592_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4592_);
v___x_4594_ = v___x_4588_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4592_);
lean_ctor_set_uint64(v_reuseFailAlloc_4600_, sizeof(void*)*1, v_tid_4586_);
v___x_4594_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4596_; 
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 4, v___x_4594_);
v___x_4596_ = v___x_4584_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_env_4575_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v_nextMacroScope_4576_);
lean_ctor_set(v_reuseFailAlloc_4599_, 2, v_ngen_4577_);
lean_ctor_set(v_reuseFailAlloc_4599_, 3, v_auxDeclNGen_4578_);
lean_ctor_set(v_reuseFailAlloc_4599_, 4, v___x_4594_);
lean_ctor_set(v_reuseFailAlloc_4599_, 5, v_cache_4579_);
lean_ctor_set(v_reuseFailAlloc_4599_, 6, v_messages_4580_);
lean_ctor_set(v_reuseFailAlloc_4599_, 7, v_infoState_4581_);
lean_ctor_set(v_reuseFailAlloc_4599_, 8, v_snapshotTasks_4582_);
v___x_4596_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4595_;
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4597_ = lean_st_ref_set(v___y_4568_, v___x_4596_);
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v_traces_4572_);
return v___x_4598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg___boxed(lean_object* v___y_4604_, lean_object* v___y_4605_){
_start:
{
lean_object* v_res_4606_; 
v_res_4606_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v___y_4604_);
lean_dec(v___y_4604_);
return v_res_4606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_){
_start:
{
lean_object* v___x_4612_; 
v___x_4612_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v___y_4610_);
return v___x_4612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v_res_4618_; 
v_res_4618_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v___y_4613_, v___y_4614_, v___y_4615_, v___y_4616_);
lean_dec(v___y_4616_);
lean_dec_ref(v___y_4615_);
lean_dec(v___y_4614_);
lean_dec_ref(v___y_4613_);
return v_res_4618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4619_, lean_object* v_zetaDeltaFVarIds_4620_, lean_object* v_a_x3f_4621_){
_start:
{
lean_object* v___x_4623_; lean_object* v_mctx_4624_; lean_object* v_cache_4625_; lean_object* v_postponed_4626_; lean_object* v_diag_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4637_; 
v___x_4623_ = lean_st_ref_take(v___y_4619_);
v_mctx_4624_ = lean_ctor_get(v___x_4623_, 0);
v_cache_4625_ = lean_ctor_get(v___x_4623_, 1);
v_postponed_4626_ = lean_ctor_get(v___x_4623_, 3);
v_diag_4627_ = lean_ctor_get(v___x_4623_, 4);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4623_);
if (v_isSharedCheck_4637_ == 0)
{
lean_object* v_unused_4638_; 
v_unused_4638_ = lean_ctor_get(v___x_4623_, 2);
lean_dec(v_unused_4638_);
v___x_4629_ = v___x_4623_;
v_isShared_4630_ = v_isSharedCheck_4637_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_diag_4627_);
lean_inc(v_postponed_4626_);
lean_inc(v_cache_4625_);
lean_inc(v_mctx_4624_);
lean_dec(v___x_4623_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4637_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
lean_object* v___x_4632_; 
if (v_isShared_4630_ == 0)
{
lean_ctor_set(v___x_4629_, 2, v_zetaDeltaFVarIds_4620_);
v___x_4632_ = v___x_4629_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_mctx_4624_);
lean_ctor_set(v_reuseFailAlloc_4636_, 1, v_cache_4625_);
lean_ctor_set(v_reuseFailAlloc_4636_, 2, v_zetaDeltaFVarIds_4620_);
lean_ctor_set(v_reuseFailAlloc_4636_, 3, v_postponed_4626_);
lean_ctor_set(v_reuseFailAlloc_4636_, 4, v_diag_4627_);
v___x_4632_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; lean_object* v___x_4635_; 
v___x_4633_ = lean_st_ref_set(v___y_4619_, v___x_4632_);
v___x_4634_ = lean_box(0);
v___x_4635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4635_, 0, v___x_4634_);
return v___x_4635_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4639_, lean_object* v_zetaDeltaFVarIds_4640_, lean_object* v_a_x3f_4641_, lean_object* v___y_4642_){
_start:
{
lean_object* v_res_4643_; 
v_res_4643_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4639_, v_zetaDeltaFVarIds_4640_, v_a_x3f_4641_);
lean_dec(v_a_x3f_4641_);
lean_dec(v___y_4639_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v_cls_4644_, lean_object* v_msg_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_ref_4651_; lean_object* v___x_4652_; lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4697_; 
v_ref_4651_ = lean_ctor_get(v___y_4648_, 5);
v___x_4652_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
v_isSharedCheck_4697_ = !lean_is_exclusive(v___x_4652_);
if (v_isSharedCheck_4697_ == 0)
{
v___x_4655_ = v___x_4652_;
v_isShared_4656_ = v_isSharedCheck_4697_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4652_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4697_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v_traceState_4658_; lean_object* v_env_4659_; lean_object* v_nextMacroScope_4660_; lean_object* v_ngen_4661_; lean_object* v_auxDeclNGen_4662_; lean_object* v_cache_4663_; lean_object* v_messages_4664_; lean_object* v_infoState_4665_; lean_object* v_snapshotTasks_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4696_; 
v___x_4657_ = lean_st_ref_take(v___y_4649_);
v_traceState_4658_ = lean_ctor_get(v___x_4657_, 4);
v_env_4659_ = lean_ctor_get(v___x_4657_, 0);
v_nextMacroScope_4660_ = lean_ctor_get(v___x_4657_, 1);
v_ngen_4661_ = lean_ctor_get(v___x_4657_, 2);
v_auxDeclNGen_4662_ = lean_ctor_get(v___x_4657_, 3);
v_cache_4663_ = lean_ctor_get(v___x_4657_, 5);
v_messages_4664_ = lean_ctor_get(v___x_4657_, 6);
v_infoState_4665_ = lean_ctor_get(v___x_4657_, 7);
v_snapshotTasks_4666_ = lean_ctor_get(v___x_4657_, 8);
v_isSharedCheck_4696_ = !lean_is_exclusive(v___x_4657_);
if (v_isSharedCheck_4696_ == 0)
{
v___x_4668_ = v___x_4657_;
v_isShared_4669_ = v_isSharedCheck_4696_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_snapshotTasks_4666_);
lean_inc(v_infoState_4665_);
lean_inc(v_messages_4664_);
lean_inc(v_cache_4663_);
lean_inc(v_traceState_4658_);
lean_inc(v_auxDeclNGen_4662_);
lean_inc(v_ngen_4661_);
lean_inc(v_nextMacroScope_4660_);
lean_inc(v_env_4659_);
lean_dec(v___x_4657_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4696_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
uint64_t v_tid_4670_; lean_object* v_traces_4671_; lean_object* v___x_4673_; uint8_t v_isShared_4674_; uint8_t v_isSharedCheck_4695_; 
v_tid_4670_ = lean_ctor_get_uint64(v_traceState_4658_, sizeof(void*)*1);
v_traces_4671_ = lean_ctor_get(v_traceState_4658_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v_traceState_4658_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4673_ = v_traceState_4658_;
v_isShared_4674_ = v_isSharedCheck_4695_;
goto v_resetjp_4672_;
}
else
{
lean_inc(v_traces_4671_);
lean_dec(v_traceState_4658_);
v___x_4673_ = lean_box(0);
v_isShared_4674_ = v_isSharedCheck_4695_;
goto v_resetjp_4672_;
}
v_resetjp_4672_:
{
lean_object* v___x_4675_; double v___x_4676_; uint8_t v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; lean_object* v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4685_; 
v___x_4675_ = lean_box(0);
v___x_4676_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0);
v___x_4677_ = 0;
v___x_4678_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__1));
v___x_4679_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4679_, 0, v_cls_4644_);
lean_ctor_set(v___x_4679_, 1, v___x_4675_);
lean_ctor_set(v___x_4679_, 2, v___x_4678_);
lean_ctor_set_float(v___x_4679_, sizeof(void*)*3, v___x_4676_);
lean_ctor_set_float(v___x_4679_, sizeof(void*)*3 + 8, v___x_4676_);
lean_ctor_set_uint8(v___x_4679_, sizeof(void*)*3 + 16, v___x_4677_);
v___x_4680_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__2));
v___x_4681_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4681_, 0, v___x_4679_);
lean_ctor_set(v___x_4681_, 1, v_a_4653_);
lean_ctor_set(v___x_4681_, 2, v___x_4680_);
lean_inc(v_ref_4651_);
v___x_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4682_, 0, v_ref_4651_);
lean_ctor_set(v___x_4682_, 1, v___x_4681_);
v___x_4683_ = l_Lean_PersistentArray_push___redArg(v_traces_4671_, v___x_4682_);
if (v_isShared_4674_ == 0)
{
lean_ctor_set(v___x_4673_, 0, v___x_4683_);
v___x_4685_ = v___x_4673_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v___x_4683_);
lean_ctor_set_uint64(v_reuseFailAlloc_4694_, sizeof(void*)*1, v_tid_4670_);
v___x_4685_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
lean_object* v___x_4687_; 
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 4, v___x_4685_);
v___x_4687_ = v___x_4668_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_env_4659_);
lean_ctor_set(v_reuseFailAlloc_4693_, 1, v_nextMacroScope_4660_);
lean_ctor_set(v_reuseFailAlloc_4693_, 2, v_ngen_4661_);
lean_ctor_set(v_reuseFailAlloc_4693_, 3, v_auxDeclNGen_4662_);
lean_ctor_set(v_reuseFailAlloc_4693_, 4, v___x_4685_);
lean_ctor_set(v_reuseFailAlloc_4693_, 5, v_cache_4663_);
lean_ctor_set(v_reuseFailAlloc_4693_, 6, v_messages_4664_);
lean_ctor_set(v_reuseFailAlloc_4693_, 7, v_infoState_4665_);
lean_ctor_set(v_reuseFailAlloc_4693_, 8, v_snapshotTasks_4666_);
v___x_4687_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4691_; 
v___x_4688_ = lean_st_ref_set(v___y_4649_, v___x_4687_);
v___x_4689_ = lean_box(0);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v___x_4689_);
v___x_4691_ = v___x_4655_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v___x_4689_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v_cls_4698_, lean_object* v_msg_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_res_4705_; 
v_res_4705_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v_cls_4698_, v_msg_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
lean_dec(v___y_4703_);
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4701_);
lean_dec_ref(v___y_4700_);
return v_res_4705_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4708_ = l_Lean_stringToMessageData(v___x_4707_);
return v___x_4708_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4711_ = l_Lean_stringToMessageData(v___x_4710_);
return v___x_4711_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; 
v___x_4713_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4714_ = l_Lean_stringToMessageData(v___x_4713_);
return v___x_4714_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4716_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4717_ = l_Lean_stringToMessageData(v___x_4716_);
return v___x_4717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4718_, lean_object* v_e_4719_, lean_object* v___x_4720_, lean_object* v___x_4721_, lean_object* v_cls_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_){
_start:
{
lean_object* v___x_4728_; lean_object* v___x_4729_; 
v___x_4728_ = lean_st_mk_ref(v___x_4718_);
v___x_4729_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4719_, v___x_4720_, v___x_4728_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; uint8_t v_isShared_4733_; uint8_t v_isSharedCheck_4793_; 
v_a_4730_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4793_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4793_ == 0)
{
v___x_4732_ = v___x_4729_;
v_isShared_4733_ = v_isSharedCheck_4793_;
goto v_resetjp_4731_;
}
else
{
lean_inc(v_a_4730_);
lean_dec(v___x_4729_);
v___x_4732_ = lean_box(0);
v_isShared_4733_ = v_isSharedCheck_4793_;
goto v_resetjp_4731_;
}
v_resetjp_4731_:
{
lean_object* v___x_4734_; lean_object* v_count_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4791_; 
v___x_4734_ = lean_st_ref_get(v___x_4728_);
lean_dec(v___x_4728_);
v_count_4735_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4791_ == 0)
{
lean_object* v_unused_4792_; 
v_unused_4792_ = lean_ctor_get(v___x_4734_, 1);
lean_dec(v_unused_4792_);
v___x_4737_ = v___x_4734_;
v_isShared_4738_ = v_isSharedCheck_4791_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_count_4735_);
lean_dec(v___x_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4791_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
uint8_t v___x_4761_; 
v___x_4761_ = lean_nat_dec_eq(v_count_4735_, v___x_4721_);
if (v___x_4761_ == 0)
{
lean_object* v___x_4762_; lean_object* v_a_4763_; uint8_t v___x_4764_; 
lean_inc(v_cls_4722_);
v___x_4762_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg(v_cls_4722_, v___y_4725_);
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
lean_inc(v_a_4763_);
lean_dec_ref(v___x_4762_);
v___x_4764_ = lean_unbox(v_a_4763_);
lean_dec(v_a_4763_);
if (v___x_4764_ == 0)
{
lean_dec(v_cls_4722_);
goto v___jp_4739_;
}
else
{
lean_object* v_expr_4765_; lean_object* v___x_4766_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v___x_4769_; 
v_expr_4765_ = lean_ctor_get(v_a_4730_, 0);
v___x_4766_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4765_);
v___x_4767_ = l_Lean_indentExpr(v_expr_4765_);
v___x_4768_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4768_, 0, v___x_4766_);
lean_ctor_set(v___x_4768_, 1, v___x_4767_);
v___x_4769_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v_cls_4722_, v___x_4768_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_dec_ref(v___x_4769_);
goto v___jp_4739_;
}
else
{
lean_object* v_a_4770_; lean_object* v___x_4772_; uint8_t v_isShared_4773_; uint8_t v_isSharedCheck_4777_; 
lean_del_object(v___x_4737_);
lean_dec(v_count_4735_);
lean_del_object(v___x_4732_);
lean_dec(v_a_4730_);
v_a_4770_ = lean_ctor_get(v___x_4769_, 0);
v_isSharedCheck_4777_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4777_ == 0)
{
v___x_4772_ = v___x_4769_;
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
else
{
lean_inc(v_a_4770_);
lean_dec(v___x_4769_);
v___x_4772_ = lean_box(0);
v_isShared_4773_ = v_isSharedCheck_4777_;
goto v_resetjp_4771_;
}
v_resetjp_4771_:
{
lean_object* v___x_4775_; 
if (v_isShared_4773_ == 0)
{
v___x_4775_ = v___x_4772_;
goto v_reusejp_4774_;
}
else
{
lean_object* v_reuseFailAlloc_4776_; 
v_reuseFailAlloc_4776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4776_, 0, v_a_4770_);
v___x_4775_ = v_reuseFailAlloc_4776_;
goto v_reusejp_4774_;
}
v_reusejp_4774_:
{
return v___x_4775_;
}
}
}
}
}
else
{
lean_object* v___x_4778_; lean_object* v_a_4779_; uint8_t v___x_4780_; 
lean_inc(v_cls_4722_);
v___x_4778_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg(v_cls_4722_, v___y_4725_);
v_a_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc(v_a_4779_);
lean_dec_ref(v___x_4778_);
v___x_4780_ = lean_unbox(v_a_4779_);
lean_dec(v_a_4779_);
if (v___x_4780_ == 0)
{
lean_dec(v_cls_4722_);
goto v___jp_4739_;
}
else
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4782_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v_cls_4722_, v___x_4781_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
if (lean_obj_tag(v___x_4782_) == 0)
{
lean_dec_ref(v___x_4782_);
goto v___jp_4739_;
}
else
{
lean_object* v_a_4783_; lean_object* v___x_4785_; uint8_t v_isShared_4786_; uint8_t v_isSharedCheck_4790_; 
lean_del_object(v___x_4737_);
lean_dec(v_count_4735_);
lean_del_object(v___x_4732_);
lean_dec(v_a_4730_);
v_a_4783_ = lean_ctor_get(v___x_4782_, 0);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4790_ == 0)
{
v___x_4785_ = v___x_4782_;
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
else
{
lean_inc(v_a_4783_);
lean_dec(v___x_4782_);
v___x_4785_ = lean_box(0);
v_isShared_4786_ = v_isSharedCheck_4790_;
goto v_resetjp_4784_;
}
v_resetjp_4784_:
{
lean_object* v___x_4788_; 
if (v_isShared_4786_ == 0)
{
v___x_4788_ = v___x_4785_;
goto v_reusejp_4787_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v_a_4783_);
v___x_4788_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4787_;
}
v_reusejp_4787_:
{
return v___x_4788_;
}
}
}
}
}
v___jp_4739_:
{
lean_object* v_expr_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4759_; 
v_expr_4740_ = lean_ctor_get(v_a_4730_, 0);
v_isSharedCheck_4759_ = !lean_is_exclusive(v_a_4730_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; 
v_unused_4760_ = lean_ctor_get(v_a_4730_, 1);
lean_dec(v_unused_4760_);
v___x_4742_ = v_a_4730_;
v_isShared_4743_ = v_isSharedCheck_4759_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_expr_4740_);
lean_dec(v_a_4730_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4759_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v___x_4744_; lean_object* v___x_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4749_; 
v___x_4744_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4745_ = l_Nat_reprFast(v_count_4735_);
v___x_4746_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4746_, 0, v___x_4745_);
v___x_4747_ = l_Lean_MessageData_ofFormat(v___x_4746_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set_tag(v___x_4742_, 7);
lean_ctor_set(v___x_4742_, 1, v___x_4747_);
lean_ctor_set(v___x_4742_, 0, v___x_4744_);
v___x_4749_ = v___x_4742_;
goto v_reusejp_4748_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v___x_4744_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v___x_4747_);
v___x_4749_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4748_;
}
v_reusejp_4748_:
{
lean_object* v___x_4750_; lean_object* v___x_4752_; 
v___x_4750_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4738_ == 0)
{
lean_ctor_set_tag(v___x_4737_, 7);
lean_ctor_set(v___x_4737_, 1, v___x_4750_);
lean_ctor_set(v___x_4737_, 0, v___x_4749_);
v___x_4752_ = v___x_4737_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v___x_4749_);
lean_ctor_set(v_reuseFailAlloc_4757_, 1, v___x_4750_);
v___x_4752_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
lean_object* v___x_4753_; lean_object* v___x_4755_; 
v___x_4753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4753_, 0, v_expr_4740_);
lean_ctor_set(v___x_4753_, 1, v___x_4752_);
if (v_isShared_4733_ == 0)
{
lean_ctor_set(v___x_4732_, 0, v___x_4753_);
v___x_4755_ = v___x_4732_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4756_; 
v_reuseFailAlloc_4756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4753_);
v___x_4755_ = v_reuseFailAlloc_4756_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
return v___x_4755_;
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
lean_object* v_a_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4801_; 
lean_dec(v___x_4728_);
lean_dec(v_cls_4722_);
v_a_4794_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4801_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4801_ == 0)
{
v___x_4796_ = v___x_4729_;
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_a_4794_);
lean_dec(v___x_4729_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4801_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
lean_object* v___x_4799_; 
if (v_isShared_4797_ == 0)
{
v___x_4799_ = v___x_4796_;
goto v_reusejp_4798_;
}
else
{
lean_object* v_reuseFailAlloc_4800_; 
v_reuseFailAlloc_4800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4800_, 0, v_a_4794_);
v___x_4799_ = v_reuseFailAlloc_4800_;
goto v_reusejp_4798_;
}
v_reusejp_4798_:
{
return v___x_4799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4802_, lean_object* v_e_4803_, lean_object* v___x_4804_, lean_object* v___x_4805_, lean_object* v_cls_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4802_, v_e_4803_, v___x_4804_, v___x_4805_, v_cls_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec(v___x_4805_);
lean_dec(v___x_4804_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4813_, lean_object* v_cache_4814_, lean_object* v_a_x3f_4815_){
_start:
{
lean_object* v___x_4817_; lean_object* v_mctx_4818_; lean_object* v_zetaDeltaFVarIds_4819_; lean_object* v_postponed_4820_; lean_object* v_diag_4821_; lean_object* v___x_4823_; uint8_t v_isShared_4824_; uint8_t v_isSharedCheck_4831_; 
v___x_4817_ = lean_st_ref_take(v___y_4813_);
v_mctx_4818_ = lean_ctor_get(v___x_4817_, 0);
v_zetaDeltaFVarIds_4819_ = lean_ctor_get(v___x_4817_, 2);
v_postponed_4820_ = lean_ctor_get(v___x_4817_, 3);
v_diag_4821_ = lean_ctor_get(v___x_4817_, 4);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4817_);
if (v_isSharedCheck_4831_ == 0)
{
lean_object* v_unused_4832_; 
v_unused_4832_ = lean_ctor_get(v___x_4817_, 1);
lean_dec(v_unused_4832_);
v___x_4823_ = v___x_4817_;
v_isShared_4824_ = v_isSharedCheck_4831_;
goto v_resetjp_4822_;
}
else
{
lean_inc(v_diag_4821_);
lean_inc(v_postponed_4820_);
lean_inc(v_zetaDeltaFVarIds_4819_);
lean_inc(v_mctx_4818_);
lean_dec(v___x_4817_);
v___x_4823_ = lean_box(0);
v_isShared_4824_ = v_isSharedCheck_4831_;
goto v_resetjp_4822_;
}
v_resetjp_4822_:
{
lean_object* v___x_4826_; 
if (v_isShared_4824_ == 0)
{
lean_ctor_set(v___x_4823_, 1, v_cache_4814_);
v___x_4826_ = v___x_4823_;
goto v_reusejp_4825_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_mctx_4818_);
lean_ctor_set(v_reuseFailAlloc_4830_, 1, v_cache_4814_);
lean_ctor_set(v_reuseFailAlloc_4830_, 2, v_zetaDeltaFVarIds_4819_);
lean_ctor_set(v_reuseFailAlloc_4830_, 3, v_postponed_4820_);
lean_ctor_set(v_reuseFailAlloc_4830_, 4, v_diag_4821_);
v___x_4826_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4825_;
}
v_reusejp_4825_:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; 
v___x_4827_ = lean_st_ref_set(v___y_4813_, v___x_4826_);
v___x_4828_ = lean_box(0);
v___x_4829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4828_);
return v___x_4829_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4833_, lean_object* v_cache_4834_, lean_object* v_a_x3f_4835_, lean_object* v___y_4836_){
_start:
{
lean_object* v_res_4837_; 
v_res_4837_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4833_, v_cache_4834_, v_a_x3f_4835_);
lean_dec(v_a_x3f_4835_);
lean_dec(v___y_4833_);
return v_res_4837_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4841_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1));
v___x_4842_ = l_Lean_MessageData_ofFormat(v___x_4841_);
return v___x_4842_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4843_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3);
v___x_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
return v___x_4845_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4);
v___x_4847_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
lean_ctor_set(v___x_4847_, 1, v___x_4846_);
lean_ctor_set(v___x_4847_, 2, v___x_4846_);
lean_ctor_set(v___x_4847_, 3, v___x_4846_);
lean_ctor_set(v___x_4847_, 4, v___x_4846_);
lean_ctor_set(v___x_4847_, 5, v___x_4846_);
return v___x_4847_;
}
}
static uint64_t _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6(void){
_start:
{
uint8_t v___x_4848_; uint64_t v___x_4849_; 
v___x_4848_ = 0;
v___x_4849_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4848_);
return v___x_4849_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7(void){
_start:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4850_ = lean_obj_once(&l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1, &l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1_once, _init_l___private_Init_While_0__Lean_Loop_forIn_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___closed__1);
v___x_4851_ = lean_unsigned_to_nat(0u);
v___x_4852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
lean_ctor_set(v___x_4852_, 1, v___x_4850_);
return v___x_4852_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_4853_, lean_object* v_e_4854_, uint8_t v___x_4855_, lean_object* v_cls_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_){
_start:
{
if (v___x_4853_ == 0)
{
lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
lean_dec(v_cls_4856_);
v___x_4862_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2);
v___x_4863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4863_, 0, v_e_4854_);
lean_ctor_set(v___x_4863_, 1, v___x_4862_);
v___x_4864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4863_);
return v___x_4864_;
}
else
{
lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v_mctx_4867_; lean_object* v_zetaDeltaFVarIds_4868_; lean_object* v_postponed_4869_; lean_object* v_diag_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_5062_; 
v___x_4865_ = lean_st_ref_get(v___y_4858_);
v___x_4866_ = lean_st_ref_take(v___y_4858_);
v_mctx_4867_ = lean_ctor_get(v___x_4866_, 0);
v_zetaDeltaFVarIds_4868_ = lean_ctor_get(v___x_4866_, 2);
v_postponed_4869_ = lean_ctor_get(v___x_4866_, 3);
v_diag_4870_ = lean_ctor_get(v___x_4866_, 4);
v_isSharedCheck_5062_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_5062_ == 0)
{
lean_object* v_unused_5063_; 
v_unused_5063_ = lean_ctor_get(v___x_4866_, 1);
lean_dec(v_unused_5063_);
v___x_4872_ = v___x_4866_;
v_isShared_4873_ = v_isSharedCheck_5062_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_diag_4870_);
lean_inc(v_postponed_4869_);
lean_inc(v_zetaDeltaFVarIds_4868_);
lean_inc(v_mctx_4867_);
lean_dec(v___x_4866_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_5062_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4874_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 1, v___x_4874_);
v___x_4876_ = v___x_4872_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_5061_; 
v_reuseFailAlloc_5061_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5061_, 0, v_mctx_4867_);
lean_ctor_set(v_reuseFailAlloc_5061_, 1, v___x_4874_);
lean_ctor_set(v_reuseFailAlloc_5061_, 2, v_zetaDeltaFVarIds_4868_);
lean_ctor_set(v_reuseFailAlloc_5061_, 3, v_postponed_4869_);
lean_ctor_set(v_reuseFailAlloc_5061_, 4, v_diag_4870_);
v___x_4876_ = v_reuseFailAlloc_5061_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v_mctx_4879_; lean_object* v_cache_4880_; lean_object* v_zetaDeltaFVarIds_4881_; lean_object* v_postponed_4882_; lean_object* v_diag_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_5060_; 
v___x_4877_ = lean_st_ref_set(v___y_4858_, v___x_4876_);
v___x_4878_ = lean_st_ref_take(v___y_4858_);
v_mctx_4879_ = lean_ctor_get(v___x_4878_, 0);
v_cache_4880_ = lean_ctor_get(v___x_4878_, 1);
v_zetaDeltaFVarIds_4881_ = lean_ctor_get(v___x_4878_, 2);
v_postponed_4882_ = lean_ctor_get(v___x_4878_, 3);
v_diag_4883_ = lean_ctor_get(v___x_4878_, 4);
v_isSharedCheck_5060_ = !lean_is_exclusive(v___x_4878_);
if (v_isSharedCheck_5060_ == 0)
{
v___x_4885_ = v___x_4878_;
v_isShared_4886_ = v_isSharedCheck_5060_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_diag_4883_);
lean_inc(v_postponed_4882_);
lean_inc(v_zetaDeltaFVarIds_4881_);
lean_inc(v_cache_4880_);
lean_inc(v_mctx_4879_);
lean_dec(v___x_4878_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_5060_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4887_ = lean_box(1);
if (v_isShared_4886_ == 0)
{
lean_ctor_set(v___x_4885_, 2, v___x_4887_);
v___x_4889_ = v___x_4885_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_5059_; 
v_reuseFailAlloc_5059_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5059_, 0, v_mctx_4879_);
lean_ctor_set(v_reuseFailAlloc_5059_, 1, v_cache_4880_);
lean_ctor_set(v_reuseFailAlloc_5059_, 2, v___x_4887_);
lean_ctor_set(v_reuseFailAlloc_5059_, 3, v_postponed_4882_);
lean_ctor_set(v_reuseFailAlloc_5059_, 4, v_diag_4883_);
v___x_4889_ = v_reuseFailAlloc_5059_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
lean_object* v___x_4890_; lean_object* v_cache_4891_; lean_object* v_keyedConfig_4892_; lean_object* v_zetaDeltaSet_4893_; lean_object* v_lctx_4894_; lean_object* v_localInstances_4895_; lean_object* v_defEqCtx_x3f_4896_; lean_object* v_synthPendingDepth_4897_; lean_object* v_canUnfold_x3f_4898_; uint8_t v_univApprox_4899_; uint8_t v_inTypeClassResolution_4900_; uint8_t v_cacheInferType_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; uint8_t v_foApprox_4904_; uint8_t v_ctxApprox_4905_; uint8_t v_quasiPatternApprox_4906_; uint8_t v_constApprox_4907_; uint8_t v_isDefEqStuckEx_4908_; uint8_t v_unificationHints_4909_; uint8_t v_proofIrrelevance_4910_; uint8_t v_assignSyntheticOpaque_4911_; uint8_t v_offsetCnstrs_4912_; uint8_t v_etaStruct_4913_; uint8_t v_univApprox_4914_; uint8_t v_iota_4915_; uint8_t v_beta_4916_; uint8_t v_proj_4917_; uint8_t v_zeta_4918_; uint8_t v_zetaDelta_4919_; uint8_t v_zetaUnused_4920_; uint8_t v_zetaHave_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_5058_; 
v___x_4890_ = lean_st_ref_set(v___y_4858_, v___x_4889_);
v_cache_4891_ = lean_ctor_get(v___x_4865_, 1);
lean_inc_ref(v_cache_4891_);
lean_dec(v___x_4865_);
v_keyedConfig_4892_ = lean_ctor_get(v___y_4857_, 0);
v_zetaDeltaSet_4893_ = lean_ctor_get(v___y_4857_, 1);
v_lctx_4894_ = lean_ctor_get(v___y_4857_, 2);
v_localInstances_4895_ = lean_ctor_get(v___y_4857_, 3);
v_defEqCtx_x3f_4896_ = lean_ctor_get(v___y_4857_, 4);
v_synthPendingDepth_4897_ = lean_ctor_get(v___y_4857_, 5);
v_canUnfold_x3f_4898_ = lean_ctor_get(v___y_4857_, 6);
v_univApprox_4899_ = lean_ctor_get_uint8(v___y_4857_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4900_ = lean_ctor_get_uint8(v___y_4857_, sizeof(void*)*7 + 2);
v_cacheInferType_4901_ = lean_ctor_get_uint8(v___y_4857_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_4898_);
lean_inc(v_synthPendingDepth_4897_);
lean_inc(v_defEqCtx_x3f_4896_);
lean_inc_ref(v_localInstances_4895_);
lean_inc_ref(v_lctx_4894_);
lean_inc(v_zetaDeltaSet_4893_);
lean_inc_ref(v_keyedConfig_4892_);
v___x_4902_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4902_, 0, v_keyedConfig_4892_);
lean_ctor_set(v___x_4902_, 1, v_zetaDeltaSet_4893_);
lean_ctor_set(v___x_4902_, 2, v_lctx_4894_);
lean_ctor_set(v___x_4902_, 3, v_localInstances_4895_);
lean_ctor_set(v___x_4902_, 4, v_defEqCtx_x3f_4896_);
lean_ctor_set(v___x_4902_, 5, v_synthPendingDepth_4897_);
lean_ctor_set(v___x_4902_, 6, v_canUnfold_x3f_4898_);
lean_ctor_set_uint8(v___x_4902_, sizeof(void*)*7, v___x_4855_);
lean_ctor_set_uint8(v___x_4902_, sizeof(void*)*7 + 1, v_univApprox_4899_);
lean_ctor_set_uint8(v___x_4902_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4900_);
lean_ctor_set_uint8(v___x_4902_, sizeof(void*)*7 + 3, v_cacheInferType_4901_);
v___x_4903_ = l_Lean_Meta_Context_config(v___x_4902_);
v_foApprox_4904_ = lean_ctor_get_uint8(v___x_4903_, 0);
v_ctxApprox_4905_ = lean_ctor_get_uint8(v___x_4903_, 1);
v_quasiPatternApprox_4906_ = lean_ctor_get_uint8(v___x_4903_, 2);
v_constApprox_4907_ = lean_ctor_get_uint8(v___x_4903_, 3);
v_isDefEqStuckEx_4908_ = lean_ctor_get_uint8(v___x_4903_, 4);
v_unificationHints_4909_ = lean_ctor_get_uint8(v___x_4903_, 5);
v_proofIrrelevance_4910_ = lean_ctor_get_uint8(v___x_4903_, 6);
v_assignSyntheticOpaque_4911_ = lean_ctor_get_uint8(v___x_4903_, 7);
v_offsetCnstrs_4912_ = lean_ctor_get_uint8(v___x_4903_, 8);
v_etaStruct_4913_ = lean_ctor_get_uint8(v___x_4903_, 10);
v_univApprox_4914_ = lean_ctor_get_uint8(v___x_4903_, 11);
v_iota_4915_ = lean_ctor_get_uint8(v___x_4903_, 12);
v_beta_4916_ = lean_ctor_get_uint8(v___x_4903_, 13);
v_proj_4917_ = lean_ctor_get_uint8(v___x_4903_, 14);
v_zeta_4918_ = lean_ctor_get_uint8(v___x_4903_, 15);
v_zetaDelta_4919_ = lean_ctor_get_uint8(v___x_4903_, 16);
v_zetaUnused_4920_ = lean_ctor_get_uint8(v___x_4903_, 17);
v_zetaHave_4921_ = lean_ctor_get_uint8(v___x_4903_, 18);
v_isSharedCheck_5058_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_5058_ == 0)
{
v___x_4923_ = v___x_4903_;
v_isShared_4924_ = v_isSharedCheck_5058_;
goto v_resetjp_4922_;
}
else
{
lean_dec(v___x_4903_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_5058_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
uint8_t v___x_4925_; lean_object* v_config_4927_; 
v___x_4925_ = 0;
if (v_isShared_4924_ == 0)
{
v_config_4927_ = v___x_4923_;
goto v_reusejp_4926_;
}
else
{
lean_object* v_reuseFailAlloc_5057_; 
v_reuseFailAlloc_5057_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 0, v_foApprox_4904_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 1, v_ctxApprox_4905_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 2, v_quasiPatternApprox_4906_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 3, v_constApprox_4907_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 4, v_isDefEqStuckEx_4908_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 5, v_unificationHints_4909_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 6, v_proofIrrelevance_4910_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 7, v_assignSyntheticOpaque_4911_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 8, v_offsetCnstrs_4912_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 10, v_etaStruct_4913_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 11, v_univApprox_4914_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 12, v_iota_4915_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 13, v_beta_4916_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 14, v_proj_4917_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 15, v_zeta_4918_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 16, v_zetaDelta_4919_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 17, v_zetaUnused_4920_);
lean_ctor_set_uint8(v_reuseFailAlloc_5057_, 18, v_zetaHave_4921_);
v_config_4927_ = v_reuseFailAlloc_5057_;
goto v_reusejp_4926_;
}
v_reusejp_4926_:
{
uint64_t v___x_4928_; uint64_t v___x_4929_; uint64_t v___x_4930_; uint64_t v___x_4931_; uint64_t v___x_4932_; uint64_t v_key_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; uint8_t v_transparency_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v_a_4942_; lean_object* v_a_4954_; lean_object* v___y_4958_; lean_object* v___y_4979_; uint8_t v___y_5007_; uint8_t v___x_5055_; uint8_t v___x_5056_; 
lean_ctor_set_uint8(v_config_4927_, 9, v___x_4925_);
v___x_4928_ = l_Lean_Meta_Context_configKey(v___x_4902_);
lean_dec_ref(v___x_4902_);
v___x_4929_ = 2ULL;
v___x_4930_ = lean_uint64_shift_right(v___x_4928_, v___x_4929_);
v___x_4931_ = lean_uint64_shift_left(v___x_4930_, v___x_4929_);
v___x_4932_ = lean_uint64_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6);
v_key_4933_ = lean_uint64_lor(v___x_4931_, v___x_4932_);
v___x_4934_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4934_, 0, v_config_4927_);
lean_ctor_set_uint64(v___x_4934_, sizeof(void*)*1, v_key_4933_);
lean_inc(v_canUnfold_x3f_4898_);
lean_inc(v_synthPendingDepth_4897_);
lean_inc(v_defEqCtx_x3f_4896_);
lean_inc_ref(v_localInstances_4895_);
lean_inc_ref(v_lctx_4894_);
lean_inc(v_zetaDeltaSet_4893_);
v___x_4935_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
lean_ctor_set(v___x_4935_, 1, v_zetaDeltaSet_4893_);
lean_ctor_set(v___x_4935_, 2, v_lctx_4894_);
lean_ctor_set(v___x_4935_, 3, v_localInstances_4895_);
lean_ctor_set(v___x_4935_, 4, v_defEqCtx_x3f_4896_);
lean_ctor_set(v___x_4935_, 5, v_synthPendingDepth_4897_);
lean_ctor_set(v___x_4935_, 6, v_canUnfold_x3f_4898_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7, v___x_4855_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7 + 1, v_univApprox_4899_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4900_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7 + 3, v_cacheInferType_4901_);
v___x_4936_ = l_Lean_Meta_Context_config(v___x_4935_);
v_transparency_4937_ = lean_ctor_get_uint8(v___x_4936_, 9);
v___x_4938_ = lean_unsigned_to_nat(0u);
v___x_4939_ = lean_box(0);
v___x_4940_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7);
v___x_5055_ = 1;
v___x_5056_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4937_, v___x_5055_);
if (v___x_5056_ == 0)
{
v___y_5007_ = v_transparency_4937_;
goto v___jp_5006_;
}
else
{
v___y_5007_ = v___x_5055_;
goto v___jp_5006_;
}
v___jp_4941_:
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4951_; 
v___x_4943_ = lean_box(0);
v___x_4944_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4858_, v_cache_4891_, v___x_4943_);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4944_);
if (v_isSharedCheck_4951_ == 0)
{
lean_object* v_unused_4952_; 
v_unused_4952_ = lean_ctor_get(v___x_4944_, 0);
lean_dec(v_unused_4952_);
v___x_4946_ = v___x_4944_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_dec(v___x_4944_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4949_; 
if (v_isShared_4947_ == 0)
{
lean_ctor_set_tag(v___x_4946_, 1);
lean_ctor_set(v___x_4946_, 0, v_a_4942_);
v___x_4949_ = v___x_4946_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4942_);
v___x_4949_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
return v___x_4949_;
}
}
}
v___jp_4953_:
{
lean_object* v___x_4955_; lean_object* v___x_4956_; 
v___x_4955_ = lean_box(0);
v___x_4956_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4858_, v_zetaDeltaFVarIds_4881_, v___x_4955_);
lean_dec_ref(v___x_4956_);
v_a_4942_ = v_a_4954_;
goto v___jp_4941_;
}
v___jp_4957_:
{
if (lean_obj_tag(v___y_4958_) == 0)
{
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4976_; 
v_a_4959_ = lean_ctor_get(v___y_4958_, 0);
v_isSharedCheck_4976_ = !lean_is_exclusive(v___y_4958_);
if (v_isSharedCheck_4976_ == 0)
{
v___x_4961_ = v___y_4958_;
v_isShared_4962_ = v_isSharedCheck_4976_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___y_4958_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4976_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
lean_inc(v_a_4959_);
if (v_isShared_4962_ == 0)
{
lean_ctor_set_tag(v___x_4961_, 1);
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4973_; 
v___x_4965_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4858_, v_zetaDeltaFVarIds_4881_, v___x_4964_);
lean_dec_ref(v___x_4965_);
v___x_4966_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4858_, v_cache_4891_, v___x_4964_);
lean_dec_ref(v___x_4964_);
v_isSharedCheck_4973_ = !lean_is_exclusive(v___x_4966_);
if (v_isSharedCheck_4973_ == 0)
{
lean_object* v_unused_4974_; 
v_unused_4974_ = lean_ctor_get(v___x_4966_, 0);
lean_dec(v_unused_4974_);
v___x_4968_ = v___x_4966_;
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
else
{
lean_dec(v___x_4966_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4973_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4971_; 
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 0, v_a_4959_);
v___x_4971_ = v___x_4968_;
goto v_reusejp_4970_;
}
else
{
lean_object* v_reuseFailAlloc_4972_; 
v_reuseFailAlloc_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4972_, 0, v_a_4959_);
v___x_4971_ = v_reuseFailAlloc_4972_;
goto v_reusejp_4970_;
}
v_reusejp_4970_:
{
return v___x_4971_;
}
}
}
}
}
else
{
lean_object* v_a_4977_; 
v_a_4977_ = lean_ctor_get(v___y_4958_, 0);
lean_inc(v_a_4977_);
lean_dec_ref(v___y_4958_);
v_a_4954_ = v_a_4977_;
goto v___jp_4953_;
}
}
v___jp_4978_:
{
lean_object* v___x_4980_; uint8_t v_foApprox_4981_; uint8_t v_ctxApprox_4982_; uint8_t v_quasiPatternApprox_4983_; uint8_t v_constApprox_4984_; uint8_t v_isDefEqStuckEx_4985_; uint8_t v_unificationHints_4986_; uint8_t v_proofIrrelevance_4987_; uint8_t v_assignSyntheticOpaque_4988_; uint8_t v_offsetCnstrs_4989_; uint8_t v_transparency_4990_; uint8_t v_univApprox_4991_; uint8_t v_zetaUnused_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5005_; 
v___x_4980_ = l_Lean_Meta_Context_config(v___y_4979_);
lean_dec_ref(v___y_4979_);
v_foApprox_4981_ = lean_ctor_get_uint8(v___x_4980_, 0);
v_ctxApprox_4982_ = lean_ctor_get_uint8(v___x_4980_, 1);
v_quasiPatternApprox_4983_ = lean_ctor_get_uint8(v___x_4980_, 2);
v_constApprox_4984_ = lean_ctor_get_uint8(v___x_4980_, 3);
v_isDefEqStuckEx_4985_ = lean_ctor_get_uint8(v___x_4980_, 4);
v_unificationHints_4986_ = lean_ctor_get_uint8(v___x_4980_, 5);
v_proofIrrelevance_4987_ = lean_ctor_get_uint8(v___x_4980_, 6);
v_assignSyntheticOpaque_4988_ = lean_ctor_get_uint8(v___x_4980_, 7);
v_offsetCnstrs_4989_ = lean_ctor_get_uint8(v___x_4980_, 8);
v_transparency_4990_ = lean_ctor_get_uint8(v___x_4980_, 9);
v_univApprox_4991_ = lean_ctor_get_uint8(v___x_4980_, 11);
v_zetaUnused_4992_ = lean_ctor_get_uint8(v___x_4980_, 17);
v_isSharedCheck_5005_ = !lean_is_exclusive(v___x_4980_);
if (v_isSharedCheck_5005_ == 0)
{
v___x_4994_ = v___x_4980_;
v_isShared_4995_ = v_isSharedCheck_5005_;
goto v_resetjp_4993_;
}
else
{
lean_dec(v___x_4980_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5005_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
uint8_t v___x_4996_; uint8_t v___x_4997_; lean_object* v___x_4999_; 
v___x_4996_ = 0;
v___x_4997_ = 2;
if (v_isShared_4995_ == 0)
{
v___x_4999_ = v___x_4994_;
goto v_reusejp_4998_;
}
else
{
lean_object* v_reuseFailAlloc_5004_; 
v_reuseFailAlloc_5004_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 0, v_foApprox_4981_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 1, v_ctxApprox_4982_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 2, v_quasiPatternApprox_4983_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 3, v_constApprox_4984_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 4, v_isDefEqStuckEx_4985_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 5, v_unificationHints_4986_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 6, v_proofIrrelevance_4987_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 7, v_assignSyntheticOpaque_4988_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 8, v_offsetCnstrs_4989_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 9, v_transparency_4990_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 11, v_univApprox_4991_);
lean_ctor_set_uint8(v_reuseFailAlloc_5004_, 17, v_zetaUnused_4992_);
v___x_4999_ = v_reuseFailAlloc_5004_;
goto v_reusejp_4998_;
}
v_reusejp_4998_:
{
uint64_t v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; 
lean_ctor_set_uint8(v___x_4999_, 10, v___x_4996_);
lean_ctor_set_uint8(v___x_4999_, 12, v___x_4855_);
lean_ctor_set_uint8(v___x_4999_, 13, v___x_4855_);
lean_ctor_set_uint8(v___x_4999_, 14, v___x_4997_);
lean_ctor_set_uint8(v___x_4999_, 15, v___x_4855_);
lean_ctor_set_uint8(v___x_4999_, 16, v___x_4855_);
lean_ctor_set_uint8(v___x_4999_, 18, v___x_4855_);
v___x_5000_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4999_);
v___x_5001_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5001_, 0, v___x_4999_);
lean_ctor_set_uint64(v___x_5001_, sizeof(void*)*1, v___x_5000_);
lean_inc(v_canUnfold_x3f_4898_);
lean_inc(v_synthPendingDepth_4897_);
lean_inc(v_defEqCtx_x3f_4896_);
lean_inc_ref(v_localInstances_4895_);
lean_inc_ref(v_lctx_4894_);
lean_inc(v_zetaDeltaSet_4893_);
v___x_5002_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5002_, 0, v___x_5001_);
lean_ctor_set(v___x_5002_, 1, v_zetaDeltaSet_4893_);
lean_ctor_set(v___x_5002_, 2, v_lctx_4894_);
lean_ctor_set(v___x_5002_, 3, v_localInstances_4895_);
lean_ctor_set(v___x_5002_, 4, v_defEqCtx_x3f_4896_);
lean_ctor_set(v___x_5002_, 5, v_synthPendingDepth_4897_);
lean_ctor_set(v___x_5002_, 6, v_canUnfold_x3f_4898_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7, v___x_4855_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7 + 1, v_univApprox_4899_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4900_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7 + 3, v_cacheInferType_4901_);
v___x_5003_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4940_, v_e_4854_, v___x_4939_, v___x_4938_, v_cls_4856_, v___x_5002_, v___y_4858_, v___y_4859_, v___y_4860_);
lean_dec_ref(v___x_5002_);
v___y_4958_ = v___x_5003_;
goto v___jp_4957_;
}
}
}
v___jp_5006_:
{
uint8_t v_foApprox_5008_; uint8_t v_ctxApprox_5009_; uint8_t v_quasiPatternApprox_5010_; uint8_t v_constApprox_5011_; uint8_t v_isDefEqStuckEx_5012_; uint8_t v_unificationHints_5013_; uint8_t v_proofIrrelevance_5014_; uint8_t v_assignSyntheticOpaque_5015_; uint8_t v_offsetCnstrs_5016_; uint8_t v_etaStruct_5017_; uint8_t v_univApprox_5018_; uint8_t v_iota_5019_; uint8_t v_beta_5020_; uint8_t v_proj_5021_; uint8_t v_zeta_5022_; uint8_t v_zetaDelta_5023_; uint8_t v_zetaUnused_5024_; uint8_t v_zetaHave_5025_; lean_object* v___x_5027_; uint8_t v_isShared_5028_; uint8_t v_isSharedCheck_5054_; 
v_foApprox_5008_ = lean_ctor_get_uint8(v___x_4936_, 0);
v_ctxApprox_5009_ = lean_ctor_get_uint8(v___x_4936_, 1);
v_quasiPatternApprox_5010_ = lean_ctor_get_uint8(v___x_4936_, 2);
v_constApprox_5011_ = lean_ctor_get_uint8(v___x_4936_, 3);
v_isDefEqStuckEx_5012_ = lean_ctor_get_uint8(v___x_4936_, 4);
v_unificationHints_5013_ = lean_ctor_get_uint8(v___x_4936_, 5);
v_proofIrrelevance_5014_ = lean_ctor_get_uint8(v___x_4936_, 6);
v_assignSyntheticOpaque_5015_ = lean_ctor_get_uint8(v___x_4936_, 7);
v_offsetCnstrs_5016_ = lean_ctor_get_uint8(v___x_4936_, 8);
v_etaStruct_5017_ = lean_ctor_get_uint8(v___x_4936_, 10);
v_univApprox_5018_ = lean_ctor_get_uint8(v___x_4936_, 11);
v_iota_5019_ = lean_ctor_get_uint8(v___x_4936_, 12);
v_beta_5020_ = lean_ctor_get_uint8(v___x_4936_, 13);
v_proj_5021_ = lean_ctor_get_uint8(v___x_4936_, 14);
v_zeta_5022_ = lean_ctor_get_uint8(v___x_4936_, 15);
v_zetaDelta_5023_ = lean_ctor_get_uint8(v___x_4936_, 16);
v_zetaUnused_5024_ = lean_ctor_get_uint8(v___x_4936_, 17);
v_zetaHave_5025_ = lean_ctor_get_uint8(v___x_4936_, 18);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5027_ = v___x_4936_;
v_isShared_5028_ = v_isSharedCheck_5054_;
goto v_resetjp_5026_;
}
else
{
lean_dec(v___x_4936_);
v___x_5027_ = lean_box(0);
v_isShared_5028_ = v_isSharedCheck_5054_;
goto v_resetjp_5026_;
}
v_resetjp_5026_:
{
lean_object* v_config_5030_; 
if (v_isShared_5028_ == 0)
{
v_config_5030_ = v___x_5027_;
goto v_reusejp_5029_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 0, v_foApprox_5008_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 1, v_ctxApprox_5009_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 2, v_quasiPatternApprox_5010_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 3, v_constApprox_5011_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 4, v_isDefEqStuckEx_5012_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 5, v_unificationHints_5013_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 6, v_proofIrrelevance_5014_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 7, v_assignSyntheticOpaque_5015_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 8, v_offsetCnstrs_5016_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 10, v_etaStruct_5017_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 11, v_univApprox_5018_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 12, v_iota_5019_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 13, v_beta_5020_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 14, v_proj_5021_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 15, v_zeta_5022_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 16, v_zetaDelta_5023_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 17, v_zetaUnused_5024_);
lean_ctor_set_uint8(v_reuseFailAlloc_5053_, 18, v_zetaHave_5025_);
v_config_5030_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5029_;
}
v_reusejp_5029_:
{
uint64_t v___x_5031_; uint64_t v___x_5032_; uint64_t v___x_5033_; uint64_t v___x_5034_; uint64_t v_key_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
lean_ctor_set_uint8(v_config_5030_, 9, v___y_5007_);
v___x_5031_ = l_Lean_Meta_Context_configKey(v___x_4935_);
lean_dec_ref(v___x_4935_);
v___x_5032_ = lean_uint64_shift_right(v___x_5031_, v___x_4929_);
v___x_5033_ = lean_uint64_shift_left(v___x_5032_, v___x_4929_);
v___x_5034_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_5007_);
v_key_5035_ = lean_uint64_lor(v___x_5033_, v___x_5034_);
v___x_5036_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5036_, 0, v_config_5030_);
lean_ctor_set_uint64(v___x_5036_, sizeof(void*)*1, v_key_5035_);
lean_inc(v_canUnfold_x3f_4898_);
lean_inc(v_synthPendingDepth_4897_);
lean_inc(v_defEqCtx_x3f_4896_);
lean_inc_ref(v_localInstances_4895_);
lean_inc_ref(v_lctx_4894_);
lean_inc(v_zetaDeltaSet_4893_);
v___x_5037_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5037_, 0, v___x_5036_);
lean_ctor_set(v___x_5037_, 1, v_zetaDeltaSet_4893_);
lean_ctor_set(v___x_5037_, 2, v_lctx_4894_);
lean_ctor_set(v___x_5037_, 3, v_localInstances_4895_);
lean_ctor_set(v___x_5037_, 4, v_defEqCtx_x3f_4896_);
lean_ctor_set(v___x_5037_, 5, v_synthPendingDepth_4897_);
lean_ctor_set(v___x_5037_, 6, v_canUnfold_x3f_4898_);
lean_ctor_set_uint8(v___x_5037_, sizeof(void*)*7, v___x_4855_);
lean_ctor_set_uint8(v___x_5037_, sizeof(void*)*7 + 1, v_univApprox_4899_);
lean_ctor_set_uint8(v___x_5037_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4900_);
lean_ctor_set_uint8(v___x_5037_, sizeof(void*)*7 + 3, v_cacheInferType_4901_);
v___x_5038_ = l_Lean_Meta_getConfig___redArg(v___x_5037_);
if (lean_obj_tag(v___x_5038_) == 0)
{
lean_object* v_a_5039_; uint8_t v_beta_5040_; 
v_a_5039_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5039_);
lean_dec_ref(v___x_5038_);
v_beta_5040_ = lean_ctor_get_uint8(v_a_5039_, 13);
if (v_beta_5040_ == 0)
{
lean_dec(v_a_5039_);
v___y_4979_ = v___x_5037_;
goto v___jp_4978_;
}
else
{
uint8_t v_iota_5041_; 
v_iota_5041_ = lean_ctor_get_uint8(v_a_5039_, 12);
if (v_iota_5041_ == 0)
{
lean_dec(v_a_5039_);
v___y_4979_ = v___x_5037_;
goto v___jp_4978_;
}
else
{
uint8_t v_zeta_5042_; 
v_zeta_5042_ = lean_ctor_get_uint8(v_a_5039_, 15);
if (v_zeta_5042_ == 0)
{
lean_dec(v_a_5039_);
v___y_4979_ = v___x_5037_;
goto v___jp_4978_;
}
else
{
uint8_t v_zetaHave_5043_; 
v_zetaHave_5043_ = lean_ctor_get_uint8(v_a_5039_, 18);
if (v_zetaHave_5043_ == 0)
{
lean_dec(v_a_5039_);
v___y_4979_ = v___x_5037_;
goto v___jp_4978_;
}
else
{
uint8_t v_zetaDelta_5044_; 
v_zetaDelta_5044_ = lean_ctor_get_uint8(v_a_5039_, 16);
if (v_zetaDelta_5044_ == 0)
{
lean_dec(v_a_5039_);
v___y_4979_ = v___x_5037_;
goto v___jp_4978_;
}
else
{
uint8_t v_etaStruct_5045_; uint8_t v_proj_5046_; uint8_t v___x_5047_; uint8_t v___x_5048_; 
v_etaStruct_5045_ = lean_ctor_get_uint8(v_a_5039_, 10);
v_proj_5046_ = lean_ctor_get_uint8(v_a_5039_, 14);
lean_dec(v_a_5039_);
v___x_5047_ = 2;
v___x_5048_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_5046_, v___x_5047_);
if (v___x_5048_ == 0)
{
v___y_4979_ = v___x_5037_;
goto v___jp_4978_;
}
else
{
uint8_t v___x_5049_; uint8_t v___x_5050_; 
v___x_5049_ = 0;
v___x_5050_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_5045_, v___x_5049_);
if (v___x_5050_ == 0)
{
v___y_4979_ = v___x_5037_;
goto v___jp_4978_;
}
else
{
lean_object* v___x_5051_; 
v___x_5051_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4940_, v_e_4854_, v___x_4939_, v___x_4938_, v_cls_4856_, v___x_5037_, v___y_4858_, v___y_4859_, v___y_4860_);
lean_dec_ref(v___x_5037_);
v___y_4958_ = v___x_5051_;
goto v___jp_4957_;
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
lean_object* v_a_5052_; 
lean_dec_ref(v___x_5037_);
lean_dec(v_cls_4856_);
lean_dec_ref(v_e_4854_);
v_a_5052_ = lean_ctor_get(v___x_5038_, 0);
lean_inc(v_a_5052_);
lean_dec_ref(v___x_5038_);
v_a_4954_ = v_a_5052_;
goto v___jp_4953_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_5064_, lean_object* v_e_5065_, lean_object* v___x_5066_, lean_object* v_cls_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_){
_start:
{
uint8_t v___x_12908__boxed_5073_; uint8_t v___x_12909__boxed_5074_; lean_object* v_res_5075_; 
v___x_12908__boxed_5073_ = lean_unbox(v___x_5064_);
v___x_12909__boxed_5074_ = lean_unbox(v___x_5066_);
v_res_5075_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_12908__boxed_5073_, v_e_5065_, v___x_12909__boxed_5074_, v_cls_5067_, v___y_5068_, v___y_5069_, v___y_5070_, v___y_5071_);
lean_dec(v___y_5071_);
lean_dec_ref(v___y_5070_);
lean_dec(v___y_5069_);
lean_dec_ref(v___y_5068_);
return v_res_5075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5076_, lean_object* v___y_5077_, lean_object* v___y_5078_, lean_object* v___y_5079_, lean_object* v___y_5080_){
_start:
{
if (lean_obj_tag(v_x_5076_) == 0)
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5090_; 
v_a_5082_ = lean_ctor_get(v_x_5076_, 0);
v_isSharedCheck_5090_ = !lean_is_exclusive(v_x_5076_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5084_ = v_x_5076_;
v_isShared_5085_ = v_isSharedCheck_5090_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v_x_5076_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5090_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5086_; lean_object* v___x_5088_; 
v___x_5086_ = l_Lean_Exception_toMessageData(v_a_5082_);
if (v_isShared_5085_ == 0)
{
lean_ctor_set(v___x_5084_, 0, v___x_5086_);
v___x_5088_ = v___x_5084_;
goto v_reusejp_5087_;
}
else
{
lean_object* v_reuseFailAlloc_5089_; 
v_reuseFailAlloc_5089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5089_, 0, v___x_5086_);
v___x_5088_ = v_reuseFailAlloc_5089_;
goto v_reusejp_5087_;
}
v_reusejp_5087_:
{
return v___x_5088_;
}
}
}
else
{
lean_object* v_a_5091_; lean_object* v___x_5093_; uint8_t v_isShared_5094_; uint8_t v_isSharedCheck_5099_; 
v_a_5091_ = lean_ctor_get(v_x_5076_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v_x_5076_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5093_ = v_x_5076_;
v_isShared_5094_ = v_isSharedCheck_5099_;
goto v_resetjp_5092_;
}
else
{
lean_inc(v_a_5091_);
lean_dec(v_x_5076_);
v___x_5093_ = lean_box(0);
v_isShared_5094_ = v_isSharedCheck_5099_;
goto v_resetjp_5092_;
}
v_resetjp_5092_:
{
lean_object* v_snd_5095_; lean_object* v___x_5097_; 
v_snd_5095_ = lean_ctor_get(v_a_5091_, 1);
lean_inc(v_snd_5095_);
lean_dec(v_a_5091_);
if (v_isShared_5094_ == 0)
{
lean_ctor_set_tag(v___x_5093_, 0);
lean_ctor_set(v___x_5093_, 0, v_snd_5095_);
v___x_5097_ = v___x_5093_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5098_; 
v_reuseFailAlloc_5098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5098_, 0, v_snd_5095_);
v___x_5097_ = v_reuseFailAlloc_5098_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
return v___x_5097_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5100_, lean_object* v___y_5101_, lean_object* v___y_5102_, lean_object* v___y_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_){
_start:
{
lean_object* v_res_5106_; 
v_res_5106_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5100_, v___y_5101_, v___y_5102_, v___y_5103_, v___y_5104_);
lean_dec(v___y_5104_);
lean_dec_ref(v___y_5103_);
lean_dec(v___y_5102_);
lean_dec_ref(v___y_5101_);
return v_res_5106_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(lean_object* v_oldTraces_5107_, lean_object* v_data_5108_, lean_object* v_ref_5109_, lean_object* v_msg_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_){
_start:
{
lean_object* v_fileName_5116_; lean_object* v_fileMap_5117_; lean_object* v_options_5118_; lean_object* v_currRecDepth_5119_; lean_object* v_maxRecDepth_5120_; lean_object* v_ref_5121_; lean_object* v_currNamespace_5122_; lean_object* v_openDecls_5123_; lean_object* v_initHeartbeats_5124_; lean_object* v_maxHeartbeats_5125_; lean_object* v_quotContext_5126_; lean_object* v_currMacroScope_5127_; uint8_t v_diag_5128_; lean_object* v_cancelTk_x3f_5129_; uint8_t v_suppressElabErrors_5130_; lean_object* v_inheritedTraceOptions_5131_; lean_object* v___x_5132_; lean_object* v_traceState_5133_; lean_object* v_traces_5134_; lean_object* v_ref_5135_; lean_object* v___x_5136_; lean_object* v___x_5137_; size_t v_sz_5138_; size_t v___x_5139_; lean_object* v___x_5140_; lean_object* v_msg_5141_; lean_object* v___x_5142_; lean_object* v_a_5143_; lean_object* v___x_5145_; uint8_t v_isShared_5146_; uint8_t v_isSharedCheck_5180_; 
v_fileName_5116_ = lean_ctor_get(v___y_5113_, 0);
v_fileMap_5117_ = lean_ctor_get(v___y_5113_, 1);
v_options_5118_ = lean_ctor_get(v___y_5113_, 2);
v_currRecDepth_5119_ = lean_ctor_get(v___y_5113_, 3);
v_maxRecDepth_5120_ = lean_ctor_get(v___y_5113_, 4);
v_ref_5121_ = lean_ctor_get(v___y_5113_, 5);
v_currNamespace_5122_ = lean_ctor_get(v___y_5113_, 6);
v_openDecls_5123_ = lean_ctor_get(v___y_5113_, 7);
v_initHeartbeats_5124_ = lean_ctor_get(v___y_5113_, 8);
v_maxHeartbeats_5125_ = lean_ctor_get(v___y_5113_, 9);
v_quotContext_5126_ = lean_ctor_get(v___y_5113_, 10);
v_currMacroScope_5127_ = lean_ctor_get(v___y_5113_, 11);
v_diag_5128_ = lean_ctor_get_uint8(v___y_5113_, sizeof(void*)*14);
v_cancelTk_x3f_5129_ = lean_ctor_get(v___y_5113_, 12);
v_suppressElabErrors_5130_ = lean_ctor_get_uint8(v___y_5113_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5131_ = lean_ctor_get(v___y_5113_, 13);
v___x_5132_ = lean_st_ref_get(v___y_5114_);
v_traceState_5133_ = lean_ctor_get(v___x_5132_, 4);
lean_inc_ref(v_traceState_5133_);
lean_dec(v___x_5132_);
v_traces_5134_ = lean_ctor_get(v_traceState_5133_, 0);
lean_inc_ref(v_traces_5134_);
lean_dec_ref(v_traceState_5133_);
v_ref_5135_ = l_Lean_replaceRef(v_ref_5109_, v_ref_5121_);
lean_inc_ref(v_inheritedTraceOptions_5131_);
lean_inc(v_cancelTk_x3f_5129_);
lean_inc(v_currMacroScope_5127_);
lean_inc(v_quotContext_5126_);
lean_inc(v_maxHeartbeats_5125_);
lean_inc(v_initHeartbeats_5124_);
lean_inc(v_openDecls_5123_);
lean_inc(v_currNamespace_5122_);
lean_inc(v_maxRecDepth_5120_);
lean_inc(v_currRecDepth_5119_);
lean_inc_ref(v_options_5118_);
lean_inc_ref(v_fileMap_5117_);
lean_inc_ref(v_fileName_5116_);
v___x_5136_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5136_, 0, v_fileName_5116_);
lean_ctor_set(v___x_5136_, 1, v_fileMap_5117_);
lean_ctor_set(v___x_5136_, 2, v_options_5118_);
lean_ctor_set(v___x_5136_, 3, v_currRecDepth_5119_);
lean_ctor_set(v___x_5136_, 4, v_maxRecDepth_5120_);
lean_ctor_set(v___x_5136_, 5, v_ref_5135_);
lean_ctor_set(v___x_5136_, 6, v_currNamespace_5122_);
lean_ctor_set(v___x_5136_, 7, v_openDecls_5123_);
lean_ctor_set(v___x_5136_, 8, v_initHeartbeats_5124_);
lean_ctor_set(v___x_5136_, 9, v_maxHeartbeats_5125_);
lean_ctor_set(v___x_5136_, 10, v_quotContext_5126_);
lean_ctor_set(v___x_5136_, 11, v_currMacroScope_5127_);
lean_ctor_set(v___x_5136_, 12, v_cancelTk_x3f_5129_);
lean_ctor_set(v___x_5136_, 13, v_inheritedTraceOptions_5131_);
lean_ctor_set_uint8(v___x_5136_, sizeof(void*)*14, v_diag_5128_);
lean_ctor_set_uint8(v___x_5136_, sizeof(void*)*14 + 1, v_suppressElabErrors_5130_);
v___x_5137_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5134_);
lean_dec_ref(v_traces_5134_);
v_sz_5138_ = lean_array_size(v___x_5137_);
v___x_5139_ = ((size_t)0ULL);
v___x_5140_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14_spec__16(v_sz_5138_, v___x_5139_, v___x_5137_);
v_msg_5141_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5141_, 0, v_data_5108_);
lean_ctor_set(v_msg_5141_, 1, v_msg_5110_);
lean_ctor_set(v_msg_5141_, 2, v___x_5140_);
v___x_5142_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5141_, v___y_5111_, v___y_5112_, v___x_5136_, v___y_5114_);
lean_dec_ref(v___x_5136_);
v_a_5143_ = lean_ctor_get(v___x_5142_, 0);
v_isSharedCheck_5180_ = !lean_is_exclusive(v___x_5142_);
if (v_isSharedCheck_5180_ == 0)
{
v___x_5145_ = v___x_5142_;
v_isShared_5146_ = v_isSharedCheck_5180_;
goto v_resetjp_5144_;
}
else
{
lean_inc(v_a_5143_);
lean_dec(v___x_5142_);
v___x_5145_ = lean_box(0);
v_isShared_5146_ = v_isSharedCheck_5180_;
goto v_resetjp_5144_;
}
v_resetjp_5144_:
{
lean_object* v___x_5147_; lean_object* v_traceState_5148_; lean_object* v_env_5149_; lean_object* v_nextMacroScope_5150_; lean_object* v_ngen_5151_; lean_object* v_auxDeclNGen_5152_; lean_object* v_cache_5153_; lean_object* v_messages_5154_; lean_object* v_infoState_5155_; lean_object* v_snapshotTasks_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5179_; 
v___x_5147_ = lean_st_ref_take(v___y_5114_);
v_traceState_5148_ = lean_ctor_get(v___x_5147_, 4);
v_env_5149_ = lean_ctor_get(v___x_5147_, 0);
v_nextMacroScope_5150_ = lean_ctor_get(v___x_5147_, 1);
v_ngen_5151_ = lean_ctor_get(v___x_5147_, 2);
v_auxDeclNGen_5152_ = lean_ctor_get(v___x_5147_, 3);
v_cache_5153_ = lean_ctor_get(v___x_5147_, 5);
v_messages_5154_ = lean_ctor_get(v___x_5147_, 6);
v_infoState_5155_ = lean_ctor_get(v___x_5147_, 7);
v_snapshotTasks_5156_ = lean_ctor_get(v___x_5147_, 8);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5147_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5158_ = v___x_5147_;
v_isShared_5159_ = v_isSharedCheck_5179_;
goto v_resetjp_5157_;
}
else
{
lean_inc(v_snapshotTasks_5156_);
lean_inc(v_infoState_5155_);
lean_inc(v_messages_5154_);
lean_inc(v_cache_5153_);
lean_inc(v_traceState_5148_);
lean_inc(v_auxDeclNGen_5152_);
lean_inc(v_ngen_5151_);
lean_inc(v_nextMacroScope_5150_);
lean_inc(v_env_5149_);
lean_dec(v___x_5147_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5179_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
uint64_t v_tid_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5177_; 
v_tid_5160_ = lean_ctor_get_uint64(v_traceState_5148_, sizeof(void*)*1);
v_isSharedCheck_5177_ = !lean_is_exclusive(v_traceState_5148_);
if (v_isSharedCheck_5177_ == 0)
{
lean_object* v_unused_5178_; 
v_unused_5178_ = lean_ctor_get(v_traceState_5148_, 0);
lean_dec(v_unused_5178_);
v___x_5162_ = v_traceState_5148_;
v_isShared_5163_ = v_isSharedCheck_5177_;
goto v_resetjp_5161_;
}
else
{
lean_dec(v_traceState_5148_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5177_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5167_; 
v___x_5164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5164_, 0, v_ref_5109_);
lean_ctor_set(v___x_5164_, 1, v_a_5143_);
v___x_5165_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5107_, v___x_5164_);
if (v_isShared_5163_ == 0)
{
lean_ctor_set(v___x_5162_, 0, v___x_5165_);
v___x_5167_ = v___x_5162_;
goto v_reusejp_5166_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v___x_5165_);
lean_ctor_set_uint64(v_reuseFailAlloc_5176_, sizeof(void*)*1, v_tid_5160_);
v___x_5167_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5166_;
}
v_reusejp_5166_:
{
lean_object* v___x_5169_; 
if (v_isShared_5159_ == 0)
{
lean_ctor_set(v___x_5158_, 4, v___x_5167_);
v___x_5169_ = v___x_5158_;
goto v_reusejp_5168_;
}
else
{
lean_object* v_reuseFailAlloc_5175_; 
v_reuseFailAlloc_5175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5175_, 0, v_env_5149_);
lean_ctor_set(v_reuseFailAlloc_5175_, 1, v_nextMacroScope_5150_);
lean_ctor_set(v_reuseFailAlloc_5175_, 2, v_ngen_5151_);
lean_ctor_set(v_reuseFailAlloc_5175_, 3, v_auxDeclNGen_5152_);
lean_ctor_set(v_reuseFailAlloc_5175_, 4, v___x_5167_);
lean_ctor_set(v_reuseFailAlloc_5175_, 5, v_cache_5153_);
lean_ctor_set(v_reuseFailAlloc_5175_, 6, v_messages_5154_);
lean_ctor_set(v_reuseFailAlloc_5175_, 7, v_infoState_5155_);
lean_ctor_set(v_reuseFailAlloc_5175_, 8, v_snapshotTasks_5156_);
v___x_5169_ = v_reuseFailAlloc_5175_;
goto v_reusejp_5168_;
}
v_reusejp_5168_:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v___x_5173_; 
v___x_5170_ = lean_st_ref_set(v___y_5114_, v___x_5169_);
v___x_5171_ = lean_box(0);
if (v_isShared_5146_ == 0)
{
lean_ctor_set(v___x_5145_, 0, v___x_5171_);
v___x_5173_ = v___x_5145_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4___boxed(lean_object* v_oldTraces_5181_, lean_object* v_data_5182_, lean_object* v_ref_5183_, lean_object* v_msg_5184_, lean_object* v___y_5185_, lean_object* v___y_5186_, lean_object* v___y_5187_, lean_object* v___y_5188_, lean_object* v___y_5189_){
_start:
{
lean_object* v_res_5190_; 
v_res_5190_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(v_oldTraces_5181_, v_data_5182_, v_ref_5183_, v_msg_5184_, v___y_5185_, v___y_5186_, v___y_5187_, v___y_5188_);
lean_dec(v___y_5188_);
lean_dec_ref(v___y_5187_);
lean_dec(v___y_5186_);
lean_dec_ref(v___y_5185_);
return v_res_5190_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__3(lean_object* v_e_5191_){
_start:
{
if (lean_obj_tag(v_e_5191_) == 0)
{
uint8_t v___x_5192_; 
v___x_5192_ = 2;
return v___x_5192_;
}
else
{
uint8_t v___x_5193_; 
v___x_5193_ = 0;
return v___x_5193_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__3___boxed(lean_object* v_e_5194_){
_start:
{
uint8_t v_res_5195_; lean_object* v_r_5196_; 
v_res_5195_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__3(v_e_5194_);
lean_dec_ref(v_e_5194_);
v_r_5196_ = lean_box(v_res_5195_);
return v_r_5196_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(lean_object* v_x_5197_){
_start:
{
if (lean_obj_tag(v_x_5197_) == 0)
{
lean_object* v_a_5199_; lean_object* v___x_5201_; uint8_t v_isShared_5202_; uint8_t v_isSharedCheck_5206_; 
v_a_5199_ = lean_ctor_get(v_x_5197_, 0);
v_isSharedCheck_5206_ = !lean_is_exclusive(v_x_5197_);
if (v_isSharedCheck_5206_ == 0)
{
v___x_5201_ = v_x_5197_;
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
else
{
lean_inc(v_a_5199_);
lean_dec(v_x_5197_);
v___x_5201_ = lean_box(0);
v_isShared_5202_ = v_isSharedCheck_5206_;
goto v_resetjp_5200_;
}
v_resetjp_5200_:
{
lean_object* v___x_5204_; 
if (v_isShared_5202_ == 0)
{
lean_ctor_set_tag(v___x_5201_, 1);
v___x_5204_ = v___x_5201_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_a_5199_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
}
else
{
lean_object* v_a_5207_; lean_object* v___x_5209_; uint8_t v_isShared_5210_; uint8_t v_isSharedCheck_5214_; 
v_a_5207_ = lean_ctor_get(v_x_5197_, 0);
v_isSharedCheck_5214_ = !lean_is_exclusive(v_x_5197_);
if (v_isSharedCheck_5214_ == 0)
{
v___x_5209_ = v_x_5197_;
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
else
{
lean_inc(v_a_5207_);
lean_dec(v_x_5197_);
v___x_5209_ = lean_box(0);
v_isShared_5210_ = v_isSharedCheck_5214_;
goto v_resetjp_5208_;
}
v_resetjp_5208_:
{
lean_object* v___x_5212_; 
if (v_isShared_5210_ == 0)
{
lean_ctor_set_tag(v___x_5209_, 0);
v___x_5212_ = v___x_5209_;
goto v_reusejp_5211_;
}
else
{
lean_object* v_reuseFailAlloc_5213_; 
v_reuseFailAlloc_5213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5213_, 0, v_a_5207_);
v___x_5212_ = v_reuseFailAlloc_5213_;
goto v_reusejp_5211_;
}
v_reusejp_5211_:
{
return v___x_5212_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg___boxed(lean_object* v_x_5215_, lean_object* v___y_5216_){
_start:
{
lean_object* v_res_5217_; 
v_res_5217_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_x_5215_);
return v_res_5217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(lean_object* v_cls_5218_, uint8_t v_collapsed_5219_, lean_object* v_tag_5220_, lean_object* v_opts_5221_, uint8_t v_clsEnabled_5222_, lean_object* v_oldTraces_5223_, lean_object* v_msg_5224_, lean_object* v_resStartStop_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_, lean_object* v___y_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_fst_5231_; lean_object* v_snd_5232_; lean_object* v___x_5234_; uint8_t v_isShared_5235_; uint8_t v_isSharedCheck_5330_; 
v_fst_5231_ = lean_ctor_get(v_resStartStop_5225_, 0);
v_snd_5232_ = lean_ctor_get(v_resStartStop_5225_, 1);
v_isSharedCheck_5330_ = !lean_is_exclusive(v_resStartStop_5225_);
if (v_isSharedCheck_5330_ == 0)
{
v___x_5234_ = v_resStartStop_5225_;
v_isShared_5235_ = v_isSharedCheck_5330_;
goto v_resetjp_5233_;
}
else
{
lean_inc(v_snd_5232_);
lean_inc(v_fst_5231_);
lean_dec(v_resStartStop_5225_);
v___x_5234_ = lean_box(0);
v_isShared_5235_ = v_isSharedCheck_5330_;
goto v_resetjp_5233_;
}
v_resetjp_5233_:
{
lean_object* v___y_5237_; lean_object* v___y_5238_; lean_object* v_data_5239_; lean_object* v_fst_5250_; lean_object* v_snd_5251_; lean_object* v___x_5253_; uint8_t v_isShared_5254_; uint8_t v_isSharedCheck_5329_; 
v_fst_5250_ = lean_ctor_get(v_snd_5232_, 0);
v_snd_5251_ = lean_ctor_get(v_snd_5232_, 1);
v_isSharedCheck_5329_ = !lean_is_exclusive(v_snd_5232_);
if (v_isSharedCheck_5329_ == 0)
{
v___x_5253_ = v_snd_5232_;
v_isShared_5254_ = v_isSharedCheck_5329_;
goto v_resetjp_5252_;
}
else
{
lean_inc(v_snd_5251_);
lean_inc(v_fst_5250_);
lean_dec(v_snd_5232_);
v___x_5253_ = lean_box(0);
v_isShared_5254_ = v_isSharedCheck_5329_;
goto v_resetjp_5252_;
}
v___jp_5236_:
{
lean_object* v___x_5240_; 
lean_inc(v___y_5237_);
v___x_5240_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__4(v_oldTraces_5223_, v_data_5239_, v___y_5237_, v___y_5238_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_);
if (lean_obj_tag(v___x_5240_) == 0)
{
lean_object* v___x_5241_; 
lean_dec_ref(v___x_5240_);
v___x_5241_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_fst_5231_);
return v___x_5241_;
}
else
{
lean_object* v_a_5242_; lean_object* v___x_5244_; uint8_t v_isShared_5245_; uint8_t v_isSharedCheck_5249_; 
lean_dec(v_fst_5231_);
v_a_5242_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5249_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5244_ = v___x_5240_;
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
else
{
lean_inc(v_a_5242_);
lean_dec(v___x_5240_);
v___x_5244_ = lean_box(0);
v_isShared_5245_ = v_isSharedCheck_5249_;
goto v_resetjp_5243_;
}
v_resetjp_5243_:
{
lean_object* v___x_5247_; 
if (v_isShared_5245_ == 0)
{
v___x_5247_ = v___x_5244_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5248_; 
v_reuseFailAlloc_5248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5248_, 0, v_a_5242_);
v___x_5247_ = v_reuseFailAlloc_5248_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
return v___x_5247_;
}
}
}
}
v_resetjp_5252_:
{
lean_object* v___x_5255_; uint8_t v___x_5256_; lean_object* v___y_5258_; lean_object* v_a_5259_; uint8_t v___y_5283_; double v___y_5314_; 
v___x_5255_ = l_Lean_trace_profiler;
v___x_5256_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5221_, v___x_5255_);
if (v___x_5256_ == 0)
{
v___y_5283_ = v___x_5256_;
goto v___jp_5282_;
}
else
{
lean_object* v___x_5319_; uint8_t v___x_5320_; 
v___x_5319_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5320_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5221_, v___x_5319_);
if (v___x_5320_ == 0)
{
lean_object* v___x_5321_; lean_object* v___x_5322_; double v___x_5323_; double v___x_5324_; double v___x_5325_; 
v___x_5321_ = l_Lean_trace_profiler_threshold;
v___x_5322_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5221_, v___x_5321_);
v___x_5323_ = lean_float_of_nat(v___x_5322_);
v___x_5324_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__4);
v___x_5325_ = lean_float_div(v___x_5323_, v___x_5324_);
v___y_5314_ = v___x_5325_;
goto v___jp_5313_;
}
else
{
lean_object* v___x_5326_; lean_object* v___x_5327_; double v___x_5328_; 
v___x_5326_ = l_Lean_trace_profiler_threshold;
v___x_5327_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5221_, v___x_5326_);
v___x_5328_ = lean_float_of_nat(v___x_5327_);
v___y_5314_ = v___x_5328_;
goto v___jp_5313_;
}
}
v___jp_5257_:
{
uint8_t v_result_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v___x_5265_; 
v_result_5260_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__3(v_fst_5231_);
v___x_5261_ = l_Lean_TraceResult_toEmoji(v_result_5260_);
v___x_5262_ = l_Lean_stringToMessageData(v___x_5261_);
v___x_5263_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
if (v_isShared_5254_ == 0)
{
lean_ctor_set_tag(v___x_5253_, 7);
lean_ctor_set(v___x_5253_, 1, v___x_5263_);
lean_ctor_set(v___x_5253_, 0, v___x_5262_);
v___x_5265_ = v___x_5253_;
goto v_reusejp_5264_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v___x_5262_);
lean_ctor_set(v_reuseFailAlloc_5276_, 1, v___x_5263_);
v___x_5265_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5264_;
}
v_reusejp_5264_:
{
lean_object* v_m_5267_; 
if (v_isShared_5235_ == 0)
{
lean_ctor_set_tag(v___x_5234_, 7);
lean_ctor_set(v___x_5234_, 1, v_a_5259_);
lean_ctor_set(v___x_5234_, 0, v___x_5265_);
v_m_5267_ = v___x_5234_;
goto v_reusejp_5266_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5265_);
lean_ctor_set(v_reuseFailAlloc_5275_, 1, v_a_5259_);
v_m_5267_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5266_;
}
v_reusejp_5266_:
{
lean_object* v___x_5268_; lean_object* v___x_5269_; double v___x_5270_; lean_object* v_data_5271_; 
v___x_5268_ = lean_box(v_result_5260_);
v___x_5269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5269_, 0, v___x_5268_);
v___x_5270_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__0);
lean_inc_ref(v_tag_5220_);
lean_inc_ref(v___x_5269_);
lean_inc(v_cls_5218_);
v_data_5271_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5271_, 0, v_cls_5218_);
lean_ctor_set(v_data_5271_, 1, v___x_5269_);
lean_ctor_set(v_data_5271_, 2, v_tag_5220_);
lean_ctor_set_float(v_data_5271_, sizeof(void*)*3, v___x_5270_);
lean_ctor_set_float(v_data_5271_, sizeof(void*)*3 + 8, v___x_5270_);
lean_ctor_set_uint8(v_data_5271_, sizeof(void*)*3 + 16, v_collapsed_5219_);
if (v___x_5256_ == 0)
{
lean_dec_ref(v___x_5269_);
lean_dec(v_snd_5251_);
lean_dec(v_fst_5250_);
lean_dec_ref(v_tag_5220_);
lean_dec(v_cls_5218_);
v___y_5237_ = v___y_5258_;
v___y_5238_ = v_m_5267_;
v_data_5239_ = v_data_5271_;
goto v___jp_5236_;
}
else
{
lean_object* v_data_5272_; double v___x_5273_; double v___x_5274_; 
lean_dec_ref(v_data_5271_);
v_data_5272_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5272_, 0, v_cls_5218_);
lean_ctor_set(v_data_5272_, 1, v___x_5269_);
lean_ctor_set(v_data_5272_, 2, v_tag_5220_);
v___x_5273_ = lean_unbox_float(v_fst_5250_);
lean_dec(v_fst_5250_);
lean_ctor_set_float(v_data_5272_, sizeof(void*)*3, v___x_5273_);
v___x_5274_ = lean_unbox_float(v_snd_5251_);
lean_dec(v_snd_5251_);
lean_ctor_set_float(v_data_5272_, sizeof(void*)*3 + 8, v___x_5274_);
lean_ctor_set_uint8(v_data_5272_, sizeof(void*)*3 + 16, v_collapsed_5219_);
v___y_5237_ = v___y_5258_;
v___y_5238_ = v_m_5267_;
v_data_5239_ = v_data_5272_;
goto v___jp_5236_;
}
}
}
}
v___jp_5277_:
{
lean_object* v_ref_5278_; lean_object* v___x_5279_; 
v_ref_5278_ = lean_ctor_get(v___y_5228_, 5);
lean_inc(v___y_5229_);
lean_inc_ref(v___y_5228_);
lean_inc(v___y_5227_);
lean_inc_ref(v___y_5226_);
lean_inc(v_fst_5231_);
v___x_5279_ = lean_apply_6(v_msg_5224_, v_fst_5231_, v___y_5226_, v___y_5227_, v___y_5228_, v___y_5229_, lean_box(0));
if (lean_obj_tag(v___x_5279_) == 0)
{
lean_object* v_a_5280_; 
v_a_5280_ = lean_ctor_get(v___x_5279_, 0);
lean_inc(v_a_5280_);
lean_dec_ref(v___x_5279_);
v___y_5258_ = v_ref_5278_;
v_a_5259_ = v_a_5280_;
goto v___jp_5257_;
}
else
{
lean_object* v___x_5281_; 
lean_dec_ref(v___x_5279_);
v___x_5281_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__3);
v___y_5258_ = v_ref_5278_;
v_a_5259_ = v___x_5281_;
goto v___jp_5257_;
}
}
v___jp_5282_:
{
if (v_clsEnabled_5222_ == 0)
{
if (v___y_5283_ == 0)
{
lean_object* v___x_5284_; lean_object* v_traceState_5285_; lean_object* v_env_5286_; lean_object* v_nextMacroScope_5287_; lean_object* v_ngen_5288_; lean_object* v_auxDeclNGen_5289_; lean_object* v_cache_5290_; lean_object* v_messages_5291_; lean_object* v_infoState_5292_; lean_object* v_snapshotTasks_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5312_; 
lean_del_object(v___x_5253_);
lean_dec(v_snd_5251_);
lean_dec(v_fst_5250_);
lean_del_object(v___x_5234_);
lean_dec_ref(v_msg_5224_);
lean_dec_ref(v_tag_5220_);
lean_dec(v_cls_5218_);
v___x_5284_ = lean_st_ref_take(v___y_5229_);
v_traceState_5285_ = lean_ctor_get(v___x_5284_, 4);
v_env_5286_ = lean_ctor_get(v___x_5284_, 0);
v_nextMacroScope_5287_ = lean_ctor_get(v___x_5284_, 1);
v_ngen_5288_ = lean_ctor_get(v___x_5284_, 2);
v_auxDeclNGen_5289_ = lean_ctor_get(v___x_5284_, 3);
v_cache_5290_ = lean_ctor_get(v___x_5284_, 5);
v_messages_5291_ = lean_ctor_get(v___x_5284_, 6);
v_infoState_5292_ = lean_ctor_get(v___x_5284_, 7);
v_snapshotTasks_5293_ = lean_ctor_get(v___x_5284_, 8);
v_isSharedCheck_5312_ = !lean_is_exclusive(v___x_5284_);
if (v_isSharedCheck_5312_ == 0)
{
v___x_5295_ = v___x_5284_;
v_isShared_5296_ = v_isSharedCheck_5312_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_snapshotTasks_5293_);
lean_inc(v_infoState_5292_);
lean_inc(v_messages_5291_);
lean_inc(v_cache_5290_);
lean_inc(v_traceState_5285_);
lean_inc(v_auxDeclNGen_5289_);
lean_inc(v_ngen_5288_);
lean_inc(v_nextMacroScope_5287_);
lean_inc(v_env_5286_);
lean_dec(v___x_5284_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5312_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
uint64_t v_tid_5297_; lean_object* v_traces_5298_; lean_object* v___x_5300_; uint8_t v_isShared_5301_; uint8_t v_isSharedCheck_5311_; 
v_tid_5297_ = lean_ctor_get_uint64(v_traceState_5285_, sizeof(void*)*1);
v_traces_5298_ = lean_ctor_get(v_traceState_5285_, 0);
v_isSharedCheck_5311_ = !lean_is_exclusive(v_traceState_5285_);
if (v_isSharedCheck_5311_ == 0)
{
v___x_5300_ = v_traceState_5285_;
v_isShared_5301_ = v_isSharedCheck_5311_;
goto v_resetjp_5299_;
}
else
{
lean_inc(v_traces_5298_);
lean_dec(v_traceState_5285_);
v___x_5300_ = lean_box(0);
v_isShared_5301_ = v_isSharedCheck_5311_;
goto v_resetjp_5299_;
}
v_resetjp_5299_:
{
lean_object* v___x_5302_; lean_object* v___x_5304_; 
v___x_5302_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5223_, v_traces_5298_);
lean_dec_ref(v_traces_5298_);
if (v_isShared_5301_ == 0)
{
lean_ctor_set(v___x_5300_, 0, v___x_5302_);
v___x_5304_ = v___x_5300_;
goto v_reusejp_5303_;
}
else
{
lean_object* v_reuseFailAlloc_5310_; 
v_reuseFailAlloc_5310_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5310_, 0, v___x_5302_);
lean_ctor_set_uint64(v_reuseFailAlloc_5310_, sizeof(void*)*1, v_tid_5297_);
v___x_5304_ = v_reuseFailAlloc_5310_;
goto v_reusejp_5303_;
}
v_reusejp_5303_:
{
lean_object* v___x_5306_; 
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 4, v___x_5304_);
v___x_5306_ = v___x_5295_;
goto v_reusejp_5305_;
}
else
{
lean_object* v_reuseFailAlloc_5309_; 
v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_env_5286_);
lean_ctor_set(v_reuseFailAlloc_5309_, 1, v_nextMacroScope_5287_);
lean_ctor_set(v_reuseFailAlloc_5309_, 2, v_ngen_5288_);
lean_ctor_set(v_reuseFailAlloc_5309_, 3, v_auxDeclNGen_5289_);
lean_ctor_set(v_reuseFailAlloc_5309_, 4, v___x_5304_);
lean_ctor_set(v_reuseFailAlloc_5309_, 5, v_cache_5290_);
lean_ctor_set(v_reuseFailAlloc_5309_, 6, v_messages_5291_);
lean_ctor_set(v_reuseFailAlloc_5309_, 7, v_infoState_5292_);
lean_ctor_set(v_reuseFailAlloc_5309_, 8, v_snapshotTasks_5293_);
v___x_5306_ = v_reuseFailAlloc_5309_;
goto v_reusejp_5305_;
}
v_reusejp_5305_:
{
lean_object* v___x_5307_; lean_object* v___x_5308_; 
v___x_5307_ = lean_st_ref_set(v___y_5229_, v___x_5306_);
v___x_5308_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_fst_5231_);
return v___x_5308_;
}
}
}
}
}
else
{
goto v___jp_5277_;
}
}
else
{
goto v___jp_5277_;
}
}
v___jp_5313_:
{
double v___x_5315_; double v___x_5316_; double v___x_5317_; uint8_t v___x_5318_; 
v___x_5315_ = lean_unbox_float(v_snd_5251_);
v___x_5316_ = lean_unbox_float(v_fst_5250_);
v___x_5317_ = lean_float_sub(v___x_5315_, v___x_5316_);
v___x_5318_ = lean_float_decLt(v___y_5314_, v___x_5317_);
v___y_5283_ = v___x_5318_;
goto v___jp_5282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3___boxed(lean_object* v_cls_5331_, lean_object* v_collapsed_5332_, lean_object* v_tag_5333_, lean_object* v_opts_5334_, lean_object* v_clsEnabled_5335_, lean_object* v_oldTraces_5336_, lean_object* v_msg_5337_, lean_object* v_resStartStop_5338_, lean_object* v___y_5339_, lean_object* v___y_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_, lean_object* v___y_5343_){
_start:
{
uint8_t v_collapsed_boxed_5344_; uint8_t v_clsEnabled_boxed_5345_; lean_object* v_res_5346_; 
v_collapsed_boxed_5344_ = lean_unbox(v_collapsed_5332_);
v_clsEnabled_boxed_5345_ = lean_unbox(v_clsEnabled_5335_);
v_res_5346_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5331_, v_collapsed_boxed_5344_, v_tag_5333_, v_opts_5334_, v_clsEnabled_boxed_5345_, v_oldTraces_5336_, v_msg_5337_, v_resStartStop_5338_, v___y_5339_, v___y_5340_, v___y_5341_, v___y_5342_);
lean_dec(v___y_5342_);
lean_dec_ref(v___y_5341_);
lean_dec(v___y_5340_);
lean_dec_ref(v___y_5339_);
lean_dec_ref(v_opts_5334_);
return v_res_5346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5351_, lean_object* v_a_5352_, lean_object* v_a_5353_, lean_object* v_a_5354_, lean_object* v_a_5355_){
_start:
{
lean_object* v___y_5358_; lean_object* v_options_5376_; uint8_t v_hasTrace_5377_; lean_object* v_cls_5378_; uint8_t v___x_5379_; uint8_t v___x_5380_; 
v_options_5376_ = lean_ctor_get(v_a_5354_, 2);
v_hasTrace_5377_ = lean_ctor_get_uint8(v_options_5376_, sizeof(void*)*1);
v_cls_5378_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5379_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5351_);
v___x_5380_ = 1;
if (v_hasTrace_5377_ == 0)
{
lean_object* v___x_5381_; 
v___x_5381_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5379_, v_e_5351_, v___x_5380_, v_cls_5378_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
v___y_5358_ = v___x_5381_;
goto v___jp_5357_;
}
else
{
lean_object* v___x_5382_; lean_object* v_a_5383_; lean_object* v___f_5384_; lean_object* v___x_5385_; lean_object* v___y_5387_; lean_object* v___y_5388_; lean_object* v_a_5389_; lean_object* v___y_5403_; lean_object* v___y_5404_; lean_object* v_a_5405_; uint8_t v___x_5456_; 
v___x_5382_ = l_Lean_isTracingEnabledFor___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___redArg(v_cls_5378_, v_a_5354_);
v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
lean_inc(v_a_5383_);
lean_dec_ref(v___x_5382_);
v___f_5384_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5385_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__3___redArg___closed__1));
v___x_5456_ = lean_unbox(v_a_5383_);
if (v___x_5456_ == 0)
{
lean_object* v___x_5457_; uint8_t v___x_5458_; 
v___x_5457_ = l_Lean_trace_profiler;
v___x_5458_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5376_, v___x_5457_);
if (v___x_5458_ == 0)
{
lean_object* v___x_5459_; 
lean_dec(v_a_5383_);
v___x_5459_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5379_, v_e_5351_, v___x_5380_, v_cls_5378_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
v___y_5358_ = v___x_5459_;
goto v___jp_5357_;
}
else
{
goto v___jp_5415_;
}
}
else
{
goto v___jp_5415_;
}
v___jp_5386_:
{
lean_object* v___x_5390_; double v___x_5391_; double v___x_5392_; double v___x_5393_; double v___x_5394_; double v___x_5395_; lean_object* v___x_5396_; lean_object* v___x_5397_; lean_object* v___x_5398_; lean_object* v___x_5399_; uint8_t v___x_5400_; lean_object* v___x_5401_; 
v___x_5390_ = lean_io_mono_nanos_now();
v___x_5391_ = lean_float_of_nat(v___y_5388_);
v___x_5392_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5393_ = lean_float_div(v___x_5391_, v___x_5392_);
v___x_5394_ = lean_float_of_nat(v___x_5390_);
v___x_5395_ = lean_float_div(v___x_5394_, v___x_5392_);
v___x_5396_ = lean_box_float(v___x_5393_);
v___x_5397_ = lean_box_float(v___x_5395_);
v___x_5398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5398_, 0, v___x_5396_);
lean_ctor_set(v___x_5398_, 1, v___x_5397_);
v___x_5399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5399_, 0, v_a_5389_);
lean_ctor_set(v___x_5399_, 1, v___x_5398_);
v___x_5400_ = lean_unbox(v_a_5383_);
lean_dec(v_a_5383_);
v___x_5401_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5378_, v___x_5380_, v___x_5385_, v_options_5376_, v___x_5400_, v___y_5387_, v___f_5384_, v___x_5399_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
v___y_5358_ = v___x_5401_;
goto v___jp_5357_;
}
v___jp_5402_:
{
lean_object* v___x_5406_; double v___x_5407_; double v___x_5408_; lean_object* v___x_5409_; lean_object* v___x_5410_; lean_object* v___x_5411_; lean_object* v___x_5412_; uint8_t v___x_5413_; lean_object* v___x_5414_; 
v___x_5406_ = lean_io_get_num_heartbeats();
v___x_5407_ = lean_float_of_nat(v___y_5403_);
v___x_5408_ = lean_float_of_nat(v___x_5406_);
v___x_5409_ = lean_box_float(v___x_5407_);
v___x_5410_ = lean_box_float(v___x_5408_);
v___x_5411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5411_, 0, v___x_5409_);
lean_ctor_set(v___x_5411_, 1, v___x_5410_);
v___x_5412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5412_, 0, v_a_5405_);
lean_ctor_set(v___x_5412_, 1, v___x_5411_);
v___x_5413_ = lean_unbox(v_a_5383_);
lean_dec(v_a_5383_);
v___x_5414_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3(v_cls_5378_, v___x_5380_, v___x_5385_, v_options_5376_, v___x_5413_, v___y_5404_, v___f_5384_, v___x_5412_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
v___y_5358_ = v___x_5414_;
goto v___jp_5357_;
}
v___jp_5415_:
{
lean_object* v___x_5416_; lean_object* v_a_5417_; lean_object* v___x_5418_; uint8_t v___x_5419_; 
v___x_5416_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___redArg(v_a_5355_);
v_a_5417_ = lean_ctor_get(v___x_5416_, 0);
lean_inc(v_a_5417_);
lean_dec_ref(v___x_5416_);
v___x_5418_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5419_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5376_, v___x_5418_);
if (v___x_5419_ == 0)
{
lean_object* v___x_5420_; lean_object* v___x_5421_; 
v___x_5420_ = lean_io_mono_nanos_now();
v___x_5421_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5379_, v_e_5351_, v___x_5380_, v_cls_5378_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
if (lean_obj_tag(v___x_5421_) == 0)
{
lean_object* v_a_5422_; lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5429_; 
v_a_5422_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5429_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5429_ == 0)
{
v___x_5424_ = v___x_5421_;
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
else
{
lean_inc(v_a_5422_);
lean_dec(v___x_5421_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5427_; 
if (v_isShared_5425_ == 0)
{
lean_ctor_set_tag(v___x_5424_, 1);
v___x_5427_ = v___x_5424_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v_a_5422_);
v___x_5427_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
v___y_5387_ = v_a_5417_;
v___y_5388_ = v___x_5420_;
v_a_5389_ = v___x_5427_;
goto v___jp_5386_;
}
}
}
else
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5437_; 
v_a_5430_ = lean_ctor_get(v___x_5421_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5421_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5432_ = v___x_5421_;
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5421_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5435_; 
if (v_isShared_5433_ == 0)
{
lean_ctor_set_tag(v___x_5432_, 0);
v___x_5435_ = v___x_5432_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5430_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
v___y_5387_ = v_a_5417_;
v___y_5388_ = v___x_5420_;
v_a_5389_ = v___x_5435_;
goto v___jp_5386_;
}
}
}
}
else
{
lean_object* v___x_5438_; lean_object* v___x_5439_; 
v___x_5438_ = lean_io_get_num_heartbeats();
v___x_5439_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5379_, v_e_5351_, v___x_5380_, v_cls_5378_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_);
if (lean_obj_tag(v___x_5439_) == 0)
{
lean_object* v_a_5440_; lean_object* v___x_5442_; uint8_t v_isShared_5443_; uint8_t v_isSharedCheck_5447_; 
v_a_5440_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5447_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5447_ == 0)
{
v___x_5442_ = v___x_5439_;
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
else
{
lean_inc(v_a_5440_);
lean_dec(v___x_5439_);
v___x_5442_ = lean_box(0);
v_isShared_5443_ = v_isSharedCheck_5447_;
goto v_resetjp_5441_;
}
v_resetjp_5441_:
{
lean_object* v___x_5445_; 
if (v_isShared_5443_ == 0)
{
lean_ctor_set_tag(v___x_5442_, 1);
v___x_5445_ = v___x_5442_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_a_5440_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
v___y_5403_ = v___x_5438_;
v___y_5404_ = v_a_5417_;
v_a_5405_ = v___x_5445_;
goto v___jp_5402_;
}
}
}
else
{
lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5455_; 
v_a_5448_ = lean_ctor_get(v___x_5439_, 0);
v_isSharedCheck_5455_ = !lean_is_exclusive(v___x_5439_);
if (v_isSharedCheck_5455_ == 0)
{
v___x_5450_ = v___x_5439_;
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_dec(v___x_5439_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5455_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v___x_5453_; 
if (v_isShared_5451_ == 0)
{
lean_ctor_set_tag(v___x_5450_, 0);
v___x_5453_ = v___x_5450_;
goto v_reusejp_5452_;
}
else
{
lean_object* v_reuseFailAlloc_5454_; 
v_reuseFailAlloc_5454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5454_, 0, v_a_5448_);
v___x_5453_ = v_reuseFailAlloc_5454_;
goto v_reusejp_5452_;
}
v_reusejp_5452_:
{
v___y_5403_ = v___x_5438_;
v___y_5404_ = v_a_5417_;
v_a_5405_ = v___x_5453_;
goto v___jp_5402_;
}
}
}
}
}
}
v___jp_5357_:
{
if (lean_obj_tag(v___y_5358_) == 0)
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5367_; 
v_a_5359_ = lean_ctor_get(v___y_5358_, 0);
v_isSharedCheck_5367_ = !lean_is_exclusive(v___y_5358_);
if (v_isSharedCheck_5367_ == 0)
{
v___x_5361_ = v___y_5358_;
v_isShared_5362_ = v_isSharedCheck_5367_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___y_5358_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5367_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v_fst_5363_; lean_object* v___x_5365_; 
v_fst_5363_ = lean_ctor_get(v_a_5359_, 0);
lean_inc(v_fst_5363_);
lean_dec(v_a_5359_);
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 0, v_fst_5363_);
v___x_5365_ = v___x_5361_;
goto v_reusejp_5364_;
}
else
{
lean_object* v_reuseFailAlloc_5366_; 
v_reuseFailAlloc_5366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5366_, 0, v_fst_5363_);
v___x_5365_ = v_reuseFailAlloc_5366_;
goto v_reusejp_5364_;
}
v_reusejp_5364_:
{
return v___x_5365_;
}
}
}
else
{
lean_object* v_a_5368_; lean_object* v___x_5370_; uint8_t v_isShared_5371_; uint8_t v_isSharedCheck_5375_; 
v_a_5368_ = lean_ctor_get(v___y_5358_, 0);
v_isSharedCheck_5375_ = !lean_is_exclusive(v___y_5358_);
if (v_isSharedCheck_5375_ == 0)
{
v___x_5370_ = v___y_5358_;
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
else
{
lean_inc(v_a_5368_);
lean_dec(v___y_5358_);
v___x_5370_ = lean_box(0);
v_isShared_5371_ = v_isSharedCheck_5375_;
goto v_resetjp_5369_;
}
v_resetjp_5369_:
{
lean_object* v___x_5373_; 
if (v_isShared_5371_ == 0)
{
v___x_5373_ = v___x_5370_;
goto v_reusejp_5372_;
}
else
{
lean_object* v_reuseFailAlloc_5374_; 
v_reuseFailAlloc_5374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5374_, 0, v_a_5368_);
v___x_5373_ = v_reuseFailAlloc_5374_;
goto v_reusejp_5372_;
}
v_reusejp_5372_:
{
return v___x_5373_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5460_, lean_object* v_a_5461_, lean_object* v_a_5462_, lean_object* v_a_5463_, lean_object* v_a_5464_, lean_object* v_a_5465_){
_start:
{
lean_object* v_res_5466_; 
v_res_5466_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5460_, v_a_5461_, v_a_5462_, v_a_5463_, v_a_5464_);
lean_dec(v_a_5464_);
lean_dec_ref(v_a_5463_);
lean_dec(v_a_5462_);
lean_dec_ref(v_a_5461_);
return v_res_5466_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5(lean_object* v_00_u03b1_5467_, lean_object* v_x_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v___x_5474_; 
v___x_5474_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___redArg(v_x_5468_);
return v___x_5474_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5___boxed(lean_object* v_00_u03b1_5475_, lean_object* v_x_5476_, lean_object* v___y_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__3_spec__5(v_00_u03b1_5475_, v_x_5476_, v___y_5477_, v___y_5478_, v___y_5479_, v___y_5480_);
lean_dec(v___y_5480_);
lean_dec_ref(v___y_5479_);
lean_dec(v___y_5478_);
lean_dec_ref(v___y_5477_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5483_, lean_object* v___y_5484_){
_start:
{
uint8_t v___x_5486_; 
v___x_5486_ = l_Lean_Expr_hasMVar(v_e_5483_);
if (v___x_5486_ == 0)
{
lean_object* v___x_5487_; 
v___x_5487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5487_, 0, v_e_5483_);
return v___x_5487_;
}
else
{
lean_object* v___x_5488_; lean_object* v_mctx_5489_; lean_object* v___x_5490_; lean_object* v_fst_5491_; lean_object* v_snd_5492_; lean_object* v___x_5493_; lean_object* v_cache_5494_; lean_object* v_zetaDeltaFVarIds_5495_; lean_object* v_postponed_5496_; lean_object* v_diag_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5506_; 
v___x_5488_ = lean_st_ref_get(v___y_5484_);
v_mctx_5489_ = lean_ctor_get(v___x_5488_, 0);
lean_inc_ref(v_mctx_5489_);
lean_dec(v___x_5488_);
v___x_5490_ = l_Lean_instantiateMVarsCore(v_mctx_5489_, v_e_5483_);
v_fst_5491_ = lean_ctor_get(v___x_5490_, 0);
lean_inc(v_fst_5491_);
v_snd_5492_ = lean_ctor_get(v___x_5490_, 1);
lean_inc(v_snd_5492_);
lean_dec_ref(v___x_5490_);
v___x_5493_ = lean_st_ref_take(v___y_5484_);
v_cache_5494_ = lean_ctor_get(v___x_5493_, 1);
v_zetaDeltaFVarIds_5495_ = lean_ctor_get(v___x_5493_, 2);
v_postponed_5496_ = lean_ctor_get(v___x_5493_, 3);
v_diag_5497_ = lean_ctor_get(v___x_5493_, 4);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5493_);
if (v_isSharedCheck_5506_ == 0)
{
lean_object* v_unused_5507_; 
v_unused_5507_ = lean_ctor_get(v___x_5493_, 0);
lean_dec(v_unused_5507_);
v___x_5499_ = v___x_5493_;
v_isShared_5500_ = v_isSharedCheck_5506_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_diag_5497_);
lean_inc(v_postponed_5496_);
lean_inc(v_zetaDeltaFVarIds_5495_);
lean_inc(v_cache_5494_);
lean_dec(v___x_5493_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5506_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v___x_5502_; 
if (v_isShared_5500_ == 0)
{
lean_ctor_set(v___x_5499_, 0, v_snd_5492_);
v___x_5502_ = v___x_5499_;
goto v_reusejp_5501_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_snd_5492_);
lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_cache_5494_);
lean_ctor_set(v_reuseFailAlloc_5505_, 2, v_zetaDeltaFVarIds_5495_);
lean_ctor_set(v_reuseFailAlloc_5505_, 3, v_postponed_5496_);
lean_ctor_set(v_reuseFailAlloc_5505_, 4, v_diag_5497_);
v___x_5502_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5501_;
}
v_reusejp_5501_:
{
lean_object* v___x_5503_; lean_object* v___x_5504_; 
v___x_5503_ = lean_st_ref_set(v___y_5484_, v___x_5502_);
v___x_5504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5504_, 0, v_fst_5491_);
return v___x_5504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_){
_start:
{
lean_object* v_res_5511_; 
v_res_5511_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5508_, v___y_5509_);
lean_dec(v___y_5509_);
return v_res_5511_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5512_, lean_object* v___y_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_){
_start:
{
lean_object* v___x_5518_; 
v___x_5518_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5512_, v___y_5514_);
return v___x_5518_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5519_, lean_object* v___y_5520_, lean_object* v___y_5521_, lean_object* v___y_5522_, lean_object* v___y_5523_, lean_object* v___y_5524_){
_start:
{
lean_object* v_res_5525_; 
v_res_5525_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5519_, v___y_5520_, v___y_5521_, v___y_5522_, v___y_5523_);
lean_dec(v___y_5523_);
lean_dec_ref(v___y_5522_);
lean_dec(v___y_5521_);
lean_dec_ref(v___y_5520_);
return v_res_5525_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5526_, lean_object* v_opts_5527_, lean_object* v_act_5528_, lean_object* v_decl_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_){
_start:
{
lean_object* v___x_5535_; lean_object* v___x_5536_; 
lean_inc(v___y_5533_);
lean_inc_ref(v___y_5532_);
lean_inc(v___y_5531_);
lean_inc_ref(v___y_5530_);
v___x_5535_ = lean_apply_4(v_act_5528_, v___y_5530_, v___y_5531_, v___y_5532_, v___y_5533_);
v___x_5536_ = l_Lean_profileitIOUnsafe___redArg(v_category_5526_, v_opts_5527_, v___x_5535_, v_decl_5529_);
return v___x_5536_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5537_, lean_object* v_opts_5538_, lean_object* v_act_5539_, lean_object* v_decl_5540_, lean_object* v___y_5541_, lean_object* v___y_5542_, lean_object* v___y_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_){
_start:
{
lean_object* v_res_5546_; 
v_res_5546_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5537_, v_opts_5538_, v_act_5539_, v_decl_5540_, v___y_5541_, v___y_5542_, v___y_5543_, v___y_5544_);
lean_dec(v___y_5544_);
lean_dec_ref(v___y_5543_);
lean_dec(v___y_5542_);
lean_dec_ref(v___y_5541_);
lean_dec_ref(v_opts_5538_);
lean_dec_ref(v_category_5537_);
return v_res_5546_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5547_, lean_object* v_category_5548_, lean_object* v_opts_5549_, lean_object* v_act_5550_, lean_object* v_decl_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_, lean_object* v___y_5554_, lean_object* v___y_5555_){
_start:
{
lean_object* v___x_5557_; 
v___x_5557_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5548_, v_opts_5549_, v_act_5550_, v_decl_5551_, v___y_5552_, v___y_5553_, v___y_5554_, v___y_5555_);
return v___x_5557_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5558_, lean_object* v_category_5559_, lean_object* v_opts_5560_, lean_object* v_act_5561_, lean_object* v_decl_5562_, lean_object* v___y_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_){
_start:
{
lean_object* v_res_5568_; 
v_res_5568_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5558_, v_category_5559_, v_opts_5560_, v_act_5561_, v_decl_5562_, v___y_5563_, v___y_5564_, v___y_5565_, v___y_5566_);
lean_dec(v___y_5566_);
lean_dec_ref(v___y_5565_);
lean_dec(v___y_5564_);
lean_dec_ref(v___y_5563_);
lean_dec_ref(v_opts_5560_);
lean_dec_ref(v_category_5559_);
return v_res_5568_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5569_, uint8_t v_isExporting_5570_, lean_object* v___x_5571_, lean_object* v___y_5572_, lean_object* v___x_5573_, lean_object* v_a_x3f_5574_){
_start:
{
lean_object* v___x_5576_; lean_object* v_env_5577_; lean_object* v_nextMacroScope_5578_; lean_object* v_ngen_5579_; lean_object* v_auxDeclNGen_5580_; lean_object* v_traceState_5581_; lean_object* v_messages_5582_; lean_object* v_infoState_5583_; lean_object* v_snapshotTasks_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5609_; 
v___x_5576_ = lean_st_ref_take(v___y_5569_);
v_env_5577_ = lean_ctor_get(v___x_5576_, 0);
v_nextMacroScope_5578_ = lean_ctor_get(v___x_5576_, 1);
v_ngen_5579_ = lean_ctor_get(v___x_5576_, 2);
v_auxDeclNGen_5580_ = lean_ctor_get(v___x_5576_, 3);
v_traceState_5581_ = lean_ctor_get(v___x_5576_, 4);
v_messages_5582_ = lean_ctor_get(v___x_5576_, 6);
v_infoState_5583_ = lean_ctor_get(v___x_5576_, 7);
v_snapshotTasks_5584_ = lean_ctor_get(v___x_5576_, 8);
v_isSharedCheck_5609_ = !lean_is_exclusive(v___x_5576_);
if (v_isSharedCheck_5609_ == 0)
{
lean_object* v_unused_5610_; 
v_unused_5610_ = lean_ctor_get(v___x_5576_, 5);
lean_dec(v_unused_5610_);
v___x_5586_ = v___x_5576_;
v_isShared_5587_ = v_isSharedCheck_5609_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_snapshotTasks_5584_);
lean_inc(v_infoState_5583_);
lean_inc(v_messages_5582_);
lean_inc(v_traceState_5581_);
lean_inc(v_auxDeclNGen_5580_);
lean_inc(v_ngen_5579_);
lean_inc(v_nextMacroScope_5578_);
lean_inc(v_env_5577_);
lean_dec(v___x_5576_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5609_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5588_; lean_object* v___x_5590_; 
v___x_5588_ = l_Lean_Environment_setExporting(v_env_5577_, v_isExporting_5570_);
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 5, v___x_5571_);
lean_ctor_set(v___x_5586_, 0, v___x_5588_);
v___x_5590_ = v___x_5586_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5608_; 
v_reuseFailAlloc_5608_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5608_, 0, v___x_5588_);
lean_ctor_set(v_reuseFailAlloc_5608_, 1, v_nextMacroScope_5578_);
lean_ctor_set(v_reuseFailAlloc_5608_, 2, v_ngen_5579_);
lean_ctor_set(v_reuseFailAlloc_5608_, 3, v_auxDeclNGen_5580_);
lean_ctor_set(v_reuseFailAlloc_5608_, 4, v_traceState_5581_);
lean_ctor_set(v_reuseFailAlloc_5608_, 5, v___x_5571_);
lean_ctor_set(v_reuseFailAlloc_5608_, 6, v_messages_5582_);
lean_ctor_set(v_reuseFailAlloc_5608_, 7, v_infoState_5583_);
lean_ctor_set(v_reuseFailAlloc_5608_, 8, v_snapshotTasks_5584_);
v___x_5590_ = v_reuseFailAlloc_5608_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v_mctx_5593_; lean_object* v_zetaDeltaFVarIds_5594_; lean_object* v_postponed_5595_; lean_object* v_diag_5596_; lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5606_; 
v___x_5591_ = lean_st_ref_set(v___y_5569_, v___x_5590_);
v___x_5592_ = lean_st_ref_take(v___y_5572_);
v_mctx_5593_ = lean_ctor_get(v___x_5592_, 0);
v_zetaDeltaFVarIds_5594_ = lean_ctor_get(v___x_5592_, 2);
v_postponed_5595_ = lean_ctor_get(v___x_5592_, 3);
v_diag_5596_ = lean_ctor_get(v___x_5592_, 4);
v_isSharedCheck_5606_ = !lean_is_exclusive(v___x_5592_);
if (v_isSharedCheck_5606_ == 0)
{
lean_object* v_unused_5607_; 
v_unused_5607_ = lean_ctor_get(v___x_5592_, 1);
lean_dec(v_unused_5607_);
v___x_5598_ = v___x_5592_;
v_isShared_5599_ = v_isSharedCheck_5606_;
goto v_resetjp_5597_;
}
else
{
lean_inc(v_diag_5596_);
lean_inc(v_postponed_5595_);
lean_inc(v_zetaDeltaFVarIds_5594_);
lean_inc(v_mctx_5593_);
lean_dec(v___x_5592_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5606_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v___x_5601_; 
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 1, v___x_5573_);
v___x_5601_ = v___x_5598_;
goto v_reusejp_5600_;
}
else
{
lean_object* v_reuseFailAlloc_5605_; 
v_reuseFailAlloc_5605_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5605_, 0, v_mctx_5593_);
lean_ctor_set(v_reuseFailAlloc_5605_, 1, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5605_, 2, v_zetaDeltaFVarIds_5594_);
lean_ctor_set(v_reuseFailAlloc_5605_, 3, v_postponed_5595_);
lean_ctor_set(v_reuseFailAlloc_5605_, 4, v_diag_5596_);
v___x_5601_ = v_reuseFailAlloc_5605_;
goto v_reusejp_5600_;
}
v_reusejp_5600_:
{
lean_object* v___x_5602_; lean_object* v___x_5603_; lean_object* v___x_5604_; 
v___x_5602_ = lean_st_ref_set(v___y_5572_, v___x_5601_);
v___x_5603_ = lean_box(0);
v___x_5604_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5604_, 0, v___x_5603_);
return v___x_5604_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5611_, lean_object* v_isExporting_5612_, lean_object* v___x_5613_, lean_object* v___y_5614_, lean_object* v___x_5615_, lean_object* v_a_x3f_5616_, lean_object* v___y_5617_){
_start:
{
uint8_t v_isExporting_boxed_5618_; lean_object* v_res_5619_; 
v_isExporting_boxed_5618_ = lean_unbox(v_isExporting_5612_);
v_res_5619_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5611_, v_isExporting_boxed_5618_, v___x_5613_, v___y_5614_, v___x_5615_, v_a_x3f_5616_);
lean_dec(v_a_x3f_5616_);
lean_dec(v___y_5614_);
lean_dec(v___y_5611_);
return v_res_5619_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5620_; 
v___x_5620_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5620_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5621_; lean_object* v___x_5622_; 
v___x_5621_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5622_, 0, v___x_5621_);
return v___x_5622_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5623_; lean_object* v___x_5624_; 
v___x_5623_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5623_);
lean_ctor_set(v___x_5624_, 1, v___x_5623_);
return v___x_5624_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5625_; lean_object* v___x_5626_; 
v___x_5625_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5626_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5625_);
lean_ctor_set(v___x_5626_, 1, v___x_5625_);
lean_ctor_set(v___x_5626_, 2, v___x_5625_);
lean_ctor_set(v___x_5626_, 3, v___x_5625_);
lean_ctor_set(v___x_5626_, 4, v___x_5625_);
lean_ctor_set(v___x_5626_, 5, v___x_5625_);
return v___x_5626_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5627_, uint8_t v_isExporting_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
lean_object* v___x_5634_; lean_object* v_env_5635_; uint8_t v_isExporting_5636_; lean_object* v___x_5637_; lean_object* v_env_5638_; lean_object* v_nextMacroScope_5639_; lean_object* v_ngen_5640_; lean_object* v_auxDeclNGen_5641_; lean_object* v_traceState_5642_; lean_object* v_messages_5643_; lean_object* v_infoState_5644_; lean_object* v_snapshotTasks_5645_; lean_object* v___x_5647_; uint8_t v_isShared_5648_; uint8_t v_isSharedCheck_5699_; 
v___x_5634_ = lean_st_ref_get(v___y_5632_);
v_env_5635_ = lean_ctor_get(v___x_5634_, 0);
lean_inc_ref(v_env_5635_);
lean_dec(v___x_5634_);
v_isExporting_5636_ = lean_ctor_get_uint8(v_env_5635_, sizeof(void*)*8);
lean_dec_ref(v_env_5635_);
v___x_5637_ = lean_st_ref_take(v___y_5632_);
v_env_5638_ = lean_ctor_get(v___x_5637_, 0);
v_nextMacroScope_5639_ = lean_ctor_get(v___x_5637_, 1);
v_ngen_5640_ = lean_ctor_get(v___x_5637_, 2);
v_auxDeclNGen_5641_ = lean_ctor_get(v___x_5637_, 3);
v_traceState_5642_ = lean_ctor_get(v___x_5637_, 4);
v_messages_5643_ = lean_ctor_get(v___x_5637_, 6);
v_infoState_5644_ = lean_ctor_get(v___x_5637_, 7);
v_snapshotTasks_5645_ = lean_ctor_get(v___x_5637_, 8);
v_isSharedCheck_5699_ = !lean_is_exclusive(v___x_5637_);
if (v_isSharedCheck_5699_ == 0)
{
lean_object* v_unused_5700_; 
v_unused_5700_ = lean_ctor_get(v___x_5637_, 5);
lean_dec(v_unused_5700_);
v___x_5647_ = v___x_5637_;
v_isShared_5648_ = v_isSharedCheck_5699_;
goto v_resetjp_5646_;
}
else
{
lean_inc(v_snapshotTasks_5645_);
lean_inc(v_infoState_5644_);
lean_inc(v_messages_5643_);
lean_inc(v_traceState_5642_);
lean_inc(v_auxDeclNGen_5641_);
lean_inc(v_ngen_5640_);
lean_inc(v_nextMacroScope_5639_);
lean_inc(v_env_5638_);
lean_dec(v___x_5637_);
v___x_5647_ = lean_box(0);
v_isShared_5648_ = v_isSharedCheck_5699_;
goto v_resetjp_5646_;
}
v_resetjp_5646_:
{
lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5652_; 
v___x_5649_ = l_Lean_Environment_setExporting(v_env_5638_, v_isExporting_5628_);
v___x_5650_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5648_ == 0)
{
lean_ctor_set(v___x_5647_, 5, v___x_5650_);
lean_ctor_set(v___x_5647_, 0, v___x_5649_);
v___x_5652_ = v___x_5647_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5649_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v_nextMacroScope_5639_);
lean_ctor_set(v_reuseFailAlloc_5698_, 2, v_ngen_5640_);
lean_ctor_set(v_reuseFailAlloc_5698_, 3, v_auxDeclNGen_5641_);
lean_ctor_set(v_reuseFailAlloc_5698_, 4, v_traceState_5642_);
lean_ctor_set(v_reuseFailAlloc_5698_, 5, v___x_5650_);
lean_ctor_set(v_reuseFailAlloc_5698_, 6, v_messages_5643_);
lean_ctor_set(v_reuseFailAlloc_5698_, 7, v_infoState_5644_);
lean_ctor_set(v_reuseFailAlloc_5698_, 8, v_snapshotTasks_5645_);
v___x_5652_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v_mctx_5655_; lean_object* v_zetaDeltaFVarIds_5656_; lean_object* v_postponed_5657_; lean_object* v_diag_5658_; lean_object* v___x_5660_; uint8_t v_isShared_5661_; uint8_t v_isSharedCheck_5696_; 
v___x_5653_ = lean_st_ref_set(v___y_5632_, v___x_5652_);
v___x_5654_ = lean_st_ref_take(v___y_5630_);
v_mctx_5655_ = lean_ctor_get(v___x_5654_, 0);
v_zetaDeltaFVarIds_5656_ = lean_ctor_get(v___x_5654_, 2);
v_postponed_5657_ = lean_ctor_get(v___x_5654_, 3);
v_diag_5658_ = lean_ctor_get(v___x_5654_, 4);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___x_5654_);
if (v_isSharedCheck_5696_ == 0)
{
lean_object* v_unused_5697_; 
v_unused_5697_ = lean_ctor_get(v___x_5654_, 1);
lean_dec(v_unused_5697_);
v___x_5660_ = v___x_5654_;
v_isShared_5661_ = v_isSharedCheck_5696_;
goto v_resetjp_5659_;
}
else
{
lean_inc(v_diag_5658_);
lean_inc(v_postponed_5657_);
lean_inc(v_zetaDeltaFVarIds_5656_);
lean_inc(v_mctx_5655_);
lean_dec(v___x_5654_);
v___x_5660_ = lean_box(0);
v_isShared_5661_ = v_isSharedCheck_5696_;
goto v_resetjp_5659_;
}
v_resetjp_5659_:
{
lean_object* v___x_5662_; lean_object* v___x_5664_; 
v___x_5662_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5661_ == 0)
{
lean_ctor_set(v___x_5660_, 1, v___x_5662_);
v___x_5664_ = v___x_5660_;
goto v_reusejp_5663_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v_mctx_5655_);
lean_ctor_set(v_reuseFailAlloc_5695_, 1, v___x_5662_);
lean_ctor_set(v_reuseFailAlloc_5695_, 2, v_zetaDeltaFVarIds_5656_);
lean_ctor_set(v_reuseFailAlloc_5695_, 3, v_postponed_5657_);
lean_ctor_set(v_reuseFailAlloc_5695_, 4, v_diag_5658_);
v___x_5664_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5663_;
}
v_reusejp_5663_:
{
lean_object* v___x_5665_; lean_object* v_r_5666_; 
v___x_5665_ = lean_st_ref_set(v___y_5630_, v___x_5664_);
lean_inc(v___y_5632_);
lean_inc_ref(v___y_5631_);
lean_inc(v___y_5630_);
lean_inc_ref(v___y_5629_);
v_r_5666_ = lean_apply_5(v_x_5627_, v___y_5629_, v___y_5630_, v___y_5631_, v___y_5632_, lean_box(0));
if (lean_obj_tag(v_r_5666_) == 0)
{
lean_object* v_a_5667_; lean_object* v___x_5669_; uint8_t v_isShared_5670_; uint8_t v_isSharedCheck_5683_; 
v_a_5667_ = lean_ctor_get(v_r_5666_, 0);
v_isSharedCheck_5683_ = !lean_is_exclusive(v_r_5666_);
if (v_isSharedCheck_5683_ == 0)
{
v___x_5669_ = v_r_5666_;
v_isShared_5670_ = v_isSharedCheck_5683_;
goto v_resetjp_5668_;
}
else
{
lean_inc(v_a_5667_);
lean_dec(v_r_5666_);
v___x_5669_ = lean_box(0);
v_isShared_5670_ = v_isSharedCheck_5683_;
goto v_resetjp_5668_;
}
v_resetjp_5668_:
{
lean_object* v___x_5672_; 
lean_inc(v_a_5667_);
if (v_isShared_5670_ == 0)
{
lean_ctor_set_tag(v___x_5669_, 1);
v___x_5672_ = v___x_5669_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5682_; 
v_reuseFailAlloc_5682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5667_);
v___x_5672_ = v_reuseFailAlloc_5682_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5673_; lean_object* v___x_5675_; uint8_t v_isShared_5676_; uint8_t v_isSharedCheck_5680_; 
v___x_5673_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5632_, v_isExporting_5636_, v___x_5650_, v___y_5630_, v___x_5662_, v___x_5672_);
lean_dec_ref(v___x_5672_);
v_isSharedCheck_5680_ = !lean_is_exclusive(v___x_5673_);
if (v_isSharedCheck_5680_ == 0)
{
lean_object* v_unused_5681_; 
v_unused_5681_ = lean_ctor_get(v___x_5673_, 0);
lean_dec(v_unused_5681_);
v___x_5675_ = v___x_5673_;
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
else
{
lean_dec(v___x_5673_);
v___x_5675_ = lean_box(0);
v_isShared_5676_ = v_isSharedCheck_5680_;
goto v_resetjp_5674_;
}
v_resetjp_5674_:
{
lean_object* v___x_5678_; 
if (v_isShared_5676_ == 0)
{
lean_ctor_set(v___x_5675_, 0, v_a_5667_);
v___x_5678_ = v___x_5675_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5667_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
}
}
else
{
lean_object* v_a_5684_; lean_object* v___x_5685_; lean_object* v___x_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5693_; 
v_a_5684_ = lean_ctor_get(v_r_5666_, 0);
lean_inc(v_a_5684_);
lean_dec_ref(v_r_5666_);
v___x_5685_ = lean_box(0);
v___x_5686_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5632_, v_isExporting_5636_, v___x_5650_, v___y_5630_, v___x_5662_, v___x_5685_);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___x_5686_);
if (v_isSharedCheck_5693_ == 0)
{
lean_object* v_unused_5694_; 
v_unused_5694_ = lean_ctor_get(v___x_5686_, 0);
lean_dec(v_unused_5694_);
v___x_5688_ = v___x_5686_;
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
else
{
lean_dec(v___x_5686_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5693_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v___x_5691_; 
if (v_isShared_5689_ == 0)
{
lean_ctor_set_tag(v___x_5688_, 1);
lean_ctor_set(v___x_5688_, 0, v_a_5684_);
v___x_5691_ = v___x_5688_;
goto v_reusejp_5690_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_a_5684_);
v___x_5691_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5690_;
}
v_reusejp_5690_:
{
return v___x_5691_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5701_, lean_object* v_isExporting_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_, lean_object* v___y_5707_){
_start:
{
uint8_t v_isExporting_boxed_5708_; lean_object* v_res_5709_; 
v_isExporting_boxed_5708_ = lean_unbox(v_isExporting_5702_);
v_res_5709_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5701_, v_isExporting_boxed_5708_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
lean_dec(v___y_5706_);
lean_dec_ref(v___y_5705_);
lean_dec(v___y_5704_);
lean_dec_ref(v___y_5703_);
return v_res_5709_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5710_, uint8_t v_when_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_){
_start:
{
if (v_when_5711_ == 0)
{
lean_object* v___x_5717_; 
lean_inc(v___y_5715_);
lean_inc_ref(v___y_5714_);
lean_inc(v___y_5713_);
lean_inc_ref(v___y_5712_);
v___x_5717_ = lean_apply_5(v_x_5710_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_, lean_box(0));
return v___x_5717_;
}
else
{
uint8_t v___x_5718_; lean_object* v___x_5719_; 
v___x_5718_ = 0;
v___x_5719_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5710_, v___x_5718_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
return v___x_5719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5720_, lean_object* v_when_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_, lean_object* v___y_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_){
_start:
{
uint8_t v_when_boxed_5727_; lean_object* v_res_5728_; 
v_when_boxed_5727_ = lean_unbox(v_when_5721_);
v_res_5728_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5720_, v_when_boxed_5727_, v___y_5722_, v___y_5723_, v___y_5724_, v___y_5725_);
lean_dec(v___y_5725_);
lean_dec_ref(v___y_5724_);
lean_dec(v___y_5723_);
lean_dec_ref(v___y_5722_);
return v_res_5728_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5729_, lean_object* v___y_5730_, lean_object* v___y_5731_, lean_object* v___y_5732_, lean_object* v___y_5733_){
_start:
{
lean_object* v___x_5735_; lean_object* v_a_5736_; lean_object* v___x_5737_; uint8_t v___x_5738_; lean_object* v___x_5739_; 
v___x_5735_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5729_, v___y_5731_);
v_a_5736_ = lean_ctor_get(v___x_5735_, 0);
lean_inc(v_a_5736_);
lean_dec_ref(v___x_5735_);
v___x_5737_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5737_, 0, v_a_5736_);
v___x_5738_ = 1;
v___x_5739_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5737_, v___x_5738_, v___y_5730_, v___y_5731_, v___y_5732_, v___y_5733_);
return v___x_5739_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_, lean_object* v___y_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_){
_start:
{
lean_object* v_res_5746_; 
v_res_5746_ = l_Lean_Meta_letToHave___lam__0(v_e_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_);
lean_dec(v___y_5744_);
lean_dec_ref(v___y_5743_);
lean_dec(v___y_5742_);
lean_dec_ref(v___y_5741_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5748_, lean_object* v_a_5749_, lean_object* v_a_5750_, lean_object* v_a_5751_, lean_object* v_a_5752_){
_start:
{
lean_object* v_options_5754_; lean_object* v___f_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5758_; 
v_options_5754_ = lean_ctor_get(v_a_5751_, 2);
v___f_5755_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5755_, 0, v_e_5748_);
v___x_5756_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5757_ = lean_box(0);
v___x_5758_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5756_, v_options_5754_, v___f_5755_, v___x_5757_, v_a_5749_, v_a_5750_, v_a_5751_, v_a_5752_);
return v___x_5758_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5759_, lean_object* v_a_5760_, lean_object* v_a_5761_, lean_object* v_a_5762_, lean_object* v_a_5763_, lean_object* v_a_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l_Lean_Meta_letToHave(v_e_5759_, v_a_5760_, v_a_5761_, v_a_5762_, v_a_5763_);
lean_dec(v_a_5763_);
lean_dec_ref(v_a_5762_);
lean_dec(v_a_5761_);
lean_dec_ref(v_a_5760_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5766_, lean_object* v_x_5767_, uint8_t v_isExporting_5768_, lean_object* v___y_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_, lean_object* v___y_5772_){
_start:
{
lean_object* v___x_5774_; 
v___x_5774_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5767_, v_isExporting_5768_, v___y_5769_, v___y_5770_, v___y_5771_, v___y_5772_);
return v___x_5774_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5775_, lean_object* v_x_5776_, lean_object* v_isExporting_5777_, lean_object* v___y_5778_, lean_object* v___y_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_){
_start:
{
uint8_t v_isExporting_boxed_5783_; lean_object* v_res_5784_; 
v_isExporting_boxed_5783_ = lean_unbox(v_isExporting_5777_);
v_res_5784_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5775_, v_x_5776_, v_isExporting_boxed_5783_, v___y_5778_, v___y_5779_, v___y_5780_, v___y_5781_);
lean_dec(v___y_5781_);
lean_dec_ref(v___y_5780_);
lean_dec(v___y_5779_);
lean_dec_ref(v___y_5778_);
return v_res_5784_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5785_, lean_object* v_x_5786_, uint8_t v_when_5787_, lean_object* v___y_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_){
_start:
{
lean_object* v___x_5793_; 
v___x_5793_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5786_, v_when_5787_, v___y_5788_, v___y_5789_, v___y_5790_, v___y_5791_);
return v___x_5793_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5794_, lean_object* v_x_5795_, lean_object* v_when_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_, lean_object* v___y_5801_){
_start:
{
uint8_t v_when_boxed_5802_; lean_object* v_res_5803_; 
v_when_boxed_5802_ = lean_unbox(v_when_5796_);
v_res_5803_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5794_, v_x_5795_, v_when_boxed_5802_, v___y_5797_, v___y_5798_, v___y_5799_, v___y_5800_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
lean_dec(v___y_5798_);
lean_dec_ref(v___y_5797_);
return v_res_5803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5860_; uint8_t v___x_5861_; lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5860_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5861_ = 0;
v___x_5862_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5863_ = l_Lean_registerTraceClass(v___x_5860_, v___x_5861_, v___x_5862_);
if (lean_obj_tag(v___x_5863_) == 0)
{
lean_object* v___x_5864_; lean_object* v___x_5865_; 
lean_dec_ref(v___x_5863_);
v___x_5864_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5865_ = l_Lean_registerTraceClass(v___x_5864_, v___x_5861_, v___x_5862_);
return v___x_5865_;
}
else
{
return v___x_5863_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5866_){
_start:
{
lean_object* v_res_5867_; 
v_res_5867_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5867_;
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
l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default = _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default();
lean_mark_persistent(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult_default);
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
