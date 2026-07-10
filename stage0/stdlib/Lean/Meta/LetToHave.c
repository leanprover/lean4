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
uint8_t l_Lean_Name_isAnonymous(lean_object*);
uint8_t lean_bool_not(uint8_t);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint32_t l_Lean_Expr_approxDepth(lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_FVarId_throwUnknown___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_findDecl_x3f___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_addZetaDeltaFVarId___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Exception_toMessageData(lean_object*);
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
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1;
static const lean_array_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2;
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
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_21_; uint8_t v___x_26_; uint8_t v___x_27_; 
v___x_26_ = l_Lean_Expr_hasFVar(v_e_18_);
v___x_27_ = lean_bool_not(v___x_26_);
if (v___x_27_ == 0)
{
v___y_21_ = v___x_27_;
goto v___jp_20_;
}
else
{
uint8_t v___x_28_; uint8_t v___x_29_; 
v___x_28_ = l_Lean_Expr_hasExprMVar(v_e_18_);
v___x_29_ = lean_bool_not(v___x_28_);
v___y_21_ = v___x_29_;
goto v___jp_20_;
}
v___jp_20_:
{
if (v___y_21_ == 0)
{
return v___y_21_;
}
else
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
uint8_t v___x_24_; uint8_t v___x_25_; 
v___x_24_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_18_);
v___x_25_ = lean_bool_not(v___x_24_);
return v___x_25_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip___boxed(lean_object* v_e_30_, lean_object* v_maxDepth_31_){
_start:
{
uint32_t v_maxDepth_boxed_32_; uint8_t v_res_33_; lean_object* v_r_34_; 
v_maxDepth_boxed_32_ = lean_unbox_uint32(v_maxDepth_31_);
lean_dec(v_maxDepth_31_);
v_res_33_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_30_, v_maxDepth_boxed_32_);
lean_dec_ref(v_e_30_);
v_r_34_ = lean_box(v_res_33_);
return v_r_34_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2(void){
_start:
{
lean_object* v___x_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v___x_38_ = lean_box(0);
v___x_39_ = ((lean_object*)(l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__1));
v___x_40_ = l_Lean_Expr_const___override(v___x_39_, v___x_38_);
return v___x_40_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = lean_box(0);
v___x_42_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v___x_42_);
lean_ctor_set(v___x_43_, 1, v___x_41_);
return v___x_43_;
}
}
static lean_object* _init_l_Lean_Meta_LetToHave_instInhabitedResult_default(void){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__3);
return v___x_44_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instInhabitedResult(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0(lean_object* v_self_46_){
_start:
{
lean_object* v_expr_47_; 
v_expr_47_ = lean_ctor_get(v_self_46_, 0);
lean_inc_ref(v_expr_47_);
return v_expr_47_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0___boxed(lean_object* v_self_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_instCoeResultExpr___lam__0(v_self_48_);
lean_dec_ref(v_self_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(lean_object* v_a_52_, lean_object* v_b_53_, lean_object* v_x_54_){
_start:
{
if (lean_obj_tag(v_x_54_) == 0)
{
lean_dec(v_b_53_);
lean_dec_ref(v_a_52_);
return v_x_54_;
}
else
{
lean_object* v_key_55_; lean_object* v_value_56_; lean_object* v_tail_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_69_; 
v_key_55_ = lean_ctor_get(v_x_54_, 0);
v_value_56_ = lean_ctor_get(v_x_54_, 1);
v_tail_57_ = lean_ctor_get(v_x_54_, 2);
v_isSharedCheck_69_ = !lean_is_exclusive(v_x_54_);
if (v_isSharedCheck_69_ == 0)
{
v___x_59_ = v_x_54_;
v_isShared_60_ = v_isSharedCheck_69_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_tail_57_);
lean_inc(v_value_56_);
lean_inc(v_key_55_);
lean_dec(v_x_54_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_69_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
uint8_t v___x_61_; 
v___x_61_ = l_Lean_ExprStructEq_beq(v_key_55_, v_a_52_);
if (v___x_61_ == 0)
{
lean_object* v___x_62_; lean_object* v___x_64_; 
v___x_62_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_52_, v_b_53_, v_tail_57_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 2, v___x_62_);
v___x_64_ = v___x_59_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_key_55_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_value_56_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v___x_62_);
v___x_64_ = v_reuseFailAlloc_65_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
return v___x_64_;
}
}
else
{
lean_object* v___x_67_; 
lean_dec(v_value_56_);
lean_dec(v_key_55_);
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 1, v_b_53_);
lean_ctor_set(v___x_59_, 0, v_a_52_);
v___x_67_ = v___x_59_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_a_52_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_b_53_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v_tail_57_);
v___x_67_ = v_reuseFailAlloc_68_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
return v___x_67_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_70_, lean_object* v_x_71_){
_start:
{
if (lean_obj_tag(v_x_71_) == 0)
{
return v_x_70_;
}
else
{
lean_object* v_key_72_; lean_object* v_value_73_; lean_object* v_tail_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_97_; 
v_key_72_ = lean_ctor_get(v_x_71_, 0);
v_value_73_ = lean_ctor_get(v_x_71_, 1);
v_tail_74_ = lean_ctor_get(v_x_71_, 2);
v_isSharedCheck_97_ = !lean_is_exclusive(v_x_71_);
if (v_isSharedCheck_97_ == 0)
{
v___x_76_ = v_x_71_;
v_isShared_77_ = v_isSharedCheck_97_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_tail_74_);
lean_inc(v_value_73_);
lean_inc(v_key_72_);
lean_dec(v_x_71_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_97_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; uint64_t v___x_79_; uint64_t v___x_80_; uint64_t v___x_81_; uint64_t v_fold_82_; uint64_t v___x_83_; uint64_t v___x_84_; uint64_t v___x_85_; size_t v___x_86_; size_t v___x_87_; size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; lean_object* v___x_91_; lean_object* v___x_93_; 
v___x_78_ = lean_array_get_size(v_x_70_);
v___x_79_ = l_Lean_ExprStructEq_hash(v_key_72_);
v___x_80_ = 32ULL;
v___x_81_ = lean_uint64_shift_right(v___x_79_, v___x_80_);
v_fold_82_ = lean_uint64_xor(v___x_79_, v___x_81_);
v___x_83_ = 16ULL;
v___x_84_ = lean_uint64_shift_right(v_fold_82_, v___x_83_);
v___x_85_ = lean_uint64_xor(v_fold_82_, v___x_84_);
v___x_86_ = lean_uint64_to_usize(v___x_85_);
v___x_87_ = lean_usize_of_nat(v___x_78_);
v___x_88_ = ((size_t)1ULL);
v___x_89_ = lean_usize_sub(v___x_87_, v___x_88_);
v___x_90_ = lean_usize_land(v___x_86_, v___x_89_);
v___x_91_ = lean_array_uget_borrowed(v_x_70_, v___x_90_);
lean_inc(v___x_91_);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 2, v___x_91_);
v___x_93_ = v___x_76_;
goto v_reusejp_92_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_key_72_);
lean_ctor_set(v_reuseFailAlloc_96_, 1, v_value_73_);
lean_ctor_set(v_reuseFailAlloc_96_, 2, v___x_91_);
v___x_93_ = v_reuseFailAlloc_96_;
goto v_reusejp_92_;
}
v_reusejp_92_:
{
lean_object* v___x_94_; 
v___x_94_ = lean_array_uset(v_x_70_, v___x_90_, v___x_93_);
v_x_70_ = v___x_94_;
v_x_71_ = v_tail_74_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(lean_object* v_i_98_, lean_object* v_source_99_, lean_object* v_target_100_){
_start:
{
lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_101_ = lean_array_get_size(v_source_99_);
v___x_102_ = lean_nat_dec_lt(v_i_98_, v___x_101_);
if (v___x_102_ == 0)
{
lean_dec_ref(v_source_99_);
lean_dec(v_i_98_);
return v_target_100_;
}
else
{
lean_object* v_es_103_; lean_object* v___x_104_; lean_object* v_source_105_; lean_object* v_target_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_es_103_ = lean_array_fget(v_source_99_, v_i_98_);
v___x_104_ = lean_box(0);
v_source_105_ = lean_array_fset(v_source_99_, v_i_98_, v___x_104_);
v_target_106_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(v_target_100_, v_es_103_);
v___x_107_ = lean_unsigned_to_nat(1u);
v___x_108_ = lean_nat_add(v_i_98_, v___x_107_);
lean_dec(v_i_98_);
v_i_98_ = v___x_108_;
v_source_99_ = v_source_105_;
v_target_100_ = v_target_106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(lean_object* v_data_110_){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v_nbuckets_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_111_ = lean_array_get_size(v_data_110_);
v___x_112_ = lean_unsigned_to_nat(2u);
v_nbuckets_113_ = lean_nat_mul(v___x_111_, v___x_112_);
v___x_114_ = lean_unsigned_to_nat(0u);
v___x_115_ = lean_box(0);
v___x_116_ = lean_mk_array(v_nbuckets_113_, v___x_115_);
v___x_117_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v___x_114_, v_data_110_, v___x_116_);
return v___x_117_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(lean_object* v_a_118_, lean_object* v_x_119_){
_start:
{
if (lean_obj_tag(v_x_119_) == 0)
{
uint8_t v___x_120_; 
v___x_120_ = 0;
return v___x_120_;
}
else
{
lean_object* v_key_121_; lean_object* v_tail_122_; uint8_t v___x_123_; 
v_key_121_ = lean_ctor_get(v_x_119_, 0);
v_tail_122_ = lean_ctor_get(v_x_119_, 2);
v___x_123_ = l_Lean_ExprStructEq_beq(v_key_121_, v_a_118_);
if (v___x_123_ == 0)
{
v_x_119_ = v_tail_122_;
goto _start;
}
else
{
return v___x_123_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg___boxed(lean_object* v_a_125_, lean_object* v_x_126_){
_start:
{
uint8_t v_res_127_; lean_object* v_r_128_; 
v_res_127_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_125_, v_x_126_);
lean_dec(v_x_126_);
lean_dec_ref(v_a_125_);
v_r_128_ = lean_box(v_res_127_);
return v_r_128_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(lean_object* v_m_129_, lean_object* v_a_130_, lean_object* v_b_131_){
_start:
{
lean_object* v_size_132_; lean_object* v_buckets_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_176_; 
v_size_132_ = lean_ctor_get(v_m_129_, 0);
v_buckets_133_ = lean_ctor_get(v_m_129_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_m_129_);
if (v_isSharedCheck_176_ == 0)
{
v___x_135_ = v_m_129_;
v_isShared_136_ = v_isSharedCheck_176_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_buckets_133_);
lean_inc(v_size_132_);
lean_dec(v_m_129_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_176_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; uint64_t v___x_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v_fold_141_; uint64_t v___x_142_; uint64_t v___x_143_; uint64_t v___x_144_; size_t v___x_145_; size_t v___x_146_; size_t v___x_147_; size_t v___x_148_; size_t v___x_149_; lean_object* v_bkt_150_; uint8_t v___x_151_; 
v___x_137_ = lean_array_get_size(v_buckets_133_);
v___x_138_ = l_Lean_ExprStructEq_hash(v_a_130_);
v___x_139_ = 32ULL;
v___x_140_ = lean_uint64_shift_right(v___x_138_, v___x_139_);
v_fold_141_ = lean_uint64_xor(v___x_138_, v___x_140_);
v___x_142_ = 16ULL;
v___x_143_ = lean_uint64_shift_right(v_fold_141_, v___x_142_);
v___x_144_ = lean_uint64_xor(v_fold_141_, v___x_143_);
v___x_145_ = lean_uint64_to_usize(v___x_144_);
v___x_146_ = lean_usize_of_nat(v___x_137_);
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_sub(v___x_146_, v___x_147_);
v___x_149_ = lean_usize_land(v___x_145_, v___x_148_);
v_bkt_150_ = lean_array_uget_borrowed(v_buckets_133_, v___x_149_);
v___x_151_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_130_, v_bkt_150_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v_size_x27_153_; lean_object* v___x_154_; lean_object* v_buckets_x27_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_152_ = lean_unsigned_to_nat(1u);
v_size_x27_153_ = lean_nat_add(v_size_132_, v___x_152_);
lean_dec(v_size_132_);
lean_inc(v_bkt_150_);
v___x_154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_154_, 0, v_a_130_);
lean_ctor_set(v___x_154_, 1, v_b_131_);
lean_ctor_set(v___x_154_, 2, v_bkt_150_);
v_buckets_x27_155_ = lean_array_uset(v_buckets_133_, v___x_149_, v___x_154_);
v___x_156_ = lean_unsigned_to_nat(4u);
v___x_157_ = lean_nat_mul(v_size_x27_153_, v___x_156_);
v___x_158_ = lean_unsigned_to_nat(3u);
v___x_159_ = lean_nat_div(v___x_157_, v___x_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_array_get_size(v_buckets_x27_155_);
v___x_161_ = lean_nat_dec_le(v___x_159_, v___x_160_);
lean_dec(v___x_159_);
if (v___x_161_ == 0)
{
lean_object* v_val_162_; lean_object* v___x_164_; 
v_val_162_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_buckets_x27_155_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_val_162_);
lean_ctor_set(v___x_135_, 0, v_size_x27_153_);
v___x_164_ = v___x_135_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_val_162_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
else
{
lean_object* v___x_167_; 
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_buckets_x27_155_);
lean_ctor_set(v___x_135_, 0, v_size_x27_153_);
v___x_167_ = v___x_135_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_size_x27_153_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_buckets_x27_155_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
else
{
lean_object* v___x_169_; lean_object* v_buckets_x27_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
lean_inc(v_bkt_150_);
v___x_169_ = lean_box(0);
v_buckets_x27_170_ = lean_array_uset(v_buckets_133_, v___x_149_, v___x_169_);
v___x_171_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_130_, v_b_131_, v_bkt_150_);
v___x_172_ = lean_array_uset(v_buckets_x27_170_, v___x_149_, v___x_171_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v___x_172_);
v___x_174_ = v___x_135_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_size_132_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(lean_object* v_r_177_, lean_object* v_a_178_, lean_object* v_a_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v_type_x3f_184_; 
v_type_x3f_184_ = lean_ctor_get(v_r_177_, 1);
lean_inc(v_type_x3f_184_);
if (lean_obj_tag(v_type_x3f_184_) == 1)
{
lean_object* v_val_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_r_177_);
v_val_185_ = lean_ctor_get(v_type_x3f_184_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v_type_x3f_184_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v_type_x3f_184_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_val_185_);
lean_dec(v_type_x3f_184_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
lean_ctor_set_tag(v___x_187_, 0);
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_val_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
else
{
lean_object* v_expr_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_222_; 
lean_dec(v_type_x3f_184_);
v_expr_193_ = lean_ctor_get(v_r_177_, 0);
v_isSharedCheck_222_ = !lean_is_exclusive(v_r_177_);
if (v_isSharedCheck_222_ == 0)
{
lean_object* v_unused_223_; 
v_unused_223_ = lean_ctor_get(v_r_177_, 1);
lean_dec(v_unused_223_);
v___x_195_ = v_r_177_;
v_isShared_196_ = v_isSharedCheck_222_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_expr_193_);
lean_dec(v_r_177_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_222_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_197_; 
lean_inc(v_a_182_);
lean_inc_ref(v_a_181_);
lean_inc(v_a_180_);
lean_inc_ref(v_a_179_);
lean_inc_ref(v_expr_193_);
v___x_197_ = lean_infer_type(v_expr_193_, v_a_179_, v_a_180_, v_a_181_, v_a_182_);
if (lean_obj_tag(v___x_197_) == 0)
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_221_; 
v_a_198_ = lean_ctor_get(v___x_197_, 0);
v_isSharedCheck_221_ = !lean_is_exclusive(v___x_197_);
if (v_isSharedCheck_221_ == 0)
{
v___x_200_ = v___x_197_;
v_isShared_201_ = v_isSharedCheck_221_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_197_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_221_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_202_; lean_object* v_count_203_; lean_object* v_results_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_220_; 
v___x_202_ = lean_st_ref_take(v_a_178_);
v_count_203_ = lean_ctor_get(v___x_202_, 0);
v_results_204_ = lean_ctor_get(v___x_202_, 1);
v_isSharedCheck_220_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_220_ == 0)
{
v___x_206_ = v___x_202_;
v_isShared_207_ = v_isSharedCheck_220_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_results_204_);
lean_inc(v_count_203_);
lean_dec(v___x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_220_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
lean_inc(v_a_198_);
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v_a_198_);
lean_inc_ref(v_expr_193_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 1, v___x_208_);
v___x_210_ = v___x_195_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_219_; 
v_reuseFailAlloc_219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_219_, 0, v_expr_193_);
lean_ctor_set(v_reuseFailAlloc_219_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_219_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_204_, v_expr_193_, v___x_210_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_211_);
v___x_213_ = v___x_206_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_218_; 
v_reuseFailAlloc_218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_218_, 0, v_count_203_);
lean_ctor_set(v_reuseFailAlloc_218_, 1, v___x_211_);
v___x_213_ = v_reuseFailAlloc_218_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v___x_214_; lean_object* v___x_216_; 
v___x_214_ = lean_st_ref_set(v_a_178_, v___x_213_);
if (v_isShared_201_ == 0)
{
v___x_216_ = v___x_200_;
goto v_reusejp_215_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_a_198_);
v___x_216_ = v_reuseFailAlloc_217_;
goto v_reusejp_215_;
}
v_reusejp_215_:
{
return v___x_216_;
}
}
}
}
}
}
else
{
lean_del_object(v___x_195_);
lean_dec_ref(v_expr_193_);
return v___x_197_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg___boxed(lean_object* v_r_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_, lean_object* v_a_229_, lean_object* v_a_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_, v_a_229_);
lean_dec(v_a_229_);
lean_dec_ref(v_a_228_);
lean_dec(v_a_227_);
lean_dec_ref(v_a_226_);
lean_dec(v_a_225_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(lean_object* v_r_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_232_, v_a_234_, v_a_235_, v_a_236_, v_a_237_, v_a_238_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___boxed(lean_object* v_r_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_, lean_object* v_a_246_, lean_object* v_a_247_, lean_object* v_a_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(v_r_241_, v_a_242_, v_a_243_, v_a_244_, v_a_245_, v_a_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_a_246_);
lean_dec(v_a_245_);
lean_dec_ref(v_a_244_);
lean_dec(v_a_243_);
lean_dec(v_a_242_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(lean_object* v_00_u03b2_250_, lean_object* v_m_251_, lean_object* v_a_252_, lean_object* v_b_253_){
_start:
{
lean_object* v___x_254_; 
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_m_251_, v_a_252_, v_b_253_);
return v___x_254_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_object* v_00_u03b2_255_, lean_object* v_a_256_, lean_object* v_x_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_256_, v_x_257_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___boxed(lean_object* v_00_u03b2_259_, lean_object* v_a_260_, lean_object* v_x_261_){
_start:
{
uint8_t v_res_262_; lean_object* v_r_263_; 
v_res_262_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(v_00_u03b2_259_, v_a_260_, v_x_261_);
lean_dec(v_x_261_);
lean_dec_ref(v_a_260_);
v_r_263_ = lean_box(v_res_262_);
return v_r_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1(lean_object* v_00_u03b2_264_, lean_object* v_data_265_){
_start:
{
lean_object* v___x_266_; 
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_data_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2(lean_object* v_00_u03b2_267_, lean_object* v_a_268_, lean_object* v_b_269_, lean_object* v_x_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_268_, v_b_269_, v_x_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_272_, lean_object* v_i_273_, lean_object* v_source_274_, lean_object* v_target_275_){
_start:
{
lean_object* v___x_276_; 
v___x_276_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v_i_273_, v_source_274_, v_target_275_);
return v___x_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_277_, lean_object* v_x_278_, lean_object* v_x_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(v_x_278_, v_x_279_);
return v___x_280_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(lean_object* v_ctx_281_){
_start:
{
uint8_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = l_List_isEmpty___redArg(v_ctx_281_);
v___x_283_ = lean_bool_not(v___x_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check___boxed(lean_object* v_ctx_284_){
_start:
{
uint8_t v_res_285_; lean_object* v_r_286_; 
v_res_285_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_ctx_284_);
lean_dec(v_ctx_284_);
v_r_286_ = lean_box(v_res_285_);
return v_r_286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(lean_object* v_e_287_, lean_object* v_m_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
uint8_t v___x_296_; 
v___x_296_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_289_);
if (v___x_296_ == 0)
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
lean_dec_ref(v_m_288_);
v___x_297_ = lean_box(0);
v___x_298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_298_, 0, v_e_287_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
v___x_299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_299_, 0, v___x_298_);
return v___x_299_;
}
else
{
lean_object* v___x_300_; 
lean_dec_ref(v_e_287_);
lean_inc(v_a_294_);
lean_inc_ref(v_a_293_);
lean_inc(v_a_292_);
lean_inc_ref(v_a_291_);
lean_inc(v_a_290_);
lean_inc(v_a_289_);
v___x_300_ = lean_apply_7(v_m_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, v_a_293_, v_a_294_, lean_box(0));
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck___boxed(lean_object* v_e_301_, lean_object* v_m_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_301_, v_m_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_, v_a_307_, v_a_308_);
lean_dec(v_a_308_);
lean_dec_ref(v_a_307_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec(v_a_303_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(lean_object* v_fvars_311_, lean_object* v_m_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_, lean_object* v_a_316_, lean_object* v_a_317_){
_start:
{
lean_object* v___x_319_; 
lean_inc(v_a_317_);
lean_inc_ref(v_a_316_);
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
v___x_319_ = lean_apply_7(v_m_312_, v_fvars_311_, v_a_313_, v_a_314_, v_a_315_, v_a_316_, v_a_317_, lean_box(0));
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg___boxed(lean_object* v_fvars_320_, lean_object* v_m_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(v_fvars_320_, v_m_321_, v_a_322_, v_a_323_, v_a_324_, v_a_325_, v_a_326_);
lean_dec(v_a_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(lean_object* v_00_u03b1_329_, lean_object* v_fvars_330_, lean_object* v_m_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_, lean_object* v_a_337_){
_start:
{
lean_object* v___x_339_; 
lean_inc(v_a_337_);
lean_inc_ref(v_a_336_);
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
v___x_339_ = lean_apply_7(v_m_331_, v_fvars_330_, v_a_333_, v_a_334_, v_a_335_, v_a_336_, v_a_337_, lean_box(0));
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed(lean_object* v_00_u03b1_340_, lean_object* v_fvars_341_, lean_object* v_m_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_, lean_object* v_a_349_){
_start:
{
lean_object* v_res_350_; 
v_res_350_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(v_00_u03b1_340_, v_fvars_341_, v_m_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
lean_dec(v_a_348_);
lean_dec_ref(v_a_347_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec(v_a_343_);
return v_res_350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(lean_object* v_a_351_){
_start:
{
lean_object* v___x_353_; lean_object* v_count_354_; lean_object* v_results_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_367_; 
v___x_353_ = lean_st_ref_take(v_a_351_);
v_count_354_ = lean_ctor_get(v___x_353_, 0);
v_results_355_ = lean_ctor_get(v___x_353_, 1);
v_isSharedCheck_367_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_367_ == 0)
{
v___x_357_ = v___x_353_;
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_results_355_);
lean_inc(v_count_354_);
lean_dec(v___x_353_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_367_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_359_ = lean_unsigned_to_nat(1u);
v___x_360_ = lean_nat_add(v_count_354_, v___x_359_);
lean_dec(v_count_354_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_360_);
v___x_362_ = v___x_357_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v_results_355_);
v___x_362_ = v_reuseFailAlloc_366_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_363_ = lean_st_ref_set(v_a_351_, v___x_362_);
v___x_364_ = lean_box(0);
v___x_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_365_, 0, v___x_364_);
return v___x_365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg___boxed(lean_object* v_a_368_, lean_object* v_a_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_368_);
lean_dec(v_a_368_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_, lean_object* v_a_375_, lean_object* v_a_376_){
_start:
{
lean_object* v___x_378_; 
v___x_378_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_372_);
return v___x_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___boxed(lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(v_a_379_, v_a_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_);
lean_dec(v_a_384_);
lean_dec_ref(v_a_383_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec(v_a_379_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(lean_object* v_a_387_, lean_object* v_x_388_){
_start:
{
if (lean_obj_tag(v_x_388_) == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_box(0);
return v___x_389_;
}
else
{
lean_object* v_key_390_; lean_object* v_value_391_; lean_object* v_tail_392_; uint8_t v___x_393_; 
v_key_390_ = lean_ctor_get(v_x_388_, 0);
v_value_391_ = lean_ctor_get(v_x_388_, 1);
v_tail_392_ = lean_ctor_get(v_x_388_, 2);
v___x_393_ = l_Lean_ExprStructEq_beq(v_key_390_, v_a_387_);
if (v___x_393_ == 0)
{
v_x_388_ = v_tail_392_;
goto _start;
}
else
{
lean_object* v___x_395_; 
lean_inc(v_value_391_);
v___x_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_395_, 0, v_value_391_);
return v___x_395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_396_, lean_object* v_x_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_396_, v_x_397_);
lean_dec(v_x_397_);
lean_dec_ref(v_a_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(lean_object* v_m_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_buckets_401_; lean_object* v___x_402_; uint64_t v___x_403_; uint64_t v___x_404_; uint64_t v___x_405_; uint64_t v_fold_406_; uint64_t v___x_407_; uint64_t v___x_408_; uint64_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; 
v_buckets_401_ = lean_ctor_get(v_m_399_, 1);
v___x_402_ = lean_array_get_size(v_buckets_401_);
v___x_403_ = l_Lean_ExprStructEq_hash(v_a_400_);
v___x_404_ = 32ULL;
v___x_405_ = lean_uint64_shift_right(v___x_403_, v___x_404_);
v_fold_406_ = lean_uint64_xor(v___x_403_, v___x_405_);
v___x_407_ = 16ULL;
v___x_408_ = lean_uint64_shift_right(v_fold_406_, v___x_407_);
v___x_409_ = lean_uint64_xor(v_fold_406_, v___x_408_);
v___x_410_ = lean_uint64_to_usize(v___x_409_);
v___x_411_ = lean_usize_of_nat(v___x_402_);
v___x_412_ = ((size_t)1ULL);
v___x_413_ = lean_usize_sub(v___x_411_, v___x_412_);
v___x_414_ = lean_usize_land(v___x_410_, v___x_413_);
v___x_415_ = lean_array_uget_borrowed(v_buckets_401_, v___x_414_);
v___x_416_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_400_, v___x_415_);
return v___x_416_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg___boxed(lean_object* v_m_417_, lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_417_, v_a_418_);
lean_dec_ref(v_a_418_);
lean_dec_ref(v_m_417_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(lean_object* v_e_420_, lean_object* v_a_421_){
_start:
{
lean_object* v___x_423_; lean_object* v_results_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_423_ = lean_st_ref_get(v_a_421_);
v_results_424_ = lean_ctor_get(v___x_423_, 1);
lean_inc_ref(v_results_424_);
lean_dec(v___x_423_);
v___x_425_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_results_424_, v_e_420_);
lean_dec_ref(v_results_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg___boxed(lean_object* v_e_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_427_, v_a_428_);
lean_dec(v_a_428_);
lean_dec_ref(v_e_427_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(lean_object* v_e_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_){
_start:
{
lean_object* v___x_439_; 
v___x_439_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_431_, v_a_433_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___boxed(lean_object* v_e_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_, lean_object* v_a_446_, lean_object* v_a_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(v_e_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_, v_a_445_, v_a_446_);
lean_dec(v_a_446_);
lean_dec_ref(v_a_445_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec(v_a_441_);
lean_dec_ref(v_e_440_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(lean_object* v_00_u03b2_449_, lean_object* v_m_450_, lean_object* v_a_451_){
_start:
{
lean_object* v___x_452_; 
v___x_452_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_450_, v_a_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___boxed(lean_object* v_00_u03b2_453_, lean_object* v_m_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(v_00_u03b2_453_, v_m_454_, v_a_455_);
lean_dec_ref(v_a_455_);
lean_dec_ref(v_m_454_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(lean_object* v_00_u03b2_457_, lean_object* v_a_458_, lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_458_, v_x_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_461_, lean_object* v_a_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(v_00_u03b2_461_, v_a_462_, v_x_463_);
lean_dec(v_x_463_);
lean_dec_ref(v_a_462_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(lean_object* v_e_465_, lean_object* v_m_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_, lean_object* v_a_471_, lean_object* v_a_472_){
_start:
{
lean_object* v_r_475_; lean_object* v___y_476_; lean_object* v___x_490_; lean_object* v_a_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_505_; 
v___x_490_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_465_, v_a_468_);
v_a_491_ = lean_ctor_get(v___x_490_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_490_);
if (v_isSharedCheck_505_ == 0)
{
v___x_493_ = v___x_490_;
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_a_491_);
lean_dec(v___x_490_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_505_;
goto v_resetjp_492_;
}
v___jp_474_:
{
lean_object* v___x_477_; lean_object* v_count_478_; lean_object* v_results_479_; lean_object* v___x_481_; uint8_t v_isShared_482_; uint8_t v_isSharedCheck_489_; 
v___x_477_ = lean_st_ref_take(v___y_476_);
v_count_478_ = lean_ctor_get(v___x_477_, 0);
v_results_479_ = lean_ctor_get(v___x_477_, 1);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_489_ == 0)
{
v___x_481_ = v___x_477_;
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
else
{
lean_inc(v_results_479_);
lean_inc(v_count_478_);
lean_dec(v___x_477_);
v___x_481_ = lean_box(0);
v_isShared_482_ = v_isSharedCheck_489_;
goto v_resetjp_480_;
}
v_resetjp_480_:
{
lean_object* v___x_483_; lean_object* v___x_485_; 
lean_inc_ref(v_r_475_);
v___x_483_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_479_, v_e_465_, v_r_475_);
if (v_isShared_482_ == 0)
{
lean_ctor_set(v___x_481_, 1, v___x_483_);
v___x_485_ = v___x_481_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_count_478_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v___x_483_);
v___x_485_ = v_reuseFailAlloc_488_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_st_ref_set(v___y_476_, v___x_485_);
v___x_487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_487_, 0, v_r_475_);
return v___x_487_;
}
}
}
v_resetjp_492_:
{
if (lean_obj_tag(v_a_491_) == 1)
{
lean_object* v_val_495_; lean_object* v___x_497_; 
lean_dec_ref(v_m_466_);
lean_dec_ref(v_e_465_);
v_val_495_ = lean_ctor_get(v_a_491_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v_a_491_, 1);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v_val_495_);
v___x_497_ = v___x_493_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_val_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
else
{
uint32_t v___x_499_; uint8_t v___x_500_; 
lean_del_object(v___x_493_);
lean_dec(v_a_491_);
v___x_499_ = 2;
v___x_500_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_465_, v___x_499_);
if (v___x_500_ == 0)
{
lean_object* v___x_501_; 
lean_inc(v_a_472_);
lean_inc_ref(v_a_471_);
lean_inc(v_a_470_);
lean_inc_ref(v_a_469_);
lean_inc(v_a_468_);
lean_inc(v_a_467_);
v___x_501_ = lean_apply_7(v_m_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, v_a_471_, v_a_472_, lean_box(0));
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
v_r_475_ = v_a_502_;
v___y_476_ = v_a_468_;
goto v___jp_474_;
}
else
{
lean_dec_ref(v_e_465_);
return v___x_501_;
}
}
else
{
lean_object* v___x_503_; lean_object* v___x_504_; 
lean_dec_ref(v_m_466_);
v___x_503_ = lean_box(0);
lean_inc_ref(v_e_465_);
v___x_504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_504_, 0, v_e_465_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
v_r_475_ = v___x_504_;
v___y_476_ = v_a_468_;
goto v___jp_474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache___boxed(lean_object* v_e_506_, lean_object* v_m_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_506_, v_m_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_a_512_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec(v_a_508_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(lean_object* v_e_516_, lean_object* v_a_517_){
_start:
{
uint8_t v___x_519_; 
v___x_519_ = l_Lean_Expr_hasLooseBVars(v_e_516_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_516_, v_a_517_);
return v___x_520_;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; 
v___x_521_ = lean_box(0);
v___x_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
return v___x_522_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg___boxed(lean_object* v_e_523_, lean_object* v_a_524_, lean_object* v_a_525_){
_start:
{
lean_object* v_res_526_; 
v_res_526_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_523_, v_a_524_);
lean_dec(v_a_524_);
lean_dec_ref(v_e_523_);
return v_res_526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(lean_object* v_e_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_527_, v_a_529_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___boxed(lean_object* v_e_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_, lean_object* v_a_542_, lean_object* v_a_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(v_e_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_, v_a_541_, v_a_542_);
lean_dec(v_a_542_);
lean_dec_ref(v_a_541_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec(v_a_537_);
lean_dec_ref(v_e_536_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(lean_object* v_e_545_, lean_object* v_a_546_, lean_object* v_a_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_550_; lean_object* v___x_551_; 
v___x_550_ = l_Lean_Expr_fvarId_x21(v_e_545_);
lean_inc(v___x_550_);
v___x_551_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_550_, v_a_546_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v_a_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_570_; 
v_a_552_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_570_ == 0)
{
v___x_554_ = v___x_551_;
v_isShared_555_ = v_isSharedCheck_570_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_a_552_);
lean_dec(v___x_551_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_570_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
if (lean_obj_tag(v_a_552_) == 1)
{
lean_object* v_val_556_; lean_object* v___x_558_; uint8_t v_isShared_559_; uint8_t v_isSharedCheck_568_; 
lean_dec(v___x_550_);
v_val_556_ = lean_ctor_get(v_a_552_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v_a_552_);
if (v_isSharedCheck_568_ == 0)
{
v___x_558_ = v_a_552_;
v_isShared_559_ = v_isSharedCheck_568_;
goto v_resetjp_557_;
}
else
{
lean_inc(v_val_556_);
lean_dec(v_a_552_);
v___x_558_ = lean_box(0);
v_isShared_559_ = v_isSharedCheck_568_;
goto v_resetjp_557_;
}
v_resetjp_557_:
{
lean_object* v___x_560_; lean_object* v___x_562_; 
v___x_560_ = l_Lean_LocalDecl_type(v_val_556_);
lean_dec(v_val_556_);
if (v_isShared_559_ == 0)
{
lean_ctor_set(v___x_558_, 0, v___x_560_);
v___x_562_ = v___x_558_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_567_; 
v_reuseFailAlloc_567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_567_, 0, v___x_560_);
v___x_562_ = v_reuseFailAlloc_567_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
lean_object* v___x_563_; lean_object* v___x_565_; 
v___x_563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_563_, 0, v_e_545_);
lean_ctor_set(v___x_563_, 1, v___x_562_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 0, v___x_563_);
v___x_565_ = v___x_554_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
}
}
else
{
lean_object* v___x_569_; 
lean_del_object(v___x_554_);
lean_dec(v_a_552_);
lean_dec_ref(v_e_545_);
v___x_569_ = l_Lean_FVarId_throwUnknown___redArg(v___x_550_, v_a_547_, v_a_548_);
return v___x_569_;
}
}
}
else
{
lean_object* v_a_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_578_; 
lean_dec(v___x_550_);
lean_dec_ref(v_e_545_);
v_a_571_ = lean_ctor_get(v___x_551_, 0);
v_isSharedCheck_578_ = !lean_is_exclusive(v___x_551_);
if (v_isSharedCheck_578_ == 0)
{
v___x_573_ = v___x_551_;
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_a_571_);
lean_dec(v___x_551_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_578_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_576_; 
if (v_isShared_574_ == 0)
{
v___x_576_ = v___x_573_;
goto v_reusejp_575_;
}
else
{
lean_object* v_reuseFailAlloc_577_; 
v_reuseFailAlloc_577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_577_, 0, v_a_571_);
v___x_576_ = v_reuseFailAlloc_577_;
goto v_reusejp_575_;
}
v_reusejp_575_:
{
return v___x_576_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg___boxed(lean_object* v_e_579_, lean_object* v_a_580_, lean_object* v_a_581_, lean_object* v_a_582_, lean_object* v_a_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_579_, v_a_580_, v_a_581_, v_a_582_);
lean_dec(v_a_582_);
lean_dec_ref(v_a_581_);
lean_dec_ref(v_a_580_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(lean_object* v_e_585_, lean_object* v_a_586_, lean_object* v_a_587_, lean_object* v_a_588_, lean_object* v_a_589_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_585_, v_a_586_, v_a_588_, v_a_589_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___boxed(lean_object* v_e_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_, lean_object* v_a_596_, lean_object* v_a_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(v_e_592_, v_a_593_, v_a_594_, v_a_595_, v_a_596_);
lean_dec(v_a_596_);
lean_dec_ref(v_a_595_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(lean_object* v_e_599_, lean_object* v___y_600_){
_start:
{
uint8_t v___x_602_; uint8_t v___x_603_; 
v___x_602_ = l_Lean_Expr_hasMVar(v_e_599_);
v___x_603_ = lean_bool_not(v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_604_; lean_object* v_mctx_605_; lean_object* v___x_606_; lean_object* v_fst_607_; lean_object* v_snd_608_; lean_object* v___x_609_; lean_object* v_cache_610_; lean_object* v_zetaDeltaFVarIds_611_; lean_object* v_postponed_612_; lean_object* v_diag_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_622_; 
v___x_604_ = lean_st_ref_get(v___y_600_);
v_mctx_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc_ref(v_mctx_605_);
lean_dec(v___x_604_);
v___x_606_ = l_Lean_instantiateMVarsCore(v_mctx_605_, v_e_599_);
v_fst_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_fst_607_);
v_snd_608_ = lean_ctor_get(v___x_606_, 1);
lean_inc(v_snd_608_);
lean_dec_ref(v___x_606_);
v___x_609_ = lean_st_ref_take(v___y_600_);
v_cache_610_ = lean_ctor_get(v___x_609_, 1);
v_zetaDeltaFVarIds_611_ = lean_ctor_get(v___x_609_, 2);
v_postponed_612_ = lean_ctor_get(v___x_609_, 3);
v_diag_613_ = lean_ctor_get(v___x_609_, 4);
v_isSharedCheck_622_ = !lean_is_exclusive(v___x_609_);
if (v_isSharedCheck_622_ == 0)
{
lean_object* v_unused_623_; 
v_unused_623_ = lean_ctor_get(v___x_609_, 0);
lean_dec(v_unused_623_);
v___x_615_ = v___x_609_;
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_diag_613_);
lean_inc(v_postponed_612_);
lean_inc(v_zetaDeltaFVarIds_611_);
lean_inc(v_cache_610_);
lean_dec(v___x_609_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_622_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
lean_object* v___x_618_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 0, v_snd_608_);
v___x_618_ = v___x_615_;
goto v_reusejp_617_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v_snd_608_);
lean_ctor_set(v_reuseFailAlloc_621_, 1, v_cache_610_);
lean_ctor_set(v_reuseFailAlloc_621_, 2, v_zetaDeltaFVarIds_611_);
lean_ctor_set(v_reuseFailAlloc_621_, 3, v_postponed_612_);
lean_ctor_set(v_reuseFailAlloc_621_, 4, v_diag_613_);
v___x_618_ = v_reuseFailAlloc_621_;
goto v_reusejp_617_;
}
v_reusejp_617_:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = lean_st_ref_set(v___y_600_, v___x_618_);
v___x_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_620_, 0, v_fst_607_);
return v___x_620_;
}
}
}
else
{
lean_object* v___x_624_; 
v___x_624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_624_, 0, v_e_599_);
return v___x_624_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg___boxed(lean_object* v_e_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_625_, v___y_626_);
lean_dec(v___y_626_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(lean_object* v_e_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_){
_start:
{
lean_object* v___x_637_; 
v___x_637_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_629_, v___y_633_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___boxed(lean_object* v_e_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(v_e_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec(v___y_644_);
lean_dec_ref(v___y_643_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec(v___y_639_);
return v_res_646_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(lean_object* v_k_647_, lean_object* v_t_648_){
_start:
{
if (lean_obj_tag(v_t_648_) == 0)
{
lean_object* v_k_649_; lean_object* v_l_650_; lean_object* v_r_651_; uint8_t v___x_652_; 
v_k_649_ = lean_ctor_get(v_t_648_, 1);
v_l_650_ = lean_ctor_get(v_t_648_, 3);
v_r_651_ = lean_ctor_get(v_t_648_, 4);
v___x_652_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_647_, v_k_649_);
switch(v___x_652_)
{
case 0:
{
v_t_648_ = v_l_650_;
goto _start;
}
case 1:
{
uint8_t v___x_654_; 
v___x_654_ = 1;
return v___x_654_;
}
default: 
{
v_t_648_ = v_r_651_;
goto _start;
}
}
}
else
{
uint8_t v___x_656_; 
v___x_656_ = 0;
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg___boxed(lean_object* v_k_657_, lean_object* v_t_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_657_, v_t_658_);
lean_dec(v_t_658_);
lean_dec(v_k_657_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(lean_object* v_as_661_, size_t v_sz_662_, size_t v_i_663_, lean_object* v_b_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_){
_start:
{
lean_object* v_a_671_; uint8_t v___x_675_; 
v___x_675_ = lean_usize_dec_lt(v_i_663_, v_sz_662_);
if (v___x_675_ == 0)
{
lean_object* v___x_676_; 
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v_b_664_);
return v___x_676_;
}
else
{
lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v___x_680_; uint8_t v_isShared_681_; uint8_t v_isSharedCheck_726_; 
v_fst_677_ = lean_ctor_get(v_b_664_, 0);
v_snd_678_ = lean_ctor_get(v_b_664_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_b_664_);
if (v_isSharedCheck_726_ == 0)
{
v___x_680_ = v_b_664_;
v_isShared_681_ = v_isSharedCheck_726_;
goto v_resetjp_679_;
}
else
{
lean_inc(v_snd_678_);
lean_inc(v_fst_677_);
lean_dec(v_b_664_);
v___x_680_ = lean_box(0);
v_isShared_681_ = v_isSharedCheck_726_;
goto v_resetjp_679_;
}
v_resetjp_679_:
{
lean_object* v_a_682_; uint8_t v___x_683_; 
v_a_682_ = lean_array_uget_borrowed(v_as_661_, v_i_663_);
v___x_683_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_a_682_, v_fst_677_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___x_703_; 
lean_inc_n(v_a_682_, 2);
v___x_684_ = l_Lean_FVarIdSet_insert(v_fst_677_, v_a_682_);
v___x_703_ = l_Lean_FVarId_isLetVar___redArg(v_a_682_, v___x_683_, v___y_665_, v___y_667_, v___y_668_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v_a_704_; uint8_t v___x_705_; 
v_a_704_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_a_704_);
lean_dec_ref_known(v___x_703_, 1);
v___x_705_ = lean_unbox(v_a_704_);
lean_dec(v_a_704_);
if (v___x_705_ == 0)
{
v___y_686_ = v___y_665_;
v___y_687_ = v___y_667_;
v___y_688_ = v___y_668_;
goto v___jp_685_;
}
else
{
lean_object* v___x_706_; 
lean_inc(v_a_682_);
v___x_706_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_a_682_, v___y_666_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_dec_ref_known(v___x_706_, 1);
v___y_686_ = v___y_665_;
v___y_687_ = v___y_667_;
v___y_688_ = v___y_668_;
goto v___jp_685_;
}
else
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_714_; 
lean_dec(v___x_684_);
lean_del_object(v___x_680_);
lean_dec(v_snd_678_);
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_714_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_714_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_714_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
lean_object* v___x_712_; 
if (v_isShared_710_ == 0)
{
v___x_712_ = v___x_709_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v_a_707_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
else
{
lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
lean_dec(v___x_684_);
lean_del_object(v___x_680_);
lean_dec(v_snd_678_);
v_a_715_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_722_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___x_703_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_dec(v___x_703_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
v___jp_685_:
{
lean_object* v___x_689_; 
lean_inc(v_a_682_);
v___x_689_ = l_Lean_FVarId_getType___redArg(v_a_682_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v___x_693_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = lean_array_push(v_snd_678_, v_a_690_);
if (v_isShared_681_ == 0)
{
lean_ctor_set(v___x_680_, 1, v___x_691_);
lean_ctor_set(v___x_680_, 0, v___x_684_);
v___x_693_ = v___x_680_;
goto v_reusejp_692_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_684_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
v___x_693_ = v_reuseFailAlloc_694_;
goto v_reusejp_692_;
}
v_reusejp_692_:
{
v_a_671_ = v___x_693_;
goto v___jp_670_;
}
}
else
{
lean_object* v_a_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_702_; 
lean_dec(v___x_684_);
lean_del_object(v___x_680_);
lean_dec(v_snd_678_);
v_a_695_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_702_ == 0)
{
v___x_697_ = v___x_689_;
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_a_695_);
lean_dec(v___x_689_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_702_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_700_; 
if (v_isShared_698_ == 0)
{
v___x_700_ = v___x_697_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
v___x_700_ = v_reuseFailAlloc_701_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
return v___x_700_;
}
}
}
}
}
else
{
lean_object* v___x_724_; 
if (v_isShared_681_ == 0)
{
v___x_724_ = v___x_680_;
goto v_reusejp_723_;
}
else
{
lean_object* v_reuseFailAlloc_725_; 
v_reuseFailAlloc_725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_725_, 0, v_fst_677_);
lean_ctor_set(v_reuseFailAlloc_725_, 1, v_snd_678_);
v___x_724_ = v_reuseFailAlloc_725_;
goto v_reusejp_723_;
}
v_reusejp_723_:
{
v_a_671_ = v___x_724_;
goto v___jp_670_;
}
}
}
}
v___jp_670_:
{
size_t v___x_672_; size_t v___x_673_; 
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_add(v_i_663_, v___x_672_);
v_i_663_ = v___x_673_;
v_b_664_ = v_a_671_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg___boxed(lean_object* v_as_727_, lean_object* v_sz_728_, lean_object* v_i_729_, lean_object* v_b_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
size_t v_sz_boxed_736_; size_t v_i_boxed_737_; lean_object* v_res_738_; 
v_sz_boxed_736_ = lean_unbox_usize(v_sz_728_);
lean_dec(v_sz_728_);
v_i_boxed_737_ = lean_unbox_usize(v_i_729_);
lean_dec(v_i_729_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_727_, v_sz_boxed_736_, v_i_boxed_737_, v_b_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
lean_dec(v___y_734_);
lean_dec_ref(v___y_733_);
lean_dec(v___y_732_);
lean_dec_ref(v___y_731_);
lean_dec_ref(v_as_727_);
return v_res_738_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_box(0);
v___x_740_ = lean_unsigned_to_nat(16u);
v___x_741_ = lean_mk_array(v___x_740_, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; 
v___x_742_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0);
v___x_743_ = lean_unsigned_to_nat(0u);
v___x_744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v___x_742_);
return v___x_744_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_747_; lean_object* v_visited_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_747_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2));
v_visited_748_ = lean_box(1);
v___x_749_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_750_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_visited_748_);
lean_ctor_set(v___x_750_, 2, v___x_747_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object* v_a_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_){
_start:
{
lean_object* v_fst_759_; lean_object* v_snd_760_; lean_object* v___x_762_; uint8_t v_isShared_763_; uint8_t v_isSharedCheck_807_; 
v_fst_759_ = lean_ctor_get(v_a_751_, 0);
v_snd_760_ = lean_ctor_get(v_a_751_, 1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_a_751_);
if (v_isSharedCheck_807_ == 0)
{
v___x_762_ = v_a_751_;
v_isShared_763_ = v_isSharedCheck_807_;
goto v_resetjp_761_;
}
else
{
lean_inc(v_snd_760_);
lean_inc(v_fst_759_);
lean_dec(v_a_751_);
v___x_762_ = lean_box(0);
v_isShared_763_ = v_isSharedCheck_807_;
goto v_resetjp_761_;
}
v_resetjp_761_:
{
lean_object* v___x_764_; lean_object* v___x_765_; uint8_t v___x_766_; uint8_t v___x_767_; 
v___x_764_ = lean_array_get_size(v_snd_760_);
v___x_765_ = lean_unsigned_to_nat(0u);
v___x_766_ = lean_nat_dec_eq(v___x_764_, v___x_765_);
v___x_767_ = lean_bool_not(v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_769_; 
if (v_isShared_763_ == 0)
{
v___x_769_ = v___x_762_;
goto v_reusejp_768_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_fst_759_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_snd_760_);
v___x_769_ = v_reuseFailAlloc_771_;
goto v_reusejp_768_;
}
v_reusejp_768_:
{
lean_object* v___x_770_; 
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v___x_769_);
return v___x_770_;
}
}
else
{
lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_772_ = l_Lean_instInhabitedExpr;
v___x_773_ = lean_unsigned_to_nat(1u);
v___x_774_ = lean_nat_sub(v___x_764_, v___x_773_);
v___x_775_ = lean_array_get_borrowed(v___x_772_, v_snd_760_, v___x_774_);
lean_dec(v___x_774_);
lean_inc(v___x_775_);
v___x_776_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v___x_775_, v___y_755_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v_fvarIds_780_; lean_object* v___x_781_; lean_object* v___x_783_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref_known(v___x_776_, 1);
v___x_778_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3);
v___x_779_ = l_Lean_collectFVars(v___x_778_, v_a_777_);
v_fvarIds_780_ = lean_ctor_get(v___x_779_, 2);
lean_inc_ref(v_fvarIds_780_);
lean_dec_ref(v___x_779_);
v___x_781_ = lean_array_pop(v_snd_760_);
if (v_isShared_763_ == 0)
{
lean_ctor_set(v___x_762_, 1, v___x_781_);
v___x_783_ = v___x_762_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_fst_759_);
lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_781_);
v___x_783_ = v_reuseFailAlloc_798_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
size_t v_sz_784_; size_t v___x_785_; lean_object* v___x_786_; 
v_sz_784_ = lean_array_size(v_fvarIds_780_);
v___x_785_ = ((size_t)0ULL);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_fvarIds_780_, v_sz_784_, v___x_785_, v___x_783_, v___y_754_, v___y_755_, v___y_756_, v___y_757_);
lean_dec_ref(v_fvarIds_780_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v_fst_788_; lean_object* v_snd_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_797_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref_known(v___x_786_, 1);
v_fst_788_ = lean_ctor_get(v_a_787_, 0);
v_snd_789_ = lean_ctor_get(v_a_787_, 1);
v_isSharedCheck_797_ = !lean_is_exclusive(v_a_787_);
if (v_isSharedCheck_797_ == 0)
{
v___x_791_ = v_a_787_;
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snd_789_);
lean_inc(v_fst_788_);
lean_dec(v_a_787_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_797_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_fst_788_);
lean_ctor_set(v_reuseFailAlloc_796_, 1, v_snd_789_);
v___x_794_ = v_reuseFailAlloc_796_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
v_a_751_ = v___x_794_;
goto _start;
}
}
}
else
{
return v___x_786_;
}
}
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_del_object(v___x_762_);
lean_dec(v_snd_760_);
lean_dec(v_fst_759_);
v_a_799_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_776_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_776_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object* v_a_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v___y_809_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object* v_e_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_){
_start:
{
lean_object* v_visited_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v_worklist_828_; lean_object* v___x_829_; lean_object* v___x_830_; 
v_visited_825_ = lean_box(1);
v___x_826_ = lean_unsigned_to_nat(1u);
v___x_827_ = lean_mk_empty_array_with_capacity(v___x_826_);
v_worklist_828_ = lean_array_push(v___x_827_, v_e_817_);
v___x_829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_829_, 0, v_visited_825_);
lean_ctor_set(v___x_829_, 1, v_worklist_828_);
v___x_830_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v___x_829_, v_a_818_, v_a_819_, v_a_820_, v_a_821_, v_a_822_, v_a_823_);
if (lean_obj_tag(v___x_830_) == 0)
{
lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_838_; 
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_838_ == 0)
{
lean_object* v_unused_839_; 
v_unused_839_ = lean_ctor_get(v___x_830_, 0);
lean_dec(v_unused_839_);
v___x_832_ = v___x_830_;
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
else
{
lean_dec(v___x_830_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_838_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v___x_834_; lean_object* v___x_836_; 
v___x_834_ = lean_box(0);
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 0, v___x_834_);
v___x_836_ = v___x_832_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_830_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_830_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_830_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object* v_e_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v_e_848_, v_a_849_, v_a_850_, v_a_851_, v_a_852_, v_a_853_, v_a_854_);
lean_dec(v_a_854_);
lean_dec_ref(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
lean_dec(v_a_850_);
lean_dec(v_a_849_);
return v_res_856_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object* v_00_u03b2_857_, lean_object* v_k_858_, lean_object* v_t_859_){
_start:
{
uint8_t v___x_860_; 
v___x_860_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_858_, v_t_859_);
return v___x_860_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object* v_00_u03b2_861_, lean_object* v_k_862_, lean_object* v_t_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(v_00_u03b2_861_, v_k_862_, v_t_863_);
lean_dec(v_t_863_);
lean_dec(v_k_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object* v_as_866_, size_t v_sz_867_, size_t v_i_868_, lean_object* v_b_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
lean_object* v___x_877_; 
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_866_, v_sz_867_, v_i_868_, v_b_869_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
return v___x_877_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object* v_as_878_, lean_object* v_sz_879_, lean_object* v_i_880_, lean_object* v_b_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_){
_start:
{
size_t v_sz_boxed_889_; size_t v_i_boxed_890_; lean_object* v_res_891_; 
v_sz_boxed_889_ = lean_unbox_usize(v_sz_879_);
lean_dec(v_sz_879_);
v_i_boxed_890_ = lean_unbox_usize(v_i_880_);
lean_dec(v_i_880_);
v_res_891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(v_as_878_, v_sz_boxed_889_, v_i_boxed_890_, v_b_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v_as_878_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_inst_892_, lean_object* v_a_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
lean_object* v___x_901_; 
v___x_901_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_inst_902_, lean_object* v_a_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_inst_902_, v_a_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_, v___y_908_, v___y_909_);
lean_dec(v___y_909_);
lean_dec_ref(v___y_908_);
lean_dec(v___y_907_);
lean_dec_ref(v___y_906_);
lean_dec(v___y_905_);
lean_dec(v___y_904_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object* v_mvarId_912_, lean_object* v___y_913_){
_start:
{
lean_object* v___x_915_; lean_object* v_mctx_916_; lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_915_ = lean_st_ref_get(v___y_913_);
v_mctx_916_ = lean_ctor_get(v___x_915_, 0);
lean_inc_ref(v_mctx_916_);
lean_dec(v___x_915_);
v___x_917_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_916_, v_mvarId_912_);
lean_dec_ref(v_mctx_916_);
v___x_918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
return v___x_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object* v_mvarId_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_919_, v___y_920_);
lean_dec(v___y_920_);
lean_dec(v_mvarId_919_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object* v_mvarId_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v___x_931_; 
v___x_931_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_923_, v___y_927_);
return v___x_931_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object* v_mvarId_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
lean_dec(v_mvarId_932_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object* v_a_941_, lean_object* v_as_942_, size_t v_sz_943_, size_t v_i_944_, lean_object* v_b_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_){
_start:
{
lean_object* v_a_954_; uint8_t v___x_958_; 
v___x_958_ = lean_usize_dec_lt(v_i_944_, v_sz_943_);
if (v___x_958_ == 0)
{
lean_object* v___x_959_; 
lean_dec_ref(v_a_941_);
v___x_959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_959_, 0, v_b_945_);
return v___x_959_;
}
else
{
lean_object* v_array_960_; lean_object* v_start_961_; lean_object* v_stop_962_; uint8_t v___x_963_; 
v_array_960_ = lean_ctor_get(v_b_945_, 0);
v_start_961_ = lean_ctor_get(v_b_945_, 1);
v_stop_962_ = lean_ctor_get(v_b_945_, 2);
v___x_963_ = lean_nat_dec_lt(v_start_961_, v_stop_962_);
if (v___x_963_ == 0)
{
lean_object* v___x_964_; 
lean_dec_ref(v_a_941_);
v___x_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_964_, 0, v_b_945_);
return v___x_964_;
}
else
{
lean_object* v___x_966_; uint8_t v_isShared_967_; uint8_t v_isSharedCheck_988_; 
lean_inc(v_stop_962_);
lean_inc(v_start_961_);
lean_inc_ref(v_array_960_);
v_isSharedCheck_988_ = !lean_is_exclusive(v_b_945_);
if (v_isSharedCheck_988_ == 0)
{
lean_object* v_unused_989_; lean_object* v_unused_990_; lean_object* v_unused_991_; 
v_unused_989_ = lean_ctor_get(v_b_945_, 2);
lean_dec(v_unused_989_);
v_unused_990_ = lean_ctor_get(v_b_945_, 1);
lean_dec(v_unused_990_);
v_unused_991_ = lean_ctor_get(v_b_945_, 0);
lean_dec(v_unused_991_);
v___x_966_ = v_b_945_;
v_isShared_967_ = v_isSharedCheck_988_;
goto v_resetjp_965_;
}
else
{
lean_dec(v_b_945_);
v___x_966_ = lean_box(0);
v_isShared_967_ = v_isSharedCheck_988_;
goto v_resetjp_965_;
}
v_resetjp_965_:
{
lean_object* v_lctx_968_; lean_object* v___x_969_; lean_object* v_a_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_974_; 
v_lctx_968_ = lean_ctor_get(v_a_941_, 1);
v___x_969_ = lean_array_fget(v_array_960_, v_start_961_);
v_a_970_ = lean_array_uget_borrowed(v_as_942_, v_i_944_);
v___x_971_ = lean_unsigned_to_nat(1u);
v___x_972_ = lean_nat_add(v_start_961_, v___x_971_);
lean_dec(v_start_961_);
if (v_isShared_967_ == 0)
{
lean_ctor_set(v___x_966_, 1, v___x_972_);
v___x_974_ = v___x_966_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_array_960_);
lean_ctor_set(v_reuseFailAlloc_987_, 1, v___x_972_);
lean_ctor_set(v_reuseFailAlloc_987_, 2, v_stop_962_);
v___x_974_ = v_reuseFailAlloc_987_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
lean_object* v___x_975_; uint8_t v___x_976_; uint8_t v___x_977_; 
lean_inc_ref(v_lctx_968_);
v___x_975_ = l_Lean_LocalContext_getFVar_x21(v_lctx_968_, v_a_970_);
v___x_976_ = 0;
v___x_977_ = l_Lean_LocalDecl_isLet(v___x_975_, v___x_976_);
lean_dec_ref(v___x_975_);
if (v___x_977_ == 0)
{
lean_dec(v___x_969_);
v_a_954_ = v___x_974_;
goto v___jp_953_;
}
else
{
lean_object* v___x_978_; 
v___x_978_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v___x_969_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
if (lean_obj_tag(v___x_978_) == 0)
{
lean_dec_ref_known(v___x_978_, 1);
v_a_954_ = v___x_974_;
goto v___jp_953_;
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec_ref(v___x_974_);
lean_dec_ref(v_a_941_);
v_a_979_ = lean_ctor_get(v___x_978_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_978_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_978_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
}
}
}
v___jp_953_:
{
size_t v___x_955_; size_t v___x_956_; 
v___x_955_ = ((size_t)1ULL);
v___x_956_ = lean_usize_add(v_i_944_, v___x_955_);
v_i_944_ = v___x_956_;
v_b_945_ = v_a_954_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object* v_a_992_, lean_object* v_as_993_, lean_object* v_sz_994_, lean_object* v_i_995_, lean_object* v_b_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
size_t v_sz_boxed_1004_; size_t v_i_boxed_1005_; lean_object* v_res_1006_; 
v_sz_boxed_1004_ = lean_unbox_usize(v_sz_994_);
lean_dec(v_sz_994_);
v_i_boxed_1005_ = lean_unbox_usize(v_i_995_);
lean_dec(v_i_995_);
v_res_1006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_992_, v_as_993_, v_sz_boxed_1004_, v_i_boxed_1005_, v_b_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v_as_993_);
return v_res_1006_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object* v_as_1007_, lean_object* v___y_1008_){
_start:
{
if (lean_obj_tag(v_as_1007_) == 0)
{
lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1010_ = lean_box(0);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v___x_1010_);
return v___x_1011_;
}
else
{
lean_object* v_head_1012_; lean_object* v_tail_1013_; lean_object* v___x_1014_; 
v_head_1012_ = lean_ctor_get(v_as_1007_, 0);
lean_inc(v_head_1012_);
v_tail_1013_ = lean_ctor_get(v_as_1007_, 1);
lean_inc(v_tail_1013_);
lean_dec_ref_known(v_as_1007_, 2);
v___x_1014_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_head_1012_, v___y_1008_);
if (lean_obj_tag(v___x_1014_) == 0)
{
lean_dec_ref_known(v___x_1014_, 1);
v_as_1007_ = v_tail_1013_;
goto _start;
}
else
{
lean_dec(v_tail_1013_);
return v___x_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object* v_as_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_){
_start:
{
lean_object* v_res_1019_; 
v_res_1019_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1016_, v___y_1017_);
lean_dec(v___y_1017_);
return v_res_1019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object* v_mvarId_1020_, lean_object* v_args_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_, lean_object* v_a_1024_, lean_object* v_a_1025_, lean_object* v_a_1026_, lean_object* v_a_1027_){
_start:
{
lean_object* v___x_1029_; lean_object* v_a_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1086_; 
v___x_1029_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1020_, v_a_1025_);
v_a_1030_ = lean_ctor_get(v___x_1029_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v___x_1029_);
if (v_isSharedCheck_1086_ == 0)
{
v___x_1032_ = v___x_1029_;
v_isShared_1033_ = v_isSharedCheck_1086_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_a_1030_);
lean_dec(v___x_1029_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1086_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
if (lean_obj_tag(v_a_1030_) == 1)
{
lean_object* v_val_1034_; lean_object* v_fvars_1035_; lean_object* v_mvarIdPending_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; uint8_t v___x_1039_; 
lean_del_object(v___x_1032_);
v_val_1034_ = lean_ctor_get(v_a_1030_, 0);
lean_inc(v_val_1034_);
lean_dec_ref_known(v_a_1030_, 1);
v_fvars_1035_ = lean_ctor_get(v_val_1034_, 0);
lean_inc_ref(v_fvars_1035_);
v_mvarIdPending_1036_ = lean_ctor_get(v_val_1034_, 1);
lean_inc(v_mvarIdPending_1036_);
lean_dec(v_val_1034_);
v___x_1037_ = lean_array_get_size(v_fvars_1035_);
v___x_1038_ = lean_array_get_size(v_args_1021_);
v___x_1039_ = lean_nat_dec_le(v___x_1037_, v___x_1038_);
if (v___x_1039_ == 0)
{
lean_object* v___x_1040_; 
lean_dec(v_mvarIdPending_1036_);
lean_dec_ref(v_fvars_1035_);
lean_dec_ref(v_args_1021_);
lean_inc(v_a_1022_);
v___x_1040_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_a_1022_, v_a_1025_);
if (lean_obj_tag(v___x_1040_) == 0)
{
lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1048_; 
v_isSharedCheck_1048_ = !lean_is_exclusive(v___x_1040_);
if (v_isSharedCheck_1048_ == 0)
{
lean_object* v_unused_1049_; 
v_unused_1049_ = lean_ctor_get(v___x_1040_, 0);
lean_dec(v_unused_1049_);
v___x_1042_ = v___x_1040_;
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
else
{
lean_dec(v___x_1040_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1048_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1046_; 
v___x_1044_ = lean_box(0);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1044_);
v___x_1046_ = v___x_1042_;
goto v_reusejp_1045_;
}
else
{
lean_object* v_reuseFailAlloc_1047_; 
v_reuseFailAlloc_1047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1047_, 0, v___x_1044_);
v___x_1046_ = v_reuseFailAlloc_1047_;
goto v_reusejp_1045_;
}
v_reusejp_1045_:
{
return v___x_1046_;
}
}
}
else
{
return v___x_1040_;
}
}
else
{
lean_object* v___x_1050_; 
v___x_1050_ = l_Lean_MVarId_getDecl(v_mvarIdPending_1036_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; size_t v_sz_1054_; size_t v___x_1055_; lean_object* v___x_1056_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v___x_1052_ = lean_unsigned_to_nat(0u);
v___x_1053_ = l_Array_toSubarray___redArg(v_args_1021_, v___x_1052_, v___x_1038_);
v_sz_1054_ = lean_array_size(v_fvars_1035_);
v___x_1055_ = ((size_t)0ULL);
v___x_1056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1051_, v_fvars_1035_, v_sz_1054_, v___x_1055_, v___x_1053_, v_a_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_);
lean_dec_ref(v_fvars_1035_);
if (lean_obj_tag(v___x_1056_) == 0)
{
lean_object* v___x_1058_; uint8_t v_isShared_1059_; uint8_t v_isSharedCheck_1064_; 
v_isSharedCheck_1064_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1064_ == 0)
{
lean_object* v_unused_1065_; 
v_unused_1065_ = lean_ctor_get(v___x_1056_, 0);
lean_dec(v_unused_1065_);
v___x_1058_ = v___x_1056_;
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
else
{
lean_dec(v___x_1056_);
v___x_1058_ = lean_box(0);
v_isShared_1059_ = v_isSharedCheck_1064_;
goto v_resetjp_1057_;
}
v_resetjp_1057_:
{
lean_object* v___x_1060_; lean_object* v___x_1062_; 
v___x_1060_ = lean_box(0);
if (v_isShared_1059_ == 0)
{
lean_ctor_set(v___x_1058_, 0, v___x_1060_);
v___x_1062_ = v___x_1058_;
goto v_reusejp_1061_;
}
else
{
lean_object* v_reuseFailAlloc_1063_; 
v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1063_, 0, v___x_1060_);
v___x_1062_ = v_reuseFailAlloc_1063_;
goto v_reusejp_1061_;
}
v_reusejp_1061_:
{
return v___x_1062_;
}
}
}
else
{
lean_object* v_a_1066_; lean_object* v___x_1068_; uint8_t v_isShared_1069_; uint8_t v_isSharedCheck_1073_; 
v_a_1066_ = lean_ctor_get(v___x_1056_, 0);
v_isSharedCheck_1073_ = !lean_is_exclusive(v___x_1056_);
if (v_isSharedCheck_1073_ == 0)
{
v___x_1068_ = v___x_1056_;
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
else
{
lean_inc(v_a_1066_);
lean_dec(v___x_1056_);
v___x_1068_ = lean_box(0);
v_isShared_1069_ = v_isSharedCheck_1073_;
goto v_resetjp_1067_;
}
v_resetjp_1067_:
{
lean_object* v___x_1071_; 
if (v_isShared_1069_ == 0)
{
v___x_1071_ = v___x_1068_;
goto v_reusejp_1070_;
}
else
{
lean_object* v_reuseFailAlloc_1072_; 
v_reuseFailAlloc_1072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_a_1066_);
v___x_1071_ = v_reuseFailAlloc_1072_;
goto v_reusejp_1070_;
}
v_reusejp_1070_:
{
return v___x_1071_;
}
}
}
}
else
{
lean_object* v_a_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1081_; 
lean_dec_ref(v_fvars_1035_);
lean_dec_ref(v_args_1021_);
v_a_1074_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1081_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1081_ == 0)
{
v___x_1076_ = v___x_1050_;
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_a_1074_);
lean_dec(v___x_1050_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1081_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1079_; 
if (v_isShared_1077_ == 0)
{
v___x_1079_ = v___x_1076_;
goto v_reusejp_1078_;
}
else
{
lean_object* v_reuseFailAlloc_1080_; 
v_reuseFailAlloc_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1080_, 0, v_a_1074_);
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
else
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_dec(v_a_1030_);
lean_dec_ref(v_args_1021_);
v___x_1082_ = lean_box(0);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 0, v___x_1082_);
v___x_1084_ = v___x_1032_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object* v_mvarId_1087_, lean_object* v_args_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_, lean_object* v_a_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1087_, v_args_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_);
lean_dec(v_a_1094_);
lean_dec_ref(v_a_1093_);
lean_dec(v_a_1092_);
lean_dec_ref(v_a_1091_);
lean_dec(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec(v_mvarId_1087_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object* v_as_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_, lean_object* v___y_1100_, lean_object* v___y_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1097_, v___y_1101_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object* v_as_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_res_1114_; 
v_res_1114_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
lean_dec(v___y_1112_);
lean_dec_ref(v___y_1111_);
lean_dec(v___y_1110_);
lean_dec_ref(v___y_1109_);
lean_dec(v___y_1108_);
lean_dec(v___y_1107_);
return v_res_1114_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object* v_e_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_, lean_object* v_a_1120_, lean_object* v_a_1121_, lean_object* v_a_1122_, lean_object* v_a_1123_){
_start:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1125_ = l_Lean_Expr_mvarId_x21(v_e_1117_);
v___x_1126_ = l_Lean_MVarId_findDecl_x3f___redArg(v___x_1125_, v_a_1121_);
if (lean_obj_tag(v___x_1126_) == 0)
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1157_; 
v_a_1127_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1129_ = v___x_1126_;
v_isShared_1130_ = v_isSharedCheck_1157_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1126_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1157_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
if (lean_obj_tag(v_a_1127_) == 1)
{
lean_object* v_val_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1155_; 
v_val_1131_ = lean_ctor_get(v_a_1127_, 0);
v_isSharedCheck_1155_ = !lean_is_exclusive(v_a_1127_);
if (v_isSharedCheck_1155_ == 0)
{
v___x_1133_ = v_a_1127_;
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_val_1131_);
lean_dec(v_a_1127_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1155_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
uint8_t v___x_1144_; 
v___x_1144_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1118_);
if (v___x_1144_ == 0)
{
lean_dec(v___x_1125_);
goto v___jp_1135_;
}
else
{
lean_object* v___x_1145_; lean_object* v___x_1146_; 
v___x_1145_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_1146_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v___x_1125_, v___x_1145_, v_a_1118_, v_a_1119_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
lean_dec(v___x_1125_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_dec_ref_known(v___x_1146_, 1);
goto v___jp_1135_;
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_del_object(v___x_1133_);
lean_dec(v_val_1131_);
lean_del_object(v___x_1129_);
lean_dec_ref(v_e_1117_);
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1146_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1146_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
v___jp_1135_:
{
lean_object* v_type_1136_; lean_object* v___x_1138_; 
v_type_1136_ = lean_ctor_get(v_val_1131_, 2);
lean_inc_ref(v_type_1136_);
lean_dec(v_val_1131_);
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 0, v_type_1136_);
v___x_1138_ = v___x_1133_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_type_1136_);
v___x_1138_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1139_; lean_object* v___x_1141_; 
v___x_1139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1139_, 0, v_e_1117_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v___x_1139_);
v___x_1141_ = v___x_1129_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v___x_1139_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
else
{
lean_object* v___x_1156_; 
lean_del_object(v___x_1129_);
lean_dec(v_a_1127_);
lean_dec_ref(v_e_1117_);
v___x_1156_ = l_Lean_Meta_throwUnknownMVar___redArg(v___x_1125_, v_a_1120_, v_a_1121_, v_a_1122_, v_a_1123_);
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1165_; 
lean_dec(v___x_1125_);
lean_dec_ref(v_e_1117_);
v_a_1158_ = lean_ctor_get(v___x_1126_, 0);
v_isSharedCheck_1165_ = !lean_is_exclusive(v___x_1126_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1160_ = v___x_1126_;
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_a_1158_);
lean_dec(v___x_1126_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1165_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1163_; 
if (v_isShared_1161_ == 0)
{
v___x_1163_ = v___x_1160_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object* v_e_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_, lean_object* v_a_1170_, lean_object* v_a_1171_, lean_object* v_a_1172_, lean_object* v_a_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1166_, v_a_1167_, v_a_1168_, v_a_1169_, v_a_1170_, v_a_1171_, v_a_1172_);
lean_dec(v_a_1172_);
lean_dec_ref(v_a_1171_);
lean_dec(v_a_1170_);
lean_dec_ref(v_a_1169_);
lean_dec(v_a_1168_);
lean_dec(v_a_1167_);
return v_res_1174_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1175_; 
v___x_1175_ = l_instMonadEIO(lean_box(0));
return v___x_1175_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object* v_msg_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_, lean_object* v___y_1184_, lean_object* v___y_1185_, lean_object* v___y_1186_){
_start:
{
lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v_toApplicative_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1253_; 
v___x_1188_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0);
v___x_1189_ = l_StateRefT_x27_instMonad___redArg(v___x_1188_);
v_toApplicative_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1253_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1253_ == 0)
{
lean_object* v_unused_1254_; 
v_unused_1254_ = lean_ctor_get(v___x_1189_, 1);
lean_dec(v_unused_1254_);
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1253_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_toApplicative_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1253_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v_toFunctor_1194_; lean_object* v_toSeq_1195_; lean_object* v_toSeqLeft_1196_; lean_object* v_toSeqRight_1197_; lean_object* v___x_1199_; uint8_t v_isShared_1200_; uint8_t v_isSharedCheck_1251_; 
v_toFunctor_1194_ = lean_ctor_get(v_toApplicative_1190_, 0);
v_toSeq_1195_ = lean_ctor_get(v_toApplicative_1190_, 2);
v_toSeqLeft_1196_ = lean_ctor_get(v_toApplicative_1190_, 3);
v_toSeqRight_1197_ = lean_ctor_get(v_toApplicative_1190_, 4);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_toApplicative_1190_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v_toApplicative_1190_, 1);
lean_dec(v_unused_1252_);
v___x_1199_ = v_toApplicative_1190_;
v_isShared_1200_ = v_isSharedCheck_1251_;
goto v_resetjp_1198_;
}
else
{
lean_inc(v_toSeqRight_1197_);
lean_inc(v_toSeqLeft_1196_);
lean_inc(v_toSeq_1195_);
lean_inc(v_toFunctor_1194_);
lean_dec(v_toApplicative_1190_);
v___x_1199_ = lean_box(0);
v_isShared_1200_ = v_isSharedCheck_1251_;
goto v_resetjp_1198_;
}
v_resetjp_1198_:
{
lean_object* v___f_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1205_; lean_object* v___f_1206_; lean_object* v___f_1207_; lean_object* v___f_1208_; lean_object* v___x_1210_; 
v___f_1201_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1));
v___f_1202_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1194_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toFunctor_1194_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toFunctor_1194_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___f_1203_);
lean_ctor_set(v___x_1205_, 1, v___f_1204_);
v___f_1206_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1206_, 0, v_toSeqRight_1197_);
v___f_1207_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1207_, 0, v_toSeqLeft_1196_);
v___f_1208_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1208_, 0, v_toSeq_1195_);
if (v_isShared_1200_ == 0)
{
lean_ctor_set(v___x_1199_, 4, v___f_1206_);
lean_ctor_set(v___x_1199_, 3, v___f_1207_);
lean_ctor_set(v___x_1199_, 2, v___f_1208_);
lean_ctor_set(v___x_1199_, 1, v___f_1201_);
lean_ctor_set(v___x_1199_, 0, v___x_1205_);
v___x_1210_ = v___x_1199_;
goto v_reusejp_1209_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v___x_1205_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___f_1201_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v___f_1208_);
lean_ctor_set(v_reuseFailAlloc_1250_, 3, v___f_1207_);
lean_ctor_set(v_reuseFailAlloc_1250_, 4, v___f_1206_);
v___x_1210_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1209_;
}
v_reusejp_1209_:
{
lean_object* v___x_1212_; 
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___f_1202_);
lean_ctor_set(v___x_1192_, 0, v___x_1210_);
v___x_1212_ = v___x_1192_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v___x_1210_);
lean_ctor_set(v_reuseFailAlloc_1249_, 1, v___f_1202_);
v___x_1212_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
lean_object* v___x_1213_; lean_object* v_toApplicative_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1247_; 
v___x_1213_ = l_StateRefT_x27_instMonad___redArg(v___x_1212_);
v_toApplicative_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v___x_1213_, 1);
lean_dec(v_unused_1248_);
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1247_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_toApplicative_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1247_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v_toFunctor_1218_; lean_object* v_toSeq_1219_; lean_object* v_toSeqLeft_1220_; lean_object* v_toSeqRight_1221_; lean_object* v___x_1223_; uint8_t v_isShared_1224_; uint8_t v_isSharedCheck_1245_; 
v_toFunctor_1218_ = lean_ctor_get(v_toApplicative_1214_, 0);
v_toSeq_1219_ = lean_ctor_get(v_toApplicative_1214_, 2);
v_toSeqLeft_1220_ = lean_ctor_get(v_toApplicative_1214_, 3);
v_toSeqRight_1221_ = lean_ctor_get(v_toApplicative_1214_, 4);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_toApplicative_1214_);
if (v_isSharedCheck_1245_ == 0)
{
lean_object* v_unused_1246_; 
v_unused_1246_ = lean_ctor_get(v_toApplicative_1214_, 1);
lean_dec(v_unused_1246_);
v___x_1223_ = v_toApplicative_1214_;
v_isShared_1224_ = v_isSharedCheck_1245_;
goto v_resetjp_1222_;
}
else
{
lean_inc(v_toSeqRight_1221_);
lean_inc(v_toSeqLeft_1220_);
lean_inc(v_toSeq_1219_);
lean_inc(v_toFunctor_1218_);
lean_dec(v_toApplicative_1214_);
v___x_1223_ = lean_box(0);
v_isShared_1224_ = v_isSharedCheck_1245_;
goto v_resetjp_1222_;
}
v_resetjp_1222_:
{
lean_object* v___f_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1229_; lean_object* v___f_1230_; lean_object* v___f_1231_; lean_object* v___f_1232_; lean_object* v___x_1234_; 
v___f_1225_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3));
v___f_1226_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1218_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toFunctor_1218_);
v___f_1228_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1228_, 0, v_toFunctor_1218_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___f_1227_);
lean_ctor_set(v___x_1229_, 1, v___f_1228_);
v___f_1230_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1230_, 0, v_toSeqRight_1221_);
v___f_1231_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1231_, 0, v_toSeqLeft_1220_);
v___f_1232_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1232_, 0, v_toSeq_1219_);
if (v_isShared_1224_ == 0)
{
lean_ctor_set(v___x_1223_, 4, v___f_1230_);
lean_ctor_set(v___x_1223_, 3, v___f_1231_);
lean_ctor_set(v___x_1223_, 2, v___f_1232_);
lean_ctor_set(v___x_1223_, 1, v___f_1225_);
lean_ctor_set(v___x_1223_, 0, v___x_1229_);
v___x_1234_ = v___x_1223_;
goto v_reusejp_1233_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1229_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___f_1225_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v___f_1232_);
lean_ctor_set(v_reuseFailAlloc_1244_, 3, v___f_1231_);
lean_ctor_set(v_reuseFailAlloc_1244_, 4, v___f_1230_);
v___x_1234_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1233_;
}
v_reusejp_1233_:
{
lean_object* v___x_1236_; 
if (v_isShared_1217_ == 0)
{
lean_ctor_set(v___x_1216_, 1, v___f_1226_);
lean_ctor_set(v___x_1216_, 0, v___x_1234_);
v___x_1236_ = v___x_1216_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1243_; 
v_reuseFailAlloc_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1243_, 0, v___x_1234_);
lean_ctor_set(v_reuseFailAlloc_1243_, 1, v___f_1226_);
v___x_1236_ = v_reuseFailAlloc_1243_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___f_1240_; lean_object* v___x_1519__overap_1241_; lean_object* v___x_1242_; 
v___x_1237_ = l_StateRefT_x27_instMonad___redArg(v___x_1236_);
v___x_1238_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1239_ = l_instInhabitedOfMonad___redArg(v___x_1237_, v___x_1238_);
v___f_1240_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1240_, 0, v___x_1239_);
v___x_1519__overap_1241_ = lean_panic_fn_borrowed(v___f_1240_, v_msg_1180_);
lean_dec_ref(v___f_1240_);
lean_inc(v___y_1186_);
lean_inc_ref(v___y_1185_);
lean_inc(v___y_1184_);
lean_inc_ref(v___y_1183_);
lean_inc(v___y_1182_);
lean_inc(v___y_1181_);
v___x_1242_ = lean_apply_7(v___x_1519__overap_1241_, v___y_1181_, v___y_1182_, v___y_1183_, v___y_1184_, v___y_1185_, v___y_1186_, lean_box(0));
return v___x_1242_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object* v_msg_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_){
_start:
{
lean_object* v_res_1263_; 
v_res_1263_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1255_, v___y_1256_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, v___y_1261_);
lean_dec(v___y_1261_);
lean_dec_ref(v___y_1260_);
lean_dec(v___y_1259_);
lean_dec_ref(v___y_1258_);
lean_dec(v___y_1257_);
lean_dec(v___y_1256_);
return v_res_1263_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1264_; 
v___x_1264_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1264_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1265_; lean_object* v___x_1266_; 
v___x_1265_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1266_, 0, v___x_1265_);
return v___x_1266_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1267_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1268_ = lean_unsigned_to_nat(0u);
v___x_1269_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1269_, 0, v___x_1268_);
lean_ctor_set(v___x_1269_, 1, v___x_1268_);
lean_ctor_set(v___x_1269_, 2, v___x_1268_);
lean_ctor_set(v___x_1269_, 3, v___x_1268_);
lean_ctor_set(v___x_1269_, 4, v___x_1267_);
lean_ctor_set(v___x_1269_, 5, v___x_1267_);
lean_ctor_set(v___x_1269_, 6, v___x_1267_);
lean_ctor_set(v___x_1269_, 7, v___x_1267_);
lean_ctor_set(v___x_1269_, 8, v___x_1267_);
lean_ctor_set(v___x_1269_, 9, v___x_1267_);
return v___x_1269_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1270_ = lean_unsigned_to_nat(32u);
v___x_1271_ = lean_mk_empty_array_with_capacity(v___x_1270_);
v___x_1272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1271_);
return v___x_1272_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1273_ = ((size_t)5ULL);
v___x_1274_ = lean_unsigned_to_nat(0u);
v___x_1275_ = lean_unsigned_to_nat(32u);
v___x_1276_ = lean_mk_empty_array_with_capacity(v___x_1275_);
v___x_1277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1278_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1276_);
lean_ctor_set(v___x_1278_, 2, v___x_1274_);
lean_ctor_set(v___x_1278_, 3, v___x_1274_);
lean_ctor_set_usize(v___x_1278_, 4, v___x_1273_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1279_ = lean_box(1);
v___x_1280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1281_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1282_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1282_, 0, v___x_1281_);
lean_ctor_set(v___x_1282_, 1, v___x_1280_);
lean_ctor_set(v___x_1282_, 2, v___x_1279_);
return v___x_1282_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1285_ = l_Lean_stringToMessageData(v___x_1284_);
return v___x_1285_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1288_ = l_Lean_stringToMessageData(v___x_1287_);
return v___x_1288_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1291_ = l_Lean_stringToMessageData(v___x_1290_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1293_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1294_ = l_Lean_stringToMessageData(v___x_1293_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1297_ = l_Lean_stringToMessageData(v___x_1296_);
return v___x_1297_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1299_; lean_object* v___x_1300_; 
v___x_1299_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1300_ = l_Lean_stringToMessageData(v___x_1299_);
return v___x_1300_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; 
v___x_1302_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1303_ = l_Lean_stringToMessageData(v___x_1302_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1304_, lean_object* v_declHint_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___x_1308_; lean_object* v_env_1309_; uint8_t v___y_1311_; uint8_t v___x_1367_; uint8_t v___x_1368_; 
v___x_1308_ = lean_st_ref_get(v___y_1306_);
v_env_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc_ref(v_env_1309_);
lean_dec(v___x_1308_);
v___x_1367_ = l_Lean_Name_isAnonymous(v_declHint_1305_);
v___x_1368_ = lean_bool_not(v___x_1367_);
if (v___x_1368_ == 0)
{
v___y_1311_ = v___x_1368_;
goto v___jp_1310_;
}
else
{
uint8_t v_isExporting_1369_; 
v_isExporting_1369_ = lean_ctor_get_uint8(v_env_1309_, sizeof(void*)*8);
v___y_1311_ = v_isExporting_1369_;
goto v___jp_1310_;
}
v___jp_1310_:
{
if (v___y_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v_env_1309_);
lean_dec(v_declHint_1305_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_msg_1304_);
return v___x_1312_;
}
else
{
uint8_t v___x_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1313_ = 0;
lean_inc_ref(v_env_1309_);
v___x_1314_ = l_Lean_Environment_setExporting(v_env_1309_, v___x_1313_);
lean_inc(v_declHint_1305_);
lean_inc_ref(v___x_1314_);
v___x_1315_ = l_Lean_Environment_contains(v___x_1314_, v_declHint_1305_, v___y_1311_);
if (v___x_1315_ == 0)
{
lean_object* v___x_1316_; 
lean_dec_ref(v___x_1314_);
lean_dec_ref(v_env_1309_);
lean_dec(v_declHint_1305_);
v___x_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1316_, 0, v_msg_1304_);
return v___x_1316_;
}
else
{
lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v_c_1322_; lean_object* v___x_1323_; 
v___x_1317_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1318_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1319_ = l_Lean_Options_empty;
v___x_1320_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1314_);
lean_ctor_set(v___x_1320_, 1, v___x_1317_);
lean_ctor_set(v___x_1320_, 2, v___x_1318_);
lean_ctor_set(v___x_1320_, 3, v___x_1319_);
lean_inc(v_declHint_1305_);
v___x_1321_ = l_Lean_MessageData_ofConstName(v_declHint_1305_, v___x_1313_);
v_c_1322_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1322_, 0, v___x_1320_);
lean_ctor_set(v_c_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1309_, v_declHint_1305_);
if (lean_obj_tag(v___x_1323_) == 0)
{
lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
lean_dec_ref(v_env_1309_);
lean_dec(v_declHint_1305_);
v___x_1324_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
lean_ctor_set(v___x_1325_, 1, v_c_1322_);
v___x_1326_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1325_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = l_Lean_MessageData_note(v___x_1327_);
v___x_1329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1329_, 0, v_msg_1304_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
v___x_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1330_, 0, v___x_1329_);
return v___x_1330_;
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1366_; 
v_val_1331_ = lean_ctor_get(v___x_1323_, 0);
v_isSharedCheck_1366_ = !lean_is_exclusive(v___x_1323_);
if (v_isSharedCheck_1366_ == 0)
{
v___x_1333_ = v___x_1323_;
v_isShared_1334_ = v_isSharedCheck_1366_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_val_1331_);
lean_dec(v___x_1323_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1366_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v_mod_1338_; uint8_t v___x_1339_; 
v___x_1335_ = lean_box(0);
v___x_1336_ = l_Lean_Environment_header(v_env_1309_);
lean_dec_ref(v_env_1309_);
v___x_1337_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1336_);
v_mod_1338_ = lean_array_get(v___x_1335_, v___x_1337_, v_val_1331_);
lean_dec(v_val_1331_);
lean_dec_ref(v___x_1337_);
v___x_1339_ = l_Lean_isPrivateName(v_declHint_1305_);
lean_dec(v_declHint_1305_);
if (v___x_1339_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1340_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1341_, 0, v___x_1340_);
lean_ctor_set(v___x_1341_, 1, v_c_1322_);
v___x_1342_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1343_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1343_, 0, v___x_1341_);
lean_ctor_set(v___x_1343_, 1, v___x_1342_);
v___x_1344_ = l_Lean_MessageData_ofName(v_mod_1338_);
v___x_1345_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1343_);
lean_ctor_set(v___x_1345_, 1, v___x_1344_);
v___x_1346_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1347_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1347_, 0, v___x_1345_);
lean_ctor_set(v___x_1347_, 1, v___x_1346_);
v___x_1348_ = l_Lean_MessageData_note(v___x_1347_);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v_msg_1304_);
lean_ctor_set(v___x_1349_, 1, v___x_1348_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1349_);
v___x_1351_ = v___x_1333_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v___x_1349_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1364_; 
v___x_1353_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1354_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1354_, 0, v___x_1353_);
lean_ctor_set(v___x_1354_, 1, v_c_1322_);
v___x_1355_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1356_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1354_);
lean_ctor_set(v___x_1356_, 1, v___x_1355_);
v___x_1357_ = l_Lean_MessageData_ofName(v_mod_1338_);
v___x_1358_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1356_);
lean_ctor_set(v___x_1358_, 1, v___x_1357_);
v___x_1359_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1360_, 0, v___x_1358_);
lean_ctor_set(v___x_1360_, 1, v___x_1359_);
v___x_1361_ = l_Lean_MessageData_note(v___x_1360_);
v___x_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1362_, 0, v_msg_1304_);
lean_ctor_set(v___x_1362_, 1, v___x_1361_);
if (v_isShared_1334_ == 0)
{
lean_ctor_set_tag(v___x_1333_, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1362_);
v___x_1364_ = v___x_1333_;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1370_, lean_object* v_declHint_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1370_, v_declHint_1371_, v___y_1372_);
lean_dec(v___y_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1375_, lean_object* v_declHint_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_){
_start:
{
lean_object* v___x_1384_; lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1394_; 
v___x_1384_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1375_, v_declHint_1376_, v___y_1382_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1394_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1392_; 
v___x_1389_ = l_Lean_unknownIdentifierMessageTag;
v___x_1390_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v_a_1385_);
if (v_isShared_1388_ == 0)
{
lean_ctor_set(v___x_1387_, 0, v___x_1390_);
v___x_1392_ = v___x_1387_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v___x_1390_);
v___x_1392_ = v_reuseFailAlloc_1393_;
goto v_reusejp_1391_;
}
v_reusejp_1391_:
{
return v___x_1392_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1395_, lean_object* v_declHint_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1395_, v_declHint_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec(v___y_1397_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
lean_object* v___x_1411_; lean_object* v_env_1412_; lean_object* v___x_1413_; lean_object* v_mctx_1414_; lean_object* v_lctx_1415_; lean_object* v_options_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1411_ = lean_st_ref_get(v___y_1409_);
v_env_1412_ = lean_ctor_get(v___x_1411_, 0);
lean_inc_ref(v_env_1412_);
lean_dec(v___x_1411_);
v___x_1413_ = lean_st_ref_get(v___y_1407_);
v_mctx_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc_ref(v_mctx_1414_);
lean_dec(v___x_1413_);
v_lctx_1415_ = lean_ctor_get(v___y_1406_, 2);
v_options_1416_ = lean_ctor_get(v___y_1408_, 2);
lean_inc_ref(v_options_1416_);
lean_inc_ref(v_lctx_1415_);
v___x_1417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1417_, 0, v_env_1412_);
lean_ctor_set(v___x_1417_, 1, v_mctx_1414_);
lean_ctor_set(v___x_1417_, 2, v_lctx_1415_);
lean_ctor_set(v___x_1417_, 3, v_options_1416_);
v___x_1418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v_msgData_1405_);
v___x_1419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
return v___x_1419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_ref_1433_; lean_object* v___x_1434_; lean_object* v_a_1435_; lean_object* v___x_1437_; uint8_t v_isShared_1438_; uint8_t v_isSharedCheck_1443_; 
v_ref_1433_ = lean_ctor_get(v___y_1430_, 5);
v___x_1434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v___x_1434_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1437_ = v___x_1434_;
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
else
{
lean_inc(v_a_1435_);
lean_dec(v___x_1434_);
v___x_1437_ = lean_box(0);
v_isShared_1438_ = v_isSharedCheck_1443_;
goto v_resetjp_1436_;
}
v_resetjp_1436_:
{
lean_object* v___x_1439_; lean_object* v___x_1441_; 
lean_inc(v_ref_1433_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v_ref_1433_);
lean_ctor_set(v___x_1439_, 1, v_a_1435_);
if (v_isShared_1438_ == 0)
{
lean_ctor_set_tag(v___x_1437_, 1);
lean_ctor_set(v___x_1437_, 0, v___x_1439_);
v___x_1441_ = v___x_1437_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1439_);
v___x_1441_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
return v___x_1441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1451_, lean_object* v_msg_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
lean_object* v_fileName_1460_; lean_object* v_fileMap_1461_; lean_object* v_options_1462_; lean_object* v_currRecDepth_1463_; lean_object* v_maxRecDepth_1464_; lean_object* v_ref_1465_; lean_object* v_currNamespace_1466_; lean_object* v_openDecls_1467_; lean_object* v_initHeartbeats_1468_; lean_object* v_maxHeartbeats_1469_; lean_object* v_quotContext_1470_; lean_object* v_currMacroScope_1471_; uint8_t v_diag_1472_; lean_object* v_cancelTk_x3f_1473_; uint8_t v_suppressElabErrors_1474_; lean_object* v_inheritedTraceOptions_1475_; lean_object* v_ref_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v_fileName_1460_ = lean_ctor_get(v___y_1457_, 0);
v_fileMap_1461_ = lean_ctor_get(v___y_1457_, 1);
v_options_1462_ = lean_ctor_get(v___y_1457_, 2);
v_currRecDepth_1463_ = lean_ctor_get(v___y_1457_, 3);
v_maxRecDepth_1464_ = lean_ctor_get(v___y_1457_, 4);
v_ref_1465_ = lean_ctor_get(v___y_1457_, 5);
v_currNamespace_1466_ = lean_ctor_get(v___y_1457_, 6);
v_openDecls_1467_ = lean_ctor_get(v___y_1457_, 7);
v_initHeartbeats_1468_ = lean_ctor_get(v___y_1457_, 8);
v_maxHeartbeats_1469_ = lean_ctor_get(v___y_1457_, 9);
v_quotContext_1470_ = lean_ctor_get(v___y_1457_, 10);
v_currMacroScope_1471_ = lean_ctor_get(v___y_1457_, 11);
v_diag_1472_ = lean_ctor_get_uint8(v___y_1457_, sizeof(void*)*14);
v_cancelTk_x3f_1473_ = lean_ctor_get(v___y_1457_, 12);
v_suppressElabErrors_1474_ = lean_ctor_get_uint8(v___y_1457_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1475_ = lean_ctor_get(v___y_1457_, 13);
v_ref_1476_ = l_Lean_replaceRef(v_ref_1451_, v_ref_1465_);
lean_inc_ref(v_inheritedTraceOptions_1475_);
lean_inc(v_cancelTk_x3f_1473_);
lean_inc(v_currMacroScope_1471_);
lean_inc(v_quotContext_1470_);
lean_inc(v_maxHeartbeats_1469_);
lean_inc(v_initHeartbeats_1468_);
lean_inc(v_openDecls_1467_);
lean_inc(v_currNamespace_1466_);
lean_inc(v_maxRecDepth_1464_);
lean_inc(v_currRecDepth_1463_);
lean_inc_ref(v_options_1462_);
lean_inc_ref(v_fileMap_1461_);
lean_inc_ref(v_fileName_1460_);
v___x_1477_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1477_, 0, v_fileName_1460_);
lean_ctor_set(v___x_1477_, 1, v_fileMap_1461_);
lean_ctor_set(v___x_1477_, 2, v_options_1462_);
lean_ctor_set(v___x_1477_, 3, v_currRecDepth_1463_);
lean_ctor_set(v___x_1477_, 4, v_maxRecDepth_1464_);
lean_ctor_set(v___x_1477_, 5, v_ref_1476_);
lean_ctor_set(v___x_1477_, 6, v_currNamespace_1466_);
lean_ctor_set(v___x_1477_, 7, v_openDecls_1467_);
lean_ctor_set(v___x_1477_, 8, v_initHeartbeats_1468_);
lean_ctor_set(v___x_1477_, 9, v_maxHeartbeats_1469_);
lean_ctor_set(v___x_1477_, 10, v_quotContext_1470_);
lean_ctor_set(v___x_1477_, 11, v_currMacroScope_1471_);
lean_ctor_set(v___x_1477_, 12, v_cancelTk_x3f_1473_);
lean_ctor_set(v___x_1477_, 13, v_inheritedTraceOptions_1475_);
lean_ctor_set_uint8(v___x_1477_, sizeof(void*)*14, v_diag_1472_);
lean_ctor_set_uint8(v___x_1477_, sizeof(void*)*14 + 1, v_suppressElabErrors_1474_);
v___x_1478_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1452_, v___y_1455_, v___y_1456_, v___x_1477_, v___y_1458_);
lean_dec_ref_known(v___x_1477_, 14);
return v___x_1478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1479_, lean_object* v_msg_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1479_, v_msg_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec(v___y_1481_);
lean_dec(v_ref_1479_);
return v_res_1488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1489_, lean_object* v_msg_1490_, lean_object* v_declHint_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_){
_start:
{
lean_object* v___x_1499_; lean_object* v_a_1500_; lean_object* v___x_1501_; 
v___x_1499_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1490_, v_declHint_1491_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
v_a_1500_ = lean_ctor_get(v___x_1499_, 0);
lean_inc(v_a_1500_);
lean_dec_ref(v___x_1499_);
v___x_1501_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1489_, v_a_1500_, v___y_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1502_, lean_object* v_msg_1503_, lean_object* v_declHint_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
lean_object* v_res_1512_; 
v_res_1512_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1502_, v_msg_1503_, v_declHint_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___y_1510_);
lean_dec_ref(v___y_1509_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec(v_ref_1502_);
return v_res_1512_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1518_ = l_Lean_stringToMessageData(v___x_1517_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1519_, lean_object* v_constName_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v___x_1528_; uint8_t v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1528_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1529_ = 0;
lean_inc(v_constName_1520_);
v___x_1530_ = l_Lean_MessageData_ofConstName(v_constName_1520_, v___x_1529_);
v___x_1531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1528_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
v___x_1532_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1531_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
v___x_1534_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1519_, v___x_1533_, v_constName_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
return v___x_1534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1535_, lean_object* v_constName_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1535_, v_constName_1536_, v___y_1537_, v___y_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec_ref(v___y_1539_);
lean_dec(v___y_1538_);
lean_dec(v___y_1537_);
lean_dec(v_ref_1535_);
return v_res_1544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v_ref_1553_; lean_object* v___x_1554_; 
v_ref_1553_ = lean_ctor_get(v___y_1550_, 5);
v___x_1554_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1553_, v_constName_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec(v___y_1556_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v___x_1572_; lean_object* v_env_1573_; uint8_t v___x_1574_; lean_object* v___x_1575_; 
v___x_1572_ = lean_st_ref_get(v___y_1570_);
v_env_1573_ = lean_ctor_get(v___x_1572_, 0);
lean_inc_ref(v_env_1573_);
lean_dec(v___x_1572_);
v___x_1574_ = 0;
lean_inc(v_constName_1564_);
v___x_1575_ = l_Lean_Environment_findConstVal_x3f(v_env_1573_, v_constName_1564_, v___x_1574_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_, v___y_1570_);
return v___x_1576_;
}
else
{
lean_object* v_val_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_constName_1564_);
v_val_1577_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1575_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_val_1577_);
lean_dec(v___x_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
lean_ctor_set_tag(v___x_1579_, 0);
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_val_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
lean_object* v_res_1593_; 
v_res_1593_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
lean_dec(v___y_1591_);
lean_dec_ref(v___y_1590_);
lean_dec(v___y_1589_);
lean_dec_ref(v___y_1588_);
lean_dec(v___y_1587_);
lean_dec(v___y_1586_);
return v_res_1593_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1597_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1598_ = lean_unsigned_to_nat(35u);
v___x_1599_ = lean_unsigned_to_nat(203u);
v___x_1600_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1601_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1602_ = l_mkPanicMessageWithDecl(v___x_1601_, v___x_1600_, v___x_1599_, v___x_1598_, v___x_1597_);
return v___x_1602_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
if (lean_obj_tag(v_e_1603_) == 4)
{
lean_object* v_declName_1611_; lean_object* v_us_1612_; lean_object* v___x_1613_; 
v_declName_1611_ = lean_ctor_get(v_e_1603_, 0);
v_us_1612_ = lean_ctor_get(v_e_1603_, 1);
lean_inc(v_declName_1611_);
v___x_1613_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1611_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; lean_object* v_levelParams_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; uint8_t v___x_1618_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref_known(v___x_1613_, 1);
v_levelParams_1615_ = lean_ctor_get(v_a_1614_, 1);
v___x_1616_ = l_List_lengthTR___redArg(v_levelParams_1615_);
v___x_1617_ = l_List_lengthTR___redArg(v_us_1612_);
v___x_1618_ = lean_nat_dec_eq(v___x_1616_, v___x_1617_);
lean_dec(v___x_1617_);
lean_dec(v___x_1616_);
if (v___x_1618_ == 0)
{
lean_object* v___x_1619_; 
lean_inc(v_us_1612_);
lean_inc(v_declName_1611_);
lean_dec(v_a_1614_);
lean_dec_ref_known(v_e_1603_, 2);
v___x_1619_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1611_, v_us_1612_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v___x_1619_;
}
else
{
lean_object* v___x_1620_; 
lean_inc(v_us_1612_);
v___x_1620_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1614_, v_us_1612_, v___y_1609_);
if (lean_obj_tag(v___x_1620_) == 0)
{
lean_object* v_a_1621_; lean_object* v___x_1623_; uint8_t v_isShared_1624_; uint8_t v_isSharedCheck_1630_; 
v_a_1621_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1623_ = v___x_1620_;
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
else
{
lean_inc(v_a_1621_);
lean_dec(v___x_1620_);
v___x_1623_ = lean_box(0);
v_isShared_1624_ = v_isSharedCheck_1630_;
goto v_resetjp_1622_;
}
v_resetjp_1622_:
{
lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1625_, 0, v_a_1621_);
v___x_1626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1626_, 0, v_e_1603_);
lean_ctor_set(v___x_1626_, 1, v___x_1625_);
if (v_isShared_1624_ == 0)
{
lean_ctor_set(v___x_1623_, 0, v___x_1626_);
v___x_1628_ = v___x_1623_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v___x_1626_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
return v___x_1628_;
}
}
}
else
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1638_; 
lean_dec_ref_known(v_e_1603_, 2);
v_a_1631_ = lean_ctor_get(v___x_1620_, 0);
v_isSharedCheck_1638_ = !lean_is_exclusive(v___x_1620_);
if (v_isSharedCheck_1638_ == 0)
{
v___x_1633_ = v___x_1620_;
v_isShared_1634_ = v_isSharedCheck_1638_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1620_);
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
}
else
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1646_; 
lean_dec_ref_known(v_e_1603_, 2);
v_a_1639_ = lean_ctor_get(v___x_1613_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1613_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1641_ = v___x_1613_;
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1613_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1646_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1644_; 
if (v_isShared_1642_ == 0)
{
v___x_1644_ = v___x_1641_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v_a_1639_);
v___x_1644_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
return v___x_1644_;
}
}
}
}
else
{
lean_object* v___x_1647_; lean_object* v___x_1648_; 
lean_dec_ref(v_e_1603_);
v___x_1647_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1648_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1647_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v___x_1648_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_, lean_object* v___y_1655_, lean_object* v___y_1656_){
_start:
{
lean_object* v_res_1657_; 
v_res_1657_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_);
lean_dec(v___y_1655_);
lean_dec_ref(v___y_1654_);
lean_dec(v___y_1653_);
lean_dec_ref(v___y_1652_);
lean_dec(v___y_1651_);
lean_dec(v___y_1650_);
return v_res_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_, lean_object* v_a_1664_){
_start:
{
lean_object* v___y_1666_; lean_object* v___x_1667_; 
lean_inc_ref(v_e_1658_);
v___y_1666_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1666_, 0, v_e_1658_);
v___x_1667_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1658_, v___y_1666_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_, v_a_1663_, v_a_1664_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1668_, lean_object* v_a_1669_, lean_object* v_a_1670_, lean_object* v_a_1671_, lean_object* v_a_1672_, lean_object* v_a_1673_, lean_object* v_a_1674_, lean_object* v_a_1675_){
_start:
{
lean_object* v_res_1676_; 
v_res_1676_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1668_, v_a_1669_, v_a_1670_, v_a_1671_, v_a_1672_, v_a_1673_, v_a_1674_);
lean_dec(v_a_1674_);
lean_dec_ref(v_a_1673_);
lean_dec(v_a_1672_);
lean_dec_ref(v_a_1671_);
lean_dec(v_a_1670_);
lean_dec(v_a_1669_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1677_, lean_object* v_constName_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
v___x_1686_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1687_, lean_object* v_constName_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1687_, v_constName_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
lean_dec(v___y_1694_);
lean_dec_ref(v___y_1693_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec(v___y_1689_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1697_, lean_object* v_ref_1698_, lean_object* v_constName_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v___x_1707_; 
v___x_1707_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1698_, v_constName_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_);
return v___x_1707_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1708_, lean_object* v_ref_1709_, lean_object* v_constName_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_){
_start:
{
lean_object* v_res_1718_; 
v_res_1718_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1708_, v_ref_1709_, v_constName_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec_ref(v___y_1713_);
lean_dec(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec(v_ref_1709_);
return v_res_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1719_, lean_object* v_ref_1720_, lean_object* v_msg_1721_, lean_object* v_declHint_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_){
_start:
{
lean_object* v___x_1730_; 
v___x_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1720_, v_msg_1721_, v_declHint_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1731_, lean_object* v_ref_1732_, lean_object* v_msg_1733_, lean_object* v_declHint_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1731_, v_ref_1732_, v_msg_1733_, v_declHint_1734_, v___y_1735_, v___y_1736_, v___y_1737_, v___y_1738_, v___y_1739_, v___y_1740_);
lean_dec(v___y_1740_);
lean_dec_ref(v___y_1739_);
lean_dec(v___y_1738_);
lean_dec_ref(v___y_1737_);
lean_dec(v___y_1736_);
lean_dec(v___y_1735_);
lean_dec(v_ref_1732_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1743_, lean_object* v_declHint_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_){
_start:
{
lean_object* v___x_1752_; 
v___x_1752_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1743_, v_declHint_1744_, v___y_1750_);
return v___x_1752_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1753_, lean_object* v_declHint_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_){
_start:
{
lean_object* v_res_1762_; 
v_res_1762_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1753_, v_declHint_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec_ref(v___y_1757_);
lean_dec(v___y_1756_);
lean_dec(v___y_1755_);
return v_res_1762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1763_, lean_object* v_ref_1764_, lean_object* v_msg_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v___x_1773_; 
v___x_1773_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1764_, v_msg_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_, v___y_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1774_, lean_object* v_ref_1775_, lean_object* v_msg_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_){
_start:
{
lean_object* v_res_1784_; 
v_res_1784_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1774_, v_ref_1775_, v_msg_1776_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_, v___y_1781_, v___y_1782_);
lean_dec(v___y_1782_);
lean_dec_ref(v___y_1781_);
lean_dec(v___y_1780_);
lean_dec_ref(v___y_1779_);
lean_dec(v___y_1778_);
lean_dec(v___y_1777_);
lean_dec(v_ref_1775_);
return v_res_1784_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1785_, lean_object* v_msg_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_){
_start:
{
lean_object* v___x_1794_; 
v___x_1794_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1786_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
return v___x_1794_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1795_, lean_object* v_msg_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1795_, v_msg_1796_, v___y_1797_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_, v___y_1802_);
lean_dec(v___y_1802_);
lean_dec_ref(v___y_1801_);
lean_dec(v___y_1800_);
lean_dec_ref(v___y_1799_);
lean_dec(v___y_1798_);
lean_dec(v___y_1797_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
uint8_t v___x_1813_; 
v___x_1813_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1806_);
if (v___x_1813_ == 0)
{
lean_object* v___x_1814_; 
v___x_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_r_1805_);
return v___x_1814_;
}
else
{
lean_object* v___x_1815_; 
lean_inc_ref(v_r_1805_);
v___x_1815_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1805_, v_a_1807_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1815_) == 0)
{
lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1868_; 
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1868_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1868_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_expr_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1866_; 
v_expr_1820_ = lean_ctor_get(v_r_1805_, 0);
v_isSharedCheck_1866_ = !lean_is_exclusive(v_r_1805_);
if (v_isSharedCheck_1866_ == 0)
{
lean_object* v_unused_1867_; 
v_unused_1867_ = lean_ctor_get(v_r_1805_, 1);
lean_dec(v_unused_1867_);
v___x_1822_ = v_r_1805_;
v_isShared_1823_ = v_isSharedCheck_1866_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_expr_1820_);
lean_dec(v_r_1805_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1866_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
uint8_t v___x_1824_; 
v___x_1824_ = l_Lean_Expr_isSort(v_a_1816_);
if (v___x_1824_ == 0)
{
lean_object* v___x_1825_; 
lean_del_object(v___x_1818_);
lean_inc(v_a_1811_);
lean_inc_ref(v_a_1810_);
lean_inc(v_a_1809_);
lean_inc_ref(v_a_1808_);
v___x_1825_ = lean_whnf(v_a_1816_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
if (lean_obj_tag(v___x_1825_) == 0)
{
lean_object* v_a_1826_; lean_object* v___x_1828_; uint8_t v_isShared_1829_; uint8_t v_isSharedCheck_1850_; 
v_a_1826_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1850_ == 0)
{
v___x_1828_ = v___x_1825_;
v_isShared_1829_ = v_isSharedCheck_1850_;
goto v_resetjp_1827_;
}
else
{
lean_inc(v_a_1826_);
lean_dec(v___x_1825_);
v___x_1828_ = lean_box(0);
v_isShared_1829_ = v_isSharedCheck_1850_;
goto v_resetjp_1827_;
}
v_resetjp_1827_:
{
if (lean_obj_tag(v_a_1826_) == 3)
{
lean_object* v___x_1830_; lean_object* v_count_1831_; lean_object* v_results_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1848_; 
v___x_1830_ = lean_st_ref_take(v_a_1807_);
v_count_1831_ = lean_ctor_get(v___x_1830_, 0);
v_results_1832_ = lean_ctor_get(v___x_1830_, 1);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1830_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1834_ = v___x_1830_;
v_isShared_1835_ = v_isSharedCheck_1848_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_results_1832_);
lean_inc(v_count_1831_);
lean_dec(v___x_1830_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1848_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1836_; lean_object* v___x_1838_; 
v___x_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1836_, 0, v_a_1826_);
lean_inc_ref(v_expr_1820_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1836_);
v___x_1838_ = v___x_1822_;
goto v_reusejp_1837_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_expr_1820_);
lean_ctor_set(v_reuseFailAlloc_1847_, 1, v___x_1836_);
v___x_1838_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1837_;
}
v_reusejp_1837_:
{
lean_object* v___x_1839_; lean_object* v___x_1841_; 
lean_inc_ref(v___x_1838_);
v___x_1839_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1832_, v_expr_1820_, v___x_1838_);
if (v_isShared_1835_ == 0)
{
lean_ctor_set(v___x_1834_, 1, v___x_1839_);
v___x_1841_ = v___x_1834_;
goto v_reusejp_1840_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_count_1831_);
lean_ctor_set(v_reuseFailAlloc_1846_, 1, v___x_1839_);
v___x_1841_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1840_;
}
v_reusejp_1840_:
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_st_ref_set(v_a_1807_, v___x_1841_);
if (v_isShared_1829_ == 0)
{
lean_ctor_set(v___x_1828_, 0, v___x_1838_);
v___x_1844_ = v___x_1828_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v___x_1838_);
v___x_1844_ = v_reuseFailAlloc_1845_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
return v___x_1844_;
}
}
}
}
}
else
{
lean_object* v___x_1849_; 
lean_del_object(v___x_1828_);
lean_dec(v_a_1826_);
lean_del_object(v___x_1822_);
v___x_1849_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1820_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
return v___x_1849_;
}
}
}
else
{
lean_object* v_a_1851_; lean_object* v___x_1853_; uint8_t v_isShared_1854_; uint8_t v_isSharedCheck_1858_; 
lean_del_object(v___x_1822_);
lean_dec_ref(v_expr_1820_);
v_a_1851_ = lean_ctor_get(v___x_1825_, 0);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1825_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1853_ = v___x_1825_;
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
else
{
lean_inc(v_a_1851_);
lean_dec(v___x_1825_);
v___x_1853_ = lean_box(0);
v_isShared_1854_ = v_isSharedCheck_1858_;
goto v_resetjp_1852_;
}
v_resetjp_1852_:
{
lean_object* v___x_1856_; 
if (v_isShared_1854_ == 0)
{
v___x_1856_ = v___x_1853_;
goto v_reusejp_1855_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v_a_1851_);
v___x_1856_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1855_;
}
v_reusejp_1855_:
{
return v___x_1856_;
}
}
}
}
else
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1859_, 0, v_a_1816_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1859_);
v___x_1861_ = v___x_1822_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1865_; 
v_reuseFailAlloc_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_expr_1820_);
lean_ctor_set(v_reuseFailAlloc_1865_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1865_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1863_; 
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1861_);
v___x_1863_ = v___x_1818_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
}
}
else
{
lean_object* v_a_1869_; lean_object* v___x_1871_; uint8_t v_isShared_1872_; uint8_t v_isSharedCheck_1876_; 
lean_dec_ref(v_r_1805_);
v_a_1869_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1876_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1871_ = v___x_1815_;
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
else
{
lean_inc(v_a_1869_);
lean_dec(v___x_1815_);
v___x_1871_ = lean_box(0);
v_isShared_1872_ = v_isSharedCheck_1876_;
goto v_resetjp_1870_;
}
v_resetjp_1870_:
{
lean_object* v___x_1874_; 
if (v_isShared_1872_ == 0)
{
v___x_1874_ = v___x_1871_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v_a_1869_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1877_, lean_object* v_a_1878_, lean_object* v_a_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_, lean_object* v_a_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1877_, v_a_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_, v_a_1883_);
lean_dec(v_a_1883_);
lean_dec_ref(v_a_1882_);
lean_dec(v_a_1881_);
lean_dec_ref(v_a_1880_);
lean_dec(v_a_1879_);
lean_dec(v_a_1878_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1886_){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = l_Lean_instInhabitedExpr;
v___x_1888_ = lean_panic_fn_borrowed(v___x_1887_, v_msg_1886_);
return v___x_1888_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1893_ = lean_unsigned_to_nat(18u);
v___x_1894_ = lean_unsigned_to_nat(1847u);
v___x_1895_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1896_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1897_ = l_mkPanicMessageWithDecl(v___x_1896_, v___x_1895_, v___x_1894_, v___x_1893_, v___x_1892_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1898_, lean_object* v_f_1899_, lean_object* v_a_1900_, lean_object* v_a_1901_, lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___y_1909_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; uint8_t v___y_1925_; lean_object* v___y_1928_; lean_object* v_fType_1943_; lean_object* v___y_1944_; lean_object* v___y_1945_; lean_object* v___y_1946_; lean_object* v___y_1947_; lean_object* v___y_1948_; uint8_t v___x_1987_; 
v___x_1987_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1901_);
if (v___x_1987_ == 0)
{
lean_object* v_expr_1988_; lean_object* v_expr_1989_; uint8_t v___y_1991_; 
v_expr_1988_ = lean_ctor_get(v_f_1899_, 0);
lean_inc_ref(v_expr_1988_);
lean_dec_ref(v_f_1899_);
v_expr_1989_ = lean_ctor_get(v_a_1900_, 0);
lean_inc_ref(v_expr_1989_);
lean_dec_ref(v_a_1900_);
if (lean_obj_tag(v_e_1898_) == 5)
{
lean_object* v_fn_1993_; lean_object* v_arg_1994_; size_t v___x_1995_; size_t v___x_1996_; uint8_t v___x_1997_; 
v_fn_1993_ = lean_ctor_get(v_e_1898_, 0);
v_arg_1994_ = lean_ctor_get(v_e_1898_, 1);
v___x_1995_ = lean_ptr_addr(v_fn_1993_);
v___x_1996_ = lean_ptr_addr(v_expr_1988_);
v___x_1997_ = lean_usize_dec_eq(v___x_1995_, v___x_1996_);
if (v___x_1997_ == 0)
{
v___y_1991_ = v___x_1997_;
goto v___jp_1990_;
}
else
{
size_t v___x_1998_; size_t v___x_1999_; uint8_t v___x_2000_; 
v___x_1998_ = lean_ptr_addr(v_arg_1994_);
v___x_1999_ = lean_ptr_addr(v_expr_1989_);
v___x_2000_ = lean_usize_dec_eq(v___x_1998_, v___x_1999_);
v___y_1991_ = v___x_2000_;
goto v___jp_1990_;
}
}
else
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
lean_dec_ref(v_expr_1989_);
lean_dec_ref(v_expr_1988_);
lean_dec_ref(v_e_1898_);
v___x_2001_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_2002_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2001_);
v___y_1909_ = v___x_2002_;
goto v___jp_1908_;
}
v___jp_1990_:
{
if (v___y_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_dec_ref(v_e_1898_);
v___x_1992_ = l_Lean_Expr_app___override(v_expr_1988_, v_expr_1989_);
v___y_1909_ = v___x_1992_;
goto v___jp_1908_;
}
else
{
lean_dec_ref(v_expr_1989_);
lean_dec_ref(v_expr_1988_);
v___y_1909_ = v_e_1898_;
goto v___jp_1908_;
}
}
}
else
{
lean_object* v___x_2003_; 
lean_inc_ref(v_f_1899_);
v___x_2003_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1899_, v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; uint8_t v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = l_Lean_Expr_isForall(v_a_2004_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; 
lean_inc(v_a_1906_);
lean_inc_ref(v_a_1905_);
lean_inc(v_a_1904_);
lean_inc_ref(v_a_1903_);
v___x_2006_ = lean_whnf(v_a_2004_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v_fType_1943_ = v_a_2007_;
v___y_1944_ = v_a_1902_;
v___y_1945_ = v_a_1903_;
v___y_1946_ = v_a_1904_;
v___y_1947_ = v_a_1905_;
v___y_1948_ = v_a_1906_;
goto v___jp_1942_;
}
else
{
lean_object* v_a_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2015_; 
lean_dec_ref(v_a_1900_);
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_e_1898_);
v_a_2008_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2015_ == 0)
{
v___x_2010_ = v___x_2006_;
v_isShared_2011_ = v_isSharedCheck_2015_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_a_2008_);
lean_dec(v___x_2006_);
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
else
{
v_fType_1943_ = v_a_2004_;
v___y_1944_ = v_a_1902_;
v___y_1945_ = v_a_1903_;
v___y_1946_ = v_a_1904_;
v___y_1947_ = v_a_1905_;
v___y_1948_ = v_a_1906_;
goto v___jp_1942_;
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec_ref(v_a_1900_);
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_e_1898_);
v_a_2016_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2003_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2003_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
v___jp_1908_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___y_1909_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
return v___x_1912_;
}
v___jp_1913_:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
v___x_1917_ = lean_expr_instantiate1(v___y_1915_, v___y_1914_);
lean_dec_ref(v___y_1914_);
lean_dec_ref(v___y_1915_);
v___x_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1917_);
v___x_1919_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1919_, 0, v___y_1916_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
return v___x_1920_;
}
v___jp_1921_:
{
if (v___y_1925_ == 0)
{
lean_object* v___x_1926_; 
lean_dec_ref(v_e_1898_);
lean_inc_ref(v___y_1923_);
v___x_1926_ = l_Lean_Expr_app___override(v___y_1922_, v___y_1923_);
v___y_1914_ = v___y_1923_;
v___y_1915_ = v___y_1924_;
v___y_1916_ = v___x_1926_;
goto v___jp_1913_;
}
else
{
lean_dec_ref(v___y_1922_);
v___y_1914_ = v___y_1923_;
v___y_1915_ = v___y_1924_;
v___y_1916_ = v_e_1898_;
goto v___jp_1913_;
}
}
v___jp_1927_:
{
if (lean_obj_tag(v_e_1898_) == 5)
{
lean_object* v_expr_1929_; lean_object* v_expr_1930_; lean_object* v_fn_1931_; lean_object* v_arg_1932_; size_t v___x_1933_; size_t v___x_1934_; uint8_t v___x_1935_; 
v_expr_1929_ = lean_ctor_get(v_f_1899_, 0);
lean_inc_ref(v_expr_1929_);
lean_dec_ref(v_f_1899_);
v_expr_1930_ = lean_ctor_get(v_a_1900_, 0);
lean_inc_ref(v_expr_1930_);
lean_dec_ref(v_a_1900_);
v_fn_1931_ = lean_ctor_get(v_e_1898_, 0);
v_arg_1932_ = lean_ctor_get(v_e_1898_, 1);
v___x_1933_ = lean_ptr_addr(v_fn_1931_);
v___x_1934_ = lean_ptr_addr(v_expr_1929_);
v___x_1935_ = lean_usize_dec_eq(v___x_1933_, v___x_1934_);
if (v___x_1935_ == 0)
{
v___y_1922_ = v_expr_1929_;
v___y_1923_ = v_expr_1930_;
v___y_1924_ = v___y_1928_;
v___y_1925_ = v___x_1935_;
goto v___jp_1921_;
}
else
{
size_t v___x_1936_; size_t v___x_1937_; uint8_t v___x_1938_; 
v___x_1936_ = lean_ptr_addr(v_arg_1932_);
v___x_1937_ = lean_ptr_addr(v_expr_1930_);
v___x_1938_ = lean_usize_dec_eq(v___x_1936_, v___x_1937_);
v___y_1922_ = v_expr_1929_;
v___y_1923_ = v_expr_1930_;
v___y_1924_ = v___y_1928_;
v___y_1925_ = v___x_1938_;
goto v___jp_1921_;
}
}
else
{
lean_object* v_expr_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_e_1898_);
v_expr_1939_ = lean_ctor_get(v_a_1900_, 0);
lean_inc_ref(v_expr_1939_);
lean_dec_ref(v_a_1900_);
v___x_1940_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1941_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1940_);
v___y_1914_ = v_expr_1939_;
v___y_1915_ = v___y_1928_;
v___y_1916_ = v___x_1941_;
goto v___jp_1913_;
}
}
v___jp_1942_:
{
if (lean_obj_tag(v_fType_1943_) == 7)
{
lean_object* v_binderType_1949_; lean_object* v_body_1950_; lean_object* v___x_1951_; 
v_binderType_1949_ = lean_ctor_get(v_fType_1943_, 1);
lean_inc_ref(v_binderType_1949_);
v_body_1950_ = lean_ctor_get(v_fType_1943_, 2);
lean_inc_ref(v_body_1950_);
lean_dec_ref_known(v_fType_1943_, 3);
lean_inc_ref(v_a_1900_);
v___x_1951_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1900_, v___y_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = l_Lean_Meta_isExprDefEq(v_binderType_1949_, v_a_1952_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1953_) == 0)
{
lean_object* v_a_1954_; uint8_t v___x_1955_; 
v_a_1954_ = lean_ctor_get(v___x_1953_, 0);
lean_inc(v_a_1954_);
lean_dec_ref_known(v___x_1953_, 1);
v___x_1955_ = lean_unbox(v_a_1954_);
lean_dec(v_a_1954_);
if (v___x_1955_ == 0)
{
lean_object* v_expr_1956_; lean_object* v_expr_1957_; lean_object* v___x_1958_; 
v_expr_1956_ = lean_ctor_get(v_f_1899_, 0);
v_expr_1957_ = lean_ctor_get(v_a_1900_, 0);
lean_inc_ref(v_expr_1957_);
lean_inc_ref(v_expr_1956_);
v___x_1958_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1956_, v_expr_1957_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_dec_ref_known(v___x_1958_, 1);
v___y_1928_ = v_body_1950_;
goto v___jp_1927_;
}
else
{
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_a_1900_);
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_e_1898_);
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1958_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1958_);
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
v___y_1928_ = v_body_1950_;
goto v___jp_1927_;
}
}
else
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1974_; 
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_a_1900_);
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_e_1898_);
v_a_1967_ = lean_ctor_get(v___x_1953_, 0);
v_isSharedCheck_1974_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1974_ == 0)
{
v___x_1969_ = v___x_1953_;
v_isShared_1970_ = v_isSharedCheck_1974_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1953_);
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
lean_object* v_a_1975_; lean_object* v___x_1977_; uint8_t v_isShared_1978_; uint8_t v_isSharedCheck_1982_; 
lean_dec_ref(v_body_1950_);
lean_dec_ref(v_binderType_1949_);
lean_dec_ref(v_a_1900_);
lean_dec_ref(v_f_1899_);
lean_dec_ref(v_e_1898_);
v_a_1975_ = lean_ctor_get(v___x_1951_, 0);
v_isSharedCheck_1982_ = !lean_is_exclusive(v___x_1951_);
if (v_isSharedCheck_1982_ == 0)
{
v___x_1977_ = v___x_1951_;
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
else
{
lean_inc(v_a_1975_);
lean_dec(v___x_1951_);
v___x_1977_ = lean_box(0);
v_isShared_1978_ = v_isSharedCheck_1982_;
goto v_resetjp_1976_;
}
v_resetjp_1976_:
{
lean_object* v___x_1980_; 
if (v_isShared_1978_ == 0)
{
v___x_1980_ = v___x_1977_;
goto v_reusejp_1979_;
}
else
{
lean_object* v_reuseFailAlloc_1981_; 
v_reuseFailAlloc_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1981_, 0, v_a_1975_);
v___x_1980_ = v_reuseFailAlloc_1981_;
goto v_reusejp_1979_;
}
v_reusejp_1979_:
{
return v___x_1980_;
}
}
}
}
else
{
lean_object* v_expr_1983_; lean_object* v_expr_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
lean_dec_ref(v_fType_1943_);
lean_dec_ref(v_e_1898_);
v_expr_1983_ = lean_ctor_get(v_f_1899_, 0);
lean_inc_ref(v_expr_1983_);
lean_dec_ref(v_f_1899_);
v_expr_1984_ = lean_ctor_get(v_a_1900_, 0);
lean_inc_ref(v_expr_1984_);
lean_dec_ref(v_a_1900_);
v___x_1985_ = l_Lean_Expr_app___override(v_expr_1983_, v_expr_1984_);
v___x_1986_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1985_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
return v___x_1986_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2024_, lean_object* v_f_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_){
_start:
{
lean_object* v_res_2034_; 
v_res_2034_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2024_, v_f_2025_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_, v_a_2031_, v_a_2032_);
lean_dec(v_a_2032_);
lean_dec_ref(v_a_2031_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec(v_a_2027_);
return v_res_2034_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v___x_2036_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2037_ = lean_unsigned_to_nat(37u);
v___x_2038_ = lean_unsigned_to_nat(345u);
v___x_2039_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2040_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2041_ = l_mkPanicMessageWithDecl(v___x_2040_, v___x_2039_, v___x_2038_, v___x_2037_, v___x_2036_);
return v___x_2041_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2042_, lean_object* v_i_2043_, lean_object* v_a_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_zero_2052_; uint8_t v_isZero_2053_; 
v_zero_2052_ = lean_unsigned_to_nat(0u);
v_isZero_2053_ = lean_nat_dec_eq(v_i_2043_, v_zero_2052_);
if (v_isZero_2053_ == 1)
{
lean_object* v___x_2054_; 
lean_dec(v_i_2043_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v_a_2044_);
return v___x_2054_;
}
else
{
lean_object* v_one_2055_; lean_object* v_n_2056_; lean_object* v___y_2058_; lean_object* v___y_2062_; lean_object* v___y_2063_; lean_object* v___y_2067_; lean_object* v___y_2068_; lean_object* v___x_2070_; 
v_one_2055_ = lean_unsigned_to_nat(1u);
v_n_2056_ = lean_nat_sub(v_i_2043_, v_one_2055_);
lean_dec(v_i_2043_);
v___x_2070_ = lean_array_fget_borrowed(v_fvars_2042_, v_n_2056_);
if (lean_obj_tag(v___x_2070_) == 1)
{
lean_object* v_fvarId_2071_; lean_object* v___x_2072_; 
v_fvarId_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_fvarId_2071_);
v___x_2072_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2071_, v___y_2047_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
lean_dec_ref_known(v___x_2072_, 1);
if (lean_obj_tag(v_a_2073_) == 1)
{
lean_object* v_val_2074_; 
v_val_2074_ = lean_ctor_get(v_a_2073_, 0);
lean_inc(v_val_2074_);
lean_dec_ref_known(v_a_2073_, 1);
if (lean_obj_tag(v_val_2074_) == 0)
{
lean_object* v_userName_2075_; lean_object* v_type_2076_; uint8_t v_bi_2077_; lean_object* v_expr_2078_; lean_object* v_type_x3f_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2100_; 
v_userName_2075_ = lean_ctor_get(v_val_2074_, 2);
lean_inc(v_userName_2075_);
v_type_2076_ = lean_ctor_get(v_val_2074_, 3);
lean_inc_ref(v_type_2076_);
v_bi_2077_ = lean_ctor_get_uint8(v_val_2074_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2074_, 4);
v_expr_2078_ = lean_ctor_get(v_a_2044_, 0);
v_type_x3f_2079_ = lean_ctor_get(v_a_2044_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_a_2044_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2081_ = v_a_2044_;
v_isShared_2082_ = v_isSharedCheck_2100_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_type_x3f_2079_);
lean_inc(v_expr_2078_);
lean_dec(v_a_2044_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2100_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___y_2086_; 
v___x_2083_ = lean_expr_abstract_range(v_type_2076_, v_n_2056_, v_fvars_2042_);
lean_dec_ref(v_type_2076_);
lean_inc_ref(v___x_2083_);
lean_inc(v_userName_2075_);
v___x_2084_ = l_Lean_Expr_lam___override(v_userName_2075_, v___x_2083_, v_expr_2078_, v_bi_2077_);
if (lean_obj_tag(v_type_x3f_2079_) == 0)
{
lean_dec_ref(v___x_2083_);
lean_dec(v_userName_2075_);
v___y_2086_ = v_type_x3f_2079_;
goto v___jp_2085_;
}
else
{
lean_object* v_val_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2099_; 
v_val_2091_ = lean_ctor_get(v_type_x3f_2079_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_type_x3f_2079_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2093_ = v_type_x3f_2079_;
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_val_2091_);
lean_dec(v_type_x3f_2079_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2099_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; lean_object* v___x_2097_; 
v___x_2095_ = l_Lean_Expr_forallE___override(v_userName_2075_, v___x_2083_, v_val_2091_, v_bi_2077_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 0, v___x_2095_);
v___x_2097_ = v___x_2093_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v___x_2095_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
v___y_2086_ = v___x_2097_;
goto v___jp_2085_;
}
}
}
v___jp_2085_:
{
lean_object* v___x_2088_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___y_2086_);
lean_ctor_set(v___x_2081_, 0, v___x_2084_);
v___x_2088_ = v___x_2081_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v___x_2084_);
lean_ctor_set(v_reuseFailAlloc_2090_, 1, v___y_2086_);
v___x_2088_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
v_i_2043_ = v_n_2056_;
v_a_2044_ = v___x_2088_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2101_; lean_object* v_type_2102_; lean_object* v_value_2103_; uint8_t v_nondep_2104_; uint8_t v_nondep_2106_; lean_object* v___x_2116_; 
v_userName_2101_ = lean_ctor_get(v_val_2074_, 2);
lean_inc(v_userName_2101_);
v_type_2102_ = lean_ctor_get(v_val_2074_, 3);
lean_inc_ref(v_type_2102_);
v_value_2103_ = lean_ctor_get(v_val_2074_, 4);
lean_inc_ref(v_value_2103_);
v_nondep_2104_ = lean_ctor_get_uint8(v_val_2074_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2074_, 5);
v___x_2116_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2048_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; uint8_t v___x_2118_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2116_, 1);
v___x_2118_ = 1;
if (v_nondep_2104_ == 0)
{
uint8_t v___x_2119_; uint8_t v___x_2120_; 
v___x_2119_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2071_, v_a_2117_);
lean_dec(v_a_2117_);
v___x_2120_ = lean_bool_not(v___x_2119_);
if (v___x_2120_ == 0)
{
v_nondep_2106_ = v___x_2120_;
goto v___jp_2105_;
}
else
{
lean_object* v___x_2121_; 
v___x_2121_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2046_);
lean_dec_ref(v___x_2121_);
v_nondep_2106_ = v___x_2118_;
goto v___jp_2105_;
}
}
else
{
lean_dec(v_a_2117_);
v_nondep_2106_ = v___x_2118_;
goto v___jp_2105_;
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_value_2103_);
lean_dec_ref(v_type_2102_);
lean_dec(v_userName_2101_);
lean_dec(v_n_2056_);
lean_dec_ref(v_a_2044_);
v_a_2122_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2116_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2116_);
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
v___jp_2105_:
{
lean_object* v_expr_2107_; lean_object* v_type_x3f_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_expr_2107_ = lean_ctor_get(v_a_2044_, 0);
lean_inc_ref(v_expr_2107_);
v_type_x3f_2108_ = lean_ctor_get(v_a_2044_, 1);
lean_inc(v_type_x3f_2108_);
lean_dec_ref(v_a_2044_);
v___x_2109_ = lean_expr_abstract_range(v_type_2102_, v_n_2056_, v_fvars_2042_);
lean_dec_ref(v_type_2102_);
v___x_2110_ = lean_expr_abstract_range(v_value_2103_, v_n_2056_, v_fvars_2042_);
lean_dec_ref(v_value_2103_);
lean_inc_ref(v___x_2110_);
lean_inc_ref(v___x_2109_);
lean_inc(v_userName_2101_);
v___x_2111_ = l_Lean_Expr_letE___override(v_userName_2101_, v___x_2109_, v___x_2110_, v_expr_2107_, v_nondep_2106_);
if (lean_obj_tag(v_type_x3f_2108_) == 0)
{
lean_dec_ref(v___x_2110_);
lean_dec_ref(v___x_2109_);
lean_dec(v_userName_2101_);
v___y_2062_ = v___x_2111_;
v___y_2063_ = v_type_x3f_2108_;
goto v___jp_2061_;
}
else
{
lean_object* v_val_2112_; uint8_t v___x_2113_; 
v_val_2112_ = lean_ctor_get(v_type_x3f_2108_, 0);
lean_inc(v_val_2112_);
lean_dec_ref_known(v_type_x3f_2108_, 1);
v___x_2113_ = lean_expr_has_loose_bvar(v_val_2112_, v_zero_2052_);
if (v___x_2113_ == 0)
{
lean_object* v___x_2114_; 
lean_dec_ref(v___x_2110_);
lean_dec_ref(v___x_2109_);
lean_dec(v_userName_2101_);
v___x_2114_ = lean_expr_lower_loose_bvars(v_val_2112_, v_one_2055_, v_one_2055_);
lean_dec(v_val_2112_);
v___y_2067_ = v___x_2111_;
v___y_2068_ = v___x_2114_;
goto v___jp_2066_;
}
else
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_Expr_letE___override(v_userName_2101_, v___x_2109_, v___x_2110_, v_val_2112_, v_nondep_2106_);
v___y_2067_ = v___x_2111_;
v___y_2068_ = v___x_2115_;
goto v___jp_2066_;
}
}
}
}
}
else
{
lean_object* v___x_2130_; 
lean_dec(v_a_2073_);
lean_dec_ref(v_a_2044_);
lean_inc(v_fvarId_2071_);
v___x_2130_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2071_, v___y_2049_, v___y_2050_);
v___y_2058_ = v___x_2130_;
goto v___jp_2057_;
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec(v_n_2056_);
lean_dec_ref(v_a_2044_);
v_a_2131_ = lean_ctor_get(v___x_2072_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2072_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2072_);
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
}
else
{
lean_object* v___x_2139_; lean_object* v___x_2140_; 
lean_dec_ref(v_a_2044_);
v___x_2139_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2140_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2139_, v___y_2045_, v___y_2046_, v___y_2047_, v___y_2048_, v___y_2049_, v___y_2050_);
v___y_2058_ = v___x_2140_;
goto v___jp_2057_;
}
v___jp_2057_:
{
if (lean_obj_tag(v___y_2058_) == 0)
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___y_2058_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___y_2058_, 1);
v_i_2043_ = v_n_2056_;
v_a_2044_ = v_a_2059_;
goto _start;
}
else
{
lean_dec(v_n_2056_);
return v___y_2058_;
}
}
v___jp_2061_:
{
lean_object* v___x_2064_; 
v___x_2064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2064_, 0, v___y_2062_);
lean_ctor_set(v___x_2064_, 1, v___y_2063_);
v_i_2043_ = v_n_2056_;
v_a_2044_ = v___x_2064_;
goto _start;
}
v___jp_2066_:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2069_, 0, v___y_2068_);
v___y_2062_ = v___y_2067_;
v___y_2063_ = v___x_2069_;
goto v___jp_2061_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2141_, lean_object* v_i_2142_, lean_object* v_a_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2141_, v_i_2142_, v_a_2143_, v___y_2144_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_, v___y_2149_);
lean_dec(v___y_2149_);
lean_dec_ref(v___y_2148_);
lean_dec(v___y_2147_);
lean_dec_ref(v___y_2146_);
lean_dec(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v_fvars_2141_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2152_, lean_object* v_a_2153_){
_start:
{
if (lean_obj_tag(v_a_2152_) == 0)
{
lean_object* v___x_2154_; 
v___x_2154_ = l_List_reverse___redArg(v_a_2153_);
return v___x_2154_;
}
else
{
lean_object* v_head_2155_; lean_object* v_tail_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2165_; 
v_head_2155_ = lean_ctor_get(v_a_2152_, 0);
v_tail_2156_ = lean_ctor_get(v_a_2152_, 1);
v_isSharedCheck_2165_ = !lean_is_exclusive(v_a_2152_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2158_ = v_a_2152_;
v_isShared_2159_ = v_isSharedCheck_2165_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_tail_2156_);
lean_inc(v_head_2155_);
lean_dec(v_a_2152_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2165_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; lean_object* v___x_2162_; 
v___x_2160_ = l_Lean_MessageData_ofExpr(v_head_2155_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 1, v_a_2153_);
lean_ctor_set(v___x_2158_, 0, v___x_2160_);
v___x_2162_ = v___x_2158_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2160_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_a_2153_);
v___x_2162_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
v_a_2152_ = v_tail_2156_;
v_a_2153_ = v___x_2162_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2166_; double v___x_2167_; 
v___x_2166_ = lean_unsigned_to_nat(0u);
v___x_2167_ = lean_float_of_nat(v___x_2166_);
return v___x_2167_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2171_, lean_object* v_msg_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_ref_2178_; lean_object* v___x_2179_; lean_object* v_a_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2224_; 
v_ref_2178_ = lean_ctor_get(v___y_2175_, 5);
v___x_2179_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2172_, v___y_2173_, v___y_2174_, v___y_2175_, v___y_2176_);
v_a_2180_ = lean_ctor_get(v___x_2179_, 0);
v_isSharedCheck_2224_ = !lean_is_exclusive(v___x_2179_);
if (v_isSharedCheck_2224_ == 0)
{
v___x_2182_ = v___x_2179_;
v_isShared_2183_ = v_isSharedCheck_2224_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_a_2180_);
lean_dec(v___x_2179_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2224_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; lean_object* v_traceState_2185_; lean_object* v_env_2186_; lean_object* v_nextMacroScope_2187_; lean_object* v_ngen_2188_; lean_object* v_auxDeclNGen_2189_; lean_object* v_cache_2190_; lean_object* v_messages_2191_; lean_object* v_infoState_2192_; lean_object* v_snapshotTasks_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2223_; 
v___x_2184_ = lean_st_ref_take(v___y_2176_);
v_traceState_2185_ = lean_ctor_get(v___x_2184_, 4);
v_env_2186_ = lean_ctor_get(v___x_2184_, 0);
v_nextMacroScope_2187_ = lean_ctor_get(v___x_2184_, 1);
v_ngen_2188_ = lean_ctor_get(v___x_2184_, 2);
v_auxDeclNGen_2189_ = lean_ctor_get(v___x_2184_, 3);
v_cache_2190_ = lean_ctor_get(v___x_2184_, 5);
v_messages_2191_ = lean_ctor_get(v___x_2184_, 6);
v_infoState_2192_ = lean_ctor_get(v___x_2184_, 7);
v_snapshotTasks_2193_ = lean_ctor_get(v___x_2184_, 8);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2184_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2195_ = v___x_2184_;
v_isShared_2196_ = v_isSharedCheck_2223_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_snapshotTasks_2193_);
lean_inc(v_infoState_2192_);
lean_inc(v_messages_2191_);
lean_inc(v_cache_2190_);
lean_inc(v_traceState_2185_);
lean_inc(v_auxDeclNGen_2189_);
lean_inc(v_ngen_2188_);
lean_inc(v_nextMacroScope_2187_);
lean_inc(v_env_2186_);
lean_dec(v___x_2184_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2223_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
uint64_t v_tid_2197_; lean_object* v_traces_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2222_; 
v_tid_2197_ = lean_ctor_get_uint64(v_traceState_2185_, sizeof(void*)*1);
v_traces_2198_ = lean_ctor_get(v_traceState_2185_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_traceState_2185_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2200_ = v_traceState_2185_;
v_isShared_2201_ = v_isSharedCheck_2222_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_traces_2198_);
lean_dec(v_traceState_2185_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2222_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; double v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2212_; 
v___x_2202_ = lean_box(0);
v___x_2203_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2204_ = 0;
v___x_2205_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2206_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2206_, 0, v_cls_2171_);
lean_ctor_set(v___x_2206_, 1, v___x_2202_);
lean_ctor_set(v___x_2206_, 2, v___x_2205_);
lean_ctor_set_float(v___x_2206_, sizeof(void*)*3, v___x_2203_);
lean_ctor_set_float(v___x_2206_, sizeof(void*)*3 + 8, v___x_2203_);
lean_ctor_set_uint8(v___x_2206_, sizeof(void*)*3 + 16, v___x_2204_);
v___x_2207_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2208_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2206_);
lean_ctor_set(v___x_2208_, 1, v_a_2180_);
lean_ctor_set(v___x_2208_, 2, v___x_2207_);
lean_inc(v_ref_2178_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v_ref_2178_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = l_Lean_PersistentArray_push___redArg(v_traces_2198_, v___x_2209_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 0, v___x_2210_);
v___x_2212_ = v___x_2200_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2210_);
lean_ctor_set_uint64(v_reuseFailAlloc_2221_, sizeof(void*)*1, v_tid_2197_);
v___x_2212_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
lean_object* v___x_2214_; 
if (v_isShared_2196_ == 0)
{
lean_ctor_set(v___x_2195_, 4, v___x_2212_);
v___x_2214_ = v___x_2195_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_env_2186_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_nextMacroScope_2187_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_ngen_2188_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v_auxDeclNGen_2189_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2220_, 5, v_cache_2190_);
lean_ctor_set(v_reuseFailAlloc_2220_, 6, v_messages_2191_);
lean_ctor_set(v_reuseFailAlloc_2220_, 7, v_infoState_2192_);
lean_ctor_set(v_reuseFailAlloc_2220_, 8, v_snapshotTasks_2193_);
v___x_2214_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2218_; 
v___x_2215_ = lean_st_ref_set(v___y_2176_, v___x_2214_);
v___x_2216_ = lean_box(0);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2216_);
v___x_2218_ = v___x_2182_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2225_, lean_object* v_msg_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2225_, v_msg_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
return v_res_2232_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v_cls_2243_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2244_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2245_ = l_Lean_Name_append(v___x_2244_, v_cls_2243_);
return v___x_2245_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2251_ = l_Lean_stringToMessageData(v___x_2250_);
return v___x_2251_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2254_ = l_Lean_stringToMessageData(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2259_ = l_Lean_MessageData_ofFormat(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2260_, lean_object* v_body_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2286_; lean_object* v___y_2287_; lean_object* v_options_2300_; uint8_t v_hasTrace_2301_; 
v_options_2300_ = lean_ctor_get(v_a_2266_, 2);
v_hasTrace_2301_ = lean_ctor_get_uint8(v_options_2300_, sizeof(void*)*1);
if (v_hasTrace_2301_ == 0)
{
v___y_2282_ = v_a_2262_;
v___y_2283_ = v_a_2263_;
v___y_2284_ = v_a_2264_;
v___y_2285_ = v_a_2265_;
v___y_2286_ = v_a_2266_;
v___y_2287_ = v_a_2267_;
goto v___jp_2281_;
}
else
{
lean_object* v_inheritedTraceOptions_2302_; lean_object* v_cls_2303_; lean_object* v___x_2304_; uint8_t v___x_2305_; 
v_inheritedTraceOptions_2302_ = lean_ctor_get(v_a_2266_, 13);
v_cls_2303_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2304_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2305_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2302_, v_options_2300_, v___x_2304_);
if (v___x_2305_ == 0)
{
v___y_2282_ = v_a_2262_;
v___y_2283_ = v_a_2263_;
v___y_2284_ = v_a_2264_;
v___y_2285_ = v_a_2265_;
v___y_2286_ = v_a_2266_;
v___y_2287_ = v_a_2267_;
goto v___jp_2281_;
}
else
{
lean_object* v_expr_2306_; lean_object* v_type_x3f_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___y_2320_; 
v_expr_2306_ = lean_ctor_get(v_body_2261_, 0);
v_type_x3f_2307_ = lean_ctor_get(v_body_2261_, 1);
v___x_2308_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2260_);
v___x_2309_ = lean_array_to_list(v_fvars_2260_);
v___x_2310_ = lean_box(0);
v___x_2311_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2309_, v___x_2310_);
v___x_2312_ = l_Lean_MessageData_ofList(v___x_2311_);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2308_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
lean_inc_ref(v_expr_2306_);
v___x_2316_ = l_Lean_MessageData_ofExpr(v_expr_2306_);
v___x_2317_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
if (lean_obj_tag(v_type_x3f_2307_) == 0)
{
lean_object* v___x_2333_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2320_ = v___x_2333_;
goto v___jp_2319_;
}
else
{
lean_object* v_val_2334_; lean_object* v___x_2335_; 
v_val_2334_ = lean_ctor_get(v_type_x3f_2307_, 0);
lean_inc(v_val_2334_);
v___x_2335_ = l_Lean_MessageData_ofExpr(v_val_2334_);
v___y_2320_ = v___x_2335_;
goto v___jp_2319_;
}
v___jp_2319_:
{
lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2321_, 0, v___x_2318_);
lean_ctor_set(v___x_2321_, 1, v___y_2320_);
v___x_2322_ = l_Lean_indentD(v___x_2321_);
v___x_2323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2323_, 0, v___x_2315_);
lean_ctor_set(v___x_2323_, 1, v___x_2322_);
v___x_2324_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2303_, v___x_2323_, v_a_2264_, v_a_2265_, v_a_2266_, v_a_2267_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_dec_ref_known(v___x_2324_, 1);
v___y_2282_ = v_a_2262_;
v___y_2283_ = v_a_2263_;
v___y_2284_ = v_a_2264_;
v___y_2285_ = v_a_2265_;
v___y_2286_ = v_a_2266_;
v___y_2287_ = v_a_2267_;
goto v___jp_2281_;
}
else
{
lean_object* v_a_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2332_; 
lean_dec_ref(v_body_2261_);
lean_dec_ref(v_fvars_2260_);
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2332_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2332_ == 0)
{
v___x_2327_ = v___x_2324_;
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_a_2325_);
lean_dec(v___x_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2332_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v___x_2330_; 
if (v_isShared_2328_ == 0)
{
v___x_2330_ = v___x_2327_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v_a_2325_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
return v___x_2330_;
}
}
}
}
}
}
v___jp_2269_:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___y_2270_);
lean_ctor_set(v___x_2278_, 1, v___y_2277_);
v___x_2279_ = lean_array_get_size(v_fvars_2260_);
v___x_2280_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2260_, v___x_2279_, v___x_2278_, v___y_2272_, v___y_2276_, v___y_2274_, v___y_2273_, v___y_2275_, v___y_2271_);
lean_dec_ref(v_fvars_2260_);
return v___x_2280_;
}
v___jp_2281_:
{
lean_object* v_expr_2288_; lean_object* v_type_x3f_2289_; lean_object* v___x_2290_; 
v_expr_2288_ = lean_ctor_get(v_body_2261_, 0);
lean_inc_ref(v_expr_2288_);
v_type_x3f_2289_ = lean_ctor_get(v_body_2261_, 1);
lean_inc(v_type_x3f_2289_);
lean_dec_ref(v_body_2261_);
v___x_2290_ = lean_expr_abstract(v_expr_2288_, v_fvars_2260_);
lean_dec_ref(v_expr_2288_);
if (lean_obj_tag(v_type_x3f_2289_) == 0)
{
v___y_2270_ = v___x_2290_;
v___y_2271_ = v___y_2287_;
v___y_2272_ = v___y_2282_;
v___y_2273_ = v___y_2285_;
v___y_2274_ = v___y_2284_;
v___y_2275_ = v___y_2286_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v_type_x3f_2289_;
goto v___jp_2269_;
}
else
{
lean_object* v_val_2291_; lean_object* v___x_2293_; uint8_t v_isShared_2294_; uint8_t v_isSharedCheck_2299_; 
v_val_2291_ = lean_ctor_get(v_type_x3f_2289_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v_type_x3f_2289_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2293_ = v_type_x3f_2289_;
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
else
{
lean_inc(v_val_2291_);
lean_dec(v_type_x3f_2289_);
v___x_2293_ = lean_box(0);
v_isShared_2294_ = v_isSharedCheck_2299_;
goto v_resetjp_2292_;
}
v_resetjp_2292_:
{
lean_object* v___x_2295_; lean_object* v___x_2297_; 
v___x_2295_ = lean_expr_abstract(v_val_2291_, v_fvars_2260_);
lean_dec(v_val_2291_);
if (v_isShared_2294_ == 0)
{
lean_ctor_set(v___x_2293_, 0, v___x_2295_);
v___x_2297_ = v___x_2293_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v___x_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
v___y_2270_ = v___x_2290_;
v___y_2271_ = v___y_2287_;
v___y_2272_ = v___y_2282_;
v___y_2273_ = v___y_2285_;
v___y_2274_ = v___y_2284_;
v___y_2275_ = v___y_2286_;
v___y_2276_ = v___y_2283_;
v___y_2277_ = v___x_2297_;
goto v___jp_2269_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2336_, lean_object* v_body_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2336_, v_body_2337_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
lean_dec(v_a_2343_);
lean_dec_ref(v_a_2342_);
lean_dec(v_a_2341_);
lean_dec_ref(v_a_2340_);
lean_dec(v_a_2339_);
lean_dec(v_a_2338_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2346_, lean_object* v_n_2347_, lean_object* v_i_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
lean_object* v___x_2358_; 
v___x_2358_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2346_, v_i_2348_, v_a_2350_, v___y_2351_, v___y_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2358_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2359_, lean_object* v_n_2360_, lean_object* v_i_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2359_, v_n_2360_, v_i_2361_, v_a_2362_, v_a_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
lean_dec(v_n_2360_);
lean_dec_ref(v_fvars_2359_);
return v_res_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2372_, lean_object* v_msg_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_, lean_object* v___y_2379_){
_start:
{
lean_object* v___x_2381_; 
v___x_2381_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2372_, v_msg_2373_, v___y_2376_, v___y_2377_, v___y_2378_, v___y_2379_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2382_, lean_object* v_msg_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2382_, v_msg_2383_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
lean_dec(v___y_2389_);
lean_dec_ref(v___y_2388_);
lean_dec(v___y_2387_);
lean_dec_ref(v___y_2386_);
lean_dec(v___y_2385_);
lean_dec(v___y_2384_);
return v_res_2391_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; 
v___x_2393_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2394_ = l_Lean_stringToMessageData(v___x_2393_);
return v___x_2394_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2398_, lean_object* v_structName_2399_, lean_object* v_idx_2400_, lean_object* v_a_2401_, lean_object* v_00_u03b1_2402_, lean_object* v_x_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v_expr_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2426_; 
v_expr_2411_ = lean_ctor_get(v_struct_2398_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_struct_2398_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v_struct_2398_, 1);
lean_dec(v_unused_2427_);
v___x_2413_ = v_struct_2398_;
v_isShared_2414_ = v_isSharedCheck_2426_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_expr_2411_);
lean_dec(v_struct_2398_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2426_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2415_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2416_ = l_Lean_mkProj(v_structName_2399_, v_idx_2400_, v_expr_2411_);
v___x_2417_ = l_Lean_indentExpr(v___x_2416_);
if (v_isShared_2414_ == 0)
{
lean_ctor_set_tag(v___x_2413_, 7);
lean_ctor_set(v___x_2413_, 1, v___x_2417_);
lean_ctor_set(v___x_2413_, 0, v___x_2415_);
v___x_2419_ = v___x_2413_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v___x_2415_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v___x_2417_);
v___x_2419_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2420_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2419_);
lean_ctor_set(v___x_2421_, 1, v___x_2420_);
v___x_2422_ = l_Lean_indentExpr(v_a_2401_);
v___x_2423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2423_, 0, v___x_2421_);
lean_ctor_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2423_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
return v___x_2424_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2428_, lean_object* v_structName_2429_, lean_object* v_idx_2430_, lean_object* v_a_2431_, lean_object* v_00_u03b1_2432_, lean_object* v_x_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_, lean_object* v___y_2438_, lean_object* v___y_2439_, lean_object* v___y_2440_){
_start:
{
lean_object* v_res_2441_; 
v_res_2441_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2428_, v_structName_2429_, v_idx_2430_, v_a_2431_, v_00_u03b1_2432_, v_x_2433_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_, v___y_2438_, v___y_2439_);
lean_dec(v___y_2439_);
lean_dec_ref(v___y_2438_);
lean_dec(v___y_2437_);
lean_dec_ref(v___y_2436_);
lean_dec(v___y_2435_);
lean_dec(v___y_2434_);
return v_res_2441_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v___x_2450_; lean_object* v_env_2451_; uint8_t v___x_2452_; lean_object* v___x_2453_; 
v___x_2450_ = lean_st_ref_get(v___y_2448_);
v_env_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc_ref(v_env_2451_);
lean_dec(v___x_2450_);
v___x_2452_ = 0;
lean_inc(v_constName_2442_);
v___x_2453_ = l_Lean_Environment_find_x3f(v_env_2451_, v_constName_2442_, v___x_2452_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v___x_2454_; 
v___x_2454_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
return v___x_2454_;
}
else
{
lean_object* v_val_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_constName_2442_);
v_val_2455_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2453_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_val_2455_);
lean_dec(v___x_2453_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
lean_ctor_set_tag(v___x_2457_, 0);
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_val_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_, lean_object* v___y_2468_, lean_object* v___y_2469_, lean_object* v___y_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2463_, v___y_2464_, v___y_2465_, v___y_2466_, v___y_2467_, v___y_2468_, v___y_2469_);
lean_dec(v___y_2469_);
lean_dec_ref(v___y_2468_);
lean_dec(v___y_2467_);
lean_dec_ref(v___y_2466_);
lean_dec(v___y_2465_);
lean_dec(v___y_2464_);
return v_res_2471_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2472_, lean_object* v_structName_2473_, lean_object* v_idx_2474_, lean_object* v_a_2475_, lean_object* v_00_u03b1_2476_, lean_object* v_x_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_){
_start:
{
lean_object* v_expr_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2500_; 
v_expr_2485_ = lean_ctor_get(v_struct_2472_, 0);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_struct_2472_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_struct_2472_, 1);
lean_dec(v_unused_2501_);
v___x_2487_ = v_struct_2472_;
v_isShared_2488_ = v_isSharedCheck_2500_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_expr_2485_);
lean_dec(v_struct_2472_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2500_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
v___x_2489_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2490_ = l_Lean_mkProj(v_structName_2473_, v_idx_2474_, v_expr_2485_);
v___x_2491_ = l_Lean_indentExpr(v___x_2490_);
if (v_isShared_2488_ == 0)
{
lean_ctor_set_tag(v___x_2487_, 7);
lean_ctor_set(v___x_2487_, 1, v___x_2491_);
lean_ctor_set(v___x_2487_, 0, v___x_2489_);
v___x_2493_ = v___x_2487_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; 
v___x_2494_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2493_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = l_Lean_indentExpr(v_a_2475_);
v___x_2497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2495_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2497_, v___y_2480_, v___y_2481_, v___y_2482_, v___y_2483_);
return v___x_2498_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2502_, lean_object* v_structName_2503_, lean_object* v_idx_2504_, lean_object* v_a_2505_, lean_object* v_00_u03b1_2506_, lean_object* v_x_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v_res_2515_; 
v_res_2515_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2502_, v_structName_2503_, v_idx_2504_, v_a_2505_, v_00_u03b1_2506_, v_x_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_);
lean_dec(v___y_2513_);
lean_dec_ref(v___y_2512_);
lean_dec(v___y_2511_);
lean_dec_ref(v___y_2510_);
lean_dec(v___y_2509_);
lean_dec(v___y_2508_);
return v_res_2515_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2516_, lean_object* v_fst_2517_, lean_object* v_struct_2518_, lean_object* v_structName_2519_, uint8_t v_a_2520_, lean_object* v___f_2521_, lean_object* v_snd_2522_, lean_object* v_____r_2523_, lean_object* v_ctorType_2524_, lean_object* v_j_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
if (lean_obj_tag(v_ctorType_2524_) == 7)
{
lean_object* v_binderType_2533_; lean_object* v_body_2534_; lean_object* v___x_2535_; 
lean_dec(v_snd_2522_);
v_binderType_2533_ = lean_ctor_get(v_ctorType_2524_, 1);
lean_inc_ref(v_binderType_2533_);
v_body_2534_ = lean_ctor_get(v_ctorType_2524_, 2);
lean_inc_ref(v_body_2534_);
lean_dec_ref_known(v_ctorType_2524_, 3);
v___x_2535_ = lean_expr_instantiate_rev_range(v_binderType_2533_, v_j_2525_, v_a_2516_, v_fst_2517_);
lean_dec_ref(v_binderType_2533_);
if (v_a_2520_ == 0)
{
lean_dec_ref(v___f_2521_);
goto v___jp_2536_;
}
else
{
lean_object* v___x_2552_; 
lean_inc_ref(v___x_2535_);
v___x_2552_ = l_Lean_Meta_isProp(v___x_2535_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; uint8_t v___x_2554_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = lean_unbox(v_a_2553_);
lean_dec(v_a_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2555_; lean_object* v___x_2556_; 
v___x_2555_ = lean_box(0);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc(v___y_2526_);
v___x_2556_ = lean_apply_9(v___f_2521_, lean_box(0), v___x_2555_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, lean_box(0));
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_dec_ref_known(v___x_2556_, 1);
goto v___jp_2536_;
}
else
{
lean_object* v_a_2557_; lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2564_; 
lean_dec_ref(v___x_2535_);
lean_dec_ref(v_body_2534_);
lean_dec(v_structName_2519_);
lean_dec_ref(v_struct_2518_);
lean_dec(v_fst_2517_);
lean_dec(v_a_2516_);
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2559_ = v___x_2556_;
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
else
{
lean_inc(v_a_2557_);
lean_dec(v___x_2556_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2564_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2562_; 
if (v_isShared_2560_ == 0)
{
v___x_2562_ = v___x_2559_;
goto v_reusejp_2561_;
}
else
{
lean_object* v_reuseFailAlloc_2563_; 
v_reuseFailAlloc_2563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2563_, 0, v_a_2557_);
v___x_2562_ = v_reuseFailAlloc_2563_;
goto v_reusejp_2561_;
}
v_reusejp_2561_:
{
return v___x_2562_;
}
}
}
}
else
{
lean_dec_ref(v___f_2521_);
goto v___jp_2536_;
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v___x_2535_);
lean_dec_ref(v_body_2534_);
lean_dec_ref(v___f_2521_);
lean_dec(v_structName_2519_);
lean_dec_ref(v_struct_2518_);
lean_dec(v_fst_2517_);
lean_dec(v_a_2516_);
v_a_2565_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___x_2552_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___x_2552_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
v___jp_2536_:
{
lean_object* v_expr_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2550_; 
v_expr_2537_ = lean_ctor_get(v_struct_2518_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v_struct_2518_);
if (v_isSharedCheck_2550_ == 0)
{
lean_object* v_unused_2551_; 
v_unused_2551_ = lean_ctor_get(v_struct_2518_, 1);
lean_dec(v_unused_2551_);
v___x_2539_ = v_struct_2518_;
v_isShared_2540_ = v_isSharedCheck_2550_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_expr_2537_);
lean_dec(v_struct_2518_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2550_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2541_ = l_Lean_Expr_proj___override(v_structName_2519_, v_a_2516_, v_expr_2537_);
v___x_2542_ = lean_array_push(v_fst_2517_, v___x_2541_);
lean_inc(v_j_2525_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 1, v___x_2535_);
lean_ctor_set(v___x_2539_, 0, v_j_2525_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_j_2525_);
lean_ctor_set(v_reuseFailAlloc_2549_, 1, v___x_2535_);
v___x_2544_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; 
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2542_);
lean_ctor_set(v___x_2545_, 1, v___x_2544_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v_body_2534_);
lean_ctor_set(v___x_2546_, 1, v___x_2545_);
v___x_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2547_, 0, v___x_2546_);
v___x_2548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2548_, 0, v___x_2547_);
return v___x_2548_;
}
}
}
}
else
{
lean_object* v___x_2573_; lean_object* v___x_2574_; 
lean_dec(v_structName_2519_);
lean_dec_ref(v_struct_2518_);
lean_dec(v_a_2516_);
v___x_2573_ = lean_box(0);
lean_inc(v___y_2531_);
lean_inc_ref(v___y_2530_);
lean_inc(v___y_2529_);
lean_inc_ref(v___y_2528_);
lean_inc(v___y_2527_);
lean_inc(v___y_2526_);
v___x_2574_ = lean_apply_9(v___f_2521_, lean_box(0), v___x_2573_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, lean_box(0));
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2585_; 
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2585_ == 0)
{
lean_object* v_unused_2586_; 
v_unused_2586_ = lean_ctor_get(v___x_2574_, 0);
lean_dec(v_unused_2586_);
v___x_2576_ = v___x_2574_;
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
else
{
lean_dec(v___x_2574_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2585_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; 
lean_inc(v_j_2525_);
v___x_2578_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2578_, 0, v_j_2525_);
lean_ctor_set(v___x_2578_, 1, v_snd_2522_);
v___x_2579_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2579_, 0, v_fst_2517_);
lean_ctor_set(v___x_2579_, 1, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v_ctorType_2524_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
if (v_isShared_2577_ == 0)
{
lean_ctor_set(v___x_2576_, 0, v___x_2581_);
v___x_2583_ = v___x_2576_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
else
{
lean_object* v_a_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2594_; 
lean_dec_ref(v_ctorType_2524_);
lean_dec(v_snd_2522_);
lean_dec(v_fst_2517_);
v_a_2587_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2594_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2594_ == 0)
{
v___x_2589_ = v___x_2574_;
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_a_2587_);
lean_dec(v___x_2574_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2594_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2592_; 
if (v_isShared_2590_ == 0)
{
v___x_2592_ = v___x_2589_;
goto v_reusejp_2591_;
}
else
{
lean_object* v_reuseFailAlloc_2593_; 
v_reuseFailAlloc_2593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2593_, 0, v_a_2587_);
v___x_2592_ = v_reuseFailAlloc_2593_;
goto v_reusejp_2591_;
}
v_reusejp_2591_:
{
return v___x_2592_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2595_ = _args[0];
lean_object* v_fst_2596_ = _args[1];
lean_object* v_struct_2597_ = _args[2];
lean_object* v_structName_2598_ = _args[3];
lean_object* v_a_2599_ = _args[4];
lean_object* v___f_2600_ = _args[5];
lean_object* v_snd_2601_ = _args[6];
lean_object* v_____r_2602_ = _args[7];
lean_object* v_ctorType_2603_ = _args[8];
lean_object* v_j_2604_ = _args[9];
lean_object* v___y_2605_ = _args[10];
lean_object* v___y_2606_ = _args[11];
lean_object* v___y_2607_ = _args[12];
lean_object* v___y_2608_ = _args[13];
lean_object* v___y_2609_ = _args[14];
lean_object* v___y_2610_ = _args[15];
lean_object* v___y_2611_ = _args[16];
_start:
{
uint8_t v_a_23337__boxed_2612_; lean_object* v_res_2613_; 
v_a_23337__boxed_2612_ = lean_unbox(v_a_2599_);
v_res_2613_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2595_, v_fst_2596_, v_struct_2597_, v_structName_2598_, v_a_23337__boxed_2612_, v___f_2600_, v_snd_2601_, v_____r_2602_, v_ctorType_2603_, v_j_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec(v_j_2604_);
return v_res_2613_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2614_, lean_object* v_struct_2615_, lean_object* v_structName_2616_, uint8_t v_a_2617_, lean_object* v_idx_2618_, lean_object* v_a_2619_, lean_object* v_a_2620_, lean_object* v_b_2621_, lean_object* v___y_2622_, lean_object* v___y_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_){
_start:
{
lean_object* v___y_2630_; uint8_t v___x_2652_; 
v___x_2652_ = lean_nat_dec_le(v_a_2620_, v_upperBound_2614_);
if (v___x_2652_ == 0)
{
lean_object* v___x_2653_; 
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_idx_2618_);
lean_dec(v_structName_2616_);
lean_dec_ref(v_struct_2615_);
v___x_2653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2653_, 0, v_b_2621_);
return v___x_2653_;
}
else
{
lean_object* v_snd_2654_; lean_object* v_snd_2655_; lean_object* v_fst_2656_; lean_object* v_fst_2657_; lean_object* v_fst_2658_; lean_object* v_snd_2659_; lean_object* v___f_2660_; uint8_t v___x_2661_; 
v_snd_2654_ = lean_ctor_get(v_b_2621_, 1);
lean_inc(v_snd_2654_);
v_snd_2655_ = lean_ctor_get(v_snd_2654_, 1);
lean_inc(v_snd_2655_);
v_fst_2656_ = lean_ctor_get(v_b_2621_, 0);
lean_inc(v_fst_2656_);
lean_dec_ref(v_b_2621_);
v_fst_2657_ = lean_ctor_get(v_snd_2654_, 0);
lean_inc(v_fst_2657_);
lean_dec(v_snd_2654_);
v_fst_2658_ = lean_ctor_get(v_snd_2655_, 0);
lean_inc(v_fst_2658_);
v_snd_2659_ = lean_ctor_get(v_snd_2655_, 1);
lean_inc(v_snd_2659_);
lean_dec(v_snd_2655_);
lean_inc_ref(v_a_2619_);
lean_inc(v_idx_2618_);
lean_inc(v_structName_2616_);
lean_inc_ref(v_struct_2615_);
v___f_2660_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2660_, 0, v_struct_2615_);
lean_closure_set(v___f_2660_, 1, v_structName_2616_);
lean_closure_set(v___f_2660_, 2, v_idx_2618_);
lean_closure_set(v___f_2660_, 3, v_a_2619_);
v___x_2661_ = l_Lean_Expr_isForall(v_fst_2656_);
if (v___x_2661_ == 0)
{
lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2662_ = lean_expr_instantiate_rev_range(v_fst_2656_, v_fst_2658_, v_a_2620_, v_fst_2657_);
lean_dec(v_fst_2658_);
lean_dec(v_fst_2656_);
lean_inc(v___y_2627_);
lean_inc_ref(v___y_2626_);
lean_inc(v___y_2625_);
lean_inc_ref(v___y_2624_);
v___x_2663_ = lean_whnf(v___x_2662_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
if (lean_obj_tag(v___x_2663_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; 
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2663_, 1);
v___x_2665_ = lean_box(0);
lean_inc(v_structName_2616_);
lean_inc_ref(v_struct_2615_);
lean_inc(v_a_2620_);
v___x_2666_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2620_, v_fst_2657_, v_struct_2615_, v_structName_2616_, v_a_2617_, v___f_2660_, v_snd_2659_, v___x_2665_, v_a_2664_, v_a_2620_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
v___y_2630_ = v___x_2666_;
goto v___jp_2629_;
}
else
{
lean_object* v_a_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2674_; 
lean_dec_ref(v___f_2660_);
lean_dec(v_snd_2659_);
lean_dec(v_fst_2657_);
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_idx_2618_);
lean_dec(v_structName_2616_);
lean_dec_ref(v_struct_2615_);
v_a_2667_ = lean_ctor_get(v___x_2663_, 0);
v_isSharedCheck_2674_ = !lean_is_exclusive(v___x_2663_);
if (v_isSharedCheck_2674_ == 0)
{
v___x_2669_ = v___x_2663_;
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_a_2667_);
lean_dec(v___x_2663_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2674_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
lean_object* v___x_2672_; 
if (v_isShared_2670_ == 0)
{
v___x_2672_ = v___x_2669_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_a_2667_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
else
{
lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2675_ = lean_box(0);
lean_inc(v_structName_2616_);
lean_inc_ref(v_struct_2615_);
lean_inc(v_a_2620_);
v___x_2676_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2620_, v_fst_2657_, v_struct_2615_, v_structName_2616_, v_a_2617_, v___f_2660_, v_snd_2659_, v___x_2675_, v_fst_2656_, v_fst_2658_, v___y_2622_, v___y_2623_, v___y_2624_, v___y_2625_, v___y_2626_, v___y_2627_);
lean_dec(v_fst_2658_);
v___y_2630_ = v___x_2676_;
goto v___jp_2629_;
}
}
v___jp_2629_:
{
if (lean_obj_tag(v___y_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2643_; 
v_a_2631_ = lean_ctor_get(v___y_2630_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___y_2630_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2633_ = v___y_2630_;
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___y_2630_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2643_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
if (lean_obj_tag(v_a_2631_) == 0)
{
lean_object* v_a_2635_; lean_object* v___x_2637_; 
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_idx_2618_);
lean_dec(v_structName_2616_);
lean_dec_ref(v_struct_2615_);
v_a_2635_ = lean_ctor_get(v_a_2631_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v_a_2631_, 1);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 0, v_a_2635_);
v___x_2637_ = v___x_2633_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2635_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
else
{
lean_object* v_a_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
lean_del_object(v___x_2633_);
v_a_2639_ = lean_ctor_get(v_a_2631_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v_a_2631_, 1);
v___x_2640_ = lean_unsigned_to_nat(1u);
v___x_2641_ = lean_nat_add(v_a_2620_, v___x_2640_);
lean_dec(v_a_2620_);
v_a_2620_ = v___x_2641_;
v_b_2621_ = v_a_2639_;
goto _start;
}
}
}
else
{
lean_object* v_a_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2651_; 
lean_dec(v_a_2620_);
lean_dec_ref(v_a_2619_);
lean_dec(v_idx_2618_);
lean_dec(v_structName_2616_);
lean_dec_ref(v_struct_2615_);
v_a_2644_ = lean_ctor_get(v___y_2630_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___y_2630_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2646_ = v___y_2630_;
v_isShared_2647_ = v_isSharedCheck_2651_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_a_2644_);
lean_dec(v___y_2630_);
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
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_a_2644_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2677_, lean_object* v_struct_2678_, lean_object* v_structName_2679_, lean_object* v_a_2680_, lean_object* v_idx_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_b_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v_a_23494__boxed_2692_; lean_object* v_res_2693_; 
v_a_23494__boxed_2692_ = lean_unbox(v_a_2680_);
v_res_2693_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2677_, v_struct_2678_, v_structName_2679_, v_a_23494__boxed_2692_, v_idx_2681_, v_a_2682_, v_a_2683_, v_b_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
lean_dec(v_upperBound_2677_);
return v_res_2693_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2696_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2697_ = lean_unsigned_to_nat(18u);
v___x_2698_ = lean_unsigned_to_nat(1896u);
v___x_2699_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2700_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2701_ = l_mkPanicMessageWithDecl(v___x_2700_, v___x_2699_, v___x_2698_, v___x_2697_, v___x_2696_);
return v___x_2701_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2703_ = lean_unsigned_to_nat(0u);
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2706_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2707_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2706_);
lean_ctor_set(v___x_2707_, 1, v___x_2705_);
return v___x_2707_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2708_; lean_object* v_dummy_2709_; 
v___x_2708_ = lean_box(0);
v_dummy_2709_ = l_Lean_Expr_sort___override(v___x_2708_);
return v_dummy_2709_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2710_, lean_object* v_structName_2711_, lean_object* v_idx_2712_, lean_object* v_struct_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2728_; uint8_t v___x_2732_; 
v___x_2732_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2714_);
if (v___x_2732_ == 0)
{
lean_dec(v_idx_2712_);
lean_dec(v_structName_2711_);
if (lean_obj_tag(v_e_2710_) == 11)
{
lean_object* v_expr_2733_; lean_object* v_typeName_2734_; lean_object* v_idx_2735_; lean_object* v_struct_2736_; size_t v___x_2737_; size_t v___x_2738_; uint8_t v___x_2739_; 
v_expr_2733_ = lean_ctor_get(v_struct_2713_, 0);
lean_inc_ref(v_expr_2733_);
lean_dec_ref(v_struct_2713_);
v_typeName_2734_ = lean_ctor_get(v_e_2710_, 0);
v_idx_2735_ = lean_ctor_get(v_e_2710_, 1);
v_struct_2736_ = lean_ctor_get(v_e_2710_, 2);
v___x_2737_ = lean_ptr_addr(v_struct_2736_);
v___x_2738_ = lean_ptr_addr(v_expr_2733_);
v___x_2739_ = lean_usize_dec_eq(v___x_2737_, v___x_2738_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; 
lean_inc(v_idx_2735_);
lean_inc(v_typeName_2734_);
lean_dec_ref_known(v_e_2710_, 3);
v___x_2740_ = l_Lean_Expr_proj___override(v_typeName_2734_, v_idx_2735_, v_expr_2733_);
v___y_2728_ = v___x_2740_;
goto v___jp_2727_;
}
else
{
lean_dec_ref(v_expr_2733_);
v___y_2728_ = v_e_2710_;
goto v___jp_2727_;
}
}
else
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
lean_dec_ref(v_struct_2713_);
lean_dec_ref(v_e_2710_);
v___x_2741_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2742_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2741_);
v___y_2728_ = v___x_2742_;
goto v___jp_2727_;
}
}
else
{
lean_object* v___x_2743_; 
lean_inc_ref(v_struct_2713_);
v___x_2743_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2713_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2743_) == 0)
{
lean_object* v_a_2744_; lean_object* v___x_2745_; 
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref_known(v___x_2743_, 1);
lean_inc(v_a_2719_);
lean_inc_ref(v_a_2718_);
lean_inc(v_a_2717_);
lean_inc_ref(v_a_2716_);
v___x_2745_ = lean_whnf(v_a_2744_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2745_) == 0)
{
lean_object* v_a_2746_; lean_object* v___x_2747_; 
v_a_2746_ = lean_ctor_get(v___x_2745_, 0);
lean_inc_n(v_a_2746_, 2);
lean_dec_ref_known(v___x_2745_, 1);
v___x_2747_ = l_Lean_Meta_isProp(v_a_2746_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2749_ = l_Lean_Expr_getAppFn(v_a_2746_);
if (lean_obj_tag(v___x_2749_) == 4)
{
lean_object* v_declName_2750_; lean_object* v_us_2751_; lean_object* v___x_2752_; lean_object* v_env_2756_; uint8_t v___x_2757_; lean_object* v___x_2758_; 
v_declName_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_declName_2750_);
v_us_2751_ = lean_ctor_get(v___x_2749_, 1);
lean_inc(v_us_2751_);
lean_dec_ref_known(v___x_2749_, 2);
v___x_2752_ = lean_st_ref_get(v_a_2719_);
v_env_2756_ = lean_ctor_get(v___x_2752_, 0);
lean_inc_ref(v_env_2756_);
lean_dec(v___x_2752_);
v___x_2757_ = 0;
v___x_2758_ = l_Lean_Environment_find_x3f(v_env_2756_, v_declName_2750_, v___x_2757_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
v___x_2759_ = lean_box(0);
v___x_2760_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2713_, v_structName_2711_, v_idx_2712_, v_a_2746_, lean_box(0), v___x_2759_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
return v___x_2760_;
}
else
{
lean_object* v_val_2761_; 
v_val_2761_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_val_2761_);
lean_dec_ref_known(v___x_2758_, 1);
if (lean_obj_tag(v_val_2761_) == 5)
{
lean_object* v_val_2762_; lean_object* v_ctors_2763_; 
v_val_2762_ = lean_ctor_get(v_val_2761_, 0);
lean_inc_ref(v_val_2762_);
lean_dec_ref_known(v_val_2761_, 1);
v_ctors_2763_ = lean_ctor_get(v_val_2762_, 4);
lean_inc(v_ctors_2763_);
if (lean_obj_tag(v_ctors_2763_) == 1)
{
lean_object* v_tail_2764_; 
v_tail_2764_ = lean_ctor_get(v_ctors_2763_, 1);
if (lean_obj_tag(v_tail_2764_) == 0)
{
lean_object* v_toConstantVal_2765_; lean_object* v_numParams_2766_; lean_object* v_numIndices_2767_; lean_object* v_head_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2878_; 
v_toConstantVal_2765_ = lean_ctor_get(v_val_2762_, 0);
lean_inc_ref(v_toConstantVal_2765_);
v_numParams_2766_ = lean_ctor_get(v_val_2762_, 1);
lean_inc(v_numParams_2766_);
v_numIndices_2767_ = lean_ctor_get(v_val_2762_, 2);
lean_inc(v_numIndices_2767_);
lean_dec_ref(v_val_2762_);
v_head_2768_ = lean_ctor_get(v_ctors_2763_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v_ctors_2763_);
if (v_isSharedCheck_2878_ == 0)
{
lean_object* v_unused_2879_; 
v_unused_2879_ = lean_ctor_get(v_ctors_2763_, 1);
lean_dec(v_unused_2879_);
v___x_2770_ = v_ctors_2763_;
v_isShared_2771_ = v_isSharedCheck_2878_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_head_2768_);
lean_dec(v_ctors_2763_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2878_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2768_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
if (lean_obj_tag(v_a_2773_) == 6)
{
lean_object* v_val_2774_; lean_object* v___y_2776_; lean_object* v___y_2777_; lean_object* v___y_2778_; lean_object* v___y_2779_; lean_object* v___y_2780_; lean_object* v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2832_; lean_object* v___y_2833_; lean_object* v___y_2834_; lean_object* v___y_2835_; lean_object* v_name_2856_; uint8_t v___x_2857_; 
v_val_2774_ = lean_ctor_get(v_a_2773_, 0);
lean_inc_ref(v_val_2774_);
lean_dec_ref_known(v_a_2773_, 1);
v_name_2856_ = lean_ctor_get(v_toConstantVal_2765_, 0);
lean_inc(v_name_2856_);
lean_dec_ref(v_toConstantVal_2765_);
v___x_2857_ = lean_name_eq(v_name_2856_, v_structName_2711_);
lean_dec(v_name_2856_);
if (v___x_2857_ == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v_val_2774_);
lean_del_object(v___x_2770_);
lean_dec(v_numIndices_2767_);
lean_dec(v_numParams_2766_);
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
v___x_2858_ = lean_box(0);
v___x_2859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2713_, v_structName_2711_, v_idx_2712_, v_a_2746_, lean_box(0), v___x_2858_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
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
v___y_2830_ = v_a_2714_;
v___y_2831_ = v_a_2715_;
v___y_2832_ = v_a_2716_;
v___y_2833_ = v_a_2717_;
v___y_2834_ = v_a_2718_;
v___y_2835_ = v_a_2719_;
goto v___jp_2829_;
}
v___jp_2775_:
{
lean_object* v_toConstantVal_2783_; lean_object* v_name_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v_toConstantVal_2783_ = lean_ctor_get(v_val_2774_, 0);
lean_inc_ref(v_toConstantVal_2783_);
lean_dec_ref(v_val_2774_);
v_name_2784_ = lean_ctor_get(v_toConstantVal_2783_, 0);
lean_inc(v_name_2784_);
lean_dec_ref(v_toConstantVal_2783_);
v___x_2785_ = l_Lean_mkConst(v_name_2784_, v_us_2751_);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = l_Array_toSubarray___redArg(v___y_2776_, v___x_2786_, v_numParams_2766_);
v___x_2788_ = l_Subarray_copy___redArg(v___x_2787_);
v___x_2789_ = l_Lean_mkAppN(v___x_2785_, v___x_2788_);
lean_dec_ref(v___x_2788_);
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
v___x_2790_ = lean_infer_type(v___x_2789_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
v___x_2792_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2771_ == 0)
{
lean_ctor_set_tag(v___x_2770_, 0);
lean_ctor_set(v___x_2770_, 1, v___x_2792_);
lean_ctor_set(v___x_2770_, 0, v_a_2791_);
v___x_2794_ = v___x_2770_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2791_);
lean_ctor_set(v_reuseFailAlloc_2820_, 1, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
uint8_t v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_unbox(v_a_2748_);
lean_dec(v_a_2748_);
lean_inc_ref(v_struct_2713_);
lean_inc(v_idx_2712_);
v___x_2796_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2712_, v_struct_2713_, v_structName_2711_, v___x_2795_, v_idx_2712_, v_a_2746_, v___x_2786_, v___x_2794_, v___y_2777_, v___y_2778_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v_idx_2712_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; lean_object* v_snd_2798_; lean_object* v_snd_2799_; lean_object* v_snd_2800_; lean_object* v_expr_2801_; lean_object* v___x_2802_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref_known(v___x_2796_, 1);
v_snd_2798_ = lean_ctor_get(v_a_2797_, 1);
lean_inc(v_snd_2798_);
lean_dec(v_a_2797_);
v_snd_2799_ = lean_ctor_get(v_snd_2798_, 1);
lean_inc(v_snd_2799_);
lean_dec(v_snd_2798_);
v_snd_2800_ = lean_ctor_get(v_snd_2799_, 1);
lean_inc(v_snd_2800_);
lean_dec(v_snd_2799_);
v_expr_2801_ = lean_ctor_get(v_struct_2713_, 0);
lean_inc_ref(v_expr_2801_);
lean_dec_ref(v_struct_2713_);
v___x_2802_ = l_Lean_Expr_cleanupAnnotations(v_snd_2800_);
if (lean_obj_tag(v_e_2710_) == 11)
{
lean_object* v_typeName_2803_; lean_object* v_idx_2804_; lean_object* v_struct_2805_; size_t v___x_2806_; size_t v___x_2807_; uint8_t v___x_2808_; 
v_typeName_2803_ = lean_ctor_get(v_e_2710_, 0);
v_idx_2804_ = lean_ctor_get(v_e_2710_, 1);
v_struct_2805_ = lean_ctor_get(v_e_2710_, 2);
v___x_2806_ = lean_ptr_addr(v_struct_2805_);
v___x_2807_ = lean_ptr_addr(v_expr_2801_);
v___x_2808_ = lean_usize_dec_eq(v___x_2806_, v___x_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2809_; 
lean_inc(v_idx_2804_);
lean_inc(v_typeName_2803_);
lean_dec_ref_known(v_e_2710_, 3);
v___x_2809_ = l_Lean_Expr_proj___override(v_typeName_2803_, v_idx_2804_, v_expr_2801_);
v___y_2722_ = v___x_2802_;
v___y_2723_ = v___x_2809_;
goto v___jp_2721_;
}
else
{
lean_dec_ref(v_expr_2801_);
v___y_2722_ = v___x_2802_;
v___y_2723_ = v_e_2710_;
goto v___jp_2721_;
}
}
else
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
lean_dec_ref(v_expr_2801_);
lean_dec_ref(v_e_2710_);
v___x_2810_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2811_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2810_);
v___y_2722_ = v___x_2802_;
v___y_2723_ = v___x_2811_;
goto v___jp_2721_;
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v_struct_2713_);
lean_dec_ref(v_e_2710_);
v_a_2812_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2796_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2796_);
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
}
else
{
lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2828_; 
lean_del_object(v___x_2770_);
lean_dec(v_a_2748_);
lean_dec(v_a_2746_);
lean_dec_ref(v_struct_2713_);
lean_dec(v_idx_2712_);
lean_dec(v_structName_2711_);
lean_dec_ref(v_e_2710_);
v_a_2821_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2828_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2828_ == 0)
{
v___x_2823_ = v___x_2790_;
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2790_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2828_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2826_; 
if (v_isShared_2824_ == 0)
{
v___x_2826_ = v___x_2823_;
goto v_reusejp_2825_;
}
else
{
lean_object* v_reuseFailAlloc_2827_; 
v_reuseFailAlloc_2827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2827_, 0, v_a_2821_);
v___x_2826_ = v_reuseFailAlloc_2827_;
goto v_reusejp_2825_;
}
v_reusejp_2825_:
{
return v___x_2826_;
}
}
}
}
v___jp_2829_:
{
lean_object* v_dummy_2836_; lean_object* v_nargs_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; uint8_t v___x_2845_; 
v_dummy_2836_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2837_ = l_Lean_Expr_getAppNumArgs(v_a_2746_);
lean_inc(v_nargs_2837_);
v___x_2838_ = lean_mk_array(v_nargs_2837_, v_dummy_2836_);
v___x_2839_ = lean_unsigned_to_nat(1u);
v___x_2840_ = lean_nat_sub(v_nargs_2837_, v___x_2839_);
lean_dec(v_nargs_2837_);
lean_inc(v_a_2746_);
v___x_2841_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2746_, v___x_2838_, v___x_2840_);
v___x_2842_ = lean_nat_add(v_numParams_2766_, v_numIndices_2767_);
lean_dec(v_numIndices_2767_);
v___x_2843_ = lean_array_get_size(v___x_2841_);
v___x_2844_ = lean_nat_dec_eq(v___x_2842_, v___x_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_bool_not(v___x_2844_);
if (v___x_2845_ == 0)
{
v___y_2776_ = v___x_2841_;
v___y_2777_ = v___y_2830_;
v___y_2778_ = v___y_2831_;
v___y_2779_ = v___y_2832_;
v___y_2780_ = v___y_2833_;
v___y_2781_ = v___y_2834_;
v___y_2782_ = v___y_2835_;
goto v___jp_2775_;
}
else
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v___x_2841_);
lean_dec_ref(v_val_2774_);
lean_del_object(v___x_2770_);
lean_dec(v_numParams_2766_);
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
v___x_2846_ = lean_box(0);
v___x_2847_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2713_, v_structName_2711_, v_idx_2712_, v_a_2746_, lean_box(0), v___x_2846_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
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
}
else
{
lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec(v_a_2773_);
lean_del_object(v___x_2770_);
lean_dec(v_numIndices_2767_);
lean_dec(v_numParams_2766_);
lean_dec_ref(v_toConstantVal_2765_);
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
v___x_2868_ = lean_box(0);
v___x_2869_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2713_, v_structName_2711_, v_idx_2712_, v_a_2746_, lean_box(0), v___x_2868_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
return v___x_2869_;
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_del_object(v___x_2770_);
lean_dec(v_numIndices_2767_);
lean_dec(v_numParams_2766_);
lean_dec_ref(v_toConstantVal_2765_);
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec(v_a_2746_);
lean_dec_ref(v_struct_2713_);
lean_dec(v_idx_2712_);
lean_dec(v_structName_2711_);
lean_dec_ref(v_e_2710_);
v_a_2870_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2772_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2772_);
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
lean_dec_ref_known(v_ctors_2763_, 2);
lean_dec_ref(v_val_2762_);
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
goto v___jp_2753_;
}
}
else
{
lean_dec(v_ctors_2763_);
lean_dec_ref(v_val_2762_);
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
goto v___jp_2753_;
}
}
else
{
lean_object* v___x_2880_; lean_object* v___x_2881_; 
lean_dec(v_val_2761_);
lean_dec(v_us_2751_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
v___x_2880_ = lean_box(0);
v___x_2881_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2713_, v_structName_2711_, v_idx_2712_, v_a_2746_, lean_box(0), v___x_2880_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
return v___x_2881_;
}
}
v___jp_2753_:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = lean_box(0);
v___x_2755_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2713_, v_structName_2711_, v_idx_2712_, v_a_2746_, lean_box(0), v___x_2754_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
return v___x_2755_;
}
}
else
{
lean_object* v___x_2882_; lean_object* v___x_2883_; 
lean_dec_ref(v___x_2749_);
lean_dec(v_a_2748_);
lean_dec_ref(v_e_2710_);
v___x_2882_ = lean_box(0);
v___x_2883_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2713_, v_structName_2711_, v_idx_2712_, v_a_2746_, lean_box(0), v___x_2882_, v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_);
return v___x_2883_;
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_a_2746_);
lean_dec_ref(v_struct_2713_);
lean_dec(v_idx_2712_);
lean_dec(v_structName_2711_);
lean_dec_ref(v_e_2710_);
v_a_2884_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2747_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2747_);
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
lean_dec_ref(v_struct_2713_);
lean_dec(v_idx_2712_);
lean_dec(v_structName_2711_);
lean_dec_ref(v_e_2710_);
v_a_2892_ = lean_ctor_get(v___x_2745_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2745_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2745_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2745_);
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
lean_dec_ref(v_struct_2713_);
lean_dec(v_idx_2712_);
lean_dec(v_structName_2711_);
lean_dec_ref(v_e_2710_);
v_a_2900_ = lean_ctor_get(v___x_2743_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2743_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2743_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2743_);
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
v___jp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2724_, 0, v___y_2722_);
v___x_2725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2725_, 0, v___y_2723_);
lean_ctor_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2726_, 0, v___x_2725_);
return v___x_2726_;
}
v___jp_2727_:
{
lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v___x_2729_ = lean_box(0);
v___x_2730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2730_, 0, v___y_2728_);
lean_ctor_set(v___x_2730_, 1, v___x_2729_);
v___x_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2731_, 0, v___x_2730_);
return v___x_2731_;
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
uint8_t v_a_24020__boxed_2957_; lean_object* v_res_2958_; 
v_a_24020__boxed_2957_ = lean_unbox(v_a_2942_);
v_res_2958_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2939_, v_struct_2940_, v_structName_2941_, v_a_24020__boxed_2957_, v_idx_2943_, v_a_2944_, v_inst_2945_, v_R_2946_, v_a_2947_, v_b_2948_, v_c_2949_, v___y_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
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
lean_dec_ref_known(v___x_2973_, 1);
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
lean_dec_ref_known(v___x_3042_, 1);
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
lean_dec_ref_known(v_type_x3f_3062_, 1);
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
v_a_3025_ = v___x_3046_;
goto v___jp_3024_;
}
else
{
size_t v___x_3050_; size_t v___x_3051_; lean_object* v___x_3052_; 
v___x_3050_ = lean_usize_of_nat(v___x_3047_);
v___x_3051_ = ((size_t)0ULL);
v___x_3052_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_3010_, v___x_3050_, v___x_3051_, v___x_3046_, v_a_3013_, v_a_3014_, v_a_3015_, v_a_3016_, v_a_3017_);
if (lean_obj_tag(v___x_3052_) == 0)
{
lean_object* v_a_3053_; 
v_a_3053_ = lean_ctor_get(v___x_3052_, 0);
lean_inc(v_a_3053_);
lean_dec_ref_known(v___x_3052_, 1);
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
lean_dec_ref(v_a_3071_);
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
lean_dec_ref_known(v___x_3108_, 1);
if (lean_obj_tag(v_val_3110_) == 1)
{
uint8_t v_v_3111_; 
v_v_3111_ = lean_ctor_get_uint8(v_val_3110_, 0);
lean_dec_ref_known(v_val_3110_, 0);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3117_){
_start:
{
if (lean_obj_tag(v_x_3117_) == 0)
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v_a_3119_ = lean_ctor_get(v_x_3117_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v_x_3117_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v_x_3117_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v_x_3117_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
lean_ctor_set_tag(v___x_3121_, 1);
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
v_a_3127_ = lean_ctor_get(v_x_3117_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v_x_3117_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v_x_3117_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v_x_3117_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
lean_ctor_set_tag(v___x_3129_, 0);
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3138_, lean_object* v_opt_3139_){
_start:
{
lean_object* v_name_3140_; lean_object* v_defValue_3141_; lean_object* v_map_3142_; lean_object* v___x_3143_; 
v_name_3140_ = lean_ctor_get(v_opt_3139_, 0);
v_defValue_3141_ = lean_ctor_get(v_opt_3139_, 1);
v_map_3142_ = lean_ctor_get(v_opts_3138_, 0);
v___x_3143_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3142_, v_name_3140_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_inc(v_defValue_3141_);
return v_defValue_3141_;
}
else
{
lean_object* v_val_3144_; 
v_val_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_val_3144_);
lean_dec_ref_known(v___x_3143_, 1);
if (lean_obj_tag(v_val_3144_) == 3)
{
lean_object* v_v_3145_; 
v_v_3145_ = lean_ctor_get(v_val_3144_, 0);
lean_inc(v_v_3145_);
lean_dec_ref_known(v_val_3144_, 1);
return v_v_3145_;
}
else
{
lean_dec(v_val_3144_);
lean_inc(v_defValue_3141_);
return v_defValue_3141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3146_, lean_object* v_opt_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3146_, v_opt_3147_);
lean_dec_ref(v_opt_3147_);
lean_dec_ref(v_opts_3146_);
return v_res_3148_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3149_){
_start:
{
if (lean_obj_tag(v_e_3149_) == 0)
{
uint8_t v___x_3150_; 
v___x_3150_ = 2;
return v___x_3150_;
}
else
{
uint8_t v___x_3151_; 
v___x_3151_ = 0;
return v___x_3151_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3152_){
_start:
{
uint8_t v_res_3153_; lean_object* v_r_3154_; 
v_res_3153_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3152_);
lean_dec_ref(v_e_3152_);
v_r_3154_ = lean_box(v_res_3153_);
return v_r_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3155_, size_t v_i_3156_, lean_object* v_bs_3157_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = lean_usize_dec_lt(v_i_3156_, v_sz_3155_);
if (v___x_3158_ == 0)
{
return v_bs_3157_;
}
else
{
lean_object* v_v_3159_; lean_object* v_msg_3160_; lean_object* v___x_3161_; lean_object* v_bs_x27_3162_; size_t v___x_3163_; size_t v___x_3164_; lean_object* v___x_3165_; 
v_v_3159_ = lean_array_uget_borrowed(v_bs_3157_, v_i_3156_);
v_msg_3160_ = lean_ctor_get(v_v_3159_, 1);
lean_inc_ref(v_msg_3160_);
v___x_3161_ = lean_unsigned_to_nat(0u);
v_bs_x27_3162_ = lean_array_uset(v_bs_3157_, v_i_3156_, v___x_3161_);
v___x_3163_ = ((size_t)1ULL);
v___x_3164_ = lean_usize_add(v_i_3156_, v___x_3163_);
v___x_3165_ = lean_array_uset(v_bs_x27_3162_, v_i_3156_, v_msg_3160_);
v_i_3156_ = v___x_3164_;
v_bs_3157_ = v___x_3165_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3167_, lean_object* v_i_3168_, lean_object* v_bs_3169_){
_start:
{
size_t v_sz_boxed_3170_; size_t v_i_boxed_3171_; lean_object* v_res_3172_; 
v_sz_boxed_3170_ = lean_unbox_usize(v_sz_3167_);
lean_dec(v_sz_3167_);
v_i_boxed_3171_ = lean_unbox_usize(v_i_3168_);
lean_dec(v_i_3168_);
v_res_3172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3170_, v_i_boxed_3171_, v_bs_3169_);
return v_res_3172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3173_, lean_object* v_data_3174_, lean_object* v_ref_3175_, lean_object* v_msg_3176_, lean_object* v___y_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_){
_start:
{
lean_object* v_fileName_3182_; lean_object* v_fileMap_3183_; lean_object* v_options_3184_; lean_object* v_currRecDepth_3185_; lean_object* v_maxRecDepth_3186_; lean_object* v_ref_3187_; lean_object* v_currNamespace_3188_; lean_object* v_openDecls_3189_; lean_object* v_initHeartbeats_3190_; lean_object* v_maxHeartbeats_3191_; lean_object* v_quotContext_3192_; lean_object* v_currMacroScope_3193_; uint8_t v_diag_3194_; lean_object* v_cancelTk_x3f_3195_; uint8_t v_suppressElabErrors_3196_; lean_object* v_inheritedTraceOptions_3197_; lean_object* v___x_3198_; lean_object* v_traceState_3199_; lean_object* v_traces_3200_; lean_object* v_ref_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; size_t v_sz_3204_; size_t v___x_3205_; lean_object* v___x_3206_; lean_object* v_msg_3207_; lean_object* v___x_3208_; lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3246_; 
v_fileName_3182_ = lean_ctor_get(v___y_3179_, 0);
v_fileMap_3183_ = lean_ctor_get(v___y_3179_, 1);
v_options_3184_ = lean_ctor_get(v___y_3179_, 2);
v_currRecDepth_3185_ = lean_ctor_get(v___y_3179_, 3);
v_maxRecDepth_3186_ = lean_ctor_get(v___y_3179_, 4);
v_ref_3187_ = lean_ctor_get(v___y_3179_, 5);
v_currNamespace_3188_ = lean_ctor_get(v___y_3179_, 6);
v_openDecls_3189_ = lean_ctor_get(v___y_3179_, 7);
v_initHeartbeats_3190_ = lean_ctor_get(v___y_3179_, 8);
v_maxHeartbeats_3191_ = lean_ctor_get(v___y_3179_, 9);
v_quotContext_3192_ = lean_ctor_get(v___y_3179_, 10);
v_currMacroScope_3193_ = lean_ctor_get(v___y_3179_, 11);
v_diag_3194_ = lean_ctor_get_uint8(v___y_3179_, sizeof(void*)*14);
v_cancelTk_x3f_3195_ = lean_ctor_get(v___y_3179_, 12);
v_suppressElabErrors_3196_ = lean_ctor_get_uint8(v___y_3179_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3197_ = lean_ctor_get(v___y_3179_, 13);
v___x_3198_ = lean_st_ref_get(v___y_3180_);
v_traceState_3199_ = lean_ctor_get(v___x_3198_, 4);
lean_inc_ref(v_traceState_3199_);
lean_dec(v___x_3198_);
v_traces_3200_ = lean_ctor_get(v_traceState_3199_, 0);
lean_inc_ref(v_traces_3200_);
lean_dec_ref(v_traceState_3199_);
v_ref_3201_ = l_Lean_replaceRef(v_ref_3175_, v_ref_3187_);
lean_inc_ref(v_inheritedTraceOptions_3197_);
lean_inc(v_cancelTk_x3f_3195_);
lean_inc(v_currMacroScope_3193_);
lean_inc(v_quotContext_3192_);
lean_inc(v_maxHeartbeats_3191_);
lean_inc(v_initHeartbeats_3190_);
lean_inc(v_openDecls_3189_);
lean_inc(v_currNamespace_3188_);
lean_inc(v_maxRecDepth_3186_);
lean_inc(v_currRecDepth_3185_);
lean_inc_ref(v_options_3184_);
lean_inc_ref(v_fileMap_3183_);
lean_inc_ref(v_fileName_3182_);
v___x_3202_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3202_, 0, v_fileName_3182_);
lean_ctor_set(v___x_3202_, 1, v_fileMap_3183_);
lean_ctor_set(v___x_3202_, 2, v_options_3184_);
lean_ctor_set(v___x_3202_, 3, v_currRecDepth_3185_);
lean_ctor_set(v___x_3202_, 4, v_maxRecDepth_3186_);
lean_ctor_set(v___x_3202_, 5, v_ref_3201_);
lean_ctor_set(v___x_3202_, 6, v_currNamespace_3188_);
lean_ctor_set(v___x_3202_, 7, v_openDecls_3189_);
lean_ctor_set(v___x_3202_, 8, v_initHeartbeats_3190_);
lean_ctor_set(v___x_3202_, 9, v_maxHeartbeats_3191_);
lean_ctor_set(v___x_3202_, 10, v_quotContext_3192_);
lean_ctor_set(v___x_3202_, 11, v_currMacroScope_3193_);
lean_ctor_set(v___x_3202_, 12, v_cancelTk_x3f_3195_);
lean_ctor_set(v___x_3202_, 13, v_inheritedTraceOptions_3197_);
lean_ctor_set_uint8(v___x_3202_, sizeof(void*)*14, v_diag_3194_);
lean_ctor_set_uint8(v___x_3202_, sizeof(void*)*14 + 1, v_suppressElabErrors_3196_);
v___x_3203_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3200_);
lean_dec_ref(v_traces_3200_);
v_sz_3204_ = lean_array_size(v___x_3203_);
v___x_3205_ = ((size_t)0ULL);
v___x_3206_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3204_, v___x_3205_, v___x_3203_);
v_msg_3207_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3207_, 0, v_data_3174_);
lean_ctor_set(v_msg_3207_, 1, v_msg_3176_);
lean_ctor_set(v_msg_3207_, 2, v___x_3206_);
v___x_3208_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3207_, v___y_3177_, v___y_3178_, v___x_3202_, v___y_3180_);
lean_dec_ref_known(v___x_3202_, 14);
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3211_ = v___x_3208_;
v_isShared_3212_ = v_isSharedCheck_3246_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3208_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3246_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3213_; lean_object* v_traceState_3214_; lean_object* v_env_3215_; lean_object* v_nextMacroScope_3216_; lean_object* v_ngen_3217_; lean_object* v_auxDeclNGen_3218_; lean_object* v_cache_3219_; lean_object* v_messages_3220_; lean_object* v_infoState_3221_; lean_object* v_snapshotTasks_3222_; lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3245_; 
v___x_3213_ = lean_st_ref_take(v___y_3180_);
v_traceState_3214_ = lean_ctor_get(v___x_3213_, 4);
v_env_3215_ = lean_ctor_get(v___x_3213_, 0);
v_nextMacroScope_3216_ = lean_ctor_get(v___x_3213_, 1);
v_ngen_3217_ = lean_ctor_get(v___x_3213_, 2);
v_auxDeclNGen_3218_ = lean_ctor_get(v___x_3213_, 3);
v_cache_3219_ = lean_ctor_get(v___x_3213_, 5);
v_messages_3220_ = lean_ctor_get(v___x_3213_, 6);
v_infoState_3221_ = lean_ctor_get(v___x_3213_, 7);
v_snapshotTasks_3222_ = lean_ctor_get(v___x_3213_, 8);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3224_ = v___x_3213_;
v_isShared_3225_ = v_isSharedCheck_3245_;
goto v_resetjp_3223_;
}
else
{
lean_inc(v_snapshotTasks_3222_);
lean_inc(v_infoState_3221_);
lean_inc(v_messages_3220_);
lean_inc(v_cache_3219_);
lean_inc(v_traceState_3214_);
lean_inc(v_auxDeclNGen_3218_);
lean_inc(v_ngen_3217_);
lean_inc(v_nextMacroScope_3216_);
lean_inc(v_env_3215_);
lean_dec(v___x_3213_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3245_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
uint64_t v_tid_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3243_; 
v_tid_3226_ = lean_ctor_get_uint64(v_traceState_3214_, sizeof(void*)*1);
v_isSharedCheck_3243_ = !lean_is_exclusive(v_traceState_3214_);
if (v_isSharedCheck_3243_ == 0)
{
lean_object* v_unused_3244_; 
v_unused_3244_ = lean_ctor_get(v_traceState_3214_, 0);
lean_dec(v_unused_3244_);
v___x_3228_ = v_traceState_3214_;
v_isShared_3229_ = v_isSharedCheck_3243_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v_traceState_3214_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3243_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_ref_3175_);
lean_ctor_set(v___x_3230_, 1, v_a_3209_);
v___x_3231_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3173_, v___x_3230_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v___x_3231_);
v___x_3233_ = v___x_3228_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v___x_3231_);
lean_ctor_set_uint64(v_reuseFailAlloc_3242_, sizeof(void*)*1, v_tid_3226_);
v___x_3233_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3235_; 
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 4, v___x_3233_);
v___x_3235_ = v___x_3224_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_env_3215_);
lean_ctor_set(v_reuseFailAlloc_3241_, 1, v_nextMacroScope_3216_);
lean_ctor_set(v_reuseFailAlloc_3241_, 2, v_ngen_3217_);
lean_ctor_set(v_reuseFailAlloc_3241_, 3, v_auxDeclNGen_3218_);
lean_ctor_set(v_reuseFailAlloc_3241_, 4, v___x_3233_);
lean_ctor_set(v_reuseFailAlloc_3241_, 5, v_cache_3219_);
lean_ctor_set(v_reuseFailAlloc_3241_, 6, v_messages_3220_);
lean_ctor_set(v_reuseFailAlloc_3241_, 7, v_infoState_3221_);
lean_ctor_set(v_reuseFailAlloc_3241_, 8, v_snapshotTasks_3222_);
v___x_3235_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3236_ = lean_st_ref_set(v___y_3180_, v___x_3235_);
v___x_3237_ = lean_box(0);
if (v_isShared_3212_ == 0)
{
lean_ctor_set(v___x_3211_, 0, v___x_3237_);
v___x_3239_ = v___x_3211_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v___x_3237_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3247_, lean_object* v_data_3248_, lean_object* v_ref_3249_, lean_object* v_msg_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v_res_3256_; 
v_res_3256_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3247_, v_data_3248_, v_ref_3249_, v_msg_3250_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
lean_dec_ref(v___y_3251_);
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
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3260_; double v___x_3261_; 
v___x_3260_ = lean_unsigned_to_nat(1000u);
v___x_3261_ = lean_float_of_nat(v___x_3260_);
return v___x_3261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3262_, uint8_t v_collapsed_3263_, lean_object* v_tag_3264_, lean_object* v_opts_3265_, uint8_t v_clsEnabled_3266_, lean_object* v_oldTraces_3267_, lean_object* v_msg_3268_, lean_object* v_resStartStop_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v_fst_3277_; lean_object* v_snd_3278_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v_data_3282_; lean_object* v_fst_3293_; lean_object* v_snd_3294_; lean_object* v___x_3295_; uint8_t v___x_3296_; lean_object* v___y_3298_; lean_object* v_a_3299_; uint8_t v___y_3314_; double v___y_3345_; 
v_fst_3277_ = lean_ctor_get(v_resStartStop_3269_, 0);
lean_inc(v_fst_3277_);
v_snd_3278_ = lean_ctor_get(v_resStartStop_3269_, 1);
lean_inc(v_snd_3278_);
lean_dec_ref(v_resStartStop_3269_);
v_fst_3293_ = lean_ctor_get(v_snd_3278_, 0);
lean_inc(v_fst_3293_);
v_snd_3294_ = lean_ctor_get(v_snd_3278_, 1);
lean_inc(v_snd_3294_);
lean_dec(v_snd_3278_);
v___x_3295_ = l_Lean_trace_profiler;
v___x_3296_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3265_, v___x_3295_);
if (v___x_3296_ == 0)
{
v___y_3314_ = v___x_3296_;
goto v___jp_3313_;
}
else
{
lean_object* v___x_3350_; uint8_t v___x_3351_; 
v___x_3350_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3351_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3265_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v___x_3352_; lean_object* v___x_3353_; double v___x_3354_; double v___x_3355_; double v___x_3356_; 
v___x_3352_ = l_Lean_trace_profiler_threshold;
v___x_3353_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3265_, v___x_3352_);
v___x_3354_ = lean_float_of_nat(v___x_3353_);
v___x_3355_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3356_ = lean_float_div(v___x_3354_, v___x_3355_);
v___y_3345_ = v___x_3356_;
goto v___jp_3344_;
}
else
{
lean_object* v___x_3357_; lean_object* v___x_3358_; double v___x_3359_; 
v___x_3357_ = l_Lean_trace_profiler_threshold;
v___x_3358_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3265_, v___x_3357_);
v___x_3359_ = lean_float_of_nat(v___x_3358_);
v___y_3345_ = v___x_3359_;
goto v___jp_3344_;
}
}
v___jp_3279_:
{
lean_object* v___x_3283_; 
lean_inc(v___y_3281_);
v___x_3283_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3267_, v_data_3282_, v___y_3281_, v___y_3280_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v___x_3284_; 
lean_dec_ref_known(v___x_3283_, 1);
v___x_3284_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3277_);
return v___x_3284_;
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_fst_3277_);
v_a_3285_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3283_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3283_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
v___jp_3297_:
{
uint8_t v_result_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; double v___x_3303_; lean_object* v_data_3304_; 
v_result_3300_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3277_);
v___x_3301_ = lean_box(v_result_3300_);
v___x_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
v___x_3303_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3264_);
lean_inc_ref(v___x_3302_);
lean_inc(v_cls_3262_);
v_data_3304_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3304_, 0, v_cls_3262_);
lean_ctor_set(v_data_3304_, 1, v___x_3302_);
lean_ctor_set(v_data_3304_, 2, v_tag_3264_);
lean_ctor_set_float(v_data_3304_, sizeof(void*)*3, v___x_3303_);
lean_ctor_set_float(v_data_3304_, sizeof(void*)*3 + 8, v___x_3303_);
lean_ctor_set_uint8(v_data_3304_, sizeof(void*)*3 + 16, v_collapsed_3263_);
if (v___x_3296_ == 0)
{
lean_dec_ref_known(v___x_3302_, 1);
lean_dec(v_snd_3294_);
lean_dec(v_fst_3293_);
lean_dec_ref(v_tag_3264_);
lean_dec(v_cls_3262_);
v___y_3280_ = v_a_3299_;
v___y_3281_ = v___y_3298_;
v_data_3282_ = v_data_3304_;
goto v___jp_3279_;
}
else
{
lean_object* v_data_3305_; double v___x_3306_; double v___x_3307_; 
lean_dec_ref_known(v_data_3304_, 3);
v_data_3305_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3305_, 0, v_cls_3262_);
lean_ctor_set(v_data_3305_, 1, v___x_3302_);
lean_ctor_set(v_data_3305_, 2, v_tag_3264_);
v___x_3306_ = lean_unbox_float(v_fst_3293_);
lean_dec(v_fst_3293_);
lean_ctor_set_float(v_data_3305_, sizeof(void*)*3, v___x_3306_);
v___x_3307_ = lean_unbox_float(v_snd_3294_);
lean_dec(v_snd_3294_);
lean_ctor_set_float(v_data_3305_, sizeof(void*)*3 + 8, v___x_3307_);
lean_ctor_set_uint8(v_data_3305_, sizeof(void*)*3 + 16, v_collapsed_3263_);
v___y_3280_ = v_a_3299_;
v___y_3281_ = v___y_3298_;
v_data_3282_ = v_data_3305_;
goto v___jp_3279_;
}
}
v___jp_3308_:
{
lean_object* v_ref_3309_; lean_object* v___x_3310_; 
v_ref_3309_ = lean_ctor_get(v___y_3274_, 5);
lean_inc(v___y_3275_);
lean_inc_ref(v___y_3274_);
lean_inc(v___y_3273_);
lean_inc_ref(v___y_3272_);
lean_inc(v___y_3271_);
lean_inc(v___y_3270_);
lean_inc(v_fst_3277_);
v___x_3310_ = lean_apply_8(v_msg_3268_, v_fst_3277_, v___y_3270_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, lean_box(0));
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v___y_3298_ = v_ref_3309_;
v_a_3299_ = v_a_3311_;
goto v___jp_3297_;
}
else
{
lean_object* v___x_3312_; 
lean_dec_ref_known(v___x_3310_, 1);
v___x_3312_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3298_ = v_ref_3309_;
v_a_3299_ = v___x_3312_;
goto v___jp_3297_;
}
}
v___jp_3313_:
{
if (v_clsEnabled_3266_ == 0)
{
if (v___y_3314_ == 0)
{
lean_object* v___x_3315_; lean_object* v_traceState_3316_; lean_object* v_env_3317_; lean_object* v_nextMacroScope_3318_; lean_object* v_ngen_3319_; lean_object* v_auxDeclNGen_3320_; lean_object* v_cache_3321_; lean_object* v_messages_3322_; lean_object* v_infoState_3323_; lean_object* v_snapshotTasks_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3343_; 
lean_dec(v_snd_3294_);
lean_dec(v_fst_3293_);
lean_dec_ref(v_msg_3268_);
lean_dec_ref(v_tag_3264_);
lean_dec(v_cls_3262_);
v___x_3315_ = lean_st_ref_take(v___y_3275_);
v_traceState_3316_ = lean_ctor_get(v___x_3315_, 4);
v_env_3317_ = lean_ctor_get(v___x_3315_, 0);
v_nextMacroScope_3318_ = lean_ctor_get(v___x_3315_, 1);
v_ngen_3319_ = lean_ctor_get(v___x_3315_, 2);
v_auxDeclNGen_3320_ = lean_ctor_get(v___x_3315_, 3);
v_cache_3321_ = lean_ctor_get(v___x_3315_, 5);
v_messages_3322_ = lean_ctor_get(v___x_3315_, 6);
v_infoState_3323_ = lean_ctor_get(v___x_3315_, 7);
v_snapshotTasks_3324_ = lean_ctor_get(v___x_3315_, 8);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3315_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3326_ = v___x_3315_;
v_isShared_3327_ = v_isSharedCheck_3343_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_snapshotTasks_3324_);
lean_inc(v_infoState_3323_);
lean_inc(v_messages_3322_);
lean_inc(v_cache_3321_);
lean_inc(v_traceState_3316_);
lean_inc(v_auxDeclNGen_3320_);
lean_inc(v_ngen_3319_);
lean_inc(v_nextMacroScope_3318_);
lean_inc(v_env_3317_);
lean_dec(v___x_3315_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3343_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
uint64_t v_tid_3328_; lean_object* v_traces_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3342_; 
v_tid_3328_ = lean_ctor_get_uint64(v_traceState_3316_, sizeof(void*)*1);
v_traces_3329_ = lean_ctor_get(v_traceState_3316_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v_traceState_3316_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3331_ = v_traceState_3316_;
v_isShared_3332_ = v_isSharedCheck_3342_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_traces_3329_);
lean_dec(v_traceState_3316_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3342_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
v___x_3333_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3267_, v_traces_3329_);
lean_dec_ref(v_traces_3329_);
if (v_isShared_3332_ == 0)
{
lean_ctor_set(v___x_3331_, 0, v___x_3333_);
v___x_3335_ = v___x_3331_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3333_);
lean_ctor_set_uint64(v_reuseFailAlloc_3341_, sizeof(void*)*1, v_tid_3328_);
v___x_3335_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
lean_object* v___x_3337_; 
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 4, v___x_3335_);
v___x_3337_ = v___x_3326_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_env_3317_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_nextMacroScope_3318_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_ngen_3319_);
lean_ctor_set(v_reuseFailAlloc_3340_, 3, v_auxDeclNGen_3320_);
lean_ctor_set(v_reuseFailAlloc_3340_, 4, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3340_, 5, v_cache_3321_);
lean_ctor_set(v_reuseFailAlloc_3340_, 6, v_messages_3322_);
lean_ctor_set(v_reuseFailAlloc_3340_, 7, v_infoState_3323_);
lean_ctor_set(v_reuseFailAlloc_3340_, 8, v_snapshotTasks_3324_);
v___x_3337_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; lean_object* v___x_3339_; 
v___x_3338_ = lean_st_ref_set(v___y_3275_, v___x_3337_);
v___x_3339_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3277_);
return v___x_3339_;
}
}
}
}
}
else
{
goto v___jp_3308_;
}
}
else
{
goto v___jp_3308_;
}
}
v___jp_3344_:
{
double v___x_3346_; double v___x_3347_; double v___x_3348_; uint8_t v___x_3349_; 
v___x_3346_ = lean_unbox_float(v_snd_3294_);
v___x_3347_ = lean_unbox_float(v_fst_3293_);
v___x_3348_ = lean_float_sub(v___x_3346_, v___x_3347_);
v___x_3349_ = lean_float_decLt(v___y_3345_, v___x_3348_);
v___y_3314_ = v___x_3349_;
goto v___jp_3313_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3360_, lean_object* v_collapsed_3361_, lean_object* v_tag_3362_, lean_object* v_opts_3363_, lean_object* v_clsEnabled_3364_, lean_object* v_oldTraces_3365_, lean_object* v_msg_3366_, lean_object* v_resStartStop_3367_, lean_object* v___y_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
uint8_t v_collapsed_boxed_3375_; uint8_t v_clsEnabled_boxed_3376_; lean_object* v_res_3377_; 
v_collapsed_boxed_3375_ = lean_unbox(v_collapsed_3361_);
v_clsEnabled_boxed_3376_ = lean_unbox(v_clsEnabled_3364_);
v_res_3377_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3360_, v_collapsed_boxed_3375_, v_tag_3362_, v_opts_3363_, v_clsEnabled_boxed_3376_, v_oldTraces_3365_, v_msg_3366_, v_resStartStop_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec(v___y_3368_);
lean_dec_ref(v_opts_3363_);
return v_res_3377_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v___x_3378_ = lean_unsigned_to_nat(32u);
v___x_3379_ = lean_mk_empty_array_with_capacity(v___x_3378_);
v___x_3380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3380_, 0, v___x_3379_);
return v___x_3380_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v___x_3381_ = ((size_t)5ULL);
v___x_3382_ = lean_unsigned_to_nat(0u);
v___x_3383_ = lean_unsigned_to_nat(32u);
v___x_3384_ = lean_mk_empty_array_with_capacity(v___x_3383_);
v___x_3385_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3386_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
lean_ctor_set(v___x_3386_, 1, v___x_3384_);
lean_ctor_set(v___x_3386_, 2, v___x_3382_);
lean_ctor_set(v___x_3386_, 3, v___x_3382_);
lean_ctor_set_usize(v___x_3386_, 4, v___x_3381_);
return v___x_3386_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3387_){
_start:
{
lean_object* v___x_3389_; lean_object* v_traceState_3390_; lean_object* v_traces_3391_; lean_object* v___x_3392_; lean_object* v_traceState_3393_; lean_object* v_env_3394_; lean_object* v_nextMacroScope_3395_; lean_object* v_ngen_3396_; lean_object* v_auxDeclNGen_3397_; lean_object* v_cache_3398_; lean_object* v_messages_3399_; lean_object* v_infoState_3400_; lean_object* v_snapshotTasks_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3420_; 
v___x_3389_ = lean_st_ref_get(v___y_3387_);
v_traceState_3390_ = lean_ctor_get(v___x_3389_, 4);
lean_inc_ref(v_traceState_3390_);
lean_dec(v___x_3389_);
v_traces_3391_ = lean_ctor_get(v_traceState_3390_, 0);
lean_inc_ref(v_traces_3391_);
lean_dec_ref(v_traceState_3390_);
v___x_3392_ = lean_st_ref_take(v___y_3387_);
v_traceState_3393_ = lean_ctor_get(v___x_3392_, 4);
v_env_3394_ = lean_ctor_get(v___x_3392_, 0);
v_nextMacroScope_3395_ = lean_ctor_get(v___x_3392_, 1);
v_ngen_3396_ = lean_ctor_get(v___x_3392_, 2);
v_auxDeclNGen_3397_ = lean_ctor_get(v___x_3392_, 3);
v_cache_3398_ = lean_ctor_get(v___x_3392_, 5);
v_messages_3399_ = lean_ctor_get(v___x_3392_, 6);
v_infoState_3400_ = lean_ctor_get(v___x_3392_, 7);
v_snapshotTasks_3401_ = lean_ctor_get(v___x_3392_, 8);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3392_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3403_ = v___x_3392_;
v_isShared_3404_ = v_isSharedCheck_3420_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_snapshotTasks_3401_);
lean_inc(v_infoState_3400_);
lean_inc(v_messages_3399_);
lean_inc(v_cache_3398_);
lean_inc(v_traceState_3393_);
lean_inc(v_auxDeclNGen_3397_);
lean_inc(v_ngen_3396_);
lean_inc(v_nextMacroScope_3395_);
lean_inc(v_env_3394_);
lean_dec(v___x_3392_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3420_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint64_t v_tid_3405_; lean_object* v___x_3407_; uint8_t v_isShared_3408_; uint8_t v_isSharedCheck_3418_; 
v_tid_3405_ = lean_ctor_get_uint64(v_traceState_3393_, sizeof(void*)*1);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_traceState_3393_);
if (v_isSharedCheck_3418_ == 0)
{
lean_object* v_unused_3419_; 
v_unused_3419_ = lean_ctor_get(v_traceState_3393_, 0);
lean_dec(v_unused_3419_);
v___x_3407_ = v_traceState_3393_;
v_isShared_3408_ = v_isSharedCheck_3418_;
goto v_resetjp_3406_;
}
else
{
lean_dec(v_traceState_3393_);
v___x_3407_ = lean_box(0);
v_isShared_3408_ = v_isSharedCheck_3418_;
goto v_resetjp_3406_;
}
v_resetjp_3406_:
{
lean_object* v___x_3409_; lean_object* v___x_3411_; 
v___x_3409_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3408_ == 0)
{
lean_ctor_set(v___x_3407_, 0, v___x_3409_);
v___x_3411_ = v___x_3407_;
goto v_reusejp_3410_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v___x_3409_);
lean_ctor_set_uint64(v_reuseFailAlloc_3417_, sizeof(void*)*1, v_tid_3405_);
v___x_3411_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3410_;
}
v_reusejp_3410_:
{
lean_object* v___x_3413_; 
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 4, v___x_3411_);
v___x_3413_ = v___x_3403_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_env_3394_);
lean_ctor_set(v_reuseFailAlloc_3416_, 1, v_nextMacroScope_3395_);
lean_ctor_set(v_reuseFailAlloc_3416_, 2, v_ngen_3396_);
lean_ctor_set(v_reuseFailAlloc_3416_, 3, v_auxDeclNGen_3397_);
lean_ctor_set(v_reuseFailAlloc_3416_, 4, v___x_3411_);
lean_ctor_set(v_reuseFailAlloc_3416_, 5, v_cache_3398_);
lean_ctor_set(v_reuseFailAlloc_3416_, 6, v_messages_3399_);
lean_ctor_set(v_reuseFailAlloc_3416_, 7, v_infoState_3400_);
lean_ctor_set(v_reuseFailAlloc_3416_, 8, v_snapshotTasks_3401_);
v___x_3413_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_st_ref_set(v___y_3387_, v___x_3413_);
v___x_3415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3415_, 0, v_traces_3391_);
return v___x_3415_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3421_);
lean_dec(v___y_3421_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v___x_3432_; 
lean_inc(v___y_3426_);
lean_inc(v___y_3425_);
v___x_3432_ = lean_apply_7(v_x_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, lean_box(0));
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3433_, v___y_3434_, v___y_3435_, v___y_3436_, v___y_3437_, v___y_3438_, v___y_3439_);
lean_dec(v___y_3435_);
lean_dec(v___y_3434_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3442_, lean_object* v_localInsts_3443_, lean_object* v_x_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___f_3452_; lean_object* v___x_3453_; 
lean_inc(v___y_3446_);
lean_inc(v___y_3445_);
v___f_3452_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3452_, 0, v_x_3444_);
lean_closure_set(v___f_3452_, 1, v___y_3445_);
lean_closure_set(v___f_3452_, 2, v___y_3446_);
v___x_3453_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3442_, v_localInsts_3443_, v___f_3452_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3453_) == 0)
{
return v___x_3453_;
}
else
{
lean_object* v_a_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3461_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3461_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3461_ == 0)
{
v___x_3456_ = v___x_3453_;
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_a_3454_);
lean_dec(v___x_3453_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3461_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3459_; 
if (v_isShared_3457_ == 0)
{
v___x_3459_ = v___x_3456_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v_a_3454_);
v___x_3459_ = v_reuseFailAlloc_3460_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
return v___x_3459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3462_, lean_object* v_localInsts_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_, lean_object* v___y_3470_, lean_object* v___y_3471_){
_start:
{
lean_object* v_res_3472_; 
v_res_3472_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3462_, v_localInsts_3463_, v_x_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_, v___y_3470_);
lean_dec(v___y_3470_);
lean_dec_ref(v___y_3469_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec(v___y_3465_);
return v_res_3472_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3473_){
_start:
{
lean_object* v___x_3475_; lean_object* v_ngen_3476_; lean_object* v_namePrefix_3477_; lean_object* v_idx_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3507_; 
v___x_3475_ = lean_st_ref_get(v___y_3473_);
v_ngen_3476_ = lean_ctor_get(v___x_3475_, 2);
lean_inc_ref(v_ngen_3476_);
lean_dec(v___x_3475_);
v_namePrefix_3477_ = lean_ctor_get(v_ngen_3476_, 0);
v_idx_3478_ = lean_ctor_get(v_ngen_3476_, 1);
v_isSharedCheck_3507_ = !lean_is_exclusive(v_ngen_3476_);
if (v_isSharedCheck_3507_ == 0)
{
v___x_3480_ = v_ngen_3476_;
v_isShared_3481_ = v_isSharedCheck_3507_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_idx_3478_);
lean_inc(v_namePrefix_3477_);
lean_dec(v_ngen_3476_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3507_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3482_; lean_object* v_env_3483_; lean_object* v_nextMacroScope_3484_; lean_object* v_auxDeclNGen_3485_; lean_object* v_traceState_3486_; lean_object* v_cache_3487_; lean_object* v_messages_3488_; lean_object* v_infoState_3489_; lean_object* v_snapshotTasks_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3505_; 
v___x_3482_ = lean_st_ref_take(v___y_3473_);
v_env_3483_ = lean_ctor_get(v___x_3482_, 0);
v_nextMacroScope_3484_ = lean_ctor_get(v___x_3482_, 1);
v_auxDeclNGen_3485_ = lean_ctor_get(v___x_3482_, 3);
v_traceState_3486_ = lean_ctor_get(v___x_3482_, 4);
v_cache_3487_ = lean_ctor_get(v___x_3482_, 5);
v_messages_3488_ = lean_ctor_get(v___x_3482_, 6);
v_infoState_3489_ = lean_ctor_get(v___x_3482_, 7);
v_snapshotTasks_3490_ = lean_ctor_get(v___x_3482_, 8);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3482_);
if (v_isSharedCheck_3505_ == 0)
{
lean_object* v_unused_3506_; 
v_unused_3506_ = lean_ctor_get(v___x_3482_, 2);
lean_dec(v_unused_3506_);
v___x_3492_ = v___x_3482_;
v_isShared_3493_ = v_isSharedCheck_3505_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_snapshotTasks_3490_);
lean_inc(v_infoState_3489_);
lean_inc(v_messages_3488_);
lean_inc(v_cache_3487_);
lean_inc(v_traceState_3486_);
lean_inc(v_auxDeclNGen_3485_);
lean_inc(v_nextMacroScope_3484_);
lean_inc(v_env_3483_);
lean_dec(v___x_3482_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3505_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v_r_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3498_; 
lean_inc(v_idx_3478_);
lean_inc(v_namePrefix_3477_);
v_r_3494_ = l_Lean_Name_num___override(v_namePrefix_3477_, v_idx_3478_);
v___x_3495_ = lean_unsigned_to_nat(1u);
v___x_3496_ = lean_nat_add(v_idx_3478_, v___x_3495_);
lean_dec(v_idx_3478_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 1, v___x_3496_);
v___x_3498_ = v___x_3480_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_namePrefix_3477_);
lean_ctor_set(v_reuseFailAlloc_3504_, 1, v___x_3496_);
v___x_3498_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
lean_object* v___x_3500_; 
if (v_isShared_3493_ == 0)
{
lean_ctor_set(v___x_3492_, 2, v___x_3498_);
v___x_3500_ = v___x_3492_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_env_3483_);
lean_ctor_set(v_reuseFailAlloc_3503_, 1, v_nextMacroScope_3484_);
lean_ctor_set(v_reuseFailAlloc_3503_, 2, v___x_3498_);
lean_ctor_set(v_reuseFailAlloc_3503_, 3, v_auxDeclNGen_3485_);
lean_ctor_set(v_reuseFailAlloc_3503_, 4, v_traceState_3486_);
lean_ctor_set(v_reuseFailAlloc_3503_, 5, v_cache_3487_);
lean_ctor_set(v_reuseFailAlloc_3503_, 6, v_messages_3488_);
lean_ctor_set(v_reuseFailAlloc_3503_, 7, v_infoState_3489_);
lean_ctor_set(v_reuseFailAlloc_3503_, 8, v_snapshotTasks_3490_);
v___x_3500_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
lean_object* v___x_3501_; lean_object* v___x_3502_; 
v___x_3501_ = lean_st_ref_set(v___y_3473_, v___x_3500_);
v___x_3502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3502_, 0, v_r_3494_);
return v___x_3502_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3508_, lean_object* v___y_3509_){
_start:
{
lean_object* v_res_3510_; 
v_res_3510_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3508_);
lean_dec(v___y_3508_);
return v_res_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
v___x_3518_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3516_);
v_a_3519_ = lean_ctor_get(v___x_3518_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3518_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3518_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3518_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3527_, lean_object* v___y_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
lean_dec(v___y_3528_);
lean_dec(v___y_3527_);
return v_res_3534_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3536_; lean_object* v___x_3537_; 
v___x_3536_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3537_ = l_Lean_stringToMessageData(v___x_3536_);
return v___x_3537_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; 
v___x_3539_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3540_ = l_Lean_stringToMessageData(v___x_3539_);
return v___x_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3543_, lean_object* v_x_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_){
_start:
{
lean_object* v___x_3552_; lean_object* v___y_3554_; uint8_t v___x_3563_; 
v___x_3552_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3563_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3545_);
if (v___x_3563_ == 0)
{
lean_object* v___x_3564_; 
v___x_3564_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3554_ = v___x_3564_;
goto v___jp_3553_;
}
else
{
lean_object* v___x_3565_; 
v___x_3565_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3554_ = v___x_3565_;
goto v___jp_3553_;
}
v___jp_3553_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
lean_inc_ref(v___y_3554_);
v___x_3555_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3555_, 0, v___y_3554_);
v___x_3556_ = l_Lean_MessageData_ofFormat(v___x_3555_);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3552_);
lean_ctor_set(v___x_3557_, 1, v___x_3556_);
v___x_3558_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = l_Lean_indentExpr(v_e_3543_);
v___x_3561_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3559_);
lean_ctor_set(v___x_3561_, 1, v___x_3560_);
v___x_3562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3562_, 0, v___x_3561_);
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3566_, lean_object* v_x_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3566_, v_x_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec(v___y_3569_);
lean_dec(v___y_3568_);
lean_dec_ref(v_x_3567_);
return v_res_3575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3576_, lean_object* v_x_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_){
_start:
{
lean_object* v_keyedConfig_3585_; uint8_t v_trackZetaDelta_3586_; lean_object* v_zetaDeltaSet_3587_; lean_object* v_localInstances_3588_; lean_object* v_defEqCtx_x3f_3589_; lean_object* v_synthPendingDepth_3590_; lean_object* v_canUnfold_x3f_3591_; uint8_t v_univApprox_3592_; uint8_t v_inTypeClassResolution_3593_; uint8_t v_cacheInferType_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; 
v_keyedConfig_3585_ = lean_ctor_get(v___y_3580_, 0);
v_trackZetaDelta_3586_ = lean_ctor_get_uint8(v___y_3580_, sizeof(void*)*7);
v_zetaDeltaSet_3587_ = lean_ctor_get(v___y_3580_, 1);
v_localInstances_3588_ = lean_ctor_get(v___y_3580_, 3);
v_defEqCtx_x3f_3589_ = lean_ctor_get(v___y_3580_, 4);
v_synthPendingDepth_3590_ = lean_ctor_get(v___y_3580_, 5);
v_canUnfold_x3f_3591_ = lean_ctor_get(v___y_3580_, 6);
v_univApprox_3592_ = lean_ctor_get_uint8(v___y_3580_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3593_ = lean_ctor_get_uint8(v___y_3580_, sizeof(void*)*7 + 2);
v_cacheInferType_3594_ = lean_ctor_get_uint8(v___y_3580_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_3591_);
lean_inc(v_synthPendingDepth_3590_);
lean_inc(v_defEqCtx_x3f_3589_);
lean_inc_ref(v_localInstances_3588_);
lean_inc(v_zetaDeltaSet_3587_);
lean_inc_ref(v_keyedConfig_3585_);
v___x_3595_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3595_, 0, v_keyedConfig_3585_);
lean_ctor_set(v___x_3595_, 1, v_zetaDeltaSet_3587_);
lean_ctor_set(v___x_3595_, 2, v_lctx_3576_);
lean_ctor_set(v___x_3595_, 3, v_localInstances_3588_);
lean_ctor_set(v___x_3595_, 4, v_defEqCtx_x3f_3589_);
lean_ctor_set(v___x_3595_, 5, v_synthPendingDepth_3590_);
lean_ctor_set(v___x_3595_, 6, v_canUnfold_x3f_3591_);
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*7, v_trackZetaDelta_3586_);
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*7 + 1, v_univApprox_3592_);
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3593_);
lean_ctor_set_uint8(v___x_3595_, sizeof(void*)*7 + 3, v_cacheInferType_3594_);
lean_inc(v___y_3583_);
lean_inc_ref(v___y_3582_);
lean_inc(v___y_3581_);
lean_inc(v___y_3579_);
lean_inc(v___y_3578_);
v___x_3596_ = lean_apply_7(v_x_3577_, v___y_3578_, v___y_3579_, v___x_3595_, v___y_3581_, v___y_3582_, v___y_3583_, lean_box(0));
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_object* v_a_3597_; lean_object* v___x_3599_; uint8_t v_isShared_3600_; uint8_t v_isSharedCheck_3604_; 
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
v_isSharedCheck_3604_ = !lean_is_exclusive(v___x_3596_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3599_ = v___x_3596_;
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
else
{
lean_inc(v_a_3597_);
lean_dec(v___x_3596_);
v___x_3599_ = lean_box(0);
v_isShared_3600_ = v_isSharedCheck_3604_;
goto v_resetjp_3598_;
}
v_resetjp_3598_:
{
lean_object* v___x_3602_; 
if (v_isShared_3600_ == 0)
{
v___x_3602_ = v___x_3599_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v_a_3597_);
v___x_3602_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
return v___x_3602_;
}
}
}
else
{
return v___x_3596_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3605_, lean_object* v_x_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
lean_object* v_res_3614_; 
v_res_3614_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3605_, v_x_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_, v___y_3611_, v___y_3612_);
lean_dec(v___y_3612_);
lean_dec_ref(v___y_3611_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec(v___y_3607_);
return v_res_3614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3617_, lean_object* v_letFVars_3618_, lean_object* v_lctx_3619_, lean_object* v_v_3620_, lean_object* v_e_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3629_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3630_ = lean_expr_instantiate_rev(v_e_3621_, v_fvars_3617_);
v___x_3631_ = lean_apply_1(v_v_3620_, v___x_3630_);
v___x_3632_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3632_, 0, lean_box(0));
lean_closure_set(v___x_3632_, 1, v_letFVars_3618_);
lean_closure_set(v___x_3632_, 2, v___x_3631_);
v___x_3633_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3619_, v___x_3629_, v___x_3632_, v___y_3622_, v___y_3623_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_);
return v___x_3633_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3634_, lean_object* v_letFVars_3635_, lean_object* v_lctx_3636_, lean_object* v_v_3637_, lean_object* v_e_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_res_3646_; 
v_res_3646_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3634_, v_letFVars_3635_, v_lctx_3636_, v_v_3637_, v_e_3638_, v___y_3639_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
lean_dec(v___y_3644_);
lean_dec_ref(v___y_3643_);
lean_dec(v___y_3642_);
lean_dec_ref(v___y_3641_);
lean_dec(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v_e_3638_);
lean_dec_ref(v_fvars_3634_);
return v_res_3646_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3649_ = l_Lean_stringToMessageData(v___x_3648_);
return v___x_3649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3650_, lean_object* v_a_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_){
_start:
{
lean_object* v___x_3659_; 
lean_inc_ref(v_a_3650_);
v___x_3659_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3650_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v_expr_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3711_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v_expr_3661_ = lean_ctor_get(v_a_3651_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_a_3651_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v_a_3651_, 1);
lean_dec(v_unused_3712_);
v___x_3663_ = v_a_3651_;
v_isShared_3664_ = v_isSharedCheck_3711_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_expr_3661_);
lean_dec(v_a_3651_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3711_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3665_; 
lean_inc(v_a_3660_);
lean_inc_ref(v_expr_3661_);
v___x_3665_ = l_Lean_Meta_isExprDefEq(v_expr_3661_, v_a_3660_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3702_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3668_ = v___x_3665_;
v_isShared_3669_ = v_isSharedCheck_3702_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_a_3666_);
lean_dec(v___x_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3702_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
uint8_t v___x_3670_; 
v___x_3670_ = lean_unbox(v_a_3666_);
lean_dec(v_a_3666_);
if (v___x_3670_ == 0)
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_del_object(v___x_3668_);
v___x_3671_ = lean_box(0);
v___x_3672_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3673_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3660_, v_expr_3661_, v___x_3671_, v___x_3672_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v_expr_3675_; lean_object* v___x_3677_; uint8_t v_isShared_3678_; uint8_t v_isSharedCheck_3688_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
lean_inc(v_a_3674_);
lean_dec_ref_known(v___x_3673_, 1);
v_expr_3675_ = lean_ctor_get(v_a_3650_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3688_ == 0)
{
lean_object* v_unused_3689_; 
v_unused_3689_ = lean_ctor_get(v_a_3650_, 1);
lean_dec(v_unused_3689_);
v___x_3677_ = v_a_3650_;
v_isShared_3678_ = v_isSharedCheck_3688_;
goto v_resetjp_3676_;
}
else
{
lean_inc(v_expr_3675_);
lean_dec(v_a_3650_);
v___x_3677_ = lean_box(0);
v_isShared_3678_ = v_isSharedCheck_3688_;
goto v_resetjp_3676_;
}
v_resetjp_3676_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3679_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3680_ = l_Lean_indentExpr(v_expr_3675_);
if (v_isShared_3678_ == 0)
{
lean_ctor_set_tag(v___x_3677_, 7);
lean_ctor_set(v___x_3677_, 1, v___x_3680_);
lean_ctor_set(v___x_3677_, 0, v___x_3679_);
v___x_3682_ = v___x_3677_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3679_);
lean_ctor_set(v_reuseFailAlloc_3687_, 1, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3684_; 
if (v_isShared_3664_ == 0)
{
lean_ctor_set_tag(v___x_3663_, 7);
lean_ctor_set(v___x_3663_, 1, v_a_3674_);
lean_ctor_set(v___x_3663_, 0, v___x_3682_);
v___x_3684_ = v___x_3663_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3686_, 1, v_a_3674_);
v___x_3684_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; 
v___x_3685_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3684_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_);
return v___x_3685_;
}
}
}
}
else
{
lean_object* v_a_3690_; lean_object* v___x_3692_; uint8_t v_isShared_3693_; uint8_t v_isSharedCheck_3697_; 
lean_del_object(v___x_3663_);
lean_dec_ref(v_a_3650_);
v_a_3690_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3692_ = v___x_3673_;
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
else
{
lean_inc(v_a_3690_);
lean_dec(v___x_3673_);
v___x_3692_ = lean_box(0);
v_isShared_3693_ = v_isSharedCheck_3697_;
goto v_resetjp_3691_;
}
v_resetjp_3691_:
{
lean_object* v___x_3695_; 
if (v_isShared_3693_ == 0)
{
v___x_3695_ = v___x_3692_;
goto v_reusejp_3694_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v_a_3690_);
v___x_3695_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3694_;
}
v_reusejp_3694_:
{
return v___x_3695_;
}
}
}
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3700_; 
lean_del_object(v___x_3663_);
lean_dec_ref(v_expr_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3650_);
v___x_3698_ = lean_box(0);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v___x_3698_);
v___x_3700_ = v___x_3668_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v___x_3698_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_del_object(v___x_3663_);
lean_dec_ref(v_expr_3661_);
lean_dec(v_a_3660_);
lean_dec_ref(v_a_3650_);
v_a_3703_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3665_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3665_);
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
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_dec_ref(v_a_3651_);
lean_dec_ref(v_a_3650_);
v_a_3713_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3659_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3659_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3721_, v_a_3722_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec(v___y_3724_);
lean_dec(v___y_3723_);
return v_res_3730_;
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_3731_; double v___x_3732_; 
v___x_3731_ = lean_unsigned_to_nat(1000000000u);
v___x_3732_ = lean_float_of_nat(v___x_3731_);
return v___x_3732_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3734_; lean_object* v___x_3735_; 
v___x_3734_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3735_ = l_Lean_stringToMessageData(v___x_3734_);
return v___x_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3736_, lean_object* v_a_3737_, lean_object* v_a_3738_, lean_object* v_a_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_, lean_object* v_a_3742_){
_start:
{
if (lean_obj_tag(v_e_3736_) == 5)
{
lean_object* v_fn_3744_; lean_object* v_arg_3745_; lean_object* v___x_3746_; 
v_fn_3744_ = lean_ctor_get(v_e_3736_, 0);
v_arg_3745_ = lean_ctor_get(v_e_3736_, 1);
lean_inc_ref(v_fn_3744_);
v___x_3746_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3744_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; lean_object* v___x_3748_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
lean_inc_ref(v_arg_3745_);
v___x_3748_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3745_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_3748_) == 0)
{
lean_object* v_a_3749_; lean_object* v___x_3751_; uint8_t v_isShared_3752_; uint8_t v_isSharedCheck_3769_; 
v_a_3749_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3769_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3769_ == 0)
{
v___x_3751_ = v___x_3748_;
v_isShared_3752_ = v_isSharedCheck_3769_;
goto v_resetjp_3750_;
}
else
{
lean_inc(v_a_3749_);
lean_dec(v___x_3748_);
v___x_3751_ = lean_box(0);
v_isShared_3752_ = v_isSharedCheck_3769_;
goto v_resetjp_3750_;
}
v_resetjp_3750_:
{
lean_object* v_expr_3753_; uint8_t v___y_3755_; size_t v___x_3763_; size_t v___x_3764_; uint8_t v___x_3765_; 
v_expr_3753_ = lean_ctor_get(v_a_3749_, 0);
lean_inc_ref(v_expr_3753_);
lean_dec(v_a_3749_);
v___x_3763_ = lean_ptr_addr(v_fn_3744_);
v___x_3764_ = lean_ptr_addr(v_a_3747_);
v___x_3765_ = lean_usize_dec_eq(v___x_3763_, v___x_3764_);
if (v___x_3765_ == 0)
{
v___y_3755_ = v___x_3765_;
goto v___jp_3754_;
}
else
{
size_t v___x_3766_; size_t v___x_3767_; uint8_t v___x_3768_; 
v___x_3766_ = lean_ptr_addr(v_arg_3745_);
v___x_3767_ = lean_ptr_addr(v_expr_3753_);
v___x_3768_ = lean_usize_dec_eq(v___x_3766_, v___x_3767_);
v___y_3755_ = v___x_3768_;
goto v___jp_3754_;
}
v___jp_3754_:
{
if (v___y_3755_ == 0)
{
lean_object* v___x_3756_; lean_object* v___x_3758_; 
lean_dec_ref_known(v_e_3736_, 2);
v___x_3756_ = l_Lean_Expr_app___override(v_a_3747_, v_expr_3753_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 0, v___x_3756_);
v___x_3758_ = v___x_3751_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v___x_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
else
{
lean_object* v___x_3761_; 
lean_dec_ref(v_expr_3753_);
lean_dec(v_a_3747_);
if (v_isShared_3752_ == 0)
{
lean_ctor_set(v___x_3751_, 0, v_e_3736_);
v___x_3761_ = v___x_3751_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_e_3736_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
}
else
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3777_; 
lean_dec(v_a_3747_);
lean_dec_ref_known(v_e_3736_, 2);
v_a_3770_ = lean_ctor_get(v___x_3748_, 0);
v_isSharedCheck_3777_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3777_ == 0)
{
v___x_3772_ = v___x_3748_;
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3748_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3777_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v___x_3775_; 
if (v_isShared_3773_ == 0)
{
v___x_3775_ = v___x_3772_;
goto v_reusejp_3774_;
}
else
{
lean_object* v_reuseFailAlloc_3776_; 
v_reuseFailAlloc_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3776_, 0, v_a_3770_);
v___x_3775_ = v_reuseFailAlloc_3776_;
goto v_reusejp_3774_;
}
v_reusejp_3774_:
{
return v___x_3775_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3736_, 2);
return v___x_3746_;
}
}
else
{
lean_object* v___x_3778_; 
v___x_3778_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3787_; 
v_a_3779_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3781_ = v___x_3778_;
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3778_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3787_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v_expr_3783_; lean_object* v___x_3785_; 
v_expr_3783_ = lean_ctor_get(v_a_3779_, 0);
lean_inc_ref(v_expr_3783_);
lean_dec(v_a_3779_);
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v_expr_3783_);
v___x_3785_ = v___x_3781_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_expr_3783_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v_a_3788_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3778_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3778_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_){
_start:
{
lean_object* v_res_3804_; 
v_res_3804_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_, v_a_3802_);
lean_dec(v_a_3802_);
lean_dec_ref(v_a_3801_);
lean_dec(v_a_3800_);
lean_dec_ref(v_a_3799_);
lean_dec(v_a_3798_);
lean_dec(v_a_3797_);
return v_res_3804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3805_, lean_object* v_a_3806_, lean_object* v_a_3807_, lean_object* v_a_3808_, lean_object* v_a_3809_, lean_object* v_a_3810_, lean_object* v_a_3811_){
_start:
{
if (lean_obj_tag(v_e_3805_) == 5)
{
lean_object* v_fn_3813_; lean_object* v_arg_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_fn_3813_ = lean_ctor_get(v_e_3805_, 0);
v_arg_3814_ = lean_ctor_get(v_e_3805_, 1);
lean_inc_ref_n(v_fn_3813_, 2);
v___x_3815_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3815_, 0, v_fn_3813_);
v___x_3816_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3813_, v___x_3815_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3818_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3816_, 1);
lean_inc_ref(v_arg_3814_);
v___x_3818_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3814_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v_a_3819_; lean_object* v___x_3820_; 
v_a_3819_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___x_3818_, 1);
v___x_3820_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3805_, v_a_3817_, v_a_3819_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3820_;
}
else
{
lean_dec(v_a_3817_);
lean_dec_ref_known(v_e_3805_, 2);
return v___x_3818_;
}
}
else
{
lean_dec_ref_known(v_e_3805_, 2);
return v___x_3816_;
}
}
else
{
lean_object* v___x_3821_; 
v___x_3821_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3805_, v_a_3806_, v_a_3807_, v_a_3808_, v_a_3809_, v_a_3810_, v_a_3811_);
return v___x_3821_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3822_, lean_object* v_a_3823_, lean_object* v_a_3824_, lean_object* v_a_3825_, lean_object* v_a_3826_, lean_object* v_a_3827_, lean_object* v_a_3828_){
_start:
{
uint8_t v___x_3830_; 
v___x_3830_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3823_);
if (v___x_3830_ == 0)
{
lean_object* v___x_3831_; 
v___x_3831_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3841_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3841_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3841_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3836_ = lean_box(0);
v___x_3837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3837_, 0, v_a_3832_);
lean_ctor_set(v___x_3837_, 1, v___x_3836_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 0, v___x_3837_);
v___x_3839_ = v___x_3834_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
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
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
v_a_3842_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3831_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3831_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
else
{
lean_object* v___x_3850_; 
v___x_3850_ = l_Lean_Expr_getAppFn(v_e_3822_);
if (lean_obj_tag(v___x_3850_) == 2)
{
lean_object* v_mvarId_3851_; lean_object* v_dummy_3852_; lean_object* v_nargs_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v_mvarId_3851_ = lean_ctor_get(v___x_3850_, 0);
lean_inc(v_mvarId_3851_);
lean_dec_ref_known(v___x_3850_, 1);
v_dummy_3852_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3853_ = l_Lean_Expr_getAppNumArgs(v_e_3822_);
lean_inc(v_nargs_3853_);
v___x_3854_ = lean_mk_array(v_nargs_3853_, v_dummy_3852_);
v___x_3855_ = lean_unsigned_to_nat(1u);
v___x_3856_ = lean_nat_sub(v_nargs_3853_, v___x_3855_);
lean_dec(v_nargs_3853_);
lean_inc_ref(v_e_3822_);
v___x_3857_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3822_, v___x_3854_, v___x_3856_);
v___x_3858_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3851_, v___x_3857_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
lean_dec(v_mvarId_3851_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v___x_3859_; 
lean_dec_ref_known(v___x_3858_, 1);
v___x_3859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
return v___x_3859_;
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3862_; uint8_t v_isShared_3863_; uint8_t v_isSharedCheck_3867_; 
lean_dec_ref(v_e_3822_);
v_a_3860_ = lean_ctor_get(v___x_3858_, 0);
v_isSharedCheck_3867_ = !lean_is_exclusive(v___x_3858_);
if (v_isSharedCheck_3867_ == 0)
{
v___x_3862_ = v___x_3858_;
v_isShared_3863_ = v_isSharedCheck_3867_;
goto v_resetjp_3861_;
}
else
{
lean_inc(v_a_3860_);
lean_dec(v___x_3858_);
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
lean_dec_ref(v___x_3850_);
v___x_3868_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_, v_a_3828_);
return v___x_3868_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_){
_start:
{
lean_object* v_res_3877_; 
v_res_3877_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
lean_dec(v_a_3875_);
lean_dec_ref(v_a_3874_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec(v_a_3870_);
return v_res_3877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3887_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_, v_a_3884_);
return v___x_3888_;
}
else
{
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3889_, lean_object* v_a_3890_, lean_object* v_a_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_){
_start:
{
lean_object* v_res_3897_; 
v_res_3897_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3889_, v_a_3890_, v_a_3891_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_);
lean_dec(v_a_3895_);
lean_dec_ref(v_a_3894_);
lean_dec(v_a_3893_);
lean_dec_ref(v_a_3892_);
lean_dec(v_a_3891_);
lean_dec(v_a_3890_);
return v_res_3897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3898_, lean_object* v_fvars_3899_, lean_object* v_doms_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
lean_object* v___x_3908_; 
v___x_3908_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3898_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3899_, v_doms_3900_, v_a_3909_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_);
return v___x_3910_;
}
else
{
return v___x_3908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3911_, lean_object* v_fvars_3912_, lean_object* v_doms_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_, lean_object* v___y_3919_, lean_object* v___y_3920_){
_start:
{
lean_object* v_res_3921_; 
v_res_3921_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3911_, v_fvars_3912_, v_doms_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_, v___y_3918_, v___y_3919_);
lean_dec(v___y_3919_);
lean_dec_ref(v___y_3918_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v_doms_3913_);
lean_dec_ref(v_fvars_3912_);
return v_res_3921_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3922_, lean_object* v_fvars_3923_, lean_object* v_doms_3924_, lean_object* v_e_3925_, lean_object* v_a_3926_, lean_object* v_a_3927_, lean_object* v_a_3928_, lean_object* v_a_3929_, lean_object* v_a_3930_, lean_object* v_a_3931_){
_start:
{
lean_object* v___x_3933_; 
v___x_3933_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3925_, v_a_3927_);
if (lean_obj_tag(v___x_3933_) == 0)
{
lean_object* v_a_3934_; 
v_a_3934_ = lean_ctor_get(v___x_3933_, 0);
lean_inc(v_a_3934_);
lean_dec_ref_known(v___x_3933_, 1);
if (lean_obj_tag(v_a_3934_) == 1)
{
lean_object* v_val_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; 
lean_dec_ref(v_e_3925_);
v_val_3935_ = lean_ctor_get(v_a_3934_, 0);
lean_inc(v_val_3935_);
lean_dec_ref_known(v_a_3934_, 1);
v___x_3936_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3937_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3937_, 0, v_fvars_3923_);
lean_closure_set(v___x_3937_, 1, v_doms_3924_);
lean_closure_set(v___x_3937_, 2, v_val_3935_);
v___x_3938_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3922_, v___x_3936_, v___x_3937_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
return v___x_3938_;
}
else
{
lean_dec(v_a_3934_);
if (lean_obj_tag(v_e_3925_) == 7)
{
lean_object* v_binderName_3939_; lean_object* v_binderType_3940_; lean_object* v_body_3941_; uint8_t v_binderInfo_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v_binderName_3939_ = lean_ctor_get(v_e_3925_, 0);
lean_inc(v_binderName_3939_);
v_binderType_3940_ = lean_ctor_get(v_e_3925_, 1);
lean_inc_ref(v_binderType_3940_);
v_body_3941_ = lean_ctor_get(v_e_3925_, 2);
lean_inc_ref(v_body_3941_);
v_binderInfo_3942_ = lean_ctor_get_uint8(v_e_3925_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3925_, 3);
v___x_3943_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3944_ = lean_expr_instantiate_rev(v_binderType_3940_, v_fvars_3923_);
lean_dec_ref(v_binderType_3940_);
v___x_3945_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3945_, 0, v___x_3944_);
lean_inc_ref(v_lctx_3922_);
v___x_3946_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3922_, v___x_3943_, v___x_3945_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
if (lean_obj_tag(v___x_3946_) == 0)
{
lean_object* v_a_3947_; lean_object* v___x_3948_; 
v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
lean_inc(v_a_3947_);
lean_dec_ref_known(v___x_3946_, 1);
v___x_3948_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; lean_object* v_expr_3950_; uint8_t v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc_n(v_a_3949_, 2);
lean_dec_ref_known(v___x_3948_, 1);
v_expr_3950_ = lean_ctor_get(v_a_3947_, 0);
v___x_3951_ = 0;
lean_inc_ref(v_expr_3950_);
v___x_3952_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3922_, v_a_3949_, v_binderName_3939_, v_expr_3950_, v_binderInfo_3942_, v___x_3951_);
v___x_3953_ = l_Lean_Expr_fvar___override(v_a_3949_);
v___x_3954_ = lean_array_push(v_fvars_3923_, v___x_3953_);
v___x_3955_ = lean_array_push(v_doms_3924_, v_a_3947_);
v_lctx_3922_ = v___x_3952_;
v_fvars_3923_ = v___x_3954_;
v_doms_3924_ = v___x_3955_;
v_e_3925_ = v_body_3941_;
goto _start;
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec(v_a_3947_);
lean_dec_ref(v_body_3941_);
lean_dec(v_binderName_3939_);
lean_dec_ref(v_doms_3924_);
lean_dec_ref(v_fvars_3923_);
lean_dec_ref(v_lctx_3922_);
v_a_3957_ = lean_ctor_get(v___x_3948_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3948_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3948_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3948_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3962_; 
if (v_isShared_3960_ == 0)
{
v___x_3962_ = v___x_3959_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3963_; 
v_reuseFailAlloc_3963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3963_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3963_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
return v___x_3962_;
}
}
}
}
else
{
lean_dec_ref(v_body_3941_);
lean_dec(v_binderName_3939_);
lean_dec_ref(v_doms_3924_);
lean_dec_ref(v_fvars_3923_);
lean_dec_ref(v_lctx_3922_);
return v___x_3946_;
}
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___f_3967_; lean_object* v___x_3968_; 
v___x_3965_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3966_ = lean_expr_instantiate_rev(v_e_3925_, v_fvars_3923_);
lean_dec_ref(v_e_3925_);
v___f_3967_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3967_, 0, v___x_3966_);
lean_closure_set(v___f_3967_, 1, v_fvars_3923_);
lean_closure_set(v___f_3967_, 2, v_doms_3924_);
v___x_3968_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3922_, v___x_3965_, v___f_3967_, v_a_3926_, v_a_3927_, v_a_3928_, v_a_3929_, v_a_3930_, v_a_3931_);
return v___x_3968_;
}
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec_ref(v_e_3925_);
lean_dec_ref(v_doms_3924_);
lean_dec_ref(v_fvars_3923_);
lean_dec_ref(v_lctx_3922_);
v_a_3969_ = lean_ctor_get(v___x_3933_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3933_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3933_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_, lean_object* v_a_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_){
_start:
{
uint32_t v___x_3985_; uint8_t v___x_3986_; 
v___x_3985_ = 5;
v___x_3986_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3977_, v___x_3985_);
if (v___x_3986_ == 0)
{
lean_object* v_lctx_3987_; lean_object* v___x_3988_; lean_object* v___x_3989_; 
v_lctx_3987_ = lean_ctor_get(v_a_3980_, 2);
v___x_3988_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3987_);
v___x_3989_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3987_, v___x_3988_, v___x_3988_, v_e_3977_, v_a_3978_, v_a_3979_, v_a_3980_, v_a_3981_, v_a_3982_, v_a_3983_);
return v___x_3989_;
}
else
{
lean_object* v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3990_ = lean_box(0);
v___x_3991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3991_, 0, v_e_3977_);
lean_ctor_set(v___x_3991_, 1, v___x_3990_);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_, lean_object* v_a_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_, v_a_3999_);
lean_dec(v_a_3999_);
lean_dec_ref(v_a_3998_);
lean_dec(v_a_3997_);
lean_dec_ref(v_a_3996_);
lean_dec(v_a_3995_);
lean_dec(v_a_3994_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_4002_, lean_object* v_e_4003_, lean_object* v_typeName_4004_, lean_object* v_idx_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4002_, v_e_4003_, v_typeName_4004_, v_idx_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec(v___y_4006_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec(v_a_4015_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v___x_4032_; 
v___x_4032_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4034_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
lean_inc(v_a_4033_);
lean_dec_ref_known(v___x_4032_, 1);
v___x_4034_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4023_, v_a_4033_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
return v___x_4034_;
}
else
{
lean_dec_ref(v_fvars_4023_);
return v___x_4032_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4035_, v___y_4036_, v___y_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec(v___y_4037_);
return v_res_4044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4045_, lean_object* v_fvars_4046_, lean_object* v_e_4047_, lean_object* v_letFVars_4048_, lean_object* v_a_4049_, lean_object* v_a_4050_, lean_object* v_a_4051_, lean_object* v_a_4052_, lean_object* v_a_4053_, lean_object* v_a_4054_){
_start:
{
switch(lean_obj_tag(v_e_4047_))
{
case 6:
{
lean_object* v_binderName_4056_; lean_object* v_binderType_4057_; lean_object* v_body_4058_; uint8_t v_binderInfo_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v_binderName_4056_ = lean_ctor_get(v_e_4047_, 0);
lean_inc(v_binderName_4056_);
v_binderType_4057_ = lean_ctor_get(v_e_4047_, 1);
lean_inc_ref(v_binderType_4057_);
v_body_4058_ = lean_ctor_get(v_e_4047_, 2);
lean_inc_ref(v_body_4058_);
v_binderInfo_4059_ = lean_ctor_get_uint8(v_e_4047_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4047_, 3);
v___x_4060_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4045_);
lean_inc(v_letFVars_4048_);
v___x_4061_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4046_, v_letFVars_4048_, v_lctx_4045_, v___x_4060_, v_binderType_4057_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec_ref(v_binderType_4057_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___x_4061_, 1);
v___x_4063_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
if (lean_obj_tag(v___x_4063_) == 0)
{
lean_object* v_a_4064_; lean_object* v_expr_4065_; uint8_t v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4069_; 
v_a_4064_ = lean_ctor_get(v___x_4063_, 0);
lean_inc_n(v_a_4064_, 2);
lean_dec_ref_known(v___x_4063_, 1);
v_expr_4065_ = lean_ctor_get(v_a_4062_, 0);
lean_inc_ref(v_expr_4065_);
lean_dec(v_a_4062_);
v___x_4066_ = 0;
v___x_4067_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4045_, v_a_4064_, v_binderName_4056_, v_expr_4065_, v_binderInfo_4059_, v___x_4066_);
v___x_4068_ = l_Lean_Expr_fvar___override(v_a_4064_);
v___x_4069_ = lean_array_push(v_fvars_4046_, v___x_4068_);
v_lctx_4045_ = v___x_4067_;
v_fvars_4046_ = v___x_4069_;
v_e_4047_ = v_body_4058_;
goto _start;
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_a_4062_);
lean_dec_ref(v_body_4058_);
lean_dec(v_binderName_4056_);
lean_dec(v_letFVars_4048_);
lean_dec_ref(v_fvars_4046_);
lean_dec_ref(v_lctx_4045_);
v_a_4071_ = lean_ctor_get(v___x_4063_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4063_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4063_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
else
{
lean_dec_ref(v_body_4058_);
lean_dec(v_binderName_4056_);
lean_dec(v_letFVars_4048_);
lean_dec_ref(v_fvars_4046_);
lean_dec_ref(v_lctx_4045_);
return v___x_4061_;
}
}
case 8:
{
lean_object* v_declName_4079_; lean_object* v_type_4080_; lean_object* v_value_4081_; lean_object* v_body_4082_; uint8_t v_nondep_4083_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_declName_4079_ = lean_ctor_get(v_e_4047_, 0);
lean_inc(v_declName_4079_);
v_type_4080_ = lean_ctor_get(v_e_4047_, 1);
lean_inc_ref(v_type_4080_);
v_value_4081_ = lean_ctor_get(v_e_4047_, 2);
lean_inc_ref(v_value_4081_);
v_body_4082_ = lean_ctor_get(v_e_4047_, 3);
lean_inc_ref(v_body_4082_);
v_nondep_4083_ = lean_ctor_get_uint8(v_e_4047_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4047_, 4);
v___x_4097_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4045_);
lean_inc(v_letFVars_4048_);
v___x_4098_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4046_, v_letFVars_4048_, v_lctx_4045_, v___x_4097_, v_type_4080_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec_ref(v_type_4080_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v___x_4100_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4045_);
lean_inc(v_letFVars_4048_);
v___x_4101_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4046_, v_letFVars_4048_, v_lctx_4045_, v___x_4100_, v_value_4081_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec_ref(v_value_4081_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; uint8_t v___x_4132_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
v___x_4132_ = l_List_isEmpty___redArg(v_letFVars_4048_);
if (v___x_4132_ == 0)
{
lean_object* v___f_4133_; lean_object* v___x_4134_; 
lean_inc(v_a_4099_);
lean_inc(v_a_4102_);
v___f_4133_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4133_, 0, v_a_4102_);
lean_closure_set(v___f_4133_, 1, v_a_4099_);
lean_inc_ref(v_lctx_4045_);
v___x_4134_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4045_, v___f_4133_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_dec_ref_known(v___x_4134_, 1);
v___y_4104_ = v_a_4049_;
v___y_4105_ = v_a_4050_;
v___y_4106_ = v_a_4051_;
v___y_4107_ = v_a_4052_;
v___y_4108_ = v_a_4053_;
v___y_4109_ = v_a_4054_;
goto v___jp_4103_;
}
else
{
lean_object* v_a_4135_; lean_object* v___x_4137_; uint8_t v_isShared_4138_; uint8_t v_isSharedCheck_4142_; 
lean_dec(v_a_4102_);
lean_dec(v_a_4099_);
lean_dec_ref(v_body_4082_);
lean_dec(v_declName_4079_);
lean_dec(v_letFVars_4048_);
lean_dec_ref(v_fvars_4046_);
lean_dec_ref(v_lctx_4045_);
v_a_4135_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4142_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4142_ == 0)
{
v___x_4137_ = v___x_4134_;
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
else
{
lean_inc(v_a_4135_);
lean_dec(v___x_4134_);
v___x_4137_ = lean_box(0);
v_isShared_4138_ = v_isSharedCheck_4142_;
goto v_resetjp_4136_;
}
v_resetjp_4136_:
{
lean_object* v___x_4140_; 
if (v_isShared_4138_ == 0)
{
v___x_4140_ = v___x_4137_;
goto v_reusejp_4139_;
}
else
{
lean_object* v_reuseFailAlloc_4141_; 
v_reuseFailAlloc_4141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4141_, 0, v_a_4135_);
v___x_4140_ = v_reuseFailAlloc_4141_;
goto v_reusejp_4139_;
}
v_reusejp_4139_:
{
return v___x_4140_;
}
}
}
}
else
{
v___y_4104_ = v_a_4049_;
v___y_4105_ = v_a_4050_;
v___y_4106_ = v_a_4051_;
v___y_4107_ = v_a_4052_;
v___y_4108_ = v_a_4053_;
v___y_4109_ = v_a_4054_;
goto v___jp_4103_;
}
v___jp_4103_:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
if (lean_obj_tag(v___x_4110_) == 0)
{
lean_object* v_a_4111_; lean_object* v_expr_4112_; lean_object* v_expr_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4122_; 
v_a_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc(v_a_4111_);
lean_dec_ref_known(v___x_4110_, 1);
v_expr_4112_ = lean_ctor_get(v_a_4099_, 0);
lean_inc_ref(v_expr_4112_);
lean_dec(v_a_4099_);
v_expr_4113_ = lean_ctor_get(v_a_4102_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v_a_4102_);
if (v_isSharedCheck_4122_ == 0)
{
lean_object* v_unused_4123_; 
v_unused_4123_ = lean_ctor_get(v_a_4102_, 1);
lean_dec(v_unused_4123_);
v___x_4115_ = v_a_4102_;
v_isShared_4116_ = v_isSharedCheck_4122_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_expr_4113_);
lean_dec(v_a_4102_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4122_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
uint8_t v___x_4117_; lean_object* v___x_4118_; 
v___x_4117_ = 0;
lean_inc(v_a_4111_);
v___x_4118_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4045_, v_a_4111_, v_declName_4079_, v_expr_4112_, v_expr_4113_, v_nondep_4083_, v___x_4117_);
if (v_nondep_4083_ == 0)
{
lean_object* v___x_4120_; 
lean_inc(v_a_4111_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set_tag(v___x_4115_, 1);
lean_ctor_set(v___x_4115_, 1, v_letFVars_4048_);
lean_ctor_set(v___x_4115_, 0, v_a_4111_);
v___x_4120_ = v___x_4115_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4111_);
lean_ctor_set(v_reuseFailAlloc_4121_, 1, v_letFVars_4048_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
v___y_4085_ = v_a_4111_;
v___y_4086_ = v___y_4109_;
v___y_4087_ = v___x_4118_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4104_;
v___y_4090_ = v___y_4105_;
v___y_4091_ = v___y_4108_;
v___y_4092_ = v___y_4106_;
v___y_4093_ = v___x_4120_;
goto v___jp_4084_;
}
}
else
{
lean_del_object(v___x_4115_);
v___y_4085_ = v_a_4111_;
v___y_4086_ = v___y_4109_;
v___y_4087_ = v___x_4118_;
v___y_4088_ = v___y_4107_;
v___y_4089_ = v___y_4104_;
v___y_4090_ = v___y_4105_;
v___y_4091_ = v___y_4108_;
v___y_4092_ = v___y_4106_;
v___y_4093_ = v_letFVars_4048_;
goto v___jp_4084_;
}
}
}
else
{
lean_object* v_a_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4131_; 
lean_dec(v_a_4102_);
lean_dec(v_a_4099_);
lean_dec_ref(v_body_4082_);
lean_dec(v_declName_4079_);
lean_dec(v_letFVars_4048_);
lean_dec_ref(v_fvars_4046_);
lean_dec_ref(v_lctx_4045_);
v_a_4124_ = lean_ctor_get(v___x_4110_, 0);
v_isSharedCheck_4131_ = !lean_is_exclusive(v___x_4110_);
if (v_isSharedCheck_4131_ == 0)
{
v___x_4126_ = v___x_4110_;
v_isShared_4127_ = v_isSharedCheck_4131_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_a_4124_);
lean_dec(v___x_4110_);
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
lean_dec(v_a_4099_);
lean_dec_ref(v_body_4082_);
lean_dec(v_declName_4079_);
lean_dec(v_letFVars_4048_);
lean_dec_ref(v_fvars_4046_);
lean_dec_ref(v_lctx_4045_);
return v___x_4101_;
}
}
else
{
lean_dec_ref(v_body_4082_);
lean_dec_ref(v_value_4081_);
lean_dec(v_declName_4079_);
lean_dec(v_letFVars_4048_);
lean_dec_ref(v_fvars_4046_);
lean_dec_ref(v_lctx_4045_);
return v___x_4098_;
}
v___jp_4084_:
{
lean_object* v___x_4094_; lean_object* v___x_4095_; 
v___x_4094_ = l_Lean_Expr_fvar___override(v___y_4085_);
v___x_4095_ = lean_array_push(v_fvars_4046_, v___x_4094_);
v_lctx_4045_ = v___y_4087_;
v_fvars_4046_ = v___x_4095_;
v_e_4047_ = v_body_4082_;
v_letFVars_4048_ = v___y_4093_;
v_a_4049_ = v___y_4089_;
v_a_4050_ = v___y_4090_;
v_a_4051_ = v___y_4092_;
v_a_4052_ = v___y_4088_;
v_a_4053_ = v___y_4091_;
v_a_4054_ = v___y_4086_;
goto _start;
}
}
default: 
{
lean_object* v___f_4143_; lean_object* v___x_4144_; 
lean_inc_ref(v_fvars_4046_);
v___f_4143_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4143_, 0, v_fvars_4046_);
v___x_4144_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4046_, v_letFVars_4048_, v_lctx_4045_, v___f_4143_, v_e_4047_, v_a_4049_, v_a_4050_, v_a_4051_, v_a_4052_, v_a_4053_, v_a_4054_);
lean_dec_ref(v_e_4047_);
lean_dec_ref(v_fvars_4046_);
return v___x_4144_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
uint32_t v___x_4153_; uint8_t v___x_4154_; 
v___x_4153_ = 5;
v___x_4154_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4145_, v___x_4153_);
if (v___x_4154_ == 0)
{
lean_object* v_lctx_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; 
v_lctx_4155_ = lean_ctor_get(v_a_4148_, 2);
v___x_4156_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4146_);
lean_inc_ref(v_lctx_4155_);
v___x_4157_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4155_, v___x_4156_, v_e_4145_, v_a_4146_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_);
return v___x_4157_;
}
else
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4158_ = lean_box(0);
v___x_4159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4159_, 0, v_e_4145_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
return v___x_4160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_, lean_object* v_a_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_){
_start:
{
lean_object* v_res_4169_; 
v_res_4169_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4161_, v_a_4162_, v_a_4163_, v_a_4164_, v_a_4165_, v_a_4166_, v_a_4167_);
lean_dec(v_a_4167_);
lean_dec_ref(v_a_4166_);
lean_dec(v_a_4165_);
lean_dec_ref(v_a_4164_);
lean_dec(v_a_4163_);
lean_dec(v_a_4162_);
return v_res_4169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_){
_start:
{
switch(lean_obj_tag(v_e_4170_))
{
case 0:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4178_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4179_ = l_Lean_MessageData_ofExpr(v_e_4170_);
v___x_4180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4178_);
lean_ctor_set(v___x_4180_, 1, v___x_4179_);
v___x_4181_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4180_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4181_;
}
case 1:
{
lean_object* v___x_4182_; 
v___x_4182_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4170_, v___y_4173_, v___y_4175_, v___y_4176_);
return v___x_4182_;
}
case 2:
{
lean_object* v___x_4183_; 
v___x_4183_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4183_;
}
case 3:
{
lean_object* v_u_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_u_4184_ = lean_ctor_get(v_e_4170_, 0);
lean_inc(v_u_4184_);
v___x_4185_ = l_Lean_Level_succ___override(v_u_4184_);
v___x_4186_ = l_Lean_Expr_sort___override(v___x_4185_);
v___x_4187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
v___x_4188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4188_, 0, v_e_4170_);
lean_ctor_set(v___x_4188_, 1, v___x_4187_);
v___x_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
return v___x_4189_;
}
case 4:
{
lean_object* v___x_4190_; 
v___x_4190_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4170_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4190_;
}
case 5:
{
lean_object* v___x_4191_; lean_object* v___x_4192_; 
lean_inc_ref(v_e_4170_);
v___x_4191_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4191_, 0, v_e_4170_);
v___x_4192_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4170_, v___x_4191_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4192_;
}
case 7:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
lean_inc_ref(v_e_4170_);
v___x_4193_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4193_, 0, v_e_4170_);
v___x_4194_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4170_, v___x_4193_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4194_;
}
case 9:
{
lean_object* v_a_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_a_4195_ = lean_ctor_get(v_e_4170_, 0);
v___x_4196_ = l_Lean_Literal_type(v_a_4195_);
v___x_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
v___x_4198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4198_, 0, v_e_4170_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4198_);
return v___x_4199_;
}
case 10:
{
lean_object* v_data_4200_; lean_object* v_expr_4201_; lean_object* v___x_4202_; 
v_data_4200_ = lean_ctor_get(v_e_4170_, 0);
v_expr_4201_ = lean_ctor_get(v_e_4170_, 1);
lean_inc_ref(v_expr_4201_);
v___x_4202_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4201_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4205_; uint8_t v_isShared_4206_; uint8_t v_isSharedCheck_4225_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4205_ = v___x_4202_;
v_isShared_4206_ = v_isSharedCheck_4225_;
goto v_resetjp_4204_;
}
else
{
lean_inc(v_a_4203_);
lean_dec(v___x_4202_);
v___x_4205_ = lean_box(0);
v_isShared_4206_ = v_isSharedCheck_4225_;
goto v_resetjp_4204_;
}
v_resetjp_4204_:
{
lean_object* v_expr_4207_; lean_object* v_type_x3f_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4224_; 
v_expr_4207_ = lean_ctor_get(v_a_4203_, 0);
v_type_x3f_4208_ = lean_ctor_get(v_a_4203_, 1);
v_isSharedCheck_4224_ = !lean_is_exclusive(v_a_4203_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4210_ = v_a_4203_;
v_isShared_4211_ = v_isSharedCheck_4224_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_type_x3f_4208_);
lean_inc(v_expr_4207_);
lean_dec(v_a_4203_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4224_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___y_4213_; size_t v___x_4220_; size_t v___x_4221_; uint8_t v___x_4222_; 
v___x_4220_ = lean_ptr_addr(v_expr_4201_);
v___x_4221_ = lean_ptr_addr(v_expr_4207_);
v___x_4222_ = lean_usize_dec_eq(v___x_4220_, v___x_4221_);
if (v___x_4222_ == 0)
{
lean_object* v___x_4223_; 
lean_inc(v_data_4200_);
lean_dec_ref_known(v_e_4170_, 2);
v___x_4223_ = l_Lean_Expr_mdata___override(v_data_4200_, v_expr_4207_);
v___y_4213_ = v___x_4223_;
goto v___jp_4212_;
}
else
{
lean_dec_ref(v_expr_4207_);
v___y_4213_ = v_e_4170_;
goto v___jp_4212_;
}
v___jp_4212_:
{
lean_object* v___x_4215_; 
if (v_isShared_4211_ == 0)
{
lean_ctor_set(v___x_4210_, 0, v___y_4213_);
v___x_4215_ = v___x_4210_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4219_; 
v_reuseFailAlloc_4219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4219_, 0, v___y_4213_);
lean_ctor_set(v_reuseFailAlloc_4219_, 1, v_type_x3f_4208_);
v___x_4215_ = v_reuseFailAlloc_4219_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
lean_object* v___x_4217_; 
if (v_isShared_4206_ == 0)
{
lean_ctor_set(v___x_4205_, 0, v___x_4215_);
v___x_4217_ = v___x_4205_;
goto v_reusejp_4216_;
}
else
{
lean_object* v_reuseFailAlloc_4218_; 
v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
v___x_4217_ = v_reuseFailAlloc_4218_;
goto v_reusejp_4216_;
}
v_reusejp_4216_:
{
return v___x_4217_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4170_, 2);
return v___x_4202_;
}
}
case 11:
{
lean_object* v_typeName_4226_; lean_object* v_idx_4227_; lean_object* v_struct_4228_; lean_object* v___f_4229_; lean_object* v___x_4230_; 
v_typeName_4226_ = lean_ctor_get(v_e_4170_, 0);
v_idx_4227_ = lean_ctor_get(v_e_4170_, 1);
v_struct_4228_ = lean_ctor_get(v_e_4170_, 2);
lean_inc(v_idx_4227_);
lean_inc(v_typeName_4226_);
lean_inc_ref(v_e_4170_);
lean_inc_ref(v_struct_4228_);
v___f_4229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4229_, 0, v_struct_4228_);
lean_closure_set(v___f_4229_, 1, v_e_4170_);
lean_closure_set(v___f_4229_, 2, v_typeName_4226_);
lean_closure_set(v___f_4229_, 3, v_idx_4227_);
v___x_4230_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4170_, v___f_4229_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4230_;
}
default: 
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
lean_inc_ref(v_e_4170_);
v___x_4231_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4231_, 0, v_e_4170_);
v___x_4232_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4170_, v___x_4231_, v___y_4171_, v___y_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
return v___x_4232_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v_options_4241_; lean_object* v_inheritedTraceOptions_4242_; uint8_t v_hasTrace_4243_; uint8_t v___x_4244_; 
v_options_4241_ = lean_ctor_get(v_a_4238_, 2);
v_inheritedTraceOptions_4242_ = lean_ctor_get(v_a_4238_, 13);
v_hasTrace_4243_ = lean_ctor_get_uint8(v_options_4241_, sizeof(void*)*1);
v___x_4244_ = lean_bool_not(v_hasTrace_4243_);
if (v___x_4244_ == 0)
{
lean_object* v___f_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; lean_object* v___y_4250_; lean_object* v___y_4251_; uint8_t v___y_4252_; lean_object* v_a_4253_; lean_object* v___y_4266_; uint8_t v___y_4267_; lean_object* v___y_4268_; lean_object* v_a_4269_; uint8_t v___y_4279_; uint8_t v_a_4329_; 
lean_inc_ref(v_e_4233_);
v___f_4245_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4245_, 0, v_e_4233_);
v___x_4246_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4247_ = 1;
v___x_4248_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
if (v_hasTrace_4243_ == 0)
{
v_a_4329_ = v_hasTrace_4243_;
goto v___jp_4328_;
}
else
{
lean_object* v___x_4333_; uint8_t v___x_4334_; 
v___x_4333_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4334_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4242_, v_options_4241_, v___x_4333_);
if (v___x_4334_ == 0)
{
v_a_4329_ = v___x_4334_;
goto v___jp_4328_;
}
else
{
v___y_4279_ = v___x_4334_;
goto v___jp_4278_;
}
}
v___jp_4249_:
{
lean_object* v___x_4254_; double v___x_4255_; double v___x_4256_; double v___x_4257_; double v___x_4258_; double v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4254_ = lean_io_mono_nanos_now();
v___x_4255_ = lean_float_of_nat(v___y_4250_);
v___x_4256_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4257_ = lean_float_div(v___x_4255_, v___x_4256_);
v___x_4258_ = lean_float_of_nat(v___x_4254_);
v___x_4259_ = lean_float_div(v___x_4258_, v___x_4256_);
v___x_4260_ = lean_box_float(v___x_4257_);
v___x_4261_ = lean_box_float(v___x_4259_);
v___x_4262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4263_, 0, v_a_4253_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4246_, v___x_4247_, v___x_4248_, v_options_4241_, v___y_4252_, v___y_4251_, v___f_4245_, v___x_4263_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4264_;
}
v___jp_4265_:
{
lean_object* v___x_4270_; double v___x_4271_; double v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4270_ = lean_io_get_num_heartbeats();
v___x_4271_ = lean_float_of_nat(v___y_4268_);
v___x_4272_ = lean_float_of_nat(v___x_4270_);
v___x_4273_ = lean_box_float(v___x_4271_);
v___x_4274_ = lean_box_float(v___x_4272_);
v___x_4275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4275_, 0, v___x_4273_);
lean_ctor_set(v___x_4275_, 1, v___x_4274_);
v___x_4276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4276_, 0, v_a_4269_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4246_, v___x_4247_, v___x_4248_, v_options_4241_, v___y_4267_, v___y_4266_, v___f_4245_, v___x_4276_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4277_;
}
v___jp_4278_:
{
lean_object* v___x_4280_; 
v___x_4280_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4239_);
if (lean_obj_tag(v___x_4280_) == 0)
{
lean_object* v_a_4281_; lean_object* v___x_4282_; uint8_t v___x_4283_; 
v_a_4281_ = lean_ctor_get(v___x_4280_, 0);
lean_inc(v_a_4281_);
lean_dec_ref_known(v___x_4280_, 1);
v___x_4282_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4283_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4241_, v___x_4282_);
if (v___x_4283_ == 0)
{
lean_object* v___x_4284_; lean_object* v___x_4285_; 
v___x_4284_ = lean_io_mono_nanos_now();
v___x_4285_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
if (lean_obj_tag(v___x_4285_) == 0)
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_a_4286_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4285_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4285_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
lean_ctor_set_tag(v___x_4288_, 1);
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
v___y_4250_ = v___x_4284_;
v___y_4251_ = v_a_4281_;
v___y_4252_ = v___y_4279_;
v_a_4253_ = v___x_4291_;
goto v___jp_4249_;
}
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
v_a_4294_ = lean_ctor_get(v___x_4285_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4285_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4285_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4285_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
lean_ctor_set_tag(v___x_4296_, 0);
v___x_4299_ = v___x_4296_;
goto v_reusejp_4298_;
}
else
{
lean_object* v_reuseFailAlloc_4300_; 
v_reuseFailAlloc_4300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4300_, 0, v_a_4294_);
v___x_4299_ = v_reuseFailAlloc_4300_;
goto v_reusejp_4298_;
}
v_reusejp_4298_:
{
v___y_4250_ = v___x_4284_;
v___y_4251_ = v_a_4281_;
v___y_4252_ = v___y_4279_;
v_a_4253_ = v___x_4299_;
goto v___jp_4249_;
}
}
}
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = lean_io_get_num_heartbeats();
v___x_4303_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4306_; uint8_t v_isShared_4307_; uint8_t v_isSharedCheck_4311_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4311_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4311_ == 0)
{
v___x_4306_ = v___x_4303_;
v_isShared_4307_ = v_isSharedCheck_4311_;
goto v_resetjp_4305_;
}
else
{
lean_inc(v_a_4304_);
lean_dec(v___x_4303_);
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
v___x_4309_ = v___x_4306_;
goto v_reusejp_4308_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v_a_4304_);
v___x_4309_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4308_;
}
v_reusejp_4308_:
{
v___y_4266_ = v_a_4281_;
v___y_4267_ = v___y_4279_;
v___y_4268_ = v___x_4302_;
v_a_4269_ = v___x_4309_;
goto v___jp_4265_;
}
}
}
else
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4319_; 
v_a_4312_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4319_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4319_ == 0)
{
v___x_4314_ = v___x_4303_;
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4303_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4319_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v___x_4317_; 
if (v_isShared_4315_ == 0)
{
lean_ctor_set_tag(v___x_4314_, 0);
v___x_4317_ = v___x_4314_;
goto v_reusejp_4316_;
}
else
{
lean_object* v_reuseFailAlloc_4318_; 
v_reuseFailAlloc_4318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
v___x_4317_ = v_reuseFailAlloc_4318_;
goto v_reusejp_4316_;
}
v_reusejp_4316_:
{
v___y_4266_ = v_a_4281_;
v___y_4267_ = v___y_4279_;
v___y_4268_ = v___x_4302_;
v_a_4269_ = v___x_4317_;
goto v___jp_4265_;
}
}
}
}
}
else
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
lean_dec_ref(v___f_4245_);
lean_dec_ref(v_e_4233_);
v_a_4320_ = lean_ctor_get(v___x_4280_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___x_4280_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___x_4280_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___x_4280_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
v___jp_4328_:
{
lean_object* v___x_4330_; uint8_t v___x_4331_; 
v___x_4330_ = l_Lean_trace_profiler;
v___x_4331_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4241_, v___x_4330_);
if (v___x_4331_ == 0)
{
lean_object* v___x_4332_; 
lean_dec_ref(v___f_4245_);
v___x_4332_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4332_;
}
else
{
v___y_4279_ = v_a_4329_;
goto v___jp_4278_;
}
}
}
else
{
lean_object* v___x_4335_; 
v___x_4335_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_, v_a_4239_);
return v___x_4335_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4336_, lean_object* v_e_4337_, lean_object* v_typeName_4338_, lean_object* v_idx_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v___x_4347_; 
v___x_4347_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4336_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; lean_object* v___x_4349_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
v___x_4349_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4337_, v_typeName_4338_, v_idx_4339_, v_a_4348_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_);
return v___x_4349_;
}
else
{
lean_dec(v_idx_4339_);
lean_dec(v_typeName_4338_);
lean_dec_ref(v_e_4337_);
return v___x_4347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v_res_4358_; 
v_res_4358_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4350_, v_a_4351_, v_a_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_);
lean_dec(v_a_4356_);
lean_dec_ref(v_a_4355_);
lean_dec(v_a_4354_);
lean_dec_ref(v_a_4353_);
lean_dec(v_a_4352_);
lean_dec(v_a_4351_);
return v_res_4358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4359_, lean_object* v_fvars_4360_, lean_object* v_doms_4361_, lean_object* v_e_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_){
_start:
{
lean_object* v_res_4370_; 
v_res_4370_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4359_, v_fvars_4360_, v_doms_4361_, v_e_4362_, v_a_4363_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_);
lean_dec(v_a_4368_);
lean_dec_ref(v_a_4367_);
lean_dec(v_a_4366_);
lean_dec_ref(v_a_4365_);
lean_dec(v_a_4364_);
lean_dec(v_a_4363_);
return v_res_4370_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_){
_start:
{
lean_object* v_res_4379_; 
v_res_4379_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_, v___y_4377_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec(v___y_4372_);
return v_res_4379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4380_, lean_object* v_fvars_4381_, lean_object* v_e_4382_, lean_object* v_letFVars_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_, lean_object* v_a_4389_, lean_object* v_a_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4380_, v_fvars_4381_, v_e_4382_, v_letFVars_4383_, v_a_4384_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_);
lean_dec(v_a_4389_);
lean_dec_ref(v_a_4388_);
lean_dec(v_a_4387_);
lean_dec_ref(v_a_4386_);
lean_dec(v_a_4385_);
lean_dec(v_a_4384_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4392_, lean_object* v_lctx_4393_, lean_object* v_localInsts_4394_, lean_object* v_x_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_){
_start:
{
lean_object* v___x_4403_; 
v___x_4403_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4393_, v_localInsts_4394_, v_x_4395_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4404_, lean_object* v_lctx_4405_, lean_object* v_localInsts_4406_, lean_object* v_x_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4404_, v_lctx_4405_, v_localInsts_4406_, v_x_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec(v___y_4408_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4416_, lean_object* v_lctx_4417_, lean_object* v_x_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_){
_start:
{
lean_object* v___x_4426_; 
v___x_4426_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4417_, v_x_4418_, v___y_4419_, v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4427_, lean_object* v_lctx_4428_, lean_object* v_x_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4427_, v_lctx_4428_, v_x_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
lean_dec(v___y_4431_);
lean_dec(v___y_4430_);
return v_res_4437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v___x_4445_; 
v___x_4445_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4443_);
return v___x_4445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_){
_start:
{
lean_object* v_res_4453_; 
v_res_4453_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_, v___y_4451_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec(v___y_4446_);
return v_res_4453_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v___x_4461_; 
v___x_4461_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4459_);
return v___x_4461_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v_res_4469_; 
v_res_4469_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_);
lean_dec(v___y_4467_);
lean_dec_ref(v___y_4466_);
lean_dec(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec(v___y_4463_);
lean_dec(v___y_4462_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4470_, lean_object* v_x_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4471_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4480_, lean_object* v_x_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_, lean_object* v___y_4488_){
_start:
{
lean_object* v_res_4489_; 
v_res_4489_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4480_, v_x_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_, v___y_4487_);
lean_dec(v___y_4487_);
lean_dec_ref(v___y_4486_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec(v___y_4482_);
return v_res_4489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4490_, lean_object* v_data_4491_, lean_object* v_ref_4492_, lean_object* v_msg_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___x_4501_; 
v___x_4501_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4490_, v_data_4491_, v_ref_4492_, v_msg_4493_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4501_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4502_, lean_object* v_data_4503_, lean_object* v_ref_4504_, lean_object* v_msg_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v_res_4513_; 
v_res_4513_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4502_, v_data_4503_, v_ref_4504_, v_msg_4505_, v___y_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
lean_dec(v___y_4511_);
lean_dec_ref(v___y_4510_);
lean_dec(v___y_4509_);
lean_dec_ref(v___y_4508_);
lean_dec(v___y_4507_);
lean_dec(v___y_4506_);
return v_res_4513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4514_){
_start:
{
lean_object* v___x_4516_; lean_object* v_traceState_4517_; lean_object* v_traces_4518_; lean_object* v___x_4519_; lean_object* v_traceState_4520_; lean_object* v_env_4521_; lean_object* v_nextMacroScope_4522_; lean_object* v_ngen_4523_; lean_object* v_auxDeclNGen_4524_; lean_object* v_cache_4525_; lean_object* v_messages_4526_; lean_object* v_infoState_4527_; lean_object* v_snapshotTasks_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4549_; 
v___x_4516_ = lean_st_ref_get(v___y_4514_);
v_traceState_4517_ = lean_ctor_get(v___x_4516_, 4);
lean_inc_ref(v_traceState_4517_);
lean_dec(v___x_4516_);
v_traces_4518_ = lean_ctor_get(v_traceState_4517_, 0);
lean_inc_ref(v_traces_4518_);
lean_dec_ref(v_traceState_4517_);
v___x_4519_ = lean_st_ref_take(v___y_4514_);
v_traceState_4520_ = lean_ctor_get(v___x_4519_, 4);
v_env_4521_ = lean_ctor_get(v___x_4519_, 0);
v_nextMacroScope_4522_ = lean_ctor_get(v___x_4519_, 1);
v_ngen_4523_ = lean_ctor_get(v___x_4519_, 2);
v_auxDeclNGen_4524_ = lean_ctor_get(v___x_4519_, 3);
v_cache_4525_ = lean_ctor_get(v___x_4519_, 5);
v_messages_4526_ = lean_ctor_get(v___x_4519_, 6);
v_infoState_4527_ = lean_ctor_get(v___x_4519_, 7);
v_snapshotTasks_4528_ = lean_ctor_get(v___x_4519_, 8);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4530_ = v___x_4519_;
v_isShared_4531_ = v_isSharedCheck_4549_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_snapshotTasks_4528_);
lean_inc(v_infoState_4527_);
lean_inc(v_messages_4526_);
lean_inc(v_cache_4525_);
lean_inc(v_traceState_4520_);
lean_inc(v_auxDeclNGen_4524_);
lean_inc(v_ngen_4523_);
lean_inc(v_nextMacroScope_4522_);
lean_inc(v_env_4521_);
lean_dec(v___x_4519_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4549_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
uint64_t v_tid_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4547_; 
v_tid_4532_ = lean_ctor_get_uint64(v_traceState_4520_, sizeof(void*)*1);
v_isSharedCheck_4547_ = !lean_is_exclusive(v_traceState_4520_);
if (v_isSharedCheck_4547_ == 0)
{
lean_object* v_unused_4548_; 
v_unused_4548_ = lean_ctor_get(v_traceState_4520_, 0);
lean_dec(v_unused_4548_);
v___x_4534_ = v_traceState_4520_;
v_isShared_4535_ = v_isSharedCheck_4547_;
goto v_resetjp_4533_;
}
else
{
lean_dec(v_traceState_4520_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4547_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4540_; 
v___x_4536_ = lean_unsigned_to_nat(32u);
v___x_4537_ = lean_mk_empty_array_with_capacity(v___x_4536_);
lean_dec_ref(v___x_4537_);
v___x_4538_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4535_ == 0)
{
lean_ctor_set(v___x_4534_, 0, v___x_4538_);
v___x_4540_ = v___x_4534_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4546_; 
v_reuseFailAlloc_4546_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4546_, 0, v___x_4538_);
lean_ctor_set_uint64(v_reuseFailAlloc_4546_, sizeof(void*)*1, v_tid_4532_);
v___x_4540_ = v_reuseFailAlloc_4546_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4542_; 
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 4, v___x_4540_);
v___x_4542_ = v___x_4530_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4545_; 
v_reuseFailAlloc_4545_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_env_4521_);
lean_ctor_set(v_reuseFailAlloc_4545_, 1, v_nextMacroScope_4522_);
lean_ctor_set(v_reuseFailAlloc_4545_, 2, v_ngen_4523_);
lean_ctor_set(v_reuseFailAlloc_4545_, 3, v_auxDeclNGen_4524_);
lean_ctor_set(v_reuseFailAlloc_4545_, 4, v___x_4540_);
lean_ctor_set(v_reuseFailAlloc_4545_, 5, v_cache_4525_);
lean_ctor_set(v_reuseFailAlloc_4545_, 6, v_messages_4526_);
lean_ctor_set(v_reuseFailAlloc_4545_, 7, v_infoState_4527_);
lean_ctor_set(v_reuseFailAlloc_4545_, 8, v_snapshotTasks_4528_);
v___x_4542_ = v_reuseFailAlloc_4545_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
lean_object* v___x_4543_; lean_object* v___x_4544_; 
v___x_4543_ = lean_st_ref_set(v___y_4514_, v___x_4542_);
v___x_4544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4544_, 0, v_traces_4518_);
return v___x_4544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4550_, lean_object* v___y_4551_){
_start:
{
lean_object* v_res_4552_; 
v_res_4552_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4550_);
lean_dec(v___y_4550_);
return v_res_4552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v___x_4558_; 
v___x_4558_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4556_);
return v___x_4558_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v_res_4564_; 
v_res_4564_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4559_, v___y_4560_, v___y_4561_, v___y_4562_);
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec(v___y_4560_);
lean_dec_ref(v___y_4559_);
return v_res_4564_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4565_, lean_object* v_zetaDeltaFVarIds_4566_, lean_object* v_a_x3f_4567_){
_start:
{
lean_object* v___x_4569_; lean_object* v_mctx_4570_; lean_object* v_cache_4571_; lean_object* v_postponed_4572_; lean_object* v_diag_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4583_; 
v___x_4569_ = lean_st_ref_take(v___y_4565_);
v_mctx_4570_ = lean_ctor_get(v___x_4569_, 0);
v_cache_4571_ = lean_ctor_get(v___x_4569_, 1);
v_postponed_4572_ = lean_ctor_get(v___x_4569_, 3);
v_diag_4573_ = lean_ctor_get(v___x_4569_, 4);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4569_);
if (v_isSharedCheck_4583_ == 0)
{
lean_object* v_unused_4584_; 
v_unused_4584_ = lean_ctor_get(v___x_4569_, 2);
lean_dec(v_unused_4584_);
v___x_4575_ = v___x_4569_;
v_isShared_4576_ = v_isSharedCheck_4583_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_diag_4573_);
lean_inc(v_postponed_4572_);
lean_inc(v_cache_4571_);
lean_inc(v_mctx_4570_);
lean_dec(v___x_4569_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4583_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4578_; 
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 2, v_zetaDeltaFVarIds_4566_);
v___x_4578_ = v___x_4575_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_mctx_4570_);
lean_ctor_set(v_reuseFailAlloc_4582_, 1, v_cache_4571_);
lean_ctor_set(v_reuseFailAlloc_4582_, 2, v_zetaDeltaFVarIds_4566_);
lean_ctor_set(v_reuseFailAlloc_4582_, 3, v_postponed_4572_);
lean_ctor_set(v_reuseFailAlloc_4582_, 4, v_diag_4573_);
v___x_4578_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; 
v___x_4579_ = lean_st_ref_set(v___y_4565_, v___x_4578_);
v___x_4580_ = lean_box(0);
v___x_4581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4581_, 0, v___x_4580_);
return v___x_4581_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4585_, lean_object* v_zetaDeltaFVarIds_4586_, lean_object* v_a_x3f_4587_, lean_object* v___y_4588_){
_start:
{
lean_object* v_res_4589_; 
v_res_4589_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4585_, v_zetaDeltaFVarIds_4586_, v_a_x3f_4587_);
lean_dec(v_a_x3f_4587_);
lean_dec(v___y_4585_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4590_, lean_object* v_msg_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_){
_start:
{
lean_object* v_ref_4597_; lean_object* v___x_4598_; lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4643_; 
v_ref_4597_ = lean_ctor_get(v___y_4594_, 5);
v___x_4598_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4643_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4643_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
lean_object* v___x_4603_; lean_object* v_traceState_4604_; lean_object* v_env_4605_; lean_object* v_nextMacroScope_4606_; lean_object* v_ngen_4607_; lean_object* v_auxDeclNGen_4608_; lean_object* v_cache_4609_; lean_object* v_messages_4610_; lean_object* v_infoState_4611_; lean_object* v_snapshotTasks_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4642_; 
v___x_4603_ = lean_st_ref_take(v___y_4595_);
v_traceState_4604_ = lean_ctor_get(v___x_4603_, 4);
v_env_4605_ = lean_ctor_get(v___x_4603_, 0);
v_nextMacroScope_4606_ = lean_ctor_get(v___x_4603_, 1);
v_ngen_4607_ = lean_ctor_get(v___x_4603_, 2);
v_auxDeclNGen_4608_ = lean_ctor_get(v___x_4603_, 3);
v_cache_4609_ = lean_ctor_get(v___x_4603_, 5);
v_messages_4610_ = lean_ctor_get(v___x_4603_, 6);
v_infoState_4611_ = lean_ctor_get(v___x_4603_, 7);
v_snapshotTasks_4612_ = lean_ctor_get(v___x_4603_, 8);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4603_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4614_ = v___x_4603_;
v_isShared_4615_ = v_isSharedCheck_4642_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_snapshotTasks_4612_);
lean_inc(v_infoState_4611_);
lean_inc(v_messages_4610_);
lean_inc(v_cache_4609_);
lean_inc(v_traceState_4604_);
lean_inc(v_auxDeclNGen_4608_);
lean_inc(v_ngen_4607_);
lean_inc(v_nextMacroScope_4606_);
lean_inc(v_env_4605_);
lean_dec(v___x_4603_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4642_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
uint64_t v_tid_4616_; lean_object* v_traces_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4641_; 
v_tid_4616_ = lean_ctor_get_uint64(v_traceState_4604_, sizeof(void*)*1);
v_traces_4617_ = lean_ctor_get(v_traceState_4604_, 0);
v_isSharedCheck_4641_ = !lean_is_exclusive(v_traceState_4604_);
if (v_isSharedCheck_4641_ == 0)
{
v___x_4619_ = v_traceState_4604_;
v_isShared_4620_ = v_isSharedCheck_4641_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_traces_4617_);
lean_dec(v_traceState_4604_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4641_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4621_; double v___x_4622_; uint8_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v___x_4621_ = lean_box(0);
v___x_4622_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4623_ = 0;
v___x_4624_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4625_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4625_, 0, v_cls_4590_);
lean_ctor_set(v___x_4625_, 1, v___x_4621_);
lean_ctor_set(v___x_4625_, 2, v___x_4624_);
lean_ctor_set_float(v___x_4625_, sizeof(void*)*3, v___x_4622_);
lean_ctor_set_float(v___x_4625_, sizeof(void*)*3 + 8, v___x_4622_);
lean_ctor_set_uint8(v___x_4625_, sizeof(void*)*3 + 16, v___x_4623_);
v___x_4626_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4627_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4627_, 0, v___x_4625_);
lean_ctor_set(v___x_4627_, 1, v_a_4599_);
lean_ctor_set(v___x_4627_, 2, v___x_4626_);
lean_inc(v_ref_4597_);
v___x_4628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4628_, 0, v_ref_4597_);
lean_ctor_set(v___x_4628_, 1, v___x_4627_);
v___x_4629_ = l_Lean_PersistentArray_push___redArg(v_traces_4617_, v___x_4628_);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 0, v___x_4629_);
v___x_4631_ = v___x_4619_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4640_; 
v_reuseFailAlloc_4640_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4640_, 0, v___x_4629_);
lean_ctor_set_uint64(v_reuseFailAlloc_4640_, sizeof(void*)*1, v_tid_4616_);
v___x_4631_ = v_reuseFailAlloc_4640_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4633_; 
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 4, v___x_4631_);
v___x_4633_ = v___x_4614_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4639_; 
v_reuseFailAlloc_4639_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4639_, 0, v_env_4605_);
lean_ctor_set(v_reuseFailAlloc_4639_, 1, v_nextMacroScope_4606_);
lean_ctor_set(v_reuseFailAlloc_4639_, 2, v_ngen_4607_);
lean_ctor_set(v_reuseFailAlloc_4639_, 3, v_auxDeclNGen_4608_);
lean_ctor_set(v_reuseFailAlloc_4639_, 4, v___x_4631_);
lean_ctor_set(v_reuseFailAlloc_4639_, 5, v_cache_4609_);
lean_ctor_set(v_reuseFailAlloc_4639_, 6, v_messages_4610_);
lean_ctor_set(v_reuseFailAlloc_4639_, 7, v_infoState_4611_);
lean_ctor_set(v_reuseFailAlloc_4639_, 8, v_snapshotTasks_4612_);
v___x_4633_ = v_reuseFailAlloc_4639_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
lean_object* v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4637_; 
v___x_4634_ = lean_st_ref_set(v___y_4595_, v___x_4633_);
v___x_4635_ = lean_box(0);
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4635_);
v___x_4637_ = v___x_4601_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4638_; 
v_reuseFailAlloc_4638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4638_, 0, v___x_4635_);
v___x_4637_ = v_reuseFailAlloc_4638_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
return v___x_4637_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4644_, lean_object* v_msg_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4644_, v_msg_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec(v___y_4647_);
lean_dec_ref(v___y_4646_);
return v_res_4651_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4654_ = l_Lean_stringToMessageData(v___x_4653_);
return v___x_4654_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4657_ = l_Lean_stringToMessageData(v___x_4656_);
return v___x_4657_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4659_; lean_object* v___x_4660_; 
v___x_4659_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4660_ = l_Lean_stringToMessageData(v___x_4659_);
return v___x_4660_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4662_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4663_ = l_Lean_stringToMessageData(v___x_4662_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4664_, lean_object* v_e_4665_, lean_object* v___x_4666_, lean_object* v___x_4667_, lean_object* v_cls_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = lean_st_mk_ref(v___x_4664_);
v___x_4675_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4665_, v___x_4666_, v___x_4674_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; lean_object* v___x_4678_; uint8_t v_isShared_4679_; uint8_t v_isSharedCheck_4745_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4745_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4745_ == 0)
{
v___x_4678_ = v___x_4675_;
v_isShared_4679_ = v_isSharedCheck_4745_;
goto v_resetjp_4677_;
}
else
{
lean_inc(v_a_4676_);
lean_dec(v___x_4675_);
v___x_4678_ = lean_box(0);
v_isShared_4679_ = v_isSharedCheck_4745_;
goto v_resetjp_4677_;
}
v_resetjp_4677_:
{
lean_object* v___x_4680_; lean_object* v_count_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4743_; 
v___x_4680_ = lean_st_ref_get(v___x_4674_);
lean_dec(v___x_4674_);
v_count_4681_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4743_ == 0)
{
lean_object* v_unused_4744_; 
v_unused_4744_ = lean_ctor_get(v___x_4680_, 1);
lean_dec(v_unused_4744_);
v___x_4683_ = v___x_4680_;
v_isShared_4684_ = v_isSharedCheck_4743_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_count_4681_);
lean_dec(v___x_4680_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4743_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
uint8_t v___x_4707_; 
v___x_4707_ = lean_nat_dec_eq(v_count_4681_, v___x_4667_);
if (v___x_4707_ == 0)
{
lean_object* v_options_4708_; uint8_t v_hasTrace_4709_; 
v_options_4708_ = lean_ctor_get(v___y_4671_, 2);
v_hasTrace_4709_ = lean_ctor_get_uint8(v_options_4708_, sizeof(void*)*1);
if (v_hasTrace_4709_ == 0)
{
lean_dec(v_cls_4668_);
goto v___jp_4685_;
}
else
{
lean_object* v_inheritedTraceOptions_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; uint8_t v___x_4713_; 
v_inheritedTraceOptions_4710_ = lean_ctor_get(v___y_4671_, 13);
v___x_4711_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4668_);
v___x_4712_ = l_Lean_Name_append(v___x_4711_, v_cls_4668_);
v___x_4713_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4710_, v_options_4708_, v___x_4712_);
lean_dec(v___x_4712_);
if (v___x_4713_ == 0)
{
lean_dec(v_cls_4668_);
goto v___jp_4685_;
}
else
{
lean_object* v_expr_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v_expr_4714_ = lean_ctor_get(v_a_4676_, 0);
v___x_4715_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4714_);
v___x_4716_ = l_Lean_indentExpr(v_expr_4714_);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4668_, v___x_4717_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_dec_ref_known(v___x_4718_, 1);
goto v___jp_4685_;
}
else
{
lean_object* v_a_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4726_; 
lean_del_object(v___x_4683_);
lean_dec(v_count_4681_);
lean_del_object(v___x_4678_);
lean_dec(v_a_4676_);
v_a_4719_ = lean_ctor_get(v___x_4718_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4718_);
if (v_isSharedCheck_4726_ == 0)
{
v___x_4721_ = v___x_4718_;
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_a_4719_);
lean_dec(v___x_4718_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4726_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4724_; 
if (v_isShared_4722_ == 0)
{
v___x_4724_ = v___x_4721_;
goto v_reusejp_4723_;
}
else
{
lean_object* v_reuseFailAlloc_4725_; 
v_reuseFailAlloc_4725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4725_, 0, v_a_4719_);
v___x_4724_ = v_reuseFailAlloc_4725_;
goto v_reusejp_4723_;
}
v_reusejp_4723_:
{
return v___x_4724_;
}
}
}
}
}
}
else
{
lean_object* v_options_4727_; uint8_t v_hasTrace_4728_; 
v_options_4727_ = lean_ctor_get(v___y_4671_, 2);
v_hasTrace_4728_ = lean_ctor_get_uint8(v_options_4727_, sizeof(void*)*1);
if (v_hasTrace_4728_ == 0)
{
lean_dec(v_cls_4668_);
goto v___jp_4685_;
}
else
{
lean_object* v_inheritedTraceOptions_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
v_inheritedTraceOptions_4729_ = lean_ctor_get(v___y_4671_, 13);
v___x_4730_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4668_);
v___x_4731_ = l_Lean_Name_append(v___x_4730_, v_cls_4668_);
v___x_4732_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4729_, v_options_4727_, v___x_4731_);
lean_dec(v___x_4731_);
if (v___x_4732_ == 0)
{
lean_dec(v_cls_4668_);
goto v___jp_4685_;
}
else
{
lean_object* v___x_4733_; lean_object* v___x_4734_; 
v___x_4733_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4734_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4668_, v___x_4733_, v___y_4669_, v___y_4670_, v___y_4671_, v___y_4672_);
if (lean_obj_tag(v___x_4734_) == 0)
{
lean_dec_ref_known(v___x_4734_, 1);
goto v___jp_4685_;
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4737_; uint8_t v_isShared_4738_; uint8_t v_isSharedCheck_4742_; 
lean_del_object(v___x_4683_);
lean_dec(v_count_4681_);
lean_del_object(v___x_4678_);
lean_dec(v_a_4676_);
v_a_4735_ = lean_ctor_get(v___x_4734_, 0);
v_isSharedCheck_4742_ = !lean_is_exclusive(v___x_4734_);
if (v_isSharedCheck_4742_ == 0)
{
v___x_4737_ = v___x_4734_;
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
else
{
lean_inc(v_a_4735_);
lean_dec(v___x_4734_);
v___x_4737_ = lean_box(0);
v_isShared_4738_ = v_isSharedCheck_4742_;
goto v_resetjp_4736_;
}
v_resetjp_4736_:
{
lean_object* v___x_4740_; 
if (v_isShared_4738_ == 0)
{
v___x_4740_ = v___x_4737_;
goto v_reusejp_4739_;
}
else
{
lean_object* v_reuseFailAlloc_4741_; 
v_reuseFailAlloc_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4741_, 0, v_a_4735_);
v___x_4740_ = v_reuseFailAlloc_4741_;
goto v_reusejp_4739_;
}
v_reusejp_4739_:
{
return v___x_4740_;
}
}
}
}
}
}
v___jp_4685_:
{
lean_object* v_expr_4686_; lean_object* v___x_4688_; uint8_t v_isShared_4689_; uint8_t v_isSharedCheck_4705_; 
v_expr_4686_ = lean_ctor_get(v_a_4676_, 0);
v_isSharedCheck_4705_ = !lean_is_exclusive(v_a_4676_);
if (v_isSharedCheck_4705_ == 0)
{
lean_object* v_unused_4706_; 
v_unused_4706_ = lean_ctor_get(v_a_4676_, 1);
lean_dec(v_unused_4706_);
v___x_4688_ = v_a_4676_;
v_isShared_4689_ = v_isSharedCheck_4705_;
goto v_resetjp_4687_;
}
else
{
lean_inc(v_expr_4686_);
lean_dec(v_a_4676_);
v___x_4688_ = lean_box(0);
v_isShared_4689_ = v_isSharedCheck_4705_;
goto v_resetjp_4687_;
}
v_resetjp_4687_:
{
lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4695_; 
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4691_ = l_Nat_reprFast(v_count_4681_);
v___x_4692_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4691_);
v___x_4693_ = l_Lean_MessageData_ofFormat(v___x_4692_);
if (v_isShared_4689_ == 0)
{
lean_ctor_set_tag(v___x_4688_, 7);
lean_ctor_set(v___x_4688_, 1, v___x_4693_);
lean_ctor_set(v___x_4688_, 0, v___x_4690_);
v___x_4695_ = v___x_4688_;
goto v_reusejp_4694_;
}
else
{
lean_object* v_reuseFailAlloc_4704_; 
v_reuseFailAlloc_4704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4704_, 0, v___x_4690_);
lean_ctor_set(v_reuseFailAlloc_4704_, 1, v___x_4693_);
v___x_4695_ = v_reuseFailAlloc_4704_;
goto v_reusejp_4694_;
}
v_reusejp_4694_:
{
lean_object* v___x_4696_; lean_object* v___x_4698_; 
v___x_4696_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4684_ == 0)
{
lean_ctor_set_tag(v___x_4683_, 7);
lean_ctor_set(v___x_4683_, 1, v___x_4696_);
lean_ctor_set(v___x_4683_, 0, v___x_4695_);
v___x_4698_ = v___x_4683_;
goto v_reusejp_4697_;
}
else
{
lean_object* v_reuseFailAlloc_4703_; 
v_reuseFailAlloc_4703_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4703_, 0, v___x_4695_);
lean_ctor_set(v_reuseFailAlloc_4703_, 1, v___x_4696_);
v___x_4698_ = v_reuseFailAlloc_4703_;
goto v_reusejp_4697_;
}
v_reusejp_4697_:
{
lean_object* v___x_4699_; lean_object* v___x_4701_; 
v___x_4699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4699_, 0, v_expr_4686_);
lean_ctor_set(v___x_4699_, 1, v___x_4698_);
if (v_isShared_4679_ == 0)
{
lean_ctor_set(v___x_4678_, 0, v___x_4699_);
v___x_4701_ = v___x_4678_;
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
}
}
}
}
}
}
else
{
lean_object* v_a_4746_; lean_object* v___x_4748_; uint8_t v_isShared_4749_; uint8_t v_isSharedCheck_4753_; 
lean_dec(v___x_4674_);
lean_dec(v_cls_4668_);
v_a_4746_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4748_ = v___x_4675_;
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
else
{
lean_inc(v_a_4746_);
lean_dec(v___x_4675_);
v___x_4748_ = lean_box(0);
v_isShared_4749_ = v_isSharedCheck_4753_;
goto v_resetjp_4747_;
}
v_resetjp_4747_:
{
lean_object* v___x_4751_; 
if (v_isShared_4749_ == 0)
{
v___x_4751_ = v___x_4748_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_a_4746_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4754_, lean_object* v_e_4755_, lean_object* v___x_4756_, lean_object* v___x_4757_, lean_object* v_cls_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_, lean_object* v___y_4762_, lean_object* v___y_4763_){
_start:
{
lean_object* v_res_4764_; 
v_res_4764_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4754_, v_e_4755_, v___x_4756_, v___x_4757_, v_cls_4758_, v___y_4759_, v___y_4760_, v___y_4761_, v___y_4762_);
lean_dec(v___y_4762_);
lean_dec_ref(v___y_4761_);
lean_dec(v___y_4760_);
lean_dec_ref(v___y_4759_);
lean_dec(v___x_4757_);
lean_dec(v___x_4756_);
return v_res_4764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4765_, lean_object* v_cache_4766_, lean_object* v_a_x3f_4767_){
_start:
{
lean_object* v___x_4769_; lean_object* v_mctx_4770_; lean_object* v_zetaDeltaFVarIds_4771_; lean_object* v_postponed_4772_; lean_object* v_diag_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4783_; 
v___x_4769_ = lean_st_ref_take(v___y_4765_);
v_mctx_4770_ = lean_ctor_get(v___x_4769_, 0);
v_zetaDeltaFVarIds_4771_ = lean_ctor_get(v___x_4769_, 2);
v_postponed_4772_ = lean_ctor_get(v___x_4769_, 3);
v_diag_4773_ = lean_ctor_get(v___x_4769_, 4);
v_isSharedCheck_4783_ = !lean_is_exclusive(v___x_4769_);
if (v_isSharedCheck_4783_ == 0)
{
lean_object* v_unused_4784_; 
v_unused_4784_ = lean_ctor_get(v___x_4769_, 1);
lean_dec(v_unused_4784_);
v___x_4775_ = v___x_4769_;
v_isShared_4776_ = v_isSharedCheck_4783_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_diag_4773_);
lean_inc(v_postponed_4772_);
lean_inc(v_zetaDeltaFVarIds_4771_);
lean_inc(v_mctx_4770_);
lean_dec(v___x_4769_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4783_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
lean_ctor_set(v___x_4775_, 1, v_cache_4766_);
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4782_; 
v_reuseFailAlloc_4782_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4782_, 0, v_mctx_4770_);
lean_ctor_set(v_reuseFailAlloc_4782_, 1, v_cache_4766_);
lean_ctor_set(v_reuseFailAlloc_4782_, 2, v_zetaDeltaFVarIds_4771_);
lean_ctor_set(v_reuseFailAlloc_4782_, 3, v_postponed_4772_);
lean_ctor_set(v_reuseFailAlloc_4782_, 4, v_diag_4773_);
v___x_4778_ = v_reuseFailAlloc_4782_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4779_ = lean_st_ref_set(v___y_4765_, v___x_4778_);
v___x_4780_ = lean_box(0);
v___x_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4780_);
return v___x_4781_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4785_, lean_object* v_cache_4786_, lean_object* v_a_x3f_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v_res_4789_; 
v_res_4789_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4785_, v_cache_4786_, v_a_x3f_4787_);
lean_dec(v_a_x3f_4787_);
lean_dec(v___y_4785_);
return v_res_4789_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4793_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1));
v___x_4794_ = l_Lean_MessageData_ofFormat(v___x_4793_);
return v___x_4794_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4795_; 
v___x_4795_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4795_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4(void){
_start:
{
lean_object* v___x_4796_; lean_object* v___x_4797_; 
v___x_4796_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3);
v___x_4797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4796_);
return v___x_4797_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5(void){
_start:
{
lean_object* v___x_4798_; lean_object* v___x_4799_; 
v___x_4798_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4);
v___x_4799_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
lean_ctor_set(v___x_4799_, 1, v___x_4798_);
lean_ctor_set(v___x_4799_, 2, v___x_4798_);
lean_ctor_set(v___x_4799_, 3, v___x_4798_);
lean_ctor_set(v___x_4799_, 4, v___x_4798_);
lean_ctor_set(v___x_4799_, 5, v___x_4798_);
return v___x_4799_;
}
}
static uint64_t _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6(void){
_start:
{
uint8_t v___x_4800_; uint64_t v___x_4801_; 
v___x_4800_ = 0;
v___x_4801_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4800_);
return v___x_4801_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7(void){
_start:
{
lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; 
v___x_4802_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4803_ = lean_unsigned_to_nat(0u);
v___x_4804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4804_, 0, v___x_4803_);
lean_ctor_set(v___x_4804_, 1, v___x_4802_);
return v___x_4804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_4805_, lean_object* v_e_4806_, uint8_t v___x_4807_, lean_object* v_cls_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
if (v___x_4805_ == 0)
{
lean_object* v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
lean_dec(v_cls_4808_);
v___x_4814_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2);
v___x_4815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4815_, 0, v_e_4806_);
lean_ctor_set(v___x_4815_, 1, v___x_4814_);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
return v___x_4816_;
}
else
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v_mctx_4819_; lean_object* v_zetaDeltaFVarIds_4820_; lean_object* v_postponed_4821_; lean_object* v_diag_4822_; lean_object* v___x_4824_; uint8_t v_isShared_4825_; uint8_t v_isSharedCheck_5010_; 
v___x_4817_ = lean_st_ref_get(v___y_4810_);
v___x_4818_ = lean_st_ref_take(v___y_4810_);
v_mctx_4819_ = lean_ctor_get(v___x_4818_, 0);
v_zetaDeltaFVarIds_4820_ = lean_ctor_get(v___x_4818_, 2);
v_postponed_4821_ = lean_ctor_get(v___x_4818_, 3);
v_diag_4822_ = lean_ctor_get(v___x_4818_, 4);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4818_);
if (v_isSharedCheck_5010_ == 0)
{
lean_object* v_unused_5011_; 
v_unused_5011_ = lean_ctor_get(v___x_4818_, 1);
lean_dec(v_unused_5011_);
v___x_4824_ = v___x_4818_;
v_isShared_4825_ = v_isSharedCheck_5010_;
goto v_resetjp_4823_;
}
else
{
lean_inc(v_diag_4822_);
lean_inc(v_postponed_4821_);
lean_inc(v_zetaDeltaFVarIds_4820_);
lean_inc(v_mctx_4819_);
lean_dec(v___x_4818_);
v___x_4824_ = lean_box(0);
v_isShared_4825_ = v_isSharedCheck_5010_;
goto v_resetjp_4823_;
}
v_resetjp_4823_:
{
lean_object* v___x_4826_; lean_object* v___x_4828_; 
v___x_4826_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5);
if (v_isShared_4825_ == 0)
{
lean_ctor_set(v___x_4824_, 1, v___x_4826_);
v___x_4828_ = v___x_4824_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_mctx_4819_);
lean_ctor_set(v_reuseFailAlloc_5009_, 1, v___x_4826_);
lean_ctor_set(v_reuseFailAlloc_5009_, 2, v_zetaDeltaFVarIds_4820_);
lean_ctor_set(v_reuseFailAlloc_5009_, 3, v_postponed_4821_);
lean_ctor_set(v_reuseFailAlloc_5009_, 4, v_diag_4822_);
v___x_4828_ = v_reuseFailAlloc_5009_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v_mctx_4831_; lean_object* v_cache_4832_; lean_object* v_zetaDeltaFVarIds_4833_; lean_object* v_postponed_4834_; lean_object* v_diag_4835_; lean_object* v___x_4837_; uint8_t v_isShared_4838_; uint8_t v_isSharedCheck_5008_; 
v___x_4829_ = lean_st_ref_set(v___y_4810_, v___x_4828_);
v___x_4830_ = lean_st_ref_take(v___y_4810_);
v_mctx_4831_ = lean_ctor_get(v___x_4830_, 0);
v_cache_4832_ = lean_ctor_get(v___x_4830_, 1);
v_zetaDeltaFVarIds_4833_ = lean_ctor_get(v___x_4830_, 2);
v_postponed_4834_ = lean_ctor_get(v___x_4830_, 3);
v_diag_4835_ = lean_ctor_get(v___x_4830_, 4);
v_isSharedCheck_5008_ = !lean_is_exclusive(v___x_4830_);
if (v_isSharedCheck_5008_ == 0)
{
v___x_4837_ = v___x_4830_;
v_isShared_4838_ = v_isSharedCheck_5008_;
goto v_resetjp_4836_;
}
else
{
lean_inc(v_diag_4835_);
lean_inc(v_postponed_4834_);
lean_inc(v_zetaDeltaFVarIds_4833_);
lean_inc(v_cache_4832_);
lean_inc(v_mctx_4831_);
lean_dec(v___x_4830_);
v___x_4837_ = lean_box(0);
v_isShared_4838_ = v_isSharedCheck_5008_;
goto v_resetjp_4836_;
}
v_resetjp_4836_:
{
lean_object* v___x_4839_; lean_object* v___x_4841_; 
v___x_4839_ = lean_box(1);
if (v_isShared_4838_ == 0)
{
lean_ctor_set(v___x_4837_, 2, v___x_4839_);
v___x_4841_ = v___x_4837_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_5007_; 
v_reuseFailAlloc_5007_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5007_, 0, v_mctx_4831_);
lean_ctor_set(v_reuseFailAlloc_5007_, 1, v_cache_4832_);
lean_ctor_set(v_reuseFailAlloc_5007_, 2, v___x_4839_);
lean_ctor_set(v_reuseFailAlloc_5007_, 3, v_postponed_4834_);
lean_ctor_set(v_reuseFailAlloc_5007_, 4, v_diag_4835_);
v___x_4841_ = v_reuseFailAlloc_5007_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
lean_object* v___x_4842_; lean_object* v_cache_4843_; lean_object* v_keyedConfig_4844_; lean_object* v_zetaDeltaSet_4845_; lean_object* v_lctx_4846_; lean_object* v_localInstances_4847_; lean_object* v_defEqCtx_x3f_4848_; lean_object* v_synthPendingDepth_4849_; lean_object* v_canUnfold_x3f_4850_; uint8_t v_univApprox_4851_; uint8_t v_inTypeClassResolution_4852_; uint8_t v_cacheInferType_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; uint8_t v_foApprox_4856_; uint8_t v_ctxApprox_4857_; uint8_t v_quasiPatternApprox_4858_; uint8_t v_constApprox_4859_; uint8_t v_isDefEqStuckEx_4860_; uint8_t v_unificationHints_4861_; uint8_t v_proofIrrelevance_4862_; uint8_t v_assignSyntheticOpaque_4863_; uint8_t v_offsetCnstrs_4864_; uint8_t v_etaStruct_4865_; uint8_t v_univApprox_4866_; uint8_t v_iota_4867_; uint8_t v_beta_4868_; uint8_t v_proj_4869_; uint8_t v_zeta_4870_; uint8_t v_zetaDelta_4871_; uint8_t v_zetaUnused_4872_; uint8_t v_zetaHave_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_5006_; 
v___x_4842_ = lean_st_ref_set(v___y_4810_, v___x_4841_);
v_cache_4843_ = lean_ctor_get(v___x_4817_, 1);
lean_inc_ref(v_cache_4843_);
lean_dec(v___x_4817_);
v_keyedConfig_4844_ = lean_ctor_get(v___y_4809_, 0);
v_zetaDeltaSet_4845_ = lean_ctor_get(v___y_4809_, 1);
v_lctx_4846_ = lean_ctor_get(v___y_4809_, 2);
v_localInstances_4847_ = lean_ctor_get(v___y_4809_, 3);
v_defEqCtx_x3f_4848_ = lean_ctor_get(v___y_4809_, 4);
v_synthPendingDepth_4849_ = lean_ctor_get(v___y_4809_, 5);
v_canUnfold_x3f_4850_ = lean_ctor_get(v___y_4809_, 6);
v_univApprox_4851_ = lean_ctor_get_uint8(v___y_4809_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4852_ = lean_ctor_get_uint8(v___y_4809_, sizeof(void*)*7 + 2);
v_cacheInferType_4853_ = lean_ctor_get_uint8(v___y_4809_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_4850_);
lean_inc(v_synthPendingDepth_4849_);
lean_inc(v_defEqCtx_x3f_4848_);
lean_inc_ref(v_localInstances_4847_);
lean_inc_ref(v_lctx_4846_);
lean_inc(v_zetaDeltaSet_4845_);
lean_inc_ref(v_keyedConfig_4844_);
v___x_4854_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4854_, 0, v_keyedConfig_4844_);
lean_ctor_set(v___x_4854_, 1, v_zetaDeltaSet_4845_);
lean_ctor_set(v___x_4854_, 2, v_lctx_4846_);
lean_ctor_set(v___x_4854_, 3, v_localInstances_4847_);
lean_ctor_set(v___x_4854_, 4, v_defEqCtx_x3f_4848_);
lean_ctor_set(v___x_4854_, 5, v_synthPendingDepth_4849_);
lean_ctor_set(v___x_4854_, 6, v_canUnfold_x3f_4850_);
lean_ctor_set_uint8(v___x_4854_, sizeof(void*)*7, v___x_4807_);
lean_ctor_set_uint8(v___x_4854_, sizeof(void*)*7 + 1, v_univApprox_4851_);
lean_ctor_set_uint8(v___x_4854_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4852_);
lean_ctor_set_uint8(v___x_4854_, sizeof(void*)*7 + 3, v_cacheInferType_4853_);
v___x_4855_ = l_Lean_Meta_Context_config(v___x_4854_);
v_foApprox_4856_ = lean_ctor_get_uint8(v___x_4855_, 0);
v_ctxApprox_4857_ = lean_ctor_get_uint8(v___x_4855_, 1);
v_quasiPatternApprox_4858_ = lean_ctor_get_uint8(v___x_4855_, 2);
v_constApprox_4859_ = lean_ctor_get_uint8(v___x_4855_, 3);
v_isDefEqStuckEx_4860_ = lean_ctor_get_uint8(v___x_4855_, 4);
v_unificationHints_4861_ = lean_ctor_get_uint8(v___x_4855_, 5);
v_proofIrrelevance_4862_ = lean_ctor_get_uint8(v___x_4855_, 6);
v_assignSyntheticOpaque_4863_ = lean_ctor_get_uint8(v___x_4855_, 7);
v_offsetCnstrs_4864_ = lean_ctor_get_uint8(v___x_4855_, 8);
v_etaStruct_4865_ = lean_ctor_get_uint8(v___x_4855_, 10);
v_univApprox_4866_ = lean_ctor_get_uint8(v___x_4855_, 11);
v_iota_4867_ = lean_ctor_get_uint8(v___x_4855_, 12);
v_beta_4868_ = lean_ctor_get_uint8(v___x_4855_, 13);
v_proj_4869_ = lean_ctor_get_uint8(v___x_4855_, 14);
v_zeta_4870_ = lean_ctor_get_uint8(v___x_4855_, 15);
v_zetaDelta_4871_ = lean_ctor_get_uint8(v___x_4855_, 16);
v_zetaUnused_4872_ = lean_ctor_get_uint8(v___x_4855_, 17);
v_zetaHave_4873_ = lean_ctor_get_uint8(v___x_4855_, 18);
v_isSharedCheck_5006_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_5006_ == 0)
{
v___x_4875_ = v___x_4855_;
v_isShared_4876_ = v_isSharedCheck_5006_;
goto v_resetjp_4874_;
}
else
{
lean_dec(v___x_4855_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_5006_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
uint8_t v___x_4877_; lean_object* v_config_4879_; 
v___x_4877_ = 0;
if (v_isShared_4876_ == 0)
{
v_config_4879_ = v___x_4875_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_5005_; 
v_reuseFailAlloc_5005_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 0, v_foApprox_4856_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 1, v_ctxApprox_4857_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 2, v_quasiPatternApprox_4858_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 3, v_constApprox_4859_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 4, v_isDefEqStuckEx_4860_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 5, v_unificationHints_4861_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 6, v_proofIrrelevance_4862_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 7, v_assignSyntheticOpaque_4863_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 8, v_offsetCnstrs_4864_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 10, v_etaStruct_4865_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 11, v_univApprox_4866_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 12, v_iota_4867_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 13, v_beta_4868_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 14, v_proj_4869_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 15, v_zeta_4870_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 16, v_zetaDelta_4871_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 17, v_zetaUnused_4872_);
lean_ctor_set_uint8(v_reuseFailAlloc_5005_, 18, v_zetaHave_4873_);
v_config_4879_ = v_reuseFailAlloc_5005_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
uint64_t v___x_4880_; uint64_t v___x_4881_; uint64_t v___x_4882_; uint64_t v___x_4883_; uint64_t v___x_4884_; uint64_t v_key_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; uint8_t v_transparency_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v_a_4894_; lean_object* v___y_4906_; lean_object* v___y_4929_; uint8_t v___y_4957_; uint8_t v___x_5003_; uint8_t v___x_5004_; 
lean_ctor_set_uint8(v_config_4879_, 9, v___x_4877_);
v___x_4880_ = l_Lean_Meta_Context_configKey(v___x_4854_);
lean_dec_ref_known(v___x_4854_, 7);
v___x_4881_ = 3ULL;
v___x_4882_ = lean_uint64_shift_right(v___x_4880_, v___x_4881_);
v___x_4883_ = lean_uint64_shift_left(v___x_4882_, v___x_4881_);
v___x_4884_ = lean_uint64_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6);
v_key_4885_ = lean_uint64_lor(v___x_4883_, v___x_4884_);
v___x_4886_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4886_, 0, v_config_4879_);
lean_ctor_set_uint64(v___x_4886_, sizeof(void*)*1, v_key_4885_);
lean_inc(v_canUnfold_x3f_4850_);
lean_inc(v_synthPendingDepth_4849_);
lean_inc(v_defEqCtx_x3f_4848_);
lean_inc_ref(v_localInstances_4847_);
lean_inc_ref(v_lctx_4846_);
lean_inc(v_zetaDeltaSet_4845_);
v___x_4887_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4887_, 0, v___x_4886_);
lean_ctor_set(v___x_4887_, 1, v_zetaDeltaSet_4845_);
lean_ctor_set(v___x_4887_, 2, v_lctx_4846_);
lean_ctor_set(v___x_4887_, 3, v_localInstances_4847_);
lean_ctor_set(v___x_4887_, 4, v_defEqCtx_x3f_4848_);
lean_ctor_set(v___x_4887_, 5, v_synthPendingDepth_4849_);
lean_ctor_set(v___x_4887_, 6, v_canUnfold_x3f_4850_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*7, v___x_4807_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*7 + 1, v_univApprox_4851_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4852_);
lean_ctor_set_uint8(v___x_4887_, sizeof(void*)*7 + 3, v_cacheInferType_4853_);
v___x_4888_ = l_Lean_Meta_Context_config(v___x_4887_);
v_transparency_4889_ = lean_ctor_get_uint8(v___x_4888_, 9);
v___x_4890_ = lean_unsigned_to_nat(0u);
v___x_4891_ = lean_box(0);
v___x_4892_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7);
v___x_5003_ = 1;
v___x_5004_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4889_, v___x_5003_);
if (v___x_5004_ == 0)
{
v___y_4957_ = v_transparency_4889_;
goto v___jp_4956_;
}
else
{
v___y_4957_ = v___x_5003_;
goto v___jp_4956_;
}
v___jp_4893_:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4903_; 
v___x_4895_ = lean_box(0);
v___x_4896_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4810_, v_cache_4843_, v___x_4895_);
v_isSharedCheck_4903_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4903_ == 0)
{
lean_object* v_unused_4904_; 
v_unused_4904_ = lean_ctor_get(v___x_4896_, 0);
lean_dec(v_unused_4904_);
v___x_4898_ = v___x_4896_;
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
else
{
lean_dec(v___x_4896_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4903_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4901_; 
if (v_isShared_4899_ == 0)
{
lean_ctor_set_tag(v___x_4898_, 1);
lean_ctor_set(v___x_4898_, 0, v_a_4894_);
v___x_4901_ = v___x_4898_;
goto v_reusejp_4900_;
}
else
{
lean_object* v_reuseFailAlloc_4902_; 
v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4894_);
v___x_4901_ = v_reuseFailAlloc_4902_;
goto v_reusejp_4900_;
}
v_reusejp_4900_:
{
return v___x_4901_;
}
}
}
v___jp_4905_:
{
if (lean_obj_tag(v___y_4906_) == 0)
{
lean_object* v_a_4907_; lean_object* v___x_4909_; uint8_t v_isShared_4910_; uint8_t v_isSharedCheck_4924_; 
v_a_4907_ = lean_ctor_get(v___y_4906_, 0);
v_isSharedCheck_4924_ = !lean_is_exclusive(v___y_4906_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4909_ = v___y_4906_;
v_isShared_4910_ = v_isSharedCheck_4924_;
goto v_resetjp_4908_;
}
else
{
lean_inc(v_a_4907_);
lean_dec(v___y_4906_);
v___x_4909_ = lean_box(0);
v_isShared_4910_ = v_isSharedCheck_4924_;
goto v_resetjp_4908_;
}
v_resetjp_4908_:
{
lean_object* v___x_4912_; 
lean_inc(v_a_4907_);
if (v_isShared_4910_ == 0)
{
lean_ctor_set_tag(v___x_4909_, 1);
v___x_4912_ = v___x_4909_;
goto v_reusejp_4911_;
}
else
{
lean_object* v_reuseFailAlloc_4923_; 
v_reuseFailAlloc_4923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4923_, 0, v_a_4907_);
v___x_4912_ = v_reuseFailAlloc_4923_;
goto v_reusejp_4911_;
}
v_reusejp_4911_:
{
lean_object* v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
v___x_4913_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4810_, v_zetaDeltaFVarIds_4833_, v___x_4912_);
lean_dec_ref(v___x_4913_);
v___x_4914_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4810_, v_cache_4843_, v___x_4912_);
lean_dec_ref(v___x_4912_);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4921_ == 0)
{
lean_object* v_unused_4922_; 
v_unused_4922_ = lean_ctor_get(v___x_4914_, 0);
lean_dec(v_unused_4922_);
v___x_4916_ = v___x_4914_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_dec(v___x_4914_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
lean_ctor_set(v___x_4916_, 0, v_a_4907_);
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4907_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
}
else
{
lean_object* v_a_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_a_4925_ = lean_ctor_get(v___y_4906_, 0);
lean_inc(v_a_4925_);
lean_dec_ref_known(v___y_4906_, 1);
v___x_4926_ = lean_box(0);
v___x_4927_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4810_, v_zetaDeltaFVarIds_4833_, v___x_4926_);
lean_dec_ref(v___x_4927_);
v_a_4894_ = v_a_4925_;
goto v___jp_4893_;
}
}
v___jp_4928_:
{
lean_object* v___x_4930_; uint8_t v_foApprox_4931_; uint8_t v_ctxApprox_4932_; uint8_t v_quasiPatternApprox_4933_; uint8_t v_constApprox_4934_; uint8_t v_isDefEqStuckEx_4935_; uint8_t v_unificationHints_4936_; uint8_t v_proofIrrelevance_4937_; uint8_t v_assignSyntheticOpaque_4938_; uint8_t v_offsetCnstrs_4939_; uint8_t v_transparency_4940_; uint8_t v_univApprox_4941_; uint8_t v_zetaUnused_4942_; lean_object* v___x_4944_; uint8_t v_isShared_4945_; uint8_t v_isSharedCheck_4955_; 
v___x_4930_ = l_Lean_Meta_Context_config(v___y_4929_);
lean_dec_ref(v___y_4929_);
v_foApprox_4931_ = lean_ctor_get_uint8(v___x_4930_, 0);
v_ctxApprox_4932_ = lean_ctor_get_uint8(v___x_4930_, 1);
v_quasiPatternApprox_4933_ = lean_ctor_get_uint8(v___x_4930_, 2);
v_constApprox_4934_ = lean_ctor_get_uint8(v___x_4930_, 3);
v_isDefEqStuckEx_4935_ = lean_ctor_get_uint8(v___x_4930_, 4);
v_unificationHints_4936_ = lean_ctor_get_uint8(v___x_4930_, 5);
v_proofIrrelevance_4937_ = lean_ctor_get_uint8(v___x_4930_, 6);
v_assignSyntheticOpaque_4938_ = lean_ctor_get_uint8(v___x_4930_, 7);
v_offsetCnstrs_4939_ = lean_ctor_get_uint8(v___x_4930_, 8);
v_transparency_4940_ = lean_ctor_get_uint8(v___x_4930_, 9);
v_univApprox_4941_ = lean_ctor_get_uint8(v___x_4930_, 11);
v_zetaUnused_4942_ = lean_ctor_get_uint8(v___x_4930_, 17);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4930_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4944_ = v___x_4930_;
v_isShared_4945_ = v_isSharedCheck_4955_;
goto v_resetjp_4943_;
}
else
{
lean_dec(v___x_4930_);
v___x_4944_ = lean_box(0);
v_isShared_4945_ = v_isSharedCheck_4955_;
goto v_resetjp_4943_;
}
v_resetjp_4943_:
{
uint8_t v___x_4946_; uint8_t v___x_4947_; lean_object* v___x_4949_; 
v___x_4946_ = 0;
v___x_4947_ = 2;
if (v_isShared_4945_ == 0)
{
v___x_4949_ = v___x_4944_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 0, v_foApprox_4931_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 1, v_ctxApprox_4932_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 2, v_quasiPatternApprox_4933_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 3, v_constApprox_4934_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 4, v_isDefEqStuckEx_4935_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 5, v_unificationHints_4936_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 6, v_proofIrrelevance_4937_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 7, v_assignSyntheticOpaque_4938_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 8, v_offsetCnstrs_4939_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 9, v_transparency_4940_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 11, v_univApprox_4941_);
lean_ctor_set_uint8(v_reuseFailAlloc_4954_, 17, v_zetaUnused_4942_);
v___x_4949_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4948_;
}
v_reusejp_4948_:
{
uint64_t v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_ctor_set_uint8(v___x_4949_, 10, v___x_4946_);
lean_ctor_set_uint8(v___x_4949_, 12, v___x_4807_);
lean_ctor_set_uint8(v___x_4949_, 13, v___x_4807_);
lean_ctor_set_uint8(v___x_4949_, 14, v___x_4947_);
lean_ctor_set_uint8(v___x_4949_, 15, v___x_4807_);
lean_ctor_set_uint8(v___x_4949_, 16, v___x_4807_);
lean_ctor_set_uint8(v___x_4949_, 18, v___x_4807_);
v___x_4950_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4949_);
v___x_4951_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4951_, 0, v___x_4949_);
lean_ctor_set_uint64(v___x_4951_, sizeof(void*)*1, v___x_4950_);
lean_inc(v_canUnfold_x3f_4850_);
lean_inc(v_synthPendingDepth_4849_);
lean_inc(v_defEqCtx_x3f_4848_);
lean_inc_ref(v_localInstances_4847_);
lean_inc_ref(v_lctx_4846_);
lean_inc(v_zetaDeltaSet_4845_);
v___x_4952_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
lean_ctor_set(v___x_4952_, 1, v_zetaDeltaSet_4845_);
lean_ctor_set(v___x_4952_, 2, v_lctx_4846_);
lean_ctor_set(v___x_4952_, 3, v_localInstances_4847_);
lean_ctor_set(v___x_4952_, 4, v_defEqCtx_x3f_4848_);
lean_ctor_set(v___x_4952_, 5, v_synthPendingDepth_4849_);
lean_ctor_set(v___x_4952_, 6, v_canUnfold_x3f_4850_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7, v___x_4807_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7 + 1, v_univApprox_4851_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4852_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7 + 3, v_cacheInferType_4853_);
v___x_4953_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4892_, v_e_4806_, v___x_4891_, v___x_4890_, v_cls_4808_, v___x_4952_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec_ref_known(v___x_4952_, 7);
v___y_4906_ = v___x_4953_;
goto v___jp_4905_;
}
}
}
v___jp_4956_:
{
uint8_t v_foApprox_4958_; uint8_t v_ctxApprox_4959_; uint8_t v_quasiPatternApprox_4960_; uint8_t v_constApprox_4961_; uint8_t v_isDefEqStuckEx_4962_; uint8_t v_unificationHints_4963_; uint8_t v_proofIrrelevance_4964_; uint8_t v_assignSyntheticOpaque_4965_; uint8_t v_offsetCnstrs_4966_; uint8_t v_etaStruct_4967_; uint8_t v_univApprox_4968_; uint8_t v_iota_4969_; uint8_t v_beta_4970_; uint8_t v_proj_4971_; uint8_t v_zeta_4972_; uint8_t v_zetaDelta_4973_; uint8_t v_zetaUnused_4974_; uint8_t v_zetaHave_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_5002_; 
v_foApprox_4958_ = lean_ctor_get_uint8(v___x_4888_, 0);
v_ctxApprox_4959_ = lean_ctor_get_uint8(v___x_4888_, 1);
v_quasiPatternApprox_4960_ = lean_ctor_get_uint8(v___x_4888_, 2);
v_constApprox_4961_ = lean_ctor_get_uint8(v___x_4888_, 3);
v_isDefEqStuckEx_4962_ = lean_ctor_get_uint8(v___x_4888_, 4);
v_unificationHints_4963_ = lean_ctor_get_uint8(v___x_4888_, 5);
v_proofIrrelevance_4964_ = lean_ctor_get_uint8(v___x_4888_, 6);
v_assignSyntheticOpaque_4965_ = lean_ctor_get_uint8(v___x_4888_, 7);
v_offsetCnstrs_4966_ = lean_ctor_get_uint8(v___x_4888_, 8);
v_etaStruct_4967_ = lean_ctor_get_uint8(v___x_4888_, 10);
v_univApprox_4968_ = lean_ctor_get_uint8(v___x_4888_, 11);
v_iota_4969_ = lean_ctor_get_uint8(v___x_4888_, 12);
v_beta_4970_ = lean_ctor_get_uint8(v___x_4888_, 13);
v_proj_4971_ = lean_ctor_get_uint8(v___x_4888_, 14);
v_zeta_4972_ = lean_ctor_get_uint8(v___x_4888_, 15);
v_zetaDelta_4973_ = lean_ctor_get_uint8(v___x_4888_, 16);
v_zetaUnused_4974_ = lean_ctor_get_uint8(v___x_4888_, 17);
v_zetaHave_4975_ = lean_ctor_get_uint8(v___x_4888_, 18);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4977_ = v___x_4888_;
v_isShared_4978_ = v_isSharedCheck_5002_;
goto v_resetjp_4976_;
}
else
{
lean_dec(v___x_4888_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_5002_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v_config_4980_; 
if (v_isShared_4978_ == 0)
{
v_config_4980_ = v___x_4977_;
goto v_reusejp_4979_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 0, v_foApprox_4958_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 1, v_ctxApprox_4959_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 2, v_quasiPatternApprox_4960_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 3, v_constApprox_4961_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 4, v_isDefEqStuckEx_4962_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 5, v_unificationHints_4963_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 6, v_proofIrrelevance_4964_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 7, v_assignSyntheticOpaque_4965_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 8, v_offsetCnstrs_4966_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 10, v_etaStruct_4967_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 11, v_univApprox_4968_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 12, v_iota_4969_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 13, v_beta_4970_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 14, v_proj_4971_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 15, v_zeta_4972_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 16, v_zetaDelta_4973_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 17, v_zetaUnused_4974_);
lean_ctor_set_uint8(v_reuseFailAlloc_5001_, 18, v_zetaHave_4975_);
v_config_4980_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4979_;
}
v_reusejp_4979_:
{
uint64_t v___x_4981_; uint64_t v___x_4982_; uint64_t v___x_4983_; uint64_t v___x_4984_; uint64_t v_key_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; lean_object* v___x_4988_; uint8_t v_beta_4989_; 
lean_ctor_set_uint8(v_config_4980_, 9, v___y_4957_);
v___x_4981_ = l_Lean_Meta_Context_configKey(v___x_4887_);
lean_dec_ref_known(v___x_4887_, 7);
v___x_4982_ = lean_uint64_shift_right(v___x_4981_, v___x_4881_);
v___x_4983_ = lean_uint64_shift_left(v___x_4982_, v___x_4881_);
v___x_4984_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_4957_);
v_key_4985_ = lean_uint64_lor(v___x_4983_, v___x_4984_);
v___x_4986_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4986_, 0, v_config_4980_);
lean_ctor_set_uint64(v___x_4986_, sizeof(void*)*1, v_key_4985_);
lean_inc(v_canUnfold_x3f_4850_);
lean_inc(v_synthPendingDepth_4849_);
lean_inc(v_defEqCtx_x3f_4848_);
lean_inc_ref(v_localInstances_4847_);
lean_inc_ref(v_lctx_4846_);
lean_inc(v_zetaDeltaSet_4845_);
v___x_4987_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4987_, 0, v___x_4986_);
lean_ctor_set(v___x_4987_, 1, v_zetaDeltaSet_4845_);
lean_ctor_set(v___x_4987_, 2, v_lctx_4846_);
lean_ctor_set(v___x_4987_, 3, v_localInstances_4847_);
lean_ctor_set(v___x_4987_, 4, v_defEqCtx_x3f_4848_);
lean_ctor_set(v___x_4987_, 5, v_synthPendingDepth_4849_);
lean_ctor_set(v___x_4987_, 6, v_canUnfold_x3f_4850_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*7, v___x_4807_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*7 + 1, v_univApprox_4851_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4852_);
lean_ctor_set_uint8(v___x_4987_, sizeof(void*)*7 + 3, v_cacheInferType_4853_);
v___x_4988_ = l_Lean_Meta_Context_config(v___x_4987_);
v_beta_4989_ = lean_ctor_get_uint8(v___x_4988_, 13);
if (v_beta_4989_ == 0)
{
lean_dec_ref(v___x_4988_);
v___y_4929_ = v___x_4987_;
goto v___jp_4928_;
}
else
{
uint8_t v_iota_4990_; 
v_iota_4990_ = lean_ctor_get_uint8(v___x_4988_, 12);
if (v_iota_4990_ == 0)
{
lean_dec_ref(v___x_4988_);
v___y_4929_ = v___x_4987_;
goto v___jp_4928_;
}
else
{
uint8_t v_zeta_4991_; 
v_zeta_4991_ = lean_ctor_get_uint8(v___x_4988_, 15);
if (v_zeta_4991_ == 0)
{
lean_dec_ref(v___x_4988_);
v___y_4929_ = v___x_4987_;
goto v___jp_4928_;
}
else
{
uint8_t v_zetaHave_4992_; 
v_zetaHave_4992_ = lean_ctor_get_uint8(v___x_4988_, 18);
if (v_zetaHave_4992_ == 0)
{
lean_dec_ref(v___x_4988_);
v___y_4929_ = v___x_4987_;
goto v___jp_4928_;
}
else
{
uint8_t v_zetaDelta_4993_; 
v_zetaDelta_4993_ = lean_ctor_get_uint8(v___x_4988_, 16);
if (v_zetaDelta_4993_ == 0)
{
lean_dec_ref(v___x_4988_);
v___y_4929_ = v___x_4987_;
goto v___jp_4928_;
}
else
{
uint8_t v_etaStruct_4994_; uint8_t v_proj_4995_; uint8_t v___x_4996_; uint8_t v___x_4997_; 
v_etaStruct_4994_ = lean_ctor_get_uint8(v___x_4988_, 10);
v_proj_4995_ = lean_ctor_get_uint8(v___x_4988_, 14);
lean_dec_ref(v___x_4988_);
v___x_4996_ = 2;
v___x_4997_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_4995_, v___x_4996_);
if (v___x_4997_ == 0)
{
v___y_4929_ = v___x_4987_;
goto v___jp_4928_;
}
else
{
uint8_t v___x_4998_; uint8_t v___x_4999_; 
v___x_4998_ = 0;
v___x_4999_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4994_, v___x_4998_);
if (v___x_4999_ == 0)
{
v___y_4929_ = v___x_4987_;
goto v___jp_4928_;
}
else
{
lean_object* v___x_5000_; 
v___x_5000_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4892_, v_e_4806_, v___x_4891_, v___x_4890_, v_cls_4808_, v___x_4987_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec_ref_known(v___x_4987_, 7);
v___y_4906_ = v___x_5000_;
goto v___jp_4905_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_5012_, lean_object* v_e_5013_, lean_object* v___x_5014_, lean_object* v_cls_5015_, lean_object* v___y_5016_, lean_object* v___y_5017_, lean_object* v___y_5018_, lean_object* v___y_5019_, lean_object* v___y_5020_){
_start:
{
uint8_t v___x_14610__boxed_5021_; uint8_t v___x_14611__boxed_5022_; lean_object* v_res_5023_; 
v___x_14610__boxed_5021_ = lean_unbox(v___x_5012_);
v___x_14611__boxed_5022_ = lean_unbox(v___x_5014_);
v_res_5023_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_14610__boxed_5021_, v_e_5013_, v___x_14611__boxed_5022_, v_cls_5015_, v___y_5016_, v___y_5017_, v___y_5018_, v___y_5019_);
lean_dec(v___y_5019_);
lean_dec_ref(v___y_5018_);
lean_dec(v___y_5017_);
lean_dec_ref(v___y_5016_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5024_, lean_object* v___y_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_){
_start:
{
if (lean_obj_tag(v_x_5024_) == 0)
{
lean_object* v_a_5030_; lean_object* v___x_5032_; uint8_t v_isShared_5033_; uint8_t v_isSharedCheck_5038_; 
v_a_5030_ = lean_ctor_get(v_x_5024_, 0);
v_isSharedCheck_5038_ = !lean_is_exclusive(v_x_5024_);
if (v_isSharedCheck_5038_ == 0)
{
v___x_5032_ = v_x_5024_;
v_isShared_5033_ = v_isSharedCheck_5038_;
goto v_resetjp_5031_;
}
else
{
lean_inc(v_a_5030_);
lean_dec(v_x_5024_);
v___x_5032_ = lean_box(0);
v_isShared_5033_ = v_isSharedCheck_5038_;
goto v_resetjp_5031_;
}
v_resetjp_5031_:
{
lean_object* v___x_5034_; lean_object* v___x_5036_; 
v___x_5034_ = l_Lean_Exception_toMessageData(v_a_5030_);
if (v_isShared_5033_ == 0)
{
lean_ctor_set(v___x_5032_, 0, v___x_5034_);
v___x_5036_ = v___x_5032_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5037_; 
v_reuseFailAlloc_5037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5037_, 0, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5037_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
return v___x_5036_;
}
}
}
else
{
lean_object* v_a_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5047_; 
v_a_5039_ = lean_ctor_get(v_x_5024_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v_x_5024_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5041_ = v_x_5024_;
v_isShared_5042_ = v_isSharedCheck_5047_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_a_5039_);
lean_dec(v_x_5024_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5047_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v_snd_5043_; lean_object* v___x_5045_; 
v_snd_5043_ = lean_ctor_get(v_a_5039_, 1);
lean_inc(v_snd_5043_);
lean_dec(v_a_5039_);
if (v_isShared_5042_ == 0)
{
lean_ctor_set_tag(v___x_5041_, 0);
lean_ctor_set(v___x_5041_, 0, v_snd_5043_);
v___x_5045_ = v___x_5041_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_snd_5043_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5048_, lean_object* v___y_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_, lean_object* v___y_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5048_, v___y_5049_, v___y_5050_, v___y_5051_, v___y_5052_);
lean_dec(v___y_5052_);
lean_dec_ref(v___y_5051_);
lean_dec(v___y_5050_);
lean_dec_ref(v___y_5049_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5055_){
_start:
{
if (lean_obj_tag(v_x_5055_) == 0)
{
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5064_; 
v_a_5057_ = lean_ctor_get(v_x_5055_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v_x_5055_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5059_ = v_x_5055_;
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v_x_5055_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v___x_5062_; 
if (v_isShared_5060_ == 0)
{
lean_ctor_set_tag(v___x_5059_, 1);
v___x_5062_ = v___x_5059_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
else
{
lean_object* v_a_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5072_; 
v_a_5065_ = lean_ctor_get(v_x_5055_, 0);
v_isSharedCheck_5072_ = !lean_is_exclusive(v_x_5055_);
if (v_isSharedCheck_5072_ == 0)
{
v___x_5067_ = v_x_5055_;
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_a_5065_);
lean_dec(v_x_5055_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5072_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
lean_object* v___x_5070_; 
if (v_isShared_5068_ == 0)
{
lean_ctor_set_tag(v___x_5067_, 0);
v___x_5070_ = v___x_5067_;
goto v_reusejp_5069_;
}
else
{
lean_object* v_reuseFailAlloc_5071_; 
v_reuseFailAlloc_5071_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
v___x_5070_ = v_reuseFailAlloc_5071_;
goto v_reusejp_5069_;
}
v_reusejp_5069_:
{
return v___x_5070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5073_, lean_object* v___y_5074_){
_start:
{
lean_object* v_res_5075_; 
v_res_5075_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5073_);
return v_res_5075_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5076_){
_start:
{
if (lean_obj_tag(v_e_5076_) == 0)
{
uint8_t v___x_5077_; 
v___x_5077_ = 2;
return v___x_5077_;
}
else
{
uint8_t v___x_5078_; 
v___x_5078_ = 0;
return v___x_5078_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5079_){
_start:
{
uint8_t v_res_5080_; lean_object* v_r_5081_; 
v_res_5080_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5079_);
lean_dec_ref(v_e_5079_);
v_r_5081_ = lean_box(v_res_5080_);
return v_r_5081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5082_, lean_object* v_data_5083_, lean_object* v_ref_5084_, lean_object* v_msg_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_, lean_object* v___y_5088_, lean_object* v___y_5089_){
_start:
{
lean_object* v_fileName_5091_; lean_object* v_fileMap_5092_; lean_object* v_options_5093_; lean_object* v_currRecDepth_5094_; lean_object* v_maxRecDepth_5095_; lean_object* v_ref_5096_; lean_object* v_currNamespace_5097_; lean_object* v_openDecls_5098_; lean_object* v_initHeartbeats_5099_; lean_object* v_maxHeartbeats_5100_; lean_object* v_quotContext_5101_; lean_object* v_currMacroScope_5102_; uint8_t v_diag_5103_; lean_object* v_cancelTk_x3f_5104_; uint8_t v_suppressElabErrors_5105_; lean_object* v_inheritedTraceOptions_5106_; lean_object* v___x_5107_; lean_object* v_traceState_5108_; lean_object* v_traces_5109_; lean_object* v_ref_5110_; lean_object* v___x_5111_; lean_object* v___x_5112_; size_t v_sz_5113_; size_t v___x_5114_; lean_object* v___x_5115_; lean_object* v_msg_5116_; lean_object* v___x_5117_; lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5155_; 
v_fileName_5091_ = lean_ctor_get(v___y_5088_, 0);
v_fileMap_5092_ = lean_ctor_get(v___y_5088_, 1);
v_options_5093_ = lean_ctor_get(v___y_5088_, 2);
v_currRecDepth_5094_ = lean_ctor_get(v___y_5088_, 3);
v_maxRecDepth_5095_ = lean_ctor_get(v___y_5088_, 4);
v_ref_5096_ = lean_ctor_get(v___y_5088_, 5);
v_currNamespace_5097_ = lean_ctor_get(v___y_5088_, 6);
v_openDecls_5098_ = lean_ctor_get(v___y_5088_, 7);
v_initHeartbeats_5099_ = lean_ctor_get(v___y_5088_, 8);
v_maxHeartbeats_5100_ = lean_ctor_get(v___y_5088_, 9);
v_quotContext_5101_ = lean_ctor_get(v___y_5088_, 10);
v_currMacroScope_5102_ = lean_ctor_get(v___y_5088_, 11);
v_diag_5103_ = lean_ctor_get_uint8(v___y_5088_, sizeof(void*)*14);
v_cancelTk_x3f_5104_ = lean_ctor_get(v___y_5088_, 12);
v_suppressElabErrors_5105_ = lean_ctor_get_uint8(v___y_5088_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5106_ = lean_ctor_get(v___y_5088_, 13);
v___x_5107_ = lean_st_ref_get(v___y_5089_);
v_traceState_5108_ = lean_ctor_get(v___x_5107_, 4);
lean_inc_ref(v_traceState_5108_);
lean_dec(v___x_5107_);
v_traces_5109_ = lean_ctor_get(v_traceState_5108_, 0);
lean_inc_ref(v_traces_5109_);
lean_dec_ref(v_traceState_5108_);
v_ref_5110_ = l_Lean_replaceRef(v_ref_5084_, v_ref_5096_);
lean_inc_ref(v_inheritedTraceOptions_5106_);
lean_inc(v_cancelTk_x3f_5104_);
lean_inc(v_currMacroScope_5102_);
lean_inc(v_quotContext_5101_);
lean_inc(v_maxHeartbeats_5100_);
lean_inc(v_initHeartbeats_5099_);
lean_inc(v_openDecls_5098_);
lean_inc(v_currNamespace_5097_);
lean_inc(v_maxRecDepth_5095_);
lean_inc(v_currRecDepth_5094_);
lean_inc_ref(v_options_5093_);
lean_inc_ref(v_fileMap_5092_);
lean_inc_ref(v_fileName_5091_);
v___x_5111_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5111_, 0, v_fileName_5091_);
lean_ctor_set(v___x_5111_, 1, v_fileMap_5092_);
lean_ctor_set(v___x_5111_, 2, v_options_5093_);
lean_ctor_set(v___x_5111_, 3, v_currRecDepth_5094_);
lean_ctor_set(v___x_5111_, 4, v_maxRecDepth_5095_);
lean_ctor_set(v___x_5111_, 5, v_ref_5110_);
lean_ctor_set(v___x_5111_, 6, v_currNamespace_5097_);
lean_ctor_set(v___x_5111_, 7, v_openDecls_5098_);
lean_ctor_set(v___x_5111_, 8, v_initHeartbeats_5099_);
lean_ctor_set(v___x_5111_, 9, v_maxHeartbeats_5100_);
lean_ctor_set(v___x_5111_, 10, v_quotContext_5101_);
lean_ctor_set(v___x_5111_, 11, v_currMacroScope_5102_);
lean_ctor_set(v___x_5111_, 12, v_cancelTk_x3f_5104_);
lean_ctor_set(v___x_5111_, 13, v_inheritedTraceOptions_5106_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*14, v_diag_5103_);
lean_ctor_set_uint8(v___x_5111_, sizeof(void*)*14 + 1, v_suppressElabErrors_5105_);
v___x_5112_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5109_);
lean_dec_ref(v_traces_5109_);
v_sz_5113_ = lean_array_size(v___x_5112_);
v___x_5114_ = ((size_t)0ULL);
v___x_5115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5113_, v___x_5114_, v___x_5112_);
v_msg_5116_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5116_, 0, v_data_5083_);
lean_ctor_set(v_msg_5116_, 1, v_msg_5085_);
lean_ctor_set(v_msg_5116_, 2, v___x_5115_);
v___x_5117_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5116_, v___y_5086_, v___y_5087_, v___x_5111_, v___y_5089_);
lean_dec_ref_known(v___x_5111_, 14);
v_a_5118_ = lean_ctor_get(v___x_5117_, 0);
v_isSharedCheck_5155_ = !lean_is_exclusive(v___x_5117_);
if (v_isSharedCheck_5155_ == 0)
{
v___x_5120_ = v___x_5117_;
v_isShared_5121_ = v_isSharedCheck_5155_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5117_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5155_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5122_; lean_object* v_traceState_5123_; lean_object* v_env_5124_; lean_object* v_nextMacroScope_5125_; lean_object* v_ngen_5126_; lean_object* v_auxDeclNGen_5127_; lean_object* v_cache_5128_; lean_object* v_messages_5129_; lean_object* v_infoState_5130_; lean_object* v_snapshotTasks_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5154_; 
v___x_5122_ = lean_st_ref_take(v___y_5089_);
v_traceState_5123_ = lean_ctor_get(v___x_5122_, 4);
v_env_5124_ = lean_ctor_get(v___x_5122_, 0);
v_nextMacroScope_5125_ = lean_ctor_get(v___x_5122_, 1);
v_ngen_5126_ = lean_ctor_get(v___x_5122_, 2);
v_auxDeclNGen_5127_ = lean_ctor_get(v___x_5122_, 3);
v_cache_5128_ = lean_ctor_get(v___x_5122_, 5);
v_messages_5129_ = lean_ctor_get(v___x_5122_, 6);
v_infoState_5130_ = lean_ctor_get(v___x_5122_, 7);
v_snapshotTasks_5131_ = lean_ctor_get(v___x_5122_, 8);
v_isSharedCheck_5154_ = !lean_is_exclusive(v___x_5122_);
if (v_isSharedCheck_5154_ == 0)
{
v___x_5133_ = v___x_5122_;
v_isShared_5134_ = v_isSharedCheck_5154_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_snapshotTasks_5131_);
lean_inc(v_infoState_5130_);
lean_inc(v_messages_5129_);
lean_inc(v_cache_5128_);
lean_inc(v_traceState_5123_);
lean_inc(v_auxDeclNGen_5127_);
lean_inc(v_ngen_5126_);
lean_inc(v_nextMacroScope_5125_);
lean_inc(v_env_5124_);
lean_dec(v___x_5122_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5154_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
uint64_t v_tid_5135_; lean_object* v___x_5137_; uint8_t v_isShared_5138_; uint8_t v_isSharedCheck_5152_; 
v_tid_5135_ = lean_ctor_get_uint64(v_traceState_5123_, sizeof(void*)*1);
v_isSharedCheck_5152_ = !lean_is_exclusive(v_traceState_5123_);
if (v_isSharedCheck_5152_ == 0)
{
lean_object* v_unused_5153_; 
v_unused_5153_ = lean_ctor_get(v_traceState_5123_, 0);
lean_dec(v_unused_5153_);
v___x_5137_ = v_traceState_5123_;
v_isShared_5138_ = v_isSharedCheck_5152_;
goto v_resetjp_5136_;
}
else
{
lean_dec(v_traceState_5123_);
v___x_5137_ = lean_box(0);
v_isShared_5138_ = v_isSharedCheck_5152_;
goto v_resetjp_5136_;
}
v_resetjp_5136_:
{
lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v___x_5142_; 
v___x_5139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5139_, 0, v_ref_5084_);
lean_ctor_set(v___x_5139_, 1, v_a_5118_);
v___x_5140_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5082_, v___x_5139_);
if (v_isShared_5138_ == 0)
{
lean_ctor_set(v___x_5137_, 0, v___x_5140_);
v___x_5142_ = v___x_5137_;
goto v_reusejp_5141_;
}
else
{
lean_object* v_reuseFailAlloc_5151_; 
v_reuseFailAlloc_5151_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5151_, 0, v___x_5140_);
lean_ctor_set_uint64(v_reuseFailAlloc_5151_, sizeof(void*)*1, v_tid_5135_);
v___x_5142_ = v_reuseFailAlloc_5151_;
goto v_reusejp_5141_;
}
v_reusejp_5141_:
{
lean_object* v___x_5144_; 
if (v_isShared_5134_ == 0)
{
lean_ctor_set(v___x_5133_, 4, v___x_5142_);
v___x_5144_ = v___x_5133_;
goto v_reusejp_5143_;
}
else
{
lean_object* v_reuseFailAlloc_5150_; 
v_reuseFailAlloc_5150_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5150_, 0, v_env_5124_);
lean_ctor_set(v_reuseFailAlloc_5150_, 1, v_nextMacroScope_5125_);
lean_ctor_set(v_reuseFailAlloc_5150_, 2, v_ngen_5126_);
lean_ctor_set(v_reuseFailAlloc_5150_, 3, v_auxDeclNGen_5127_);
lean_ctor_set(v_reuseFailAlloc_5150_, 4, v___x_5142_);
lean_ctor_set(v_reuseFailAlloc_5150_, 5, v_cache_5128_);
lean_ctor_set(v_reuseFailAlloc_5150_, 6, v_messages_5129_);
lean_ctor_set(v_reuseFailAlloc_5150_, 7, v_infoState_5130_);
lean_ctor_set(v_reuseFailAlloc_5150_, 8, v_snapshotTasks_5131_);
v___x_5144_ = v_reuseFailAlloc_5150_;
goto v_reusejp_5143_;
}
v_reusejp_5143_:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5148_; 
v___x_5145_ = lean_st_ref_set(v___y_5089_, v___x_5144_);
v___x_5146_ = lean_box(0);
if (v_isShared_5121_ == 0)
{
lean_ctor_set(v___x_5120_, 0, v___x_5146_);
v___x_5148_ = v___x_5120_;
goto v_reusejp_5147_;
}
else
{
lean_object* v_reuseFailAlloc_5149_; 
v_reuseFailAlloc_5149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5149_, 0, v___x_5146_);
v___x_5148_ = v_reuseFailAlloc_5149_;
goto v_reusejp_5147_;
}
v_reusejp_5147_:
{
return v___x_5148_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5156_, lean_object* v_data_5157_, lean_object* v_ref_5158_, lean_object* v_msg_5159_, lean_object* v___y_5160_, lean_object* v___y_5161_, lean_object* v___y_5162_, lean_object* v___y_5163_, lean_object* v___y_5164_){
_start:
{
lean_object* v_res_5165_; 
v_res_5165_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5156_, v_data_5157_, v_ref_5158_, v_msg_5159_, v___y_5160_, v___y_5161_, v___y_5162_, v___y_5163_);
lean_dec(v___y_5163_);
lean_dec_ref(v___y_5162_);
lean_dec(v___y_5161_);
lean_dec_ref(v___y_5160_);
return v_res_5165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5166_, uint8_t v_collapsed_5167_, lean_object* v_tag_5168_, lean_object* v_opts_5169_, uint8_t v_clsEnabled_5170_, lean_object* v_oldTraces_5171_, lean_object* v_msg_5172_, lean_object* v_resStartStop_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_, lean_object* v___y_5176_, lean_object* v___y_5177_){
_start:
{
lean_object* v_fst_5179_; lean_object* v_snd_5180_; lean_object* v___y_5182_; lean_object* v___y_5183_; lean_object* v_data_5184_; lean_object* v_fst_5195_; lean_object* v_snd_5196_; lean_object* v___x_5197_; uint8_t v___x_5198_; lean_object* v___y_5200_; lean_object* v_a_5201_; uint8_t v___y_5216_; double v___y_5247_; 
v_fst_5179_ = lean_ctor_get(v_resStartStop_5173_, 0);
lean_inc(v_fst_5179_);
v_snd_5180_ = lean_ctor_get(v_resStartStop_5173_, 1);
lean_inc(v_snd_5180_);
lean_dec_ref(v_resStartStop_5173_);
v_fst_5195_ = lean_ctor_get(v_snd_5180_, 0);
lean_inc(v_fst_5195_);
v_snd_5196_ = lean_ctor_get(v_snd_5180_, 1);
lean_inc(v_snd_5196_);
lean_dec(v_snd_5180_);
v___x_5197_ = l_Lean_trace_profiler;
v___x_5198_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5169_, v___x_5197_);
if (v___x_5198_ == 0)
{
v___y_5216_ = v___x_5198_;
goto v___jp_5215_;
}
else
{
lean_object* v___x_5252_; uint8_t v___x_5253_; 
v___x_5252_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5253_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5169_, v___x_5252_);
if (v___x_5253_ == 0)
{
lean_object* v___x_5254_; lean_object* v___x_5255_; double v___x_5256_; double v___x_5257_; double v___x_5258_; 
v___x_5254_ = l_Lean_trace_profiler_threshold;
v___x_5255_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5169_, v___x_5254_);
v___x_5256_ = lean_float_of_nat(v___x_5255_);
v___x_5257_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5258_ = lean_float_div(v___x_5256_, v___x_5257_);
v___y_5247_ = v___x_5258_;
goto v___jp_5246_;
}
else
{
lean_object* v___x_5259_; lean_object* v___x_5260_; double v___x_5261_; 
v___x_5259_ = l_Lean_trace_profiler_threshold;
v___x_5260_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5169_, v___x_5259_);
v___x_5261_ = lean_float_of_nat(v___x_5260_);
v___y_5247_ = v___x_5261_;
goto v___jp_5246_;
}
}
v___jp_5181_:
{
lean_object* v___x_5185_; 
lean_inc(v___y_5182_);
v___x_5185_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5171_, v_data_5184_, v___y_5182_, v___y_5183_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_);
if (lean_obj_tag(v___x_5185_) == 0)
{
lean_object* v___x_5186_; 
lean_dec_ref_known(v___x_5185_, 1);
v___x_5186_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5179_);
return v___x_5186_;
}
else
{
lean_object* v_a_5187_; lean_object* v___x_5189_; uint8_t v_isShared_5190_; uint8_t v_isSharedCheck_5194_; 
lean_dec(v_fst_5179_);
v_a_5187_ = lean_ctor_get(v___x_5185_, 0);
v_isSharedCheck_5194_ = !lean_is_exclusive(v___x_5185_);
if (v_isSharedCheck_5194_ == 0)
{
v___x_5189_ = v___x_5185_;
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
else
{
lean_inc(v_a_5187_);
lean_dec(v___x_5185_);
v___x_5189_ = lean_box(0);
v_isShared_5190_ = v_isSharedCheck_5194_;
goto v_resetjp_5188_;
}
v_resetjp_5188_:
{
lean_object* v___x_5192_; 
if (v_isShared_5190_ == 0)
{
v___x_5192_ = v___x_5189_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5193_; 
v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
v___x_5192_ = v_reuseFailAlloc_5193_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
return v___x_5192_;
}
}
}
}
v___jp_5199_:
{
uint8_t v_result_5202_; lean_object* v___x_5203_; lean_object* v___x_5204_; double v___x_5205_; lean_object* v_data_5206_; 
v_result_5202_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5179_);
v___x_5203_ = lean_box(v_result_5202_);
v___x_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5203_);
v___x_5205_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5168_);
lean_inc_ref(v___x_5204_);
lean_inc(v_cls_5166_);
v_data_5206_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5206_, 0, v_cls_5166_);
lean_ctor_set(v_data_5206_, 1, v___x_5204_);
lean_ctor_set(v_data_5206_, 2, v_tag_5168_);
lean_ctor_set_float(v_data_5206_, sizeof(void*)*3, v___x_5205_);
lean_ctor_set_float(v_data_5206_, sizeof(void*)*3 + 8, v___x_5205_);
lean_ctor_set_uint8(v_data_5206_, sizeof(void*)*3 + 16, v_collapsed_5167_);
if (v___x_5198_ == 0)
{
lean_dec_ref_known(v___x_5204_, 1);
lean_dec(v_snd_5196_);
lean_dec(v_fst_5195_);
lean_dec_ref(v_tag_5168_);
lean_dec(v_cls_5166_);
v___y_5182_ = v___y_5200_;
v___y_5183_ = v_a_5201_;
v_data_5184_ = v_data_5206_;
goto v___jp_5181_;
}
else
{
lean_object* v_data_5207_; double v___x_5208_; double v___x_5209_; 
lean_dec_ref_known(v_data_5206_, 3);
v_data_5207_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5207_, 0, v_cls_5166_);
lean_ctor_set(v_data_5207_, 1, v___x_5204_);
lean_ctor_set(v_data_5207_, 2, v_tag_5168_);
v___x_5208_ = lean_unbox_float(v_fst_5195_);
lean_dec(v_fst_5195_);
lean_ctor_set_float(v_data_5207_, sizeof(void*)*3, v___x_5208_);
v___x_5209_ = lean_unbox_float(v_snd_5196_);
lean_dec(v_snd_5196_);
lean_ctor_set_float(v_data_5207_, sizeof(void*)*3 + 8, v___x_5209_);
lean_ctor_set_uint8(v_data_5207_, sizeof(void*)*3 + 16, v_collapsed_5167_);
v___y_5182_ = v___y_5200_;
v___y_5183_ = v_a_5201_;
v_data_5184_ = v_data_5207_;
goto v___jp_5181_;
}
}
v___jp_5210_:
{
lean_object* v_ref_5211_; lean_object* v___x_5212_; 
v_ref_5211_ = lean_ctor_get(v___y_5176_, 5);
lean_inc(v___y_5177_);
lean_inc_ref(v___y_5176_);
lean_inc(v___y_5175_);
lean_inc_ref(v___y_5174_);
lean_inc(v_fst_5179_);
v___x_5212_ = lean_apply_6(v_msg_5172_, v_fst_5179_, v___y_5174_, v___y_5175_, v___y_5176_, v___y_5177_, lean_box(0));
if (lean_obj_tag(v___x_5212_) == 0)
{
lean_object* v_a_5213_; 
v_a_5213_ = lean_ctor_get(v___x_5212_, 0);
lean_inc(v_a_5213_);
lean_dec_ref_known(v___x_5212_, 1);
v___y_5200_ = v_ref_5211_;
v_a_5201_ = v_a_5213_;
goto v___jp_5199_;
}
else
{
lean_object* v___x_5214_; 
lean_dec_ref_known(v___x_5212_, 1);
v___x_5214_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5200_ = v_ref_5211_;
v_a_5201_ = v___x_5214_;
goto v___jp_5199_;
}
}
v___jp_5215_:
{
if (v_clsEnabled_5170_ == 0)
{
if (v___y_5216_ == 0)
{
lean_object* v___x_5217_; lean_object* v_traceState_5218_; lean_object* v_env_5219_; lean_object* v_nextMacroScope_5220_; lean_object* v_ngen_5221_; lean_object* v_auxDeclNGen_5222_; lean_object* v_cache_5223_; lean_object* v_messages_5224_; lean_object* v_infoState_5225_; lean_object* v_snapshotTasks_5226_; lean_object* v___x_5228_; uint8_t v_isShared_5229_; uint8_t v_isSharedCheck_5245_; 
lean_dec(v_snd_5196_);
lean_dec(v_fst_5195_);
lean_dec_ref(v_msg_5172_);
lean_dec_ref(v_tag_5168_);
lean_dec(v_cls_5166_);
v___x_5217_ = lean_st_ref_take(v___y_5177_);
v_traceState_5218_ = lean_ctor_get(v___x_5217_, 4);
v_env_5219_ = lean_ctor_get(v___x_5217_, 0);
v_nextMacroScope_5220_ = lean_ctor_get(v___x_5217_, 1);
v_ngen_5221_ = lean_ctor_get(v___x_5217_, 2);
v_auxDeclNGen_5222_ = lean_ctor_get(v___x_5217_, 3);
v_cache_5223_ = lean_ctor_get(v___x_5217_, 5);
v_messages_5224_ = lean_ctor_get(v___x_5217_, 6);
v_infoState_5225_ = lean_ctor_get(v___x_5217_, 7);
v_snapshotTasks_5226_ = lean_ctor_get(v___x_5217_, 8);
v_isSharedCheck_5245_ = !lean_is_exclusive(v___x_5217_);
if (v_isSharedCheck_5245_ == 0)
{
v___x_5228_ = v___x_5217_;
v_isShared_5229_ = v_isSharedCheck_5245_;
goto v_resetjp_5227_;
}
else
{
lean_inc(v_snapshotTasks_5226_);
lean_inc(v_infoState_5225_);
lean_inc(v_messages_5224_);
lean_inc(v_cache_5223_);
lean_inc(v_traceState_5218_);
lean_inc(v_auxDeclNGen_5222_);
lean_inc(v_ngen_5221_);
lean_inc(v_nextMacroScope_5220_);
lean_inc(v_env_5219_);
lean_dec(v___x_5217_);
v___x_5228_ = lean_box(0);
v_isShared_5229_ = v_isSharedCheck_5245_;
goto v_resetjp_5227_;
}
v_resetjp_5227_:
{
uint64_t v_tid_5230_; lean_object* v_traces_5231_; lean_object* v___x_5233_; uint8_t v_isShared_5234_; uint8_t v_isSharedCheck_5244_; 
v_tid_5230_ = lean_ctor_get_uint64(v_traceState_5218_, sizeof(void*)*1);
v_traces_5231_ = lean_ctor_get(v_traceState_5218_, 0);
v_isSharedCheck_5244_ = !lean_is_exclusive(v_traceState_5218_);
if (v_isSharedCheck_5244_ == 0)
{
v___x_5233_ = v_traceState_5218_;
v_isShared_5234_ = v_isSharedCheck_5244_;
goto v_resetjp_5232_;
}
else
{
lean_inc(v_traces_5231_);
lean_dec(v_traceState_5218_);
v___x_5233_ = lean_box(0);
v_isShared_5234_ = v_isSharedCheck_5244_;
goto v_resetjp_5232_;
}
v_resetjp_5232_:
{
lean_object* v___x_5235_; lean_object* v___x_5237_; 
v___x_5235_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5171_, v_traces_5231_);
lean_dec_ref(v_traces_5231_);
if (v_isShared_5234_ == 0)
{
lean_ctor_set(v___x_5233_, 0, v___x_5235_);
v___x_5237_ = v___x_5233_;
goto v_reusejp_5236_;
}
else
{
lean_object* v_reuseFailAlloc_5243_; 
v_reuseFailAlloc_5243_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5243_, 0, v___x_5235_);
lean_ctor_set_uint64(v_reuseFailAlloc_5243_, sizeof(void*)*1, v_tid_5230_);
v___x_5237_ = v_reuseFailAlloc_5243_;
goto v_reusejp_5236_;
}
v_reusejp_5236_:
{
lean_object* v___x_5239_; 
if (v_isShared_5229_ == 0)
{
lean_ctor_set(v___x_5228_, 4, v___x_5237_);
v___x_5239_ = v___x_5228_;
goto v_reusejp_5238_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_env_5219_);
lean_ctor_set(v_reuseFailAlloc_5242_, 1, v_nextMacroScope_5220_);
lean_ctor_set(v_reuseFailAlloc_5242_, 2, v_ngen_5221_);
lean_ctor_set(v_reuseFailAlloc_5242_, 3, v_auxDeclNGen_5222_);
lean_ctor_set(v_reuseFailAlloc_5242_, 4, v___x_5237_);
lean_ctor_set(v_reuseFailAlloc_5242_, 5, v_cache_5223_);
lean_ctor_set(v_reuseFailAlloc_5242_, 6, v_messages_5224_);
lean_ctor_set(v_reuseFailAlloc_5242_, 7, v_infoState_5225_);
lean_ctor_set(v_reuseFailAlloc_5242_, 8, v_snapshotTasks_5226_);
v___x_5239_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5238_;
}
v_reusejp_5238_:
{
lean_object* v___x_5240_; lean_object* v___x_5241_; 
v___x_5240_ = lean_st_ref_set(v___y_5177_, v___x_5239_);
v___x_5241_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5179_);
return v___x_5241_;
}
}
}
}
}
else
{
goto v___jp_5210_;
}
}
else
{
goto v___jp_5210_;
}
}
v___jp_5246_:
{
double v___x_5248_; double v___x_5249_; double v___x_5250_; uint8_t v___x_5251_; 
v___x_5248_ = lean_unbox_float(v_snd_5196_);
v___x_5249_ = lean_unbox_float(v_fst_5195_);
v___x_5250_ = lean_float_sub(v___x_5248_, v___x_5249_);
v___x_5251_ = lean_float_decLt(v___y_5247_, v___x_5250_);
v___y_5216_ = v___x_5251_;
goto v___jp_5215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5262_, lean_object* v_collapsed_5263_, lean_object* v_tag_5264_, lean_object* v_opts_5265_, lean_object* v_clsEnabled_5266_, lean_object* v_oldTraces_5267_, lean_object* v_msg_5268_, lean_object* v_resStartStop_5269_, lean_object* v___y_5270_, lean_object* v___y_5271_, lean_object* v___y_5272_, lean_object* v___y_5273_, lean_object* v___y_5274_){
_start:
{
uint8_t v_collapsed_boxed_5275_; uint8_t v_clsEnabled_boxed_5276_; lean_object* v_res_5277_; 
v_collapsed_boxed_5275_ = lean_unbox(v_collapsed_5263_);
v_clsEnabled_boxed_5276_ = lean_unbox(v_clsEnabled_5266_);
v_res_5277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5262_, v_collapsed_boxed_5275_, v_tag_5264_, v_opts_5265_, v_clsEnabled_boxed_5276_, v_oldTraces_5267_, v_msg_5268_, v_resStartStop_5269_, v___y_5270_, v___y_5271_, v___y_5272_, v___y_5273_);
lean_dec(v___y_5273_);
lean_dec_ref(v___y_5272_);
lean_dec(v___y_5271_);
lean_dec_ref(v___y_5270_);
lean_dec_ref(v_opts_5265_);
return v_res_5277_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5282_; lean_object* v___x_5283_; lean_object* v___x_5284_; 
v_cls_5282_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5283_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5284_ = l_Lean_Name_append(v___x_5283_, v_cls_5282_);
return v___x_5284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_){
_start:
{
lean_object* v___y_5292_; lean_object* v_options_5310_; lean_object* v_inheritedTraceOptions_5311_; uint8_t v_hasTrace_5312_; lean_object* v_cls_5313_; uint8_t v___x_5314_; uint8_t v___x_5315_; uint8_t v___x_5316_; 
v_options_5310_ = lean_ctor_get(v_a_5288_, 2);
v_inheritedTraceOptions_5311_ = lean_ctor_get(v_a_5288_, 13);
v_hasTrace_5312_ = lean_ctor_get_uint8(v_options_5310_, sizeof(void*)*1);
v_cls_5313_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5314_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5285_);
v___x_5315_ = 1;
v___x_5316_ = lean_bool_not(v_hasTrace_5312_);
if (v___x_5316_ == 0)
{
lean_object* v___f_5317_; lean_object* v___x_5318_; uint8_t v___y_5320_; lean_object* v___y_5321_; lean_object* v___y_5322_; lean_object* v_a_5323_; uint8_t v___y_5336_; lean_object* v___y_5337_; lean_object* v___y_5338_; lean_object* v_a_5339_; uint8_t v___y_5349_; uint8_t v_a_5391_; 
v___f_5317_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5318_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
if (v_hasTrace_5312_ == 0)
{
v_a_5391_ = v_hasTrace_5312_;
goto v___jp_5390_;
}
else
{
lean_object* v___x_5395_; uint8_t v___x_5396_; 
v___x_5395_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5396_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5311_, v_options_5310_, v___x_5395_);
if (v___x_5396_ == 0)
{
v_a_5391_ = v___x_5396_;
goto v___jp_5390_;
}
else
{
v___y_5349_ = v___x_5396_;
goto v___jp_5348_;
}
}
v___jp_5319_:
{
lean_object* v___x_5324_; double v___x_5325_; double v___x_5326_; double v___x_5327_; double v___x_5328_; double v___x_5329_; lean_object* v___x_5330_; lean_object* v___x_5331_; lean_object* v___x_5332_; lean_object* v___x_5333_; lean_object* v___x_5334_; 
v___x_5324_ = lean_io_mono_nanos_now();
v___x_5325_ = lean_float_of_nat(v___y_5322_);
v___x_5326_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5327_ = lean_float_div(v___x_5325_, v___x_5326_);
v___x_5328_ = lean_float_of_nat(v___x_5324_);
v___x_5329_ = lean_float_div(v___x_5328_, v___x_5326_);
v___x_5330_ = lean_box_float(v___x_5327_);
v___x_5331_ = lean_box_float(v___x_5329_);
v___x_5332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5330_);
lean_ctor_set(v___x_5332_, 1, v___x_5331_);
v___x_5333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5333_, 0, v_a_5323_);
lean_ctor_set(v___x_5333_, 1, v___x_5332_);
v___x_5334_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5313_, v___x_5315_, v___x_5318_, v_options_5310_, v___y_5320_, v___y_5321_, v___f_5317_, v___x_5333_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
v___y_5292_ = v___x_5334_;
goto v___jp_5291_;
}
v___jp_5335_:
{
lean_object* v___x_5340_; double v___x_5341_; double v___x_5342_; lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___x_5345_; lean_object* v___x_5346_; lean_object* v___x_5347_; 
v___x_5340_ = lean_io_get_num_heartbeats();
v___x_5341_ = lean_float_of_nat(v___y_5338_);
v___x_5342_ = lean_float_of_nat(v___x_5340_);
v___x_5343_ = lean_box_float(v___x_5341_);
v___x_5344_ = lean_box_float(v___x_5342_);
v___x_5345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5345_, 0, v___x_5343_);
lean_ctor_set(v___x_5345_, 1, v___x_5344_);
v___x_5346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5346_, 0, v_a_5339_);
lean_ctor_set(v___x_5346_, 1, v___x_5345_);
v___x_5347_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5313_, v___x_5315_, v___x_5318_, v_options_5310_, v___y_5336_, v___y_5337_, v___f_5317_, v___x_5346_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
v___y_5292_ = v___x_5347_;
goto v___jp_5291_;
}
v___jp_5348_:
{
lean_object* v___x_5350_; lean_object* v_a_5351_; lean_object* v___x_5352_; uint8_t v___x_5353_; 
v___x_5350_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5289_);
v_a_5351_ = lean_ctor_get(v___x_5350_, 0);
lean_inc(v_a_5351_);
lean_dec_ref(v___x_5350_);
v___x_5352_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5353_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5310_, v___x_5352_);
if (v___x_5353_ == 0)
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5354_ = lean_io_mono_nanos_now();
v___x_5355_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5314_, v_e_5285_, v___x_5315_, v_cls_5313_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
if (lean_obj_tag(v___x_5355_) == 0)
{
lean_object* v_a_5356_; lean_object* v___x_5358_; uint8_t v_isShared_5359_; uint8_t v_isSharedCheck_5363_; 
v_a_5356_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5358_ = v___x_5355_;
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
else
{
lean_inc(v_a_5356_);
lean_dec(v___x_5355_);
v___x_5358_ = lean_box(0);
v_isShared_5359_ = v_isSharedCheck_5363_;
goto v_resetjp_5357_;
}
v_resetjp_5357_:
{
lean_object* v___x_5361_; 
if (v_isShared_5359_ == 0)
{
lean_ctor_set_tag(v___x_5358_, 1);
v___x_5361_ = v___x_5358_;
goto v_reusejp_5360_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v_a_5356_);
v___x_5361_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5360_;
}
v_reusejp_5360_:
{
v___y_5320_ = v___y_5349_;
v___y_5321_ = v_a_5351_;
v___y_5322_ = v___x_5354_;
v_a_5323_ = v___x_5361_;
goto v___jp_5319_;
}
}
}
else
{
lean_object* v_a_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5371_; 
v_a_5364_ = lean_ctor_get(v___x_5355_, 0);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5355_);
if (v_isSharedCheck_5371_ == 0)
{
v___x_5366_ = v___x_5355_;
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_a_5364_);
lean_dec(v___x_5355_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5369_; 
if (v_isShared_5367_ == 0)
{
lean_ctor_set_tag(v___x_5366_, 0);
v___x_5369_ = v___x_5366_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_a_5364_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
v___y_5320_ = v___y_5349_;
v___y_5321_ = v_a_5351_;
v___y_5322_ = v___x_5354_;
v_a_5323_ = v___x_5369_;
goto v___jp_5319_;
}
}
}
}
else
{
lean_object* v___x_5372_; lean_object* v___x_5373_; 
v___x_5372_ = lean_io_get_num_heartbeats();
v___x_5373_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5314_, v_e_5285_, v___x_5315_, v_cls_5313_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5381_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5381_ == 0)
{
v___x_5376_ = v___x_5373_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5373_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set_tag(v___x_5376_, 1);
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v_a_5374_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
v___y_5336_ = v___y_5349_;
v___y_5337_ = v_a_5351_;
v___y_5338_ = v___x_5372_;
v_a_5339_ = v___x_5379_;
goto v___jp_5335_;
}
}
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
v_a_5382_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5373_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5373_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
lean_ctor_set_tag(v___x_5384_, 0);
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
v___y_5336_ = v___y_5349_;
v___y_5337_ = v_a_5351_;
v___y_5338_ = v___x_5372_;
v_a_5339_ = v___x_5387_;
goto v___jp_5335_;
}
}
}
}
}
v___jp_5390_:
{
lean_object* v___x_5392_; uint8_t v___x_5393_; 
v___x_5392_ = l_Lean_trace_profiler;
v___x_5393_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5310_, v___x_5392_);
if (v___x_5393_ == 0)
{
lean_object* v___x_5394_; 
v___x_5394_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5314_, v_e_5285_, v___x_5315_, v_cls_5313_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
v___y_5292_ = v___x_5394_;
goto v___jp_5291_;
}
else
{
v___y_5349_ = v_a_5391_;
goto v___jp_5348_;
}
}
}
else
{
lean_object* v___x_5397_; 
v___x_5397_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5314_, v_e_5285_, v___x_5315_, v_cls_5313_, v_a_5286_, v_a_5287_, v_a_5288_, v_a_5289_);
v___y_5292_ = v___x_5397_;
goto v___jp_5291_;
}
v___jp_5291_:
{
if (lean_obj_tag(v___y_5292_) == 0)
{
lean_object* v_a_5293_; lean_object* v___x_5295_; uint8_t v_isShared_5296_; uint8_t v_isSharedCheck_5301_; 
v_a_5293_ = lean_ctor_get(v___y_5292_, 0);
v_isSharedCheck_5301_ = !lean_is_exclusive(v___y_5292_);
if (v_isSharedCheck_5301_ == 0)
{
v___x_5295_ = v___y_5292_;
v_isShared_5296_ = v_isSharedCheck_5301_;
goto v_resetjp_5294_;
}
else
{
lean_inc(v_a_5293_);
lean_dec(v___y_5292_);
v___x_5295_ = lean_box(0);
v_isShared_5296_ = v_isSharedCheck_5301_;
goto v_resetjp_5294_;
}
v_resetjp_5294_:
{
lean_object* v_fst_5297_; lean_object* v___x_5299_; 
v_fst_5297_ = lean_ctor_get(v_a_5293_, 0);
lean_inc(v_fst_5297_);
lean_dec(v_a_5293_);
if (v_isShared_5296_ == 0)
{
lean_ctor_set(v___x_5295_, 0, v_fst_5297_);
v___x_5299_ = v___x_5295_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5300_; 
v_reuseFailAlloc_5300_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_fst_5297_);
v___x_5299_ = v_reuseFailAlloc_5300_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
return v___x_5299_;
}
}
}
else
{
lean_object* v_a_5302_; lean_object* v___x_5304_; uint8_t v_isShared_5305_; uint8_t v_isSharedCheck_5309_; 
v_a_5302_ = lean_ctor_get(v___y_5292_, 0);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___y_5292_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5304_ = v___y_5292_;
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
else
{
lean_inc(v_a_5302_);
lean_dec(v___y_5292_);
v___x_5304_ = lean_box(0);
v_isShared_5305_ = v_isSharedCheck_5309_;
goto v_resetjp_5303_;
}
v_resetjp_5303_:
{
lean_object* v___x_5307_; 
if (v_isShared_5305_ == 0)
{
v___x_5307_ = v___x_5304_;
goto v_reusejp_5306_;
}
else
{
lean_object* v_reuseFailAlloc_5308_; 
v_reuseFailAlloc_5308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5308_, 0, v_a_5302_);
v___x_5307_ = v_reuseFailAlloc_5308_;
goto v_reusejp_5306_;
}
v_reusejp_5306_:
{
return v___x_5307_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5398_, lean_object* v_a_5399_, lean_object* v_a_5400_, lean_object* v_a_5401_, lean_object* v_a_5402_, lean_object* v_a_5403_){
_start:
{
lean_object* v_res_5404_; 
v_res_5404_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5398_, v_a_5399_, v_a_5400_, v_a_5401_, v_a_5402_);
lean_dec(v_a_5402_);
lean_dec_ref(v_a_5401_);
lean_dec(v_a_5400_);
lean_dec_ref(v_a_5399_);
return v_res_5404_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5405_, lean_object* v_x_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___x_5412_; 
v___x_5412_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5406_);
return v___x_5412_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5413_, lean_object* v_x_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5413_, v_x_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
lean_dec(v___y_5418_);
lean_dec_ref(v___y_5417_);
lean_dec(v___y_5416_);
lean_dec_ref(v___y_5415_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5421_, lean_object* v___y_5422_){
_start:
{
uint8_t v___x_5424_; uint8_t v___x_5425_; 
v___x_5424_ = l_Lean_Expr_hasMVar(v_e_5421_);
v___x_5425_ = lean_bool_not(v___x_5424_);
if (v___x_5425_ == 0)
{
lean_object* v___x_5426_; lean_object* v_mctx_5427_; lean_object* v___x_5428_; lean_object* v_fst_5429_; lean_object* v_snd_5430_; lean_object* v___x_5431_; lean_object* v_cache_5432_; lean_object* v_zetaDeltaFVarIds_5433_; lean_object* v_postponed_5434_; lean_object* v_diag_5435_; lean_object* v___x_5437_; uint8_t v_isShared_5438_; uint8_t v_isSharedCheck_5444_; 
v___x_5426_ = lean_st_ref_get(v___y_5422_);
v_mctx_5427_ = lean_ctor_get(v___x_5426_, 0);
lean_inc_ref(v_mctx_5427_);
lean_dec(v___x_5426_);
v___x_5428_ = l_Lean_instantiateMVarsCore(v_mctx_5427_, v_e_5421_);
v_fst_5429_ = lean_ctor_get(v___x_5428_, 0);
lean_inc(v_fst_5429_);
v_snd_5430_ = lean_ctor_get(v___x_5428_, 1);
lean_inc(v_snd_5430_);
lean_dec_ref(v___x_5428_);
v___x_5431_ = lean_st_ref_take(v___y_5422_);
v_cache_5432_ = lean_ctor_get(v___x_5431_, 1);
v_zetaDeltaFVarIds_5433_ = lean_ctor_get(v___x_5431_, 2);
v_postponed_5434_ = lean_ctor_get(v___x_5431_, 3);
v_diag_5435_ = lean_ctor_get(v___x_5431_, 4);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5431_);
if (v_isSharedCheck_5444_ == 0)
{
lean_object* v_unused_5445_; 
v_unused_5445_ = lean_ctor_get(v___x_5431_, 0);
lean_dec(v_unused_5445_);
v___x_5437_ = v___x_5431_;
v_isShared_5438_ = v_isSharedCheck_5444_;
goto v_resetjp_5436_;
}
else
{
lean_inc(v_diag_5435_);
lean_inc(v_postponed_5434_);
lean_inc(v_zetaDeltaFVarIds_5433_);
lean_inc(v_cache_5432_);
lean_dec(v___x_5431_);
v___x_5437_ = lean_box(0);
v_isShared_5438_ = v_isSharedCheck_5444_;
goto v_resetjp_5436_;
}
v_resetjp_5436_:
{
lean_object* v___x_5440_; 
if (v_isShared_5438_ == 0)
{
lean_ctor_set(v___x_5437_, 0, v_snd_5430_);
v___x_5440_ = v___x_5437_;
goto v_reusejp_5439_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_snd_5430_);
lean_ctor_set(v_reuseFailAlloc_5443_, 1, v_cache_5432_);
lean_ctor_set(v_reuseFailAlloc_5443_, 2, v_zetaDeltaFVarIds_5433_);
lean_ctor_set(v_reuseFailAlloc_5443_, 3, v_postponed_5434_);
lean_ctor_set(v_reuseFailAlloc_5443_, 4, v_diag_5435_);
v___x_5440_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5439_;
}
v_reusejp_5439_:
{
lean_object* v___x_5441_; lean_object* v___x_5442_; 
v___x_5441_ = lean_st_ref_set(v___y_5422_, v___x_5440_);
v___x_5442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5442_, 0, v_fst_5429_);
return v___x_5442_;
}
}
}
else
{
lean_object* v___x_5446_; 
v___x_5446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5446_, 0, v_e_5421_);
return v___x_5446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_){
_start:
{
lean_object* v_res_5450_; 
v_res_5450_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5447_, v___y_5448_);
lean_dec(v___y_5448_);
return v_res_5450_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5451_, lean_object* v___y_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_){
_start:
{
lean_object* v___x_5457_; 
v___x_5457_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5451_, v___y_5453_);
return v___x_5457_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_, lean_object* v___y_5461_, lean_object* v___y_5462_, lean_object* v___y_5463_){
_start:
{
lean_object* v_res_5464_; 
v_res_5464_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5458_, v___y_5459_, v___y_5460_, v___y_5461_, v___y_5462_);
lean_dec(v___y_5462_);
lean_dec_ref(v___y_5461_);
lean_dec(v___y_5460_);
lean_dec_ref(v___y_5459_);
return v_res_5464_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5465_, lean_object* v_opts_5466_, lean_object* v_act_5467_, lean_object* v_decl_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_){
_start:
{
lean_object* v___x_5474_; lean_object* v___x_5475_; 
lean_inc(v___y_5472_);
lean_inc_ref(v___y_5471_);
lean_inc(v___y_5470_);
lean_inc_ref(v___y_5469_);
v___x_5474_ = lean_apply_4(v_act_5467_, v___y_5469_, v___y_5470_, v___y_5471_, v___y_5472_);
v___x_5475_ = l_Lean_profileitIOUnsafe___redArg(v_category_5465_, v_opts_5466_, v___x_5474_, v_decl_5468_);
return v___x_5475_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5476_, lean_object* v_opts_5477_, lean_object* v_act_5478_, lean_object* v_decl_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_, lean_object* v___y_5483_, lean_object* v___y_5484_){
_start:
{
lean_object* v_res_5485_; 
v_res_5485_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5476_, v_opts_5477_, v_act_5478_, v_decl_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_);
lean_dec(v___y_5483_);
lean_dec_ref(v___y_5482_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec_ref(v_opts_5477_);
lean_dec_ref(v_category_5476_);
return v_res_5485_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5486_, lean_object* v_category_5487_, lean_object* v_opts_5488_, lean_object* v_act_5489_, lean_object* v_decl_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_, lean_object* v___y_5494_){
_start:
{
lean_object* v___x_5496_; 
v___x_5496_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5487_, v_opts_5488_, v_act_5489_, v_decl_5490_, v___y_5491_, v___y_5492_, v___y_5493_, v___y_5494_);
return v___x_5496_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5497_, lean_object* v_category_5498_, lean_object* v_opts_5499_, lean_object* v_act_5500_, lean_object* v_decl_5501_, lean_object* v___y_5502_, lean_object* v___y_5503_, lean_object* v___y_5504_, lean_object* v___y_5505_, lean_object* v___y_5506_){
_start:
{
lean_object* v_res_5507_; 
v_res_5507_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5497_, v_category_5498_, v_opts_5499_, v_act_5500_, v_decl_5501_, v___y_5502_, v___y_5503_, v___y_5504_, v___y_5505_);
lean_dec(v___y_5505_);
lean_dec_ref(v___y_5504_);
lean_dec(v___y_5503_);
lean_dec_ref(v___y_5502_);
lean_dec_ref(v_opts_5499_);
lean_dec_ref(v_category_5498_);
return v_res_5507_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5508_, uint8_t v_isExporting_5509_, lean_object* v___x_5510_, lean_object* v___y_5511_, lean_object* v___x_5512_, lean_object* v_a_x3f_5513_){
_start:
{
lean_object* v___x_5515_; lean_object* v_env_5516_; lean_object* v_nextMacroScope_5517_; lean_object* v_ngen_5518_; lean_object* v_auxDeclNGen_5519_; lean_object* v_traceState_5520_; lean_object* v_messages_5521_; lean_object* v_infoState_5522_; lean_object* v_snapshotTasks_5523_; lean_object* v___x_5525_; uint8_t v_isShared_5526_; uint8_t v_isSharedCheck_5548_; 
v___x_5515_ = lean_st_ref_take(v___y_5508_);
v_env_5516_ = lean_ctor_get(v___x_5515_, 0);
v_nextMacroScope_5517_ = lean_ctor_get(v___x_5515_, 1);
v_ngen_5518_ = lean_ctor_get(v___x_5515_, 2);
v_auxDeclNGen_5519_ = lean_ctor_get(v___x_5515_, 3);
v_traceState_5520_ = lean_ctor_get(v___x_5515_, 4);
v_messages_5521_ = lean_ctor_get(v___x_5515_, 6);
v_infoState_5522_ = lean_ctor_get(v___x_5515_, 7);
v_snapshotTasks_5523_ = lean_ctor_get(v___x_5515_, 8);
v_isSharedCheck_5548_ = !lean_is_exclusive(v___x_5515_);
if (v_isSharedCheck_5548_ == 0)
{
lean_object* v_unused_5549_; 
v_unused_5549_ = lean_ctor_get(v___x_5515_, 5);
lean_dec(v_unused_5549_);
v___x_5525_ = v___x_5515_;
v_isShared_5526_ = v_isSharedCheck_5548_;
goto v_resetjp_5524_;
}
else
{
lean_inc(v_snapshotTasks_5523_);
lean_inc(v_infoState_5522_);
lean_inc(v_messages_5521_);
lean_inc(v_traceState_5520_);
lean_inc(v_auxDeclNGen_5519_);
lean_inc(v_ngen_5518_);
lean_inc(v_nextMacroScope_5517_);
lean_inc(v_env_5516_);
lean_dec(v___x_5515_);
v___x_5525_ = lean_box(0);
v_isShared_5526_ = v_isSharedCheck_5548_;
goto v_resetjp_5524_;
}
v_resetjp_5524_:
{
lean_object* v___x_5527_; lean_object* v___x_5529_; 
v___x_5527_ = l_Lean_Environment_setExporting(v_env_5516_, v_isExporting_5509_);
if (v_isShared_5526_ == 0)
{
lean_ctor_set(v___x_5525_, 5, v___x_5510_);
lean_ctor_set(v___x_5525_, 0, v___x_5527_);
v___x_5529_ = v___x_5525_;
goto v_reusejp_5528_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_nextMacroScope_5517_);
lean_ctor_set(v_reuseFailAlloc_5547_, 2, v_ngen_5518_);
lean_ctor_set(v_reuseFailAlloc_5547_, 3, v_auxDeclNGen_5519_);
lean_ctor_set(v_reuseFailAlloc_5547_, 4, v_traceState_5520_);
lean_ctor_set(v_reuseFailAlloc_5547_, 5, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5547_, 6, v_messages_5521_);
lean_ctor_set(v_reuseFailAlloc_5547_, 7, v_infoState_5522_);
lean_ctor_set(v_reuseFailAlloc_5547_, 8, v_snapshotTasks_5523_);
v___x_5529_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5528_;
}
v_reusejp_5528_:
{
lean_object* v___x_5530_; lean_object* v___x_5531_; lean_object* v_mctx_5532_; lean_object* v_zetaDeltaFVarIds_5533_; lean_object* v_postponed_5534_; lean_object* v_diag_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5545_; 
v___x_5530_ = lean_st_ref_set(v___y_5508_, v___x_5529_);
v___x_5531_ = lean_st_ref_take(v___y_5511_);
v_mctx_5532_ = lean_ctor_get(v___x_5531_, 0);
v_zetaDeltaFVarIds_5533_ = lean_ctor_get(v___x_5531_, 2);
v_postponed_5534_ = lean_ctor_get(v___x_5531_, 3);
v_diag_5535_ = lean_ctor_get(v___x_5531_, 4);
v_isSharedCheck_5545_ = !lean_is_exclusive(v___x_5531_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; 
v_unused_5546_ = lean_ctor_get(v___x_5531_, 1);
lean_dec(v_unused_5546_);
v___x_5537_ = v___x_5531_;
v_isShared_5538_ = v_isSharedCheck_5545_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_diag_5535_);
lean_inc(v_postponed_5534_);
lean_inc(v_zetaDeltaFVarIds_5533_);
lean_inc(v_mctx_5532_);
lean_dec(v___x_5531_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5545_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5540_; 
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 1, v___x_5512_);
v___x_5540_ = v___x_5537_;
goto v_reusejp_5539_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v_mctx_5532_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v___x_5512_);
lean_ctor_set(v_reuseFailAlloc_5544_, 2, v_zetaDeltaFVarIds_5533_);
lean_ctor_set(v_reuseFailAlloc_5544_, 3, v_postponed_5534_);
lean_ctor_set(v_reuseFailAlloc_5544_, 4, v_diag_5535_);
v___x_5540_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5539_;
}
v_reusejp_5539_:
{
lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; 
v___x_5541_ = lean_st_ref_set(v___y_5511_, v___x_5540_);
v___x_5542_ = lean_box(0);
v___x_5543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5543_, 0, v___x_5542_);
return v___x_5543_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5550_, lean_object* v_isExporting_5551_, lean_object* v___x_5552_, lean_object* v___y_5553_, lean_object* v___x_5554_, lean_object* v_a_x3f_5555_, lean_object* v___y_5556_){
_start:
{
uint8_t v_isExporting_boxed_5557_; lean_object* v_res_5558_; 
v_isExporting_boxed_5557_ = lean_unbox(v_isExporting_5551_);
v_res_5558_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5550_, v_isExporting_boxed_5557_, v___x_5552_, v___y_5553_, v___x_5554_, v_a_x3f_5555_);
lean_dec(v_a_x3f_5555_);
lean_dec(v___y_5553_);
lean_dec(v___y_5550_);
return v_res_5558_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5559_; 
v___x_5559_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5559_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5560_; lean_object* v___x_5561_; 
v___x_5560_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5561_, 0, v___x_5560_);
return v___x_5561_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5562_; lean_object* v___x_5563_; 
v___x_5562_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5563_, 0, v___x_5562_);
lean_ctor_set(v___x_5563_, 1, v___x_5562_);
return v___x_5563_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5564_; lean_object* v___x_5565_; 
v___x_5564_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5565_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5565_, 0, v___x_5564_);
lean_ctor_set(v___x_5565_, 1, v___x_5564_);
lean_ctor_set(v___x_5565_, 2, v___x_5564_);
lean_ctor_set(v___x_5565_, 3, v___x_5564_);
lean_ctor_set(v___x_5565_, 4, v___x_5564_);
lean_ctor_set(v___x_5565_, 5, v___x_5564_);
return v___x_5565_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5566_, uint8_t v_isExporting_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_){
_start:
{
lean_object* v___x_5573_; lean_object* v_env_5574_; uint8_t v_isExporting_5575_; uint8_t v___y_5642_; lean_object* v___x_5644_; uint8_t v_isModule_5645_; uint8_t v___x_5646_; 
v___x_5573_ = lean_st_ref_get(v___y_5571_);
v_env_5574_ = lean_ctor_get(v___x_5573_, 0);
lean_inc_ref(v_env_5574_);
lean_dec(v___x_5573_);
v_isExporting_5575_ = lean_ctor_get_uint8(v_env_5574_, sizeof(void*)*8);
v___x_5644_ = l_Lean_Environment_header(v_env_5574_);
lean_dec_ref(v_env_5574_);
v_isModule_5645_ = lean_ctor_get_uint8(v___x_5644_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5644_);
v___x_5646_ = lean_bool_not(v_isModule_5645_);
if (v___x_5646_ == 0)
{
if (v_isExporting_5575_ == 0)
{
if (v_isExporting_5567_ == 0)
{
lean_object* v___x_5647_; 
lean_inc(v___y_5571_);
lean_inc_ref(v___y_5570_);
lean_inc(v___y_5569_);
lean_inc_ref(v___y_5568_);
v___x_5647_ = lean_apply_5(v_x_5566_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, lean_box(0));
return v___x_5647_;
}
else
{
goto v___jp_5576_;
}
}
else
{
v___y_5642_ = v_isExporting_5567_;
goto v___jp_5641_;
}
}
else
{
v___y_5642_ = v___x_5646_;
goto v___jp_5641_;
}
v___jp_5576_:
{
lean_object* v___x_5577_; lean_object* v_env_5578_; lean_object* v_nextMacroScope_5579_; lean_object* v_ngen_5580_; lean_object* v_auxDeclNGen_5581_; lean_object* v_traceState_5582_; lean_object* v_messages_5583_; lean_object* v_infoState_5584_; lean_object* v_snapshotTasks_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5639_; 
v___x_5577_ = lean_st_ref_take(v___y_5571_);
v_env_5578_ = lean_ctor_get(v___x_5577_, 0);
v_nextMacroScope_5579_ = lean_ctor_get(v___x_5577_, 1);
v_ngen_5580_ = lean_ctor_get(v___x_5577_, 2);
v_auxDeclNGen_5581_ = lean_ctor_get(v___x_5577_, 3);
v_traceState_5582_ = lean_ctor_get(v___x_5577_, 4);
v_messages_5583_ = lean_ctor_get(v___x_5577_, 6);
v_infoState_5584_ = lean_ctor_get(v___x_5577_, 7);
v_snapshotTasks_5585_ = lean_ctor_get(v___x_5577_, 8);
v_isSharedCheck_5639_ = !lean_is_exclusive(v___x_5577_);
if (v_isSharedCheck_5639_ == 0)
{
lean_object* v_unused_5640_; 
v_unused_5640_ = lean_ctor_get(v___x_5577_, 5);
lean_dec(v_unused_5640_);
v___x_5587_ = v___x_5577_;
v_isShared_5588_ = v_isSharedCheck_5639_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_snapshotTasks_5585_);
lean_inc(v_infoState_5584_);
lean_inc(v_messages_5583_);
lean_inc(v_traceState_5582_);
lean_inc(v_auxDeclNGen_5581_);
lean_inc(v_ngen_5580_);
lean_inc(v_nextMacroScope_5579_);
lean_inc(v_env_5578_);
lean_dec(v___x_5577_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5639_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5589_; lean_object* v___x_5590_; lean_object* v___x_5592_; 
v___x_5589_ = l_Lean_Environment_setExporting(v_env_5578_, v_isExporting_5567_);
v___x_5590_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 5, v___x_5590_);
lean_ctor_set(v___x_5587_, 0, v___x_5589_);
v___x_5592_ = v___x_5587_;
goto v_reusejp_5591_;
}
else
{
lean_object* v_reuseFailAlloc_5638_; 
v_reuseFailAlloc_5638_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5638_, 0, v___x_5589_);
lean_ctor_set(v_reuseFailAlloc_5638_, 1, v_nextMacroScope_5579_);
lean_ctor_set(v_reuseFailAlloc_5638_, 2, v_ngen_5580_);
lean_ctor_set(v_reuseFailAlloc_5638_, 3, v_auxDeclNGen_5581_);
lean_ctor_set(v_reuseFailAlloc_5638_, 4, v_traceState_5582_);
lean_ctor_set(v_reuseFailAlloc_5638_, 5, v___x_5590_);
lean_ctor_set(v_reuseFailAlloc_5638_, 6, v_messages_5583_);
lean_ctor_set(v_reuseFailAlloc_5638_, 7, v_infoState_5584_);
lean_ctor_set(v_reuseFailAlloc_5638_, 8, v_snapshotTasks_5585_);
v___x_5592_ = v_reuseFailAlloc_5638_;
goto v_reusejp_5591_;
}
v_reusejp_5591_:
{
lean_object* v___x_5593_; lean_object* v___x_5594_; lean_object* v_mctx_5595_; lean_object* v_zetaDeltaFVarIds_5596_; lean_object* v_postponed_5597_; lean_object* v_diag_5598_; lean_object* v___x_5600_; uint8_t v_isShared_5601_; uint8_t v_isSharedCheck_5636_; 
v___x_5593_ = lean_st_ref_set(v___y_5571_, v___x_5592_);
v___x_5594_ = lean_st_ref_take(v___y_5569_);
v_mctx_5595_ = lean_ctor_get(v___x_5594_, 0);
v_zetaDeltaFVarIds_5596_ = lean_ctor_get(v___x_5594_, 2);
v_postponed_5597_ = lean_ctor_get(v___x_5594_, 3);
v_diag_5598_ = lean_ctor_get(v___x_5594_, 4);
v_isSharedCheck_5636_ = !lean_is_exclusive(v___x_5594_);
if (v_isSharedCheck_5636_ == 0)
{
lean_object* v_unused_5637_; 
v_unused_5637_ = lean_ctor_get(v___x_5594_, 1);
lean_dec(v_unused_5637_);
v___x_5600_ = v___x_5594_;
v_isShared_5601_ = v_isSharedCheck_5636_;
goto v_resetjp_5599_;
}
else
{
lean_inc(v_diag_5598_);
lean_inc(v_postponed_5597_);
lean_inc(v_zetaDeltaFVarIds_5596_);
lean_inc(v_mctx_5595_);
lean_dec(v___x_5594_);
v___x_5600_ = lean_box(0);
v_isShared_5601_ = v_isSharedCheck_5636_;
goto v_resetjp_5599_;
}
v_resetjp_5599_:
{
lean_object* v___x_5602_; lean_object* v___x_5604_; 
v___x_5602_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5601_ == 0)
{
lean_ctor_set(v___x_5600_, 1, v___x_5602_);
v___x_5604_ = v___x_5600_;
goto v_reusejp_5603_;
}
else
{
lean_object* v_reuseFailAlloc_5635_; 
v_reuseFailAlloc_5635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5635_, 0, v_mctx_5595_);
lean_ctor_set(v_reuseFailAlloc_5635_, 1, v___x_5602_);
lean_ctor_set(v_reuseFailAlloc_5635_, 2, v_zetaDeltaFVarIds_5596_);
lean_ctor_set(v_reuseFailAlloc_5635_, 3, v_postponed_5597_);
lean_ctor_set(v_reuseFailAlloc_5635_, 4, v_diag_5598_);
v___x_5604_ = v_reuseFailAlloc_5635_;
goto v_reusejp_5603_;
}
v_reusejp_5603_:
{
lean_object* v___x_5605_; lean_object* v_r_5606_; 
v___x_5605_ = lean_st_ref_set(v___y_5569_, v___x_5604_);
lean_inc(v___y_5571_);
lean_inc_ref(v___y_5570_);
lean_inc(v___y_5569_);
lean_inc_ref(v___y_5568_);
v_r_5606_ = lean_apply_5(v_x_5566_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, lean_box(0));
if (lean_obj_tag(v_r_5606_) == 0)
{
lean_object* v_a_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5623_; 
v_a_5607_ = lean_ctor_get(v_r_5606_, 0);
v_isSharedCheck_5623_ = !lean_is_exclusive(v_r_5606_);
if (v_isSharedCheck_5623_ == 0)
{
v___x_5609_ = v_r_5606_;
v_isShared_5610_ = v_isSharedCheck_5623_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_a_5607_);
lean_dec(v_r_5606_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5623_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5612_; 
lean_inc(v_a_5607_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set_tag(v___x_5609_, 1);
v___x_5612_ = v___x_5609_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v_a_5607_);
v___x_5612_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
lean_object* v___x_5613_; lean_object* v___x_5615_; uint8_t v_isShared_5616_; uint8_t v_isSharedCheck_5620_; 
v___x_5613_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5571_, v_isExporting_5575_, v___x_5590_, v___y_5569_, v___x_5602_, v___x_5612_);
lean_dec_ref(v___x_5612_);
v_isSharedCheck_5620_ = !lean_is_exclusive(v___x_5613_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; 
v_unused_5621_ = lean_ctor_get(v___x_5613_, 0);
lean_dec(v_unused_5621_);
v___x_5615_ = v___x_5613_;
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
else
{
lean_dec(v___x_5613_);
v___x_5615_ = lean_box(0);
v_isShared_5616_ = v_isSharedCheck_5620_;
goto v_resetjp_5614_;
}
v_resetjp_5614_:
{
lean_object* v___x_5618_; 
if (v_isShared_5616_ == 0)
{
lean_ctor_set(v___x_5615_, 0, v_a_5607_);
v___x_5618_ = v___x_5615_;
goto v_reusejp_5617_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v_a_5607_);
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
}
else
{
lean_object* v_a_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5628_; uint8_t v_isShared_5629_; uint8_t v_isSharedCheck_5633_; 
v_a_5624_ = lean_ctor_get(v_r_5606_, 0);
lean_inc(v_a_5624_);
lean_dec_ref_known(v_r_5606_, 1);
v___x_5625_ = lean_box(0);
v___x_5626_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5571_, v_isExporting_5575_, v___x_5590_, v___y_5569_, v___x_5602_, v___x_5625_);
v_isSharedCheck_5633_ = !lean_is_exclusive(v___x_5626_);
if (v_isSharedCheck_5633_ == 0)
{
lean_object* v_unused_5634_; 
v_unused_5634_ = lean_ctor_get(v___x_5626_, 0);
lean_dec(v_unused_5634_);
v___x_5628_ = v___x_5626_;
v_isShared_5629_ = v_isSharedCheck_5633_;
goto v_resetjp_5627_;
}
else
{
lean_dec(v___x_5626_);
v___x_5628_ = lean_box(0);
v_isShared_5629_ = v_isSharedCheck_5633_;
goto v_resetjp_5627_;
}
v_resetjp_5627_:
{
lean_object* v___x_5631_; 
if (v_isShared_5629_ == 0)
{
lean_ctor_set_tag(v___x_5628_, 1);
lean_ctor_set(v___x_5628_, 0, v_a_5624_);
v___x_5631_ = v___x_5628_;
goto v_reusejp_5630_;
}
else
{
lean_object* v_reuseFailAlloc_5632_; 
v_reuseFailAlloc_5632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5632_, 0, v_a_5624_);
v___x_5631_ = v_reuseFailAlloc_5632_;
goto v_reusejp_5630_;
}
v_reusejp_5630_:
{
return v___x_5631_;
}
}
}
}
}
}
}
}
v___jp_5641_:
{
if (v___y_5642_ == 0)
{
goto v___jp_5576_;
}
else
{
lean_object* v___x_5643_; 
lean_inc(v___y_5571_);
lean_inc_ref(v___y_5570_);
lean_inc(v___y_5569_);
lean_inc_ref(v___y_5568_);
v___x_5643_ = lean_apply_5(v_x_5566_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_, lean_box(0));
return v___x_5643_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5648_, lean_object* v_isExporting_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_){
_start:
{
uint8_t v_isExporting_boxed_5655_; lean_object* v_res_5656_; 
v_isExporting_boxed_5655_ = lean_unbox(v_isExporting_5649_);
v_res_5656_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5648_, v_isExporting_boxed_5655_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec(v___y_5651_);
lean_dec_ref(v___y_5650_);
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5657_, uint8_t v_when_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_){
_start:
{
if (v_when_5658_ == 0)
{
lean_object* v___x_5664_; 
lean_inc(v___y_5662_);
lean_inc_ref(v___y_5661_);
lean_inc(v___y_5660_);
lean_inc_ref(v___y_5659_);
v___x_5664_ = lean_apply_5(v_x_5657_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_, lean_box(0));
return v___x_5664_;
}
else
{
uint8_t v___x_5665_; lean_object* v___x_5666_; 
v___x_5665_ = 0;
v___x_5666_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5657_, v___x_5665_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
return v___x_5666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5667_, lean_object* v_when_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
uint8_t v_when_boxed_5674_; lean_object* v_res_5675_; 
v_when_boxed_5674_ = lean_unbox(v_when_5668_);
v_res_5675_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5667_, v_when_boxed_5674_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
return v_res_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_){
_start:
{
lean_object* v___x_5682_; lean_object* v_a_5683_; lean_object* v___x_5684_; uint8_t v___x_5685_; lean_object* v___x_5686_; 
v___x_5682_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5676_, v___y_5678_);
v_a_5683_ = lean_ctor_get(v___x_5682_, 0);
lean_inc(v_a_5683_);
lean_dec_ref(v___x_5682_);
v___x_5684_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5684_, 0, v_a_5683_);
v___x_5685_ = 1;
v___x_5686_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5684_, v___x_5685_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
return v___x_5686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
lean_object* v_res_5693_; 
v_res_5693_ = l_Lean_Meta_letToHave___lam__0(v_e_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
lean_dec(v___y_5691_);
lean_dec_ref(v___y_5690_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
return v_res_5693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5695_, lean_object* v_a_5696_, lean_object* v_a_5697_, lean_object* v_a_5698_, lean_object* v_a_5699_){
_start:
{
lean_object* v_options_5701_; lean_object* v___f_5702_; lean_object* v___x_5703_; lean_object* v___x_5704_; lean_object* v___x_5705_; 
v_options_5701_ = lean_ctor_get(v_a_5698_, 2);
v___f_5702_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5702_, 0, v_e_5695_);
v___x_5703_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5704_ = lean_box(0);
v___x_5705_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5703_, v_options_5701_, v___f_5702_, v___x_5704_, v_a_5696_, v_a_5697_, v_a_5698_, v_a_5699_);
return v___x_5705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5706_, lean_object* v_a_5707_, lean_object* v_a_5708_, lean_object* v_a_5709_, lean_object* v_a_5710_, lean_object* v_a_5711_){
_start:
{
lean_object* v_res_5712_; 
v_res_5712_ = l_Lean_Meta_letToHave(v_e_5706_, v_a_5707_, v_a_5708_, v_a_5709_, v_a_5710_);
lean_dec(v_a_5710_);
lean_dec_ref(v_a_5709_);
lean_dec(v_a_5708_);
lean_dec_ref(v_a_5707_);
return v_res_5712_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5713_, lean_object* v_x_5714_, uint8_t v_isExporting_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_){
_start:
{
lean_object* v___x_5721_; 
v___x_5721_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5714_, v_isExporting_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
return v___x_5721_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5722_, lean_object* v_x_5723_, lean_object* v_isExporting_5724_, lean_object* v___y_5725_, lean_object* v___y_5726_, lean_object* v___y_5727_, lean_object* v___y_5728_, lean_object* v___y_5729_){
_start:
{
uint8_t v_isExporting_boxed_5730_; lean_object* v_res_5731_; 
v_isExporting_boxed_5730_ = lean_unbox(v_isExporting_5724_);
v_res_5731_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5722_, v_x_5723_, v_isExporting_boxed_5730_, v___y_5725_, v___y_5726_, v___y_5727_, v___y_5728_);
lean_dec(v___y_5728_);
lean_dec_ref(v___y_5727_);
lean_dec(v___y_5726_);
lean_dec_ref(v___y_5725_);
return v_res_5731_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5732_, lean_object* v_x_5733_, uint8_t v_when_5734_, lean_object* v___y_5735_, lean_object* v___y_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_){
_start:
{
lean_object* v___x_5740_; 
v___x_5740_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5733_, v_when_5734_, v___y_5735_, v___y_5736_, v___y_5737_, v___y_5738_);
return v___x_5740_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5741_, lean_object* v_x_5742_, lean_object* v_when_5743_, lean_object* v___y_5744_, lean_object* v___y_5745_, lean_object* v___y_5746_, lean_object* v___y_5747_, lean_object* v___y_5748_){
_start:
{
uint8_t v_when_boxed_5749_; lean_object* v_res_5750_; 
v_when_boxed_5749_ = lean_unbox(v_when_5743_);
v_res_5750_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5741_, v_x_5742_, v_when_boxed_5749_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_);
lean_dec(v___y_5747_);
lean_dec_ref(v___y_5746_);
lean_dec(v___y_5745_);
lean_dec_ref(v___y_5744_);
return v_res_5750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5807_; uint8_t v___x_5808_; lean_object* v___x_5809_; lean_object* v___x_5810_; 
v___x_5807_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5808_ = 0;
v___x_5809_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5810_ = l_Lean_registerTraceClass(v___x_5807_, v___x_5808_, v___x_5809_);
if (lean_obj_tag(v___x_5810_) == 0)
{
lean_object* v___x_5811_; lean_object* v___x_5812_; 
lean_dec_ref_known(v___x_5810_, 1);
v___x_5811_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5812_ = l_Lean_registerTraceClass(v___x_5811_, v___x_5808_, v___x_5809_);
return v___x_5812_;
}
else
{
return v___x_5810_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5813_){
_start:
{
lean_object* v_res_5814_; 
v_res_5814_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5814_;
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
