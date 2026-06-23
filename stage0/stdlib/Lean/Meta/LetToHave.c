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
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_735_ = lean_box(0);
v___x_736_ = lean_unsigned_to_nat(16u);
v___x_737_ = lean_mk_array(v___x_736_, v___x_735_);
return v___x_737_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_738_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0);
v___x_739_ = lean_unsigned_to_nat(0u);
v___x_740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_739_);
lean_ctor_set(v___x_740_, 1, v___x_738_);
return v___x_740_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_743_; lean_object* v_visited_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_743_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2));
v_visited_744_ = lean_box(1);
v___x_745_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_746_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_745_);
lean_ctor_set(v___x_746_, 1, v_visited_744_);
lean_ctor_set(v___x_746_, 2, v___x_743_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object* v_a_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
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
v___x_769_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object* v_a_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
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
v___x_825_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v___x_824_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_inst_887_, lean_object* v_a_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v___x_896_; 
v___x_896_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_inst_897_, lean_object* v_a_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_inst_897_, v_a_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
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
v___x_1886_ = lean_unsigned_to_nat(1849u);
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
v___x_2689_ = lean_unsigned_to_nat(1898u);
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3107_){
_start:
{
if (lean_obj_tag(v_x_3107_) == 0)
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v_x_3107_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_x_3107_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v_x_3107_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v_x_3107_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set_tag(v___x_3111_, 1);
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3115_, 0, v_a_3109_);
v___x_3114_ = v_reuseFailAlloc_3115_;
goto v_reusejp_3113_;
}
v_reusejp_3113_:
{
return v___x_3114_;
}
}
}
else
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
v_a_3117_ = lean_ctor_get(v_x_3107_, 0);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_x_3107_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3119_ = v_x_3107_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v_x_3107_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set_tag(v___x_3119_, 0);
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3117_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3125_, lean_object* v___y_3126_){
_start:
{
lean_object* v_res_3127_; 
v_res_3127_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3125_);
return v_res_3127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3128_, lean_object* v_opt_3129_){
_start:
{
lean_object* v_name_3130_; lean_object* v_defValue_3131_; lean_object* v_map_3132_; lean_object* v___x_3133_; 
v_name_3130_ = lean_ctor_get(v_opt_3129_, 0);
v_defValue_3131_ = lean_ctor_get(v_opt_3129_, 1);
v_map_3132_ = lean_ctor_get(v_opts_3128_, 0);
v___x_3133_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3132_, v_name_3130_);
if (lean_obj_tag(v___x_3133_) == 0)
{
lean_inc(v_defValue_3131_);
return v_defValue_3131_;
}
else
{
lean_object* v_val_3134_; 
v_val_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc(v_val_3134_);
lean_dec_ref_known(v___x_3133_, 1);
if (lean_obj_tag(v_val_3134_) == 3)
{
lean_object* v_v_3135_; 
v_v_3135_ = lean_ctor_get(v_val_3134_, 0);
lean_inc(v_v_3135_);
lean_dec_ref_known(v_val_3134_, 1);
return v_v_3135_;
}
else
{
lean_dec(v_val_3134_);
lean_inc(v_defValue_3131_);
return v_defValue_3131_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3136_, lean_object* v_opt_3137_){
_start:
{
lean_object* v_res_3138_; 
v_res_3138_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3136_, v_opt_3137_);
lean_dec_ref(v_opt_3137_);
lean_dec_ref(v_opts_3136_);
return v_res_3138_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3139_){
_start:
{
if (lean_obj_tag(v_e_3139_) == 0)
{
uint8_t v___x_3140_; 
v___x_3140_ = 2;
return v___x_3140_;
}
else
{
uint8_t v___x_3141_; 
v___x_3141_ = 0;
return v___x_3141_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3142_){
_start:
{
uint8_t v_res_3143_; lean_object* v_r_3144_; 
v_res_3143_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3142_);
lean_dec_ref(v_e_3142_);
v_r_3144_ = lean_box(v_res_3143_);
return v_r_3144_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3145_, size_t v_i_3146_, lean_object* v_bs_3147_){
_start:
{
uint8_t v___x_3148_; 
v___x_3148_ = lean_usize_dec_lt(v_i_3146_, v_sz_3145_);
if (v___x_3148_ == 0)
{
return v_bs_3147_;
}
else
{
lean_object* v_v_3149_; lean_object* v_msg_3150_; lean_object* v___x_3151_; lean_object* v_bs_x27_3152_; size_t v___x_3153_; size_t v___x_3154_; lean_object* v___x_3155_; 
v_v_3149_ = lean_array_uget_borrowed(v_bs_3147_, v_i_3146_);
v_msg_3150_ = lean_ctor_get(v_v_3149_, 1);
lean_inc_ref(v_msg_3150_);
v___x_3151_ = lean_unsigned_to_nat(0u);
v_bs_x27_3152_ = lean_array_uset(v_bs_3147_, v_i_3146_, v___x_3151_);
v___x_3153_ = ((size_t)1ULL);
v___x_3154_ = lean_usize_add(v_i_3146_, v___x_3153_);
v___x_3155_ = lean_array_uset(v_bs_x27_3152_, v_i_3146_, v_msg_3150_);
v_i_3146_ = v___x_3154_;
v_bs_3147_ = v___x_3155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3157_, lean_object* v_i_3158_, lean_object* v_bs_3159_){
_start:
{
size_t v_sz_boxed_3160_; size_t v_i_boxed_3161_; lean_object* v_res_3162_; 
v_sz_boxed_3160_ = lean_unbox_usize(v_sz_3157_);
lean_dec(v_sz_3157_);
v_i_boxed_3161_ = lean_unbox_usize(v_i_3158_);
lean_dec(v_i_3158_);
v_res_3162_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3160_, v_i_boxed_3161_, v_bs_3159_);
return v_res_3162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3163_, lean_object* v_data_3164_, lean_object* v_ref_3165_, lean_object* v_msg_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_){
_start:
{
lean_object* v_fileName_3172_; lean_object* v_fileMap_3173_; lean_object* v_options_3174_; lean_object* v_currRecDepth_3175_; lean_object* v_maxRecDepth_3176_; lean_object* v_ref_3177_; lean_object* v_currNamespace_3178_; lean_object* v_openDecls_3179_; lean_object* v_initHeartbeats_3180_; lean_object* v_maxHeartbeats_3181_; lean_object* v_quotContext_3182_; lean_object* v_currMacroScope_3183_; uint8_t v_diag_3184_; lean_object* v_cancelTk_x3f_3185_; uint8_t v_suppressElabErrors_3186_; lean_object* v_inheritedTraceOptions_3187_; lean_object* v___x_3188_; lean_object* v_traceState_3189_; lean_object* v_traces_3190_; lean_object* v_ref_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; size_t v_sz_3194_; size_t v___x_3195_; lean_object* v___x_3196_; lean_object* v_msg_3197_; lean_object* v___x_3198_; lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3236_; 
v_fileName_3172_ = lean_ctor_get(v___y_3169_, 0);
v_fileMap_3173_ = lean_ctor_get(v___y_3169_, 1);
v_options_3174_ = lean_ctor_get(v___y_3169_, 2);
v_currRecDepth_3175_ = lean_ctor_get(v___y_3169_, 3);
v_maxRecDepth_3176_ = lean_ctor_get(v___y_3169_, 4);
v_ref_3177_ = lean_ctor_get(v___y_3169_, 5);
v_currNamespace_3178_ = lean_ctor_get(v___y_3169_, 6);
v_openDecls_3179_ = lean_ctor_get(v___y_3169_, 7);
v_initHeartbeats_3180_ = lean_ctor_get(v___y_3169_, 8);
v_maxHeartbeats_3181_ = lean_ctor_get(v___y_3169_, 9);
v_quotContext_3182_ = lean_ctor_get(v___y_3169_, 10);
v_currMacroScope_3183_ = lean_ctor_get(v___y_3169_, 11);
v_diag_3184_ = lean_ctor_get_uint8(v___y_3169_, sizeof(void*)*14);
v_cancelTk_x3f_3185_ = lean_ctor_get(v___y_3169_, 12);
v_suppressElabErrors_3186_ = lean_ctor_get_uint8(v___y_3169_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3187_ = lean_ctor_get(v___y_3169_, 13);
v___x_3188_ = lean_st_ref_get(v___y_3170_);
v_traceState_3189_ = lean_ctor_get(v___x_3188_, 4);
lean_inc_ref(v_traceState_3189_);
lean_dec(v___x_3188_);
v_traces_3190_ = lean_ctor_get(v_traceState_3189_, 0);
lean_inc_ref(v_traces_3190_);
lean_dec_ref(v_traceState_3189_);
v_ref_3191_ = l_Lean_replaceRef(v_ref_3165_, v_ref_3177_);
lean_inc_ref(v_inheritedTraceOptions_3187_);
lean_inc(v_cancelTk_x3f_3185_);
lean_inc(v_currMacroScope_3183_);
lean_inc(v_quotContext_3182_);
lean_inc(v_maxHeartbeats_3181_);
lean_inc(v_initHeartbeats_3180_);
lean_inc(v_openDecls_3179_);
lean_inc(v_currNamespace_3178_);
lean_inc(v_maxRecDepth_3176_);
lean_inc(v_currRecDepth_3175_);
lean_inc_ref(v_options_3174_);
lean_inc_ref(v_fileMap_3173_);
lean_inc_ref(v_fileName_3172_);
v___x_3192_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3192_, 0, v_fileName_3172_);
lean_ctor_set(v___x_3192_, 1, v_fileMap_3173_);
lean_ctor_set(v___x_3192_, 2, v_options_3174_);
lean_ctor_set(v___x_3192_, 3, v_currRecDepth_3175_);
lean_ctor_set(v___x_3192_, 4, v_maxRecDepth_3176_);
lean_ctor_set(v___x_3192_, 5, v_ref_3191_);
lean_ctor_set(v___x_3192_, 6, v_currNamespace_3178_);
lean_ctor_set(v___x_3192_, 7, v_openDecls_3179_);
lean_ctor_set(v___x_3192_, 8, v_initHeartbeats_3180_);
lean_ctor_set(v___x_3192_, 9, v_maxHeartbeats_3181_);
lean_ctor_set(v___x_3192_, 10, v_quotContext_3182_);
lean_ctor_set(v___x_3192_, 11, v_currMacroScope_3183_);
lean_ctor_set(v___x_3192_, 12, v_cancelTk_x3f_3185_);
lean_ctor_set(v___x_3192_, 13, v_inheritedTraceOptions_3187_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*14, v_diag_3184_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*14 + 1, v_suppressElabErrors_3186_);
v___x_3193_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3190_);
lean_dec_ref(v_traces_3190_);
v_sz_3194_ = lean_array_size(v___x_3193_);
v___x_3195_ = ((size_t)0ULL);
v___x_3196_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3194_, v___x_3195_, v___x_3193_);
v_msg_3197_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3197_, 0, v_data_3164_);
lean_ctor_set(v_msg_3197_, 1, v_msg_3166_);
lean_ctor_set(v_msg_3197_, 2, v___x_3196_);
v___x_3198_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3197_, v___y_3167_, v___y_3168_, v___x_3192_, v___y_3170_);
lean_dec_ref_known(v___x_3192_, 14);
v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v___x_3198_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3201_ = v___x_3198_;
v_isShared_3202_ = v_isSharedCheck_3236_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___x_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3236_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v___x_3203_; lean_object* v_traceState_3204_; lean_object* v_env_3205_; lean_object* v_nextMacroScope_3206_; lean_object* v_ngen_3207_; lean_object* v_auxDeclNGen_3208_; lean_object* v_cache_3209_; lean_object* v_messages_3210_; lean_object* v_infoState_3211_; lean_object* v_snapshotTasks_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3235_; 
v___x_3203_ = lean_st_ref_take(v___y_3170_);
v_traceState_3204_ = lean_ctor_get(v___x_3203_, 4);
v_env_3205_ = lean_ctor_get(v___x_3203_, 0);
v_nextMacroScope_3206_ = lean_ctor_get(v___x_3203_, 1);
v_ngen_3207_ = lean_ctor_get(v___x_3203_, 2);
v_auxDeclNGen_3208_ = lean_ctor_get(v___x_3203_, 3);
v_cache_3209_ = lean_ctor_get(v___x_3203_, 5);
v_messages_3210_ = lean_ctor_get(v___x_3203_, 6);
v_infoState_3211_ = lean_ctor_get(v___x_3203_, 7);
v_snapshotTasks_3212_ = lean_ctor_get(v___x_3203_, 8);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3214_ = v___x_3203_;
v_isShared_3215_ = v_isSharedCheck_3235_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_snapshotTasks_3212_);
lean_inc(v_infoState_3211_);
lean_inc(v_messages_3210_);
lean_inc(v_cache_3209_);
lean_inc(v_traceState_3204_);
lean_inc(v_auxDeclNGen_3208_);
lean_inc(v_ngen_3207_);
lean_inc(v_nextMacroScope_3206_);
lean_inc(v_env_3205_);
lean_dec(v___x_3203_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3235_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint64_t v_tid_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3233_; 
v_tid_3216_ = lean_ctor_get_uint64(v_traceState_3204_, sizeof(void*)*1);
v_isSharedCheck_3233_ = !lean_is_exclusive(v_traceState_3204_);
if (v_isSharedCheck_3233_ == 0)
{
lean_object* v_unused_3234_; 
v_unused_3234_ = lean_ctor_get(v_traceState_3204_, 0);
lean_dec(v_unused_3234_);
v___x_3218_ = v_traceState_3204_;
v_isShared_3219_ = v_isSharedCheck_3233_;
goto v_resetjp_3217_;
}
else
{
lean_dec(v_traceState_3204_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3233_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3223_; 
v___x_3220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3220_, 0, v_ref_3165_);
lean_ctor_set(v___x_3220_, 1, v_a_3199_);
v___x_3221_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3163_, v___x_3220_);
if (v_isShared_3219_ == 0)
{
lean_ctor_set(v___x_3218_, 0, v___x_3221_);
v___x_3223_ = v___x_3218_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3221_);
lean_ctor_set_uint64(v_reuseFailAlloc_3232_, sizeof(void*)*1, v_tid_3216_);
v___x_3223_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3225_; 
if (v_isShared_3215_ == 0)
{
lean_ctor_set(v___x_3214_, 4, v___x_3223_);
v___x_3225_ = v___x_3214_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_env_3205_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v_nextMacroScope_3206_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_ngen_3207_);
lean_ctor_set(v_reuseFailAlloc_3231_, 3, v_auxDeclNGen_3208_);
lean_ctor_set(v_reuseFailAlloc_3231_, 4, v___x_3223_);
lean_ctor_set(v_reuseFailAlloc_3231_, 5, v_cache_3209_);
lean_ctor_set(v_reuseFailAlloc_3231_, 6, v_messages_3210_);
lean_ctor_set(v_reuseFailAlloc_3231_, 7, v_infoState_3211_);
lean_ctor_set(v_reuseFailAlloc_3231_, 8, v_snapshotTasks_3212_);
v___x_3225_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3226_ = lean_st_ref_set(v___y_3170_, v___x_3225_);
v___x_3227_ = lean_box(0);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v___x_3227_);
v___x_3229_ = v___x_3201_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3230_; 
v_reuseFailAlloc_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3230_, 0, v___x_3227_);
v___x_3229_ = v_reuseFailAlloc_3230_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
return v___x_3229_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3237_, lean_object* v_data_3238_, lean_object* v_ref_3239_, lean_object* v_msg_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3237_, v_data_3238_, v_ref_3239_, v_msg_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
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
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3250_; double v___x_3251_; 
v___x_3250_ = lean_unsigned_to_nat(1000u);
v___x_3251_ = lean_float_of_nat(v___x_3250_);
return v___x_3251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3252_, uint8_t v_collapsed_3253_, lean_object* v_tag_3254_, lean_object* v_opts_3255_, uint8_t v_clsEnabled_3256_, lean_object* v_oldTraces_3257_, lean_object* v_msg_3258_, lean_object* v_resStartStop_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_fst_3267_; lean_object* v_snd_3268_; lean_object* v___y_3270_; lean_object* v___y_3271_; lean_object* v_data_3272_; lean_object* v_fst_3283_; lean_object* v_snd_3284_; lean_object* v___x_3285_; uint8_t v___x_3286_; lean_object* v___y_3288_; lean_object* v_a_3289_; uint8_t v___y_3304_; double v___y_3335_; 
v_fst_3267_ = lean_ctor_get(v_resStartStop_3259_, 0);
lean_inc(v_fst_3267_);
v_snd_3268_ = lean_ctor_get(v_resStartStop_3259_, 1);
lean_inc(v_snd_3268_);
lean_dec_ref(v_resStartStop_3259_);
v_fst_3283_ = lean_ctor_get(v_snd_3268_, 0);
lean_inc(v_fst_3283_);
v_snd_3284_ = lean_ctor_get(v_snd_3268_, 1);
lean_inc(v_snd_3284_);
lean_dec(v_snd_3268_);
v___x_3285_ = l_Lean_trace_profiler;
v___x_3286_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3255_, v___x_3285_);
if (v___x_3286_ == 0)
{
v___y_3304_ = v___x_3286_;
goto v___jp_3303_;
}
else
{
lean_object* v___x_3340_; uint8_t v___x_3341_; 
v___x_3340_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3341_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3255_, v___x_3340_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3343_; double v___x_3344_; double v___x_3345_; double v___x_3346_; 
v___x_3342_ = l_Lean_trace_profiler_threshold;
v___x_3343_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3255_, v___x_3342_);
v___x_3344_ = lean_float_of_nat(v___x_3343_);
v___x_3345_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3346_ = lean_float_div(v___x_3344_, v___x_3345_);
v___y_3335_ = v___x_3346_;
goto v___jp_3334_;
}
else
{
lean_object* v___x_3347_; lean_object* v___x_3348_; double v___x_3349_; 
v___x_3347_ = l_Lean_trace_profiler_threshold;
v___x_3348_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3255_, v___x_3347_);
v___x_3349_ = lean_float_of_nat(v___x_3348_);
v___y_3335_ = v___x_3349_;
goto v___jp_3334_;
}
}
v___jp_3269_:
{
lean_object* v___x_3273_; 
lean_inc(v___y_3271_);
v___x_3273_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3257_, v_data_3272_, v___y_3271_, v___y_3270_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v___x_3274_; 
lean_dec_ref_known(v___x_3273_, 1);
v___x_3274_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3267_);
return v___x_3274_;
}
else
{
lean_object* v_a_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3282_; 
lean_dec(v_fst_3267_);
v_a_3275_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3282_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3282_ == 0)
{
v___x_3277_ = v___x_3273_;
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_a_3275_);
lean_dec(v___x_3273_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3282_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3280_; 
if (v_isShared_3278_ == 0)
{
v___x_3280_ = v___x_3277_;
goto v_reusejp_3279_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_a_3275_);
v___x_3280_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3279_;
}
v_reusejp_3279_:
{
return v___x_3280_;
}
}
}
}
v___jp_3287_:
{
uint8_t v_result_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; double v___x_3293_; lean_object* v_data_3294_; 
v_result_3290_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3267_);
v___x_3291_ = lean_box(v_result_3290_);
v___x_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3292_, 0, v___x_3291_);
v___x_3293_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3254_);
lean_inc_ref(v___x_3292_);
lean_inc(v_cls_3252_);
v_data_3294_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3294_, 0, v_cls_3252_);
lean_ctor_set(v_data_3294_, 1, v___x_3292_);
lean_ctor_set(v_data_3294_, 2, v_tag_3254_);
lean_ctor_set_float(v_data_3294_, sizeof(void*)*3, v___x_3293_);
lean_ctor_set_float(v_data_3294_, sizeof(void*)*3 + 8, v___x_3293_);
lean_ctor_set_uint8(v_data_3294_, sizeof(void*)*3 + 16, v_collapsed_3253_);
if (v___x_3286_ == 0)
{
lean_dec_ref_known(v___x_3292_, 1);
lean_dec(v_snd_3284_);
lean_dec(v_fst_3283_);
lean_dec_ref(v_tag_3254_);
lean_dec(v_cls_3252_);
v___y_3270_ = v_a_3289_;
v___y_3271_ = v___y_3288_;
v_data_3272_ = v_data_3294_;
goto v___jp_3269_;
}
else
{
lean_object* v_data_3295_; double v___x_3296_; double v___x_3297_; 
lean_dec_ref_known(v_data_3294_, 3);
v_data_3295_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3295_, 0, v_cls_3252_);
lean_ctor_set(v_data_3295_, 1, v___x_3292_);
lean_ctor_set(v_data_3295_, 2, v_tag_3254_);
v___x_3296_ = lean_unbox_float(v_fst_3283_);
lean_dec(v_fst_3283_);
lean_ctor_set_float(v_data_3295_, sizeof(void*)*3, v___x_3296_);
v___x_3297_ = lean_unbox_float(v_snd_3284_);
lean_dec(v_snd_3284_);
lean_ctor_set_float(v_data_3295_, sizeof(void*)*3 + 8, v___x_3297_);
lean_ctor_set_uint8(v_data_3295_, sizeof(void*)*3 + 16, v_collapsed_3253_);
v___y_3270_ = v_a_3289_;
v___y_3271_ = v___y_3288_;
v_data_3272_ = v_data_3295_;
goto v___jp_3269_;
}
}
v___jp_3298_:
{
lean_object* v_ref_3299_; lean_object* v___x_3300_; 
v_ref_3299_ = lean_ctor_get(v___y_3264_, 5);
lean_inc(v___y_3265_);
lean_inc_ref(v___y_3264_);
lean_inc(v___y_3263_);
lean_inc_ref(v___y_3262_);
lean_inc(v___y_3261_);
lean_inc(v___y_3260_);
lean_inc(v_fst_3267_);
v___x_3300_ = lean_apply_8(v_msg_3258_, v_fst_3267_, v___y_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_, lean_box(0));
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; 
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3301_);
lean_dec_ref_known(v___x_3300_, 1);
v___y_3288_ = v_ref_3299_;
v_a_3289_ = v_a_3301_;
goto v___jp_3287_;
}
else
{
lean_object* v___x_3302_; 
lean_dec_ref_known(v___x_3300_, 1);
v___x_3302_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3288_ = v_ref_3299_;
v_a_3289_ = v___x_3302_;
goto v___jp_3287_;
}
}
v___jp_3303_:
{
if (v_clsEnabled_3256_ == 0)
{
if (v___y_3304_ == 0)
{
lean_object* v___x_3305_; lean_object* v_traceState_3306_; lean_object* v_env_3307_; lean_object* v_nextMacroScope_3308_; lean_object* v_ngen_3309_; lean_object* v_auxDeclNGen_3310_; lean_object* v_cache_3311_; lean_object* v_messages_3312_; lean_object* v_infoState_3313_; lean_object* v_snapshotTasks_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_snd_3284_);
lean_dec(v_fst_3283_);
lean_dec_ref(v_msg_3258_);
lean_dec_ref(v_tag_3254_);
lean_dec(v_cls_3252_);
v___x_3305_ = lean_st_ref_take(v___y_3265_);
v_traceState_3306_ = lean_ctor_get(v___x_3305_, 4);
v_env_3307_ = lean_ctor_get(v___x_3305_, 0);
v_nextMacroScope_3308_ = lean_ctor_get(v___x_3305_, 1);
v_ngen_3309_ = lean_ctor_get(v___x_3305_, 2);
v_auxDeclNGen_3310_ = lean_ctor_get(v___x_3305_, 3);
v_cache_3311_ = lean_ctor_get(v___x_3305_, 5);
v_messages_3312_ = lean_ctor_get(v___x_3305_, 6);
v_infoState_3313_ = lean_ctor_get(v___x_3305_, 7);
v_snapshotTasks_3314_ = lean_ctor_get(v___x_3305_, 8);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3305_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3316_ = v___x_3305_;
v_isShared_3317_ = v_isSharedCheck_3333_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_snapshotTasks_3314_);
lean_inc(v_infoState_3313_);
lean_inc(v_messages_3312_);
lean_inc(v_cache_3311_);
lean_inc(v_traceState_3306_);
lean_inc(v_auxDeclNGen_3310_);
lean_inc(v_ngen_3309_);
lean_inc(v_nextMacroScope_3308_);
lean_inc(v_env_3307_);
lean_dec(v___x_3305_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3333_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
uint64_t v_tid_3318_; lean_object* v_traces_3319_; lean_object* v___x_3321_; uint8_t v_isShared_3322_; uint8_t v_isSharedCheck_3332_; 
v_tid_3318_ = lean_ctor_get_uint64(v_traceState_3306_, sizeof(void*)*1);
v_traces_3319_ = lean_ctor_get(v_traceState_3306_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_traceState_3306_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3321_ = v_traceState_3306_;
v_isShared_3322_ = v_isSharedCheck_3332_;
goto v_resetjp_3320_;
}
else
{
lean_inc(v_traces_3319_);
lean_dec(v_traceState_3306_);
v___x_3321_ = lean_box(0);
v_isShared_3322_ = v_isSharedCheck_3332_;
goto v_resetjp_3320_;
}
v_resetjp_3320_:
{
lean_object* v___x_3323_; lean_object* v___x_3325_; 
v___x_3323_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3257_, v_traces_3319_);
lean_dec_ref(v_traces_3319_);
if (v_isShared_3322_ == 0)
{
lean_ctor_set(v___x_3321_, 0, v___x_3323_);
v___x_3325_ = v___x_3321_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v___x_3323_);
lean_ctor_set_uint64(v_reuseFailAlloc_3331_, sizeof(void*)*1, v_tid_3318_);
v___x_3325_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
lean_object* v___x_3327_; 
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 4, v___x_3325_);
v___x_3327_ = v___x_3316_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3330_; 
v_reuseFailAlloc_3330_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_env_3307_);
lean_ctor_set(v_reuseFailAlloc_3330_, 1, v_nextMacroScope_3308_);
lean_ctor_set(v_reuseFailAlloc_3330_, 2, v_ngen_3309_);
lean_ctor_set(v_reuseFailAlloc_3330_, 3, v_auxDeclNGen_3310_);
lean_ctor_set(v_reuseFailAlloc_3330_, 4, v___x_3325_);
lean_ctor_set(v_reuseFailAlloc_3330_, 5, v_cache_3311_);
lean_ctor_set(v_reuseFailAlloc_3330_, 6, v_messages_3312_);
lean_ctor_set(v_reuseFailAlloc_3330_, 7, v_infoState_3313_);
lean_ctor_set(v_reuseFailAlloc_3330_, 8, v_snapshotTasks_3314_);
v___x_3327_ = v_reuseFailAlloc_3330_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_st_ref_set(v___y_3265_, v___x_3327_);
v___x_3329_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3267_);
return v___x_3329_;
}
}
}
}
}
else
{
goto v___jp_3298_;
}
}
else
{
goto v___jp_3298_;
}
}
v___jp_3334_:
{
double v___x_3336_; double v___x_3337_; double v___x_3338_; uint8_t v___x_3339_; 
v___x_3336_ = lean_unbox_float(v_snd_3284_);
v___x_3337_ = lean_unbox_float(v_fst_3283_);
v___x_3338_ = lean_float_sub(v___x_3336_, v___x_3337_);
v___x_3339_ = lean_float_decLt(v___y_3335_, v___x_3338_);
v___y_3304_ = v___x_3339_;
goto v___jp_3303_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3350_, lean_object* v_collapsed_3351_, lean_object* v_tag_3352_, lean_object* v_opts_3353_, lean_object* v_clsEnabled_3354_, lean_object* v_oldTraces_3355_, lean_object* v_msg_3356_, lean_object* v_resStartStop_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
uint8_t v_collapsed_boxed_3365_; uint8_t v_clsEnabled_boxed_3366_; lean_object* v_res_3367_; 
v_collapsed_boxed_3365_ = lean_unbox(v_collapsed_3351_);
v_clsEnabled_boxed_3366_ = lean_unbox(v_clsEnabled_3354_);
v_res_3367_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3350_, v_collapsed_boxed_3365_, v_tag_3352_, v_opts_3353_, v_clsEnabled_boxed_3366_, v_oldTraces_3355_, v_msg_3356_, v_resStartStop_3357_, v___y_3358_, v___y_3359_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_);
lean_dec(v___y_3363_);
lean_dec_ref(v___y_3362_);
lean_dec(v___y_3361_);
lean_dec_ref(v___y_3360_);
lean_dec(v___y_3359_);
lean_dec(v___y_3358_);
lean_dec_ref(v_opts_3353_);
return v_res_3367_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3368_ = lean_unsigned_to_nat(32u);
v___x_3369_ = lean_mk_empty_array_with_capacity(v___x_3368_);
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
return v___x_3370_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; 
v___x_3371_ = ((size_t)5ULL);
v___x_3372_ = lean_unsigned_to_nat(0u);
v___x_3373_ = lean_unsigned_to_nat(32u);
v___x_3374_ = lean_mk_empty_array_with_capacity(v___x_3373_);
v___x_3375_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3376_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3376_, 0, v___x_3375_);
lean_ctor_set(v___x_3376_, 1, v___x_3374_);
lean_ctor_set(v___x_3376_, 2, v___x_3372_);
lean_ctor_set(v___x_3376_, 3, v___x_3372_);
lean_ctor_set_usize(v___x_3376_, 4, v___x_3371_);
return v___x_3376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3377_){
_start:
{
lean_object* v___x_3379_; lean_object* v_traceState_3380_; lean_object* v_traces_3381_; lean_object* v___x_3382_; lean_object* v_traceState_3383_; lean_object* v_env_3384_; lean_object* v_nextMacroScope_3385_; lean_object* v_ngen_3386_; lean_object* v_auxDeclNGen_3387_; lean_object* v_cache_3388_; lean_object* v_messages_3389_; lean_object* v_infoState_3390_; lean_object* v_snapshotTasks_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3410_; 
v___x_3379_ = lean_st_ref_get(v___y_3377_);
v_traceState_3380_ = lean_ctor_get(v___x_3379_, 4);
lean_inc_ref(v_traceState_3380_);
lean_dec(v___x_3379_);
v_traces_3381_ = lean_ctor_get(v_traceState_3380_, 0);
lean_inc_ref(v_traces_3381_);
lean_dec_ref(v_traceState_3380_);
v___x_3382_ = lean_st_ref_take(v___y_3377_);
v_traceState_3383_ = lean_ctor_get(v___x_3382_, 4);
v_env_3384_ = lean_ctor_get(v___x_3382_, 0);
v_nextMacroScope_3385_ = lean_ctor_get(v___x_3382_, 1);
v_ngen_3386_ = lean_ctor_get(v___x_3382_, 2);
v_auxDeclNGen_3387_ = lean_ctor_get(v___x_3382_, 3);
v_cache_3388_ = lean_ctor_get(v___x_3382_, 5);
v_messages_3389_ = lean_ctor_get(v___x_3382_, 6);
v_infoState_3390_ = lean_ctor_get(v___x_3382_, 7);
v_snapshotTasks_3391_ = lean_ctor_get(v___x_3382_, 8);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3393_ = v___x_3382_;
v_isShared_3394_ = v_isSharedCheck_3410_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_snapshotTasks_3391_);
lean_inc(v_infoState_3390_);
lean_inc(v_messages_3389_);
lean_inc(v_cache_3388_);
lean_inc(v_traceState_3383_);
lean_inc(v_auxDeclNGen_3387_);
lean_inc(v_ngen_3386_);
lean_inc(v_nextMacroScope_3385_);
lean_inc(v_env_3384_);
lean_dec(v___x_3382_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3410_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
uint64_t v_tid_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3408_; 
v_tid_3395_ = lean_ctor_get_uint64(v_traceState_3383_, sizeof(void*)*1);
v_isSharedCheck_3408_ = !lean_is_exclusive(v_traceState_3383_);
if (v_isSharedCheck_3408_ == 0)
{
lean_object* v_unused_3409_; 
v_unused_3409_ = lean_ctor_get(v_traceState_3383_, 0);
lean_dec(v_unused_3409_);
v___x_3397_ = v_traceState_3383_;
v_isShared_3398_ = v_isSharedCheck_3408_;
goto v_resetjp_3396_;
}
else
{
lean_dec(v_traceState_3383_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3408_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3399_; lean_object* v___x_3401_; 
v___x_3399_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3398_ == 0)
{
lean_ctor_set(v___x_3397_, 0, v___x_3399_);
v___x_3401_ = v___x_3397_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3407_; 
v_reuseFailAlloc_3407_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3407_, 0, v___x_3399_);
lean_ctor_set_uint64(v_reuseFailAlloc_3407_, sizeof(void*)*1, v_tid_3395_);
v___x_3401_ = v_reuseFailAlloc_3407_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
lean_object* v___x_3403_; 
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 4, v___x_3401_);
v___x_3403_ = v___x_3393_;
goto v_reusejp_3402_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_env_3384_);
lean_ctor_set(v_reuseFailAlloc_3406_, 1, v_nextMacroScope_3385_);
lean_ctor_set(v_reuseFailAlloc_3406_, 2, v_ngen_3386_);
lean_ctor_set(v_reuseFailAlloc_3406_, 3, v_auxDeclNGen_3387_);
lean_ctor_set(v_reuseFailAlloc_3406_, 4, v___x_3401_);
lean_ctor_set(v_reuseFailAlloc_3406_, 5, v_cache_3388_);
lean_ctor_set(v_reuseFailAlloc_3406_, 6, v_messages_3389_);
lean_ctor_set(v_reuseFailAlloc_3406_, 7, v_infoState_3390_);
lean_ctor_set(v_reuseFailAlloc_3406_, 8, v_snapshotTasks_3391_);
v___x_3403_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3402_;
}
v_reusejp_3402_:
{
lean_object* v___x_3404_; lean_object* v___x_3405_; 
v___x_3404_ = lean_st_ref_set(v___y_3377_, v___x_3403_);
v___x_3405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3405_, 0, v_traces_3381_);
return v___x_3405_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3411_);
lean_dec(v___y_3411_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v___x_3422_; 
lean_inc(v___y_3416_);
lean_inc(v___y_3415_);
v___x_3422_ = lean_apply_7(v_x_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_, v___y_3420_, lean_box(0));
return v___x_3422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_){
_start:
{
lean_object* v_res_3431_; 
v_res_3431_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3423_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
lean_dec(v___y_3425_);
lean_dec(v___y_3424_);
return v_res_3431_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3432_, lean_object* v_localInsts_3433_, lean_object* v_x_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v___f_3442_; lean_object* v___x_3443_; 
lean_inc(v___y_3436_);
lean_inc(v___y_3435_);
v___f_3442_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3442_, 0, v_x_3434_);
lean_closure_set(v___f_3442_, 1, v___y_3435_);
lean_closure_set(v___f_3442_, 2, v___y_3436_);
v___x_3443_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3432_, v_localInsts_3433_, v___f_3442_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3443_) == 0)
{
return v___x_3443_;
}
else
{
lean_object* v_a_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3451_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3451_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3451_ == 0)
{
v___x_3446_ = v___x_3443_;
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_a_3444_);
lean_dec(v___x_3443_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3451_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3449_; 
if (v_isShared_3447_ == 0)
{
v___x_3449_ = v___x_3446_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3450_; 
v_reuseFailAlloc_3450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3450_, 0, v_a_3444_);
v___x_3449_ = v_reuseFailAlloc_3450_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
return v___x_3449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3452_, lean_object* v_localInsts_3453_, lean_object* v_x_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_){
_start:
{
lean_object* v_res_3462_; 
v_res_3462_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3452_, v_localInsts_3453_, v_x_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_, v___y_3460_);
lean_dec(v___y_3460_);
lean_dec_ref(v___y_3459_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec(v___y_3455_);
return v_res_3462_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v_ngen_3466_; lean_object* v_namePrefix_3467_; lean_object* v_idx_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3497_; 
v___x_3465_ = lean_st_ref_get(v___y_3463_);
v_ngen_3466_ = lean_ctor_get(v___x_3465_, 2);
lean_inc_ref(v_ngen_3466_);
lean_dec(v___x_3465_);
v_namePrefix_3467_ = lean_ctor_get(v_ngen_3466_, 0);
v_idx_3468_ = lean_ctor_get(v_ngen_3466_, 1);
v_isSharedCheck_3497_ = !lean_is_exclusive(v_ngen_3466_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3470_ = v_ngen_3466_;
v_isShared_3471_ = v_isSharedCheck_3497_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_idx_3468_);
lean_inc(v_namePrefix_3467_);
lean_dec(v_ngen_3466_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3497_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3472_; lean_object* v_env_3473_; lean_object* v_nextMacroScope_3474_; lean_object* v_auxDeclNGen_3475_; lean_object* v_traceState_3476_; lean_object* v_cache_3477_; lean_object* v_messages_3478_; lean_object* v_infoState_3479_; lean_object* v_snapshotTasks_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3495_; 
v___x_3472_ = lean_st_ref_take(v___y_3463_);
v_env_3473_ = lean_ctor_get(v___x_3472_, 0);
v_nextMacroScope_3474_ = lean_ctor_get(v___x_3472_, 1);
v_auxDeclNGen_3475_ = lean_ctor_get(v___x_3472_, 3);
v_traceState_3476_ = lean_ctor_get(v___x_3472_, 4);
v_cache_3477_ = lean_ctor_get(v___x_3472_, 5);
v_messages_3478_ = lean_ctor_get(v___x_3472_, 6);
v_infoState_3479_ = lean_ctor_get(v___x_3472_, 7);
v_snapshotTasks_3480_ = lean_ctor_get(v___x_3472_, 8);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3472_);
if (v_isSharedCheck_3495_ == 0)
{
lean_object* v_unused_3496_; 
v_unused_3496_ = lean_ctor_get(v___x_3472_, 2);
lean_dec(v_unused_3496_);
v___x_3482_ = v___x_3472_;
v_isShared_3483_ = v_isSharedCheck_3495_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_snapshotTasks_3480_);
lean_inc(v_infoState_3479_);
lean_inc(v_messages_3478_);
lean_inc(v_cache_3477_);
lean_inc(v_traceState_3476_);
lean_inc(v_auxDeclNGen_3475_);
lean_inc(v_nextMacroScope_3474_);
lean_inc(v_env_3473_);
lean_dec(v___x_3472_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3495_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v_r_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
lean_inc(v_idx_3468_);
lean_inc(v_namePrefix_3467_);
v_r_3484_ = l_Lean_Name_num___override(v_namePrefix_3467_, v_idx_3468_);
v___x_3485_ = lean_unsigned_to_nat(1u);
v___x_3486_ = lean_nat_add(v_idx_3468_, v___x_3485_);
lean_dec(v_idx_3468_);
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 1, v___x_3486_);
v___x_3488_ = v___x_3470_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_namePrefix_3467_);
lean_ctor_set(v_reuseFailAlloc_3494_, 1, v___x_3486_);
v___x_3488_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3490_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 2, v___x_3488_);
v___x_3490_ = v___x_3482_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3493_; 
v_reuseFailAlloc_3493_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3493_, 0, v_env_3473_);
lean_ctor_set(v_reuseFailAlloc_3493_, 1, v_nextMacroScope_3474_);
lean_ctor_set(v_reuseFailAlloc_3493_, 2, v___x_3488_);
lean_ctor_set(v_reuseFailAlloc_3493_, 3, v_auxDeclNGen_3475_);
lean_ctor_set(v_reuseFailAlloc_3493_, 4, v_traceState_3476_);
lean_ctor_set(v_reuseFailAlloc_3493_, 5, v_cache_3477_);
lean_ctor_set(v_reuseFailAlloc_3493_, 6, v_messages_3478_);
lean_ctor_set(v_reuseFailAlloc_3493_, 7, v_infoState_3479_);
lean_ctor_set(v_reuseFailAlloc_3493_, 8, v_snapshotTasks_3480_);
v___x_3490_ = v_reuseFailAlloc_3493_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
lean_object* v___x_3491_; lean_object* v___x_3492_; 
v___x_3491_ = lean_st_ref_set(v___y_3463_, v___x_3490_);
v___x_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3492_, 0, v_r_3484_);
return v___x_3492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3498_);
lean_dec(v___y_3498_);
return v_res_3500_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v___x_3508_; lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
v___x_3508_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3506_);
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3508_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3508_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3517_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v___y_3518_);
lean_dec(v___y_3517_);
return v_res_3524_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
v___x_3526_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3527_ = l_Lean_stringToMessageData(v___x_3526_);
return v___x_3527_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3529_; lean_object* v___x_3530_; 
v___x_3529_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3530_ = l_Lean_stringToMessageData(v___x_3529_);
return v___x_3530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3533_, lean_object* v_x_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v___x_3542_; lean_object* v___y_3544_; uint8_t v___x_3553_; 
v___x_3542_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3553_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3535_);
if (v___x_3553_ == 0)
{
lean_object* v___x_3554_; 
v___x_3554_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3544_ = v___x_3554_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3555_; 
v___x_3555_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3544_ = v___x_3555_;
goto v___jp_3543_;
}
v___jp_3543_:
{
lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3551_; lean_object* v___x_3552_; 
lean_inc_ref(v___y_3544_);
v___x_3545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___y_3544_);
v___x_3546_ = l_Lean_MessageData_ofFormat(v___x_3545_);
v___x_3547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3542_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
v___x_3548_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3549_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3549_, 0, v___x_3547_);
lean_ctor_set(v___x_3549_, 1, v___x_3548_);
v___x_3550_ = l_Lean_indentExpr(v_e_3533_);
v___x_3551_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3551_, 0, v___x_3549_);
lean_ctor_set(v___x_3551_, 1, v___x_3550_);
v___x_3552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3552_, 0, v___x_3551_);
return v___x_3552_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3556_, lean_object* v_x_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
lean_object* v_res_3565_; 
v_res_3565_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3556_, v_x_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_, v___y_3563_);
lean_dec(v___y_3563_);
lean_dec_ref(v___y_3562_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v_x_3557_);
return v_res_3565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3566_, lean_object* v_x_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
lean_object* v_keyedConfig_3575_; uint8_t v_trackZetaDelta_3576_; lean_object* v_zetaDeltaSet_3577_; lean_object* v_localInstances_3578_; lean_object* v_defEqCtx_x3f_3579_; lean_object* v_synthPendingDepth_3580_; lean_object* v_canUnfold_x3f_3581_; uint8_t v_univApprox_3582_; uint8_t v_inTypeClassResolution_3583_; uint8_t v_cacheInferType_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; 
v_keyedConfig_3575_ = lean_ctor_get(v___y_3570_, 0);
v_trackZetaDelta_3576_ = lean_ctor_get_uint8(v___y_3570_, sizeof(void*)*7);
v_zetaDeltaSet_3577_ = lean_ctor_get(v___y_3570_, 1);
v_localInstances_3578_ = lean_ctor_get(v___y_3570_, 3);
v_defEqCtx_x3f_3579_ = lean_ctor_get(v___y_3570_, 4);
v_synthPendingDepth_3580_ = lean_ctor_get(v___y_3570_, 5);
v_canUnfold_x3f_3581_ = lean_ctor_get(v___y_3570_, 6);
v_univApprox_3582_ = lean_ctor_get_uint8(v___y_3570_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3583_ = lean_ctor_get_uint8(v___y_3570_, sizeof(void*)*7 + 2);
v_cacheInferType_3584_ = lean_ctor_get_uint8(v___y_3570_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_3581_);
lean_inc(v_synthPendingDepth_3580_);
lean_inc(v_defEqCtx_x3f_3579_);
lean_inc_ref(v_localInstances_3578_);
lean_inc(v_zetaDeltaSet_3577_);
lean_inc_ref(v_keyedConfig_3575_);
v___x_3585_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3585_, 0, v_keyedConfig_3575_);
lean_ctor_set(v___x_3585_, 1, v_zetaDeltaSet_3577_);
lean_ctor_set(v___x_3585_, 2, v_lctx_3566_);
lean_ctor_set(v___x_3585_, 3, v_localInstances_3578_);
lean_ctor_set(v___x_3585_, 4, v_defEqCtx_x3f_3579_);
lean_ctor_set(v___x_3585_, 5, v_synthPendingDepth_3580_);
lean_ctor_set(v___x_3585_, 6, v_canUnfold_x3f_3581_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*7, v_trackZetaDelta_3576_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*7 + 1, v_univApprox_3582_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3583_);
lean_ctor_set_uint8(v___x_3585_, sizeof(void*)*7 + 3, v_cacheInferType_3584_);
lean_inc(v___y_3573_);
lean_inc_ref(v___y_3572_);
lean_inc(v___y_3571_);
lean_inc(v___y_3569_);
lean_inc(v___y_3568_);
v___x_3586_ = lean_apply_7(v_x_3567_, v___y_3568_, v___y_3569_, v___x_3585_, v___y_3571_, v___y_3572_, v___y_3573_, lean_box(0));
if (lean_obj_tag(v___x_3586_) == 0)
{
lean_object* v_a_3587_; lean_object* v___x_3589_; uint8_t v_isShared_3590_; uint8_t v_isSharedCheck_3594_; 
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
v_isSharedCheck_3594_ = !lean_is_exclusive(v___x_3586_);
if (v_isSharedCheck_3594_ == 0)
{
v___x_3589_ = v___x_3586_;
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
else
{
lean_inc(v_a_3587_);
lean_dec(v___x_3586_);
v___x_3589_ = lean_box(0);
v_isShared_3590_ = v_isSharedCheck_3594_;
goto v_resetjp_3588_;
}
v_resetjp_3588_:
{
lean_object* v___x_3592_; 
if (v_isShared_3590_ == 0)
{
v___x_3592_ = v___x_3589_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v_a_3587_);
v___x_3592_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
return v___x_3592_;
}
}
}
else
{
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3595_, lean_object* v_x_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3595_, v_x_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
lean_dec(v___y_3600_);
lean_dec_ref(v___y_3599_);
lean_dec(v___y_3598_);
lean_dec(v___y_3597_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3607_, lean_object* v_letFVars_3608_, lean_object* v_lctx_3609_, lean_object* v_v_3610_, lean_object* v_e_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_){
_start:
{
lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3619_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3620_ = lean_expr_instantiate_rev(v_e_3611_, v_fvars_3607_);
v___x_3621_ = lean_apply_1(v_v_3610_, v___x_3620_);
v___x_3622_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3622_, 0, lean_box(0));
lean_closure_set(v___x_3622_, 1, v_letFVars_3608_);
lean_closure_set(v___x_3622_, 2, v___x_3621_);
v___x_3623_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3609_, v___x_3619_, v___x_3622_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
return v___x_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3624_, lean_object* v_letFVars_3625_, lean_object* v_lctx_3626_, lean_object* v_v_3627_, lean_object* v_e_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v_res_3636_; 
v_res_3636_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3624_, v_letFVars_3625_, v_lctx_3626_, v_v_3627_, v_e_3628_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec(v___y_3629_);
lean_dec_ref(v_e_3628_);
lean_dec_ref(v_fvars_3624_);
return v_res_3636_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3638_; lean_object* v___x_3639_; 
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3639_ = l_Lean_stringToMessageData(v___x_3638_);
return v___x_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3640_, lean_object* v_a_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_){
_start:
{
lean_object* v___x_3649_; 
lean_inc_ref(v_a_3640_);
v___x_3649_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3640_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v_expr_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3701_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
v_expr_3651_ = lean_ctor_get(v_a_3641_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v_a_3641_);
if (v_isSharedCheck_3701_ == 0)
{
lean_object* v_unused_3702_; 
v_unused_3702_ = lean_ctor_get(v_a_3641_, 1);
lean_dec(v_unused_3702_);
v___x_3653_ = v_a_3641_;
v_isShared_3654_ = v_isSharedCheck_3701_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_expr_3651_);
lean_dec(v_a_3641_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3701_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v___x_3655_; 
lean_inc(v_a_3650_);
lean_inc_ref(v_expr_3651_);
v___x_3655_ = l_Lean_Meta_isExprDefEq(v_expr_3651_, v_a_3650_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3692_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3692_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3692_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3692_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3692_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
uint8_t v___x_3660_; 
v___x_3660_ = lean_unbox(v_a_3656_);
lean_dec(v_a_3656_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
lean_del_object(v___x_3658_);
v___x_3661_ = lean_box(0);
v___x_3662_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3663_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3650_, v_expr_3651_, v___x_3661_, v___x_3662_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v_expr_3665_; lean_object* v___x_3667_; uint8_t v_isShared_3668_; uint8_t v_isSharedCheck_3678_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v_expr_3665_ = lean_ctor_get(v_a_3640_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v_a_3640_);
if (v_isSharedCheck_3678_ == 0)
{
lean_object* v_unused_3679_; 
v_unused_3679_ = lean_ctor_get(v_a_3640_, 1);
lean_dec(v_unused_3679_);
v___x_3667_ = v_a_3640_;
v_isShared_3668_ = v_isSharedCheck_3678_;
goto v_resetjp_3666_;
}
else
{
lean_inc(v_expr_3665_);
lean_dec(v_a_3640_);
v___x_3667_ = lean_box(0);
v_isShared_3668_ = v_isSharedCheck_3678_;
goto v_resetjp_3666_;
}
v_resetjp_3666_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3669_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3670_ = l_Lean_indentExpr(v_expr_3665_);
if (v_isShared_3668_ == 0)
{
lean_ctor_set_tag(v___x_3667_, 7);
lean_ctor_set(v___x_3667_, 1, v___x_3670_);
lean_ctor_set(v___x_3667_, 0, v___x_3669_);
v___x_3672_ = v___x_3667_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3669_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3674_; 
if (v_isShared_3654_ == 0)
{
lean_ctor_set_tag(v___x_3653_, 7);
lean_ctor_set(v___x_3653_, 1, v_a_3664_);
lean_ctor_set(v___x_3653_, 0, v___x_3672_);
v___x_3674_ = v___x_3653_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v___x_3672_);
lean_ctor_set(v_reuseFailAlloc_3676_, 1, v_a_3664_);
v___x_3674_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3675_; 
v___x_3675_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3674_, v___y_3644_, v___y_3645_, v___y_3646_, v___y_3647_);
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_del_object(v___x_3653_);
lean_dec_ref(v_a_3640_);
v_a_3680_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3663_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3663_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
else
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
lean_del_object(v___x_3653_);
lean_dec_ref(v_expr_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3640_);
v___x_3688_ = lean_box(0);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3688_);
v___x_3690_ = v___x_3658_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
return v___x_3690_;
}
}
}
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_del_object(v___x_3653_);
lean_dec_ref(v_expr_3651_);
lean_dec(v_a_3650_);
lean_dec_ref(v_a_3640_);
v_a_3693_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3655_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3655_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_dec_ref(v_a_3641_);
lean_dec_ref(v_a_3640_);
v_a_3703_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3649_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3649_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_){
_start:
{
lean_object* v_res_3720_; 
v_res_3720_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3711_, v_a_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec(v___y_3716_);
lean_dec_ref(v___y_3715_);
lean_dec(v___y_3714_);
lean_dec(v___y_3713_);
return v_res_3720_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_, lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
if (lean_obj_tag(v_e_3724_) == 5)
{
lean_object* v_fn_3732_; lean_object* v_arg_3733_; lean_object* v___x_3734_; 
v_fn_3732_ = lean_ctor_get(v_e_3724_, 0);
v_arg_3733_ = lean_ctor_get(v_e_3724_, 1);
lean_inc_ref(v_fn_3732_);
v___x_3734_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3732_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3736_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
lean_inc(v_a_3735_);
lean_dec_ref_known(v___x_3734_, 1);
lean_inc_ref(v_arg_3733_);
v___x_3736_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3733_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3757_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3757_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3757_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_expr_3741_; uint8_t v___y_3743_; size_t v___x_3751_; size_t v___x_3752_; uint8_t v___x_3753_; 
v_expr_3741_ = lean_ctor_get(v_a_3737_, 0);
lean_inc_ref(v_expr_3741_);
lean_dec(v_a_3737_);
v___x_3751_ = lean_ptr_addr(v_fn_3732_);
v___x_3752_ = lean_ptr_addr(v_a_3735_);
v___x_3753_ = lean_usize_dec_eq(v___x_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
v___y_3743_ = v___x_3753_;
goto v___jp_3742_;
}
else
{
size_t v___x_3754_; size_t v___x_3755_; uint8_t v___x_3756_; 
v___x_3754_ = lean_ptr_addr(v_arg_3733_);
v___x_3755_ = lean_ptr_addr(v_expr_3741_);
v___x_3756_ = lean_usize_dec_eq(v___x_3754_, v___x_3755_);
v___y_3743_ = v___x_3756_;
goto v___jp_3742_;
}
v___jp_3742_:
{
if (v___y_3743_ == 0)
{
lean_object* v___x_3744_; lean_object* v___x_3746_; 
lean_dec_ref_known(v_e_3724_, 2);
v___x_3744_ = l_Lean_Expr_app___override(v_a_3735_, v_expr_3741_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3744_);
v___x_3746_ = v___x_3739_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
else
{
lean_object* v___x_3749_; 
lean_dec_ref(v_expr_3741_);
lean_dec(v_a_3735_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_e_3724_);
v___x_3749_ = v___x_3739_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_e_3724_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_dec(v_a_3735_);
lean_dec_ref_known(v_e_3724_, 2);
v_a_3758_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3736_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3736_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3724_, 2);
return v___x_3734_;
}
}
else
{
lean_object* v___x_3766_; 
v___x_3766_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
if (lean_obj_tag(v___x_3766_) == 0)
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3775_; 
v_a_3767_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3769_ = v___x_3766_;
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3766_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3775_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v_expr_3771_; lean_object* v___x_3773_; 
v_expr_3771_ = lean_ctor_get(v_a_3767_, 0);
lean_inc_ref(v_expr_3771_);
lean_dec(v_a_3767_);
if (v_isShared_3770_ == 0)
{
lean_ctor_set(v___x_3769_, 0, v_expr_3771_);
v___x_3773_ = v___x_3769_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_expr_3771_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
v_a_3776_ = lean_ctor_get(v___x_3766_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3766_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3766_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_){
_start:
{
lean_object* v_res_3792_; 
v_res_3792_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_, v_a_3790_);
lean_dec(v_a_3790_);
lean_dec_ref(v_a_3789_);
lean_dec(v_a_3788_);
lean_dec_ref(v_a_3787_);
lean_dec(v_a_3786_);
lean_dec(v_a_3785_);
return v_res_3792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3793_, lean_object* v_a_3794_, lean_object* v_a_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_){
_start:
{
if (lean_obj_tag(v_e_3793_) == 5)
{
lean_object* v_fn_3801_; lean_object* v_arg_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; 
v_fn_3801_ = lean_ctor_get(v_e_3793_, 0);
v_arg_3802_ = lean_ctor_get(v_e_3793_, 1);
lean_inc_ref_n(v_fn_3801_, 2);
v___x_3803_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3803_, 0, v_fn_3801_);
v___x_3804_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3801_, v___x_3803_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3806_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v___x_3804_, 1);
lean_inc_ref(v_arg_3802_);
v___x_3806_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3802_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; lean_object* v___x_3808_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref_known(v___x_3806_, 1);
v___x_3808_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3793_, v_a_3805_, v_a_3807_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
return v___x_3808_;
}
else
{
lean_dec(v_a_3805_);
lean_dec_ref_known(v_e_3793_, 2);
return v___x_3806_;
}
}
else
{
lean_dec_ref_known(v_e_3793_, 2);
return v___x_3804_;
}
}
else
{
lean_object* v___x_3809_; 
v___x_3809_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3793_, v_a_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_);
return v___x_3809_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3810_, lean_object* v_a_3811_, lean_object* v_a_3812_, lean_object* v_a_3813_, lean_object* v_a_3814_, lean_object* v_a_3815_, lean_object* v_a_3816_){
_start:
{
uint8_t v___x_3818_; 
v___x_3818_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3811_);
if (v___x_3818_ == 0)
{
lean_object* v___x_3819_; 
v___x_3819_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
if (lean_obj_tag(v___x_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3829_; 
v_a_3820_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3822_ = v___x_3819_;
v_isShared_3823_ = v_isSharedCheck_3829_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3829_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3827_; 
v___x_3824_ = lean_box(0);
v___x_3825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3825_, 0, v_a_3820_);
lean_ctor_set(v___x_3825_, 1, v___x_3824_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set(v___x_3822_, 0, v___x_3825_);
v___x_3827_ = v___x_3822_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3825_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
v_a_3830_ = lean_ctor_get(v___x_3819_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3819_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3819_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
else
{
lean_object* v___x_3838_; 
v___x_3838_ = l_Lean_Expr_getAppFn(v_e_3810_);
if (lean_obj_tag(v___x_3838_) == 2)
{
lean_object* v_mvarId_3839_; lean_object* v_dummy_3840_; lean_object* v_nargs_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; 
v_mvarId_3839_ = lean_ctor_get(v___x_3838_, 0);
lean_inc(v_mvarId_3839_);
lean_dec_ref_known(v___x_3838_, 1);
v_dummy_3840_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3841_ = l_Lean_Expr_getAppNumArgs(v_e_3810_);
lean_inc(v_nargs_3841_);
v___x_3842_ = lean_mk_array(v_nargs_3841_, v_dummy_3840_);
v___x_3843_ = lean_unsigned_to_nat(1u);
v___x_3844_ = lean_nat_sub(v_nargs_3841_, v___x_3843_);
lean_dec(v_nargs_3841_);
lean_inc_ref(v_e_3810_);
v___x_3845_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3810_, v___x_3842_, v___x_3844_);
v___x_3846_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3839_, v___x_3845_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
lean_dec(v_mvarId_3839_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v___x_3847_; 
lean_dec_ref_known(v___x_3846_, 1);
v___x_3847_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
return v___x_3847_;
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec_ref(v_e_3810_);
v_a_3848_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3846_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3846_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v___x_3856_; 
lean_dec_ref(v___x_3838_);
v___x_3856_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3810_, v_a_3811_, v_a_3812_, v_a_3813_, v_a_3814_, v_a_3815_, v_a_3816_);
return v___x_3856_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec(v_a_3858_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3866_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3875_, v_a_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_);
return v___x_3876_;
}
else
{
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3877_, lean_object* v_a_3878_, lean_object* v_a_3879_, lean_object* v_a_3880_, lean_object* v_a_3881_, lean_object* v_a_3882_, lean_object* v_a_3883_, lean_object* v_a_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3877_, v_a_3878_, v_a_3879_, v_a_3880_, v_a_3881_, v_a_3882_, v_a_3883_);
lean_dec(v_a_3883_);
lean_dec_ref(v_a_3882_);
lean_dec(v_a_3881_);
lean_dec_ref(v_a_3880_);
lean_dec(v_a_3879_);
lean_dec(v_a_3878_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3886_, lean_object* v_fvars_3887_, lean_object* v_doms_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_){
_start:
{
lean_object* v___x_3896_; 
v___x_3896_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3886_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3898_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
lean_inc(v_a_3897_);
lean_dec_ref_known(v___x_3896_, 1);
v___x_3898_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3887_, v_doms_3888_, v_a_3897_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_, v___y_3893_, v___y_3894_);
return v___x_3898_;
}
else
{
return v___x_3896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3899_, lean_object* v_fvars_3900_, lean_object* v_doms_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_){
_start:
{
lean_object* v_res_3909_; 
v_res_3909_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3899_, v_fvars_3900_, v_doms_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3906_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec(v___y_3902_);
lean_dec_ref(v_doms_3901_);
lean_dec_ref(v_fvars_3900_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3910_, lean_object* v_fvars_3911_, lean_object* v_doms_3912_, lean_object* v_e_3913_, lean_object* v_a_3914_, lean_object* v_a_3915_, lean_object* v_a_3916_, lean_object* v_a_3917_, lean_object* v_a_3918_, lean_object* v_a_3919_){
_start:
{
lean_object* v___x_3921_; 
v___x_3921_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3913_, v_a_3915_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc(v_a_3922_);
lean_dec_ref_known(v___x_3921_, 1);
if (lean_obj_tag(v_a_3922_) == 1)
{
lean_object* v_val_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
lean_dec_ref(v_e_3913_);
v_val_3923_ = lean_ctor_get(v_a_3922_, 0);
lean_inc(v_val_3923_);
lean_dec_ref_known(v_a_3922_, 1);
v___x_3924_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3925_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3925_, 0, v_fvars_3911_);
lean_closure_set(v___x_3925_, 1, v_doms_3912_);
lean_closure_set(v___x_3925_, 2, v_val_3923_);
v___x_3926_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3910_, v___x_3924_, v___x_3925_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3926_;
}
else
{
lean_dec(v_a_3922_);
if (lean_obj_tag(v_e_3913_) == 7)
{
lean_object* v_binderName_3927_; lean_object* v_binderType_3928_; lean_object* v_body_3929_; uint8_t v_binderInfo_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v_binderName_3927_ = lean_ctor_get(v_e_3913_, 0);
lean_inc(v_binderName_3927_);
v_binderType_3928_ = lean_ctor_get(v_e_3913_, 1);
lean_inc_ref(v_binderType_3928_);
v_body_3929_ = lean_ctor_get(v_e_3913_, 2);
lean_inc_ref(v_body_3929_);
v_binderInfo_3930_ = lean_ctor_get_uint8(v_e_3913_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3913_, 3);
v___x_3931_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3932_ = lean_expr_instantiate_rev(v_binderType_3928_, v_fvars_3911_);
lean_dec_ref(v_binderType_3928_);
v___x_3933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3933_, 0, v___x_3932_);
lean_inc_ref(v_lctx_3910_);
v___x_3934_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3910_, v___x_3931_, v___x_3933_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3934_) == 0)
{
lean_object* v_a_3935_; lean_object* v___x_3936_; 
v_a_3935_ = lean_ctor_get(v___x_3934_, 0);
lean_inc(v_a_3935_);
lean_dec_ref_known(v___x_3934_, 1);
v___x_3936_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
if (lean_obj_tag(v___x_3936_) == 0)
{
lean_object* v_a_3937_; lean_object* v_expr_3938_; uint8_t v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; 
v_a_3937_ = lean_ctor_get(v___x_3936_, 0);
lean_inc_n(v_a_3937_, 2);
lean_dec_ref_known(v___x_3936_, 1);
v_expr_3938_ = lean_ctor_get(v_a_3935_, 0);
v___x_3939_ = 0;
lean_inc_ref(v_expr_3938_);
v___x_3940_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3910_, v_a_3937_, v_binderName_3927_, v_expr_3938_, v_binderInfo_3930_, v___x_3939_);
v___x_3941_ = l_Lean_Expr_fvar___override(v_a_3937_);
v___x_3942_ = lean_array_push(v_fvars_3911_, v___x_3941_);
v___x_3943_ = lean_array_push(v_doms_3912_, v_a_3935_);
v_lctx_3910_ = v___x_3940_;
v_fvars_3911_ = v___x_3942_;
v_doms_3912_ = v___x_3943_;
v_e_3913_ = v_body_3929_;
goto _start;
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec(v_a_3935_);
lean_dec_ref(v_body_3929_);
lean_dec(v_binderName_3927_);
lean_dec_ref(v_doms_3912_);
lean_dec_ref(v_fvars_3911_);
lean_dec_ref(v_lctx_3910_);
v_a_3945_ = lean_ctor_get(v___x_3936_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3936_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3936_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3936_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
else
{
lean_dec_ref(v_body_3929_);
lean_dec(v_binderName_3927_);
lean_dec_ref(v_doms_3912_);
lean_dec_ref(v_fvars_3911_);
lean_dec_ref(v_lctx_3910_);
return v___x_3934_;
}
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___f_3955_; lean_object* v___x_3956_; 
v___x_3953_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3954_ = lean_expr_instantiate_rev(v_e_3913_, v_fvars_3911_);
lean_dec_ref(v_e_3913_);
v___f_3955_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3955_, 0, v___x_3954_);
lean_closure_set(v___f_3955_, 1, v_fvars_3911_);
lean_closure_set(v___f_3955_, 2, v_doms_3912_);
v___x_3956_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3910_, v___x_3953_, v___f_3955_, v_a_3914_, v_a_3915_, v_a_3916_, v_a_3917_, v_a_3918_, v_a_3919_);
return v___x_3956_;
}
}
}
else
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3964_; 
lean_dec_ref(v_e_3913_);
lean_dec_ref(v_doms_3912_);
lean_dec_ref(v_fvars_3911_);
lean_dec_ref(v_lctx_3910_);
v_a_3957_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3959_ = v___x_3921_;
v_isShared_3960_ = v_isSharedCheck_3964_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3921_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3965_, lean_object* v_a_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_){
_start:
{
uint32_t v___x_3973_; uint8_t v___x_3974_; 
v___x_3973_ = 5;
v___x_3974_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3965_, v___x_3973_);
if (v___x_3974_ == 0)
{
lean_object* v_lctx_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v_lctx_3975_ = lean_ctor_get(v_a_3968_, 2);
v___x_3976_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3975_);
v___x_3977_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3975_, v___x_3976_, v___x_3976_, v_e_3965_, v_a_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_);
return v___x_3977_;
}
else
{
lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3978_ = lean_box(0);
v___x_3979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3979_, 0, v_e_3965_);
lean_ctor_set(v___x_3979_, 1, v___x_3978_);
v___x_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3979_);
return v___x_3980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_, lean_object* v_a_3988_){
_start:
{
lean_object* v_res_3989_; 
v_res_3989_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_, v_a_3987_);
lean_dec(v_a_3987_);
lean_dec_ref(v_a_3986_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec(v_a_3982_);
return v_res_3989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_3990_, lean_object* v_e_3991_, lean_object* v_typeName_3992_, lean_object* v_idx_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_3990_, v_e_3991_, v_typeName_3992_, v_idx_3993_, v___y_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
lean_dec(v___y_3995_);
lean_dec(v___y_3994_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4002_, lean_object* v_a_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_, lean_object* v_a_4008_, lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
lean_dec(v_a_4008_);
lean_dec_ref(v_a_4007_);
lean_dec(v_a_4006_);
lean_dec_ref(v_a_4005_);
lean_dec(v_a_4004_);
lean_dec(v_a_4003_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v___x_4020_; 
v___x_4020_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4022_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4021_);
lean_dec_ref_known(v___x_4020_, 1);
v___x_4022_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4011_, v_a_4021_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
return v___x_4022_;
}
else
{
lean_dec_ref(v_fvars_4011_);
return v___x_4020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_res_4032_; 
v_res_4032_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_, v___y_4030_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec(v___y_4028_);
lean_dec_ref(v___y_4027_);
lean_dec(v___y_4026_);
lean_dec(v___y_4025_);
return v_res_4032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4033_, lean_object* v_fvars_4034_, lean_object* v_e_4035_, lean_object* v_letFVars_4036_, lean_object* v_a_4037_, lean_object* v_a_4038_, lean_object* v_a_4039_, lean_object* v_a_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_){
_start:
{
switch(lean_obj_tag(v_e_4035_))
{
case 6:
{
lean_object* v_binderName_4044_; lean_object* v_binderType_4045_; lean_object* v_body_4046_; uint8_t v_binderInfo_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v_binderName_4044_ = lean_ctor_get(v_e_4035_, 0);
lean_inc(v_binderName_4044_);
v_binderType_4045_ = lean_ctor_get(v_e_4035_, 1);
lean_inc_ref(v_binderType_4045_);
v_body_4046_ = lean_ctor_get(v_e_4035_, 2);
lean_inc_ref(v_body_4046_);
v_binderInfo_4047_ = lean_ctor_get_uint8(v_e_4035_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4035_, 3);
v___x_4048_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4033_);
lean_inc(v_letFVars_4036_);
v___x_4049_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4034_, v_letFVars_4036_, v_lctx_4033_, v___x_4048_, v_binderType_4045_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec_ref(v_binderType_4045_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref_known(v___x_4049_, 1);
v___x_4051_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v_expr_4053_; uint8_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
lean_inc_n(v_a_4052_, 2);
lean_dec_ref_known(v___x_4051_, 1);
v_expr_4053_ = lean_ctor_get(v_a_4050_, 0);
lean_inc_ref(v_expr_4053_);
lean_dec(v_a_4050_);
v___x_4054_ = 0;
v___x_4055_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4033_, v_a_4052_, v_binderName_4044_, v_expr_4053_, v_binderInfo_4047_, v___x_4054_);
v___x_4056_ = l_Lean_Expr_fvar___override(v_a_4052_);
v___x_4057_ = lean_array_push(v_fvars_4034_, v___x_4056_);
v_lctx_4033_ = v___x_4055_;
v_fvars_4034_ = v___x_4057_;
v_e_4035_ = v_body_4046_;
goto _start;
}
else
{
lean_object* v_a_4059_; lean_object* v___x_4061_; uint8_t v_isShared_4062_; uint8_t v_isSharedCheck_4066_; 
lean_dec(v_a_4050_);
lean_dec_ref(v_body_4046_);
lean_dec(v_binderName_4044_);
lean_dec(v_letFVars_4036_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_lctx_4033_);
v_a_4059_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4061_ = v___x_4051_;
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
else
{
lean_inc(v_a_4059_);
lean_dec(v___x_4051_);
v___x_4061_ = lean_box(0);
v_isShared_4062_ = v_isSharedCheck_4066_;
goto v_resetjp_4060_;
}
v_resetjp_4060_:
{
lean_object* v___x_4064_; 
if (v_isShared_4062_ == 0)
{
v___x_4064_ = v___x_4061_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_a_4059_);
v___x_4064_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
return v___x_4064_;
}
}
}
}
else
{
lean_dec_ref(v_body_4046_);
lean_dec(v_binderName_4044_);
lean_dec(v_letFVars_4036_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_lctx_4033_);
return v___x_4049_;
}
}
case 8:
{
lean_object* v_declName_4067_; lean_object* v_type_4068_; lean_object* v_value_4069_; lean_object* v_body_4070_; uint8_t v_nondep_4071_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v_declName_4067_ = lean_ctor_get(v_e_4035_, 0);
lean_inc(v_declName_4067_);
v_type_4068_ = lean_ctor_get(v_e_4035_, 1);
lean_inc_ref(v_type_4068_);
v_value_4069_ = lean_ctor_get(v_e_4035_, 2);
lean_inc_ref(v_value_4069_);
v_body_4070_ = lean_ctor_get(v_e_4035_, 3);
lean_inc_ref(v_body_4070_);
v_nondep_4071_ = lean_ctor_get_uint8(v_e_4035_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4035_, 4);
v___x_4085_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4033_);
lean_inc(v_letFVars_4036_);
v___x_4086_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4034_, v_letFVars_4036_, v_lctx_4033_, v___x_4085_, v_type_4068_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec_ref(v_type_4068_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
lean_inc(v_a_4087_);
lean_dec_ref_known(v___x_4086_, 1);
v___x_4088_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4033_);
lean_inc(v_letFVars_4036_);
v___x_4089_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4034_, v_letFVars_4036_, v_lctx_4033_, v___x_4088_, v_value_4069_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec_ref(v_value_4069_);
if (lean_obj_tag(v___x_4089_) == 0)
{
lean_object* v_a_4090_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; uint8_t v___x_4120_; 
v_a_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc(v_a_4090_);
lean_dec_ref_known(v___x_4089_, 1);
v___x_4120_ = l_List_isEmpty___redArg(v_letFVars_4036_);
if (v___x_4120_ == 0)
{
lean_object* v___f_4121_; lean_object* v___x_4122_; 
lean_inc(v_a_4087_);
lean_inc(v_a_4090_);
v___f_4121_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4121_, 0, v_a_4090_);
lean_closure_set(v___f_4121_, 1, v_a_4087_);
lean_inc_ref(v_lctx_4033_);
v___x_4122_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4033_, v___f_4121_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
if (lean_obj_tag(v___x_4122_) == 0)
{
lean_dec_ref_known(v___x_4122_, 1);
v___y_4092_ = v_a_4037_;
v___y_4093_ = v_a_4038_;
v___y_4094_ = v_a_4039_;
v___y_4095_ = v_a_4040_;
v___y_4096_ = v_a_4041_;
v___y_4097_ = v_a_4042_;
goto v___jp_4091_;
}
else
{
lean_object* v_a_4123_; lean_object* v___x_4125_; uint8_t v_isShared_4126_; uint8_t v_isSharedCheck_4130_; 
lean_dec(v_a_4090_);
lean_dec(v_a_4087_);
lean_dec_ref(v_body_4070_);
lean_dec(v_declName_4067_);
lean_dec(v_letFVars_4036_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_lctx_4033_);
v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4122_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4125_ = v___x_4122_;
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
else
{
lean_inc(v_a_4123_);
lean_dec(v___x_4122_);
v___x_4125_ = lean_box(0);
v_isShared_4126_ = v_isSharedCheck_4130_;
goto v_resetjp_4124_;
}
v_resetjp_4124_:
{
lean_object* v___x_4128_; 
if (v_isShared_4126_ == 0)
{
v___x_4128_ = v___x_4125_;
goto v_reusejp_4127_;
}
else
{
lean_object* v_reuseFailAlloc_4129_; 
v_reuseFailAlloc_4129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4129_, 0, v_a_4123_);
v___x_4128_ = v_reuseFailAlloc_4129_;
goto v_reusejp_4127_;
}
v_reusejp_4127_:
{
return v___x_4128_;
}
}
}
}
else
{
v___y_4092_ = v_a_4037_;
v___y_4093_ = v_a_4038_;
v___y_4094_ = v_a_4039_;
v___y_4095_ = v_a_4040_;
v___y_4096_ = v_a_4041_;
v___y_4097_ = v_a_4042_;
goto v___jp_4091_;
}
v___jp_4091_:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v_expr_4100_; lean_object* v_expr_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4110_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v_expr_4100_ = lean_ctor_get(v_a_4087_, 0);
lean_inc_ref(v_expr_4100_);
lean_dec(v_a_4087_);
v_expr_4101_ = lean_ctor_get(v_a_4090_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v_a_4090_);
if (v_isSharedCheck_4110_ == 0)
{
lean_object* v_unused_4111_; 
v_unused_4111_ = lean_ctor_get(v_a_4090_, 1);
lean_dec(v_unused_4111_);
v___x_4103_ = v_a_4090_;
v_isShared_4104_ = v_isSharedCheck_4110_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_expr_4101_);
lean_dec(v_a_4090_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4110_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
uint8_t v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = 0;
lean_inc(v_a_4099_);
v___x_4106_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4033_, v_a_4099_, v_declName_4067_, v_expr_4100_, v_expr_4101_, v_nondep_4071_, v___x_4105_);
if (v_nondep_4071_ == 0)
{
lean_object* v___x_4108_; 
lean_inc(v_a_4099_);
if (v_isShared_4104_ == 0)
{
lean_ctor_set_tag(v___x_4103_, 1);
lean_ctor_set(v___x_4103_, 1, v_letFVars_4036_);
lean_ctor_set(v___x_4103_, 0, v_a_4099_);
v___x_4108_ = v___x_4103_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4099_);
lean_ctor_set(v_reuseFailAlloc_4109_, 1, v_letFVars_4036_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
v___y_4073_ = v___x_4106_;
v___y_4074_ = v___y_4095_;
v___y_4075_ = v___y_4096_;
v___y_4076_ = v___y_4093_;
v___y_4077_ = v___y_4092_;
v___y_4078_ = v___y_4094_;
v___y_4079_ = v_a_4099_;
v___y_4080_ = v___y_4097_;
v___y_4081_ = v___x_4108_;
goto v___jp_4072_;
}
}
else
{
lean_del_object(v___x_4103_);
v___y_4073_ = v___x_4106_;
v___y_4074_ = v___y_4095_;
v___y_4075_ = v___y_4096_;
v___y_4076_ = v___y_4093_;
v___y_4077_ = v___y_4092_;
v___y_4078_ = v___y_4094_;
v___y_4079_ = v_a_4099_;
v___y_4080_ = v___y_4097_;
v___y_4081_ = v_letFVars_4036_;
goto v___jp_4072_;
}
}
}
else
{
lean_object* v_a_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4119_; 
lean_dec(v_a_4090_);
lean_dec(v_a_4087_);
lean_dec_ref(v_body_4070_);
lean_dec(v_declName_4067_);
lean_dec(v_letFVars_4036_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_lctx_4033_);
v_a_4112_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4119_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4119_ == 0)
{
v___x_4114_ = v___x_4098_;
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_a_4112_);
lean_dec(v___x_4098_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4119_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4117_; 
if (v_isShared_4115_ == 0)
{
v___x_4117_ = v___x_4114_;
goto v_reusejp_4116_;
}
else
{
lean_object* v_reuseFailAlloc_4118_; 
v_reuseFailAlloc_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4118_, 0, v_a_4112_);
v___x_4117_ = v_reuseFailAlloc_4118_;
goto v_reusejp_4116_;
}
v_reusejp_4116_:
{
return v___x_4117_;
}
}
}
}
}
else
{
lean_dec(v_a_4087_);
lean_dec_ref(v_body_4070_);
lean_dec(v_declName_4067_);
lean_dec(v_letFVars_4036_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_lctx_4033_);
return v___x_4089_;
}
}
else
{
lean_dec_ref(v_body_4070_);
lean_dec_ref(v_value_4069_);
lean_dec(v_declName_4067_);
lean_dec(v_letFVars_4036_);
lean_dec_ref(v_fvars_4034_);
lean_dec_ref(v_lctx_4033_);
return v___x_4086_;
}
v___jp_4072_:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = l_Lean_Expr_fvar___override(v___y_4079_);
v___x_4083_ = lean_array_push(v_fvars_4034_, v___x_4082_);
v_lctx_4033_ = v___y_4073_;
v_fvars_4034_ = v___x_4083_;
v_e_4035_ = v_body_4070_;
v_letFVars_4036_ = v___y_4081_;
v_a_4037_ = v___y_4077_;
v_a_4038_ = v___y_4076_;
v_a_4039_ = v___y_4078_;
v_a_4040_ = v___y_4074_;
v_a_4041_ = v___y_4075_;
v_a_4042_ = v___y_4080_;
goto _start;
}
}
default: 
{
lean_object* v___f_4131_; lean_object* v___x_4132_; 
lean_inc_ref(v_fvars_4034_);
v___f_4131_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4131_, 0, v_fvars_4034_);
v___x_4132_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4034_, v_letFVars_4036_, v_lctx_4033_, v___f_4131_, v_e_4035_, v_a_4037_, v_a_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_);
lean_dec_ref(v_e_4035_);
lean_dec_ref(v_fvars_4034_);
return v___x_4132_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
uint32_t v___x_4141_; uint8_t v___x_4142_; 
v___x_4141_ = 5;
v___x_4142_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4133_, v___x_4141_);
if (v___x_4142_ == 0)
{
lean_object* v_lctx_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v_lctx_4143_ = lean_ctor_get(v_a_4136_, 2);
v___x_4144_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4134_);
lean_inc_ref(v_lctx_4143_);
v___x_4145_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4143_, v___x_4144_, v_e_4133_, v_a_4134_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_);
return v___x_4145_;
}
else
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4146_ = lean_box(0);
v___x_4147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4147_, 0, v_e_4133_);
lean_ctor_set(v___x_4147_, 1, v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
return v___x_4148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_){
_start:
{
lean_object* v_res_4157_; 
v_res_4157_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_, v_a_4154_, v_a_4155_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
lean_dec(v_a_4153_);
lean_dec_ref(v_a_4152_);
lean_dec(v_a_4151_);
lean_dec(v_a_4150_);
return v_res_4157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_){
_start:
{
switch(lean_obj_tag(v_e_4158_))
{
case 0:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4166_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4167_ = l_Lean_MessageData_ofExpr(v_e_4158_);
v___x_4168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4168_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4169_;
}
case 1:
{
lean_object* v___x_4170_; 
v___x_4170_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4158_, v___y_4161_, v___y_4163_, v___y_4164_);
return v___x_4170_;
}
case 2:
{
lean_object* v___x_4171_; 
v___x_4171_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4171_;
}
case 3:
{
lean_object* v_u_4172_; lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v_u_4172_ = lean_ctor_get(v_e_4158_, 0);
lean_inc(v_u_4172_);
v___x_4173_ = l_Lean_Level_succ___override(v_u_4172_);
v___x_4174_ = l_Lean_Expr_sort___override(v___x_4173_);
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_e_4158_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
return v___x_4177_;
}
case 4:
{
lean_object* v___x_4178_; 
v___x_4178_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4178_;
}
case 5:
{
lean_object* v___x_4179_; lean_object* v___x_4180_; 
lean_inc_ref(v_e_4158_);
v___x_4179_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4179_, 0, v_e_4158_);
v___x_4180_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4158_, v___x_4179_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4180_;
}
case 7:
{
lean_object* v___x_4181_; lean_object* v___x_4182_; 
lean_inc_ref(v_e_4158_);
v___x_4181_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4181_, 0, v_e_4158_);
v___x_4182_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4158_, v___x_4181_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4182_;
}
case 9:
{
lean_object* v_a_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; 
v_a_4183_ = lean_ctor_get(v_e_4158_, 0);
v___x_4184_ = l_Lean_Literal_type(v_a_4183_);
v___x_4185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
v___x_4186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4186_, 0, v_e_4158_);
lean_ctor_set(v___x_4186_, 1, v___x_4185_);
v___x_4187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
return v___x_4187_;
}
case 10:
{
lean_object* v_data_4188_; lean_object* v_expr_4189_; lean_object* v___x_4190_; 
v_data_4188_ = lean_ctor_get(v_e_4158_, 0);
v_expr_4189_ = lean_ctor_get(v_e_4158_, 1);
lean_inc_ref(v_expr_4189_);
v___x_4190_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4189_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4213_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4213_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4213_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v_expr_4195_; lean_object* v_type_x3f_4196_; lean_object* v___x_4198_; uint8_t v_isShared_4199_; uint8_t v_isSharedCheck_4212_; 
v_expr_4195_ = lean_ctor_get(v_a_4191_, 0);
v_type_x3f_4196_ = lean_ctor_get(v_a_4191_, 1);
v_isSharedCheck_4212_ = !lean_is_exclusive(v_a_4191_);
if (v_isSharedCheck_4212_ == 0)
{
v___x_4198_ = v_a_4191_;
v_isShared_4199_ = v_isSharedCheck_4212_;
goto v_resetjp_4197_;
}
else
{
lean_inc(v_type_x3f_4196_);
lean_inc(v_expr_4195_);
lean_dec(v_a_4191_);
v___x_4198_ = lean_box(0);
v_isShared_4199_ = v_isSharedCheck_4212_;
goto v_resetjp_4197_;
}
v_resetjp_4197_:
{
lean_object* v___y_4201_; size_t v___x_4208_; size_t v___x_4209_; uint8_t v___x_4210_; 
v___x_4208_ = lean_ptr_addr(v_expr_4189_);
v___x_4209_ = lean_ptr_addr(v_expr_4195_);
v___x_4210_ = lean_usize_dec_eq(v___x_4208_, v___x_4209_);
if (v___x_4210_ == 0)
{
lean_object* v___x_4211_; 
lean_inc(v_data_4188_);
lean_dec_ref_known(v_e_4158_, 2);
v___x_4211_ = l_Lean_Expr_mdata___override(v_data_4188_, v_expr_4195_);
v___y_4201_ = v___x_4211_;
goto v___jp_4200_;
}
else
{
lean_dec_ref(v_expr_4195_);
v___y_4201_ = v_e_4158_;
goto v___jp_4200_;
}
v___jp_4200_:
{
lean_object* v___x_4203_; 
if (v_isShared_4199_ == 0)
{
lean_ctor_set(v___x_4198_, 0, v___y_4201_);
v___x_4203_ = v___x_4198_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v___y_4201_);
lean_ctor_set(v_reuseFailAlloc_4207_, 1, v_type_x3f_4196_);
v___x_4203_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
lean_object* v___x_4205_; 
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v___x_4203_);
v___x_4205_ = v___x_4193_;
goto v_reusejp_4204_;
}
else
{
lean_object* v_reuseFailAlloc_4206_; 
v_reuseFailAlloc_4206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4206_, 0, v___x_4203_);
v___x_4205_ = v_reuseFailAlloc_4206_;
goto v_reusejp_4204_;
}
v_reusejp_4204_:
{
return v___x_4205_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4158_, 2);
return v___x_4190_;
}
}
case 11:
{
lean_object* v_typeName_4214_; lean_object* v_idx_4215_; lean_object* v_struct_4216_; lean_object* v___f_4217_; lean_object* v___x_4218_; 
v_typeName_4214_ = lean_ctor_get(v_e_4158_, 0);
v_idx_4215_ = lean_ctor_get(v_e_4158_, 1);
v_struct_4216_ = lean_ctor_get(v_e_4158_, 2);
lean_inc(v_idx_4215_);
lean_inc(v_typeName_4214_);
lean_inc_ref(v_e_4158_);
lean_inc_ref(v_struct_4216_);
v___f_4217_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4217_, 0, v_struct_4216_);
lean_closure_set(v___f_4217_, 1, v_e_4158_);
lean_closure_set(v___f_4217_, 2, v_typeName_4214_);
lean_closure_set(v___f_4217_, 3, v_idx_4215_);
v___x_4218_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4158_, v___f_4217_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4218_;
}
default: 
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
lean_inc_ref(v_e_4158_);
v___x_4219_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4219_, 0, v_e_4158_);
v___x_4220_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4158_, v___x_4219_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
return v___x_4220_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4221_; double v___x_4222_; 
v___x_4221_ = lean_unsigned_to_nat(1000000000u);
v___x_4222_ = lean_float_of_nat(v___x_4221_);
return v___x_4222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4223_, lean_object* v_a_4224_, lean_object* v_a_4225_, lean_object* v_a_4226_, lean_object* v_a_4227_, lean_object* v_a_4228_, lean_object* v_a_4229_){
_start:
{
lean_object* v_options_4231_; uint8_t v_hasTrace_4232_; 
v_options_4231_ = lean_ctor_get(v_a_4228_, 2);
v_hasTrace_4232_ = lean_ctor_get_uint8(v_options_4231_, sizeof(void*)*1);
if (v_hasTrace_4232_ == 0)
{
lean_object* v___x_4233_; 
v___x_4233_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
return v___x_4233_;
}
else
{
lean_object* v_inheritedTraceOptions_4234_; lean_object* v___f_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v_a_4243_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v_a_4258_; 
v_inheritedTraceOptions_4234_ = lean_ctor_get(v_a_4228_, 13);
lean_inc_ref(v_e_4223_);
v___f_4235_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4235_, 0, v_e_4223_);
v___x_4236_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4237_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4238_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4234_, v_options_4231_, v___x_4238_);
if (v___x_4239_ == 0)
{
lean_object* v___x_4316_; uint8_t v___x_4317_; 
v___x_4316_ = l_Lean_trace_profiler;
v___x_4317_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4231_, v___x_4316_);
if (v___x_4317_ == 0)
{
lean_object* v___x_4318_; 
lean_dec_ref(v___f_4235_);
v___x_4318_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
return v___x_4318_;
}
else
{
goto v___jp_4267_;
}
}
else
{
goto v___jp_4267_;
}
v___jp_4240_:
{
lean_object* v___x_4244_; double v___x_4245_; double v___x_4246_; double v___x_4247_; double v___x_4248_; double v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; 
v___x_4244_ = lean_io_mono_nanos_now();
v___x_4245_ = lean_float_of_nat(v___y_4242_);
v___x_4246_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4247_ = lean_float_div(v___x_4245_, v___x_4246_);
v___x_4248_ = lean_float_of_nat(v___x_4244_);
v___x_4249_ = lean_float_div(v___x_4248_, v___x_4246_);
v___x_4250_ = lean_box_float(v___x_4247_);
v___x_4251_ = lean_box_float(v___x_4249_);
v___x_4252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4253_, 0, v_a_4243_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4236_, v_hasTrace_4232_, v___x_4237_, v_options_4231_, v___x_4239_, v___y_4241_, v___f_4235_, v___x_4253_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
return v___x_4254_;
}
v___jp_4255_:
{
lean_object* v___x_4259_; double v___x_4260_; double v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v___x_4259_ = lean_io_get_num_heartbeats();
v___x_4260_ = lean_float_of_nat(v___y_4256_);
v___x_4261_ = lean_float_of_nat(v___x_4259_);
v___x_4262_ = lean_box_float(v___x_4260_);
v___x_4263_ = lean_box_float(v___x_4261_);
v___x_4264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4264_, 0, v___x_4262_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
v___x_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4265_, 0, v_a_4258_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4236_, v_hasTrace_4232_, v___x_4237_, v_options_4231_, v___x_4239_, v___y_4257_, v___f_4235_, v___x_4265_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
return v___x_4266_;
}
v___jp_4267_:
{
lean_object* v___x_4268_; 
v___x_4268_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4229_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4270_; uint8_t v___x_4271_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4268_, 1);
v___x_4270_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4271_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4231_, v___x_4270_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4272_ = lean_io_mono_nanos_now();
v___x_4273_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
if (lean_obj_tag(v___x_4273_) == 0)
{
lean_object* v_a_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4281_; 
v_a_4274_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4281_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4281_ == 0)
{
v___x_4276_ = v___x_4273_;
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_a_4274_);
lean_dec(v___x_4273_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4281_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v___x_4279_; 
if (v_isShared_4277_ == 0)
{
lean_ctor_set_tag(v___x_4276_, 1);
v___x_4279_ = v___x_4276_;
goto v_reusejp_4278_;
}
else
{
lean_object* v_reuseFailAlloc_4280_; 
v_reuseFailAlloc_4280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
v___x_4279_ = v_reuseFailAlloc_4280_;
goto v_reusejp_4278_;
}
v_reusejp_4278_:
{
v___y_4241_ = v_a_4269_;
v___y_4242_ = v___x_4272_;
v_a_4243_ = v___x_4279_;
goto v___jp_4240_;
}
}
}
else
{
lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4289_; 
v_a_4282_ = lean_ctor_get(v___x_4273_, 0);
v_isSharedCheck_4289_ = !lean_is_exclusive(v___x_4273_);
if (v_isSharedCheck_4289_ == 0)
{
v___x_4284_ = v___x_4273_;
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4273_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4289_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4287_; 
if (v_isShared_4285_ == 0)
{
lean_ctor_set_tag(v___x_4284_, 0);
v___x_4287_ = v___x_4284_;
goto v_reusejp_4286_;
}
else
{
lean_object* v_reuseFailAlloc_4288_; 
v_reuseFailAlloc_4288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4288_, 0, v_a_4282_);
v___x_4287_ = v_reuseFailAlloc_4288_;
goto v_reusejp_4286_;
}
v_reusejp_4286_:
{
v___y_4241_ = v_a_4269_;
v___y_4242_ = v___x_4272_;
v_a_4243_ = v___x_4287_;
goto v___jp_4240_;
}
}
}
}
else
{
lean_object* v___x_4290_; lean_object* v___x_4291_; 
v___x_4290_ = lean_io_get_num_heartbeats();
v___x_4291_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4223_, v_a_4224_, v_a_4225_, v_a_4226_, v_a_4227_, v_a_4228_, v_a_4229_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4291_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4291_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
lean_ctor_set_tag(v___x_4294_, 1);
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
v___y_4256_ = v___x_4290_;
v___y_4257_ = v_a_4269_;
v_a_4258_ = v___x_4297_;
goto v___jp_4255_;
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
v_a_4300_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4291_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4291_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set_tag(v___x_4302_, 0);
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
v___y_4256_ = v___x_4290_;
v___y_4257_ = v_a_4269_;
v_a_4258_ = v___x_4305_;
goto v___jp_4255_;
}
}
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
lean_dec_ref(v___f_4235_);
lean_dec_ref(v_e_4223_);
v_a_4308_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___x_4268_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4268_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
return v___x_4313_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4319_, lean_object* v_e_4320_, lean_object* v_typeName_4321_, lean_object* v_idx_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_){
_start:
{
lean_object* v___x_4330_; 
v___x_4330_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4319_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v_a_4331_; lean_object* v___x_4332_; 
v_a_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc(v_a_4331_);
lean_dec_ref_known(v___x_4330_, 1);
v___x_4332_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4320_, v_typeName_4321_, v_idx_4322_, v_a_4331_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_, v___y_4328_);
return v___x_4332_;
}
else
{
lean_dec(v_idx_4322_);
lean_dec(v_typeName_4321_);
lean_dec_ref(v_e_4320_);
return v___x_4330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_, v_a_4338_, v_a_4339_);
lean_dec(v_a_4339_);
lean_dec_ref(v_a_4338_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
lean_dec(v_a_4335_);
lean_dec(v_a_4334_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4342_, lean_object* v_fvars_4343_, lean_object* v_doms_4344_, lean_object* v_e_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4342_, v_fvars_4343_, v_doms_4344_, v_e_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec(v_a_4346_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
lean_object* v_res_4362_; 
v_res_4362_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec(v___y_4355_);
return v_res_4362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4363_, lean_object* v_fvars_4364_, lean_object* v_e_4365_, lean_object* v_letFVars_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_, lean_object* v_a_4371_, lean_object* v_a_4372_, lean_object* v_a_4373_){
_start:
{
lean_object* v_res_4374_; 
v_res_4374_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4363_, v_fvars_4364_, v_e_4365_, v_letFVars_4366_, v_a_4367_, v_a_4368_, v_a_4369_, v_a_4370_, v_a_4371_, v_a_4372_);
lean_dec(v_a_4372_);
lean_dec_ref(v_a_4371_);
lean_dec(v_a_4370_);
lean_dec_ref(v_a_4369_);
lean_dec(v_a_4368_);
lean_dec(v_a_4367_);
return v_res_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4375_, lean_object* v_lctx_4376_, lean_object* v_localInsts_4377_, lean_object* v_x_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_){
_start:
{
lean_object* v___x_4386_; 
v___x_4386_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4376_, v_localInsts_4377_, v_x_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
return v___x_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4387_, lean_object* v_lctx_4388_, lean_object* v_localInsts_4389_, lean_object* v_x_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4387_, v_lctx_4388_, v_localInsts_4389_, v_x_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
lean_dec(v___y_4391_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4399_, lean_object* v_lctx_4400_, lean_object* v_x_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___x_4409_; 
v___x_4409_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4400_, v_x_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
return v___x_4409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4410_, lean_object* v_lctx_4411_, lean_object* v_x_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v_res_4420_; 
v_res_4420_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4410_, v_lctx_4411_, v_x_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec_ref(v___y_4415_);
lean_dec(v___y_4414_);
lean_dec(v___y_4413_);
return v_res_4420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v___x_4428_; 
v___x_4428_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4426_);
return v___x_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_){
_start:
{
lean_object* v_res_4436_; 
v_res_4436_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4429_, v___y_4430_, v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec_ref(v___y_4431_);
lean_dec(v___y_4430_);
lean_dec(v___y_4429_);
return v_res_4436_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v___x_4444_; 
v___x_4444_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4442_);
return v___x_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v_res_4452_; 
v_res_4452_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_, v___y_4450_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec(v___y_4448_);
lean_dec_ref(v___y_4447_);
lean_dec(v___y_4446_);
lean_dec(v___y_4445_);
return v_res_4452_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4453_, lean_object* v_x_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_){
_start:
{
lean_object* v___x_4462_; 
v___x_4462_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4454_);
return v___x_4462_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4463_, lean_object* v_x_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_){
_start:
{
lean_object* v_res_4472_; 
v_res_4472_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4463_, v_x_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_, v___y_4469_, v___y_4470_);
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
lean_dec(v___y_4468_);
lean_dec_ref(v___y_4467_);
lean_dec(v___y_4466_);
lean_dec(v___y_4465_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4473_, lean_object* v_data_4474_, lean_object* v_ref_4475_, lean_object* v_msg_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_){
_start:
{
lean_object* v___x_4484_; 
v___x_4484_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4473_, v_data_4474_, v_ref_4475_, v_msg_4476_, v___y_4479_, v___y_4480_, v___y_4481_, v___y_4482_);
return v___x_4484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4485_, lean_object* v_data_4486_, lean_object* v_ref_4487_, lean_object* v_msg_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v_res_4496_; 
v_res_4496_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4485_, v_data_4486_, v_ref_4487_, v_msg_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
lean_dec(v___y_4494_);
lean_dec_ref(v___y_4493_);
lean_dec(v___y_4492_);
lean_dec_ref(v___y_4491_);
lean_dec(v___y_4490_);
lean_dec(v___y_4489_);
return v_res_4496_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4497_){
_start:
{
lean_object* v___x_4499_; lean_object* v_traceState_4500_; lean_object* v_traces_4501_; lean_object* v___x_4502_; lean_object* v_traceState_4503_; lean_object* v_env_4504_; lean_object* v_nextMacroScope_4505_; lean_object* v_ngen_4506_; lean_object* v_auxDeclNGen_4507_; lean_object* v_cache_4508_; lean_object* v_messages_4509_; lean_object* v_infoState_4510_; lean_object* v_snapshotTasks_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4532_; 
v___x_4499_ = lean_st_ref_get(v___y_4497_);
v_traceState_4500_ = lean_ctor_get(v___x_4499_, 4);
lean_inc_ref(v_traceState_4500_);
lean_dec(v___x_4499_);
v_traces_4501_ = lean_ctor_get(v_traceState_4500_, 0);
lean_inc_ref(v_traces_4501_);
lean_dec_ref(v_traceState_4500_);
v___x_4502_ = lean_st_ref_take(v___y_4497_);
v_traceState_4503_ = lean_ctor_get(v___x_4502_, 4);
v_env_4504_ = lean_ctor_get(v___x_4502_, 0);
v_nextMacroScope_4505_ = lean_ctor_get(v___x_4502_, 1);
v_ngen_4506_ = lean_ctor_get(v___x_4502_, 2);
v_auxDeclNGen_4507_ = lean_ctor_get(v___x_4502_, 3);
v_cache_4508_ = lean_ctor_get(v___x_4502_, 5);
v_messages_4509_ = lean_ctor_get(v___x_4502_, 6);
v_infoState_4510_ = lean_ctor_get(v___x_4502_, 7);
v_snapshotTasks_4511_ = lean_ctor_get(v___x_4502_, 8);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4513_ = v___x_4502_;
v_isShared_4514_ = v_isSharedCheck_4532_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_snapshotTasks_4511_);
lean_inc(v_infoState_4510_);
lean_inc(v_messages_4509_);
lean_inc(v_cache_4508_);
lean_inc(v_traceState_4503_);
lean_inc(v_auxDeclNGen_4507_);
lean_inc(v_ngen_4506_);
lean_inc(v_nextMacroScope_4505_);
lean_inc(v_env_4504_);
lean_dec(v___x_4502_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4532_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
uint64_t v_tid_4515_; lean_object* v___x_4517_; uint8_t v_isShared_4518_; uint8_t v_isSharedCheck_4530_; 
v_tid_4515_ = lean_ctor_get_uint64(v_traceState_4503_, sizeof(void*)*1);
v_isSharedCheck_4530_ = !lean_is_exclusive(v_traceState_4503_);
if (v_isSharedCheck_4530_ == 0)
{
lean_object* v_unused_4531_; 
v_unused_4531_ = lean_ctor_get(v_traceState_4503_, 0);
lean_dec(v_unused_4531_);
v___x_4517_ = v_traceState_4503_;
v_isShared_4518_ = v_isSharedCheck_4530_;
goto v_resetjp_4516_;
}
else
{
lean_dec(v_traceState_4503_);
v___x_4517_ = lean_box(0);
v_isShared_4518_ = v_isSharedCheck_4530_;
goto v_resetjp_4516_;
}
v_resetjp_4516_:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___x_4523_; 
v___x_4519_ = lean_unsigned_to_nat(32u);
v___x_4520_ = lean_mk_empty_array_with_capacity(v___x_4519_);
lean_dec_ref(v___x_4520_);
v___x_4521_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4518_ == 0)
{
lean_ctor_set(v___x_4517_, 0, v___x_4521_);
v___x_4523_ = v___x_4517_;
goto v_reusejp_4522_;
}
else
{
lean_object* v_reuseFailAlloc_4529_; 
v_reuseFailAlloc_4529_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4529_, 0, v___x_4521_);
lean_ctor_set_uint64(v_reuseFailAlloc_4529_, sizeof(void*)*1, v_tid_4515_);
v___x_4523_ = v_reuseFailAlloc_4529_;
goto v_reusejp_4522_;
}
v_reusejp_4522_:
{
lean_object* v___x_4525_; 
if (v_isShared_4514_ == 0)
{
lean_ctor_set(v___x_4513_, 4, v___x_4523_);
v___x_4525_ = v___x_4513_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_env_4504_);
lean_ctor_set(v_reuseFailAlloc_4528_, 1, v_nextMacroScope_4505_);
lean_ctor_set(v_reuseFailAlloc_4528_, 2, v_ngen_4506_);
lean_ctor_set(v_reuseFailAlloc_4528_, 3, v_auxDeclNGen_4507_);
lean_ctor_set(v_reuseFailAlloc_4528_, 4, v___x_4523_);
lean_ctor_set(v_reuseFailAlloc_4528_, 5, v_cache_4508_);
lean_ctor_set(v_reuseFailAlloc_4528_, 6, v_messages_4509_);
lean_ctor_set(v_reuseFailAlloc_4528_, 7, v_infoState_4510_);
lean_ctor_set(v_reuseFailAlloc_4528_, 8, v_snapshotTasks_4511_);
v___x_4525_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; 
v___x_4526_ = lean_st_ref_set(v___y_4497_, v___x_4525_);
v___x_4527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4527_, 0, v_traces_4501_);
return v___x_4527_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4533_, lean_object* v___y_4534_){
_start:
{
lean_object* v_res_4535_; 
v_res_4535_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4533_);
lean_dec(v___y_4533_);
return v_res_4535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v___x_4541_; 
v___x_4541_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4539_);
return v___x_4541_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v_res_4547_; 
v_res_4547_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4542_, v___y_4543_, v___y_4544_, v___y_4545_);
lean_dec(v___y_4545_);
lean_dec_ref(v___y_4544_);
lean_dec(v___y_4543_);
lean_dec_ref(v___y_4542_);
return v_res_4547_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4548_, lean_object* v_zetaDeltaFVarIds_4549_, lean_object* v_a_x3f_4550_){
_start:
{
lean_object* v___x_4552_; lean_object* v_mctx_4553_; lean_object* v_cache_4554_; lean_object* v_postponed_4555_; lean_object* v_diag_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4566_; 
v___x_4552_ = lean_st_ref_take(v___y_4548_);
v_mctx_4553_ = lean_ctor_get(v___x_4552_, 0);
v_cache_4554_ = lean_ctor_get(v___x_4552_, 1);
v_postponed_4555_ = lean_ctor_get(v___x_4552_, 3);
v_diag_4556_ = lean_ctor_get(v___x_4552_, 4);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; 
v_unused_4567_ = lean_ctor_get(v___x_4552_, 2);
lean_dec(v_unused_4567_);
v___x_4558_ = v___x_4552_;
v_isShared_4559_ = v_isSharedCheck_4566_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_diag_4556_);
lean_inc(v_postponed_4555_);
lean_inc(v_cache_4554_);
lean_inc(v_mctx_4553_);
lean_dec(v___x_4552_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4566_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4561_; 
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 2, v_zetaDeltaFVarIds_4549_);
v___x_4561_ = v___x_4558_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_mctx_4553_);
lean_ctor_set(v_reuseFailAlloc_4565_, 1, v_cache_4554_);
lean_ctor_set(v_reuseFailAlloc_4565_, 2, v_zetaDeltaFVarIds_4549_);
lean_ctor_set(v_reuseFailAlloc_4565_, 3, v_postponed_4555_);
lean_ctor_set(v_reuseFailAlloc_4565_, 4, v_diag_4556_);
v___x_4561_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4560_;
}
v_reusejp_4560_:
{
lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4564_; 
v___x_4562_ = lean_st_ref_set(v___y_4548_, v___x_4561_);
v___x_4563_ = lean_box(0);
v___x_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4564_, 0, v___x_4563_);
return v___x_4564_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4568_, lean_object* v_zetaDeltaFVarIds_4569_, lean_object* v_a_x3f_4570_, lean_object* v___y_4571_){
_start:
{
lean_object* v_res_4572_; 
v_res_4572_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4568_, v_zetaDeltaFVarIds_4569_, v_a_x3f_4570_);
lean_dec(v_a_x3f_4570_);
lean_dec(v___y_4568_);
return v_res_4572_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4573_, lean_object* v_msg_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v_ref_4580_; lean_object* v___x_4581_; lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4626_; 
v_ref_4580_ = lean_ctor_get(v___y_4577_, 5);
v___x_4581_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4574_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4626_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4626_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4586_; lean_object* v_traceState_4587_; lean_object* v_env_4588_; lean_object* v_nextMacroScope_4589_; lean_object* v_ngen_4590_; lean_object* v_auxDeclNGen_4591_; lean_object* v_cache_4592_; lean_object* v_messages_4593_; lean_object* v_infoState_4594_; lean_object* v_snapshotTasks_4595_; lean_object* v___x_4597_; uint8_t v_isShared_4598_; uint8_t v_isSharedCheck_4625_; 
v___x_4586_ = lean_st_ref_take(v___y_4578_);
v_traceState_4587_ = lean_ctor_get(v___x_4586_, 4);
v_env_4588_ = lean_ctor_get(v___x_4586_, 0);
v_nextMacroScope_4589_ = lean_ctor_get(v___x_4586_, 1);
v_ngen_4590_ = lean_ctor_get(v___x_4586_, 2);
v_auxDeclNGen_4591_ = lean_ctor_get(v___x_4586_, 3);
v_cache_4592_ = lean_ctor_get(v___x_4586_, 5);
v_messages_4593_ = lean_ctor_get(v___x_4586_, 6);
v_infoState_4594_ = lean_ctor_get(v___x_4586_, 7);
v_snapshotTasks_4595_ = lean_ctor_get(v___x_4586_, 8);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4597_ = v___x_4586_;
v_isShared_4598_ = v_isSharedCheck_4625_;
goto v_resetjp_4596_;
}
else
{
lean_inc(v_snapshotTasks_4595_);
lean_inc(v_infoState_4594_);
lean_inc(v_messages_4593_);
lean_inc(v_cache_4592_);
lean_inc(v_traceState_4587_);
lean_inc(v_auxDeclNGen_4591_);
lean_inc(v_ngen_4590_);
lean_inc(v_nextMacroScope_4589_);
lean_inc(v_env_4588_);
lean_dec(v___x_4586_);
v___x_4597_ = lean_box(0);
v_isShared_4598_ = v_isSharedCheck_4625_;
goto v_resetjp_4596_;
}
v_resetjp_4596_:
{
uint64_t v_tid_4599_; lean_object* v_traces_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4624_; 
v_tid_4599_ = lean_ctor_get_uint64(v_traceState_4587_, sizeof(void*)*1);
v_traces_4600_ = lean_ctor_get(v_traceState_4587_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v_traceState_4587_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4602_ = v_traceState_4587_;
v_isShared_4603_ = v_isSharedCheck_4624_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_traces_4600_);
lean_dec(v_traceState_4587_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4624_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
lean_object* v___x_4604_; double v___x_4605_; uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
v___x_4604_ = lean_box(0);
v___x_4605_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4606_ = 0;
v___x_4607_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4608_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4608_, 0, v_cls_4573_);
lean_ctor_set(v___x_4608_, 1, v___x_4604_);
lean_ctor_set(v___x_4608_, 2, v___x_4607_);
lean_ctor_set_float(v___x_4608_, sizeof(void*)*3, v___x_4605_);
lean_ctor_set_float(v___x_4608_, sizeof(void*)*3 + 8, v___x_4605_);
lean_ctor_set_uint8(v___x_4608_, sizeof(void*)*3 + 16, v___x_4606_);
v___x_4609_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4610_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4610_, 0, v___x_4608_);
lean_ctor_set(v___x_4610_, 1, v_a_4582_);
lean_ctor_set(v___x_4610_, 2, v___x_4609_);
lean_inc(v_ref_4580_);
v___x_4611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4611_, 0, v_ref_4580_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
v___x_4612_ = l_Lean_PersistentArray_push___redArg(v_traces_4600_, v___x_4611_);
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4612_);
v___x_4614_ = v___x_4602_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4612_);
lean_ctor_set_uint64(v_reuseFailAlloc_4623_, sizeof(void*)*1, v_tid_4599_);
v___x_4614_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
lean_object* v___x_4616_; 
if (v_isShared_4598_ == 0)
{
lean_ctor_set(v___x_4597_, 4, v___x_4614_);
v___x_4616_ = v___x_4597_;
goto v_reusejp_4615_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_env_4588_);
lean_ctor_set(v_reuseFailAlloc_4622_, 1, v_nextMacroScope_4589_);
lean_ctor_set(v_reuseFailAlloc_4622_, 2, v_ngen_4590_);
lean_ctor_set(v_reuseFailAlloc_4622_, 3, v_auxDeclNGen_4591_);
lean_ctor_set(v_reuseFailAlloc_4622_, 4, v___x_4614_);
lean_ctor_set(v_reuseFailAlloc_4622_, 5, v_cache_4592_);
lean_ctor_set(v_reuseFailAlloc_4622_, 6, v_messages_4593_);
lean_ctor_set(v_reuseFailAlloc_4622_, 7, v_infoState_4594_);
lean_ctor_set(v_reuseFailAlloc_4622_, 8, v_snapshotTasks_4595_);
v___x_4616_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4615_;
}
v_reusejp_4615_:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4620_; 
v___x_4617_ = lean_st_ref_set(v___y_4578_, v___x_4616_);
v___x_4618_ = lean_box(0);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v___x_4618_);
v___x_4620_ = v___x_4584_;
goto v_reusejp_4619_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4618_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4627_, lean_object* v_msg_4628_, lean_object* v___y_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v_res_4634_; 
v_res_4634_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4627_, v_msg_4628_, v___y_4629_, v___y_4630_, v___y_4631_, v___y_4632_);
lean_dec(v___y_4632_);
lean_dec_ref(v___y_4631_);
lean_dec(v___y_4630_);
lean_dec_ref(v___y_4629_);
return v_res_4634_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4637_ = l_Lean_stringToMessageData(v___x_4636_);
return v___x_4637_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; 
v___x_4639_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4640_ = l_Lean_stringToMessageData(v___x_4639_);
return v___x_4640_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4642_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4643_ = l_Lean_stringToMessageData(v___x_4642_);
return v___x_4643_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4645_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4646_ = l_Lean_stringToMessageData(v___x_4645_);
return v___x_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4647_, lean_object* v_e_4648_, lean_object* v___x_4649_, lean_object* v___x_4650_, lean_object* v_cls_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
v___x_4657_ = lean_st_mk_ref(v___x_4647_);
v___x_4658_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4648_, v___x_4649_, v___x_4657_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4728_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4728_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4728_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
lean_object* v___x_4663_; lean_object* v_count_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4726_; 
v___x_4663_ = lean_st_ref_get(v___x_4657_);
lean_dec(v___x_4657_);
v_count_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4726_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4726_ == 0)
{
lean_object* v_unused_4727_; 
v_unused_4727_ = lean_ctor_get(v___x_4663_, 1);
lean_dec(v_unused_4727_);
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4726_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_count_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4726_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
uint8_t v___x_4690_; 
v___x_4690_ = lean_nat_dec_eq(v_count_4664_, v___x_4650_);
if (v___x_4690_ == 0)
{
lean_object* v_options_4691_; uint8_t v_hasTrace_4692_; 
v_options_4691_ = lean_ctor_get(v___y_4654_, 2);
v_hasTrace_4692_ = lean_ctor_get_uint8(v_options_4691_, sizeof(void*)*1);
if (v_hasTrace_4692_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v_inheritedTraceOptions_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v_inheritedTraceOptions_4693_ = lean_ctor_get(v___y_4654_, 13);
v___x_4694_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4651_);
v___x_4695_ = l_Lean_Name_append(v___x_4694_, v_cls_4651_);
v___x_4696_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4693_, v_options_4691_, v___x_4695_);
lean_dec(v___x_4695_);
if (v___x_4696_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v_expr_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; 
v_expr_4697_ = lean_ctor_get(v_a_4659_, 0);
v___x_4698_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4697_);
v___x_4699_ = l_Lean_indentExpr(v_expr_4697_);
v___x_4700_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4700_, 0, v___x_4698_);
lean_ctor_set(v___x_4700_, 1, v___x_4699_);
v___x_4701_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4651_, v___x_4700_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_dec_ref_known(v___x_4701_, 1);
goto v___jp_4668_;
}
else
{
lean_object* v_a_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4709_; 
lean_del_object(v___x_4666_);
lean_dec(v_count_4664_);
lean_del_object(v___x_4661_);
lean_dec(v_a_4659_);
v_a_4702_ = lean_ctor_get(v___x_4701_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4701_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4704_ = v___x_4701_;
v_isShared_4705_ = v_isSharedCheck_4709_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_a_4702_);
lean_dec(v___x_4701_);
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
}
else
{
lean_object* v_options_4710_; uint8_t v_hasTrace_4711_; 
v_options_4710_ = lean_ctor_get(v___y_4654_, 2);
v_hasTrace_4711_ = lean_ctor_get_uint8(v_options_4710_, sizeof(void*)*1);
if (v_hasTrace_4711_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v_inheritedTraceOptions_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; uint8_t v___x_4715_; 
v_inheritedTraceOptions_4712_ = lean_ctor_get(v___y_4654_, 13);
v___x_4713_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4651_);
v___x_4714_ = l_Lean_Name_append(v___x_4713_, v_cls_4651_);
v___x_4715_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4712_, v_options_4710_, v___x_4714_);
lean_dec(v___x_4714_);
if (v___x_4715_ == 0)
{
lean_dec(v_cls_4651_);
goto v___jp_4668_;
}
else
{
lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4716_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4717_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4651_, v___x_4716_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_dec_ref_known(v___x_4717_, 1);
goto v___jp_4668_;
}
else
{
lean_object* v_a_4718_; lean_object* v___x_4720_; uint8_t v_isShared_4721_; uint8_t v_isSharedCheck_4725_; 
lean_del_object(v___x_4666_);
lean_dec(v_count_4664_);
lean_del_object(v___x_4661_);
lean_dec(v_a_4659_);
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4717_);
if (v_isSharedCheck_4725_ == 0)
{
v___x_4720_ = v___x_4717_;
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
else
{
lean_inc(v_a_4718_);
lean_dec(v___x_4717_);
v___x_4720_ = lean_box(0);
v_isShared_4721_ = v_isSharedCheck_4725_;
goto v_resetjp_4719_;
}
v_resetjp_4719_:
{
lean_object* v___x_4723_; 
if (v_isShared_4721_ == 0)
{
v___x_4723_ = v___x_4720_;
goto v_reusejp_4722_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_a_4718_);
v___x_4723_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4722_;
}
v_reusejp_4722_:
{
return v___x_4723_;
}
}
}
}
}
}
v___jp_4668_:
{
lean_object* v_expr_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4688_; 
v_expr_4669_ = lean_ctor_get(v_a_4659_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v_a_4659_);
if (v_isSharedCheck_4688_ == 0)
{
lean_object* v_unused_4689_; 
v_unused_4689_ = lean_ctor_get(v_a_4659_, 1);
lean_dec(v_unused_4689_);
v___x_4671_ = v_a_4659_;
v_isShared_4672_ = v_isSharedCheck_4688_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_expr_4669_);
lean_dec(v_a_4659_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4688_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; lean_object* v___x_4678_; 
v___x_4673_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4674_ = l_Nat_reprFast(v_count_4664_);
v___x_4675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4675_, 0, v___x_4674_);
v___x_4676_ = l_Lean_MessageData_ofFormat(v___x_4675_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set_tag(v___x_4671_, 7);
lean_ctor_set(v___x_4671_, 1, v___x_4676_);
lean_ctor_set(v___x_4671_, 0, v___x_4673_);
v___x_4678_ = v___x_4671_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4673_);
lean_ctor_set(v_reuseFailAlloc_4687_, 1, v___x_4676_);
v___x_4678_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
lean_object* v___x_4679_; lean_object* v___x_4681_; 
v___x_4679_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4667_ == 0)
{
lean_ctor_set_tag(v___x_4666_, 7);
lean_ctor_set(v___x_4666_, 1, v___x_4679_);
lean_ctor_set(v___x_4666_, 0, v___x_4678_);
v___x_4681_ = v___x_4666_;
goto v_reusejp_4680_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4678_);
lean_ctor_set(v_reuseFailAlloc_4686_, 1, v___x_4679_);
v___x_4681_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4680_;
}
v_reusejp_4680_:
{
lean_object* v___x_4682_; lean_object* v___x_4684_; 
v___x_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4682_, 0, v_expr_4669_);
lean_ctor_set(v___x_4682_, 1, v___x_4681_);
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4682_);
v___x_4684_ = v___x_4661_;
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
}
}
}
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
lean_dec(v___x_4657_);
lean_dec(v_cls_4651_);
v_a_4729_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4658_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4658_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4737_, lean_object* v_e_4738_, lean_object* v___x_4739_, lean_object* v___x_4740_, lean_object* v_cls_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v_res_4747_; 
v_res_4747_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4737_, v_e_4738_, v___x_4739_, v___x_4740_, v_cls_4741_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
lean_dec(v___x_4740_);
lean_dec(v___x_4739_);
return v_res_4747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4748_, lean_object* v_cache_4749_, lean_object* v_a_x3f_4750_){
_start:
{
lean_object* v___x_4752_; lean_object* v_mctx_4753_; lean_object* v_zetaDeltaFVarIds_4754_; lean_object* v_postponed_4755_; lean_object* v_diag_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4766_; 
v___x_4752_ = lean_st_ref_take(v___y_4748_);
v_mctx_4753_ = lean_ctor_get(v___x_4752_, 0);
v_zetaDeltaFVarIds_4754_ = lean_ctor_get(v___x_4752_, 2);
v_postponed_4755_ = lean_ctor_get(v___x_4752_, 3);
v_diag_4756_ = lean_ctor_get(v___x_4752_, 4);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4752_);
if (v_isSharedCheck_4766_ == 0)
{
lean_object* v_unused_4767_; 
v_unused_4767_ = lean_ctor_get(v___x_4752_, 1);
lean_dec(v_unused_4767_);
v___x_4758_ = v___x_4752_;
v_isShared_4759_ = v_isSharedCheck_4766_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_diag_4756_);
lean_inc(v_postponed_4755_);
lean_inc(v_zetaDeltaFVarIds_4754_);
lean_inc(v_mctx_4753_);
lean_dec(v___x_4752_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4766_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
lean_ctor_set(v___x_4758_, 1, v_cache_4749_);
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_mctx_4753_);
lean_ctor_set(v_reuseFailAlloc_4765_, 1, v_cache_4749_);
lean_ctor_set(v_reuseFailAlloc_4765_, 2, v_zetaDeltaFVarIds_4754_);
lean_ctor_set(v_reuseFailAlloc_4765_, 3, v_postponed_4755_);
lean_ctor_set(v_reuseFailAlloc_4765_, 4, v_diag_4756_);
v___x_4761_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4762_ = lean_st_ref_set(v___y_4748_, v___x_4761_);
v___x_4763_ = lean_box(0);
v___x_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4764_, 0, v___x_4763_);
return v___x_4764_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4768_, lean_object* v_cache_4769_, lean_object* v_a_x3f_4770_, lean_object* v___y_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4768_, v_cache_4769_, v_a_x3f_4770_);
lean_dec(v_a_x3f_4770_);
lean_dec(v___y_4768_);
return v_res_4772_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2(void){
_start:
{
lean_object* v___x_4776_; lean_object* v___x_4777_; 
v___x_4776_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1));
v___x_4777_ = l_Lean_MessageData_ofFormat(v___x_4776_);
return v___x_4777_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3(void){
_start:
{
lean_object* v___x_4778_; 
v___x_4778_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4778_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4(void){
_start:
{
lean_object* v___x_4779_; lean_object* v___x_4780_; 
v___x_4779_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3);
v___x_4780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4779_);
return v___x_4780_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5(void){
_start:
{
lean_object* v___x_4781_; lean_object* v___x_4782_; 
v___x_4781_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4);
v___x_4782_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4781_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
lean_ctor_set(v___x_4782_, 2, v___x_4781_);
lean_ctor_set(v___x_4782_, 3, v___x_4781_);
lean_ctor_set(v___x_4782_, 4, v___x_4781_);
lean_ctor_set(v___x_4782_, 5, v___x_4781_);
return v___x_4782_;
}
}
static uint64_t _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6(void){
_start:
{
uint8_t v___x_4783_; uint64_t v___x_4784_; 
v___x_4783_ = 0;
v___x_4784_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_4783_);
return v___x_4784_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7(void){
_start:
{
lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4785_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4786_ = lean_unsigned_to_nat(0u);
v___x_4787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
lean_ctor_set(v___x_4787_, 1, v___x_4785_);
return v___x_4787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_4788_, lean_object* v_e_4789_, uint8_t v___x_4790_, lean_object* v_cls_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
if (v___x_4788_ == 0)
{
lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
lean_dec(v_cls_4791_);
v___x_4797_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2);
v___x_4798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4798_, 0, v_e_4789_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
v___x_4799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4798_);
return v___x_4799_;
}
else
{
lean_object* v___x_4800_; lean_object* v___x_4801_; lean_object* v_mctx_4802_; lean_object* v_zetaDeltaFVarIds_4803_; lean_object* v_postponed_4804_; lean_object* v_diag_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4993_; 
v___x_4800_ = lean_st_ref_get(v___y_4793_);
v___x_4801_ = lean_st_ref_take(v___y_4793_);
v_mctx_4802_ = lean_ctor_get(v___x_4801_, 0);
v_zetaDeltaFVarIds_4803_ = lean_ctor_get(v___x_4801_, 2);
v_postponed_4804_ = lean_ctor_get(v___x_4801_, 3);
v_diag_4805_ = lean_ctor_get(v___x_4801_, 4);
v_isSharedCheck_4993_ = !lean_is_exclusive(v___x_4801_);
if (v_isSharedCheck_4993_ == 0)
{
lean_object* v_unused_4994_; 
v_unused_4994_ = lean_ctor_get(v___x_4801_, 1);
lean_dec(v_unused_4994_);
v___x_4807_ = v___x_4801_;
v_isShared_4808_ = v_isSharedCheck_4993_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_diag_4805_);
lean_inc(v_postponed_4804_);
lean_inc(v_zetaDeltaFVarIds_4803_);
lean_inc(v_mctx_4802_);
lean_dec(v___x_4801_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4993_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4809_; lean_object* v___x_4811_; 
v___x_4809_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 1, v___x_4809_);
v___x_4811_ = v___x_4807_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4992_; 
v_reuseFailAlloc_4992_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4992_, 0, v_mctx_4802_);
lean_ctor_set(v_reuseFailAlloc_4992_, 1, v___x_4809_);
lean_ctor_set(v_reuseFailAlloc_4992_, 2, v_zetaDeltaFVarIds_4803_);
lean_ctor_set(v_reuseFailAlloc_4992_, 3, v_postponed_4804_);
lean_ctor_set(v_reuseFailAlloc_4992_, 4, v_diag_4805_);
v___x_4811_ = v_reuseFailAlloc_4992_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
lean_object* v___x_4812_; lean_object* v___x_4813_; lean_object* v_mctx_4814_; lean_object* v_cache_4815_; lean_object* v_zetaDeltaFVarIds_4816_; lean_object* v_postponed_4817_; lean_object* v_diag_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4991_; 
v___x_4812_ = lean_st_ref_set(v___y_4793_, v___x_4811_);
v___x_4813_ = lean_st_ref_take(v___y_4793_);
v_mctx_4814_ = lean_ctor_get(v___x_4813_, 0);
v_cache_4815_ = lean_ctor_get(v___x_4813_, 1);
v_zetaDeltaFVarIds_4816_ = lean_ctor_get(v___x_4813_, 2);
v_postponed_4817_ = lean_ctor_get(v___x_4813_, 3);
v_diag_4818_ = lean_ctor_get(v___x_4813_, 4);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4813_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4820_ = v___x_4813_;
v_isShared_4821_ = v_isSharedCheck_4991_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_diag_4818_);
lean_inc(v_postponed_4817_);
lean_inc(v_zetaDeltaFVarIds_4816_);
lean_inc(v_cache_4815_);
lean_inc(v_mctx_4814_);
lean_dec(v___x_4813_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4991_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4822_; lean_object* v___x_4824_; 
v___x_4822_ = lean_box(1);
if (v_isShared_4821_ == 0)
{
lean_ctor_set(v___x_4820_, 2, v___x_4822_);
v___x_4824_ = v___x_4820_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v_mctx_4814_);
lean_ctor_set(v_reuseFailAlloc_4990_, 1, v_cache_4815_);
lean_ctor_set(v_reuseFailAlloc_4990_, 2, v___x_4822_);
lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_postponed_4817_);
lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_diag_4818_);
v___x_4824_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
lean_object* v___x_4825_; lean_object* v_cache_4826_; lean_object* v_keyedConfig_4827_; lean_object* v_zetaDeltaSet_4828_; lean_object* v_lctx_4829_; lean_object* v_localInstances_4830_; lean_object* v_defEqCtx_x3f_4831_; lean_object* v_synthPendingDepth_4832_; lean_object* v_canUnfold_x3f_4833_; uint8_t v_univApprox_4834_; uint8_t v_inTypeClassResolution_4835_; uint8_t v_cacheInferType_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; uint8_t v_foApprox_4839_; uint8_t v_ctxApprox_4840_; uint8_t v_quasiPatternApprox_4841_; uint8_t v_constApprox_4842_; uint8_t v_isDefEqStuckEx_4843_; uint8_t v_unificationHints_4844_; uint8_t v_proofIrrelevance_4845_; uint8_t v_assignSyntheticOpaque_4846_; uint8_t v_offsetCnstrs_4847_; uint8_t v_etaStruct_4848_; uint8_t v_univApprox_4849_; uint8_t v_iota_4850_; uint8_t v_beta_4851_; uint8_t v_proj_4852_; uint8_t v_zeta_4853_; uint8_t v_zetaDelta_4854_; uint8_t v_zetaUnused_4855_; uint8_t v_zetaHave_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4989_; 
v___x_4825_ = lean_st_ref_set(v___y_4793_, v___x_4824_);
v_cache_4826_ = lean_ctor_get(v___x_4800_, 1);
lean_inc_ref(v_cache_4826_);
lean_dec(v___x_4800_);
v_keyedConfig_4827_ = lean_ctor_get(v___y_4792_, 0);
v_zetaDeltaSet_4828_ = lean_ctor_get(v___y_4792_, 1);
v_lctx_4829_ = lean_ctor_get(v___y_4792_, 2);
v_localInstances_4830_ = lean_ctor_get(v___y_4792_, 3);
v_defEqCtx_x3f_4831_ = lean_ctor_get(v___y_4792_, 4);
v_synthPendingDepth_4832_ = lean_ctor_get(v___y_4792_, 5);
v_canUnfold_x3f_4833_ = lean_ctor_get(v___y_4792_, 6);
v_univApprox_4834_ = lean_ctor_get_uint8(v___y_4792_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4835_ = lean_ctor_get_uint8(v___y_4792_, sizeof(void*)*7 + 2);
v_cacheInferType_4836_ = lean_ctor_get_uint8(v___y_4792_, sizeof(void*)*7 + 3);
lean_inc(v_canUnfold_x3f_4833_);
lean_inc(v_synthPendingDepth_4832_);
lean_inc(v_defEqCtx_x3f_4831_);
lean_inc_ref(v_localInstances_4830_);
lean_inc_ref(v_lctx_4829_);
lean_inc(v_zetaDeltaSet_4828_);
lean_inc_ref(v_keyedConfig_4827_);
v___x_4837_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4837_, 0, v_keyedConfig_4827_);
lean_ctor_set(v___x_4837_, 1, v_zetaDeltaSet_4828_);
lean_ctor_set(v___x_4837_, 2, v_lctx_4829_);
lean_ctor_set(v___x_4837_, 3, v_localInstances_4830_);
lean_ctor_set(v___x_4837_, 4, v_defEqCtx_x3f_4831_);
lean_ctor_set(v___x_4837_, 5, v_synthPendingDepth_4832_);
lean_ctor_set(v___x_4837_, 6, v_canUnfold_x3f_4833_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7, v___x_4790_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7 + 1, v_univApprox_4834_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4835_);
lean_ctor_set_uint8(v___x_4837_, sizeof(void*)*7 + 3, v_cacheInferType_4836_);
v___x_4838_ = l_Lean_Meta_Context_config(v___x_4837_);
v_foApprox_4839_ = lean_ctor_get_uint8(v___x_4838_, 0);
v_ctxApprox_4840_ = lean_ctor_get_uint8(v___x_4838_, 1);
v_quasiPatternApprox_4841_ = lean_ctor_get_uint8(v___x_4838_, 2);
v_constApprox_4842_ = lean_ctor_get_uint8(v___x_4838_, 3);
v_isDefEqStuckEx_4843_ = lean_ctor_get_uint8(v___x_4838_, 4);
v_unificationHints_4844_ = lean_ctor_get_uint8(v___x_4838_, 5);
v_proofIrrelevance_4845_ = lean_ctor_get_uint8(v___x_4838_, 6);
v_assignSyntheticOpaque_4846_ = lean_ctor_get_uint8(v___x_4838_, 7);
v_offsetCnstrs_4847_ = lean_ctor_get_uint8(v___x_4838_, 8);
v_etaStruct_4848_ = lean_ctor_get_uint8(v___x_4838_, 10);
v_univApprox_4849_ = lean_ctor_get_uint8(v___x_4838_, 11);
v_iota_4850_ = lean_ctor_get_uint8(v___x_4838_, 12);
v_beta_4851_ = lean_ctor_get_uint8(v___x_4838_, 13);
v_proj_4852_ = lean_ctor_get_uint8(v___x_4838_, 14);
v_zeta_4853_ = lean_ctor_get_uint8(v___x_4838_, 15);
v_zetaDelta_4854_ = lean_ctor_get_uint8(v___x_4838_, 16);
v_zetaUnused_4855_ = lean_ctor_get_uint8(v___x_4838_, 17);
v_zetaHave_4856_ = lean_ctor_get_uint8(v___x_4838_, 18);
v_isSharedCheck_4989_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4989_ == 0)
{
v___x_4858_ = v___x_4838_;
v_isShared_4859_ = v_isSharedCheck_4989_;
goto v_resetjp_4857_;
}
else
{
lean_dec(v___x_4838_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4989_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
uint8_t v___x_4860_; lean_object* v_config_4862_; 
v___x_4860_ = 0;
if (v_isShared_4859_ == 0)
{
v_config_4862_ = v___x_4858_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4988_; 
v_reuseFailAlloc_4988_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 0, v_foApprox_4839_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 1, v_ctxApprox_4840_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 2, v_quasiPatternApprox_4841_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 3, v_constApprox_4842_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 4, v_isDefEqStuckEx_4843_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 5, v_unificationHints_4844_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 6, v_proofIrrelevance_4845_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 7, v_assignSyntheticOpaque_4846_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 8, v_offsetCnstrs_4847_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 10, v_etaStruct_4848_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 11, v_univApprox_4849_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 12, v_iota_4850_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 13, v_beta_4851_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 14, v_proj_4852_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 15, v_zeta_4853_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 16, v_zetaDelta_4854_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 17, v_zetaUnused_4855_);
lean_ctor_set_uint8(v_reuseFailAlloc_4988_, 18, v_zetaHave_4856_);
v_config_4862_ = v_reuseFailAlloc_4988_;
goto v_reusejp_4861_;
}
v_reusejp_4861_:
{
uint64_t v___x_4863_; uint64_t v___x_4864_; uint64_t v___x_4865_; uint64_t v___x_4866_; uint64_t v___x_4867_; uint64_t v_key_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; uint8_t v_transparency_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v_a_4877_; lean_object* v___y_4889_; lean_object* v___y_4912_; uint8_t v___y_4940_; uint8_t v___x_4986_; uint8_t v___x_4987_; 
lean_ctor_set_uint8(v_config_4862_, 9, v___x_4860_);
v___x_4863_ = l_Lean_Meta_Context_configKey(v___x_4837_);
lean_dec_ref_known(v___x_4837_, 7);
v___x_4864_ = 3ULL;
v___x_4865_ = lean_uint64_shift_right(v___x_4863_, v___x_4864_);
v___x_4866_ = lean_uint64_shift_left(v___x_4865_, v___x_4864_);
v___x_4867_ = lean_uint64_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6);
v_key_4868_ = lean_uint64_lor(v___x_4866_, v___x_4867_);
v___x_4869_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4869_, 0, v_config_4862_);
lean_ctor_set_uint64(v___x_4869_, sizeof(void*)*1, v_key_4868_);
lean_inc(v_canUnfold_x3f_4833_);
lean_inc(v_synthPendingDepth_4832_);
lean_inc(v_defEqCtx_x3f_4831_);
lean_inc_ref(v_localInstances_4830_);
lean_inc_ref(v_lctx_4829_);
lean_inc(v_zetaDeltaSet_4828_);
v___x_4870_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
lean_ctor_set(v___x_4870_, 1, v_zetaDeltaSet_4828_);
lean_ctor_set(v___x_4870_, 2, v_lctx_4829_);
lean_ctor_set(v___x_4870_, 3, v_localInstances_4830_);
lean_ctor_set(v___x_4870_, 4, v_defEqCtx_x3f_4831_);
lean_ctor_set(v___x_4870_, 5, v_synthPendingDepth_4832_);
lean_ctor_set(v___x_4870_, 6, v_canUnfold_x3f_4833_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*7, v___x_4790_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*7 + 1, v_univApprox_4834_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4835_);
lean_ctor_set_uint8(v___x_4870_, sizeof(void*)*7 + 3, v_cacheInferType_4836_);
v___x_4871_ = l_Lean_Meta_Context_config(v___x_4870_);
v_transparency_4872_ = lean_ctor_get_uint8(v___x_4871_, 9);
v___x_4873_ = lean_unsigned_to_nat(0u);
v___x_4874_ = lean_box(0);
v___x_4875_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7);
v___x_4986_ = 1;
v___x_4987_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4872_, v___x_4986_);
if (v___x_4987_ == 0)
{
v___y_4940_ = v_transparency_4872_;
goto v___jp_4939_;
}
else
{
v___y_4940_ = v___x_4986_;
goto v___jp_4939_;
}
v___jp_4876_:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4886_; 
v___x_4878_ = lean_box(0);
v___x_4879_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4793_, v_cache_4826_, v___x_4878_);
v_isSharedCheck_4886_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4886_ == 0)
{
lean_object* v_unused_4887_; 
v_unused_4887_ = lean_ctor_get(v___x_4879_, 0);
lean_dec(v_unused_4887_);
v___x_4881_ = v___x_4879_;
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
else
{
lean_dec(v___x_4879_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4886_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4884_; 
if (v_isShared_4882_ == 0)
{
lean_ctor_set_tag(v___x_4881_, 1);
lean_ctor_set(v___x_4881_, 0, v_a_4877_);
v___x_4884_ = v___x_4881_;
goto v_reusejp_4883_;
}
else
{
lean_object* v_reuseFailAlloc_4885_; 
v_reuseFailAlloc_4885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4885_, 0, v_a_4877_);
v___x_4884_ = v_reuseFailAlloc_4885_;
goto v_reusejp_4883_;
}
v_reusejp_4883_:
{
return v___x_4884_;
}
}
}
v___jp_4888_:
{
if (lean_obj_tag(v___y_4889_) == 0)
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4907_; 
v_a_4890_ = lean_ctor_get(v___y_4889_, 0);
v_isSharedCheck_4907_ = !lean_is_exclusive(v___y_4889_);
if (v_isSharedCheck_4907_ == 0)
{
v___x_4892_ = v___y_4889_;
v_isShared_4893_ = v_isSharedCheck_4907_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___y_4889_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4907_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
lean_inc(v_a_4890_);
if (v_isShared_4893_ == 0)
{
lean_ctor_set_tag(v___x_4892_, 1);
v___x_4895_ = v___x_4892_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4906_; 
v_reuseFailAlloc_4906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4906_, 0, v_a_4890_);
v___x_4895_ = v_reuseFailAlloc_4906_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4899_; uint8_t v_isShared_4900_; uint8_t v_isSharedCheck_4904_; 
v___x_4896_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4793_, v_zetaDeltaFVarIds_4816_, v___x_4895_);
lean_dec_ref(v___x_4896_);
v___x_4897_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4793_, v_cache_4826_, v___x_4895_);
lean_dec_ref(v___x_4895_);
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4904_ == 0)
{
lean_object* v_unused_4905_; 
v_unused_4905_ = lean_ctor_get(v___x_4897_, 0);
lean_dec(v_unused_4905_);
v___x_4899_ = v___x_4897_;
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
else
{
lean_dec(v___x_4897_);
v___x_4899_ = lean_box(0);
v_isShared_4900_ = v_isSharedCheck_4904_;
goto v_resetjp_4898_;
}
v_resetjp_4898_:
{
lean_object* v___x_4902_; 
if (v_isShared_4900_ == 0)
{
lean_ctor_set(v___x_4899_, 0, v_a_4890_);
v___x_4902_ = v___x_4899_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v_a_4890_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
}
}
else
{
lean_object* v_a_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v_a_4908_ = lean_ctor_get(v___y_4889_, 0);
lean_inc(v_a_4908_);
lean_dec_ref_known(v___y_4889_, 1);
v___x_4909_ = lean_box(0);
v___x_4910_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4793_, v_zetaDeltaFVarIds_4816_, v___x_4909_);
lean_dec_ref(v___x_4910_);
v_a_4877_ = v_a_4908_;
goto v___jp_4876_;
}
}
v___jp_4911_:
{
lean_object* v___x_4913_; uint8_t v_foApprox_4914_; uint8_t v_ctxApprox_4915_; uint8_t v_quasiPatternApprox_4916_; uint8_t v_constApprox_4917_; uint8_t v_isDefEqStuckEx_4918_; uint8_t v_unificationHints_4919_; uint8_t v_proofIrrelevance_4920_; uint8_t v_assignSyntheticOpaque_4921_; uint8_t v_offsetCnstrs_4922_; uint8_t v_transparency_4923_; uint8_t v_univApprox_4924_; uint8_t v_zetaUnused_4925_; lean_object* v___x_4927_; uint8_t v_isShared_4928_; uint8_t v_isSharedCheck_4938_; 
v___x_4913_ = l_Lean_Meta_Context_config(v___y_4912_);
lean_dec_ref(v___y_4912_);
v_foApprox_4914_ = lean_ctor_get_uint8(v___x_4913_, 0);
v_ctxApprox_4915_ = lean_ctor_get_uint8(v___x_4913_, 1);
v_quasiPatternApprox_4916_ = lean_ctor_get_uint8(v___x_4913_, 2);
v_constApprox_4917_ = lean_ctor_get_uint8(v___x_4913_, 3);
v_isDefEqStuckEx_4918_ = lean_ctor_get_uint8(v___x_4913_, 4);
v_unificationHints_4919_ = lean_ctor_get_uint8(v___x_4913_, 5);
v_proofIrrelevance_4920_ = lean_ctor_get_uint8(v___x_4913_, 6);
v_assignSyntheticOpaque_4921_ = lean_ctor_get_uint8(v___x_4913_, 7);
v_offsetCnstrs_4922_ = lean_ctor_get_uint8(v___x_4913_, 8);
v_transparency_4923_ = lean_ctor_get_uint8(v___x_4913_, 9);
v_univApprox_4924_ = lean_ctor_get_uint8(v___x_4913_, 11);
v_zetaUnused_4925_ = lean_ctor_get_uint8(v___x_4913_, 17);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4913_);
if (v_isSharedCheck_4938_ == 0)
{
v___x_4927_ = v___x_4913_;
v_isShared_4928_ = v_isSharedCheck_4938_;
goto v_resetjp_4926_;
}
else
{
lean_dec(v___x_4913_);
v___x_4927_ = lean_box(0);
v_isShared_4928_ = v_isSharedCheck_4938_;
goto v_resetjp_4926_;
}
v_resetjp_4926_:
{
uint8_t v___x_4929_; uint8_t v___x_4930_; lean_object* v___x_4932_; 
v___x_4929_ = 0;
v___x_4930_ = 2;
if (v_isShared_4928_ == 0)
{
v___x_4932_ = v___x_4927_;
goto v_reusejp_4931_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 0, v_foApprox_4914_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 1, v_ctxApprox_4915_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 2, v_quasiPatternApprox_4916_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 3, v_constApprox_4917_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 4, v_isDefEqStuckEx_4918_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 5, v_unificationHints_4919_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 6, v_proofIrrelevance_4920_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 7, v_assignSyntheticOpaque_4921_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 8, v_offsetCnstrs_4922_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 9, v_transparency_4923_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 11, v_univApprox_4924_);
lean_ctor_set_uint8(v_reuseFailAlloc_4937_, 17, v_zetaUnused_4925_);
v___x_4932_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4931_;
}
v_reusejp_4931_:
{
uint64_t v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; 
lean_ctor_set_uint8(v___x_4932_, 10, v___x_4929_);
lean_ctor_set_uint8(v___x_4932_, 12, v___x_4790_);
lean_ctor_set_uint8(v___x_4932_, 13, v___x_4790_);
lean_ctor_set_uint8(v___x_4932_, 14, v___x_4930_);
lean_ctor_set_uint8(v___x_4932_, 15, v___x_4790_);
lean_ctor_set_uint8(v___x_4932_, 16, v___x_4790_);
lean_ctor_set_uint8(v___x_4932_, 18, v___x_4790_);
v___x_4933_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4932_);
v___x_4934_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4934_, 0, v___x_4932_);
lean_ctor_set_uint64(v___x_4934_, sizeof(void*)*1, v___x_4933_);
lean_inc(v_canUnfold_x3f_4833_);
lean_inc(v_synthPendingDepth_4832_);
lean_inc(v_defEqCtx_x3f_4831_);
lean_inc_ref(v_localInstances_4830_);
lean_inc_ref(v_lctx_4829_);
lean_inc(v_zetaDeltaSet_4828_);
v___x_4935_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4935_, 0, v___x_4934_);
lean_ctor_set(v___x_4935_, 1, v_zetaDeltaSet_4828_);
lean_ctor_set(v___x_4935_, 2, v_lctx_4829_);
lean_ctor_set(v___x_4935_, 3, v_localInstances_4830_);
lean_ctor_set(v___x_4935_, 4, v_defEqCtx_x3f_4831_);
lean_ctor_set(v___x_4935_, 5, v_synthPendingDepth_4832_);
lean_ctor_set(v___x_4935_, 6, v_canUnfold_x3f_4833_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7, v___x_4790_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7 + 1, v_univApprox_4834_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4835_);
lean_ctor_set_uint8(v___x_4935_, sizeof(void*)*7 + 3, v_cacheInferType_4836_);
v___x_4936_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4875_, v_e_4789_, v___x_4874_, v___x_4873_, v_cls_4791_, v___x_4935_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec_ref_known(v___x_4935_, 7);
v___y_4889_ = v___x_4936_;
goto v___jp_4888_;
}
}
}
v___jp_4939_:
{
uint8_t v_foApprox_4941_; uint8_t v_ctxApprox_4942_; uint8_t v_quasiPatternApprox_4943_; uint8_t v_constApprox_4944_; uint8_t v_isDefEqStuckEx_4945_; uint8_t v_unificationHints_4946_; uint8_t v_proofIrrelevance_4947_; uint8_t v_assignSyntheticOpaque_4948_; uint8_t v_offsetCnstrs_4949_; uint8_t v_etaStruct_4950_; uint8_t v_univApprox_4951_; uint8_t v_iota_4952_; uint8_t v_beta_4953_; uint8_t v_proj_4954_; uint8_t v_zeta_4955_; uint8_t v_zetaDelta_4956_; uint8_t v_zetaUnused_4957_; uint8_t v_zetaHave_4958_; lean_object* v___x_4960_; uint8_t v_isShared_4961_; uint8_t v_isSharedCheck_4985_; 
v_foApprox_4941_ = lean_ctor_get_uint8(v___x_4871_, 0);
v_ctxApprox_4942_ = lean_ctor_get_uint8(v___x_4871_, 1);
v_quasiPatternApprox_4943_ = lean_ctor_get_uint8(v___x_4871_, 2);
v_constApprox_4944_ = lean_ctor_get_uint8(v___x_4871_, 3);
v_isDefEqStuckEx_4945_ = lean_ctor_get_uint8(v___x_4871_, 4);
v_unificationHints_4946_ = lean_ctor_get_uint8(v___x_4871_, 5);
v_proofIrrelevance_4947_ = lean_ctor_get_uint8(v___x_4871_, 6);
v_assignSyntheticOpaque_4948_ = lean_ctor_get_uint8(v___x_4871_, 7);
v_offsetCnstrs_4949_ = lean_ctor_get_uint8(v___x_4871_, 8);
v_etaStruct_4950_ = lean_ctor_get_uint8(v___x_4871_, 10);
v_univApprox_4951_ = lean_ctor_get_uint8(v___x_4871_, 11);
v_iota_4952_ = lean_ctor_get_uint8(v___x_4871_, 12);
v_beta_4953_ = lean_ctor_get_uint8(v___x_4871_, 13);
v_proj_4954_ = lean_ctor_get_uint8(v___x_4871_, 14);
v_zeta_4955_ = lean_ctor_get_uint8(v___x_4871_, 15);
v_zetaDelta_4956_ = lean_ctor_get_uint8(v___x_4871_, 16);
v_zetaUnused_4957_ = lean_ctor_get_uint8(v___x_4871_, 17);
v_zetaHave_4958_ = lean_ctor_get_uint8(v___x_4871_, 18);
v_isSharedCheck_4985_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4985_ == 0)
{
v___x_4960_ = v___x_4871_;
v_isShared_4961_ = v_isSharedCheck_4985_;
goto v_resetjp_4959_;
}
else
{
lean_dec(v___x_4871_);
v___x_4960_ = lean_box(0);
v_isShared_4961_ = v_isSharedCheck_4985_;
goto v_resetjp_4959_;
}
v_resetjp_4959_:
{
lean_object* v_config_4963_; 
if (v_isShared_4961_ == 0)
{
v_config_4963_ = v___x_4960_;
goto v_reusejp_4962_;
}
else
{
lean_object* v_reuseFailAlloc_4984_; 
v_reuseFailAlloc_4984_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 0, v_foApprox_4941_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 1, v_ctxApprox_4942_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 2, v_quasiPatternApprox_4943_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 3, v_constApprox_4944_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 4, v_isDefEqStuckEx_4945_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 5, v_unificationHints_4946_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 6, v_proofIrrelevance_4947_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 7, v_assignSyntheticOpaque_4948_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 8, v_offsetCnstrs_4949_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 10, v_etaStruct_4950_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 11, v_univApprox_4951_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 12, v_iota_4952_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 13, v_beta_4953_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 14, v_proj_4954_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 15, v_zeta_4955_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 16, v_zetaDelta_4956_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 17, v_zetaUnused_4957_);
lean_ctor_set_uint8(v_reuseFailAlloc_4984_, 18, v_zetaHave_4958_);
v_config_4963_ = v_reuseFailAlloc_4984_;
goto v_reusejp_4962_;
}
v_reusejp_4962_:
{
uint64_t v___x_4964_; uint64_t v___x_4965_; uint64_t v___x_4966_; uint64_t v___x_4967_; uint64_t v_key_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; lean_object* v___x_4971_; uint8_t v_beta_4972_; 
lean_ctor_set_uint8(v_config_4963_, 9, v___y_4940_);
v___x_4964_ = l_Lean_Meta_Context_configKey(v___x_4870_);
lean_dec_ref_known(v___x_4870_, 7);
v___x_4965_ = lean_uint64_shift_right(v___x_4964_, v___x_4864_);
v___x_4966_ = lean_uint64_shift_left(v___x_4965_, v___x_4864_);
v___x_4967_ = l_Lean_Meta_TransparencyMode_toUInt64(v___y_4940_);
v_key_4968_ = lean_uint64_lor(v___x_4966_, v___x_4967_);
v___x_4969_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4969_, 0, v_config_4963_);
lean_ctor_set_uint64(v___x_4969_, sizeof(void*)*1, v_key_4968_);
lean_inc(v_canUnfold_x3f_4833_);
lean_inc(v_synthPendingDepth_4832_);
lean_inc(v_defEqCtx_x3f_4831_);
lean_inc_ref(v_localInstances_4830_);
lean_inc_ref(v_lctx_4829_);
lean_inc(v_zetaDeltaSet_4828_);
v___x_4970_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
lean_ctor_set(v___x_4970_, 1, v_zetaDeltaSet_4828_);
lean_ctor_set(v___x_4970_, 2, v_lctx_4829_);
lean_ctor_set(v___x_4970_, 3, v_localInstances_4830_);
lean_ctor_set(v___x_4970_, 4, v_defEqCtx_x3f_4831_);
lean_ctor_set(v___x_4970_, 5, v_synthPendingDepth_4832_);
lean_ctor_set(v___x_4970_, 6, v_canUnfold_x3f_4833_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*7, v___x_4790_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*7 + 1, v_univApprox_4834_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4835_);
lean_ctor_set_uint8(v___x_4970_, sizeof(void*)*7 + 3, v_cacheInferType_4836_);
v___x_4971_ = l_Lean_Meta_Context_config(v___x_4970_);
v_beta_4972_ = lean_ctor_get_uint8(v___x_4971_, 13);
if (v_beta_4972_ == 0)
{
lean_dec_ref(v___x_4971_);
v___y_4912_ = v___x_4970_;
goto v___jp_4911_;
}
else
{
uint8_t v_iota_4973_; 
v_iota_4973_ = lean_ctor_get_uint8(v___x_4971_, 12);
if (v_iota_4973_ == 0)
{
lean_dec_ref(v___x_4971_);
v___y_4912_ = v___x_4970_;
goto v___jp_4911_;
}
else
{
uint8_t v_zeta_4974_; 
v_zeta_4974_ = lean_ctor_get_uint8(v___x_4971_, 15);
if (v_zeta_4974_ == 0)
{
lean_dec_ref(v___x_4971_);
v___y_4912_ = v___x_4970_;
goto v___jp_4911_;
}
else
{
uint8_t v_zetaHave_4975_; 
v_zetaHave_4975_ = lean_ctor_get_uint8(v___x_4971_, 18);
if (v_zetaHave_4975_ == 0)
{
lean_dec_ref(v___x_4971_);
v___y_4912_ = v___x_4970_;
goto v___jp_4911_;
}
else
{
uint8_t v_zetaDelta_4976_; 
v_zetaDelta_4976_ = lean_ctor_get_uint8(v___x_4971_, 16);
if (v_zetaDelta_4976_ == 0)
{
lean_dec_ref(v___x_4971_);
v___y_4912_ = v___x_4970_;
goto v___jp_4911_;
}
else
{
uint8_t v_etaStruct_4977_; uint8_t v_proj_4978_; uint8_t v___x_4979_; uint8_t v___x_4980_; 
v_etaStruct_4977_ = lean_ctor_get_uint8(v___x_4971_, 10);
v_proj_4978_ = lean_ctor_get_uint8(v___x_4971_, 14);
lean_dec_ref(v___x_4971_);
v___x_4979_ = 2;
v___x_4980_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_4978_, v___x_4979_);
if (v___x_4980_ == 0)
{
v___y_4912_ = v___x_4970_;
goto v___jp_4911_;
}
else
{
uint8_t v___x_4981_; uint8_t v___x_4982_; 
v___x_4981_ = 0;
v___x_4982_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4977_, v___x_4981_);
if (v___x_4982_ == 0)
{
v___y_4912_ = v___x_4970_;
goto v___jp_4911_;
}
else
{
lean_object* v___x_4983_; 
v___x_4983_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4875_, v_e_4789_, v___x_4874_, v___x_4873_, v_cls_4791_, v___x_4970_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec_ref_known(v___x_4970_, 7);
v___y_4889_ = v___x_4983_;
goto v___jp_4888_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_4995_, lean_object* v_e_4996_, lean_object* v___x_4997_, lean_object* v_cls_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_){
_start:
{
uint8_t v___x_14648__boxed_5004_; uint8_t v___x_14649__boxed_5005_; lean_object* v_res_5006_; 
v___x_14648__boxed_5004_ = lean_unbox(v___x_4995_);
v___x_14649__boxed_5005_ = lean_unbox(v___x_4997_);
v_res_5006_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_14648__boxed_5004_, v_e_4996_, v___x_14649__boxed_5005_, v_cls_4998_, v___y_4999_, v___y_5000_, v___y_5001_, v___y_5002_);
lean_dec(v___y_5002_);
lean_dec_ref(v___y_5001_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
return v_res_5006_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_, lean_object* v___y_5011_){
_start:
{
if (lean_obj_tag(v_x_5007_) == 0)
{
lean_object* v_a_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5021_; 
v_a_5013_ = lean_ctor_get(v_x_5007_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v_x_5007_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5015_ = v_x_5007_;
v_isShared_5016_ = v_isSharedCheck_5021_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_a_5013_);
lean_dec(v_x_5007_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5021_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5017_ = l_Lean_Exception_toMessageData(v_a_5013_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 0, v___x_5017_);
v___x_5019_ = v___x_5015_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5020_; 
v_reuseFailAlloc_5020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5020_, 0, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5020_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
return v___x_5019_;
}
}
}
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5030_; 
v_a_5022_ = lean_ctor_get(v_x_5007_, 0);
v_isSharedCheck_5030_ = !lean_is_exclusive(v_x_5007_);
if (v_isSharedCheck_5030_ == 0)
{
v___x_5024_ = v_x_5007_;
v_isShared_5025_ = v_isSharedCheck_5030_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v_x_5007_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5030_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v_snd_5026_; lean_object* v___x_5028_; 
v_snd_5026_ = lean_ctor_get(v_a_5022_, 1);
lean_inc(v_snd_5026_);
lean_dec(v_a_5022_);
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 0);
lean_ctor_set(v___x_5024_, 0, v_snd_5026_);
v___x_5028_ = v___x_5024_;
goto v_reusejp_5027_;
}
else
{
lean_object* v_reuseFailAlloc_5029_; 
v_reuseFailAlloc_5029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5029_, 0, v_snd_5026_);
v___x_5028_ = v_reuseFailAlloc_5029_;
goto v_reusejp_5027_;
}
v_reusejp_5027_:
{
return v___x_5028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_, lean_object* v___y_5036_){
_start:
{
lean_object* v_res_5037_; 
v_res_5037_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5031_, v___y_5032_, v___y_5033_, v___y_5034_, v___y_5035_);
lean_dec(v___y_5035_);
lean_dec_ref(v___y_5034_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
return v_res_5037_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5038_){
_start:
{
if (lean_obj_tag(v_x_5038_) == 0)
{
lean_object* v_a_5040_; lean_object* v___x_5042_; uint8_t v_isShared_5043_; uint8_t v_isSharedCheck_5047_; 
v_a_5040_ = lean_ctor_get(v_x_5038_, 0);
v_isSharedCheck_5047_ = !lean_is_exclusive(v_x_5038_);
if (v_isSharedCheck_5047_ == 0)
{
v___x_5042_ = v_x_5038_;
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
else
{
lean_inc(v_a_5040_);
lean_dec(v_x_5038_);
v___x_5042_ = lean_box(0);
v_isShared_5043_ = v_isSharedCheck_5047_;
goto v_resetjp_5041_;
}
v_resetjp_5041_:
{
lean_object* v___x_5045_; 
if (v_isShared_5043_ == 0)
{
lean_ctor_set_tag(v___x_5042_, 1);
v___x_5045_ = v___x_5042_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5046_; 
v_reuseFailAlloc_5046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5046_, 0, v_a_5040_);
v___x_5045_ = v_reuseFailAlloc_5046_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
return v___x_5045_;
}
}
}
else
{
lean_object* v_a_5048_; lean_object* v___x_5050_; uint8_t v_isShared_5051_; uint8_t v_isSharedCheck_5055_; 
v_a_5048_ = lean_ctor_get(v_x_5038_, 0);
v_isSharedCheck_5055_ = !lean_is_exclusive(v_x_5038_);
if (v_isSharedCheck_5055_ == 0)
{
v___x_5050_ = v_x_5038_;
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
else
{
lean_inc(v_a_5048_);
lean_dec(v_x_5038_);
v___x_5050_ = lean_box(0);
v_isShared_5051_ = v_isSharedCheck_5055_;
goto v_resetjp_5049_;
}
v_resetjp_5049_:
{
lean_object* v___x_5053_; 
if (v_isShared_5051_ == 0)
{
lean_ctor_set_tag(v___x_5050_, 0);
v___x_5053_ = v___x_5050_;
goto v_reusejp_5052_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v_a_5048_);
v___x_5053_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5052_;
}
v_reusejp_5052_:
{
return v___x_5053_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5056_, lean_object* v___y_5057_){
_start:
{
lean_object* v_res_5058_; 
v_res_5058_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5056_);
return v_res_5058_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5059_){
_start:
{
if (lean_obj_tag(v_e_5059_) == 0)
{
uint8_t v___x_5060_; 
v___x_5060_ = 2;
return v___x_5060_;
}
else
{
uint8_t v___x_5061_; 
v___x_5061_ = 0;
return v___x_5061_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5062_){
_start:
{
uint8_t v_res_5063_; lean_object* v_r_5064_; 
v_res_5063_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5062_);
lean_dec_ref(v_e_5062_);
v_r_5064_ = lean_box(v_res_5063_);
return v_r_5064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5065_, lean_object* v_data_5066_, lean_object* v_ref_5067_, lean_object* v_msg_5068_, lean_object* v___y_5069_, lean_object* v___y_5070_, lean_object* v___y_5071_, lean_object* v___y_5072_){
_start:
{
lean_object* v_fileName_5074_; lean_object* v_fileMap_5075_; lean_object* v_options_5076_; lean_object* v_currRecDepth_5077_; lean_object* v_maxRecDepth_5078_; lean_object* v_ref_5079_; lean_object* v_currNamespace_5080_; lean_object* v_openDecls_5081_; lean_object* v_initHeartbeats_5082_; lean_object* v_maxHeartbeats_5083_; lean_object* v_quotContext_5084_; lean_object* v_currMacroScope_5085_; uint8_t v_diag_5086_; lean_object* v_cancelTk_x3f_5087_; uint8_t v_suppressElabErrors_5088_; lean_object* v_inheritedTraceOptions_5089_; lean_object* v___x_5090_; lean_object* v_traceState_5091_; lean_object* v_traces_5092_; lean_object* v_ref_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; size_t v_sz_5096_; size_t v___x_5097_; lean_object* v___x_5098_; lean_object* v_msg_5099_; lean_object* v___x_5100_; lean_object* v_a_5101_; lean_object* v___x_5103_; uint8_t v_isShared_5104_; uint8_t v_isSharedCheck_5138_; 
v_fileName_5074_ = lean_ctor_get(v___y_5071_, 0);
v_fileMap_5075_ = lean_ctor_get(v___y_5071_, 1);
v_options_5076_ = lean_ctor_get(v___y_5071_, 2);
v_currRecDepth_5077_ = lean_ctor_get(v___y_5071_, 3);
v_maxRecDepth_5078_ = lean_ctor_get(v___y_5071_, 4);
v_ref_5079_ = lean_ctor_get(v___y_5071_, 5);
v_currNamespace_5080_ = lean_ctor_get(v___y_5071_, 6);
v_openDecls_5081_ = lean_ctor_get(v___y_5071_, 7);
v_initHeartbeats_5082_ = lean_ctor_get(v___y_5071_, 8);
v_maxHeartbeats_5083_ = lean_ctor_get(v___y_5071_, 9);
v_quotContext_5084_ = lean_ctor_get(v___y_5071_, 10);
v_currMacroScope_5085_ = lean_ctor_get(v___y_5071_, 11);
v_diag_5086_ = lean_ctor_get_uint8(v___y_5071_, sizeof(void*)*14);
v_cancelTk_x3f_5087_ = lean_ctor_get(v___y_5071_, 12);
v_suppressElabErrors_5088_ = lean_ctor_get_uint8(v___y_5071_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5089_ = lean_ctor_get(v___y_5071_, 13);
v___x_5090_ = lean_st_ref_get(v___y_5072_);
v_traceState_5091_ = lean_ctor_get(v___x_5090_, 4);
lean_inc_ref(v_traceState_5091_);
lean_dec(v___x_5090_);
v_traces_5092_ = lean_ctor_get(v_traceState_5091_, 0);
lean_inc_ref(v_traces_5092_);
lean_dec_ref(v_traceState_5091_);
v_ref_5093_ = l_Lean_replaceRef(v_ref_5067_, v_ref_5079_);
lean_inc_ref(v_inheritedTraceOptions_5089_);
lean_inc(v_cancelTk_x3f_5087_);
lean_inc(v_currMacroScope_5085_);
lean_inc(v_quotContext_5084_);
lean_inc(v_maxHeartbeats_5083_);
lean_inc(v_initHeartbeats_5082_);
lean_inc(v_openDecls_5081_);
lean_inc(v_currNamespace_5080_);
lean_inc(v_maxRecDepth_5078_);
lean_inc(v_currRecDepth_5077_);
lean_inc_ref(v_options_5076_);
lean_inc_ref(v_fileMap_5075_);
lean_inc_ref(v_fileName_5074_);
v___x_5094_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5094_, 0, v_fileName_5074_);
lean_ctor_set(v___x_5094_, 1, v_fileMap_5075_);
lean_ctor_set(v___x_5094_, 2, v_options_5076_);
lean_ctor_set(v___x_5094_, 3, v_currRecDepth_5077_);
lean_ctor_set(v___x_5094_, 4, v_maxRecDepth_5078_);
lean_ctor_set(v___x_5094_, 5, v_ref_5093_);
lean_ctor_set(v___x_5094_, 6, v_currNamespace_5080_);
lean_ctor_set(v___x_5094_, 7, v_openDecls_5081_);
lean_ctor_set(v___x_5094_, 8, v_initHeartbeats_5082_);
lean_ctor_set(v___x_5094_, 9, v_maxHeartbeats_5083_);
lean_ctor_set(v___x_5094_, 10, v_quotContext_5084_);
lean_ctor_set(v___x_5094_, 11, v_currMacroScope_5085_);
lean_ctor_set(v___x_5094_, 12, v_cancelTk_x3f_5087_);
lean_ctor_set(v___x_5094_, 13, v_inheritedTraceOptions_5089_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*14, v_diag_5086_);
lean_ctor_set_uint8(v___x_5094_, sizeof(void*)*14 + 1, v_suppressElabErrors_5088_);
v___x_5095_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5092_);
lean_dec_ref(v_traces_5092_);
v_sz_5096_ = lean_array_size(v___x_5095_);
v___x_5097_ = ((size_t)0ULL);
v___x_5098_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5096_, v___x_5097_, v___x_5095_);
v_msg_5099_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5099_, 0, v_data_5066_);
lean_ctor_set(v_msg_5099_, 1, v_msg_5068_);
lean_ctor_set(v_msg_5099_, 2, v___x_5098_);
v___x_5100_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5099_, v___y_5069_, v___y_5070_, v___x_5094_, v___y_5072_);
lean_dec_ref_known(v___x_5094_, 14);
v_a_5101_ = lean_ctor_get(v___x_5100_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5103_ = v___x_5100_;
v_isShared_5104_ = v_isSharedCheck_5138_;
goto v_resetjp_5102_;
}
else
{
lean_inc(v_a_5101_);
lean_dec(v___x_5100_);
v___x_5103_ = lean_box(0);
v_isShared_5104_ = v_isSharedCheck_5138_;
goto v_resetjp_5102_;
}
v_resetjp_5102_:
{
lean_object* v___x_5105_; lean_object* v_traceState_5106_; lean_object* v_env_5107_; lean_object* v_nextMacroScope_5108_; lean_object* v_ngen_5109_; lean_object* v_auxDeclNGen_5110_; lean_object* v_cache_5111_; lean_object* v_messages_5112_; lean_object* v_infoState_5113_; lean_object* v_snapshotTasks_5114_; lean_object* v___x_5116_; uint8_t v_isShared_5117_; uint8_t v_isSharedCheck_5137_; 
v___x_5105_ = lean_st_ref_take(v___y_5072_);
v_traceState_5106_ = lean_ctor_get(v___x_5105_, 4);
v_env_5107_ = lean_ctor_get(v___x_5105_, 0);
v_nextMacroScope_5108_ = lean_ctor_get(v___x_5105_, 1);
v_ngen_5109_ = lean_ctor_get(v___x_5105_, 2);
v_auxDeclNGen_5110_ = lean_ctor_get(v___x_5105_, 3);
v_cache_5111_ = lean_ctor_get(v___x_5105_, 5);
v_messages_5112_ = lean_ctor_get(v___x_5105_, 6);
v_infoState_5113_ = lean_ctor_get(v___x_5105_, 7);
v_snapshotTasks_5114_ = lean_ctor_get(v___x_5105_, 8);
v_isSharedCheck_5137_ = !lean_is_exclusive(v___x_5105_);
if (v_isSharedCheck_5137_ == 0)
{
v___x_5116_ = v___x_5105_;
v_isShared_5117_ = v_isSharedCheck_5137_;
goto v_resetjp_5115_;
}
else
{
lean_inc(v_snapshotTasks_5114_);
lean_inc(v_infoState_5113_);
lean_inc(v_messages_5112_);
lean_inc(v_cache_5111_);
lean_inc(v_traceState_5106_);
lean_inc(v_auxDeclNGen_5110_);
lean_inc(v_ngen_5109_);
lean_inc(v_nextMacroScope_5108_);
lean_inc(v_env_5107_);
lean_dec(v___x_5105_);
v___x_5116_ = lean_box(0);
v_isShared_5117_ = v_isSharedCheck_5137_;
goto v_resetjp_5115_;
}
v_resetjp_5115_:
{
uint64_t v_tid_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5135_; 
v_tid_5118_ = lean_ctor_get_uint64(v_traceState_5106_, sizeof(void*)*1);
v_isSharedCheck_5135_ = !lean_is_exclusive(v_traceState_5106_);
if (v_isSharedCheck_5135_ == 0)
{
lean_object* v_unused_5136_; 
v_unused_5136_ = lean_ctor_get(v_traceState_5106_, 0);
lean_dec(v_unused_5136_);
v___x_5120_ = v_traceState_5106_;
v_isShared_5121_ = v_isSharedCheck_5135_;
goto v_resetjp_5119_;
}
else
{
lean_dec(v_traceState_5106_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5135_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5122_; lean_object* v___x_5123_; lean_object* v___x_5125_; 
v___x_5122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5122_, 0, v_ref_5067_);
lean_ctor_set(v___x_5122_, 1, v_a_5101_);
v___x_5123_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5065_, v___x_5122_);
if (v_isShared_5121_ == 0)
{
lean_ctor_set(v___x_5120_, 0, v___x_5123_);
v___x_5125_ = v___x_5120_;
goto v_reusejp_5124_;
}
else
{
lean_object* v_reuseFailAlloc_5134_; 
v_reuseFailAlloc_5134_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5134_, 0, v___x_5123_);
lean_ctor_set_uint64(v_reuseFailAlloc_5134_, sizeof(void*)*1, v_tid_5118_);
v___x_5125_ = v_reuseFailAlloc_5134_;
goto v_reusejp_5124_;
}
v_reusejp_5124_:
{
lean_object* v___x_5127_; 
if (v_isShared_5117_ == 0)
{
lean_ctor_set(v___x_5116_, 4, v___x_5125_);
v___x_5127_ = v___x_5116_;
goto v_reusejp_5126_;
}
else
{
lean_object* v_reuseFailAlloc_5133_; 
v_reuseFailAlloc_5133_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5133_, 0, v_env_5107_);
lean_ctor_set(v_reuseFailAlloc_5133_, 1, v_nextMacroScope_5108_);
lean_ctor_set(v_reuseFailAlloc_5133_, 2, v_ngen_5109_);
lean_ctor_set(v_reuseFailAlloc_5133_, 3, v_auxDeclNGen_5110_);
lean_ctor_set(v_reuseFailAlloc_5133_, 4, v___x_5125_);
lean_ctor_set(v_reuseFailAlloc_5133_, 5, v_cache_5111_);
lean_ctor_set(v_reuseFailAlloc_5133_, 6, v_messages_5112_);
lean_ctor_set(v_reuseFailAlloc_5133_, 7, v_infoState_5113_);
lean_ctor_set(v_reuseFailAlloc_5133_, 8, v_snapshotTasks_5114_);
v___x_5127_ = v_reuseFailAlloc_5133_;
goto v_reusejp_5126_;
}
v_reusejp_5126_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5131_; 
v___x_5128_ = lean_st_ref_set(v___y_5072_, v___x_5127_);
v___x_5129_ = lean_box(0);
if (v_isShared_5104_ == 0)
{
lean_ctor_set(v___x_5103_, 0, v___x_5129_);
v___x_5131_ = v___x_5103_;
goto v_reusejp_5130_;
}
else
{
lean_object* v_reuseFailAlloc_5132_; 
v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5132_, 0, v___x_5129_);
v___x_5131_ = v_reuseFailAlloc_5132_;
goto v_reusejp_5130_;
}
v_reusejp_5130_:
{
return v___x_5131_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5139_, lean_object* v_data_5140_, lean_object* v_ref_5141_, lean_object* v_msg_5142_, lean_object* v___y_5143_, lean_object* v___y_5144_, lean_object* v___y_5145_, lean_object* v___y_5146_, lean_object* v___y_5147_){
_start:
{
lean_object* v_res_5148_; 
v_res_5148_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5139_, v_data_5140_, v_ref_5141_, v_msg_5142_, v___y_5143_, v___y_5144_, v___y_5145_, v___y_5146_);
lean_dec(v___y_5146_);
lean_dec_ref(v___y_5145_);
lean_dec(v___y_5144_);
lean_dec_ref(v___y_5143_);
return v_res_5148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5149_, uint8_t v_collapsed_5150_, lean_object* v_tag_5151_, lean_object* v_opts_5152_, uint8_t v_clsEnabled_5153_, lean_object* v_oldTraces_5154_, lean_object* v_msg_5155_, lean_object* v_resStartStop_5156_, lean_object* v___y_5157_, lean_object* v___y_5158_, lean_object* v___y_5159_, lean_object* v___y_5160_){
_start:
{
lean_object* v_fst_5162_; lean_object* v_snd_5163_; lean_object* v___y_5165_; lean_object* v___y_5166_; lean_object* v_data_5167_; lean_object* v_fst_5178_; lean_object* v_snd_5179_; lean_object* v___x_5180_; uint8_t v___x_5181_; lean_object* v___y_5183_; lean_object* v_a_5184_; uint8_t v___y_5199_; double v___y_5230_; 
v_fst_5162_ = lean_ctor_get(v_resStartStop_5156_, 0);
lean_inc(v_fst_5162_);
v_snd_5163_ = lean_ctor_get(v_resStartStop_5156_, 1);
lean_inc(v_snd_5163_);
lean_dec_ref(v_resStartStop_5156_);
v_fst_5178_ = lean_ctor_get(v_snd_5163_, 0);
lean_inc(v_fst_5178_);
v_snd_5179_ = lean_ctor_get(v_snd_5163_, 1);
lean_inc(v_snd_5179_);
lean_dec(v_snd_5163_);
v___x_5180_ = l_Lean_trace_profiler;
v___x_5181_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5152_, v___x_5180_);
if (v___x_5181_ == 0)
{
v___y_5199_ = v___x_5181_;
goto v___jp_5198_;
}
else
{
lean_object* v___x_5235_; uint8_t v___x_5236_; 
v___x_5235_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5236_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5152_, v___x_5235_);
if (v___x_5236_ == 0)
{
lean_object* v___x_5237_; lean_object* v___x_5238_; double v___x_5239_; double v___x_5240_; double v___x_5241_; 
v___x_5237_ = l_Lean_trace_profiler_threshold;
v___x_5238_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5152_, v___x_5237_);
v___x_5239_ = lean_float_of_nat(v___x_5238_);
v___x_5240_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5241_ = lean_float_div(v___x_5239_, v___x_5240_);
v___y_5230_ = v___x_5241_;
goto v___jp_5229_;
}
else
{
lean_object* v___x_5242_; lean_object* v___x_5243_; double v___x_5244_; 
v___x_5242_ = l_Lean_trace_profiler_threshold;
v___x_5243_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5152_, v___x_5242_);
v___x_5244_ = lean_float_of_nat(v___x_5243_);
v___y_5230_ = v___x_5244_;
goto v___jp_5229_;
}
}
v___jp_5164_:
{
lean_object* v___x_5168_; 
lean_inc(v___y_5165_);
v___x_5168_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5154_, v_data_5167_, v___y_5165_, v___y_5166_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_);
if (lean_obj_tag(v___x_5168_) == 0)
{
lean_object* v___x_5169_; 
lean_dec_ref_known(v___x_5168_, 1);
v___x_5169_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5162_);
return v___x_5169_;
}
else
{
lean_object* v_a_5170_; lean_object* v___x_5172_; uint8_t v_isShared_5173_; uint8_t v_isSharedCheck_5177_; 
lean_dec(v_fst_5162_);
v_a_5170_ = lean_ctor_get(v___x_5168_, 0);
v_isSharedCheck_5177_ = !lean_is_exclusive(v___x_5168_);
if (v_isSharedCheck_5177_ == 0)
{
v___x_5172_ = v___x_5168_;
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
else
{
lean_inc(v_a_5170_);
lean_dec(v___x_5168_);
v___x_5172_ = lean_box(0);
v_isShared_5173_ = v_isSharedCheck_5177_;
goto v_resetjp_5171_;
}
v_resetjp_5171_:
{
lean_object* v___x_5175_; 
if (v_isShared_5173_ == 0)
{
v___x_5175_ = v___x_5172_;
goto v_reusejp_5174_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_a_5170_);
v___x_5175_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5174_;
}
v_reusejp_5174_:
{
return v___x_5175_;
}
}
}
}
v___jp_5182_:
{
uint8_t v_result_5185_; lean_object* v___x_5186_; lean_object* v___x_5187_; double v___x_5188_; lean_object* v_data_5189_; 
v_result_5185_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5162_);
v___x_5186_ = lean_box(v_result_5185_);
v___x_5187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5186_);
v___x_5188_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5151_);
lean_inc_ref(v___x_5187_);
lean_inc(v_cls_5149_);
v_data_5189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5189_, 0, v_cls_5149_);
lean_ctor_set(v_data_5189_, 1, v___x_5187_);
lean_ctor_set(v_data_5189_, 2, v_tag_5151_);
lean_ctor_set_float(v_data_5189_, sizeof(void*)*3, v___x_5188_);
lean_ctor_set_float(v_data_5189_, sizeof(void*)*3 + 8, v___x_5188_);
lean_ctor_set_uint8(v_data_5189_, sizeof(void*)*3 + 16, v_collapsed_5150_);
if (v___x_5181_ == 0)
{
lean_dec_ref_known(v___x_5187_, 1);
lean_dec(v_snd_5179_);
lean_dec(v_fst_5178_);
lean_dec_ref(v_tag_5151_);
lean_dec(v_cls_5149_);
v___y_5165_ = v___y_5183_;
v___y_5166_ = v_a_5184_;
v_data_5167_ = v_data_5189_;
goto v___jp_5164_;
}
else
{
lean_object* v_data_5190_; double v___x_5191_; double v___x_5192_; 
lean_dec_ref_known(v_data_5189_, 3);
v_data_5190_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5190_, 0, v_cls_5149_);
lean_ctor_set(v_data_5190_, 1, v___x_5187_);
lean_ctor_set(v_data_5190_, 2, v_tag_5151_);
v___x_5191_ = lean_unbox_float(v_fst_5178_);
lean_dec(v_fst_5178_);
lean_ctor_set_float(v_data_5190_, sizeof(void*)*3, v___x_5191_);
v___x_5192_ = lean_unbox_float(v_snd_5179_);
lean_dec(v_snd_5179_);
lean_ctor_set_float(v_data_5190_, sizeof(void*)*3 + 8, v___x_5192_);
lean_ctor_set_uint8(v_data_5190_, sizeof(void*)*3 + 16, v_collapsed_5150_);
v___y_5165_ = v___y_5183_;
v___y_5166_ = v_a_5184_;
v_data_5167_ = v_data_5190_;
goto v___jp_5164_;
}
}
v___jp_5193_:
{
lean_object* v_ref_5194_; lean_object* v___x_5195_; 
v_ref_5194_ = lean_ctor_get(v___y_5159_, 5);
lean_inc(v___y_5160_);
lean_inc_ref(v___y_5159_);
lean_inc(v___y_5158_);
lean_inc_ref(v___y_5157_);
lean_inc(v_fst_5162_);
v___x_5195_ = lean_apply_6(v_msg_5155_, v_fst_5162_, v___y_5157_, v___y_5158_, v___y_5159_, v___y_5160_, lean_box(0));
if (lean_obj_tag(v___x_5195_) == 0)
{
lean_object* v_a_5196_; 
v_a_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc(v_a_5196_);
lean_dec_ref_known(v___x_5195_, 1);
v___y_5183_ = v_ref_5194_;
v_a_5184_ = v_a_5196_;
goto v___jp_5182_;
}
else
{
lean_object* v___x_5197_; 
lean_dec_ref_known(v___x_5195_, 1);
v___x_5197_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5183_ = v_ref_5194_;
v_a_5184_ = v___x_5197_;
goto v___jp_5182_;
}
}
v___jp_5198_:
{
if (v_clsEnabled_5153_ == 0)
{
if (v___y_5199_ == 0)
{
lean_object* v___x_5200_; lean_object* v_traceState_5201_; lean_object* v_env_5202_; lean_object* v_nextMacroScope_5203_; lean_object* v_ngen_5204_; lean_object* v_auxDeclNGen_5205_; lean_object* v_cache_5206_; lean_object* v_messages_5207_; lean_object* v_infoState_5208_; lean_object* v_snapshotTasks_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5228_; 
lean_dec(v_snd_5179_);
lean_dec(v_fst_5178_);
lean_dec_ref(v_msg_5155_);
lean_dec_ref(v_tag_5151_);
lean_dec(v_cls_5149_);
v___x_5200_ = lean_st_ref_take(v___y_5160_);
v_traceState_5201_ = lean_ctor_get(v___x_5200_, 4);
v_env_5202_ = lean_ctor_get(v___x_5200_, 0);
v_nextMacroScope_5203_ = lean_ctor_get(v___x_5200_, 1);
v_ngen_5204_ = lean_ctor_get(v___x_5200_, 2);
v_auxDeclNGen_5205_ = lean_ctor_get(v___x_5200_, 3);
v_cache_5206_ = lean_ctor_get(v___x_5200_, 5);
v_messages_5207_ = lean_ctor_get(v___x_5200_, 6);
v_infoState_5208_ = lean_ctor_get(v___x_5200_, 7);
v_snapshotTasks_5209_ = lean_ctor_get(v___x_5200_, 8);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5211_ = v___x_5200_;
v_isShared_5212_ = v_isSharedCheck_5228_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_snapshotTasks_5209_);
lean_inc(v_infoState_5208_);
lean_inc(v_messages_5207_);
lean_inc(v_cache_5206_);
lean_inc(v_traceState_5201_);
lean_inc(v_auxDeclNGen_5205_);
lean_inc(v_ngen_5204_);
lean_inc(v_nextMacroScope_5203_);
lean_inc(v_env_5202_);
lean_dec(v___x_5200_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5228_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
uint64_t v_tid_5213_; lean_object* v_traces_5214_; lean_object* v___x_5216_; uint8_t v_isShared_5217_; uint8_t v_isSharedCheck_5227_; 
v_tid_5213_ = lean_ctor_get_uint64(v_traceState_5201_, sizeof(void*)*1);
v_traces_5214_ = lean_ctor_get(v_traceState_5201_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v_traceState_5201_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5216_ = v_traceState_5201_;
v_isShared_5217_ = v_isSharedCheck_5227_;
goto v_resetjp_5215_;
}
else
{
lean_inc(v_traces_5214_);
lean_dec(v_traceState_5201_);
v___x_5216_ = lean_box(0);
v_isShared_5217_ = v_isSharedCheck_5227_;
goto v_resetjp_5215_;
}
v_resetjp_5215_:
{
lean_object* v___x_5218_; lean_object* v___x_5220_; 
v___x_5218_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5154_, v_traces_5214_);
lean_dec_ref(v_traces_5214_);
if (v_isShared_5217_ == 0)
{
lean_ctor_set(v___x_5216_, 0, v___x_5218_);
v___x_5220_ = v___x_5216_;
goto v_reusejp_5219_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5226_, 0, v___x_5218_);
lean_ctor_set_uint64(v_reuseFailAlloc_5226_, sizeof(void*)*1, v_tid_5213_);
v___x_5220_ = v_reuseFailAlloc_5226_;
goto v_reusejp_5219_;
}
v_reusejp_5219_:
{
lean_object* v___x_5222_; 
if (v_isShared_5212_ == 0)
{
lean_ctor_set(v___x_5211_, 4, v___x_5220_);
v___x_5222_ = v___x_5211_;
goto v_reusejp_5221_;
}
else
{
lean_object* v_reuseFailAlloc_5225_; 
v_reuseFailAlloc_5225_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5225_, 0, v_env_5202_);
lean_ctor_set(v_reuseFailAlloc_5225_, 1, v_nextMacroScope_5203_);
lean_ctor_set(v_reuseFailAlloc_5225_, 2, v_ngen_5204_);
lean_ctor_set(v_reuseFailAlloc_5225_, 3, v_auxDeclNGen_5205_);
lean_ctor_set(v_reuseFailAlloc_5225_, 4, v___x_5220_);
lean_ctor_set(v_reuseFailAlloc_5225_, 5, v_cache_5206_);
lean_ctor_set(v_reuseFailAlloc_5225_, 6, v_messages_5207_);
lean_ctor_set(v_reuseFailAlloc_5225_, 7, v_infoState_5208_);
lean_ctor_set(v_reuseFailAlloc_5225_, 8, v_snapshotTasks_5209_);
v___x_5222_ = v_reuseFailAlloc_5225_;
goto v_reusejp_5221_;
}
v_reusejp_5221_:
{
lean_object* v___x_5223_; lean_object* v___x_5224_; 
v___x_5223_ = lean_st_ref_set(v___y_5160_, v___x_5222_);
v___x_5224_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5162_);
return v___x_5224_;
}
}
}
}
}
else
{
goto v___jp_5193_;
}
}
else
{
goto v___jp_5193_;
}
}
v___jp_5229_:
{
double v___x_5231_; double v___x_5232_; double v___x_5233_; uint8_t v___x_5234_; 
v___x_5231_ = lean_unbox_float(v_snd_5179_);
v___x_5232_ = lean_unbox_float(v_fst_5178_);
v___x_5233_ = lean_float_sub(v___x_5231_, v___x_5232_);
v___x_5234_ = lean_float_decLt(v___y_5230_, v___x_5233_);
v___y_5199_ = v___x_5234_;
goto v___jp_5198_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5245_, lean_object* v_collapsed_5246_, lean_object* v_tag_5247_, lean_object* v_opts_5248_, lean_object* v_clsEnabled_5249_, lean_object* v_oldTraces_5250_, lean_object* v_msg_5251_, lean_object* v_resStartStop_5252_, lean_object* v___y_5253_, lean_object* v___y_5254_, lean_object* v___y_5255_, lean_object* v___y_5256_, lean_object* v___y_5257_){
_start:
{
uint8_t v_collapsed_boxed_5258_; uint8_t v_clsEnabled_boxed_5259_; lean_object* v_res_5260_; 
v_collapsed_boxed_5258_ = lean_unbox(v_collapsed_5246_);
v_clsEnabled_boxed_5259_ = lean_unbox(v_clsEnabled_5249_);
v_res_5260_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5245_, v_collapsed_boxed_5258_, v_tag_5247_, v_opts_5248_, v_clsEnabled_boxed_5259_, v_oldTraces_5250_, v_msg_5251_, v_resStartStop_5252_, v___y_5253_, v___y_5254_, v___y_5255_, v___y_5256_);
lean_dec(v___y_5256_);
lean_dec_ref(v___y_5255_);
lean_dec(v___y_5254_);
lean_dec_ref(v___y_5253_);
lean_dec_ref(v_opts_5248_);
return v_res_5260_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; 
v_cls_5265_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5266_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5267_ = l_Lean_Name_append(v___x_5266_, v_cls_5265_);
return v___x_5267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5268_, lean_object* v_a_5269_, lean_object* v_a_5270_, lean_object* v_a_5271_, lean_object* v_a_5272_){
_start:
{
lean_object* v___y_5275_; lean_object* v_options_5293_; lean_object* v_inheritedTraceOptions_5294_; uint8_t v_hasTrace_5295_; lean_object* v_cls_5296_; uint8_t v___x_5297_; uint8_t v___x_5298_; 
v_options_5293_ = lean_ctor_get(v_a_5271_, 2);
v_inheritedTraceOptions_5294_ = lean_ctor_get(v_a_5271_, 13);
v_hasTrace_5295_ = lean_ctor_get_uint8(v_options_5293_, sizeof(void*)*1);
v_cls_5296_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5297_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5268_);
v___x_5298_ = 1;
if (v_hasTrace_5295_ == 0)
{
lean_object* v___x_5299_; 
v___x_5299_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5297_, v_e_5268_, v___x_5298_, v_cls_5296_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
v___y_5275_ = v___x_5299_;
goto v___jp_5274_;
}
else
{
lean_object* v___f_5300_; lean_object* v___x_5301_; lean_object* v___x_5302_; uint8_t v___x_5303_; lean_object* v___y_5305_; lean_object* v___y_5306_; lean_object* v_a_5307_; lean_object* v___y_5320_; lean_object* v___y_5321_; lean_object* v_a_5322_; 
v___f_5300_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5301_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5302_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5303_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5294_, v_options_5293_, v___x_5302_);
if (v___x_5303_ == 0)
{
lean_object* v___x_5372_; uint8_t v___x_5373_; 
v___x_5372_ = l_Lean_trace_profiler;
v___x_5373_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5293_, v___x_5372_);
if (v___x_5373_ == 0)
{
lean_object* v___x_5374_; 
v___x_5374_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5297_, v_e_5268_, v___x_5298_, v_cls_5296_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
v___y_5275_ = v___x_5374_;
goto v___jp_5274_;
}
else
{
goto v___jp_5331_;
}
}
else
{
goto v___jp_5331_;
}
v___jp_5304_:
{
lean_object* v___x_5308_; double v___x_5309_; double v___x_5310_; double v___x_5311_; double v___x_5312_; double v___x_5313_; lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v___x_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; 
v___x_5308_ = lean_io_mono_nanos_now();
v___x_5309_ = lean_float_of_nat(v___y_5305_);
v___x_5310_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5311_ = lean_float_div(v___x_5309_, v___x_5310_);
v___x_5312_ = lean_float_of_nat(v___x_5308_);
v___x_5313_ = lean_float_div(v___x_5312_, v___x_5310_);
v___x_5314_ = lean_box_float(v___x_5311_);
v___x_5315_ = lean_box_float(v___x_5313_);
v___x_5316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5316_, 0, v___x_5314_);
lean_ctor_set(v___x_5316_, 1, v___x_5315_);
v___x_5317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5317_, 0, v_a_5307_);
lean_ctor_set(v___x_5317_, 1, v___x_5316_);
v___x_5318_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5296_, v___x_5298_, v___x_5301_, v_options_5293_, v___x_5303_, v___y_5306_, v___f_5300_, v___x_5317_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
v___y_5275_ = v___x_5318_;
goto v___jp_5274_;
}
v___jp_5319_:
{
lean_object* v___x_5323_; double v___x_5324_; double v___x_5325_; lean_object* v___x_5326_; lean_object* v___x_5327_; lean_object* v___x_5328_; lean_object* v___x_5329_; lean_object* v___x_5330_; 
v___x_5323_ = lean_io_get_num_heartbeats();
v___x_5324_ = lean_float_of_nat(v___y_5320_);
v___x_5325_ = lean_float_of_nat(v___x_5323_);
v___x_5326_ = lean_box_float(v___x_5324_);
v___x_5327_ = lean_box_float(v___x_5325_);
v___x_5328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5328_, 0, v___x_5326_);
lean_ctor_set(v___x_5328_, 1, v___x_5327_);
v___x_5329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5329_, 0, v_a_5322_);
lean_ctor_set(v___x_5329_, 1, v___x_5328_);
v___x_5330_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5296_, v___x_5298_, v___x_5301_, v_options_5293_, v___x_5303_, v___y_5321_, v___f_5300_, v___x_5329_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
v___y_5275_ = v___x_5330_;
goto v___jp_5274_;
}
v___jp_5331_:
{
lean_object* v___x_5332_; lean_object* v_a_5333_; lean_object* v___x_5334_; uint8_t v___x_5335_; 
v___x_5332_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5272_);
v_a_5333_ = lean_ctor_get(v___x_5332_, 0);
lean_inc(v_a_5333_);
lean_dec_ref(v___x_5332_);
v___x_5334_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5335_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5293_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; lean_object* v___x_5337_; 
v___x_5336_ = lean_io_mono_nanos_now();
v___x_5337_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5297_, v_e_5268_, v___x_5298_, v_cls_5296_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
if (lean_obj_tag(v___x_5337_) == 0)
{
lean_object* v_a_5338_; lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5345_; 
v_a_5338_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5345_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5345_ == 0)
{
v___x_5340_ = v___x_5337_;
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
else
{
lean_inc(v_a_5338_);
lean_dec(v___x_5337_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5345_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5343_; 
if (v_isShared_5341_ == 0)
{
lean_ctor_set_tag(v___x_5340_, 1);
v___x_5343_ = v___x_5340_;
goto v_reusejp_5342_;
}
else
{
lean_object* v_reuseFailAlloc_5344_; 
v_reuseFailAlloc_5344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5344_, 0, v_a_5338_);
v___x_5343_ = v_reuseFailAlloc_5344_;
goto v_reusejp_5342_;
}
v_reusejp_5342_:
{
v___y_5305_ = v___x_5336_;
v___y_5306_ = v_a_5333_;
v_a_5307_ = v___x_5343_;
goto v___jp_5304_;
}
}
}
else
{
lean_object* v_a_5346_; lean_object* v___x_5348_; uint8_t v_isShared_5349_; uint8_t v_isSharedCheck_5353_; 
v_a_5346_ = lean_ctor_get(v___x_5337_, 0);
v_isSharedCheck_5353_ = !lean_is_exclusive(v___x_5337_);
if (v_isSharedCheck_5353_ == 0)
{
v___x_5348_ = v___x_5337_;
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
else
{
lean_inc(v_a_5346_);
lean_dec(v___x_5337_);
v___x_5348_ = lean_box(0);
v_isShared_5349_ = v_isSharedCheck_5353_;
goto v_resetjp_5347_;
}
v_resetjp_5347_:
{
lean_object* v___x_5351_; 
if (v_isShared_5349_ == 0)
{
lean_ctor_set_tag(v___x_5348_, 0);
v___x_5351_ = v___x_5348_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v_a_5346_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
v___y_5305_ = v___x_5336_;
v___y_5306_ = v_a_5333_;
v_a_5307_ = v___x_5351_;
goto v___jp_5304_;
}
}
}
}
else
{
lean_object* v___x_5354_; lean_object* v___x_5355_; 
v___x_5354_ = lean_io_get_num_heartbeats();
v___x_5355_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5297_, v_e_5268_, v___x_5298_, v_cls_5296_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_);
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
v___y_5320_ = v___x_5354_;
v___y_5321_ = v_a_5333_;
v_a_5322_ = v___x_5361_;
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
v___y_5320_ = v___x_5354_;
v___y_5321_ = v_a_5333_;
v_a_5322_ = v___x_5369_;
goto v___jp_5319_;
}
}
}
}
}
}
v___jp_5274_:
{
if (lean_obj_tag(v___y_5275_) == 0)
{
lean_object* v_a_5276_; lean_object* v___x_5278_; uint8_t v_isShared_5279_; uint8_t v_isSharedCheck_5284_; 
v_a_5276_ = lean_ctor_get(v___y_5275_, 0);
v_isSharedCheck_5284_ = !lean_is_exclusive(v___y_5275_);
if (v_isSharedCheck_5284_ == 0)
{
v___x_5278_ = v___y_5275_;
v_isShared_5279_ = v_isSharedCheck_5284_;
goto v_resetjp_5277_;
}
else
{
lean_inc(v_a_5276_);
lean_dec(v___y_5275_);
v___x_5278_ = lean_box(0);
v_isShared_5279_ = v_isSharedCheck_5284_;
goto v_resetjp_5277_;
}
v_resetjp_5277_:
{
lean_object* v_fst_5280_; lean_object* v___x_5282_; 
v_fst_5280_ = lean_ctor_get(v_a_5276_, 0);
lean_inc(v_fst_5280_);
lean_dec(v_a_5276_);
if (v_isShared_5279_ == 0)
{
lean_ctor_set(v___x_5278_, 0, v_fst_5280_);
v___x_5282_ = v___x_5278_;
goto v_reusejp_5281_;
}
else
{
lean_object* v_reuseFailAlloc_5283_; 
v_reuseFailAlloc_5283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5283_, 0, v_fst_5280_);
v___x_5282_ = v_reuseFailAlloc_5283_;
goto v_reusejp_5281_;
}
v_reusejp_5281_:
{
return v___x_5282_;
}
}
}
else
{
lean_object* v_a_5285_; lean_object* v___x_5287_; uint8_t v_isShared_5288_; uint8_t v_isSharedCheck_5292_; 
v_a_5285_ = lean_ctor_get(v___y_5275_, 0);
v_isSharedCheck_5292_ = !lean_is_exclusive(v___y_5275_);
if (v_isSharedCheck_5292_ == 0)
{
v___x_5287_ = v___y_5275_;
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
else
{
lean_inc(v_a_5285_);
lean_dec(v___y_5275_);
v___x_5287_ = lean_box(0);
v_isShared_5288_ = v_isSharedCheck_5292_;
goto v_resetjp_5286_;
}
v_resetjp_5286_:
{
lean_object* v___x_5290_; 
if (v_isShared_5288_ == 0)
{
v___x_5290_ = v___x_5287_;
goto v_reusejp_5289_;
}
else
{
lean_object* v_reuseFailAlloc_5291_; 
v_reuseFailAlloc_5291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5291_, 0, v_a_5285_);
v___x_5290_ = v_reuseFailAlloc_5291_;
goto v_reusejp_5289_;
}
v_reusejp_5289_:
{
return v___x_5290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5375_, lean_object* v_a_5376_, lean_object* v_a_5377_, lean_object* v_a_5378_, lean_object* v_a_5379_, lean_object* v_a_5380_){
_start:
{
lean_object* v_res_5381_; 
v_res_5381_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5375_, v_a_5376_, v_a_5377_, v_a_5378_, v_a_5379_);
lean_dec(v_a_5379_);
lean_dec_ref(v_a_5378_);
lean_dec(v_a_5377_);
lean_dec_ref(v_a_5376_);
return v_res_5381_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5382_, lean_object* v_x_5383_, lean_object* v___y_5384_, lean_object* v___y_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v___x_5389_; 
v___x_5389_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5383_);
return v___x_5389_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5390_, lean_object* v_x_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_, lean_object* v___y_5396_){
_start:
{
lean_object* v_res_5397_; 
v_res_5397_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5390_, v_x_5391_, v___y_5392_, v___y_5393_, v___y_5394_, v___y_5395_);
lean_dec(v___y_5395_);
lean_dec_ref(v___y_5394_);
lean_dec(v___y_5393_);
lean_dec_ref(v___y_5392_);
return v_res_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5398_, lean_object* v___y_5399_){
_start:
{
uint8_t v___x_5401_; 
v___x_5401_ = l_Lean_Expr_hasMVar(v_e_5398_);
if (v___x_5401_ == 0)
{
lean_object* v___x_5402_; 
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v_e_5398_);
return v___x_5402_;
}
else
{
lean_object* v___x_5403_; lean_object* v_mctx_5404_; lean_object* v___x_5405_; lean_object* v_fst_5406_; lean_object* v_snd_5407_; lean_object* v___x_5408_; lean_object* v_cache_5409_; lean_object* v_zetaDeltaFVarIds_5410_; lean_object* v_postponed_5411_; lean_object* v_diag_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5421_; 
v___x_5403_ = lean_st_ref_get(v___y_5399_);
v_mctx_5404_ = lean_ctor_get(v___x_5403_, 0);
lean_inc_ref(v_mctx_5404_);
lean_dec(v___x_5403_);
v___x_5405_ = l_Lean_instantiateMVarsCore(v_mctx_5404_, v_e_5398_);
v_fst_5406_ = lean_ctor_get(v___x_5405_, 0);
lean_inc(v_fst_5406_);
v_snd_5407_ = lean_ctor_get(v___x_5405_, 1);
lean_inc(v_snd_5407_);
lean_dec_ref(v___x_5405_);
v___x_5408_ = lean_st_ref_take(v___y_5399_);
v_cache_5409_ = lean_ctor_get(v___x_5408_, 1);
v_zetaDeltaFVarIds_5410_ = lean_ctor_get(v___x_5408_, 2);
v_postponed_5411_ = lean_ctor_get(v___x_5408_, 3);
v_diag_5412_ = lean_ctor_get(v___x_5408_, 4);
v_isSharedCheck_5421_ = !lean_is_exclusive(v___x_5408_);
if (v_isSharedCheck_5421_ == 0)
{
lean_object* v_unused_5422_; 
v_unused_5422_ = lean_ctor_get(v___x_5408_, 0);
lean_dec(v_unused_5422_);
v___x_5414_ = v___x_5408_;
v_isShared_5415_ = v_isSharedCheck_5421_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_diag_5412_);
lean_inc(v_postponed_5411_);
lean_inc(v_zetaDeltaFVarIds_5410_);
lean_inc(v_cache_5409_);
lean_dec(v___x_5408_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5421_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v___x_5417_; 
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 0, v_snd_5407_);
v___x_5417_ = v___x_5414_;
goto v_reusejp_5416_;
}
else
{
lean_object* v_reuseFailAlloc_5420_; 
v_reuseFailAlloc_5420_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5420_, 0, v_snd_5407_);
lean_ctor_set(v_reuseFailAlloc_5420_, 1, v_cache_5409_);
lean_ctor_set(v_reuseFailAlloc_5420_, 2, v_zetaDeltaFVarIds_5410_);
lean_ctor_set(v_reuseFailAlloc_5420_, 3, v_postponed_5411_);
lean_ctor_set(v_reuseFailAlloc_5420_, 4, v_diag_5412_);
v___x_5417_ = v_reuseFailAlloc_5420_;
goto v_reusejp_5416_;
}
v_reusejp_5416_:
{
lean_object* v___x_5418_; lean_object* v___x_5419_; 
v___x_5418_ = lean_st_ref_set(v___y_5399_, v___x_5417_);
v___x_5419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5419_, 0, v_fst_5406_);
return v___x_5419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5423_, lean_object* v___y_5424_, lean_object* v___y_5425_){
_start:
{
lean_object* v_res_5426_; 
v_res_5426_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5423_, v___y_5424_);
lean_dec(v___y_5424_);
return v_res_5426_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_){
_start:
{
lean_object* v___x_5433_; 
v___x_5433_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5427_, v___y_5429_);
return v___x_5433_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5434_, lean_object* v___y_5435_, lean_object* v___y_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_){
_start:
{
lean_object* v_res_5440_; 
v_res_5440_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_);
lean_dec(v___y_5438_);
lean_dec_ref(v___y_5437_);
lean_dec(v___y_5436_);
lean_dec_ref(v___y_5435_);
return v_res_5440_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5441_, lean_object* v_opts_5442_, lean_object* v_act_5443_, lean_object* v_decl_5444_, lean_object* v___y_5445_, lean_object* v___y_5446_, lean_object* v___y_5447_, lean_object* v___y_5448_){
_start:
{
lean_object* v___x_5450_; lean_object* v___x_5451_; 
lean_inc(v___y_5448_);
lean_inc_ref(v___y_5447_);
lean_inc(v___y_5446_);
lean_inc_ref(v___y_5445_);
v___x_5450_ = lean_apply_4(v_act_5443_, v___y_5445_, v___y_5446_, v___y_5447_, v___y_5448_);
v___x_5451_ = l_Lean_profileitIOUnsafe___redArg(v_category_5441_, v_opts_5442_, v___x_5450_, v_decl_5444_);
return v___x_5451_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5452_, lean_object* v_opts_5453_, lean_object* v_act_5454_, lean_object* v_decl_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_, lean_object* v___y_5459_, lean_object* v___y_5460_){
_start:
{
lean_object* v_res_5461_; 
v_res_5461_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5452_, v_opts_5453_, v_act_5454_, v_decl_5455_, v___y_5456_, v___y_5457_, v___y_5458_, v___y_5459_);
lean_dec(v___y_5459_);
lean_dec_ref(v___y_5458_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec_ref(v_opts_5453_);
lean_dec_ref(v_category_5452_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5462_, lean_object* v_category_5463_, lean_object* v_opts_5464_, lean_object* v_act_5465_, lean_object* v_decl_5466_, lean_object* v___y_5467_, lean_object* v___y_5468_, lean_object* v___y_5469_, lean_object* v___y_5470_){
_start:
{
lean_object* v___x_5472_; 
v___x_5472_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5463_, v_opts_5464_, v_act_5465_, v_decl_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
return v___x_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5473_, lean_object* v_category_5474_, lean_object* v_opts_5475_, lean_object* v_act_5476_, lean_object* v_decl_5477_, lean_object* v___y_5478_, lean_object* v___y_5479_, lean_object* v___y_5480_, lean_object* v___y_5481_, lean_object* v___y_5482_){
_start:
{
lean_object* v_res_5483_; 
v_res_5483_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5473_, v_category_5474_, v_opts_5475_, v_act_5476_, v_decl_5477_, v___y_5478_, v___y_5479_, v___y_5480_, v___y_5481_);
lean_dec(v___y_5481_);
lean_dec_ref(v___y_5480_);
lean_dec(v___y_5479_);
lean_dec_ref(v___y_5478_);
lean_dec_ref(v_opts_5475_);
lean_dec_ref(v_category_5474_);
return v_res_5483_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5484_, uint8_t v_isExporting_5485_, lean_object* v___x_5486_, lean_object* v___y_5487_, lean_object* v___x_5488_, lean_object* v_a_x3f_5489_){
_start:
{
lean_object* v___x_5491_; lean_object* v_env_5492_; lean_object* v_nextMacroScope_5493_; lean_object* v_ngen_5494_; lean_object* v_auxDeclNGen_5495_; lean_object* v_traceState_5496_; lean_object* v_messages_5497_; lean_object* v_infoState_5498_; lean_object* v_snapshotTasks_5499_; lean_object* v___x_5501_; uint8_t v_isShared_5502_; uint8_t v_isSharedCheck_5524_; 
v___x_5491_ = lean_st_ref_take(v___y_5484_);
v_env_5492_ = lean_ctor_get(v___x_5491_, 0);
v_nextMacroScope_5493_ = lean_ctor_get(v___x_5491_, 1);
v_ngen_5494_ = lean_ctor_get(v___x_5491_, 2);
v_auxDeclNGen_5495_ = lean_ctor_get(v___x_5491_, 3);
v_traceState_5496_ = lean_ctor_get(v___x_5491_, 4);
v_messages_5497_ = lean_ctor_get(v___x_5491_, 6);
v_infoState_5498_ = lean_ctor_get(v___x_5491_, 7);
v_snapshotTasks_5499_ = lean_ctor_get(v___x_5491_, 8);
v_isSharedCheck_5524_ = !lean_is_exclusive(v___x_5491_);
if (v_isSharedCheck_5524_ == 0)
{
lean_object* v_unused_5525_; 
v_unused_5525_ = lean_ctor_get(v___x_5491_, 5);
lean_dec(v_unused_5525_);
v___x_5501_ = v___x_5491_;
v_isShared_5502_ = v_isSharedCheck_5524_;
goto v_resetjp_5500_;
}
else
{
lean_inc(v_snapshotTasks_5499_);
lean_inc(v_infoState_5498_);
lean_inc(v_messages_5497_);
lean_inc(v_traceState_5496_);
lean_inc(v_auxDeclNGen_5495_);
lean_inc(v_ngen_5494_);
lean_inc(v_nextMacroScope_5493_);
lean_inc(v_env_5492_);
lean_dec(v___x_5491_);
v___x_5501_ = lean_box(0);
v_isShared_5502_ = v_isSharedCheck_5524_;
goto v_resetjp_5500_;
}
v_resetjp_5500_:
{
lean_object* v___x_5503_; lean_object* v___x_5505_; 
v___x_5503_ = l_Lean_Environment_setExporting(v_env_5492_, v_isExporting_5485_);
if (v_isShared_5502_ == 0)
{
lean_ctor_set(v___x_5501_, 5, v___x_5486_);
lean_ctor_set(v___x_5501_, 0, v___x_5503_);
v___x_5505_ = v___x_5501_;
goto v_reusejp_5504_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5503_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_nextMacroScope_5493_);
lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_ngen_5494_);
lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_auxDeclNGen_5495_);
lean_ctor_set(v_reuseFailAlloc_5523_, 4, v_traceState_5496_);
lean_ctor_set(v_reuseFailAlloc_5523_, 5, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5523_, 6, v_messages_5497_);
lean_ctor_set(v_reuseFailAlloc_5523_, 7, v_infoState_5498_);
lean_ctor_set(v_reuseFailAlloc_5523_, 8, v_snapshotTasks_5499_);
v___x_5505_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5504_;
}
v_reusejp_5504_:
{
lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v_mctx_5508_; lean_object* v_zetaDeltaFVarIds_5509_; lean_object* v_postponed_5510_; lean_object* v_diag_5511_; lean_object* v___x_5513_; uint8_t v_isShared_5514_; uint8_t v_isSharedCheck_5521_; 
v___x_5506_ = lean_st_ref_set(v___y_5484_, v___x_5505_);
v___x_5507_ = lean_st_ref_take(v___y_5487_);
v_mctx_5508_ = lean_ctor_get(v___x_5507_, 0);
v_zetaDeltaFVarIds_5509_ = lean_ctor_get(v___x_5507_, 2);
v_postponed_5510_ = lean_ctor_get(v___x_5507_, 3);
v_diag_5511_ = lean_ctor_get(v___x_5507_, 4);
v_isSharedCheck_5521_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; 
v_unused_5522_ = lean_ctor_get(v___x_5507_, 1);
lean_dec(v_unused_5522_);
v___x_5513_ = v___x_5507_;
v_isShared_5514_ = v_isSharedCheck_5521_;
goto v_resetjp_5512_;
}
else
{
lean_inc(v_diag_5511_);
lean_inc(v_postponed_5510_);
lean_inc(v_zetaDeltaFVarIds_5509_);
lean_inc(v_mctx_5508_);
lean_dec(v___x_5507_);
v___x_5513_ = lean_box(0);
v_isShared_5514_ = v_isSharedCheck_5521_;
goto v_resetjp_5512_;
}
v_resetjp_5512_:
{
lean_object* v___x_5516_; 
if (v_isShared_5514_ == 0)
{
lean_ctor_set(v___x_5513_, 1, v___x_5488_);
v___x_5516_ = v___x_5513_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v_mctx_5508_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v___x_5488_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_zetaDeltaFVarIds_5509_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v_postponed_5510_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v_diag_5511_);
v___x_5516_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5517_; lean_object* v___x_5518_; lean_object* v___x_5519_; 
v___x_5517_ = lean_st_ref_set(v___y_5487_, v___x_5516_);
v___x_5518_ = lean_box(0);
v___x_5519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5519_, 0, v___x_5518_);
return v___x_5519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5526_, lean_object* v_isExporting_5527_, lean_object* v___x_5528_, lean_object* v___y_5529_, lean_object* v___x_5530_, lean_object* v_a_x3f_5531_, lean_object* v___y_5532_){
_start:
{
uint8_t v_isExporting_boxed_5533_; lean_object* v_res_5534_; 
v_isExporting_boxed_5533_ = lean_unbox(v_isExporting_5527_);
v_res_5534_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5526_, v_isExporting_boxed_5533_, v___x_5528_, v___y_5529_, v___x_5530_, v_a_x3f_5531_);
lean_dec(v_a_x3f_5531_);
lean_dec(v___y_5529_);
lean_dec(v___y_5526_);
return v_res_5534_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5535_; 
v___x_5535_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5535_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5536_; lean_object* v___x_5537_; 
v___x_5536_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5537_, 0, v___x_5536_);
return v___x_5537_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; 
v___x_5538_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5539_, 0, v___x_5538_);
lean_ctor_set(v___x_5539_, 1, v___x_5538_);
return v___x_5539_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5540_; lean_object* v___x_5541_; 
v___x_5540_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5541_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5541_, 0, v___x_5540_);
lean_ctor_set(v___x_5541_, 1, v___x_5540_);
lean_ctor_set(v___x_5541_, 2, v___x_5540_);
lean_ctor_set(v___x_5541_, 3, v___x_5540_);
lean_ctor_set(v___x_5541_, 4, v___x_5540_);
lean_ctor_set(v___x_5541_, 5, v___x_5540_);
return v___x_5541_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5542_, uint8_t v_isExporting_5543_, lean_object* v___y_5544_, lean_object* v___y_5545_, lean_object* v___y_5546_, lean_object* v___y_5547_){
_start:
{
lean_object* v___x_5549_; lean_object* v_env_5550_; uint8_t v_isExporting_5551_; lean_object* v___x_5552_; lean_object* v_env_5553_; lean_object* v_nextMacroScope_5554_; lean_object* v_ngen_5555_; lean_object* v_auxDeclNGen_5556_; lean_object* v_traceState_5557_; lean_object* v_messages_5558_; lean_object* v_infoState_5559_; lean_object* v_snapshotTasks_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5614_; 
v___x_5549_ = lean_st_ref_get(v___y_5547_);
v_env_5550_ = lean_ctor_get(v___x_5549_, 0);
lean_inc_ref(v_env_5550_);
lean_dec(v___x_5549_);
v_isExporting_5551_ = lean_ctor_get_uint8(v_env_5550_, sizeof(void*)*8);
lean_dec_ref(v_env_5550_);
v___x_5552_ = lean_st_ref_take(v___y_5547_);
v_env_5553_ = lean_ctor_get(v___x_5552_, 0);
v_nextMacroScope_5554_ = lean_ctor_get(v___x_5552_, 1);
v_ngen_5555_ = lean_ctor_get(v___x_5552_, 2);
v_auxDeclNGen_5556_ = lean_ctor_get(v___x_5552_, 3);
v_traceState_5557_ = lean_ctor_get(v___x_5552_, 4);
v_messages_5558_ = lean_ctor_get(v___x_5552_, 6);
v_infoState_5559_ = lean_ctor_get(v___x_5552_, 7);
v_snapshotTasks_5560_ = lean_ctor_get(v___x_5552_, 8);
v_isSharedCheck_5614_ = !lean_is_exclusive(v___x_5552_);
if (v_isSharedCheck_5614_ == 0)
{
lean_object* v_unused_5615_; 
v_unused_5615_ = lean_ctor_get(v___x_5552_, 5);
lean_dec(v_unused_5615_);
v___x_5562_ = v___x_5552_;
v_isShared_5563_ = v_isSharedCheck_5614_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_snapshotTasks_5560_);
lean_inc(v_infoState_5559_);
lean_inc(v_messages_5558_);
lean_inc(v_traceState_5557_);
lean_inc(v_auxDeclNGen_5556_);
lean_inc(v_ngen_5555_);
lean_inc(v_nextMacroScope_5554_);
lean_inc(v_env_5553_);
lean_dec(v___x_5552_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5614_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5564_; lean_object* v___x_5565_; lean_object* v___x_5567_; 
v___x_5564_ = l_Lean_Environment_setExporting(v_env_5553_, v_isExporting_5543_);
v___x_5565_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 5, v___x_5565_);
lean_ctor_set(v___x_5562_, 0, v___x_5564_);
v___x_5567_ = v___x_5562_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5613_; 
v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5613_, 1, v_nextMacroScope_5554_);
lean_ctor_set(v_reuseFailAlloc_5613_, 2, v_ngen_5555_);
lean_ctor_set(v_reuseFailAlloc_5613_, 3, v_auxDeclNGen_5556_);
lean_ctor_set(v_reuseFailAlloc_5613_, 4, v_traceState_5557_);
lean_ctor_set(v_reuseFailAlloc_5613_, 5, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5613_, 6, v_messages_5558_);
lean_ctor_set(v_reuseFailAlloc_5613_, 7, v_infoState_5559_);
lean_ctor_set(v_reuseFailAlloc_5613_, 8, v_snapshotTasks_5560_);
v___x_5567_ = v_reuseFailAlloc_5613_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
lean_object* v___x_5568_; lean_object* v___x_5569_; lean_object* v_mctx_5570_; lean_object* v_zetaDeltaFVarIds_5571_; lean_object* v_postponed_5572_; lean_object* v_diag_5573_; lean_object* v___x_5575_; uint8_t v_isShared_5576_; uint8_t v_isSharedCheck_5611_; 
v___x_5568_ = lean_st_ref_set(v___y_5547_, v___x_5567_);
v___x_5569_ = lean_st_ref_take(v___y_5545_);
v_mctx_5570_ = lean_ctor_get(v___x_5569_, 0);
v_zetaDeltaFVarIds_5571_ = lean_ctor_get(v___x_5569_, 2);
v_postponed_5572_ = lean_ctor_get(v___x_5569_, 3);
v_diag_5573_ = lean_ctor_get(v___x_5569_, 4);
v_isSharedCheck_5611_ = !lean_is_exclusive(v___x_5569_);
if (v_isSharedCheck_5611_ == 0)
{
lean_object* v_unused_5612_; 
v_unused_5612_ = lean_ctor_get(v___x_5569_, 1);
lean_dec(v_unused_5612_);
v___x_5575_ = v___x_5569_;
v_isShared_5576_ = v_isSharedCheck_5611_;
goto v_resetjp_5574_;
}
else
{
lean_inc(v_diag_5573_);
lean_inc(v_postponed_5572_);
lean_inc(v_zetaDeltaFVarIds_5571_);
lean_inc(v_mctx_5570_);
lean_dec(v___x_5569_);
v___x_5575_ = lean_box(0);
v_isShared_5576_ = v_isSharedCheck_5611_;
goto v_resetjp_5574_;
}
v_resetjp_5574_:
{
lean_object* v___x_5577_; lean_object* v___x_5579_; 
v___x_5577_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5576_ == 0)
{
lean_ctor_set(v___x_5575_, 1, v___x_5577_);
v___x_5579_ = v___x_5575_;
goto v_reusejp_5578_;
}
else
{
lean_object* v_reuseFailAlloc_5610_; 
v_reuseFailAlloc_5610_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5610_, 0, v_mctx_5570_);
lean_ctor_set(v_reuseFailAlloc_5610_, 1, v___x_5577_);
lean_ctor_set(v_reuseFailAlloc_5610_, 2, v_zetaDeltaFVarIds_5571_);
lean_ctor_set(v_reuseFailAlloc_5610_, 3, v_postponed_5572_);
lean_ctor_set(v_reuseFailAlloc_5610_, 4, v_diag_5573_);
v___x_5579_ = v_reuseFailAlloc_5610_;
goto v_reusejp_5578_;
}
v_reusejp_5578_:
{
lean_object* v___x_5580_; lean_object* v_r_5581_; 
v___x_5580_ = lean_st_ref_set(v___y_5545_, v___x_5579_);
lean_inc(v___y_5547_);
lean_inc_ref(v___y_5546_);
lean_inc(v___y_5545_);
lean_inc_ref(v___y_5544_);
v_r_5581_ = lean_apply_5(v_x_5542_, v___y_5544_, v___y_5545_, v___y_5546_, v___y_5547_, lean_box(0));
if (lean_obj_tag(v_r_5581_) == 0)
{
lean_object* v_a_5582_; lean_object* v___x_5584_; uint8_t v_isShared_5585_; uint8_t v_isSharedCheck_5598_; 
v_a_5582_ = lean_ctor_get(v_r_5581_, 0);
v_isSharedCheck_5598_ = !lean_is_exclusive(v_r_5581_);
if (v_isSharedCheck_5598_ == 0)
{
v___x_5584_ = v_r_5581_;
v_isShared_5585_ = v_isSharedCheck_5598_;
goto v_resetjp_5583_;
}
else
{
lean_inc(v_a_5582_);
lean_dec(v_r_5581_);
v___x_5584_ = lean_box(0);
v_isShared_5585_ = v_isSharedCheck_5598_;
goto v_resetjp_5583_;
}
v_resetjp_5583_:
{
lean_object* v___x_5587_; 
lean_inc(v_a_5582_);
if (v_isShared_5585_ == 0)
{
lean_ctor_set_tag(v___x_5584_, 1);
v___x_5587_ = v___x_5584_;
goto v_reusejp_5586_;
}
else
{
lean_object* v_reuseFailAlloc_5597_; 
v_reuseFailAlloc_5597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5582_);
v___x_5587_ = v_reuseFailAlloc_5597_;
goto v_reusejp_5586_;
}
v_reusejp_5586_:
{
lean_object* v___x_5588_; lean_object* v___x_5590_; uint8_t v_isShared_5591_; uint8_t v_isSharedCheck_5595_; 
v___x_5588_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5547_, v_isExporting_5551_, v___x_5565_, v___y_5545_, v___x_5577_, v___x_5587_);
lean_dec_ref(v___x_5587_);
v_isSharedCheck_5595_ = !lean_is_exclusive(v___x_5588_);
if (v_isSharedCheck_5595_ == 0)
{
lean_object* v_unused_5596_; 
v_unused_5596_ = lean_ctor_get(v___x_5588_, 0);
lean_dec(v_unused_5596_);
v___x_5590_ = v___x_5588_;
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
else
{
lean_dec(v___x_5588_);
v___x_5590_ = lean_box(0);
v_isShared_5591_ = v_isSharedCheck_5595_;
goto v_resetjp_5589_;
}
v_resetjp_5589_:
{
lean_object* v___x_5593_; 
if (v_isShared_5591_ == 0)
{
lean_ctor_set(v___x_5590_, 0, v_a_5582_);
v___x_5593_ = v___x_5590_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v_a_5582_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
}
else
{
lean_object* v_a_5599_; lean_object* v___x_5600_; lean_object* v___x_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5608_; 
v_a_5599_ = lean_ctor_get(v_r_5581_, 0);
lean_inc(v_a_5599_);
lean_dec_ref_known(v_r_5581_, 1);
v___x_5600_ = lean_box(0);
v___x_5601_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5547_, v_isExporting_5551_, v___x_5565_, v___y_5545_, v___x_5577_, v___x_5600_);
v_isSharedCheck_5608_ = !lean_is_exclusive(v___x_5601_);
if (v_isSharedCheck_5608_ == 0)
{
lean_object* v_unused_5609_; 
v_unused_5609_ = lean_ctor_get(v___x_5601_, 0);
lean_dec(v_unused_5609_);
v___x_5603_ = v___x_5601_;
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
else
{
lean_dec(v___x_5601_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5608_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v___x_5606_; 
if (v_isShared_5604_ == 0)
{
lean_ctor_set_tag(v___x_5603_, 1);
lean_ctor_set(v___x_5603_, 0, v_a_5599_);
v___x_5606_ = v___x_5603_;
goto v_reusejp_5605_;
}
else
{
lean_object* v_reuseFailAlloc_5607_; 
v_reuseFailAlloc_5607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5607_, 0, v_a_5599_);
v___x_5606_ = v_reuseFailAlloc_5607_;
goto v_reusejp_5605_;
}
v_reusejp_5605_:
{
return v___x_5606_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5616_, lean_object* v_isExporting_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_){
_start:
{
uint8_t v_isExporting_boxed_5623_; lean_object* v_res_5624_; 
v_isExporting_boxed_5623_ = lean_unbox(v_isExporting_5617_);
v_res_5624_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5616_, v_isExporting_boxed_5623_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
lean_dec(v___y_5621_);
lean_dec_ref(v___y_5620_);
lean_dec(v___y_5619_);
lean_dec_ref(v___y_5618_);
return v_res_5624_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5625_, uint8_t v_when_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_){
_start:
{
if (v_when_5626_ == 0)
{
lean_object* v___x_5632_; 
lean_inc(v___y_5630_);
lean_inc_ref(v___y_5629_);
lean_inc(v___y_5628_);
lean_inc_ref(v___y_5627_);
v___x_5632_ = lean_apply_5(v_x_5625_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_, lean_box(0));
return v___x_5632_;
}
else
{
uint8_t v___x_5633_; lean_object* v___x_5634_; 
v___x_5633_ = 0;
v___x_5634_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5625_, v___x_5633_, v___y_5627_, v___y_5628_, v___y_5629_, v___y_5630_);
return v___x_5634_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5635_, lean_object* v_when_5636_, lean_object* v___y_5637_, lean_object* v___y_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_){
_start:
{
uint8_t v_when_boxed_5642_; lean_object* v_res_5643_; 
v_when_boxed_5642_ = lean_unbox(v_when_5636_);
v_res_5643_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5635_, v_when_boxed_5642_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec(v___y_5638_);
lean_dec_ref(v___y_5637_);
return v_res_5643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5644_, lean_object* v___y_5645_, lean_object* v___y_5646_, lean_object* v___y_5647_, lean_object* v___y_5648_){
_start:
{
lean_object* v___x_5650_; lean_object* v_a_5651_; lean_object* v___x_5652_; uint8_t v___x_5653_; lean_object* v___x_5654_; 
v___x_5650_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5644_, v___y_5646_);
v_a_5651_ = lean_ctor_get(v___x_5650_, 0);
lean_inc(v_a_5651_);
lean_dec_ref(v___x_5650_);
v___x_5652_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5652_, 0, v_a_5651_);
v___x_5653_ = 1;
v___x_5654_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5652_, v___x_5653_, v___y_5645_, v___y_5646_, v___y_5647_, v___y_5648_);
return v___x_5654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5655_, lean_object* v___y_5656_, lean_object* v___y_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_){
_start:
{
lean_object* v_res_5661_; 
v_res_5661_ = l_Lean_Meta_letToHave___lam__0(v_e_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec(v___y_5657_);
lean_dec_ref(v___y_5656_);
return v_res_5661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5663_, lean_object* v_a_5664_, lean_object* v_a_5665_, lean_object* v_a_5666_, lean_object* v_a_5667_){
_start:
{
lean_object* v_options_5669_; lean_object* v___f_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5673_; 
v_options_5669_ = lean_ctor_get(v_a_5666_, 2);
v___f_5670_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5670_, 0, v_e_5663_);
v___x_5671_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5672_ = lean_box(0);
v___x_5673_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5671_, v_options_5669_, v___f_5670_, v___x_5672_, v_a_5664_, v_a_5665_, v_a_5666_, v_a_5667_);
return v___x_5673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5674_, lean_object* v_a_5675_, lean_object* v_a_5676_, lean_object* v_a_5677_, lean_object* v_a_5678_, lean_object* v_a_5679_){
_start:
{
lean_object* v_res_5680_; 
v_res_5680_ = l_Lean_Meta_letToHave(v_e_5674_, v_a_5675_, v_a_5676_, v_a_5677_, v_a_5678_);
lean_dec(v_a_5678_);
lean_dec_ref(v_a_5677_);
lean_dec(v_a_5676_);
lean_dec_ref(v_a_5675_);
return v_res_5680_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5681_, lean_object* v_x_5682_, uint8_t v_isExporting_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_, lean_object* v___y_5686_, lean_object* v___y_5687_){
_start:
{
lean_object* v___x_5689_; 
v___x_5689_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5682_, v_isExporting_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
return v___x_5689_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5690_, lean_object* v_x_5691_, lean_object* v_isExporting_5692_, lean_object* v___y_5693_, lean_object* v___y_5694_, lean_object* v___y_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_){
_start:
{
uint8_t v_isExporting_boxed_5698_; lean_object* v_res_5699_; 
v_isExporting_boxed_5698_ = lean_unbox(v_isExporting_5692_);
v_res_5699_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5690_, v_x_5691_, v_isExporting_boxed_5698_, v___y_5693_, v___y_5694_, v___y_5695_, v___y_5696_);
lean_dec(v___y_5696_);
lean_dec_ref(v___y_5695_);
lean_dec(v___y_5694_);
lean_dec_ref(v___y_5693_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5700_, lean_object* v_x_5701_, uint8_t v_when_5702_, lean_object* v___y_5703_, lean_object* v___y_5704_, lean_object* v___y_5705_, lean_object* v___y_5706_){
_start:
{
lean_object* v___x_5708_; 
v___x_5708_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5701_, v_when_5702_, v___y_5703_, v___y_5704_, v___y_5705_, v___y_5706_);
return v___x_5708_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5709_, lean_object* v_x_5710_, lean_object* v_when_5711_, lean_object* v___y_5712_, lean_object* v___y_5713_, lean_object* v___y_5714_, lean_object* v___y_5715_, lean_object* v___y_5716_){
_start:
{
uint8_t v_when_boxed_5717_; lean_object* v_res_5718_; 
v_when_boxed_5717_ = lean_unbox(v_when_5711_);
v_res_5718_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5709_, v_x_5710_, v_when_boxed_5717_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
lean_dec(v___y_5715_);
lean_dec_ref(v___y_5714_);
lean_dec(v___y_5713_);
lean_dec_ref(v___y_5712_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5775_; uint8_t v___x_5776_; lean_object* v___x_5777_; lean_object* v___x_5778_; 
v___x_5775_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5776_ = 0;
v___x_5777_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5778_ = l_Lean_registerTraceClass(v___x_5775_, v___x_5776_, v___x_5777_);
if (lean_obj_tag(v___x_5778_) == 0)
{
lean_object* v___x_5779_; lean_object* v___x_5780_; 
lean_dec_ref_known(v___x_5778_, 1);
v___x_5779_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5780_ = l_Lean_registerTraceClass(v___x_5779_, v___x_5776_, v___x_5777_);
return v___x_5780_;
}
else
{
return v___x_5778_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5781_){
_start:
{
lean_object* v_res_5782_; 
v_res_5782_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5782_;
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
