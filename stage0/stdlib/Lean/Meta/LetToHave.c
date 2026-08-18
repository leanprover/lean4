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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
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
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2;
static const lean_array_object l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3 = (const lean_object*)&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_value;
static lean_once_cell_t l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__4;
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
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object*, lean_object*);
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
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(lean_object* v_m_48_, lean_object* v_query_49_, lean_object* v_x_50_, lean_object* v_x_51_, lean_object* v_x_52_){
_start:
{
lean_object* v_zero_53_; uint8_t v_isZero_54_; 
v_zero_53_ = lean_unsigned_to_nat(0u);
v_isZero_54_ = lean_nat_dec_eq(v_x_51_, v_zero_53_);
if (v_isZero_54_ == 1)
{
lean_dec(v_x_52_);
lean_dec(v_x_51_);
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_55_; 
v___x_55_ = lean_box(2);
return v___x_55_;
}
else
{
lean_object* v_val_56_; lean_object* v___x_58_; uint8_t v_isShared_59_; uint8_t v_isSharedCheck_63_; 
v_val_56_ = lean_ctor_get(v_x_50_, 0);
v_isSharedCheck_63_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_63_ == 0)
{
v___x_58_ = v_x_50_;
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
else
{
lean_inc(v_val_56_);
lean_dec(v_x_50_);
v___x_58_ = lean_box(0);
v_isShared_59_ = v_isSharedCheck_63_;
goto v_resetjp_57_;
}
v_resetjp_57_:
{
lean_object* v___x_61_; 
if (v_isShared_59_ == 0)
{
v___x_61_ = v___x_58_;
goto v_reusejp_60_;
}
else
{
lean_object* v_reuseFailAlloc_62_; 
v_reuseFailAlloc_62_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_62_, 0, v_val_56_);
v___x_61_ = v_reuseFailAlloc_62_;
goto v_reusejp_60_;
}
v_reusejp_60_:
{
return v___x_61_;
}
}
}
}
else
{
lean_object* v_keyArray_64_; lean_object* v_valueArray_65_; lean_object* v___x_66_; uint8_t v_isSome_67_; 
v_keyArray_64_ = lean_ctor_get(v_m_48_, 1);
v_valueArray_65_ = lean_ctor_get(v_m_48_, 2);
v___x_66_ = lean_array_fget_borrowed(v_keyArray_64_, v_x_52_);
v_isSome_67_ = lean_noption_is_some(v___x_66_);
if (v_isSome_67_ == 0)
{
lean_dec(v_x_51_);
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_68_, 0, v_x_52_);
return v___x_68_;
}
else
{
lean_object* v_val_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_76_; 
lean_dec(v_x_52_);
v_val_69_ = lean_ctor_get(v_x_50_, 0);
v_isSharedCheck_76_ = !lean_is_exclusive(v_x_50_);
if (v_isSharedCheck_76_ == 0)
{
v___x_71_ = v_x_50_;
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_val_69_);
lean_dec(v_x_50_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_76_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v___x_74_; 
if (v_isShared_72_ == 0)
{
v___x_74_ = v___x_71_;
goto v_reusejp_73_;
}
else
{
lean_object* v_reuseFailAlloc_75_; 
v_reuseFailAlloc_75_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_75_, 0, v_val_69_);
v___x_74_ = v_reuseFailAlloc_75_;
goto v_reusejp_73_;
}
v_reusejp_73_:
{
return v___x_74_;
}
}
}
}
else
{
lean_object* v_one_77_; lean_object* v_n_78_; lean_object* v___y_80_; 
v_one_77_ = lean_unsigned_to_nat(1u);
v_n_78_ = lean_nat_sub(v_x_51_, v_one_77_);
lean_dec(v_x_51_);
if (v_isSome_67_ == 0)
{
goto v___jp_86_;
}
else
{
lean_object* v___x_88_; uint8_t v_isSome_89_; 
v___x_88_ = lean_array_fget_borrowed(v_valueArray_65_, v_x_52_);
v_isSome_89_ = lean_noption_is_some(v___x_88_);
if (v_isSome_89_ == 0)
{
goto v___jp_86_;
}
else
{
lean_object* v_val_90_; uint8_t v___x_91_; 
lean_inc(v___x_66_);
v_val_90_ = lean_noption_get(v___x_66_);
v___x_91_ = l_Lean_ExprStructEq_beq(v_val_90_, v_query_49_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_93_; uint8_t v___x_94_; 
lean_dec(v_val_90_);
v___x_92_ = lean_array_get_size(v_keyArray_64_);
v___x_93_ = lean_nat_add(v_x_52_, v_one_77_);
lean_dec(v_x_52_);
v___x_94_ = lean_nat_dec_lt(v___x_93_, v___x_92_);
if (v___x_94_ == 0)
{
lean_dec(v___x_93_);
v_x_51_ = v_n_78_;
v_x_52_ = v_zero_53_;
goto _start;
}
else
{
v_x_51_ = v_n_78_;
v_x_52_ = v___x_93_;
goto _start;
}
}
else
{
lean_object* v_val_97_; lean_object* v___x_98_; 
lean_dec(v_n_78_);
lean_dec(v_x_50_);
lean_inc(v___x_88_);
v_val_97_ = lean_noption_get(v___x_88_);
v___x_98_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_98_, 0, v_x_52_);
lean_ctor_set(v___x_98_, 1, v_val_90_);
lean_ctor_set(v___x_98_, 2, v_val_97_);
return v___x_98_;
}
}
}
v___jp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; uint8_t v___x_83_; 
v___x_81_ = lean_array_get_size(v_keyArray_64_);
v___x_82_ = lean_nat_add(v_x_52_, v_one_77_);
lean_dec(v_x_52_);
v___x_83_ = lean_nat_dec_lt(v___x_82_, v___x_81_);
if (v___x_83_ == 0)
{
lean_dec(v___x_82_);
v_x_50_ = v___y_80_;
v_x_51_ = v_n_78_;
v_x_52_ = v_zero_53_;
goto _start;
}
else
{
v_x_50_ = v___y_80_;
v_x_51_ = v_n_78_;
v_x_52_ = v___x_82_;
goto _start;
}
}
v___jp_86_:
{
if (lean_obj_tag(v_x_50_) == 0)
{
lean_object* v___x_87_; 
lean_inc(v_x_52_);
v___x_87_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_87_, 0, v_x_52_);
v___y_80_ = v___x_87_;
goto v___jp_79_;
}
else
{
v___y_80_ = v_x_50_;
goto v___jp_79_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg___boxed(lean_object* v_m_99_, lean_object* v_query_100_, lean_object* v_x_101_, lean_object* v_x_102_, lean_object* v_x_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_m_99_, v_query_100_, v_x_101_, v_x_102_, v_x_103_);
lean_dec_ref(v_query_100_);
lean_dec_ref(v_m_99_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(lean_object* v_m_105_, lean_object* v_query_106_){
_start:
{
lean_object* v_keyArray_107_; lean_object* v___x_108_; uint64_t v___x_109_; uint64_t v___x_110_; uint64_t v___x_111_; uint64_t v_fold_112_; uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v___x_115_; size_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; size_t v___x_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_keyArray_107_ = lean_ctor_get(v_m_105_, 1);
v___x_108_ = lean_array_get_size(v_keyArray_107_);
v___x_109_ = l_Lean_ExprStructEq_hash(v_query_106_);
v___x_110_ = 32ULL;
v___x_111_ = lean_uint64_shift_right(v___x_109_, v___x_110_);
v_fold_112_ = lean_uint64_xor(v___x_109_, v___x_111_);
v___x_113_ = 16ULL;
v___x_114_ = lean_uint64_shift_right(v_fold_112_, v___x_113_);
v___x_115_ = lean_uint64_xor(v_fold_112_, v___x_114_);
v___x_116_ = lean_uint64_to_usize(v___x_115_);
v___x_117_ = lean_usize_of_nat(v___x_108_);
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_sub(v___x_117_, v___x_118_);
v___x_120_ = lean_usize_land(v___x_116_, v___x_119_);
v___x_121_ = lean_usize_to_nat(v___x_120_);
v___x_122_ = lean_box(0);
v___x_123_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_m_105_, v_query_106_, v___x_122_, v___x_108_, v___x_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg___boxed(lean_object* v_m_124_, lean_object* v_query_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_m_124_, v_query_125_);
lean_dec_ref(v_query_125_);
lean_dec_ref(v_m_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___redArg(lean_object* v_b_127_, lean_object* v_acc_128_, lean_object* v_i_129_){
_start:
{
lean_object* v___y_131_; lean_object* v_keyArray_139_; lean_object* v_valueArray_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_keyArray_139_ = lean_ctor_get(v_b_127_, 1);
v_valueArray_140_ = lean_ctor_get(v_b_127_, 2);
v___x_141_ = lean_array_get_size(v_keyArray_139_);
v___x_142_ = lean_nat_dec_lt(v_i_129_, v___x_141_);
if (v___x_142_ == 0)
{
lean_dec(v_i_129_);
return v_acc_128_;
}
else
{
lean_object* v___x_143_; uint8_t v_isSome_144_; 
v___x_143_ = lean_array_fget_borrowed(v_keyArray_139_, v_i_129_);
v_isSome_144_ = lean_noption_is_some(v___x_143_);
if (v_isSome_144_ == 0)
{
goto v___jp_135_;
}
else
{
lean_object* v___x_145_; uint8_t v_isSome_146_; 
v___x_145_ = lean_array_fget_borrowed(v_valueArray_140_, v_i_129_);
v_isSome_146_ = lean_noption_is_some(v___x_145_);
if (v_isSome_146_ == 0)
{
goto v___jp_135_;
}
else
{
lean_object* v_val_147_; lean_object* v_val_148_; lean_object* v_i_150_; lean_object* v___x_155_; 
lean_inc(v___x_143_);
v_val_147_ = lean_noption_get(v___x_143_);
lean_inc(v___x_145_);
v_val_148_ = lean_noption_get(v___x_145_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_acc_128_, v_val_147_);
switch(lean_obj_tag(v___x_155_))
{
case 0:
{
lean_object* v_index_156_; lean_object* v_size_157_; lean_object* v___x_158_; 
v_index_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_index_156_);
lean_dec_ref_known(v___x_155_, 3);
v_size_157_ = lean_ctor_get(v_acc_128_, 0);
lean_inc(v_size_157_);
v___x_158_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_128_, v_size_157_, v_index_156_, v_val_147_, v_val_148_);
lean_dec(v_index_156_);
v___y_131_ = v___x_158_;
goto v___jp_130_;
}
case 1:
{
lean_object* v_index_159_; 
v_index_159_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_index_159_);
lean_dec_ref_known(v___x_155_, 1);
v_i_150_ = v_index_159_;
goto v___jp_149_;
}
default: 
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = lean_unsigned_to_nat(0u);
v___x_161_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_128_, v___x_160_);
if (lean_obj_tag(v___x_161_) == 0)
{
lean_object* v_index_162_; 
v_index_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_index_162_);
lean_dec_ref_known(v___x_161_, 1);
v_i_150_ = v_index_162_;
goto v___jp_149_;
}
else
{
lean_dec(v_val_148_);
lean_dec(v_val_147_);
v___y_131_ = v_acc_128_;
goto v___jp_130_;
}
}
}
v___jp_149_:
{
lean_object* v_size_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; 
v_size_151_ = lean_ctor_get(v_acc_128_, 0);
v___x_152_ = lean_unsigned_to_nat(1u);
v___x_153_ = lean_nat_add(v_size_151_, v___x_152_);
v___x_154_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_128_, v___x_153_, v_i_150_, v_val_147_, v_val_148_);
lean_dec(v_i_150_);
v___y_131_ = v___x_154_;
goto v___jp_130_;
}
}
}
}
v___jp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_i_129_, v___x_132_);
lean_dec(v_i_129_);
v_acc_128_ = v___y_131_;
v_i_129_ = v___x_133_;
goto _start;
}
v___jp_135_:
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = lean_nat_add(v_i_129_, v___x_136_);
lean_dec(v_i_129_);
v_i_129_ = v___x_137_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_163_, lean_object* v_acc_164_, lean_object* v_i_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___redArg(v_b_163_, v_acc_164_, v_i_165_);
lean_dec_ref(v_b_163_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___redArg(lean_object* v_init_167_, lean_object* v_b_168_){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___redArg(v_b_168_, v_init_167_, v___x_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___redArg___boxed(lean_object* v_init_171_, lean_object* v_b_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___redArg(v_init_171_, v_b_172_);
lean_dec_ref(v_b_172_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(lean_object* v_m_174_){
_start:
{
lean_object* v_keyArray_175_; lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v_cellCount_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v_target_182_; lean_object* v___x_183_; 
v_keyArray_175_ = lean_ctor_get(v_m_174_, 1);
v___x_176_ = lean_array_get_size(v_keyArray_175_);
v___x_177_ = lean_unsigned_to_nat(2u);
v_cellCount_178_ = lean_nat_mul(v___x_176_, v___x_177_);
v___x_179_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_178_);
v___x_180_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_178_);
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_178_);
v_target_182_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_182_, 0, v___x_179_);
lean_ctor_set(v_target_182_, 1, v___x_180_);
lean_ctor_set(v_target_182_, 2, v___x_181_);
v___x_183_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___redArg(v_target_182_, v_m_174_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg___boxed(lean_object* v_m_184_){
_start:
{
lean_object* v_res_185_; 
v_res_185_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_m_184_);
lean_dec_ref(v_m_184_);
return v_res_185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(lean_object* v_r_186_, lean_object* v_a_187_, lean_object* v_a_188_, lean_object* v_a_189_, lean_object* v_a_190_, lean_object* v_a_191_){
_start:
{
lean_object* v_type_x3f_193_; 
v_type_x3f_193_ = lean_ctor_get(v_r_186_, 1);
lean_inc(v_type_x3f_193_);
if (lean_obj_tag(v_type_x3f_193_) == 1)
{
lean_object* v_val_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec_ref(v_r_186_);
v_val_194_ = lean_ctor_get(v_type_x3f_193_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v_type_x3f_193_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v_type_x3f_193_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_val_194_);
lean_dec(v_type_x3f_193_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
lean_ctor_set_tag(v___x_196_, 0);
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_val_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
else
{
lean_object* v_expr_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_296_; 
lean_dec(v_type_x3f_193_);
v_expr_202_ = lean_ctor_get(v_r_186_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v_r_186_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v_r_186_, 1);
lean_dec(v_unused_297_);
v___x_204_ = v_r_186_;
v_isShared_205_ = v_isSharedCheck_296_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_expr_202_);
lean_dec(v_r_186_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_296_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_206_; 
lean_inc(v_a_191_);
lean_inc_ref(v_a_190_);
lean_inc(v_a_189_);
lean_inc_ref(v_a_188_);
lean_inc_ref(v_expr_202_);
v___x_206_ = lean_infer_type(v_expr_202_, v_a_188_, v_a_189_, v_a_190_, v_a_191_);
if (lean_obj_tag(v___x_206_) == 0)
{
lean_object* v_a_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_295_; 
v_a_207_ = lean_ctor_get(v___x_206_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_206_);
if (v_isSharedCheck_295_ == 0)
{
v___x_209_ = v___x_206_;
v_isShared_210_ = v_isSharedCheck_295_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_a_207_);
lean_dec(v___x_206_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_295_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
lean_object* v___x_211_; lean_object* v_count_212_; lean_object* v_results_213_; lean_object* v___x_215_; uint8_t v_isShared_216_; uint8_t v_isSharedCheck_294_; 
v___x_211_ = lean_st_ref_take(v_a_187_);
v_count_212_ = lean_ctor_get(v___x_211_, 0);
v_results_213_ = lean_ctor_get(v___x_211_, 1);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_294_ == 0)
{
v___x_215_ = v___x_211_;
v_isShared_216_ = v_isSharedCheck_294_;
goto v_resetjp_214_;
}
else
{
lean_inc(v_results_213_);
lean_inc(v_count_212_);
lean_dec(v___x_211_);
v___x_215_ = lean_box(0);
v_isShared_216_ = v_isSharedCheck_294_;
goto v_resetjp_214_;
}
v_resetjp_214_:
{
lean_object* v___y_218_; lean_object* v___x_226_; lean_object* v___x_228_; 
lean_inc(v_a_207_);
v___x_226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_226_, 0, v_a_207_);
lean_inc_ref(v_expr_202_);
if (v_isShared_205_ == 0)
{
lean_ctor_set(v___x_204_, 1, v___x_226_);
v___x_228_ = v___x_204_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_expr_202_);
lean_ctor_set(v_reuseFailAlloc_293_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_293_;
goto v_reusejp_227_;
}
v___jp_217_:
{
lean_object* v___x_220_; 
if (v_isShared_216_ == 0)
{
lean_ctor_set(v___x_215_, 1, v___y_218_);
v___x_220_ = v___x_215_;
goto v_reusejp_219_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_count_212_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v___y_218_);
v___x_220_ = v_reuseFailAlloc_225_;
goto v_reusejp_219_;
}
v_reusejp_219_:
{
lean_object* v___x_221_; lean_object* v___x_223_; 
v___x_221_ = lean_st_ref_put(v_a_187_, v___x_220_);
if (v_isShared_210_ == 0)
{
v___x_223_ = v___x_209_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_207_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
v_reusejp_227_:
{
lean_object* v___y_230_; lean_object* v_i_231_; lean_object* v___y_237_; lean_object* v___y_247_; lean_object* v_i_248_; lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_213_, v_expr_202_);
switch(lean_obj_tag(v___x_263_))
{
case 0:
{
lean_object* v_index_264_; lean_object* v_size_265_; lean_object* v___x_266_; 
v_index_264_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_index_264_);
lean_dec_ref_known(v___x_263_, 3);
v_size_265_ = lean_ctor_get(v_results_213_, 0);
lean_inc(v_size_265_);
v___x_266_ = l_Std_DHashMap_Raw_setEntry___redArg(v_results_213_, v_size_265_, v_index_264_, v_expr_202_, v___x_228_);
lean_dec(v_index_264_);
v___y_218_ = v___x_266_;
goto v___jp_217_;
}
case 1:
{
lean_object* v_index_267_; lean_object* v_size_268_; lean_object* v_keyArray_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; uint8_t v___x_273_; 
v_index_267_ = lean_ctor_get(v___x_263_, 0);
lean_inc(v_index_267_);
lean_dec_ref_known(v___x_263_, 1);
v_size_268_ = lean_ctor_get(v_results_213_, 0);
v_keyArray_269_ = lean_ctor_get(v_results_213_, 1);
v___x_270_ = lean_unsigned_to_nat(1u);
v___x_271_ = lean_nat_add(v_size_268_, v___x_270_);
v___x_272_ = lean_array_get_size(v_keyArray_269_);
v___x_273_ = lean_nat_dec_lt(v___x_271_, v___x_272_);
if (v___x_273_ == 0)
{
lean_dec(v___x_271_);
lean_dec(v_index_267_);
goto v___jp_253_;
}
else
{
lean_object* v___x_274_; lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; uint8_t v___x_278_; 
v___x_274_ = lean_unsigned_to_nat(4u);
v___x_275_ = lean_nat_mul(v___x_271_, v___x_274_);
v___x_276_ = lean_unsigned_to_nat(3u);
v___x_277_ = lean_nat_mul(v___x_272_, v___x_276_);
v___x_278_ = lean_nat_dec_le(v___x_275_, v___x_277_);
lean_dec(v___x_277_);
lean_dec(v___x_275_);
if (v___x_278_ == 0)
{
lean_dec(v___x_271_);
lean_dec(v_index_267_);
goto v___jp_253_;
}
else
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Raw_setEntry___redArg(v_results_213_, v___x_271_, v_index_267_, v_expr_202_, v___x_228_);
lean_dec(v_index_267_);
v___y_218_ = v___x_279_;
goto v___jp_217_;
}
}
}
default: 
{
lean_object* v_size_280_; lean_object* v_keyArray_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; 
v_size_280_ = lean_ctor_get(v_results_213_, 0);
v_keyArray_281_ = lean_ctor_get(v_results_213_, 1);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_add(v_size_280_, v___x_282_);
v___x_284_ = lean_array_get_size(v_keyArray_281_);
v___x_285_ = lean_nat_dec_lt(v___x_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec(v___x_283_);
v___x_286_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_213_);
lean_dec_ref(v_results_213_);
v___y_237_ = v___x_286_;
goto v___jp_236_;
}
else
{
lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_287_ = lean_unsigned_to_nat(4u);
v___x_288_ = lean_nat_mul(v___x_283_, v___x_287_);
lean_dec(v___x_283_);
v___x_289_ = lean_unsigned_to_nat(3u);
v___x_290_ = lean_nat_mul(v___x_284_, v___x_289_);
v___x_291_ = lean_nat_dec_le(v___x_288_, v___x_290_);
lean_dec(v___x_290_);
lean_dec(v___x_288_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; 
v___x_292_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_213_);
lean_dec_ref(v_results_213_);
v___y_237_ = v___x_292_;
goto v___jp_236_;
}
else
{
v___y_237_ = v_results_213_;
goto v___jp_236_;
}
}
}
}
v___jp_229_:
{
lean_object* v_size_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_size_232_ = lean_ctor_get(v___y_230_, 0);
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_size_232_, v___x_233_);
v___x_235_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_230_, v___x_234_, v_i_231_, v_expr_202_, v___x_228_);
lean_dec(v_i_231_);
v___y_218_ = v___x_235_;
goto v___jp_217_;
}
v___jp_236_:
{
lean_object* v___x_238_; 
v___x_238_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v___y_237_, v_expr_202_);
switch(lean_obj_tag(v___x_238_))
{
case 0:
{
lean_object* v_index_239_; lean_object* v_size_240_; lean_object* v___x_241_; 
v_index_239_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_index_239_);
lean_dec_ref_known(v___x_238_, 3);
v_size_240_ = lean_ctor_get(v___y_237_, 0);
lean_inc(v_size_240_);
v___x_241_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_237_, v_size_240_, v_index_239_, v_expr_202_, v___x_228_);
lean_dec(v_index_239_);
v___y_218_ = v___x_241_;
goto v___jp_217_;
}
case 1:
{
lean_object* v_index_242_; 
v_index_242_ = lean_ctor_get(v___x_238_, 0);
lean_inc(v_index_242_);
lean_dec_ref_known(v___x_238_, 1);
v___y_230_ = v___y_237_;
v_i_231_ = v_index_242_;
goto v___jp_229_;
}
default: 
{
lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_237_, v___x_243_);
if (lean_obj_tag(v___x_244_) == 0)
{
lean_object* v_index_245_; 
v_index_245_ = lean_ctor_get(v___x_244_, 0);
lean_inc(v_index_245_);
lean_dec_ref_known(v___x_244_, 1);
v___y_230_ = v___y_237_;
v_i_231_ = v_index_245_;
goto v___jp_229_;
}
else
{
lean_dec_ref(v___x_228_);
lean_dec_ref(v_expr_202_);
v___y_218_ = v___y_237_;
goto v___jp_217_;
}
}
}
}
v___jp_246_:
{
lean_object* v_size_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v_size_249_ = lean_ctor_get(v___y_247_, 0);
v___x_250_ = lean_unsigned_to_nat(1u);
v___x_251_ = lean_nat_add(v_size_249_, v___x_250_);
v___x_252_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_247_, v___x_251_, v_i_248_, v_expr_202_, v___x_228_);
lean_dec(v_i_248_);
v___y_218_ = v___x_252_;
goto v___jp_217_;
}
v___jp_253_:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_213_);
lean_dec_ref(v_results_213_);
v___x_255_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v___x_254_, v_expr_202_);
switch(lean_obj_tag(v___x_255_))
{
case 0:
{
lean_object* v_index_256_; lean_object* v_size_257_; lean_object* v___x_258_; 
v_index_256_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_256_);
lean_dec_ref_known(v___x_255_, 3);
v_size_257_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_size_257_);
v___x_258_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_254_, v_size_257_, v_index_256_, v_expr_202_, v___x_228_);
lean_dec(v_index_256_);
v___y_218_ = v___x_258_;
goto v___jp_217_;
}
case 1:
{
lean_object* v_index_259_; 
v_index_259_ = lean_ctor_get(v___x_255_, 0);
lean_inc(v_index_259_);
lean_dec_ref_known(v___x_255_, 1);
v___y_247_ = v___x_254_;
v_i_248_ = v_index_259_;
goto v___jp_246_;
}
default: 
{
lean_object* v___x_260_; lean_object* v___x_261_; 
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_254_, v___x_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v_index_262_; 
v_index_262_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_index_262_);
lean_dec_ref_known(v___x_261_, 1);
v___y_247_ = v___x_254_;
v_i_248_ = v_index_262_;
goto v___jp_246_;
}
else
{
lean_dec_ref(v___x_228_);
lean_dec_ref(v_expr_202_);
v___y_218_ = v___x_254_;
goto v___jp_217_;
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
lean_del_object(v___x_204_);
lean_dec_ref(v_expr_202_);
return v___x_206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg___boxed(lean_object* v_r_298_, lean_object* v_a_299_, lean_object* v_a_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_298_, v_a_299_, v_a_300_, v_a_301_, v_a_302_, v_a_303_);
lean_dec(v_a_303_);
lean_dec_ref(v_a_302_);
lean_dec(v_a_301_);
lean_dec_ref(v_a_300_);
lean_dec(v_a_299_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(lean_object* v_r_306_, lean_object* v_a_307_, lean_object* v_a_308_, lean_object* v_a_309_, lean_object* v_a_310_, lean_object* v_a_311_, lean_object* v_a_312_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_306_, v_a_308_, v_a_309_, v_a_310_, v_a_311_, v_a_312_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___boxed(lean_object* v_r_315_, lean_object* v_a_316_, lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(v_r_315_, v_a_316_, v_a_317_, v_a_318_, v_a_319_, v_a_320_, v_a_321_);
lean_dec(v_a_321_);
lean_dec_ref(v_a_320_);
lean_dec(v_a_319_);
lean_dec_ref(v_a_318_);
lean_dec(v_a_317_);
lean_dec(v_a_316_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(lean_object* v_00_u03b2_324_, lean_object* v_m_325_, lean_object* v_query_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_m_325_, v_query_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___boxed(lean_object* v_00_u03b2_328_, lean_object* v_m_329_, lean_object* v_query_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(v_00_u03b2_328_, v_m_329_, v_query_330_);
lean_dec_ref(v_query_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1(lean_object* v_00_u03b2_332_, lean_object* v_m_333_){
_start:
{
lean_object* v___x_334_; 
v___x_334_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_m_333_);
return v___x_334_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___boxed(lean_object* v_00_u03b2_335_, lean_object* v_m_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1(v_00_u03b2_335_, v_m_336_);
lean_dec_ref(v_m_336_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_object* v_00_u03b2_338_, lean_object* v_m_339_, lean_object* v_query_340_, lean_object* v_x_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v___x_345_; 
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_m_339_, v_query_340_, v_x_341_, v_x_342_, v_x_343_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___boxed(lean_object* v_00_u03b2_346_, lean_object* v_m_347_, lean_object* v_query_348_, lean_object* v_x_349_, lean_object* v_x_350_, lean_object* v_x_351_, lean_object* v_x_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(v_00_u03b2_346_, v_m_347_, v_query_348_, v_x_349_, v_x_350_, v_x_351_, v_x_352_);
lean_dec_ref(v_query_348_);
lean_dec_ref(v_m_347_);
return v_res_353_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2(lean_object* v_00_u03b2_354_, lean_object* v_init_355_, lean_object* v_b_356_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___redArg(v_init_355_, v_b_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2___boxed(lean_object* v_00_u03b2_358_, lean_object* v_init_359_, lean_object* v_b_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2(v_00_u03b2_358_, v_init_359_, v_b_360_);
lean_dec_ref(v_b_360_);
return v_res_361_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_362_, lean_object* v_b_363_, lean_object* v_acc_364_, lean_object* v_i_365_){
_start:
{
lean_object* v___x_366_; 
v___x_366_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___redArg(v_b_363_, v_acc_364_, v_i_365_);
return v___x_366_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_367_, lean_object* v_b_368_, lean_object* v_acc_369_, lean_object* v_i_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1_spec__2_spec__3(v_00_u03b2_367_, v_b_368_, v_acc_369_, v_i_370_);
lean_dec_ref(v_b_368_);
return v_res_371_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(lean_object* v_ctx_372_){
_start:
{
uint8_t v___x_373_; 
v___x_373_ = l_List_isEmpty___redArg(v_ctx_372_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; 
v___x_374_ = 1;
return v___x_374_;
}
else
{
uint8_t v___x_375_; 
v___x_375_ = 0;
return v___x_375_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check___boxed(lean_object* v_ctx_376_){
_start:
{
uint8_t v_res_377_; lean_object* v_r_378_; 
v_res_377_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_ctx_376_);
lean_dec(v_ctx_376_);
v_r_378_ = lean_box(v_res_377_);
return v_r_378_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(lean_object* v_e_379_, lean_object* v_m_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_, lean_object* v_a_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
uint8_t v___x_388_; 
v___x_388_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_381_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; 
lean_dec_ref(v_m_380_);
v___x_389_ = lean_box(0);
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_e_379_);
lean_ctor_set(v___x_390_, 1, v___x_389_);
v___x_391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_391_, 0, v___x_390_);
return v___x_391_;
}
else
{
lean_object* v___x_392_; 
lean_dec_ref(v_e_379_);
lean_inc(v_a_386_);
lean_inc_ref(v_a_385_);
lean_inc(v_a_384_);
lean_inc_ref(v_a_383_);
lean_inc(v_a_382_);
lean_inc(v_a_381_);
v___x_392_ = lean_apply_7(v_m_380_, v_a_381_, v_a_382_, v_a_383_, v_a_384_, v_a_385_, v_a_386_, lean_box(0));
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck___boxed(lean_object* v_e_393_, lean_object* v_m_394_, lean_object* v_a_395_, lean_object* v_a_396_, lean_object* v_a_397_, lean_object* v_a_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_393_, v_m_394_, v_a_395_, v_a_396_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
lean_dec(v_a_398_);
lean_dec_ref(v_a_397_);
lean_dec(v_a_396_);
lean_dec(v_a_395_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(lean_object* v_fvars_403_, lean_object* v_m_404_, lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_411_; 
lean_inc(v_a_409_);
lean_inc_ref(v_a_408_);
lean_inc(v_a_407_);
lean_inc_ref(v_a_406_);
lean_inc(v_a_405_);
v___x_411_ = lean_apply_7(v_m_404_, v_fvars_403_, v_a_405_, v_a_406_, v_a_407_, v_a_408_, v_a_409_, lean_box(0));
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg___boxed(lean_object* v_fvars_412_, lean_object* v_m_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(v_fvars_412_, v_m_413_, v_a_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
lean_dec(v_a_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(lean_object* v_00_u03b1_421_, lean_object* v_fvars_422_, lean_object* v_m_423_, lean_object* v_a_424_, lean_object* v_a_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v___x_431_; 
lean_inc(v_a_429_);
lean_inc_ref(v_a_428_);
lean_inc(v_a_427_);
lean_inc_ref(v_a_426_);
lean_inc(v_a_425_);
v___x_431_ = lean_apply_7(v_m_423_, v_fvars_422_, v_a_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_, lean_box(0));
return v___x_431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed(lean_object* v_00_u03b1_432_, lean_object* v_fvars_433_, lean_object* v_m_434_, lean_object* v_a_435_, lean_object* v_a_436_, lean_object* v_a_437_, lean_object* v_a_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(v_00_u03b1_432_, v_fvars_433_, v_m_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
lean_dec(v_a_440_);
lean_dec_ref(v_a_439_);
lean_dec(v_a_438_);
lean_dec_ref(v_a_437_);
lean_dec(v_a_436_);
lean_dec(v_a_435_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(lean_object* v_a_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_count_446_; lean_object* v_results_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_459_; 
v___x_445_ = lean_st_ref_take(v_a_443_);
v_count_446_ = lean_ctor_get(v___x_445_, 0);
v_results_447_ = lean_ctor_get(v___x_445_, 1);
v_isSharedCheck_459_ = !lean_is_exclusive(v___x_445_);
if (v_isSharedCheck_459_ == 0)
{
v___x_449_ = v___x_445_;
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_results_447_);
lean_inc(v_count_446_);
lean_dec(v___x_445_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_459_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_454_; 
v___x_451_ = lean_unsigned_to_nat(1u);
v___x_452_ = lean_nat_add(v_count_446_, v___x_451_);
lean_dec(v_count_446_);
if (v_isShared_450_ == 0)
{
lean_ctor_set(v___x_449_, 0, v___x_452_);
v___x_454_ = v___x_449_;
goto v_reusejp_453_;
}
else
{
lean_object* v_reuseFailAlloc_458_; 
v_reuseFailAlloc_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_458_, 0, v___x_452_);
lean_ctor_set(v_reuseFailAlloc_458_, 1, v_results_447_);
v___x_454_ = v_reuseFailAlloc_458_;
goto v_reusejp_453_;
}
v_reusejp_453_:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_455_ = lean_st_ref_put(v_a_443_, v___x_454_);
v___x_456_ = lean_box(0);
v___x_457_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
return v___x_457_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg___boxed(lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_460_);
lean_dec(v_a_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(lean_object* v_a_463_, lean_object* v_a_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_464_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___boxed(lean_object* v_a_471_, lean_object* v_a_472_, lean_object* v_a_473_, lean_object* v_a_474_, lean_object* v_a_475_, lean_object* v_a_476_, lean_object* v_a_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(v_a_471_, v_a_472_, v_a_473_, v_a_474_, v_a_475_, v_a_476_);
lean_dec(v_a_476_);
lean_dec_ref(v_a_475_);
lean_dec(v_a_474_);
lean_dec_ref(v_a_473_);
lean_dec(v_a_472_);
lean_dec(v_a_471_);
return v_res_478_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(lean_object* v_m_479_, lean_object* v_query_480_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_m_479_, v_query_480_);
if (lean_obj_tag(v___x_481_) == 0)
{
lean_object* v_index_482_; lean_object* v_key_483_; lean_object* v_value_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_491_; 
v_index_482_ = lean_ctor_get(v___x_481_, 0);
v_key_483_ = lean_ctor_get(v___x_481_, 1);
v_value_484_ = lean_ctor_get(v___x_481_, 2);
v_isSharedCheck_491_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_491_ == 0)
{
v___x_486_ = v___x_481_;
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_value_484_);
lean_inc(v_key_483_);
lean_inc(v_index_482_);
lean_dec(v___x_481_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_491_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_489_; 
if (v_isShared_487_ == 0)
{
v___x_489_ = v___x_486_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_index_482_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_key_483_);
lean_ctor_set(v_reuseFailAlloc_490_, 2, v_value_484_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
}
else
{
lean_object* v___x_492_; 
lean_dec(v___x_481_);
v___x_492_ = lean_box(1);
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_m_493_, lean_object* v_query_494_){
_start:
{
lean_object* v_res_495_; 
v_res_495_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_m_493_, v_query_494_);
lean_dec_ref(v_query_494_);
lean_dec_ref(v_m_493_);
return v_res_495_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(lean_object* v_m_496_, lean_object* v_a_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_m_496_, v_a_497_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_value_499_; lean_object* v___x_500_; 
v_value_499_ = lean_ctor_get(v___x_498_, 2);
lean_inc(v_value_499_);
lean_dec_ref_known(v___x_498_, 3);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v_value_499_);
return v___x_500_;
}
else
{
lean_object* v___x_501_; 
v___x_501_ = lean_box(0);
return v___x_501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg___boxed(lean_object* v_m_502_, lean_object* v_a_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_502_, v_a_503_);
lean_dec_ref(v_a_503_);
lean_dec_ref(v_m_502_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(lean_object* v_e_505_, lean_object* v_a_506_){
_start:
{
lean_object* v___x_508_; lean_object* v_results_509_; lean_object* v___x_510_; lean_object* v___x_511_; 
v___x_508_ = lean_st_ref_get(v_a_506_);
v_results_509_ = lean_ctor_get(v___x_508_, 1);
lean_inc_ref(v_results_509_);
lean_dec(v___x_508_);
v___x_510_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_results_509_, v_e_505_);
lean_dec_ref(v_results_509_);
v___x_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg___boxed(lean_object* v_e_512_, lean_object* v_a_513_, lean_object* v_a_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_512_, v_a_513_);
lean_dec(v_a_513_);
lean_dec_ref(v_e_512_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(lean_object* v_e_516_, lean_object* v_a_517_, lean_object* v_a_518_, lean_object* v_a_519_, lean_object* v_a_520_, lean_object* v_a_521_, lean_object* v_a_522_){
_start:
{
lean_object* v___x_524_; 
v___x_524_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_516_, v_a_518_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___boxed(lean_object* v_e_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_, lean_object* v_a_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(v_e_525_, v_a_526_, v_a_527_, v_a_528_, v_a_529_, v_a_530_, v_a_531_);
lean_dec(v_a_531_);
lean_dec_ref(v_a_530_);
lean_dec(v_a_529_);
lean_dec_ref(v_a_528_);
lean_dec(v_a_527_);
lean_dec(v_a_526_);
lean_dec_ref(v_e_525_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_a_536_){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_535_, v_a_536_);
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___boxed(lean_object* v_00_u03b2_538_, lean_object* v_m_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(v_00_u03b2_538_, v_m_539_, v_a_540_);
lean_dec_ref(v_a_540_);
lean_dec_ref(v_m_539_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(lean_object* v_00_u03b2_542_, lean_object* v_m_543_, lean_object* v_query_544_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_m_543_, v_query_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_546_, lean_object* v_m_547_, lean_object* v_query_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(v_00_u03b2_546_, v_m_547_, v_query_548_);
lean_dec_ref(v_query_548_);
lean_dec_ref(v_m_547_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(lean_object* v_e_550_, lean_object* v_m_551_, lean_object* v_a_552_, lean_object* v_a_553_, lean_object* v_a_554_, lean_object* v_a_555_, lean_object* v_a_556_, lean_object* v_a_557_){
_start:
{
lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; lean_object* v___y_563_; lean_object* v___y_568_; lean_object* v___y_569_; lean_object* v___y_570_; lean_object* v___y_571_; lean_object* v_i_572_; lean_object* v___y_578_; lean_object* v___y_579_; lean_object* v___y_580_; lean_object* v___y_581_; lean_object* v___y_591_; lean_object* v___y_592_; lean_object* v___y_593_; lean_object* v___y_594_; lean_object* v_i_595_; lean_object* v___y_601_; lean_object* v___y_602_; lean_object* v___y_603_; lean_object* v___y_604_; lean_object* v_r_615_; lean_object* v___y_616_; lean_object* v___x_650_; lean_object* v_a_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_665_; 
v___x_650_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_550_, v_a_553_);
v_a_651_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_665_ == 0)
{
v___x_653_ = v___x_650_;
v_isShared_654_ = v_isSharedCheck_665_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_a_651_);
lean_dec(v___x_650_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_665_;
goto v_resetjp_652_;
}
v___jp_559_:
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v___y_560_);
lean_ctor_set(v___x_564_, 1, v___y_563_);
v___x_565_ = lean_st_ref_put(v___y_561_, v___x_564_);
v___x_566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_566_, 0, v___y_562_);
return v___x_566_;
}
v___jp_567_:
{
lean_object* v_size_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v_size_573_ = lean_ctor_get(v___y_571_, 0);
v___x_574_ = lean_unsigned_to_nat(1u);
v___x_575_ = lean_nat_add(v_size_573_, v___x_574_);
lean_inc_ref(v___y_570_);
v___x_576_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_571_, v___x_575_, v_i_572_, v_e_550_, v___y_570_);
lean_dec(v_i_572_);
v___y_560_ = v___y_568_;
v___y_561_ = v___y_569_;
v___y_562_ = v___y_570_;
v___y_563_ = v___x_576_;
goto v___jp_559_;
}
v___jp_577_:
{
lean_object* v___x_582_; 
v___x_582_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v___y_581_, v_e_550_);
switch(lean_obj_tag(v___x_582_))
{
case 0:
{
lean_object* v_index_583_; lean_object* v_size_584_; lean_object* v___x_585_; 
v_index_583_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_index_583_);
lean_dec_ref_known(v___x_582_, 3);
v_size_584_ = lean_ctor_get(v___y_581_, 0);
lean_inc(v_size_584_);
lean_inc_ref(v___y_580_);
v___x_585_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_581_, v_size_584_, v_index_583_, v_e_550_, v___y_580_);
lean_dec(v_index_583_);
v___y_560_ = v___y_578_;
v___y_561_ = v___y_579_;
v___y_562_ = v___y_580_;
v___y_563_ = v___x_585_;
goto v___jp_559_;
}
case 1:
{
lean_object* v_index_586_; 
v_index_586_ = lean_ctor_get(v___x_582_, 0);
lean_inc(v_index_586_);
lean_dec_ref_known(v___x_582_, 1);
v___y_568_ = v___y_578_;
v___y_569_ = v___y_579_;
v___y_570_ = v___y_580_;
v___y_571_ = v___y_581_;
v_i_572_ = v_index_586_;
goto v___jp_567_;
}
default: 
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_581_, v___x_587_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_index_589_; 
v_index_589_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_index_589_);
lean_dec_ref_known(v___x_588_, 1);
v___y_568_ = v___y_578_;
v___y_569_ = v___y_579_;
v___y_570_ = v___y_580_;
v___y_571_ = v___y_581_;
v_i_572_ = v_index_589_;
goto v___jp_567_;
}
else
{
lean_dec_ref(v_e_550_);
v___y_560_ = v___y_578_;
v___y_561_ = v___y_579_;
v___y_562_ = v___y_580_;
v___y_563_ = v___y_581_;
goto v___jp_559_;
}
}
}
}
v___jp_590_:
{
lean_object* v_size_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v_size_596_ = lean_ctor_get(v___y_593_, 0);
v___x_597_ = lean_unsigned_to_nat(1u);
v___x_598_ = lean_nat_add(v_size_596_, v___x_597_);
lean_inc_ref(v___y_594_);
v___x_599_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_593_, v___x_598_, v_i_595_, v_e_550_, v___y_594_);
lean_dec(v_i_595_);
v___y_560_ = v___y_591_;
v___y_561_ = v___y_592_;
v___y_562_ = v___y_594_;
v___y_563_ = v___x_599_;
goto v___jp_559_;
}
v___jp_600_:
{
lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_605_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v___y_601_);
lean_dec_ref(v___y_601_);
v___x_606_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v___x_605_, v_e_550_);
switch(lean_obj_tag(v___x_606_))
{
case 0:
{
lean_object* v_index_607_; lean_object* v_size_608_; lean_object* v___x_609_; 
v_index_607_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_index_607_);
lean_dec_ref_known(v___x_606_, 3);
v_size_608_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_size_608_);
lean_inc_ref(v___y_604_);
v___x_609_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_605_, v_size_608_, v_index_607_, v_e_550_, v___y_604_);
lean_dec(v_index_607_);
v___y_560_ = v___y_602_;
v___y_561_ = v___y_603_;
v___y_562_ = v___y_604_;
v___y_563_ = v___x_609_;
goto v___jp_559_;
}
case 1:
{
lean_object* v_index_610_; 
v_index_610_ = lean_ctor_get(v___x_606_, 0);
lean_inc(v_index_610_);
lean_dec_ref_known(v___x_606_, 1);
v___y_591_ = v___y_602_;
v___y_592_ = v___y_603_;
v___y_593_ = v___x_605_;
v___y_594_ = v___y_604_;
v_i_595_ = v_index_610_;
goto v___jp_590_;
}
default: 
{
lean_object* v___x_611_; lean_object* v___x_612_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_605_, v___x_611_);
if (lean_obj_tag(v___x_612_) == 0)
{
lean_object* v_index_613_; 
v_index_613_ = lean_ctor_get(v___x_612_, 0);
lean_inc(v_index_613_);
lean_dec_ref_known(v___x_612_, 1);
v___y_591_ = v___y_602_;
v___y_592_ = v___y_603_;
v___y_593_ = v___x_605_;
v___y_594_ = v___y_604_;
v_i_595_ = v_index_613_;
goto v___jp_590_;
}
else
{
lean_dec_ref(v_e_550_);
v___y_560_ = v___y_602_;
v___y_561_ = v___y_603_;
v___y_562_ = v___y_604_;
v___y_563_ = v___x_605_;
goto v___jp_559_;
}
}
}
}
v___jp_614_:
{
lean_object* v___x_617_; lean_object* v_count_618_; lean_object* v_results_619_; lean_object* v___x_620_; 
v___x_617_ = lean_st_ref_take(v___y_616_);
v_count_618_ = lean_ctor_get(v___x_617_, 0);
lean_inc(v_count_618_);
v_results_619_ = lean_ctor_get(v___x_617_, 1);
lean_inc_ref(v_results_619_);
lean_dec(v___x_617_);
v___x_620_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_619_, v_e_550_);
switch(lean_obj_tag(v___x_620_))
{
case 0:
{
lean_object* v_index_621_; lean_object* v_size_622_; lean_object* v___x_623_; 
v_index_621_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_index_621_);
lean_dec_ref_known(v___x_620_, 3);
v_size_622_ = lean_ctor_get(v_results_619_, 0);
lean_inc(v_size_622_);
lean_inc_ref(v_r_615_);
v___x_623_ = l_Std_DHashMap_Raw_setEntry___redArg(v_results_619_, v_size_622_, v_index_621_, v_e_550_, v_r_615_);
lean_dec(v_index_621_);
v___y_560_ = v_count_618_;
v___y_561_ = v___y_616_;
v___y_562_ = v_r_615_;
v___y_563_ = v___x_623_;
goto v___jp_559_;
}
case 1:
{
lean_object* v_index_624_; lean_object* v_size_625_; lean_object* v_keyArray_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_index_624_ = lean_ctor_get(v___x_620_, 0);
lean_inc(v_index_624_);
lean_dec_ref_known(v___x_620_, 1);
v_size_625_ = lean_ctor_get(v_results_619_, 0);
v_keyArray_626_ = lean_ctor_get(v_results_619_, 1);
v___x_627_ = lean_unsigned_to_nat(1u);
v___x_628_ = lean_nat_add(v_size_625_, v___x_627_);
v___x_629_ = lean_array_get_size(v_keyArray_626_);
v___x_630_ = lean_nat_dec_lt(v___x_628_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec(v___x_628_);
lean_dec(v_index_624_);
v___y_601_ = v_results_619_;
v___y_602_ = v_count_618_;
v___y_603_ = v___y_616_;
v___y_604_ = v_r_615_;
goto v___jp_600_;
}
else
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; uint8_t v___x_635_; 
v___x_631_ = lean_unsigned_to_nat(4u);
v___x_632_ = lean_nat_mul(v___x_628_, v___x_631_);
v___x_633_ = lean_unsigned_to_nat(3u);
v___x_634_ = lean_nat_mul(v___x_629_, v___x_633_);
v___x_635_ = lean_nat_dec_le(v___x_632_, v___x_634_);
lean_dec(v___x_634_);
lean_dec(v___x_632_);
if (v___x_635_ == 0)
{
lean_dec(v___x_628_);
lean_dec(v_index_624_);
v___y_601_ = v_results_619_;
v___y_602_ = v_count_618_;
v___y_603_ = v___y_616_;
v___y_604_ = v_r_615_;
goto v___jp_600_;
}
else
{
lean_object* v___x_636_; 
lean_inc_ref(v_r_615_);
v___x_636_ = l_Std_DHashMap_Raw_setEntry___redArg(v_results_619_, v___x_628_, v_index_624_, v_e_550_, v_r_615_);
lean_dec(v_index_624_);
v___y_560_ = v_count_618_;
v___y_561_ = v___y_616_;
v___y_562_ = v_r_615_;
v___y_563_ = v___x_636_;
goto v___jp_559_;
}
}
}
default: 
{
lean_object* v_size_637_; lean_object* v_keyArray_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_size_637_ = lean_ctor_get(v_results_619_, 0);
v_keyArray_638_ = lean_ctor_get(v_results_619_, 1);
v___x_639_ = lean_unsigned_to_nat(1u);
v___x_640_ = lean_nat_add(v_size_637_, v___x_639_);
v___x_641_ = lean_array_get_size(v_keyArray_638_);
v___x_642_ = lean_nat_dec_lt(v___x_640_, v___x_641_);
if (v___x_642_ == 0)
{
lean_object* v___x_643_; 
lean_dec(v___x_640_);
v___x_643_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_619_);
lean_dec_ref(v_results_619_);
v___y_578_ = v_count_618_;
v___y_579_ = v___y_616_;
v___y_580_ = v_r_615_;
v___y_581_ = v___x_643_;
goto v___jp_577_;
}
else
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; uint8_t v___x_648_; 
v___x_644_ = lean_unsigned_to_nat(4u);
v___x_645_ = lean_nat_mul(v___x_640_, v___x_644_);
lean_dec(v___x_640_);
v___x_646_ = lean_unsigned_to_nat(3u);
v___x_647_ = lean_nat_mul(v___x_641_, v___x_646_);
v___x_648_ = lean_nat_dec_le(v___x_645_, v___x_647_);
lean_dec(v___x_647_);
lean_dec(v___x_645_);
if (v___x_648_ == 0)
{
lean_object* v___x_649_; 
v___x_649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_619_);
lean_dec_ref(v_results_619_);
v___y_578_ = v_count_618_;
v___y_579_ = v___y_616_;
v___y_580_ = v_r_615_;
v___y_581_ = v___x_649_;
goto v___jp_577_;
}
else
{
v___y_578_ = v_count_618_;
v___y_579_ = v___y_616_;
v___y_580_ = v_r_615_;
v___y_581_ = v_results_619_;
goto v___jp_577_;
}
}
}
}
}
v_resetjp_652_:
{
if (lean_obj_tag(v_a_651_) == 1)
{
lean_object* v_val_655_; lean_object* v___x_657_; 
lean_dec_ref(v_m_551_);
lean_dec_ref(v_e_550_);
v_val_655_ = lean_ctor_get(v_a_651_, 0);
lean_inc(v_val_655_);
lean_dec_ref_known(v_a_651_, 1);
if (v_isShared_654_ == 0)
{
lean_ctor_set(v___x_653_, 0, v_val_655_);
v___x_657_ = v___x_653_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v_val_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
else
{
uint32_t v___x_659_; uint8_t v___x_660_; 
lean_del_object(v___x_653_);
lean_dec(v_a_651_);
v___x_659_ = 2;
v___x_660_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_550_, v___x_659_);
if (v___x_660_ == 0)
{
lean_object* v___x_661_; 
lean_inc(v_a_557_);
lean_inc_ref(v_a_556_);
lean_inc(v_a_555_);
lean_inc_ref(v_a_554_);
lean_inc(v_a_553_);
lean_inc(v_a_552_);
v___x_661_ = lean_apply_7(v_m_551_, v_a_552_, v_a_553_, v_a_554_, v_a_555_, v_a_556_, v_a_557_, lean_box(0));
if (lean_obj_tag(v___x_661_) == 0)
{
lean_object* v_a_662_; 
v_a_662_ = lean_ctor_get(v___x_661_, 0);
lean_inc(v_a_662_);
lean_dec_ref_known(v___x_661_, 1);
v_r_615_ = v_a_662_;
v___y_616_ = v_a_553_;
goto v___jp_614_;
}
else
{
lean_dec_ref(v_e_550_);
return v___x_661_;
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref(v_m_551_);
v___x_663_ = lean_box(0);
lean_inc_ref(v_e_550_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_e_550_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
v_r_615_ = v___x_664_;
v___y_616_ = v_a_553_;
goto v___jp_614_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache___boxed(lean_object* v_e_666_, lean_object* v_m_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_, lean_object* v_a_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_666_, v_m_667_, v_a_668_, v_a_669_, v_a_670_, v_a_671_, v_a_672_, v_a_673_);
lean_dec(v_a_673_);
lean_dec_ref(v_a_672_);
lean_dec(v_a_671_);
lean_dec_ref(v_a_670_);
lean_dec(v_a_669_);
lean_dec(v_a_668_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(lean_object* v_e_676_, lean_object* v_a_677_){
_start:
{
uint8_t v___x_679_; 
v___x_679_ = l_Lean_Expr_hasLooseBVars(v_e_676_);
if (v___x_679_ == 0)
{
lean_object* v___x_680_; 
v___x_680_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_676_, v_a_677_);
return v___x_680_;
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; 
v___x_681_ = lean_box(0);
v___x_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_682_, 0, v___x_681_);
return v___x_682_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg___boxed(lean_object* v_e_683_, lean_object* v_a_684_, lean_object* v_a_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_683_, v_a_684_);
lean_dec(v_a_684_);
lean_dec_ref(v_e_683_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(lean_object* v_e_687_, lean_object* v_a_688_, lean_object* v_a_689_, lean_object* v_a_690_, lean_object* v_a_691_, lean_object* v_a_692_, lean_object* v_a_693_){
_start:
{
lean_object* v___x_695_; 
v___x_695_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_687_, v_a_689_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___boxed(lean_object* v_e_696_, lean_object* v_a_697_, lean_object* v_a_698_, lean_object* v_a_699_, lean_object* v_a_700_, lean_object* v_a_701_, lean_object* v_a_702_, lean_object* v_a_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(v_e_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_);
lean_dec(v_a_702_);
lean_dec_ref(v_a_701_);
lean_dec(v_a_700_);
lean_dec_ref(v_a_699_);
lean_dec(v_a_698_);
lean_dec(v_a_697_);
lean_dec_ref(v_e_696_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(lean_object* v_e_705_, lean_object* v_a_706_, lean_object* v_a_707_, lean_object* v_a_708_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Lean_Expr_fvarId_x21(v_e_705_);
lean_inc(v___x_710_);
v___x_711_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_710_, v_a_706_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_730_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_730_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_730_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
if (lean_obj_tag(v_a_712_) == 1)
{
lean_object* v_val_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_728_; 
lean_dec(v___x_710_);
v_val_716_ = lean_ctor_get(v_a_712_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_728_ == 0)
{
v___x_718_ = v_a_712_;
v_isShared_719_ = v_isSharedCheck_728_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_val_716_);
lean_dec(v_a_712_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_728_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v___x_720_; lean_object* v___x_722_; 
v___x_720_ = l_Lean_LocalDecl_type(v_val_716_);
lean_dec(v_val_716_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_720_);
v___x_722_ = v___x_718_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_727_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_723_, 0, v_e_705_);
lean_ctor_set(v___x_723_, 1, v___x_722_);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_723_);
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v___x_723_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v___x_729_; 
lean_del_object(v___x_714_);
lean_dec(v_a_712_);
lean_dec_ref(v_e_705_);
v___x_729_ = l_Lean_FVarId_throwUnknown___redArg(v___x_710_, v_a_707_, v_a_708_);
return v___x_729_;
}
}
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v___x_710_);
lean_dec_ref(v_e_705_);
v_a_731_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_711_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_711_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg___boxed(lean_object* v_e_739_, lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_){
_start:
{
lean_object* v_res_744_; 
v_res_744_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_739_, v_a_740_, v_a_741_, v_a_742_);
lean_dec(v_a_742_);
lean_dec_ref(v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(lean_object* v_e_745_, lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_745_, v_a_746_, v_a_748_, v_a_749_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___boxed(lean_object* v_e_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(v_e_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_);
lean_dec(v_a_756_);
lean_dec_ref(v_a_755_);
lean_dec(v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(lean_object* v_e_759_, lean_object* v___y_760_){
_start:
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_Expr_hasMVar(v_e_759_);
if (v___x_762_ == 0)
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_763_, 0, v_e_759_);
return v___x_763_;
}
else
{
lean_object* v___x_764_; lean_object* v_mctx_765_; lean_object* v___x_766_; lean_object* v_fst_767_; lean_object* v_snd_768_; lean_object* v___x_769_; lean_object* v_cache_770_; lean_object* v_zetaDeltaFVarIds_771_; lean_object* v_postponed_772_; lean_object* v_diag_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_782_; 
v___x_764_ = lean_st_ref_get(v___y_760_);
v_mctx_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc_ref(v_mctx_765_);
lean_dec(v___x_764_);
v___x_766_ = l_Lean_instantiateMVarsCore(v_mctx_765_, v_e_759_);
v_fst_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_fst_767_);
v_snd_768_ = lean_ctor_get(v___x_766_, 1);
lean_inc(v_snd_768_);
lean_dec_ref(v___x_766_);
v___x_769_ = lean_st_ref_take(v___y_760_);
v_cache_770_ = lean_ctor_get(v___x_769_, 1);
v_zetaDeltaFVarIds_771_ = lean_ctor_get(v___x_769_, 2);
v_postponed_772_ = lean_ctor_get(v___x_769_, 3);
v_diag_773_ = lean_ctor_get(v___x_769_, 4);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v___x_769_, 0);
lean_dec(v_unused_783_);
v___x_775_ = v___x_769_;
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_diag_773_);
lean_inc(v_postponed_772_);
lean_inc(v_zetaDeltaFVarIds_771_);
lean_inc(v_cache_770_);
lean_dec(v___x_769_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_782_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
lean_ctor_set(v___x_775_, 0, v_snd_768_);
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v_snd_768_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_cache_770_);
lean_ctor_set(v_reuseFailAlloc_781_, 2, v_zetaDeltaFVarIds_771_);
lean_ctor_set(v_reuseFailAlloc_781_, 3, v_postponed_772_);
lean_ctor_set(v_reuseFailAlloc_781_, 4, v_diag_773_);
v___x_778_ = v_reuseFailAlloc_781_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_779_ = lean_st_ref_put(v___y_760_, v___x_778_);
v___x_780_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_780_, 0, v_fst_767_);
return v___x_780_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg___boxed(lean_object* v_e_784_, lean_object* v___y_785_, lean_object* v___y_786_){
_start:
{
lean_object* v_res_787_; 
v_res_787_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_784_, v___y_785_);
lean_dec(v___y_785_);
return v_res_787_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(lean_object* v_e_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_788_, v___y_792_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___boxed(lean_object* v_e_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(v_e_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec(v___y_798_);
return v_res_805_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(lean_object* v_k_806_, lean_object* v_t_807_){
_start:
{
if (lean_obj_tag(v_t_807_) == 0)
{
lean_object* v_k_808_; lean_object* v_l_809_; lean_object* v_r_810_; uint8_t v___x_811_; 
v_k_808_ = lean_ctor_get(v_t_807_, 1);
v_l_809_ = lean_ctor_get(v_t_807_, 3);
v_r_810_ = lean_ctor_get(v_t_807_, 4);
v___x_811_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_806_, v_k_808_);
switch(v___x_811_)
{
case 0:
{
v_t_807_ = v_l_809_;
goto _start;
}
case 1:
{
uint8_t v___x_813_; 
v___x_813_ = 1;
return v___x_813_;
}
default: 
{
v_t_807_ = v_r_810_;
goto _start;
}
}
}
else
{
uint8_t v___x_815_; 
v___x_815_ = 0;
return v___x_815_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg___boxed(lean_object* v_k_816_, lean_object* v_t_817_){
_start:
{
uint8_t v_res_818_; lean_object* v_r_819_; 
v_res_818_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_816_, v_t_817_);
lean_dec(v_t_817_);
lean_dec(v_k_816_);
v_r_819_ = lean_box(v_res_818_);
return v_r_819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(lean_object* v_as_820_, size_t v_sz_821_, size_t v_i_822_, lean_object* v_b_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_){
_start:
{
lean_object* v_a_830_; uint8_t v___x_834_; 
v___x_834_ = lean_usize_dec_lt(v_i_822_, v_sz_821_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_835_, 0, v_b_823_);
return v___x_835_;
}
else
{
lean_object* v_fst_836_; lean_object* v_snd_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_885_; 
v_fst_836_ = lean_ctor_get(v_b_823_, 0);
v_snd_837_ = lean_ctor_get(v_b_823_, 1);
v_isSharedCheck_885_ = !lean_is_exclusive(v_b_823_);
if (v_isSharedCheck_885_ == 0)
{
v___x_839_ = v_b_823_;
v_isShared_840_ = v_isSharedCheck_885_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_snd_837_);
lean_inc(v_fst_836_);
lean_dec(v_b_823_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_885_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v_a_841_; uint8_t v___x_842_; 
v_a_841_ = lean_array_uget_borrowed(v_as_820_, v_i_822_);
v___x_842_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_a_841_, v_fst_836_);
if (v___x_842_ == 0)
{
lean_object* v___x_843_; lean_object* v___y_845_; lean_object* v___y_846_; lean_object* v___y_847_; lean_object* v___x_862_; 
lean_inc_n(v_a_841_, 2);
v___x_843_ = l_Lean_FVarIdSet_insert(v_fst_836_, v_a_841_);
v___x_862_ = l_Lean_FVarId_isLetVar___redArg(v_a_841_, v___x_842_, v___y_824_, v___y_826_, v___y_827_);
if (lean_obj_tag(v___x_862_) == 0)
{
lean_object* v_a_863_; uint8_t v___x_864_; 
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref_known(v___x_862_, 1);
v___x_864_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
if (v___x_864_ == 0)
{
v___y_845_ = v___y_824_;
v___y_846_ = v___y_826_;
v___y_847_ = v___y_827_;
goto v___jp_844_;
}
else
{
lean_object* v___x_865_; 
lean_inc(v_a_841_);
v___x_865_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_a_841_, v___y_825_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_dec_ref_known(v___x_865_, 1);
v___y_845_ = v___y_824_;
v___y_846_ = v___y_826_;
v___y_847_ = v___y_827_;
goto v___jp_844_;
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec(v___x_843_);
lean_del_object(v___x_839_);
lean_dec(v_snd_837_);
v_a_866_ = lean_ctor_get(v___x_865_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_865_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_865_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_865_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v___x_843_);
lean_del_object(v___x_839_);
lean_dec(v_snd_837_);
v_a_874_ = lean_ctor_get(v___x_862_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_862_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_862_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_862_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
v___jp_844_:
{
lean_object* v___x_848_; 
lean_inc(v_a_841_);
v___x_848_ = l_Lean_FVarId_getType___redArg(v_a_841_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; lean_object* v___x_850_; lean_object* v___x_852_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
v___x_850_ = lean_array_push(v_snd_837_, v_a_849_);
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 1, v___x_850_);
lean_ctor_set(v___x_839_, 0, v___x_843_);
v___x_852_ = v___x_839_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
v_a_830_ = v___x_852_;
goto v___jp_829_;
}
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
lean_dec(v___x_843_);
lean_del_object(v___x_839_);
lean_dec(v_snd_837_);
v_a_854_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_848_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_848_);
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
else
{
lean_object* v___x_883_; 
if (v_isShared_840_ == 0)
{
v___x_883_ = v___x_839_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_fst_836_);
lean_ctor_set(v_reuseFailAlloc_884_, 1, v_snd_837_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
v_a_830_ = v___x_883_;
goto v___jp_829_;
}
}
}
}
v___jp_829_:
{
size_t v___x_831_; size_t v___x_832_; 
v___x_831_ = ((size_t)1ULL);
v___x_832_ = lean_usize_add(v_i_822_, v___x_831_);
v_i_822_ = v___x_832_;
v_b_823_ = v_a_830_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg___boxed(lean_object* v_as_886_, lean_object* v_sz_887_, lean_object* v_i_888_, lean_object* v_b_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
size_t v_sz_boxed_895_; size_t v_i_boxed_896_; lean_object* v_res_897_; 
v_sz_boxed_895_ = lean_unbox_usize(v_sz_887_);
lean_dec(v_sz_887_);
v_i_boxed_896_ = lean_unbox_usize(v_i_888_);
lean_dec(v_i_888_);
v_res_897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_886_, v_sz_boxed_895_, v_i_boxed_896_, v_b_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec_ref(v_as_886_);
return v_res_897_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v_cellCount_898_; lean_object* v___x_899_; 
v_cellCount_898_ = lean_unsigned_to_nat(16u);
v___x_899_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_898_);
return v___x_899_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_900_; lean_object* v___x_901_; 
v_cellCount_900_ = lean_unsigned_to_nat(16u);
v___x_901_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_900_);
return v___x_901_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; 
v___x_902_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_903_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0);
v___x_904_ = lean_unsigned_to_nat(0u);
v___x_905_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_905_, 0, v___x_904_);
lean_ctor_set(v___x_905_, 1, v___x_903_);
lean_ctor_set(v___x_905_, 2, v___x_902_);
return v___x_905_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_908_; lean_object* v_visited_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3));
v_visited_909_ = lean_box(1);
v___x_910_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2);
v___x_911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
lean_ctor_set(v___x_911_, 1, v_visited_909_);
lean_ctor_set(v___x_911_, 2, v___x_908_);
return v___x_911_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object* v_a_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_){
_start:
{
lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_967_; 
v_fst_920_ = lean_ctor_get(v_a_912_, 0);
v_snd_921_ = lean_ctor_get(v_a_912_, 1);
v_isSharedCheck_967_ = !lean_is_exclusive(v_a_912_);
if (v_isSharedCheck_967_ == 0)
{
v___x_923_ = v_a_912_;
v_isShared_924_ = v_isSharedCheck_967_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_snd_921_);
lean_inc(v_fst_920_);
lean_dec(v_a_912_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_967_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v___x_925_ = lean_array_get_size(v_snd_921_);
v___x_926_ = lean_unsigned_to_nat(0u);
v___x_927_ = lean_nat_dec_eq(v___x_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_928_ = l_Lean_instInhabitedExpr;
v___x_929_ = lean_unsigned_to_nat(1u);
v___x_930_ = lean_nat_sub(v___x_925_, v___x_929_);
v___x_931_ = lean_array_get_borrowed(v___x_928_, v_snd_921_, v___x_930_);
lean_dec(v___x_930_);
lean_inc(v___x_931_);
v___x_932_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v___x_931_, v___y_916_);
if (lean_obj_tag(v___x_932_) == 0)
{
lean_object* v_a_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v_fvarIds_936_; lean_object* v___x_937_; lean_object* v___x_939_; 
v_a_933_ = lean_ctor_get(v___x_932_, 0);
lean_inc(v_a_933_);
lean_dec_ref_known(v___x_932_, 1);
v___x_934_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__4);
v___x_935_ = l_Lean_collectFVars(v___x_934_, v_a_933_);
v_fvarIds_936_ = lean_ctor_get(v___x_935_, 2);
lean_inc_ref(v_fvarIds_936_);
lean_dec_ref(v___x_935_);
v___x_937_ = lean_array_pop(v_snd_921_);
if (v_isShared_924_ == 0)
{
lean_ctor_set(v___x_923_, 1, v___x_937_);
v___x_939_ = v___x_923_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_fst_920_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_937_);
v___x_939_ = v_reuseFailAlloc_954_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
size_t v_sz_940_; size_t v___x_941_; lean_object* v___x_942_; 
v_sz_940_ = lean_array_size(v_fvarIds_936_);
v___x_941_ = ((size_t)0ULL);
v___x_942_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_fvarIds_936_, v_sz_940_, v___x_941_, v___x_939_, v___y_915_, v___y_916_, v___y_917_, v___y_918_);
lean_dec_ref(v_fvarIds_936_);
if (lean_obj_tag(v___x_942_) == 0)
{
lean_object* v_a_943_; lean_object* v_fst_944_; lean_object* v_snd_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_953_; 
v_a_943_ = lean_ctor_get(v___x_942_, 0);
lean_inc(v_a_943_);
lean_dec_ref_known(v___x_942_, 1);
v_fst_944_ = lean_ctor_get(v_a_943_, 0);
v_snd_945_ = lean_ctor_get(v_a_943_, 1);
v_isSharedCheck_953_ = !lean_is_exclusive(v_a_943_);
if (v_isSharedCheck_953_ == 0)
{
v___x_947_ = v_a_943_;
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_snd_945_);
lean_inc(v_fst_944_);
lean_dec(v_a_943_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_953_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_fst_944_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v_snd_945_);
v___x_950_ = v_reuseFailAlloc_952_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
v_a_912_ = v___x_950_;
goto _start;
}
}
}
else
{
return v___x_942_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
lean_del_object(v___x_923_);
lean_dec(v_snd_921_);
lean_dec(v_fst_920_);
v_a_955_ = lean_ctor_get(v___x_932_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_932_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_932_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_932_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
else
{
lean_object* v___x_964_; 
if (v_isShared_924_ == 0)
{
v___x_964_ = v___x_923_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_966_; 
v_reuseFailAlloc_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_966_, 0, v_fst_920_);
lean_ctor_set(v_reuseFailAlloc_966_, 1, v_snd_921_);
v___x_964_ = v_reuseFailAlloc_966_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
return v___x_965_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object* v_a_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
lean_object* v_res_976_; 
v_res_976_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
lean_dec(v___y_974_);
lean_dec_ref(v___y_973_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec(v___y_969_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object* v_e_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_){
_start:
{
lean_object* v_visited_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v_worklist_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v_visited_985_ = lean_box(1);
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_mk_empty_array_with_capacity(v___x_986_);
v_worklist_988_ = lean_array_push(v___x_987_, v_e_977_);
v___x_989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_989_, 0, v_visited_985_);
lean_ctor_set(v___x_989_, 1, v_worklist_988_);
v___x_990_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v___x_989_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_);
if (lean_obj_tag(v___x_990_) == 0)
{
lean_object* v___x_992_; uint8_t v_isShared_993_; uint8_t v_isSharedCheck_998_; 
v_isSharedCheck_998_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_998_ == 0)
{
lean_object* v_unused_999_; 
v_unused_999_ = lean_ctor_get(v___x_990_, 0);
lean_dec(v_unused_999_);
v___x_992_ = v___x_990_;
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
else
{
lean_dec(v___x_990_);
v___x_992_ = lean_box(0);
v_isShared_993_ = v_isSharedCheck_998_;
goto v_resetjp_991_;
}
v_resetjp_991_:
{
lean_object* v___x_994_; lean_object* v___x_996_; 
v___x_994_ = lean_box(0);
if (v_isShared_993_ == 0)
{
lean_ctor_set(v___x_992_, 0, v___x_994_);
v___x_996_ = v___x_992_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_994_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
}
else
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1007_; 
v_a_1000_ = lean_ctor_get(v___x_990_, 0);
v_isSharedCheck_1007_ = !lean_is_exclusive(v___x_990_);
if (v_isSharedCheck_1007_ == 0)
{
v___x_1002_ = v___x_990_;
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_990_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1007_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v___x_1005_; 
if (v_isShared_1003_ == 0)
{
v___x_1005_ = v___x_1002_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v_a_1000_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object* v_e_1008_, lean_object* v_a_1009_, lean_object* v_a_1010_, lean_object* v_a_1011_, lean_object* v_a_1012_, lean_object* v_a_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v_e_1008_, v_a_1009_, v_a_1010_, v_a_1011_, v_a_1012_, v_a_1013_, v_a_1014_);
lean_dec(v_a_1014_);
lean_dec_ref(v_a_1013_);
lean_dec(v_a_1012_);
lean_dec_ref(v_a_1011_);
lean_dec(v_a_1010_);
lean_dec(v_a_1009_);
return v_res_1016_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object* v_00_u03b2_1017_, lean_object* v_k_1018_, lean_object* v_t_1019_){
_start:
{
uint8_t v___x_1020_; 
v___x_1020_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_1018_, v_t_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_k_1022_, lean_object* v_t_1023_){
_start:
{
uint8_t v_res_1024_; lean_object* v_r_1025_; 
v_res_1024_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(v_00_u03b2_1021_, v_k_1022_, v_t_1023_);
lean_dec(v_t_1023_);
lean_dec(v_k_1022_);
v_r_1025_ = lean_box(v_res_1024_);
return v_r_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object* v_as_1026_, size_t v_sz_1027_, size_t v_i_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
lean_object* v___x_1037_; 
v___x_1037_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_1026_, v_sz_1027_, v_i_1028_, v_b_1029_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
return v___x_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object* v_as_1038_, lean_object* v_sz_1039_, lean_object* v_i_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
size_t v_sz_boxed_1049_; size_t v_i_boxed_1050_; lean_object* v_res_1051_; 
v_sz_boxed_1049_ = lean_unbox_usize(v_sz_1039_);
lean_dec(v_sz_1039_);
v_i_boxed_1050_ = lean_unbox_usize(v_i_1040_);
lean_dec(v_i_1040_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(v_as_1038_, v_sz_boxed_1049_, v_i_boxed_1050_, v_b_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v_as_1038_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_inst_1052_, lean_object* v_a_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v___x_1061_; 
v___x_1061_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_, v___y_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_inst_1062_, lean_object* v_a_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_inst_1062_, v_a_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec(v___y_1064_);
return v_res_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object* v_mvarId_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v___x_1075_; lean_object* v_mctx_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1075_ = lean_st_ref_get(v___y_1073_);
v_mctx_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc_ref(v_mctx_1076_);
lean_dec(v___x_1075_);
v___x_1077_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_1076_, v_mvarId_1072_);
lean_dec_ref(v_mctx_1076_);
v___x_1078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
return v___x_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object* v_mvarId_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_){
_start:
{
lean_object* v_res_1082_; 
v_res_1082_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec(v_mvarId_1079_);
return v_res_1082_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object* v_mvarId_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1083_, v___y_1087_);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object* v_mvarId_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v_res_1100_; 
v_res_1100_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_, v___y_1098_);
lean_dec(v___y_1098_);
lean_dec_ref(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec(v___y_1093_);
lean_dec(v_mvarId_1092_);
return v_res_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object* v_a_1101_, lean_object* v_as_1102_, size_t v_sz_1103_, size_t v_i_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_){
_start:
{
lean_object* v_a_1114_; uint8_t v___x_1118_; 
v___x_1118_ = lean_usize_dec_lt(v_i_1104_, v_sz_1103_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref(v_a_1101_);
v___x_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1119_, 0, v_b_1105_);
return v___x_1119_;
}
else
{
lean_object* v_array_1120_; lean_object* v_start_1121_; lean_object* v_stop_1122_; uint8_t v___x_1123_; 
v_array_1120_ = lean_ctor_get(v_b_1105_, 0);
v_start_1121_ = lean_ctor_get(v_b_1105_, 1);
v_stop_1122_ = lean_ctor_get(v_b_1105_, 2);
v___x_1123_ = lean_nat_dec_lt(v_start_1121_, v_stop_1122_);
if (v___x_1123_ == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v_a_1101_);
v___x_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1124_, 0, v_b_1105_);
return v___x_1124_;
}
else
{
lean_object* v___x_1126_; uint8_t v_isShared_1127_; uint8_t v_isSharedCheck_1148_; 
lean_inc(v_stop_1122_);
lean_inc(v_start_1121_);
lean_inc_ref(v_array_1120_);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_b_1105_);
if (v_isSharedCheck_1148_ == 0)
{
lean_object* v_unused_1149_; lean_object* v_unused_1150_; lean_object* v_unused_1151_; 
v_unused_1149_ = lean_ctor_get(v_b_1105_, 2);
lean_dec(v_unused_1149_);
v_unused_1150_ = lean_ctor_get(v_b_1105_, 1);
lean_dec(v_unused_1150_);
v_unused_1151_ = lean_ctor_get(v_b_1105_, 0);
lean_dec(v_unused_1151_);
v___x_1126_ = v_b_1105_;
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
else
{
lean_dec(v_b_1105_);
v___x_1126_ = lean_box(0);
v_isShared_1127_ = v_isSharedCheck_1148_;
goto v_resetjp_1125_;
}
v_resetjp_1125_:
{
lean_object* v_lctx_1128_; lean_object* v___x_1129_; lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1134_; 
v_lctx_1128_ = lean_ctor_get(v_a_1101_, 1);
v___x_1129_ = lean_array_fget(v_array_1120_, v_start_1121_);
v_a_1130_ = lean_array_uget_borrowed(v_as_1102_, v_i_1104_);
v___x_1131_ = lean_unsigned_to_nat(1u);
v___x_1132_ = lean_nat_add(v_start_1121_, v___x_1131_);
lean_dec(v_start_1121_);
if (v_isShared_1127_ == 0)
{
lean_ctor_set(v___x_1126_, 1, v___x_1132_);
v___x_1134_ = v___x_1126_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_array_1120_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v___x_1132_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_stop_1122_);
v___x_1134_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; uint8_t v___x_1136_; uint8_t v___x_1137_; 
lean_inc_ref(v_lctx_1128_);
v___x_1135_ = l_Lean_LocalContext_getFVar_x21(v_lctx_1128_, v_a_1130_);
v___x_1136_ = 0;
v___x_1137_ = l_Lean_LocalDecl_isLet(v___x_1135_, v___x_1136_);
lean_dec_ref(v___x_1135_);
if (v___x_1137_ == 0)
{
lean_dec(v___x_1129_);
v_a_1114_ = v___x_1134_;
goto v___jp_1113_;
}
else
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v___x_1129_, v___y_1106_, v___y_1107_, v___y_1108_, v___y_1109_, v___y_1110_, v___y_1111_);
if (lean_obj_tag(v___x_1138_) == 0)
{
lean_dec_ref_known(v___x_1138_, 1);
v_a_1114_ = v___x_1134_;
goto v___jp_1113_;
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec_ref(v___x_1134_);
lean_dec_ref(v_a_1101_);
v_a_1139_ = lean_ctor_get(v___x_1138_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1138_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1138_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1138_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
}
}
v___jp_1113_:
{
size_t v___x_1115_; size_t v___x_1116_; 
v___x_1115_ = ((size_t)1ULL);
v___x_1116_ = lean_usize_add(v_i_1104_, v___x_1115_);
v_i_1104_ = v___x_1116_;
v_b_1105_ = v_a_1114_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object* v_a_1152_, lean_object* v_as_1153_, lean_object* v_sz_1154_, lean_object* v_i_1155_, lean_object* v_b_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_, lean_object* v___y_1163_){
_start:
{
size_t v_sz_boxed_1164_; size_t v_i_boxed_1165_; lean_object* v_res_1166_; 
v_sz_boxed_1164_ = lean_unbox_usize(v_sz_1154_);
lean_dec(v_sz_1154_);
v_i_boxed_1165_ = lean_unbox_usize(v_i_1155_);
lean_dec(v_i_1155_);
v_res_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1152_, v_as_1153_, v_sz_boxed_1164_, v_i_boxed_1165_, v_b_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_, v___y_1161_, v___y_1162_);
lean_dec(v___y_1162_);
lean_dec_ref(v___y_1161_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1159_);
lean_dec(v___y_1158_);
lean_dec(v___y_1157_);
lean_dec_ref(v_as_1153_);
return v_res_1166_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object* v_as_1167_, lean_object* v___y_1168_){
_start:
{
if (lean_obj_tag(v_as_1167_) == 0)
{
lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1170_ = lean_box(0);
v___x_1171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1170_);
return v___x_1171_;
}
else
{
lean_object* v_head_1172_; lean_object* v_tail_1173_; lean_object* v___x_1174_; 
v_head_1172_ = lean_ctor_get(v_as_1167_, 0);
lean_inc(v_head_1172_);
v_tail_1173_ = lean_ctor_get(v_as_1167_, 1);
lean_inc(v_tail_1173_);
lean_dec_ref_known(v_as_1167_, 2);
v___x_1174_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_head_1172_, v___y_1168_);
if (lean_obj_tag(v___x_1174_) == 0)
{
lean_dec_ref_known(v___x_1174_, 1);
v_as_1167_ = v_tail_1173_;
goto _start;
}
else
{
lean_dec(v_tail_1173_);
return v___x_1174_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object* v_as_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_){
_start:
{
lean_object* v_res_1179_; 
v_res_1179_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1176_, v___y_1177_);
lean_dec(v___y_1177_);
return v_res_1179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object* v_mvarId_1180_, lean_object* v_args_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_){
_start:
{
lean_object* v___x_1189_; lean_object* v_a_1190_; lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1246_; 
v___x_1189_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1180_, v_a_1185_);
v_a_1190_ = lean_ctor_get(v___x_1189_, 0);
v_isSharedCheck_1246_ = !lean_is_exclusive(v___x_1189_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1192_ = v___x_1189_;
v_isShared_1193_ = v_isSharedCheck_1246_;
goto v_resetjp_1191_;
}
else
{
lean_inc(v_a_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1246_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
if (lean_obj_tag(v_a_1190_) == 1)
{
lean_object* v_val_1194_; lean_object* v_fvars_1195_; lean_object* v_mvarIdPending_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; uint8_t v___x_1199_; 
lean_del_object(v___x_1192_);
v_val_1194_ = lean_ctor_get(v_a_1190_, 0);
lean_inc(v_val_1194_);
lean_dec_ref_known(v_a_1190_, 1);
v_fvars_1195_ = lean_ctor_get(v_val_1194_, 0);
lean_inc_ref(v_fvars_1195_);
v_mvarIdPending_1196_ = lean_ctor_get(v_val_1194_, 1);
lean_inc(v_mvarIdPending_1196_);
lean_dec(v_val_1194_);
v___x_1197_ = lean_array_get_size(v_fvars_1195_);
v___x_1198_ = lean_array_get_size(v_args_1181_);
v___x_1199_ = lean_nat_dec_le(v___x_1197_, v___x_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; 
lean_dec(v_mvarIdPending_1196_);
lean_dec_ref(v_fvars_1195_);
lean_dec_ref(v_args_1181_);
lean_inc(v_a_1182_);
v___x_1200_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_a_1182_, v_a_1185_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1208_; 
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1208_ == 0)
{
lean_object* v_unused_1209_; 
v_unused_1209_ = lean_ctor_get(v___x_1200_, 0);
lean_dec(v_unused_1209_);
v___x_1202_ = v___x_1200_;
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v___x_1200_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1208_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1204_; lean_object* v___x_1206_; 
v___x_1204_ = lean_box(0);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 0, v___x_1204_);
v___x_1206_ = v___x_1202_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
return v___x_1200_;
}
}
else
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_MVarId_getDecl(v_mvarIdPending_1196_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; size_t v_sz_1214_; size_t v___x_1215_; lean_object* v___x_1216_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = lean_unsigned_to_nat(0u);
v___x_1213_ = l_Array_toSubarray___redArg(v_args_1181_, v___x_1212_, v___x_1198_);
v_sz_1214_ = lean_array_size(v_fvars_1195_);
v___x_1215_ = ((size_t)0ULL);
v___x_1216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1211_, v_fvars_1195_, v_sz_1214_, v___x_1215_, v___x_1213_, v_a_1182_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec_ref(v_fvars_1195_);
if (lean_obj_tag(v___x_1216_) == 0)
{
lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1224_; 
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1224_ == 0)
{
lean_object* v_unused_1225_; 
v_unused_1225_ = lean_ctor_get(v___x_1216_, 0);
lean_dec(v_unused_1225_);
v___x_1218_ = v___x_1216_;
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
else
{
lean_dec(v___x_1216_);
v___x_1218_ = lean_box(0);
v_isShared_1219_ = v_isSharedCheck_1224_;
goto v_resetjp_1217_;
}
v_resetjp_1217_:
{
lean_object* v___x_1220_; lean_object* v___x_1222_; 
v___x_1220_ = lean_box(0);
if (v_isShared_1219_ == 0)
{
lean_ctor_set(v___x_1218_, 0, v___x_1220_);
v___x_1222_ = v___x_1218_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
else
{
lean_object* v_a_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1233_; 
v_a_1226_ = lean_ctor_get(v___x_1216_, 0);
v_isSharedCheck_1233_ = !lean_is_exclusive(v___x_1216_);
if (v_isSharedCheck_1233_ == 0)
{
v___x_1228_ = v___x_1216_;
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_a_1226_);
lean_dec(v___x_1216_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1233_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v___x_1231_; 
if (v_isShared_1229_ == 0)
{
v___x_1231_ = v___x_1228_;
goto v_reusejp_1230_;
}
else
{
lean_object* v_reuseFailAlloc_1232_; 
v_reuseFailAlloc_1232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1232_, 0, v_a_1226_);
v___x_1231_ = v_reuseFailAlloc_1232_;
goto v_reusejp_1230_;
}
v_reusejp_1230_:
{
return v___x_1231_;
}
}
}
}
else
{
lean_object* v_a_1234_; lean_object* v___x_1236_; uint8_t v_isShared_1237_; uint8_t v_isSharedCheck_1241_; 
lean_dec_ref(v_fvars_1195_);
lean_dec_ref(v_args_1181_);
v_a_1234_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1241_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1236_ = v___x_1210_;
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
else
{
lean_inc(v_a_1234_);
lean_dec(v___x_1210_);
v___x_1236_ = lean_box(0);
v_isShared_1237_ = v_isSharedCheck_1241_;
goto v_resetjp_1235_;
}
v_resetjp_1235_:
{
lean_object* v___x_1239_; 
if (v_isShared_1237_ == 0)
{
v___x_1239_ = v___x_1236_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_a_1234_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
else
{
lean_object* v___x_1242_; lean_object* v___x_1244_; 
lean_dec(v_a_1190_);
lean_dec_ref(v_args_1181_);
v___x_1242_ = lean_box(0);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 0, v___x_1242_);
v___x_1244_ = v___x_1192_;
goto v_reusejp_1243_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1242_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object* v_mvarId_1247_, lean_object* v_args_1248_, lean_object* v_a_1249_, lean_object* v_a_1250_, lean_object* v_a_1251_, lean_object* v_a_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_){
_start:
{
lean_object* v_res_1256_; 
v_res_1256_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1247_, v_args_1248_, v_a_1249_, v_a_1250_, v_a_1251_, v_a_1252_, v_a_1253_, v_a_1254_);
lean_dec(v_a_1254_);
lean_dec_ref(v_a_1253_);
lean_dec(v_a_1252_);
lean_dec_ref(v_a_1251_);
lean_dec(v_a_1250_);
lean_dec(v_a_1249_);
lean_dec(v_mvarId_1247_);
return v_res_1256_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object* v_as_1257_, lean_object* v___y_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1257_, v___y_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object* v_as_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_, v___y_1271_, v___y_1272_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec(v___y_1267_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object* v_e_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_, lean_object* v_a_1283_){
_start:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = l_Lean_Expr_mvarId_x21(v_e_1277_);
v___x_1286_ = l_Lean_MVarId_findDecl_x3f___redArg(v___x_1285_, v_a_1281_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v___x_1289_; uint8_t v_isShared_1290_; uint8_t v_isSharedCheck_1317_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1289_ = v___x_1286_;
v_isShared_1290_ = v_isSharedCheck_1317_;
goto v_resetjp_1288_;
}
else
{
lean_inc(v_a_1287_);
lean_dec(v___x_1286_);
v___x_1289_ = lean_box(0);
v_isShared_1290_ = v_isSharedCheck_1317_;
goto v_resetjp_1288_;
}
v_resetjp_1288_:
{
if (lean_obj_tag(v_a_1287_) == 1)
{
lean_object* v_val_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1315_; 
v_val_1291_ = lean_ctor_get(v_a_1287_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1293_ = v_a_1287_;
v_isShared_1294_ = v_isSharedCheck_1315_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_val_1291_);
lean_dec(v_a_1287_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1315_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
uint8_t v___x_1304_; 
v___x_1304_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1278_);
if (v___x_1304_ == 0)
{
lean_dec(v___x_1285_);
goto v___jp_1295_;
}
else
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_1306_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v___x_1285_, v___x_1305_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
lean_dec(v___x_1285_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_dec_ref_known(v___x_1306_, 1);
goto v___jp_1295_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_del_object(v___x_1293_);
lean_dec(v_val_1291_);
lean_del_object(v___x_1289_);
lean_dec_ref(v_e_1277_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
}
v___jp_1295_:
{
lean_object* v_type_1296_; lean_object* v___x_1298_; 
v_type_1296_ = lean_ctor_get(v_val_1291_, 2);
lean_inc_ref(v_type_1296_);
lean_dec(v_val_1291_);
if (v_isShared_1294_ == 0)
{
lean_ctor_set(v___x_1293_, 0, v_type_1296_);
v___x_1298_ = v___x_1293_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_type_1296_);
v___x_1298_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1299_, 0, v_e_1277_);
lean_ctor_set(v___x_1299_, 1, v___x_1298_);
if (v_isShared_1290_ == 0)
{
lean_ctor_set(v___x_1289_, 0, v___x_1299_);
v___x_1301_ = v___x_1289_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v___x_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
}
else
{
lean_object* v___x_1316_; 
lean_del_object(v___x_1289_);
lean_dec(v_a_1287_);
lean_dec_ref(v_e_1277_);
v___x_1316_ = l_Lean_Meta_throwUnknownMVar___redArg(v___x_1285_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_);
return v___x_1316_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v___x_1285_);
lean_dec_ref(v_e_1277_);
v_a_1318_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1286_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1286_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object* v_e_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_, lean_object* v_a_1329_, lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v_res_1334_; 
v_res_1334_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1326_, v_a_1327_, v_a_1328_, v_a_1329_, v_a_1330_, v_a_1331_, v_a_1332_);
lean_dec(v_a_1332_);
lean_dec_ref(v_a_1331_);
lean_dec(v_a_1330_);
lean_dec_ref(v_a_1329_);
lean_dec(v_a_1328_);
lean_dec(v_a_1327_);
return v_res_1334_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1335_; 
v___x_1335_ = l_instMonadEIO(lean_box(0));
return v___x_1335_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object* v_msg_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v_toApplicative_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1413_; 
v___x_1348_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0);
v___x_1349_ = l_StateRefT_x27_instMonad___redArg(v___x_1348_);
v_toApplicative_1350_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1413_ == 0)
{
lean_object* v_unused_1414_; 
v_unused_1414_ = lean_ctor_get(v___x_1349_, 1);
lean_dec(v_unused_1414_);
v___x_1352_ = v___x_1349_;
v_isShared_1353_ = v_isSharedCheck_1413_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_toApplicative_1350_);
lean_dec(v___x_1349_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1413_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v_toFunctor_1354_; lean_object* v_toSeq_1355_; lean_object* v_toSeqLeft_1356_; lean_object* v_toSeqRight_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1411_; 
v_toFunctor_1354_ = lean_ctor_get(v_toApplicative_1350_, 0);
v_toSeq_1355_ = lean_ctor_get(v_toApplicative_1350_, 2);
v_toSeqLeft_1356_ = lean_ctor_get(v_toApplicative_1350_, 3);
v_toSeqRight_1357_ = lean_ctor_get(v_toApplicative_1350_, 4);
v_isSharedCheck_1411_ = !lean_is_exclusive(v_toApplicative_1350_);
if (v_isSharedCheck_1411_ == 0)
{
lean_object* v_unused_1412_; 
v_unused_1412_ = lean_ctor_get(v_toApplicative_1350_, 1);
lean_dec(v_unused_1412_);
v___x_1359_ = v_toApplicative_1350_;
v_isShared_1360_ = v_isSharedCheck_1411_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_toSeqRight_1357_);
lean_inc(v_toSeqLeft_1356_);
lean_inc(v_toSeq_1355_);
lean_inc(v_toFunctor_1354_);
lean_dec(v_toApplicative_1350_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1411_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___f_1361_; lean_object* v___f_1362_; lean_object* v___f_1363_; lean_object* v___f_1364_; lean_object* v___x_1365_; lean_object* v___f_1366_; lean_object* v___f_1367_; lean_object* v___f_1368_; lean_object* v___x_1370_; 
v___f_1361_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1));
v___f_1362_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1354_);
v___f_1363_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1363_, 0, v_toFunctor_1354_);
v___f_1364_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1364_, 0, v_toFunctor_1354_);
v___x_1365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___f_1363_);
lean_ctor_set(v___x_1365_, 1, v___f_1364_);
v___f_1366_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1366_, 0, v_toSeqRight_1357_);
v___f_1367_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1367_, 0, v_toSeqLeft_1356_);
v___f_1368_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1368_, 0, v_toSeq_1355_);
if (v_isShared_1360_ == 0)
{
lean_ctor_set(v___x_1359_, 4, v___f_1366_);
lean_ctor_set(v___x_1359_, 3, v___f_1367_);
lean_ctor_set(v___x_1359_, 2, v___f_1368_);
lean_ctor_set(v___x_1359_, 1, v___f_1361_);
lean_ctor_set(v___x_1359_, 0, v___x_1365_);
v___x_1370_ = v___x_1359_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v___x_1365_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v___f_1361_);
lean_ctor_set(v_reuseFailAlloc_1410_, 2, v___f_1368_);
lean_ctor_set(v_reuseFailAlloc_1410_, 3, v___f_1367_);
lean_ctor_set(v_reuseFailAlloc_1410_, 4, v___f_1366_);
v___x_1370_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
lean_object* v___x_1372_; 
if (v_isShared_1353_ == 0)
{
lean_ctor_set(v___x_1352_, 1, v___f_1362_);
lean_ctor_set(v___x_1352_, 0, v___x_1370_);
v___x_1372_ = v___x_1352_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1409_; 
v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1370_);
lean_ctor_set(v_reuseFailAlloc_1409_, 1, v___f_1362_);
v___x_1372_ = v_reuseFailAlloc_1409_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
lean_object* v___x_1373_; lean_object* v_toApplicative_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1407_; 
v___x_1373_ = l_StateRefT_x27_instMonad___redArg(v___x_1372_);
v_toApplicative_1374_ = lean_ctor_get(v___x_1373_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1373_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; 
v_unused_1408_ = lean_ctor_get(v___x_1373_, 1);
lean_dec(v_unused_1408_);
v___x_1376_ = v___x_1373_;
v_isShared_1377_ = v_isSharedCheck_1407_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_toApplicative_1374_);
lean_dec(v___x_1373_);
v___x_1376_ = lean_box(0);
v_isShared_1377_ = v_isSharedCheck_1407_;
goto v_resetjp_1375_;
}
v_resetjp_1375_:
{
lean_object* v_toFunctor_1378_; lean_object* v_toSeq_1379_; lean_object* v_toSeqLeft_1380_; lean_object* v_toSeqRight_1381_; lean_object* v___x_1383_; uint8_t v_isShared_1384_; uint8_t v_isSharedCheck_1405_; 
v_toFunctor_1378_ = lean_ctor_get(v_toApplicative_1374_, 0);
v_toSeq_1379_ = lean_ctor_get(v_toApplicative_1374_, 2);
v_toSeqLeft_1380_ = lean_ctor_get(v_toApplicative_1374_, 3);
v_toSeqRight_1381_ = lean_ctor_get(v_toApplicative_1374_, 4);
v_isSharedCheck_1405_ = !lean_is_exclusive(v_toApplicative_1374_);
if (v_isSharedCheck_1405_ == 0)
{
lean_object* v_unused_1406_; 
v_unused_1406_ = lean_ctor_get(v_toApplicative_1374_, 1);
lean_dec(v_unused_1406_);
v___x_1383_ = v_toApplicative_1374_;
v_isShared_1384_ = v_isSharedCheck_1405_;
goto v_resetjp_1382_;
}
else
{
lean_inc(v_toSeqRight_1381_);
lean_inc(v_toSeqLeft_1380_);
lean_inc(v_toSeq_1379_);
lean_inc(v_toFunctor_1378_);
lean_dec(v_toApplicative_1374_);
v___x_1383_ = lean_box(0);
v_isShared_1384_ = v_isSharedCheck_1405_;
goto v_resetjp_1382_;
}
v_resetjp_1382_:
{
lean_object* v___f_1385_; lean_object* v___f_1386_; lean_object* v___f_1387_; lean_object* v___f_1388_; lean_object* v___x_1389_; lean_object* v___f_1390_; lean_object* v___f_1391_; lean_object* v___f_1392_; lean_object* v___x_1394_; 
v___f_1385_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3));
v___f_1386_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1378_);
v___f_1387_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1387_, 0, v_toFunctor_1378_);
v___f_1388_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1388_, 0, v_toFunctor_1378_);
v___x_1389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1389_, 0, v___f_1387_);
lean_ctor_set(v___x_1389_, 1, v___f_1388_);
v___f_1390_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1390_, 0, v_toSeqRight_1381_);
v___f_1391_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1391_, 0, v_toSeqLeft_1380_);
v___f_1392_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1392_, 0, v_toSeq_1379_);
if (v_isShared_1384_ == 0)
{
lean_ctor_set(v___x_1383_, 4, v___f_1390_);
lean_ctor_set(v___x_1383_, 3, v___f_1391_);
lean_ctor_set(v___x_1383_, 2, v___f_1392_);
lean_ctor_set(v___x_1383_, 1, v___f_1385_);
lean_ctor_set(v___x_1383_, 0, v___x_1389_);
v___x_1394_ = v___x_1383_;
goto v_reusejp_1393_;
}
else
{
lean_object* v_reuseFailAlloc_1404_; 
v_reuseFailAlloc_1404_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1404_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1404_, 1, v___f_1385_);
lean_ctor_set(v_reuseFailAlloc_1404_, 2, v___f_1392_);
lean_ctor_set(v_reuseFailAlloc_1404_, 3, v___f_1391_);
lean_ctor_set(v_reuseFailAlloc_1404_, 4, v___f_1390_);
v___x_1394_ = v_reuseFailAlloc_1404_;
goto v_reusejp_1393_;
}
v_reusejp_1393_:
{
lean_object* v___x_1396_; 
if (v_isShared_1377_ == 0)
{
lean_ctor_set(v___x_1376_, 1, v___f_1386_);
lean_ctor_set(v___x_1376_, 0, v___x_1394_);
v___x_1396_ = v___x_1376_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1403_, 1, v___f_1386_);
v___x_1396_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___f_1400_; lean_object* v___x_1519__overap_1401_; lean_object* v___x_1402_; 
v___x_1397_ = l_StateRefT_x27_instMonad___redArg(v___x_1396_);
v___x_1398_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1399_ = l_instInhabitedOfMonad___redArg(v___x_1397_, v___x_1398_);
v___f_1400_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1400_, 0, v___x_1399_);
v___x_1519__overap_1401_ = lean_panic_fn_borrowed(v___f_1400_, v_msg_1340_);
lean_dec_ref(v___f_1400_);
lean_inc(v___y_1346_);
lean_inc_ref(v___y_1345_);
lean_inc(v___y_1344_);
lean_inc_ref(v___y_1343_);
lean_inc(v___y_1342_);
lean_inc(v___y_1341_);
v___x_1402_ = lean_apply_7(v___x_1519__overap_1401_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_, lean_box(0));
return v___x_1402_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object* v_msg_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
lean_dec(v___y_1421_);
lean_dec_ref(v___y_1420_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec(v___y_1416_);
return v_res_1423_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1424_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
return v___x_1426_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; 
v___x_1427_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1428_ = lean_unsigned_to_nat(0u);
v___x_1429_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1428_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_ctor_set(v___x_1429_, 2, v___x_1428_);
lean_ctor_set(v___x_1429_, 3, v___x_1428_);
lean_ctor_set(v___x_1429_, 4, v___x_1427_);
lean_ctor_set(v___x_1429_, 5, v___x_1427_);
lean_ctor_set(v___x_1429_, 6, v___x_1427_);
lean_ctor_set(v___x_1429_, 7, v___x_1427_);
lean_ctor_set(v___x_1429_, 8, v___x_1427_);
lean_ctor_set(v___x_1429_, 9, v___x_1427_);
lean_ctor_set(v___x_1429_, 10, v___x_1427_);
return v___x_1429_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_unsigned_to_nat(32u);
v___x_1431_ = lean_mk_empty_array_with_capacity(v___x_1430_);
v___x_1432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1433_ = ((size_t)5ULL);
v___x_1434_ = lean_unsigned_to_nat(0u);
v___x_1435_ = lean_unsigned_to_nat(32u);
v___x_1436_ = lean_mk_empty_array_with_capacity(v___x_1435_);
v___x_1437_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1438_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1438_, 0, v___x_1437_);
lean_ctor_set(v___x_1438_, 1, v___x_1436_);
lean_ctor_set(v___x_1438_, 2, v___x_1434_);
lean_ctor_set(v___x_1438_, 3, v___x_1434_);
lean_ctor_set_usize(v___x_1438_, 4, v___x_1433_);
return v___x_1438_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1439_ = lean_box(1);
v___x_1440_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1441_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1442_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
lean_ctor_set(v___x_1442_, 1, v___x_1440_);
lean_ctor_set(v___x_1442_, 2, v___x_1439_);
return v___x_1442_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1444_; lean_object* v___x_1445_; 
v___x_1444_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1445_ = l_Lean_stringToMessageData(v___x_1444_);
return v___x_1445_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1447_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1448_ = l_Lean_stringToMessageData(v___x_1447_);
return v___x_1448_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1450_; lean_object* v___x_1451_; 
v___x_1450_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1451_ = l_Lean_stringToMessageData(v___x_1450_);
return v___x_1451_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1462_; lean_object* v___x_1463_; 
v___x_1462_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1463_ = l_Lean_stringToMessageData(v___x_1462_);
return v___x_1463_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1464_, lean_object* v_declHint_1465_, lean_object* v___y_1466_){
_start:
{
lean_object* v___x_1468_; lean_object* v_env_1469_; uint8_t v___x_1470_; 
v___x_1468_ = lean_st_ref_get(v___y_1466_);
v_env_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc_ref(v_env_1469_);
lean_dec(v___x_1468_);
v___x_1470_ = l_Lean_Name_isAnonymous(v_declHint_1465_);
if (v___x_1470_ == 0)
{
uint8_t v_isExporting_1471_; 
v_isExporting_1471_ = lean_ctor_get_uint8(v_env_1469_, sizeof(void*)*8);
if (v_isExporting_1471_ == 0)
{
lean_object* v___x_1472_; 
lean_dec_ref(v_env_1469_);
lean_dec(v_declHint_1465_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_msg_1464_);
return v___x_1472_;
}
else
{
lean_object* v___x_1473_; uint8_t v___x_1474_; 
lean_inc_ref(v_env_1469_);
v___x_1473_ = l_Lean_Environment_setExporting(v_env_1469_, v___x_1470_);
lean_inc(v_declHint_1465_);
lean_inc_ref(v___x_1473_);
v___x_1474_ = l_Lean_Environment_contains(v___x_1473_, v_declHint_1465_, v_isExporting_1471_);
if (v___x_1474_ == 0)
{
lean_object* v___x_1475_; 
lean_dec_ref(v___x_1473_);
lean_dec_ref(v_env_1469_);
lean_dec(v_declHint_1465_);
v___x_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1475_, 0, v_msg_1464_);
return v___x_1475_;
}
else
{
lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v_c_1481_; lean_object* v___x_1482_; 
v___x_1476_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1477_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1478_ = l_Lean_Options_empty;
v___x_1479_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1473_);
lean_ctor_set(v___x_1479_, 1, v___x_1476_);
lean_ctor_set(v___x_1479_, 2, v___x_1477_);
lean_ctor_set(v___x_1479_, 3, v___x_1478_);
lean_inc(v_declHint_1465_);
v___x_1480_ = l_Lean_MessageData_ofConstName(v_declHint_1465_, v___x_1470_);
v_c_1481_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1481_, 0, v___x_1479_);
lean_ctor_set(v_c_1481_, 1, v___x_1480_);
v___x_1482_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1469_, v_declHint_1465_);
if (lean_obj_tag(v___x_1482_) == 0)
{
lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
lean_dec_ref(v_env_1469_);
lean_dec(v_declHint_1465_);
v___x_1483_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v_c_1481_);
v___x_1485_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1486_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1486_, 0, v___x_1484_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
v___x_1487_ = l_Lean_MessageData_note(v___x_1486_);
v___x_1488_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1488_, 0, v_msg_1464_);
lean_ctor_set(v___x_1488_, 1, v___x_1487_);
v___x_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1489_, 0, v___x_1488_);
return v___x_1489_;
}
else
{
lean_object* v_val_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1525_; 
v_val_1490_ = lean_ctor_get(v___x_1482_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1482_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1492_ = v___x_1482_;
v_isShared_1493_ = v_isSharedCheck_1525_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_val_1490_);
lean_dec(v___x_1482_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1525_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v_mod_1497_; uint8_t v___x_1498_; 
v___x_1494_ = lean_box(0);
v___x_1495_ = l_Lean_Environment_header(v_env_1469_);
lean_dec_ref(v_env_1469_);
v___x_1496_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1495_);
v_mod_1497_ = lean_array_get(v___x_1494_, v___x_1496_, v_val_1490_);
lean_dec(v_val_1490_);
lean_dec_ref(v___x_1496_);
v___x_1498_ = l_Lean_isPrivateName(v_declHint_1465_);
lean_dec(v_declHint_1465_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1510_; 
v___x_1499_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v_c_1481_);
v___x_1501_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1502_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1500_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_MessageData_ofName(v_mod_1497_);
v___x_1504_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1502_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
v___x_1505_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1506_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1504_);
lean_ctor_set(v___x_1506_, 1, v___x_1505_);
v___x_1507_ = l_Lean_MessageData_note(v___x_1506_);
v___x_1508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1508_, 0, v_msg_1464_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1508_);
v___x_1510_ = v___x_1492_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1508_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1523_; 
v___x_1512_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1513_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v_c_1481_);
v___x_1514_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1513_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = l_Lean_MessageData_ofName(v_mod_1497_);
v___x_1517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1517_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = l_Lean_MessageData_note(v___x_1519_);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v_msg_1464_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
if (v_isShared_1493_ == 0)
{
lean_ctor_set_tag(v___x_1492_, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1521_);
v___x_1523_ = v___x_1492_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v___x_1521_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1526_; 
lean_dec_ref(v_env_1469_);
lean_dec(v_declHint_1465_);
v___x_1526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_msg_1464_);
return v___x_1526_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1527_, lean_object* v_declHint_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1527_, v_declHint_1528_, v___y_1529_);
lean_dec(v___y_1529_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1532_, lean_object* v_declHint_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v_a_1542_; lean_object* v___x_1544_; uint8_t v_isShared_1545_; uint8_t v_isSharedCheck_1551_; 
v___x_1541_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1532_, v_declHint_1533_, v___y_1539_);
v_a_1542_ = lean_ctor_get(v___x_1541_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1541_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1544_ = v___x_1541_;
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
else
{
lean_inc(v_a_1542_);
lean_dec(v___x_1541_);
v___x_1544_ = lean_box(0);
v_isShared_1545_ = v_isSharedCheck_1551_;
goto v_resetjp_1543_;
}
v_resetjp_1543_:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; 
v___x_1546_ = l_Lean_unknownIdentifierMessageTag;
v___x_1547_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1547_, 0, v___x_1546_);
lean_ctor_set(v___x_1547_, 1, v_a_1542_);
if (v_isShared_1545_ == 0)
{
lean_ctor_set(v___x_1544_, 0, v___x_1547_);
v___x_1549_ = v___x_1544_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1552_, lean_object* v_declHint_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1552_, v_declHint_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec(v___y_1554_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v___x_1568_; lean_object* v_env_1569_; lean_object* v___x_1570_; lean_object* v_mctx_1571_; lean_object* v_lctx_1572_; lean_object* v_options_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1568_ = lean_st_ref_get(v___y_1566_);
v_env_1569_ = lean_ctor_get(v___x_1568_, 0);
lean_inc_ref(v_env_1569_);
lean_dec(v___x_1568_);
v___x_1570_ = lean_st_ref_get(v___y_1564_);
v_mctx_1571_ = lean_ctor_get(v___x_1570_, 0);
lean_inc_ref(v_mctx_1571_);
lean_dec(v___x_1570_);
v_lctx_1572_ = lean_ctor_get(v___y_1563_, 2);
v_options_1573_ = lean_ctor_get(v___y_1565_, 2);
lean_inc_ref(v_options_1573_);
lean_inc_ref(v_lctx_1572_);
v___x_1574_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1574_, 0, v_env_1569_);
lean_ctor_set(v___x_1574_, 1, v_mctx_1571_);
lean_ctor_set(v___x_1574_, 2, v_lctx_1572_);
lean_ctor_set(v___x_1574_, 3, v_options_1573_);
v___x_1575_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1575_, 0, v___x_1574_);
lean_ctor_set(v___x_1575_, 1, v_msgData_1562_);
v___x_1576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
return v___x_1576_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v_ref_1590_; lean_object* v___x_1591_; lean_object* v_a_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1600_; 
v_ref_1590_ = lean_ctor_get(v___y_1587_, 5);
v___x_1591_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
v_a_1592_ = lean_ctor_get(v___x_1591_, 0);
v_isSharedCheck_1600_ = !lean_is_exclusive(v___x_1591_);
if (v_isSharedCheck_1600_ == 0)
{
v___x_1594_ = v___x_1591_;
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_a_1592_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1600_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
lean_object* v___x_1596_; lean_object* v___x_1598_; 
lean_inc(v_ref_1590_);
v___x_1596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1596_, 0, v_ref_1590_);
lean_ctor_set(v___x_1596_, 1, v_a_1592_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set_tag(v___x_1594_, 1);
lean_ctor_set(v___x_1594_, 0, v___x_1596_);
v___x_1598_ = v___x_1594_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1599_; 
v_reuseFailAlloc_1599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1599_, 0, v___x_1596_);
v___x_1598_ = v_reuseFailAlloc_1599_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
return v___x_1598_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1601_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1608_, lean_object* v_msg_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v_fileName_1617_; lean_object* v_fileMap_1618_; lean_object* v_options_1619_; lean_object* v_currRecDepth_1620_; lean_object* v_maxRecDepth_1621_; lean_object* v_ref_1622_; lean_object* v_currNamespace_1623_; lean_object* v_openDecls_1624_; lean_object* v_initHeartbeats_1625_; lean_object* v_maxHeartbeats_1626_; lean_object* v_quotContext_1627_; lean_object* v_currMacroScope_1628_; uint8_t v_diag_1629_; lean_object* v_cancelTk_x3f_1630_; uint8_t v_suppressElabErrors_1631_; lean_object* v_inheritedTraceOptions_1632_; lean_object* v_ref_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; 
v_fileName_1617_ = lean_ctor_get(v___y_1614_, 0);
v_fileMap_1618_ = lean_ctor_get(v___y_1614_, 1);
v_options_1619_ = lean_ctor_get(v___y_1614_, 2);
v_currRecDepth_1620_ = lean_ctor_get(v___y_1614_, 3);
v_maxRecDepth_1621_ = lean_ctor_get(v___y_1614_, 4);
v_ref_1622_ = lean_ctor_get(v___y_1614_, 5);
v_currNamespace_1623_ = lean_ctor_get(v___y_1614_, 6);
v_openDecls_1624_ = lean_ctor_get(v___y_1614_, 7);
v_initHeartbeats_1625_ = lean_ctor_get(v___y_1614_, 8);
v_maxHeartbeats_1626_ = lean_ctor_get(v___y_1614_, 9);
v_quotContext_1627_ = lean_ctor_get(v___y_1614_, 10);
v_currMacroScope_1628_ = lean_ctor_get(v___y_1614_, 11);
v_diag_1629_ = lean_ctor_get_uint8(v___y_1614_, sizeof(void*)*14);
v_cancelTk_x3f_1630_ = lean_ctor_get(v___y_1614_, 12);
v_suppressElabErrors_1631_ = lean_ctor_get_uint8(v___y_1614_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1632_ = lean_ctor_get(v___y_1614_, 13);
v_ref_1633_ = l_Lean_replaceRef(v_ref_1608_, v_ref_1622_);
lean_inc_ref(v_inheritedTraceOptions_1632_);
lean_inc(v_cancelTk_x3f_1630_);
lean_inc(v_currMacroScope_1628_);
lean_inc(v_quotContext_1627_);
lean_inc(v_maxHeartbeats_1626_);
lean_inc(v_initHeartbeats_1625_);
lean_inc(v_openDecls_1624_);
lean_inc(v_currNamespace_1623_);
lean_inc(v_maxRecDepth_1621_);
lean_inc(v_currRecDepth_1620_);
lean_inc_ref(v_options_1619_);
lean_inc_ref(v_fileMap_1618_);
lean_inc_ref(v_fileName_1617_);
v___x_1634_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1634_, 0, v_fileName_1617_);
lean_ctor_set(v___x_1634_, 1, v_fileMap_1618_);
lean_ctor_set(v___x_1634_, 2, v_options_1619_);
lean_ctor_set(v___x_1634_, 3, v_currRecDepth_1620_);
lean_ctor_set(v___x_1634_, 4, v_maxRecDepth_1621_);
lean_ctor_set(v___x_1634_, 5, v_ref_1633_);
lean_ctor_set(v___x_1634_, 6, v_currNamespace_1623_);
lean_ctor_set(v___x_1634_, 7, v_openDecls_1624_);
lean_ctor_set(v___x_1634_, 8, v_initHeartbeats_1625_);
lean_ctor_set(v___x_1634_, 9, v_maxHeartbeats_1626_);
lean_ctor_set(v___x_1634_, 10, v_quotContext_1627_);
lean_ctor_set(v___x_1634_, 11, v_currMacroScope_1628_);
lean_ctor_set(v___x_1634_, 12, v_cancelTk_x3f_1630_);
lean_ctor_set(v___x_1634_, 13, v_inheritedTraceOptions_1632_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*14, v_diag_1629_);
lean_ctor_set_uint8(v___x_1634_, sizeof(void*)*14 + 1, v_suppressElabErrors_1631_);
v___x_1635_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1609_, v___y_1612_, v___y_1613_, v___x_1634_, v___y_1615_);
lean_dec_ref_known(v___x_1634_, 14);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1636_, lean_object* v_msg_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1636_, v_msg_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
lean_dec(v_ref_1636_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1646_, lean_object* v_msg_1647_, lean_object* v_declHint_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_, lean_object* v___y_1653_, lean_object* v___y_1654_){
_start:
{
lean_object* v___x_1656_; lean_object* v_a_1657_; lean_object* v___x_1658_; 
v___x_1656_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1647_, v_declHint_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref(v___x_1656_);
v___x_1658_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1646_, v_a_1657_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1659_, lean_object* v_msg_1660_, lean_object* v_declHint_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1659_, v_msg_1660_, v_declHint_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
lean_dec(v___y_1667_);
lean_dec_ref(v___y_1666_);
lean_dec(v___y_1665_);
lean_dec_ref(v___y_1664_);
lean_dec(v___y_1663_);
lean_dec(v___y_1662_);
lean_dec(v_ref_1659_);
return v_res_1669_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1672_ = l_Lean_stringToMessageData(v___x_1671_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1675_ = l_Lean_stringToMessageData(v___x_1674_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1676_, lean_object* v_constName_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; uint8_t v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1685_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1686_ = 0;
lean_inc(v_constName_1677_);
v___x_1687_ = l_Lean_MessageData_ofConstName(v_constName_1677_, v___x_1686_);
v___x_1688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1685_);
lean_ctor_set(v___x_1688_, 1, v___x_1687_);
v___x_1689_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1690_, 0, v___x_1688_);
lean_ctor_set(v___x_1690_, 1, v___x_1689_);
v___x_1691_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1676_, v___x_1690_, v_constName_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1692_, lean_object* v_constName_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1692_, v_constName_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
lean_dec(v___y_1699_);
lean_dec_ref(v___y_1698_);
lean_dec(v___y_1697_);
lean_dec_ref(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v___y_1694_);
lean_dec(v_ref_1692_);
return v_res_1701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
lean_object* v_ref_1710_; lean_object* v___x_1711_; 
v_ref_1710_ = lean_ctor_get(v___y_1707_, 5);
v___x_1711_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1710_, v_constName_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_);
return v___x_1711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
lean_object* v_res_1720_; 
v_res_1720_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
return v_res_1720_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_){
_start:
{
lean_object* v___x_1729_; lean_object* v_env_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; 
v___x_1729_ = lean_st_ref_get(v___y_1727_);
v_env_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc_ref(v_env_1730_);
lean_dec(v___x_1729_);
v___x_1731_ = 0;
lean_inc(v_constName_1721_);
v___x_1732_ = l_Lean_Environment_findConstVal_x3f(v_env_1730_, v_constName_1721_, v___x_1731_);
if (lean_obj_tag(v___x_1732_) == 0)
{
lean_object* v___x_1733_; 
v___x_1733_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_);
return v___x_1733_;
}
else
{
lean_object* v_val_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1741_; 
lean_dec(v_constName_1721_);
v_val_1734_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1736_ = v___x_1732_;
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_val_1734_);
lean_dec(v___x_1732_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1741_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1739_; 
if (v_isShared_1737_ == 0)
{
lean_ctor_set_tag(v___x_1736_, 0);
v___x_1739_ = v___x_1736_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_val_1734_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
return v___x_1739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec(v___y_1743_);
return v_res_1750_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1754_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1755_ = lean_unsigned_to_nat(35u);
v___x_1756_ = lean_unsigned_to_nat(203u);
v___x_1757_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1758_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1759_ = l_mkPanicMessageWithDecl(v___x_1758_, v___x_1757_, v___x_1756_, v___x_1755_, v___x_1754_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
if (lean_obj_tag(v_e_1760_) == 4)
{
lean_object* v_declName_1768_; lean_object* v_us_1769_; lean_object* v___x_1770_; 
v_declName_1768_ = lean_ctor_get(v_e_1760_, 0);
v_us_1769_ = lean_ctor_get(v_e_1760_, 1);
lean_inc(v_declName_1768_);
v___x_1770_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1768_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v_levelParams_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; uint8_t v___x_1775_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v_levelParams_1772_ = lean_ctor_get(v_a_1771_, 1);
v___x_1773_ = l_List_lengthTR___redArg(v_levelParams_1772_);
v___x_1774_ = l_List_lengthTR___redArg(v_us_1769_);
v___x_1775_ = lean_nat_dec_eq(v___x_1773_, v___x_1774_);
lean_dec(v___x_1774_);
lean_dec(v___x_1773_);
if (v___x_1775_ == 0)
{
lean_object* v___x_1776_; 
lean_inc(v_us_1769_);
lean_inc(v_declName_1768_);
lean_dec(v_a_1771_);
lean_dec_ref_known(v_e_1760_, 2);
v___x_1776_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1768_, v_us_1769_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1776_;
}
else
{
lean_object* v___x_1777_; 
lean_inc(v_us_1769_);
v___x_1777_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1771_, v_us_1769_, v___y_1766_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1787_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1780_ = v___x_1777_;
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1777_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1787_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1785_; 
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v_a_1778_);
v___x_1783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1783_, 0, v_e_1760_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
if (v_isShared_1781_ == 0)
{
lean_ctor_set(v___x_1780_, 0, v___x_1783_);
v___x_1785_ = v___x_1780_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v___x_1783_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
else
{
lean_object* v_a_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1795_; 
lean_dec_ref_known(v_e_1760_, 2);
v_a_1788_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1795_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1795_ == 0)
{
v___x_1790_ = v___x_1777_;
v_isShared_1791_ = v_isSharedCheck_1795_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_a_1788_);
lean_dec(v___x_1777_);
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
lean_object* v_a_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1803_; 
lean_dec_ref_known(v_e_1760_, 2);
v_a_1796_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1798_ = v___x_1770_;
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_a_1796_);
lean_dec(v___x_1770_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1803_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1801_; 
if (v_isShared_1799_ == 0)
{
v___x_1801_ = v___x_1798_;
goto v_reusejp_1800_;
}
else
{
lean_object* v_reuseFailAlloc_1802_; 
v_reuseFailAlloc_1802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1802_, 0, v_a_1796_);
v___x_1801_ = v_reuseFailAlloc_1802_;
goto v_reusejp_1800_;
}
v_reusejp_1800_:
{
return v___x_1801_;
}
}
}
}
else
{
lean_object* v___x_1804_; lean_object* v___x_1805_; 
lean_dec_ref(v_e_1760_);
v___x_1804_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1805_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1804_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
return v___x_1805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1806_, v___y_1807_, v___y_1808_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
lean_dec(v___y_1810_);
lean_dec_ref(v___y_1809_);
lean_dec(v___y_1808_);
lean_dec(v___y_1807_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
lean_object* v___y_1823_; lean_object* v___x_1824_; 
lean_inc_ref(v_e_1815_);
v___y_1823_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1823_, 0, v_e_1815_);
v___x_1824_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1815_, v___y_1823_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_, v_a_1821_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1825_, v_a_1826_, v_a_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec(v_a_1827_);
lean_dec(v_a_1826_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1834_, lean_object* v_constName_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1835_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1844_, lean_object* v_constName_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1844_, v_constName_1845_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
lean_dec(v___y_1849_);
lean_dec_ref(v___y_1848_);
lean_dec(v___y_1847_);
lean_dec(v___y_1846_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1854_, lean_object* v_ref_1855_, lean_object* v_constName_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___x_1864_; 
v___x_1864_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1855_, v_constName_1856_, v___y_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
return v___x_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1865_, lean_object* v_ref_1866_, lean_object* v_constName_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_){
_start:
{
lean_object* v_res_1875_; 
v_res_1875_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1865_, v_ref_1866_, v_constName_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_);
lean_dec(v___y_1873_);
lean_dec_ref(v___y_1872_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
lean_dec(v___y_1869_);
lean_dec(v___y_1868_);
lean_dec(v_ref_1866_);
return v_res_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1876_, lean_object* v_ref_1877_, lean_object* v_msg_1878_, lean_object* v_declHint_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v___x_1887_; 
v___x_1887_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1877_, v_msg_1878_, v_declHint_1879_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
return v___x_1887_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1888_, lean_object* v_ref_1889_, lean_object* v_msg_1890_, lean_object* v_declHint_1891_, lean_object* v___y_1892_, lean_object* v___y_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1888_, v_ref_1889_, v_msg_1890_, v_declHint_1891_, v___y_1892_, v___y_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
lean_dec(v___y_1893_);
lean_dec(v___y_1892_);
lean_dec(v_ref_1889_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1900_, lean_object* v_declHint_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_, lean_object* v___y_1906_, lean_object* v___y_1907_){
_start:
{
lean_object* v___x_1909_; 
v___x_1909_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1900_, v_declHint_1901_, v___y_1907_);
return v___x_1909_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1910_, lean_object* v_declHint_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_, lean_object* v___y_1915_, lean_object* v___y_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v_res_1919_; 
v_res_1919_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1910_, v_declHint_1911_, v___y_1912_, v___y_1913_, v___y_1914_, v___y_1915_, v___y_1916_, v___y_1917_);
lean_dec(v___y_1917_);
lean_dec_ref(v___y_1916_);
lean_dec(v___y_1915_);
lean_dec_ref(v___y_1914_);
lean_dec(v___y_1913_);
lean_dec(v___y_1912_);
return v_res_1919_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1920_, lean_object* v_ref_1921_, lean_object* v_msg_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_, lean_object* v___y_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1921_, v_msg_1922_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1931_, lean_object* v_ref_1932_, lean_object* v_msg_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1931_, v_ref_1932_, v_msg_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_, v___y_1939_);
lean_dec(v___y_1939_);
lean_dec_ref(v___y_1938_);
lean_dec(v___y_1937_);
lean_dec_ref(v___y_1936_);
lean_dec(v___y_1935_);
lean_dec(v___y_1934_);
lean_dec(v_ref_1932_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1942_, lean_object* v_msg_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1943_, v___y_1946_, v___y_1947_, v___y_1948_, v___y_1949_);
return v___x_1951_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1952_, lean_object* v_msg_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1952_, v_msg_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec(v___y_1954_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_, lean_object* v_a_1965_, lean_object* v_a_1966_, lean_object* v_a_1967_, lean_object* v_a_1968_){
_start:
{
uint8_t v___x_1970_; 
v___x_1970_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1963_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_r_1962_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; 
lean_inc_ref(v_r_1962_);
v___x_1972_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1962_, v_a_1964_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1972_) == 0)
{
lean_object* v_a_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_2090_; 
v_a_1973_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_1975_ = v___x_1972_;
v_isShared_1976_ = v_isSharedCheck_2090_;
goto v_resetjp_1974_;
}
else
{
lean_inc(v_a_1973_);
lean_dec(v___x_1972_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_2090_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v_expr_1977_; lean_object* v___x_1979_; uint8_t v_isShared_1980_; uint8_t v_isSharedCheck_2088_; 
v_expr_1977_ = lean_ctor_get(v_r_1962_, 0);
v_isSharedCheck_2088_ = !lean_is_exclusive(v_r_1962_);
if (v_isSharedCheck_2088_ == 0)
{
lean_object* v_unused_2089_; 
v_unused_2089_ = lean_ctor_get(v_r_1962_, 1);
lean_dec(v_unused_2089_);
v___x_1979_ = v_r_1962_;
v_isShared_1980_ = v_isSharedCheck_2088_;
goto v_resetjp_1978_;
}
else
{
lean_inc(v_expr_1977_);
lean_dec(v_r_1962_);
v___x_1979_ = lean_box(0);
v_isShared_1980_ = v_isSharedCheck_2088_;
goto v_resetjp_1978_;
}
v_resetjp_1978_:
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Expr_isSort(v_a_1973_);
if (v___x_1981_ == 0)
{
lean_object* v___x_1982_; 
lean_del_object(v___x_1975_);
lean_inc(v_a_1968_);
lean_inc_ref(v_a_1967_);
lean_inc(v_a_1966_);
lean_inc_ref(v_a_1965_);
v___x_1982_ = lean_whnf(v_a_1973_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; lean_object* v___x_1985_; uint8_t v_isShared_1986_; uint8_t v_isSharedCheck_2072_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_1985_ = v___x_1982_;
v_isShared_1986_ = v_isSharedCheck_2072_;
goto v_resetjp_1984_;
}
else
{
lean_inc(v_a_1983_);
lean_dec(v___x_1982_);
v___x_1985_ = lean_box(0);
v_isShared_1986_ = v_isSharedCheck_2072_;
goto v_resetjp_1984_;
}
v_resetjp_1984_:
{
if (lean_obj_tag(v_a_1983_) == 3)
{
lean_object* v___x_1987_; lean_object* v_count_1988_; lean_object* v_results_1989_; lean_object* v___x_1991_; uint8_t v_isShared_1992_; uint8_t v_isSharedCheck_2070_; 
v___x_1987_ = lean_st_ref_take(v_a_1964_);
v_count_1988_ = lean_ctor_get(v___x_1987_, 0);
v_results_1989_ = lean_ctor_get(v___x_1987_, 1);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_1987_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_1991_ = v___x_1987_;
v_isShared_1992_ = v_isSharedCheck_2070_;
goto v_resetjp_1990_;
}
else
{
lean_inc(v_results_1989_);
lean_inc(v_count_1988_);
lean_dec(v___x_1987_);
v___x_1991_ = lean_box(0);
v_isShared_1992_ = v_isSharedCheck_2070_;
goto v_resetjp_1990_;
}
v_resetjp_1990_:
{
lean_object* v___x_1993_; lean_object* v___x_1995_; 
v___x_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1993_, 0, v_a_1983_);
lean_inc_ref(v_expr_1977_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_1993_);
v___x_1995_ = v___x_1979_;
goto v_reusejp_1994_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_expr_1977_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_1993_);
v___x_1995_ = v_reuseFailAlloc_2069_;
goto v_reusejp_1994_;
}
v_reusejp_1994_:
{
lean_object* v___y_1997_; lean_object* v___y_2006_; lean_object* v_i_2007_; lean_object* v___y_2013_; lean_object* v___y_2023_; lean_object* v_i_2024_; lean_object* v___x_2039_; 
v___x_2039_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1989_, v_expr_1977_);
switch(lean_obj_tag(v___x_2039_))
{
case 0:
{
lean_object* v_index_2040_; lean_object* v_size_2041_; lean_object* v___x_2042_; 
v_index_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_index_2040_);
lean_dec_ref_known(v___x_2039_, 3);
v_size_2041_ = lean_ctor_get(v_results_1989_, 0);
lean_inc(v_size_2041_);
lean_inc_ref(v___x_1995_);
v___x_2042_ = l_Std_DHashMap_Raw_setEntry___redArg(v_results_1989_, v_size_2041_, v_index_2040_, v_expr_1977_, v___x_1995_);
lean_dec(v_index_2040_);
v___y_1997_ = v___x_2042_;
goto v___jp_1996_;
}
case 1:
{
lean_object* v_index_2043_; lean_object* v_size_2044_; lean_object* v_keyArray_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; uint8_t v___x_2049_; 
v_index_2043_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_index_2043_);
lean_dec_ref_known(v___x_2039_, 1);
v_size_2044_ = lean_ctor_get(v_results_1989_, 0);
v_keyArray_2045_ = lean_ctor_get(v_results_1989_, 1);
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_add(v_size_2044_, v___x_2046_);
v___x_2048_ = lean_array_get_size(v_keyArray_2045_);
v___x_2049_ = lean_nat_dec_lt(v___x_2047_, v___x_2048_);
if (v___x_2049_ == 0)
{
lean_dec(v___x_2047_);
lean_dec(v_index_2043_);
goto v___jp_2029_;
}
else
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2050_ = lean_unsigned_to_nat(4u);
v___x_2051_ = lean_nat_mul(v___x_2047_, v___x_2050_);
v___x_2052_ = lean_unsigned_to_nat(3u);
v___x_2053_ = lean_nat_mul(v___x_2048_, v___x_2052_);
v___x_2054_ = lean_nat_dec_le(v___x_2051_, v___x_2053_);
lean_dec(v___x_2053_);
lean_dec(v___x_2051_);
if (v___x_2054_ == 0)
{
lean_dec(v___x_2047_);
lean_dec(v_index_2043_);
goto v___jp_2029_;
}
else
{
lean_object* v___x_2055_; 
lean_inc_ref(v___x_1995_);
v___x_2055_ = l_Std_DHashMap_Raw_setEntry___redArg(v_results_1989_, v___x_2047_, v_index_2043_, v_expr_1977_, v___x_1995_);
lean_dec(v_index_2043_);
v___y_1997_ = v___x_2055_;
goto v___jp_1996_;
}
}
}
default: 
{
lean_object* v_size_2056_; lean_object* v_keyArray_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; uint8_t v___x_2061_; 
v_size_2056_ = lean_ctor_get(v_results_1989_, 0);
v_keyArray_2057_ = lean_ctor_get(v_results_1989_, 1);
v___x_2058_ = lean_unsigned_to_nat(1u);
v___x_2059_ = lean_nat_add(v_size_2056_, v___x_2058_);
v___x_2060_ = lean_array_get_size(v_keyArray_2057_);
v___x_2061_ = lean_nat_dec_lt(v___x_2059_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; 
lean_dec(v___x_2059_);
v___x_2062_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_1989_);
lean_dec_ref(v_results_1989_);
v___y_2013_ = v___x_2062_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2063_ = lean_unsigned_to_nat(4u);
v___x_2064_ = lean_nat_mul(v___x_2059_, v___x_2063_);
lean_dec(v___x_2059_);
v___x_2065_ = lean_unsigned_to_nat(3u);
v___x_2066_ = lean_nat_mul(v___x_2060_, v___x_2065_);
v___x_2067_ = lean_nat_dec_le(v___x_2064_, v___x_2066_);
lean_dec(v___x_2066_);
lean_dec(v___x_2064_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; 
v___x_2068_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_1989_);
lean_dec_ref(v_results_1989_);
v___y_2013_ = v___x_2068_;
goto v___jp_2012_;
}
else
{
v___y_2013_ = v_results_1989_;
goto v___jp_2012_;
}
}
}
}
v___jp_1996_:
{
lean_object* v___x_1999_; 
if (v_isShared_1992_ == 0)
{
lean_ctor_set(v___x_1991_, 1, v___y_1997_);
v___x_1999_ = v___x_1991_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_count_1988_);
lean_ctor_set(v_reuseFailAlloc_2004_, 1, v___y_1997_);
v___x_1999_ = v_reuseFailAlloc_2004_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_st_ref_put(v_a_1964_, v___x_1999_);
if (v_isShared_1986_ == 0)
{
lean_ctor_set(v___x_1985_, 0, v___x_1995_);
v___x_2002_ = v___x_1985_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v___x_1995_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
v___jp_2005_:
{
lean_object* v_size_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v_size_2008_ = lean_ctor_get(v___y_2006_, 0);
v___x_2009_ = lean_unsigned_to_nat(1u);
v___x_2010_ = lean_nat_add(v_size_2008_, v___x_2009_);
lean_inc_ref(v___x_1995_);
v___x_2011_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2006_, v___x_2010_, v_i_2007_, v_expr_1977_, v___x_1995_);
lean_dec(v_i_2007_);
v___y_1997_ = v___x_2011_;
goto v___jp_1996_;
}
v___jp_2012_:
{
lean_object* v___x_2014_; 
v___x_2014_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v___y_2013_, v_expr_1977_);
switch(lean_obj_tag(v___x_2014_))
{
case 0:
{
lean_object* v_index_2015_; lean_object* v_size_2016_; lean_object* v___x_2017_; 
v_index_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_index_2015_);
lean_dec_ref_known(v___x_2014_, 3);
v_size_2016_ = lean_ctor_get(v___y_2013_, 0);
lean_inc(v_size_2016_);
lean_inc_ref(v___x_1995_);
v___x_2017_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2013_, v_size_2016_, v_index_2015_, v_expr_1977_, v___x_1995_);
lean_dec(v_index_2015_);
v___y_1997_ = v___x_2017_;
goto v___jp_1996_;
}
case 1:
{
lean_object* v_index_2018_; 
v_index_2018_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_index_2018_);
lean_dec_ref_known(v___x_2014_, 1);
v___y_2006_ = v___y_2013_;
v_i_2007_ = v_index_2018_;
goto v___jp_2005_;
}
default: 
{
lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v___x_2020_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_2013_, v___x_2019_);
if (lean_obj_tag(v___x_2020_) == 0)
{
lean_object* v_index_2021_; 
v_index_2021_ = lean_ctor_get(v___x_2020_, 0);
lean_inc(v_index_2021_);
lean_dec_ref_known(v___x_2020_, 1);
v___y_2006_ = v___y_2013_;
v_i_2007_ = v_index_2021_;
goto v___jp_2005_;
}
else
{
lean_dec_ref(v_expr_1977_);
v___y_1997_ = v___y_2013_;
goto v___jp_1996_;
}
}
}
}
v___jp_2022_:
{
lean_object* v_size_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; 
v_size_2025_ = lean_ctor_get(v___y_2023_, 0);
v___x_2026_ = lean_unsigned_to_nat(1u);
v___x_2027_ = lean_nat_add(v_size_2025_, v___x_2026_);
lean_inc_ref(v___x_1995_);
v___x_2028_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_2023_, v___x_2027_, v_i_2024_, v_expr_1977_, v___x_1995_);
lean_dec(v_i_2024_);
v___y_1997_ = v___x_2028_;
goto v___jp_1996_;
}
v___jp_2029_:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2030_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__1___redArg(v_results_1989_);
lean_dec_ref(v_results_1989_);
v___x_2031_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v___x_2030_, v_expr_1977_);
switch(lean_obj_tag(v___x_2031_))
{
case 0:
{
lean_object* v_index_2032_; lean_object* v_size_2033_; lean_object* v___x_2034_; 
v_index_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_index_2032_);
lean_dec_ref_known(v___x_2031_, 3);
v_size_2033_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_size_2033_);
lean_inc_ref(v___x_1995_);
v___x_2034_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_2030_, v_size_2033_, v_index_2032_, v_expr_1977_, v___x_1995_);
lean_dec(v_index_2032_);
v___y_1997_ = v___x_2034_;
goto v___jp_1996_;
}
case 1:
{
lean_object* v_index_2035_; 
v_index_2035_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_index_2035_);
lean_dec_ref_known(v___x_2031_, 1);
v___y_2023_ = v___x_2030_;
v_i_2024_ = v_index_2035_;
goto v___jp_2022_;
}
default: 
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_unsigned_to_nat(0u);
v___x_2037_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_2030_, v___x_2036_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_index_2038_; 
v_index_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_index_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___y_2023_ = v___x_2030_;
v_i_2024_ = v_index_2038_;
goto v___jp_2022_;
}
else
{
lean_dec_ref(v_expr_1977_);
v___y_1997_ = v___x_2030_;
goto v___jp_1996_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2071_; 
lean_del_object(v___x_1985_);
lean_dec(v_a_1983_);
lean_del_object(v___x_1979_);
v___x_2071_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1977_, v_a_1965_, v_a_1966_, v_a_1967_, v_a_1968_);
return v___x_2071_;
}
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_del_object(v___x_1979_);
lean_dec_ref(v_expr_1977_);
v_a_2073_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_1982_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_1982_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
else
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_a_1973_);
if (v_isShared_1980_ == 0)
{
lean_ctor_set(v___x_1979_, 1, v___x_2081_);
v___x_2083_ = v___x_1979_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2087_; 
v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_expr_1977_);
lean_ctor_set(v_reuseFailAlloc_2087_, 1, v___x_2081_);
v___x_2083_ = v_reuseFailAlloc_2087_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2085_; 
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_2083_);
v___x_2085_ = v___x_1975_;
goto v_reusejp_2084_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2083_);
v___x_2085_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2084_;
}
v_reusejp_2084_:
{
return v___x_2085_;
}
}
}
}
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec_ref(v_r_1962_);
v_a_2091_ = lean_ctor_get(v___x_1972_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_1972_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_1972_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_1972_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_2099_, lean_object* v_a_2100_, lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_, lean_object* v_a_2106_){
_start:
{
lean_object* v_res_2107_; 
v_res_2107_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_2099_, v_a_2100_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_, v_a_2105_);
lean_dec(v_a_2105_);
lean_dec_ref(v_a_2104_);
lean_dec(v_a_2103_);
lean_dec_ref(v_a_2102_);
lean_dec(v_a_2101_);
lean_dec(v_a_2100_);
return v_res_2107_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_2108_){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2109_ = l_Lean_instInhabitedExpr;
v___x_2110_ = lean_panic_fn_borrowed(v___x_2109_, v_msg_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2114_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_2115_ = lean_unsigned_to_nat(18u);
v___x_2116_ = lean_unsigned_to_nat(1847u);
v___x_2117_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_2118_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2119_ = l_mkPanicMessageWithDecl(v___x_2118_, v___x_2117_, v___x_2116_, v___x_2115_, v___x_2114_);
return v___x_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_2120_, lean_object* v_f_2121_, lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v___y_2131_; lean_object* v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; lean_object* v___y_2144_; lean_object* v___y_2145_; lean_object* v___y_2146_; uint8_t v___y_2147_; lean_object* v___y_2150_; lean_object* v_fType_2165_; lean_object* v___y_2166_; lean_object* v___y_2167_; lean_object* v___y_2168_; lean_object* v___y_2169_; lean_object* v___y_2170_; uint8_t v___x_2209_; 
v___x_2209_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2123_);
if (v___x_2209_ == 0)
{
lean_object* v_expr_2210_; lean_object* v_expr_2211_; uint8_t v___y_2213_; 
v_expr_2210_ = lean_ctor_get(v_f_2121_, 0);
lean_inc_ref(v_expr_2210_);
lean_dec_ref(v_f_2121_);
v_expr_2211_ = lean_ctor_get(v_a_2122_, 0);
lean_inc_ref(v_expr_2211_);
lean_dec_ref(v_a_2122_);
if (lean_obj_tag(v_e_2120_) == 5)
{
lean_object* v_fn_2215_; lean_object* v_arg_2216_; size_t v___x_2217_; size_t v___x_2218_; uint8_t v___x_2219_; 
v_fn_2215_ = lean_ctor_get(v_e_2120_, 0);
v_arg_2216_ = lean_ctor_get(v_e_2120_, 1);
v___x_2217_ = lean_ptr_addr(v_fn_2215_);
v___x_2218_ = lean_ptr_addr(v_expr_2210_);
v___x_2219_ = lean_usize_dec_eq(v___x_2217_, v___x_2218_);
if (v___x_2219_ == 0)
{
v___y_2213_ = v___x_2219_;
goto v___jp_2212_;
}
else
{
size_t v___x_2220_; size_t v___x_2221_; uint8_t v___x_2222_; 
v___x_2220_ = lean_ptr_addr(v_arg_2216_);
v___x_2221_ = lean_ptr_addr(v_expr_2211_);
v___x_2222_ = lean_usize_dec_eq(v___x_2220_, v___x_2221_);
v___y_2213_ = v___x_2222_;
goto v___jp_2212_;
}
}
else
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_dec_ref(v_expr_2211_);
lean_dec_ref(v_expr_2210_);
lean_dec_ref(v_e_2120_);
v___x_2223_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_2224_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2223_);
v___y_2131_ = v___x_2224_;
goto v___jp_2130_;
}
v___jp_2212_:
{
if (v___y_2213_ == 0)
{
lean_object* v___x_2214_; 
lean_dec_ref(v_e_2120_);
v___x_2214_ = l_Lean_Expr_app___override(v_expr_2210_, v_expr_2211_);
v___y_2131_ = v___x_2214_;
goto v___jp_2130_;
}
else
{
lean_dec_ref(v_expr_2211_);
lean_dec_ref(v_expr_2210_);
v___y_2131_ = v_e_2120_;
goto v___jp_2130_;
}
}
}
else
{
lean_object* v___x_2225_; 
lean_inc_ref(v_f_2121_);
v___x_2225_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_2121_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2225_) == 0)
{
lean_object* v_a_2226_; uint8_t v___x_2227_; 
v_a_2226_ = lean_ctor_get(v___x_2225_, 0);
lean_inc(v_a_2226_);
lean_dec_ref_known(v___x_2225_, 1);
v___x_2227_ = l_Lean_Expr_isForall(v_a_2226_);
if (v___x_2227_ == 0)
{
lean_object* v___x_2228_; 
lean_inc(v_a_2128_);
lean_inc_ref(v_a_2127_);
lean_inc(v_a_2126_);
lean_inc_ref(v_a_2125_);
v___x_2228_ = lean_whnf(v_a_2226_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v_fType_2165_ = v_a_2229_;
v___y_2166_ = v_a_2124_;
v___y_2167_ = v_a_2125_;
v___y_2168_ = v_a_2126_;
v___y_2169_ = v_a_2127_;
v___y_2170_ = v_a_2128_;
goto v___jp_2164_;
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec_ref(v_a_2122_);
lean_dec_ref(v_f_2121_);
lean_dec_ref(v_e_2120_);
v_a_2230_ = lean_ctor_get(v___x_2228_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2228_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2228_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2228_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
v_fType_2165_ = v_a_2226_;
v___y_2166_ = v_a_2124_;
v___y_2167_ = v_a_2125_;
v___y_2168_ = v_a_2126_;
v___y_2169_ = v_a_2127_;
v___y_2170_ = v_a_2128_;
goto v___jp_2164_;
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v_a_2122_);
lean_dec_ref(v_f_2121_);
lean_dec_ref(v_e_2120_);
v_a_2238_ = lean_ctor_get(v___x_2225_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2225_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2225_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2225_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
v___jp_2130_:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_box(0);
v___x_2133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2133_, 0, v___y_2131_);
lean_ctor_set(v___x_2133_, 1, v___x_2132_);
v___x_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2134_, 0, v___x_2133_);
return v___x_2134_;
}
v___jp_2135_:
{
lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2139_ = lean_expr_instantiate1(v___y_2136_, v___y_2137_);
lean_dec_ref(v___y_2137_);
lean_dec_ref(v___y_2136_);
v___x_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2140_, 0, v___x_2139_);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___y_2138_);
lean_ctor_set(v___x_2141_, 1, v___x_2140_);
v___x_2142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
return v___x_2142_;
}
v___jp_2143_:
{
if (v___y_2147_ == 0)
{
lean_object* v___x_2148_; 
lean_dec_ref(v_e_2120_);
lean_inc_ref(v___y_2145_);
v___x_2148_ = l_Lean_Expr_app___override(v___y_2144_, v___y_2145_);
v___y_2136_ = v___y_2146_;
v___y_2137_ = v___y_2145_;
v___y_2138_ = v___x_2148_;
goto v___jp_2135_;
}
else
{
lean_dec_ref(v___y_2144_);
v___y_2136_ = v___y_2146_;
v___y_2137_ = v___y_2145_;
v___y_2138_ = v_e_2120_;
goto v___jp_2135_;
}
}
v___jp_2149_:
{
if (lean_obj_tag(v_e_2120_) == 5)
{
lean_object* v_expr_2151_; lean_object* v_expr_2152_; lean_object* v_fn_2153_; lean_object* v_arg_2154_; size_t v___x_2155_; size_t v___x_2156_; uint8_t v___x_2157_; 
v_expr_2151_ = lean_ctor_get(v_f_2121_, 0);
lean_inc_ref(v_expr_2151_);
lean_dec_ref(v_f_2121_);
v_expr_2152_ = lean_ctor_get(v_a_2122_, 0);
lean_inc_ref(v_expr_2152_);
lean_dec_ref(v_a_2122_);
v_fn_2153_ = lean_ctor_get(v_e_2120_, 0);
v_arg_2154_ = lean_ctor_get(v_e_2120_, 1);
v___x_2155_ = lean_ptr_addr(v_fn_2153_);
v___x_2156_ = lean_ptr_addr(v_expr_2151_);
v___x_2157_ = lean_usize_dec_eq(v___x_2155_, v___x_2156_);
if (v___x_2157_ == 0)
{
v___y_2144_ = v_expr_2151_;
v___y_2145_ = v_expr_2152_;
v___y_2146_ = v___y_2150_;
v___y_2147_ = v___x_2157_;
goto v___jp_2143_;
}
else
{
size_t v___x_2158_; size_t v___x_2159_; uint8_t v___x_2160_; 
v___x_2158_ = lean_ptr_addr(v_arg_2154_);
v___x_2159_ = lean_ptr_addr(v_expr_2152_);
v___x_2160_ = lean_usize_dec_eq(v___x_2158_, v___x_2159_);
v___y_2144_ = v_expr_2151_;
v___y_2145_ = v_expr_2152_;
v___y_2146_ = v___y_2150_;
v___y_2147_ = v___x_2160_;
goto v___jp_2143_;
}
}
else
{
lean_object* v_expr_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
lean_dec_ref(v_f_2121_);
lean_dec_ref(v_e_2120_);
v_expr_2161_ = lean_ctor_get(v_a_2122_, 0);
lean_inc_ref(v_expr_2161_);
lean_dec_ref(v_a_2122_);
v___x_2162_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_2163_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2162_);
v___y_2136_ = v___y_2150_;
v___y_2137_ = v_expr_2161_;
v___y_2138_ = v___x_2163_;
goto v___jp_2135_;
}
}
v___jp_2164_:
{
if (lean_obj_tag(v_fType_2165_) == 7)
{
lean_object* v_binderType_2171_; lean_object* v_body_2172_; lean_object* v___x_2173_; 
v_binderType_2171_ = lean_ctor_get(v_fType_2165_, 1);
lean_inc_ref(v_binderType_2171_);
v_body_2172_ = lean_ctor_get(v_fType_2165_, 2);
lean_inc_ref(v_body_2172_);
lean_dec_ref_known(v_fType_2165_, 3);
lean_inc_ref(v_a_2122_);
v___x_2173_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_2122_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
v___x_2175_ = l_Lean_Meta_isExprDefEq(v_binderType_2171_, v_a_2174_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; uint8_t v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
v___x_2177_ = lean_unbox(v_a_2176_);
lean_dec(v_a_2176_);
if (v___x_2177_ == 0)
{
lean_object* v_expr_2178_; lean_object* v_expr_2179_; lean_object* v___x_2180_; 
v_expr_2178_ = lean_ctor_get(v_f_2121_, 0);
v_expr_2179_ = lean_ctor_get(v_a_2122_, 0);
lean_inc_ref(v_expr_2179_);
lean_inc_ref(v_expr_2178_);
v___x_2180_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_2178_, v_expr_2179_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
if (lean_obj_tag(v___x_2180_) == 0)
{
lean_dec_ref_known(v___x_2180_, 1);
v___y_2150_ = v_body_2172_;
goto v___jp_2149_;
}
else
{
lean_object* v_a_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2188_; 
lean_dec_ref(v_body_2172_);
lean_dec_ref(v_a_2122_);
lean_dec_ref(v_f_2121_);
lean_dec_ref(v_e_2120_);
v_a_2181_ = lean_ctor_get(v___x_2180_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2180_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2183_ = v___x_2180_;
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
else
{
lean_inc(v_a_2181_);
lean_dec(v___x_2180_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2188_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2186_; 
if (v_isShared_2184_ == 0)
{
v___x_2186_ = v___x_2183_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_a_2181_);
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
else
{
v___y_2150_ = v_body_2172_;
goto v___jp_2149_;
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec_ref(v_body_2172_);
lean_dec_ref(v_a_2122_);
lean_dec_ref(v_f_2121_);
lean_dec_ref(v_e_2120_);
v_a_2189_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2175_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2175_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
else
{
lean_object* v_a_2197_; lean_object* v___x_2199_; uint8_t v_isShared_2200_; uint8_t v_isSharedCheck_2204_; 
lean_dec_ref(v_body_2172_);
lean_dec_ref(v_binderType_2171_);
lean_dec_ref(v_a_2122_);
lean_dec_ref(v_f_2121_);
lean_dec_ref(v_e_2120_);
v_a_2197_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2199_ = v___x_2173_;
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
else
{
lean_inc(v_a_2197_);
lean_dec(v___x_2173_);
v___x_2199_ = lean_box(0);
v_isShared_2200_ = v_isSharedCheck_2204_;
goto v_resetjp_2198_;
}
v_resetjp_2198_:
{
lean_object* v___x_2202_; 
if (v_isShared_2200_ == 0)
{
v___x_2202_ = v___x_2199_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v_a_2197_);
v___x_2202_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
return v___x_2202_;
}
}
}
}
else
{
lean_object* v_expr_2205_; lean_object* v_expr_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
lean_dec_ref(v_fType_2165_);
lean_dec_ref(v_e_2120_);
v_expr_2205_ = lean_ctor_get(v_f_2121_, 0);
lean_inc_ref(v_expr_2205_);
lean_dec_ref(v_f_2121_);
v_expr_2206_ = lean_ctor_get(v_a_2122_, 0);
lean_inc_ref(v_expr_2206_);
lean_dec_ref(v_a_2122_);
v___x_2207_ = l_Lean_Expr_app___override(v_expr_2205_, v_expr_2206_);
v___x_2208_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_2207_, v___y_2167_, v___y_2168_, v___y_2169_, v___y_2170_);
return v___x_2208_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2246_, lean_object* v_f_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_, lean_object* v_a_2252_, lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2246_, v_f_2247_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_, v_a_2252_, v_a_2253_, v_a_2254_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
lean_dec(v_a_2252_);
lean_dec_ref(v_a_2251_);
lean_dec(v_a_2250_);
lean_dec(v_a_2249_);
return v_res_2256_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2259_ = lean_unsigned_to_nat(37u);
v___x_2260_ = lean_unsigned_to_nat(345u);
v___x_2261_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2262_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2263_ = l_mkPanicMessageWithDecl(v___x_2262_, v___x_2261_, v___x_2260_, v___x_2259_, v___x_2258_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2264_, lean_object* v_i_2265_, lean_object* v_a_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_){
_start:
{
lean_object* v_zero_2274_; uint8_t v_isZero_2275_; 
v_zero_2274_ = lean_unsigned_to_nat(0u);
v_isZero_2275_ = lean_nat_dec_eq(v_i_2265_, v_zero_2274_);
if (v_isZero_2275_ == 1)
{
lean_object* v___x_2276_; 
lean_dec(v_i_2265_);
v___x_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2276_, 0, v_a_2266_);
return v___x_2276_;
}
else
{
lean_object* v_one_2277_; lean_object* v_n_2278_; lean_object* v___y_2280_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___y_2289_; lean_object* v___y_2290_; lean_object* v___x_2292_; 
v_one_2277_ = lean_unsigned_to_nat(1u);
v_n_2278_ = lean_nat_sub(v_i_2265_, v_one_2277_);
lean_dec(v_i_2265_);
v___x_2292_ = lean_array_fget_borrowed(v_fvars_2264_, v_n_2278_);
if (lean_obj_tag(v___x_2292_) == 1)
{
lean_object* v_fvarId_2293_; lean_object* v___x_2294_; 
v_fvarId_2293_ = lean_ctor_get(v___x_2292_, 0);
lean_inc(v_fvarId_2293_);
v___x_2294_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2293_, v___y_2269_);
if (lean_obj_tag(v___x_2294_) == 0)
{
lean_object* v_a_2295_; 
v_a_2295_ = lean_ctor_get(v___x_2294_, 0);
lean_inc(v_a_2295_);
lean_dec_ref_known(v___x_2294_, 1);
if (lean_obj_tag(v_a_2295_) == 1)
{
lean_object* v_val_2296_; 
v_val_2296_ = lean_ctor_get(v_a_2295_, 0);
lean_inc(v_val_2296_);
lean_dec_ref_known(v_a_2295_, 1);
if (lean_obj_tag(v_val_2296_) == 0)
{
lean_object* v_userName_2297_; lean_object* v_type_2298_; uint8_t v_bi_2299_; lean_object* v_expr_2300_; lean_object* v_type_x3f_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2322_; 
v_userName_2297_ = lean_ctor_get(v_val_2296_, 2);
lean_inc(v_userName_2297_);
v_type_2298_ = lean_ctor_get(v_val_2296_, 3);
lean_inc_ref(v_type_2298_);
v_bi_2299_ = lean_ctor_get_uint8(v_val_2296_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2296_, 4);
v_expr_2300_ = lean_ctor_get(v_a_2266_, 0);
v_type_x3f_2301_ = lean_ctor_get(v_a_2266_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2266_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2303_ = v_a_2266_;
v_isShared_2304_ = v_isSharedCheck_2322_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_type_x3f_2301_);
lean_inc(v_expr_2300_);
lean_dec(v_a_2266_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2322_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___y_2308_; 
v___x_2305_ = lean_expr_abstract_range(v_type_2298_, v_n_2278_, v_fvars_2264_);
lean_dec_ref(v_type_2298_);
lean_inc_ref(v___x_2305_);
lean_inc(v_userName_2297_);
v___x_2306_ = l_Lean_Expr_lam___override(v_userName_2297_, v___x_2305_, v_expr_2300_, v_bi_2299_);
if (lean_obj_tag(v_type_x3f_2301_) == 0)
{
lean_dec_ref(v___x_2305_);
lean_dec(v_userName_2297_);
v___y_2308_ = v_type_x3f_2301_;
goto v___jp_2307_;
}
else
{
lean_object* v_val_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2321_; 
v_val_2313_ = lean_ctor_get(v_type_x3f_2301_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_type_x3f_2301_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2315_ = v_type_x3f_2301_;
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_val_2313_);
lean_dec(v_type_x3f_2301_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2321_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = l_Lean_Expr_forallE___override(v_userName_2297_, v___x_2305_, v_val_2313_, v_bi_2299_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v___x_2317_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
v___y_2308_ = v___x_2319_;
goto v___jp_2307_;
}
}
}
v___jp_2307_:
{
lean_object* v___x_2310_; 
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 1, v___y_2308_);
lean_ctor_set(v___x_2303_, 0, v___x_2306_);
v___x_2310_ = v___x_2303_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v___x_2306_);
lean_ctor_set(v_reuseFailAlloc_2312_, 1, v___y_2308_);
v___x_2310_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
v_i_2265_ = v_n_2278_;
v_a_2266_ = v___x_2310_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2323_; lean_object* v_type_2324_; lean_object* v_value_2325_; uint8_t v_nondep_2326_; uint8_t v_nondep_2328_; lean_object* v___x_2338_; 
v_userName_2323_ = lean_ctor_get(v_val_2296_, 2);
lean_inc(v_userName_2323_);
v_type_2324_ = lean_ctor_get(v_val_2296_, 3);
lean_inc_ref(v_type_2324_);
v_value_2325_ = lean_ctor_get(v_val_2296_, 4);
lean_inc_ref(v_value_2325_);
v_nondep_2326_ = lean_ctor_get_uint8(v_val_2296_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2296_, 5);
v___x_2338_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2270_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; uint8_t v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = 1;
if (v_nondep_2326_ == 0)
{
uint8_t v___x_2341_; 
v___x_2341_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2293_, v_a_2339_);
lean_dec(v_a_2339_);
if (v___x_2341_ == 0)
{
lean_object* v___x_2342_; 
v___x_2342_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2268_);
lean_dec_ref(v___x_2342_);
v_nondep_2328_ = v___x_2340_;
goto v___jp_2327_;
}
else
{
v_nondep_2328_ = v_nondep_2326_;
goto v___jp_2327_;
}
}
else
{
lean_dec(v_a_2339_);
v_nondep_2328_ = v___x_2340_;
goto v___jp_2327_;
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec_ref(v_value_2325_);
lean_dec_ref(v_type_2324_);
lean_dec(v_userName_2323_);
lean_dec(v_n_2278_);
lean_dec_ref(v_a_2266_);
v_a_2343_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2338_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2338_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
v___jp_2327_:
{
lean_object* v_expr_2329_; lean_object* v_type_x3f_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v_expr_2329_ = lean_ctor_get(v_a_2266_, 0);
lean_inc_ref(v_expr_2329_);
v_type_x3f_2330_ = lean_ctor_get(v_a_2266_, 1);
lean_inc(v_type_x3f_2330_);
lean_dec_ref(v_a_2266_);
v___x_2331_ = lean_expr_abstract_range(v_type_2324_, v_n_2278_, v_fvars_2264_);
lean_dec_ref(v_type_2324_);
v___x_2332_ = lean_expr_abstract_range(v_value_2325_, v_n_2278_, v_fvars_2264_);
lean_dec_ref(v_value_2325_);
lean_inc_ref(v___x_2332_);
lean_inc_ref(v___x_2331_);
lean_inc(v_userName_2323_);
v___x_2333_ = l_Lean_Expr_letE___override(v_userName_2323_, v___x_2331_, v___x_2332_, v_expr_2329_, v_nondep_2328_);
if (lean_obj_tag(v_type_x3f_2330_) == 0)
{
lean_dec_ref(v___x_2332_);
lean_dec_ref(v___x_2331_);
lean_dec(v_userName_2323_);
v___y_2284_ = v___x_2333_;
v___y_2285_ = v_type_x3f_2330_;
goto v___jp_2283_;
}
else
{
lean_object* v_val_2334_; uint8_t v___x_2335_; 
v_val_2334_ = lean_ctor_get(v_type_x3f_2330_, 0);
lean_inc(v_val_2334_);
lean_dec_ref_known(v_type_x3f_2330_, 1);
v___x_2335_ = lean_expr_has_loose_bvar(v_val_2334_, v_zero_2274_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_dec_ref(v___x_2332_);
lean_dec_ref(v___x_2331_);
lean_dec(v_userName_2323_);
v___x_2336_ = lean_expr_lower_loose_bvars(v_val_2334_, v_one_2277_, v_one_2277_);
lean_dec(v_val_2334_);
v___y_2289_ = v___x_2333_;
v___y_2290_ = v___x_2336_;
goto v___jp_2288_;
}
else
{
lean_object* v___x_2337_; 
v___x_2337_ = l_Lean_Expr_letE___override(v_userName_2323_, v___x_2331_, v___x_2332_, v_val_2334_, v_nondep_2328_);
v___y_2289_ = v___x_2333_;
v___y_2290_ = v___x_2337_;
goto v___jp_2288_;
}
}
}
}
}
else
{
lean_object* v___x_2351_; 
lean_dec(v_a_2295_);
lean_dec_ref(v_a_2266_);
lean_inc(v_fvarId_2293_);
v___x_2351_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2293_, v___y_2271_, v___y_2272_);
v___y_2280_ = v___x_2351_;
goto v___jp_2279_;
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v_n_2278_);
lean_dec_ref(v_a_2266_);
v_a_2352_ = lean_ctor_get(v___x_2294_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2294_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2294_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2294_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec_ref(v_a_2266_);
v___x_2360_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2361_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2360_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_, v___y_2272_);
v___y_2280_ = v___x_2361_;
goto v___jp_2279_;
}
v___jp_2279_:
{
if (lean_obj_tag(v___y_2280_) == 0)
{
lean_object* v_a_2281_; 
v_a_2281_ = lean_ctor_get(v___y_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___y_2280_, 1);
v_i_2265_ = v_n_2278_;
v_a_2266_ = v_a_2281_;
goto _start;
}
else
{
lean_dec(v_n_2278_);
return v___y_2280_;
}
}
v___jp_2283_:
{
lean_object* v___x_2286_; 
v___x_2286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2286_, 0, v___y_2284_);
lean_ctor_set(v___x_2286_, 1, v___y_2285_);
v_i_2265_ = v_n_2278_;
v_a_2266_ = v___x_2286_;
goto _start;
}
v___jp_2288_:
{
lean_object* v___x_2291_; 
v___x_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2291_, 0, v___y_2290_);
v___y_2284_ = v___y_2289_;
v___y_2285_ = v___x_2291_;
goto v___jp_2283_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2362_, lean_object* v_i_2363_, lean_object* v_a_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2362_, v_i_2363_, v_a_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec_ref(v___y_2367_);
lean_dec(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v_fvars_2362_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
if (lean_obj_tag(v_a_2373_) == 0)
{
lean_object* v___x_2375_; 
v___x_2375_ = l_List_reverse___redArg(v_a_2374_);
return v___x_2375_;
}
else
{
lean_object* v_head_2376_; lean_object* v_tail_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2386_; 
v_head_2376_ = lean_ctor_get(v_a_2373_, 0);
v_tail_2377_ = lean_ctor_get(v_a_2373_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_a_2373_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2379_ = v_a_2373_;
v_isShared_2380_ = v_isSharedCheck_2386_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_tail_2377_);
lean_inc(v_head_2376_);
lean_dec(v_a_2373_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2386_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2381_ = l_Lean_MessageData_ofExpr(v_head_2376_);
if (v_isShared_2380_ == 0)
{
lean_ctor_set(v___x_2379_, 1, v_a_2374_);
lean_ctor_set(v___x_2379_, 0, v___x_2381_);
v___x_2383_ = v___x_2379_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_a_2374_);
v___x_2383_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
v_a_2373_ = v_tail_2377_;
v_a_2374_ = v___x_2383_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2387_; double v___x_2388_; 
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_float_of_nat(v___x_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2392_, lean_object* v_msg_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_, lean_object* v___y_2397_){
_start:
{
lean_object* v_ref_2399_; lean_object* v___x_2400_; lean_object* v_a_2401_; lean_object* v___x_2403_; uint8_t v_isShared_2404_; uint8_t v_isSharedCheck_2445_; 
v_ref_2399_ = lean_ctor_get(v___y_2396_, 5);
v___x_2400_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2393_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2397_);
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2403_ = v___x_2400_;
v_isShared_2404_ = v_isSharedCheck_2445_;
goto v_resetjp_2402_;
}
else
{
lean_inc(v_a_2401_);
lean_dec(v___x_2400_);
v___x_2403_ = lean_box(0);
v_isShared_2404_ = v_isSharedCheck_2445_;
goto v_resetjp_2402_;
}
v_resetjp_2402_:
{
lean_object* v___x_2405_; lean_object* v_traceState_2406_; lean_object* v_env_2407_; lean_object* v_nextMacroScope_2408_; lean_object* v_ngen_2409_; lean_object* v_auxDeclNGen_2410_; lean_object* v_cache_2411_; lean_object* v_messages_2412_; lean_object* v_infoState_2413_; lean_object* v_snapshotTasks_2414_; lean_object* v___x_2416_; uint8_t v_isShared_2417_; uint8_t v_isSharedCheck_2444_; 
v___x_2405_ = lean_st_ref_take(v___y_2397_);
v_traceState_2406_ = lean_ctor_get(v___x_2405_, 4);
v_env_2407_ = lean_ctor_get(v___x_2405_, 0);
v_nextMacroScope_2408_ = lean_ctor_get(v___x_2405_, 1);
v_ngen_2409_ = lean_ctor_get(v___x_2405_, 2);
v_auxDeclNGen_2410_ = lean_ctor_get(v___x_2405_, 3);
v_cache_2411_ = lean_ctor_get(v___x_2405_, 5);
v_messages_2412_ = lean_ctor_get(v___x_2405_, 6);
v_infoState_2413_ = lean_ctor_get(v___x_2405_, 7);
v_snapshotTasks_2414_ = lean_ctor_get(v___x_2405_, 8);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2416_ = v___x_2405_;
v_isShared_2417_ = v_isSharedCheck_2444_;
goto v_resetjp_2415_;
}
else
{
lean_inc(v_snapshotTasks_2414_);
lean_inc(v_infoState_2413_);
lean_inc(v_messages_2412_);
lean_inc(v_cache_2411_);
lean_inc(v_traceState_2406_);
lean_inc(v_auxDeclNGen_2410_);
lean_inc(v_ngen_2409_);
lean_inc(v_nextMacroScope_2408_);
lean_inc(v_env_2407_);
lean_dec(v___x_2405_);
v___x_2416_ = lean_box(0);
v_isShared_2417_ = v_isSharedCheck_2444_;
goto v_resetjp_2415_;
}
v_resetjp_2415_:
{
uint64_t v_tid_2418_; lean_object* v_traces_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2443_; 
v_tid_2418_ = lean_ctor_get_uint64(v_traceState_2406_, sizeof(void*)*1);
v_traces_2419_ = lean_ctor_get(v_traceState_2406_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v_traceState_2406_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2421_ = v_traceState_2406_;
v_isShared_2422_ = v_isSharedCheck_2443_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_traces_2419_);
lean_dec(v_traceState_2406_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2443_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2423_; double v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2433_; 
v___x_2423_ = lean_box(0);
v___x_2424_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2425_ = 0;
v___x_2426_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2427_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2427_, 0, v_cls_2392_);
lean_ctor_set(v___x_2427_, 1, v___x_2423_);
lean_ctor_set(v___x_2427_, 2, v___x_2426_);
lean_ctor_set_float(v___x_2427_, sizeof(void*)*3, v___x_2424_);
lean_ctor_set_float(v___x_2427_, sizeof(void*)*3 + 8, v___x_2424_);
lean_ctor_set_uint8(v___x_2427_, sizeof(void*)*3 + 16, v___x_2425_);
v___x_2428_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2429_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2427_);
lean_ctor_set(v___x_2429_, 1, v_a_2401_);
lean_ctor_set(v___x_2429_, 2, v___x_2428_);
lean_inc(v_ref_2399_);
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v_ref_2399_);
lean_ctor_set(v___x_2430_, 1, v___x_2429_);
v___x_2431_ = l_Lean_PersistentArray_push___redArg(v_traces_2419_, v___x_2430_);
if (v_isShared_2422_ == 0)
{
lean_ctor_set(v___x_2421_, 0, v___x_2431_);
v___x_2433_ = v___x_2421_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2431_);
lean_ctor_set_uint64(v_reuseFailAlloc_2442_, sizeof(void*)*1, v_tid_2418_);
v___x_2433_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
lean_object* v___x_2435_; 
if (v_isShared_2417_ == 0)
{
lean_ctor_set(v___x_2416_, 4, v___x_2433_);
v___x_2435_ = v___x_2416_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_env_2407_);
lean_ctor_set(v_reuseFailAlloc_2441_, 1, v_nextMacroScope_2408_);
lean_ctor_set(v_reuseFailAlloc_2441_, 2, v_ngen_2409_);
lean_ctor_set(v_reuseFailAlloc_2441_, 3, v_auxDeclNGen_2410_);
lean_ctor_set(v_reuseFailAlloc_2441_, 4, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2441_, 5, v_cache_2411_);
lean_ctor_set(v_reuseFailAlloc_2441_, 6, v_messages_2412_);
lean_ctor_set(v_reuseFailAlloc_2441_, 7, v_infoState_2413_);
lean_ctor_set(v_reuseFailAlloc_2441_, 8, v_snapshotTasks_2414_);
v___x_2435_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2439_; 
v___x_2436_ = lean_st_ref_put(v___y_2397_, v___x_2435_);
v___x_2437_ = lean_box(0);
if (v_isShared_2404_ == 0)
{
lean_ctor_set(v___x_2403_, 0, v___x_2437_);
v___x_2439_ = v___x_2403_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v___x_2437_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2446_, lean_object* v_msg_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_){
_start:
{
lean_object* v_res_2453_; 
v_res_2453_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2446_, v_msg_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_);
lean_dec(v___y_2451_);
lean_dec_ref(v___y_2450_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
return v_res_2453_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_cls_2464_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2465_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2466_ = l_Lean_Name_append(v___x_2465_, v_cls_2464_);
return v___x_2466_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2469_ = l_Lean_stringToMessageData(v___x_2468_);
return v___x_2469_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; 
v___x_2471_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2472_ = l_Lean_stringToMessageData(v___x_2471_);
return v___x_2472_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; 
v___x_2474_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2475_ = l_Lean_stringToMessageData(v___x_2474_);
return v___x_2475_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2480_ = l_Lean_MessageData_ofFormat(v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2481_, lean_object* v_body_2482_, lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v___y_2491_; lean_object* v___y_2492_; lean_object* v___y_2493_; lean_object* v___y_2494_; lean_object* v___y_2495_; lean_object* v___y_2496_; lean_object* v___y_2497_; lean_object* v___y_2498_; lean_object* v___y_2503_; lean_object* v___y_2504_; lean_object* v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v_options_2521_; uint8_t v_hasTrace_2522_; 
v_options_2521_ = lean_ctor_get(v_a_2487_, 2);
v_hasTrace_2522_ = lean_ctor_get_uint8(v_options_2521_, sizeof(void*)*1);
if (v_hasTrace_2522_ == 0)
{
v___y_2503_ = v_a_2483_;
v___y_2504_ = v_a_2484_;
v___y_2505_ = v_a_2485_;
v___y_2506_ = v_a_2486_;
v___y_2507_ = v_a_2487_;
v___y_2508_ = v_a_2488_;
goto v___jp_2502_;
}
else
{
lean_object* v_inheritedTraceOptions_2523_; lean_object* v_cls_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_inheritedTraceOptions_2523_ = lean_ctor_get(v_a_2487_, 13);
v_cls_2524_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2525_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2526_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2523_, v_options_2521_, v___x_2525_);
if (v___x_2526_ == 0)
{
v___y_2503_ = v_a_2483_;
v___y_2504_ = v_a_2484_;
v___y_2505_ = v_a_2485_;
v___y_2506_ = v_a_2486_;
v___y_2507_ = v_a_2487_;
v___y_2508_ = v_a_2488_;
goto v___jp_2502_;
}
else
{
lean_object* v_expr_2527_; lean_object* v_type_x3f_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___y_2541_; 
v_expr_2527_ = lean_ctor_get(v_body_2482_, 0);
v_type_x3f_2528_ = lean_ctor_get(v_body_2482_, 1);
v___x_2529_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2481_);
v___x_2530_ = lean_array_to_list(v_fvars_2481_);
v___x_2531_ = lean_box(0);
v___x_2532_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2530_, v___x_2531_);
v___x_2533_ = l_Lean_MessageData_ofList(v___x_2532_);
v___x_2534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2534_, 0, v___x_2529_);
lean_ctor_set(v___x_2534_, 1, v___x_2533_);
v___x_2535_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2536_, 0, v___x_2534_);
lean_ctor_set(v___x_2536_, 1, v___x_2535_);
lean_inc_ref(v_expr_2527_);
v___x_2537_ = l_Lean_MessageData_ofExpr(v_expr_2527_);
v___x_2538_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2537_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
if (lean_obj_tag(v_type_x3f_2528_) == 0)
{
lean_object* v___x_2554_; 
v___x_2554_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2541_ = v___x_2554_;
goto v___jp_2540_;
}
else
{
lean_object* v_val_2555_; lean_object* v___x_2556_; 
v_val_2555_ = lean_ctor_get(v_type_x3f_2528_, 0);
lean_inc(v_val_2555_);
v___x_2556_ = l_Lean_MessageData_ofExpr(v_val_2555_);
v___y_2541_ = v___x_2556_;
goto v___jp_2540_;
}
v___jp_2540_:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2539_);
lean_ctor_set(v___x_2542_, 1, v___y_2541_);
v___x_2543_ = l_Lean_indentD(v___x_2542_);
v___x_2544_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2544_, 0, v___x_2536_);
lean_ctor_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2524_, v___x_2544_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_dec_ref_known(v___x_2545_, 1);
v___y_2503_ = v_a_2483_;
v___y_2504_ = v_a_2484_;
v___y_2505_ = v_a_2485_;
v___y_2506_ = v_a_2486_;
v___y_2507_ = v_a_2487_;
v___y_2508_ = v_a_2488_;
goto v___jp_2502_;
}
else
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v_body_2482_);
lean_dec_ref(v_fvars_2481_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_a_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
v___jp_2490_:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v___x_2499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___y_2496_);
lean_ctor_set(v___x_2499_, 1, v___y_2498_);
v___x_2500_ = lean_array_get_size(v_fvars_2481_);
v___x_2501_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2481_, v___x_2500_, v___x_2499_, v___y_2495_, v___y_2494_, v___y_2492_, v___y_2491_, v___y_2493_, v___y_2497_);
lean_dec_ref(v_fvars_2481_);
return v___x_2501_;
}
v___jp_2502_:
{
lean_object* v_expr_2509_; lean_object* v_type_x3f_2510_; lean_object* v___x_2511_; 
v_expr_2509_ = lean_ctor_get(v_body_2482_, 0);
lean_inc_ref(v_expr_2509_);
v_type_x3f_2510_ = lean_ctor_get(v_body_2482_, 1);
lean_inc(v_type_x3f_2510_);
lean_dec_ref(v_body_2482_);
v___x_2511_ = lean_expr_abstract(v_expr_2509_, v_fvars_2481_);
lean_dec_ref(v_expr_2509_);
if (lean_obj_tag(v_type_x3f_2510_) == 0)
{
v___y_2491_ = v___y_2506_;
v___y_2492_ = v___y_2505_;
v___y_2493_ = v___y_2507_;
v___y_2494_ = v___y_2504_;
v___y_2495_ = v___y_2503_;
v___y_2496_ = v___x_2511_;
v___y_2497_ = v___y_2508_;
v___y_2498_ = v_type_x3f_2510_;
goto v___jp_2490_;
}
else
{
lean_object* v_val_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2520_; 
v_val_2512_ = lean_ctor_get(v_type_x3f_2510_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_type_x3f_2510_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2514_ = v_type_x3f_2510_;
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_val_2512_);
lean_dec(v_type_x3f_2510_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2520_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2516_; lean_object* v___x_2518_; 
v___x_2516_ = lean_expr_abstract(v_val_2512_, v_fvars_2481_);
lean_dec(v_val_2512_);
if (v_isShared_2515_ == 0)
{
lean_ctor_set(v___x_2514_, 0, v___x_2516_);
v___x_2518_ = v___x_2514_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
v___y_2491_ = v___y_2506_;
v___y_2492_ = v___y_2505_;
v___y_2493_ = v___y_2507_;
v___y_2494_ = v___y_2504_;
v___y_2495_ = v___y_2503_;
v___y_2496_ = v___x_2511_;
v___y_2497_ = v___y_2508_;
v___y_2498_ = v___x_2518_;
goto v___jp_2490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2557_, lean_object* v_body_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2557_, v_body_2558_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_, v_a_2564_);
lean_dec(v_a_2564_);
lean_dec_ref(v_a_2563_);
lean_dec(v_a_2562_);
lean_dec_ref(v_a_2561_);
lean_dec(v_a_2560_);
lean_dec(v_a_2559_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2567_, lean_object* v_n_2568_, lean_object* v_i_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_, lean_object* v___y_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_){
_start:
{
lean_object* v___x_2579_; 
v___x_2579_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2567_, v_i_2569_, v_a_2571_, v___y_2572_, v___y_2573_, v___y_2574_, v___y_2575_, v___y_2576_, v___y_2577_);
return v___x_2579_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2580_, lean_object* v_n_2581_, lean_object* v_i_2582_, lean_object* v_a_2583_, lean_object* v_a_2584_, lean_object* v___y_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_){
_start:
{
lean_object* v_res_2592_; 
v_res_2592_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2580_, v_n_2581_, v_i_2582_, v_a_2583_, v_a_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v_n_2581_);
lean_dec_ref(v_fvars_2580_);
return v_res_2592_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2593_, lean_object* v_msg_2594_, lean_object* v___y_2595_, lean_object* v___y_2596_, lean_object* v___y_2597_, lean_object* v___y_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_){
_start:
{
lean_object* v___x_2602_; 
v___x_2602_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2593_, v_msg_2594_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_);
return v___x_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2603_, lean_object* v_msg_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_, lean_object* v___y_2611_){
_start:
{
lean_object* v_res_2612_; 
v_res_2612_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2603_, v_msg_2604_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v___y_2610_);
lean_dec_ref(v___y_2609_);
lean_dec(v___y_2608_);
lean_dec_ref(v___y_2607_);
lean_dec(v___y_2606_);
lean_dec(v___y_2605_);
return v_res_2612_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2614_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2615_ = l_Lean_stringToMessageData(v___x_2614_);
return v___x_2615_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; 
v___x_2617_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2618_ = l_Lean_stringToMessageData(v___x_2617_);
return v___x_2618_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2619_, lean_object* v_structName_2620_, lean_object* v_idx_2621_, lean_object* v_a_2622_, lean_object* v_00_u03b1_2623_, lean_object* v_x_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_){
_start:
{
lean_object* v_expr_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2647_; 
v_expr_2632_ = lean_ctor_get(v_struct_2619_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v_struct_2619_);
if (v_isSharedCheck_2647_ == 0)
{
lean_object* v_unused_2648_; 
v_unused_2648_ = lean_ctor_get(v_struct_2619_, 1);
lean_dec(v_unused_2648_);
v___x_2634_ = v_struct_2619_;
v_isShared_2635_ = v_isSharedCheck_2647_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_expr_2632_);
lean_dec(v_struct_2619_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2647_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2640_; 
v___x_2636_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2637_ = l_Lean_mkProj(v_structName_2620_, v_idx_2621_, v_expr_2632_);
v___x_2638_ = l_Lean_indentExpr(v___x_2637_);
if (v_isShared_2635_ == 0)
{
lean_ctor_set_tag(v___x_2634_, 7);
lean_ctor_set(v___x_2634_, 1, v___x_2638_);
lean_ctor_set(v___x_2634_, 0, v___x_2636_);
v___x_2640_ = v___x_2634_;
goto v_reusejp_2639_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2646_, 1, v___x_2638_);
v___x_2640_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2639_;
}
v_reusejp_2639_:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; 
v___x_2641_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = l_Lean_indentExpr(v_a_2622_);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2644_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
return v___x_2645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2649_, lean_object* v_structName_2650_, lean_object* v_idx_2651_, lean_object* v_a_2652_, lean_object* v_00_u03b1_2653_, lean_object* v_x_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2649_, v_structName_2650_, v_idx_2651_, v_a_2652_, v_00_u03b1_2653_, v_x_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec(v___y_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; lean_object* v_env_2672_; uint8_t v___x_2673_; lean_object* v___x_2674_; 
v___x_2671_ = lean_st_ref_get(v___y_2669_);
v_env_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc_ref(v_env_2672_);
lean_dec(v___x_2671_);
v___x_2673_ = 0;
lean_inc(v_constName_2663_);
v___x_2674_ = l_Lean_Environment_find_x3f(v_env_2672_, v_constName_2663_, v___x_2673_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v___x_2675_; 
v___x_2675_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2675_;
}
else
{
lean_object* v_val_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_dec(v_constName_2663_);
v_val_2676_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2674_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_val_2676_);
lean_dec(v___x_2674_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set_tag(v___x_2678_, 0);
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_val_2676_);
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
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
lean_dec(v___y_2688_);
lean_dec_ref(v___y_2687_);
lean_dec(v___y_2686_);
lean_dec(v___y_2685_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2693_, lean_object* v_structName_2694_, lean_object* v_idx_2695_, lean_object* v_a_2696_, lean_object* v_00_u03b1_2697_, lean_object* v_x_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_expr_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2721_; 
v_expr_2706_ = lean_ctor_get(v_struct_2693_, 0);
v_isSharedCheck_2721_ = !lean_is_exclusive(v_struct_2693_);
if (v_isSharedCheck_2721_ == 0)
{
lean_object* v_unused_2722_; 
v_unused_2722_ = lean_ctor_get(v_struct_2693_, 1);
lean_dec(v_unused_2722_);
v___x_2708_ = v_struct_2693_;
v_isShared_2709_ = v_isSharedCheck_2721_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_expr_2706_);
lean_dec(v_struct_2693_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2721_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2714_; 
v___x_2710_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2711_ = l_Lean_mkProj(v_structName_2694_, v_idx_2695_, v_expr_2706_);
v___x_2712_ = l_Lean_indentExpr(v___x_2711_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set_tag(v___x_2708_, 7);
lean_ctor_set(v___x_2708_, 1, v___x_2712_);
lean_ctor_set(v___x_2708_, 0, v___x_2710_);
v___x_2714_ = v___x_2708_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2720_; 
v_reuseFailAlloc_2720_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2720_, 0, v___x_2710_);
lean_ctor_set(v_reuseFailAlloc_2720_, 1, v___x_2712_);
v___x_2714_ = v_reuseFailAlloc_2720_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2715_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2716_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2716_, 0, v___x_2714_);
lean_ctor_set(v___x_2716_, 1, v___x_2715_);
v___x_2717_ = l_Lean_indentExpr(v_a_2696_);
v___x_2718_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2718_, 0, v___x_2716_);
lean_ctor_set(v___x_2718_, 1, v___x_2717_);
v___x_2719_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2718_, v___y_2701_, v___y_2702_, v___y_2703_, v___y_2704_);
return v___x_2719_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2723_, lean_object* v_structName_2724_, lean_object* v_idx_2725_, lean_object* v_a_2726_, lean_object* v_00_u03b1_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2723_, v_structName_2724_, v_idx_2725_, v_a_2726_, v_00_u03b1_2727_, v_x_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
lean_dec(v___y_2734_);
lean_dec_ref(v___y_2733_);
lean_dec(v___y_2732_);
lean_dec_ref(v___y_2731_);
lean_dec(v___y_2730_);
lean_dec(v___y_2729_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2737_, lean_object* v_fst_2738_, lean_object* v_struct_2739_, lean_object* v_structName_2740_, uint8_t v_a_2741_, lean_object* v___f_2742_, lean_object* v_snd_2743_, lean_object* v_____r_2744_, lean_object* v_ctorType_2745_, lean_object* v_j_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
if (lean_obj_tag(v_ctorType_2745_) == 7)
{
lean_object* v_binderType_2754_; lean_object* v_body_2755_; lean_object* v___x_2756_; 
lean_dec(v_snd_2743_);
v_binderType_2754_ = lean_ctor_get(v_ctorType_2745_, 1);
lean_inc_ref(v_binderType_2754_);
v_body_2755_ = lean_ctor_get(v_ctorType_2745_, 2);
lean_inc_ref(v_body_2755_);
lean_dec_ref_known(v_ctorType_2745_, 3);
v___x_2756_ = lean_expr_instantiate_rev_range(v_binderType_2754_, v_j_2746_, v_a_2737_, v_fst_2738_);
lean_dec_ref(v_binderType_2754_);
if (v_a_2741_ == 0)
{
lean_dec_ref(v___f_2742_);
goto v___jp_2757_;
}
else
{
lean_object* v___x_2773_; 
lean_inc_ref(v___x_2756_);
v___x_2773_ = l_Lean_Meta_isProp(v___x_2756_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; uint8_t v___x_2775_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = lean_unbox(v_a_2774_);
lean_dec(v_a_2774_);
if (v___x_2775_ == 0)
{
lean_object* v___x_2776_; lean_object* v___x_2777_; 
v___x_2776_ = lean_box(0);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v___y_2748_);
lean_inc(v___y_2747_);
v___x_2777_ = lean_apply_9(v___f_2742_, lean_box(0), v___x_2776_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, lean_box(0));
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_dec_ref_known(v___x_2777_, 1);
goto v___jp_2757_;
}
else
{
lean_object* v_a_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2785_; 
lean_dec_ref(v___x_2756_);
lean_dec_ref(v_body_2755_);
lean_dec(v_structName_2740_);
lean_dec_ref(v_struct_2739_);
lean_dec(v_fst_2738_);
lean_dec(v_a_2737_);
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2780_ = v___x_2777_;
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_a_2778_);
lean_dec(v___x_2777_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2785_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2783_; 
if (v_isShared_2781_ == 0)
{
v___x_2783_ = v___x_2780_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2778_);
v___x_2783_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
return v___x_2783_;
}
}
}
}
else
{
lean_dec_ref(v___f_2742_);
goto v___jp_2757_;
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_dec_ref(v___x_2756_);
lean_dec_ref(v_body_2755_);
lean_dec_ref(v___f_2742_);
lean_dec(v_structName_2740_);
lean_dec_ref(v_struct_2739_);
lean_dec(v_fst_2738_);
lean_dec(v_a_2737_);
v_a_2786_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2773_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2773_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
v___jp_2757_:
{
lean_object* v_expr_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2771_; 
v_expr_2758_ = lean_ctor_get(v_struct_2739_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v_struct_2739_);
if (v_isSharedCheck_2771_ == 0)
{
lean_object* v_unused_2772_; 
v_unused_2772_ = lean_ctor_get(v_struct_2739_, 1);
lean_dec(v_unused_2772_);
v___x_2760_ = v_struct_2739_;
v_isShared_2761_ = v_isSharedCheck_2771_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_expr_2758_);
lean_dec(v_struct_2739_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2771_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2765_; 
v___x_2762_ = l_Lean_Expr_proj___override(v_structName_2740_, v_a_2737_, v_expr_2758_);
v___x_2763_ = lean_array_push(v_fst_2738_, v___x_2762_);
lean_inc(v_j_2746_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 1, v___x_2756_);
lean_ctor_set(v___x_2760_, 0, v_j_2746_);
v___x_2765_ = v___x_2760_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_j_2746_);
lean_ctor_set(v_reuseFailAlloc_2770_, 1, v___x_2756_);
v___x_2765_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2766_, 0, v___x_2763_);
lean_ctor_set(v___x_2766_, 1, v___x_2765_);
v___x_2767_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2767_, 0, v_body_2755_);
lean_ctor_set(v___x_2767_, 1, v___x_2766_);
v___x_2768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2768_, 0, v___x_2767_);
v___x_2769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
return v___x_2769_;
}
}
}
}
else
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
lean_dec(v_structName_2740_);
lean_dec_ref(v_struct_2739_);
lean_dec(v_a_2737_);
v___x_2794_ = lean_box(0);
lean_inc(v___y_2752_);
lean_inc_ref(v___y_2751_);
lean_inc(v___y_2750_);
lean_inc_ref(v___y_2749_);
lean_inc(v___y_2748_);
lean_inc(v___y_2747_);
v___x_2795_ = lean_apply_9(v___f_2742_, lean_box(0), v___x_2794_, v___y_2747_, v___y_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_, lean_box(0));
if (lean_obj_tag(v___x_2795_) == 0)
{
lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2806_; 
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2806_ == 0)
{
lean_object* v_unused_2807_; 
v_unused_2807_ = lean_ctor_get(v___x_2795_, 0);
lean_dec(v_unused_2807_);
v___x_2797_ = v___x_2795_;
v_isShared_2798_ = v_isSharedCheck_2806_;
goto v_resetjp_2796_;
}
else
{
lean_dec(v___x_2795_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2806_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2804_; 
lean_inc(v_j_2746_);
v___x_2799_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2799_, 0, v_j_2746_);
lean_ctor_set(v___x_2799_, 1, v_snd_2743_);
v___x_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2800_, 0, v_fst_2738_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v_ctorType_2745_);
lean_ctor_set(v___x_2801_, 1, v___x_2800_);
v___x_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2801_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 0, v___x_2802_);
v___x_2804_ = v___x_2797_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2802_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec_ref(v_ctorType_2745_);
lean_dec(v_snd_2743_);
lean_dec(v_fst_2738_);
v_a_2808_ = lean_ctor_get(v___x_2795_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2795_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2795_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2795_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2816_ = _args[0];
lean_object* v_fst_2817_ = _args[1];
lean_object* v_struct_2818_ = _args[2];
lean_object* v_structName_2819_ = _args[3];
lean_object* v_a_2820_ = _args[4];
lean_object* v___f_2821_ = _args[5];
lean_object* v_snd_2822_ = _args[6];
lean_object* v_____r_2823_ = _args[7];
lean_object* v_ctorType_2824_ = _args[8];
lean_object* v_j_2825_ = _args[9];
lean_object* v___y_2826_ = _args[10];
lean_object* v___y_2827_ = _args[11];
lean_object* v___y_2828_ = _args[12];
lean_object* v___y_2829_ = _args[13];
lean_object* v___y_2830_ = _args[14];
lean_object* v___y_2831_ = _args[15];
lean_object* v___y_2832_ = _args[16];
_start:
{
uint8_t v_a_23462__boxed_2833_; lean_object* v_res_2834_; 
v_a_23462__boxed_2833_ = lean_unbox(v_a_2820_);
v_res_2834_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2816_, v_fst_2817_, v_struct_2818_, v_structName_2819_, v_a_23462__boxed_2833_, v___f_2821_, v_snd_2822_, v_____r_2823_, v_ctorType_2824_, v_j_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec(v_j_2825_);
return v_res_2834_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2835_, lean_object* v_struct_2836_, lean_object* v_structName_2837_, uint8_t v_a_2838_, lean_object* v_idx_2839_, lean_object* v_a_2840_, lean_object* v_a_2841_, lean_object* v_b_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___y_2851_; uint8_t v___x_2873_; 
v___x_2873_ = lean_nat_dec_le(v_a_2841_, v_upperBound_2835_);
if (v___x_2873_ == 0)
{
lean_object* v___x_2874_; 
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_idx_2839_);
lean_dec(v_structName_2837_);
lean_dec_ref(v_struct_2836_);
v___x_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2874_, 0, v_b_2842_);
return v___x_2874_;
}
else
{
lean_object* v_snd_2875_; lean_object* v_snd_2876_; lean_object* v_fst_2877_; lean_object* v_fst_2878_; lean_object* v_fst_2879_; lean_object* v_snd_2880_; lean_object* v___f_2881_; uint8_t v___x_2882_; 
v_snd_2875_ = lean_ctor_get(v_b_2842_, 1);
lean_inc(v_snd_2875_);
v_snd_2876_ = lean_ctor_get(v_snd_2875_, 1);
lean_inc(v_snd_2876_);
v_fst_2877_ = lean_ctor_get(v_b_2842_, 0);
lean_inc(v_fst_2877_);
lean_dec_ref(v_b_2842_);
v_fst_2878_ = lean_ctor_get(v_snd_2875_, 0);
lean_inc(v_fst_2878_);
lean_dec(v_snd_2875_);
v_fst_2879_ = lean_ctor_get(v_snd_2876_, 0);
lean_inc(v_fst_2879_);
v_snd_2880_ = lean_ctor_get(v_snd_2876_, 1);
lean_inc(v_snd_2880_);
lean_dec(v_snd_2876_);
lean_inc_ref(v_a_2840_);
lean_inc(v_idx_2839_);
lean_inc(v_structName_2837_);
lean_inc_ref(v_struct_2836_);
v___f_2881_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2881_, 0, v_struct_2836_);
lean_closure_set(v___f_2881_, 1, v_structName_2837_);
lean_closure_set(v___f_2881_, 2, v_idx_2839_);
lean_closure_set(v___f_2881_, 3, v_a_2840_);
v___x_2882_ = l_Lean_Expr_isForall(v_fst_2877_);
if (v___x_2882_ == 0)
{
lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2883_ = lean_expr_instantiate_rev_range(v_fst_2877_, v_fst_2879_, v_a_2841_, v_fst_2878_);
lean_dec(v_fst_2879_);
lean_dec(v_fst_2877_);
lean_inc(v___y_2848_);
lean_inc_ref(v___y_2847_);
lean_inc(v___y_2846_);
lean_inc_ref(v___y_2845_);
v___x_2884_ = lean_whnf(v___x_2883_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
if (lean_obj_tag(v___x_2884_) == 0)
{
lean_object* v_a_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v_a_2885_ = lean_ctor_get(v___x_2884_, 0);
lean_inc(v_a_2885_);
lean_dec_ref_known(v___x_2884_, 1);
v___x_2886_ = lean_box(0);
lean_inc(v_structName_2837_);
lean_inc_ref(v_struct_2836_);
lean_inc(v_a_2841_);
v___x_2887_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2841_, v_fst_2878_, v_struct_2836_, v_structName_2837_, v_a_2838_, v___f_2881_, v_snd_2880_, v___x_2886_, v_a_2885_, v_a_2841_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
v___y_2851_ = v___x_2887_;
goto v___jp_2850_;
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___f_2881_);
lean_dec(v_snd_2880_);
lean_dec(v_fst_2878_);
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_idx_2839_);
lean_dec(v_structName_2837_);
lean_dec_ref(v_struct_2836_);
v_a_2888_ = lean_ctor_get(v___x_2884_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2884_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2884_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2884_);
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
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2896_ = lean_box(0);
lean_inc(v_structName_2837_);
lean_inc_ref(v_struct_2836_);
lean_inc(v_a_2841_);
v___x_2897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2841_, v_fst_2878_, v_struct_2836_, v_structName_2837_, v_a_2838_, v___f_2881_, v_snd_2880_, v___x_2896_, v_fst_2877_, v_fst_2879_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_);
lean_dec(v_fst_2879_);
v___y_2851_ = v___x_2897_;
goto v___jp_2850_;
}
}
v___jp_2850_:
{
if (lean_obj_tag(v___y_2851_) == 0)
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2864_; 
v_a_2852_ = lean_ctor_get(v___y_2851_, 0);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___y_2851_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2854_ = v___y_2851_;
v_isShared_2855_ = v_isSharedCheck_2864_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___y_2851_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2864_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
if (lean_obj_tag(v_a_2852_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2858_; 
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_idx_2839_);
lean_dec(v_structName_2837_);
lean_dec_ref(v_struct_2836_);
v_a_2856_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v_a_2852_, 1);
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 0, v_a_2856_);
v___x_2858_ = v___x_2854_;
goto v_reusejp_2857_;
}
else
{
lean_object* v_reuseFailAlloc_2859_; 
v_reuseFailAlloc_2859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2856_);
v___x_2858_ = v_reuseFailAlloc_2859_;
goto v_reusejp_2857_;
}
v_reusejp_2857_:
{
return v___x_2858_;
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_del_object(v___x_2854_);
v_a_2860_ = lean_ctor_get(v_a_2852_, 0);
lean_inc(v_a_2860_);
lean_dec_ref_known(v_a_2852_, 1);
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_add(v_a_2841_, v___x_2861_);
lean_dec(v_a_2841_);
v_a_2841_ = v___x_2862_;
v_b_2842_ = v_a_2860_;
goto _start;
}
}
}
else
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
lean_dec(v_a_2841_);
lean_dec_ref(v_a_2840_);
lean_dec(v_idx_2839_);
lean_dec(v_structName_2837_);
lean_dec_ref(v_struct_2836_);
v_a_2865_ = lean_ctor_get(v___y_2851_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___y_2851_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___y_2851_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___y_2851_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2898_, lean_object* v_struct_2899_, lean_object* v_structName_2900_, lean_object* v_a_2901_, lean_object* v_idx_2902_, lean_object* v_a_2903_, lean_object* v_a_2904_, lean_object* v_b_2905_, lean_object* v___y_2906_, lean_object* v___y_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_){
_start:
{
uint8_t v_a_23619__boxed_2913_; lean_object* v_res_2914_; 
v_a_23619__boxed_2913_ = lean_unbox(v_a_2901_);
v_res_2914_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2898_, v_struct_2899_, v_structName_2900_, v_a_23619__boxed_2913_, v_idx_2902_, v_a_2903_, v_a_2904_, v_b_2905_, v___y_2906_, v___y_2907_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
lean_dec(v___y_2909_);
lean_dec_ref(v___y_2908_);
lean_dec(v___y_2907_);
lean_dec(v___y_2906_);
lean_dec(v_upperBound_2898_);
return v_res_2914_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2917_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2918_ = lean_unsigned_to_nat(18u);
v___x_2919_ = lean_unsigned_to_nat(1896u);
v___x_2920_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2921_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2922_ = l_mkPanicMessageWithDecl(v___x_2921_, v___x_2920_, v___x_2919_, v___x_2918_, v___x_2917_);
return v___x_2922_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2924_ = lean_unsigned_to_nat(0u);
v___x_2925_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
lean_ctor_set(v___x_2925_, 1, v___x_2923_);
return v___x_2925_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2926_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2927_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
lean_ctor_set(v___x_2928_, 1, v___x_2926_);
return v___x_2928_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2929_; lean_object* v_dummy_2930_; 
v___x_2929_ = lean_box(0);
v_dummy_2930_ = l_Lean_Expr_sort___override(v___x_2929_);
return v_dummy_2930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2931_, lean_object* v_structName_2932_, lean_object* v_idx_2933_, lean_object* v_struct_2934_, lean_object* v_a_2935_, lean_object* v_a_2936_, lean_object* v_a_2937_, lean_object* v_a_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2949_; uint8_t v___x_2953_; 
v___x_2953_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2935_);
if (v___x_2953_ == 0)
{
lean_dec(v_idx_2933_);
lean_dec(v_structName_2932_);
if (lean_obj_tag(v_e_2931_) == 11)
{
lean_object* v_expr_2954_; lean_object* v_typeName_2955_; lean_object* v_idx_2956_; lean_object* v_struct_2957_; size_t v___x_2958_; size_t v___x_2959_; uint8_t v___x_2960_; 
v_expr_2954_ = lean_ctor_get(v_struct_2934_, 0);
lean_inc_ref(v_expr_2954_);
lean_dec_ref(v_struct_2934_);
v_typeName_2955_ = lean_ctor_get(v_e_2931_, 0);
v_idx_2956_ = lean_ctor_get(v_e_2931_, 1);
v_struct_2957_ = lean_ctor_get(v_e_2931_, 2);
v___x_2958_ = lean_ptr_addr(v_struct_2957_);
v___x_2959_ = lean_ptr_addr(v_expr_2954_);
v___x_2960_ = lean_usize_dec_eq(v___x_2958_, v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_inc(v_idx_2956_);
lean_inc(v_typeName_2955_);
lean_dec_ref_known(v_e_2931_, 3);
v___x_2961_ = l_Lean_Expr_proj___override(v_typeName_2955_, v_idx_2956_, v_expr_2954_);
v___y_2949_ = v___x_2961_;
goto v___jp_2948_;
}
else
{
lean_dec_ref(v_expr_2954_);
v___y_2949_ = v_e_2931_;
goto v___jp_2948_;
}
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
lean_dec_ref(v_struct_2934_);
lean_dec_ref(v_e_2931_);
v___x_2962_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2963_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2962_);
v___y_2949_ = v___x_2963_;
goto v___jp_2948_;
}
}
else
{
lean_object* v___x_2964_; 
lean_inc_ref(v_struct_2934_);
v___x_2964_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2934_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v_a_2965_; lean_object* v___x_2966_; 
v_a_2965_ = lean_ctor_get(v___x_2964_, 0);
lean_inc(v_a_2965_);
lean_dec_ref_known(v___x_2964_, 1);
lean_inc(v_a_2940_);
lean_inc_ref(v_a_2939_);
lean_inc(v_a_2938_);
lean_inc_ref(v_a_2937_);
v___x_2966_ = lean_whnf(v_a_2965_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc_n(v_a_2967_, 2);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = l_Lean_Meta_isProp(v_a_2967_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = l_Lean_Expr_getAppFn(v_a_2967_);
if (lean_obj_tag(v___x_2970_) == 4)
{
lean_object* v_declName_2971_; lean_object* v_us_2972_; lean_object* v___x_2973_; lean_object* v_env_2977_; uint8_t v___x_2978_; lean_object* v___x_2979_; 
v_declName_2971_ = lean_ctor_get(v___x_2970_, 0);
lean_inc(v_declName_2971_);
v_us_2972_ = lean_ctor_get(v___x_2970_, 1);
lean_inc(v_us_2972_);
lean_dec_ref_known(v___x_2970_, 2);
v___x_2973_ = lean_st_ref_get(v_a_2940_);
v_env_2977_ = lean_ctor_get(v___x_2973_, 0);
lean_inc_ref(v_env_2977_);
lean_dec(v___x_2973_);
v___x_2978_ = 0;
v___x_2979_ = l_Lean_Environment_find_x3f(v_env_2977_, v_declName_2971_, v___x_2978_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
v___x_2980_ = lean_box(0);
v___x_2981_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2934_, v_structName_2932_, v_idx_2933_, v_a_2967_, lean_box(0), v___x_2980_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2981_;
}
else
{
lean_object* v_val_2982_; 
v_val_2982_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_val_2982_);
lean_dec_ref_known(v___x_2979_, 1);
if (lean_obj_tag(v_val_2982_) == 5)
{
lean_object* v_val_2983_; lean_object* v_ctors_2984_; 
v_val_2983_ = lean_ctor_get(v_val_2982_, 0);
lean_inc_ref(v_val_2983_);
lean_dec_ref_known(v_val_2982_, 1);
v_ctors_2984_ = lean_ctor_get(v_val_2983_, 4);
lean_inc(v_ctors_2984_);
if (lean_obj_tag(v_ctors_2984_) == 1)
{
lean_object* v_tail_2985_; 
v_tail_2985_ = lean_ctor_get(v_ctors_2984_, 1);
if (lean_obj_tag(v_tail_2985_) == 0)
{
lean_object* v_toConstantVal_2986_; lean_object* v_numParams_2987_; lean_object* v_numIndices_2988_; lean_object* v_head_2989_; lean_object* v___x_2991_; uint8_t v_isShared_2992_; uint8_t v_isSharedCheck_3098_; 
v_toConstantVal_2986_ = lean_ctor_get(v_val_2983_, 0);
lean_inc_ref(v_toConstantVal_2986_);
v_numParams_2987_ = lean_ctor_get(v_val_2983_, 1);
lean_inc(v_numParams_2987_);
v_numIndices_2988_ = lean_ctor_get(v_val_2983_, 2);
lean_inc(v_numIndices_2988_);
lean_dec_ref(v_val_2983_);
v_head_2989_ = lean_ctor_get(v_ctors_2984_, 0);
v_isSharedCheck_3098_ = !lean_is_exclusive(v_ctors_2984_);
if (v_isSharedCheck_3098_ == 0)
{
lean_object* v_unused_3099_; 
v_unused_3099_ = lean_ctor_get(v_ctors_2984_, 1);
lean_dec(v_unused_3099_);
v___x_2991_ = v_ctors_2984_;
v_isShared_2992_ = v_isSharedCheck_3098_;
goto v_resetjp_2990_;
}
else
{
lean_inc(v_head_2989_);
lean_dec(v_ctors_2984_);
v___x_2991_ = lean_box(0);
v_isShared_2992_ = v_isSharedCheck_3098_;
goto v_resetjp_2990_;
}
v_resetjp_2990_:
{
lean_object* v___x_2993_; 
v___x_2993_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2989_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
if (lean_obj_tag(v___x_2993_) == 0)
{
lean_object* v_a_2994_; 
v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
lean_inc(v_a_2994_);
lean_dec_ref_known(v___x_2993_, 1);
if (lean_obj_tag(v_a_2994_) == 6)
{
lean_object* v_val_2995_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v___y_3055_; lean_object* v___y_3056_; lean_object* v_name_3076_; uint8_t v___x_3077_; 
v_val_2995_ = lean_ctor_get(v_a_2994_, 0);
lean_inc_ref(v_val_2995_);
lean_dec_ref_known(v_a_2994_, 1);
v_name_3076_ = lean_ctor_get(v_toConstantVal_2986_, 0);
lean_inc(v_name_3076_);
lean_dec_ref(v_toConstantVal_2986_);
v___x_3077_ = lean_name_eq(v_name_3076_, v_structName_2932_);
lean_dec(v_name_3076_);
if (v___x_3077_ == 0)
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v_a_3080_; lean_object* v___x_3082_; uint8_t v_isShared_3083_; uint8_t v_isSharedCheck_3087_; 
lean_dec_ref(v_val_2995_);
lean_del_object(v___x_2991_);
lean_dec(v_numIndices_2988_);
lean_dec(v_numParams_2987_);
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
v___x_3078_ = lean_box(0);
v___x_3079_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2934_, v_structName_2932_, v_idx_2933_, v_a_2967_, lean_box(0), v___x_3078_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
v_a_3080_ = lean_ctor_get(v___x_3079_, 0);
v_isSharedCheck_3087_ = !lean_is_exclusive(v___x_3079_);
if (v_isSharedCheck_3087_ == 0)
{
v___x_3082_ = v___x_3079_;
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
else
{
lean_inc(v_a_3080_);
lean_dec(v___x_3079_);
v___x_3082_ = lean_box(0);
v_isShared_3083_ = v_isSharedCheck_3087_;
goto v_resetjp_3081_;
}
v_resetjp_3081_:
{
lean_object* v___x_3085_; 
if (v_isShared_3083_ == 0)
{
v___x_3085_ = v___x_3082_;
goto v_reusejp_3084_;
}
else
{
lean_object* v_reuseFailAlloc_3086_; 
v_reuseFailAlloc_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3086_, 0, v_a_3080_);
v___x_3085_ = v_reuseFailAlloc_3086_;
goto v_reusejp_3084_;
}
v_reusejp_3084_:
{
return v___x_3085_;
}
}
}
else
{
v___y_3051_ = v_a_2935_;
v___y_3052_ = v_a_2936_;
v___y_3053_ = v_a_2937_;
v___y_3054_ = v_a_2938_;
v___y_3055_ = v_a_2939_;
v___y_3056_ = v_a_2940_;
goto v___jp_3050_;
}
v___jp_2996_:
{
lean_object* v_toConstantVal_3004_; lean_object* v_name_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v_toConstantVal_3004_ = lean_ctor_get(v_val_2995_, 0);
lean_inc_ref(v_toConstantVal_3004_);
lean_dec_ref(v_val_2995_);
v_name_3005_ = lean_ctor_get(v_toConstantVal_3004_, 0);
lean_inc(v_name_3005_);
lean_dec_ref(v_toConstantVal_3004_);
v___x_3006_ = l_Lean_mkConst(v_name_3005_, v_us_2972_);
v___x_3007_ = lean_unsigned_to_nat(0u);
v___x_3008_ = l_Array_toSubarray___redArg(v___y_2997_, v___x_3007_, v_numParams_2987_);
v___x_3009_ = l_Subarray_copy___redArg(v___x_3008_);
v___x_3010_ = l_Lean_mkAppN(v___x_3006_, v___x_3009_);
lean_dec_ref(v___x_3009_);
lean_inc(v___y_3003_);
lean_inc_ref(v___y_3002_);
lean_inc(v___y_3001_);
lean_inc_ref(v___y_3000_);
v___x_3011_ = lean_infer_type(v___x_3010_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3013_; lean_object* v___x_3015_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
lean_inc(v_a_3012_);
lean_dec_ref_known(v___x_3011_, 1);
v___x_3013_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2992_ == 0)
{
lean_ctor_set_tag(v___x_2991_, 0);
lean_ctor_set(v___x_2991_, 1, v___x_3013_);
lean_ctor_set(v___x_2991_, 0, v_a_3012_);
v___x_3015_ = v___x_2991_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3012_);
lean_ctor_set(v_reuseFailAlloc_3041_, 1, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
uint8_t v___x_3016_; lean_object* v___x_3017_; 
v___x_3016_ = lean_unbox(v_a_2969_);
lean_dec(v_a_2969_);
lean_inc_ref(v_struct_2934_);
lean_inc(v_idx_2933_);
v___x_3017_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2933_, v_struct_2934_, v_structName_2932_, v___x_3016_, v_idx_2933_, v_a_2967_, v___x_3007_, v___x_3015_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_, v___y_3002_, v___y_3003_);
lean_dec(v_idx_2933_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_snd_3019_; lean_object* v_snd_3020_; lean_object* v_snd_3021_; lean_object* v_expr_3022_; lean_object* v___x_3023_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v_snd_3019_ = lean_ctor_get(v_a_3018_, 1);
lean_inc(v_snd_3019_);
lean_dec(v_a_3018_);
v_snd_3020_ = lean_ctor_get(v_snd_3019_, 1);
lean_inc(v_snd_3020_);
lean_dec(v_snd_3019_);
v_snd_3021_ = lean_ctor_get(v_snd_3020_, 1);
lean_inc(v_snd_3021_);
lean_dec(v_snd_3020_);
v_expr_3022_ = lean_ctor_get(v_struct_2934_, 0);
lean_inc_ref(v_expr_3022_);
lean_dec_ref(v_struct_2934_);
v___x_3023_ = l_Lean_Expr_cleanupAnnotations(v_snd_3021_);
if (lean_obj_tag(v_e_2931_) == 11)
{
lean_object* v_typeName_3024_; lean_object* v_idx_3025_; lean_object* v_struct_3026_; size_t v___x_3027_; size_t v___x_3028_; uint8_t v___x_3029_; 
v_typeName_3024_ = lean_ctor_get(v_e_2931_, 0);
v_idx_3025_ = lean_ctor_get(v_e_2931_, 1);
v_struct_3026_ = lean_ctor_get(v_e_2931_, 2);
v___x_3027_ = lean_ptr_addr(v_struct_3026_);
v___x_3028_ = lean_ptr_addr(v_expr_3022_);
v___x_3029_ = lean_usize_dec_eq(v___x_3027_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; 
lean_inc(v_idx_3025_);
lean_inc(v_typeName_3024_);
lean_dec_ref_known(v_e_2931_, 3);
v___x_3030_ = l_Lean_Expr_proj___override(v_typeName_3024_, v_idx_3025_, v_expr_3022_);
v___y_2943_ = v___x_3023_;
v___y_2944_ = v___x_3030_;
goto v___jp_2942_;
}
else
{
lean_dec_ref(v_expr_3022_);
v___y_2943_ = v___x_3023_;
v___y_2944_ = v_e_2931_;
goto v___jp_2942_;
}
}
else
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
lean_dec_ref(v_expr_3022_);
lean_dec_ref(v_e_2931_);
v___x_3031_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_3032_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3031_);
v___y_2943_ = v___x_3023_;
v___y_2944_ = v___x_3032_;
goto v___jp_2942_;
}
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v_struct_2934_);
lean_dec_ref(v_e_2931_);
v_a_3033_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3017_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3017_);
v___x_3035_ = lean_box(0);
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
v_resetjp_3034_:
{
lean_object* v___x_3038_; 
if (v_isShared_3036_ == 0)
{
v___x_3038_ = v___x_3035_;
goto v_reusejp_3037_;
}
else
{
lean_object* v_reuseFailAlloc_3039_; 
v_reuseFailAlloc_3039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_a_3033_);
v___x_3038_ = v_reuseFailAlloc_3039_;
goto v_reusejp_3037_;
}
v_reusejp_3037_:
{
return v___x_3038_;
}
}
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_del_object(v___x_2991_);
lean_dec(v_a_2969_);
lean_dec(v_a_2967_);
lean_dec_ref(v_struct_2934_);
lean_dec(v_idx_2933_);
lean_dec(v_structName_2932_);
lean_dec_ref(v_e_2931_);
v_a_3042_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3011_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3011_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
v___jp_3050_:
{
lean_object* v_dummy_3057_; lean_object* v_nargs_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___x_3065_; 
v_dummy_3057_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3058_ = l_Lean_Expr_getAppNumArgs(v_a_2967_);
lean_inc(v_nargs_3058_);
v___x_3059_ = lean_mk_array(v_nargs_3058_, v_dummy_3057_);
v___x_3060_ = lean_unsigned_to_nat(1u);
v___x_3061_ = lean_nat_sub(v_nargs_3058_, v___x_3060_);
lean_dec(v_nargs_3058_);
lean_inc(v_a_2967_);
v___x_3062_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2967_, v___x_3059_, v___x_3061_);
v___x_3063_ = lean_nat_add(v_numParams_2987_, v_numIndices_2988_);
lean_dec(v_numIndices_2988_);
v___x_3064_ = lean_array_get_size(v___x_3062_);
v___x_3065_ = lean_nat_dec_eq(v___x_3063_, v___x_3064_);
lean_dec(v___x_3063_);
if (v___x_3065_ == 0)
{
if (v___x_2953_ == 0)
{
v___y_2997_ = v___x_3062_;
v___y_2998_ = v___y_3051_;
v___y_2999_ = v___y_3052_;
v___y_3000_ = v___y_3053_;
v___y_3001_ = v___y_3054_;
v___y_3002_ = v___y_3055_;
v___y_3003_ = v___y_3056_;
goto v___jp_2996_;
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v_a_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3075_; 
lean_dec_ref(v___x_3062_);
lean_dec_ref(v_val_2995_);
lean_del_object(v___x_2991_);
lean_dec(v_numParams_2987_);
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
v___x_3066_ = lean_box(0);
v___x_3067_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2934_, v_structName_2932_, v_idx_2933_, v_a_2967_, lean_box(0), v___x_3066_, v___y_3051_, v___y_3052_, v___y_3053_, v___y_3054_, v___y_3055_, v___y_3056_);
v_a_3068_ = lean_ctor_get(v___x_3067_, 0);
v_isSharedCheck_3075_ = !lean_is_exclusive(v___x_3067_);
if (v_isSharedCheck_3075_ == 0)
{
v___x_3070_ = v___x_3067_;
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_a_3068_);
lean_dec(v___x_3067_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3075_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___x_3073_; 
if (v_isShared_3071_ == 0)
{
v___x_3073_ = v___x_3070_;
goto v_reusejp_3072_;
}
else
{
lean_object* v_reuseFailAlloc_3074_; 
v_reuseFailAlloc_3074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3074_, 0, v_a_3068_);
v___x_3073_ = v_reuseFailAlloc_3074_;
goto v_reusejp_3072_;
}
v_reusejp_3072_:
{
return v___x_3073_;
}
}
}
}
else
{
v___y_2997_ = v___x_3062_;
v___y_2998_ = v___y_3051_;
v___y_2999_ = v___y_3052_;
v___y_3000_ = v___y_3053_;
v___y_3001_ = v___y_3054_;
v___y_3002_ = v___y_3055_;
v___y_3003_ = v___y_3056_;
goto v___jp_2996_;
}
}
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec(v_a_2994_);
lean_del_object(v___x_2991_);
lean_dec(v_numIndices_2988_);
lean_dec(v_numParams_2987_);
lean_dec_ref(v_toConstantVal_2986_);
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
v___x_3088_ = lean_box(0);
v___x_3089_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2934_, v_structName_2932_, v_idx_2933_, v_a_2967_, lean_box(0), v___x_3088_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_3089_;
}
}
else
{
lean_object* v_a_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3097_; 
lean_del_object(v___x_2991_);
lean_dec(v_numIndices_2988_);
lean_dec(v_numParams_2987_);
lean_dec_ref(v_toConstantVal_2986_);
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec(v_a_2967_);
lean_dec_ref(v_struct_2934_);
lean_dec(v_idx_2933_);
lean_dec(v_structName_2932_);
lean_dec_ref(v_e_2931_);
v_a_3090_ = lean_ctor_get(v___x_2993_, 0);
v_isSharedCheck_3097_ = !lean_is_exclusive(v___x_2993_);
if (v_isSharedCheck_3097_ == 0)
{
v___x_3092_ = v___x_2993_;
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_a_3090_);
lean_dec(v___x_2993_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3097_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3095_; 
if (v_isShared_3093_ == 0)
{
v___x_3095_ = v___x_3092_;
goto v_reusejp_3094_;
}
else
{
lean_object* v_reuseFailAlloc_3096_; 
v_reuseFailAlloc_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3096_, 0, v_a_3090_);
v___x_3095_ = v_reuseFailAlloc_3096_;
goto v_reusejp_3094_;
}
v_reusejp_3094_:
{
return v___x_3095_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2984_, 2);
lean_dec_ref(v_val_2983_);
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
goto v___jp_2974_;
}
}
else
{
lean_dec(v_ctors_2984_);
lean_dec_ref(v_val_2983_);
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
goto v___jp_2974_;
}
}
else
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
lean_dec(v_val_2982_);
lean_dec(v_us_2972_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
v___x_3100_ = lean_box(0);
v___x_3101_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2934_, v_structName_2932_, v_idx_2933_, v_a_2967_, lean_box(0), v___x_3100_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_3101_;
}
}
v___jp_2974_:
{
lean_object* v___x_2975_; lean_object* v___x_2976_; 
v___x_2975_ = lean_box(0);
v___x_2976_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2934_, v_structName_2932_, v_idx_2933_, v_a_2967_, lean_box(0), v___x_2975_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_2976_;
}
}
else
{
lean_object* v___x_3102_; lean_object* v___x_3103_; 
lean_dec_ref(v___x_2970_);
lean_dec(v_a_2969_);
lean_dec_ref(v_e_2931_);
v___x_3102_ = lean_box(0);
v___x_3103_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2934_, v_structName_2932_, v_idx_2933_, v_a_2967_, lean_box(0), v___x_3102_, v_a_2935_, v_a_2936_, v_a_2937_, v_a_2938_, v_a_2939_, v_a_2940_);
return v___x_3103_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec(v_a_2967_);
lean_dec_ref(v_struct_2934_);
lean_dec(v_idx_2933_);
lean_dec(v_structName_2932_);
lean_dec_ref(v_e_2931_);
v_a_3104_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_2968_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_2968_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v_struct_2934_);
lean_dec(v_idx_2933_);
lean_dec(v_structName_2932_);
lean_dec_ref(v_e_2931_);
v_a_3112_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_2966_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_2966_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
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
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_dec_ref(v_struct_2934_);
lean_dec(v_idx_2933_);
lean_dec(v_structName_2932_);
lean_dec_ref(v_e_2931_);
v_a_3120_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_2964_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_2964_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
v___jp_2942_:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2945_, 0, v___y_2943_);
v___x_2946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2946_, 0, v___y_2944_);
lean_ctor_set(v___x_2946_, 1, v___x_2945_);
v___x_2947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2946_);
return v___x_2947_;
}
v___jp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2950_ = lean_box(0);
v___x_2951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___y_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2951_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_3128_, lean_object* v_structName_3129_, lean_object* v_idx_3130_, lean_object* v_struct_3131_, lean_object* v_a_3132_, lean_object* v_a_3133_, lean_object* v_a_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_, lean_object* v_a_3137_, lean_object* v_a_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_3128_, v_structName_3129_, v_idx_3130_, v_struct_3131_, v_a_3132_, v_a_3133_, v_a_3134_, v_a_3135_, v_a_3136_, v_a_3137_);
lean_dec(v_a_3137_);
lean_dec_ref(v_a_3136_);
lean_dec(v_a_3135_);
lean_dec_ref(v_a_3134_);
lean_dec(v_a_3133_);
lean_dec(v_a_3132_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_3140_, lean_object* v_struct_3141_, lean_object* v_structName_3142_, uint8_t v_a_3143_, lean_object* v_idx_3144_, lean_object* v_a_3145_, lean_object* v_inst_3146_, lean_object* v_R_3147_, lean_object* v_a_3148_, lean_object* v_b_3149_, lean_object* v_c_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___x_3158_; 
v___x_3158_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_3140_, v_struct_3141_, v_structName_3142_, v_a_3143_, v_idx_3144_, v_a_3145_, v_a_3148_, v_b_3149_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
return v___x_3158_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_3159_ = _args[0];
lean_object* v_struct_3160_ = _args[1];
lean_object* v_structName_3161_ = _args[2];
lean_object* v_a_3162_ = _args[3];
lean_object* v_idx_3163_ = _args[4];
lean_object* v_a_3164_ = _args[5];
lean_object* v_inst_3165_ = _args[6];
lean_object* v_R_3166_ = _args[7];
lean_object* v_a_3167_ = _args[8];
lean_object* v_b_3168_ = _args[9];
lean_object* v_c_3169_ = _args[10];
lean_object* v___y_3170_ = _args[11];
lean_object* v___y_3171_ = _args[12];
lean_object* v___y_3172_ = _args[13];
lean_object* v___y_3173_ = _args[14];
lean_object* v___y_3174_ = _args[15];
lean_object* v___y_3175_ = _args[16];
lean_object* v___y_3176_ = _args[17];
_start:
{
uint8_t v_a_24143__boxed_3177_; lean_object* v_res_3178_; 
v_a_24143__boxed_3177_ = lean_unbox(v_a_3162_);
v_res_3178_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_3159_, v_struct_3160_, v_structName_3161_, v_a_24143__boxed_3177_, v_idx_3163_, v_a_3164_, v_inst_3165_, v_R_3166_, v_a_3167_, v_b_3168_, v_c_3169_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
lean_dec(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec(v_upperBound_3159_);
return v_res_3178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_3179_, size_t v_i_3180_, size_t v_stop_3181_, lean_object* v_b_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
uint8_t v___x_3189_; 
v___x_3189_ = lean_usize_dec_eq(v_i_3180_, v_stop_3181_);
if (v___x_3189_ == 0)
{
size_t v___x_3190_; size_t v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v___x_3190_ = ((size_t)1ULL);
v___x_3191_ = lean_usize_sub(v_i_3180_, v___x_3190_);
v___x_3192_ = lean_array_uget_borrowed(v_as_3179_, v___x_3191_);
lean_inc(v___x_3192_);
v___x_3193_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_3192_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref_known(v___x_3193_, 1);
v___x_3195_ = l_Lean_Expr_sortLevel_x21(v_a_3194_);
lean_dec(v_a_3194_);
v___x_3196_ = l_Lean_mkLevelIMax_x27(v___x_3195_, v_b_3182_);
v_i_3180_ = v___x_3191_;
v_b_3182_ = v___x_3196_;
goto _start;
}
else
{
lean_object* v_a_3198_; lean_object* v___x_3200_; uint8_t v_isShared_3201_; uint8_t v_isSharedCheck_3205_; 
lean_dec(v_b_3182_);
v_a_3198_ = lean_ctor_get(v___x_3193_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___x_3193_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3200_ = v___x_3193_;
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
else
{
lean_inc(v_a_3198_);
lean_dec(v___x_3193_);
v___x_3200_ = lean_box(0);
v_isShared_3201_ = v_isSharedCheck_3205_;
goto v_resetjp_3199_;
}
v_resetjp_3199_:
{
lean_object* v___x_3203_; 
if (v_isShared_3201_ == 0)
{
v___x_3203_ = v___x_3200_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
}
else
{
lean_object* v___x_3206_; 
v___x_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3206_, 0, v_b_3182_);
return v___x_3206_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_3207_, lean_object* v_i_3208_, lean_object* v_stop_3209_, lean_object* v_b_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_, lean_object* v___y_3215_, lean_object* v___y_3216_){
_start:
{
size_t v_i_boxed_3217_; size_t v_stop_boxed_3218_; lean_object* v_res_3219_; 
v_i_boxed_3217_ = lean_unbox_usize(v_i_3208_);
lean_dec(v_i_3208_);
v_stop_boxed_3218_ = lean_unbox_usize(v_stop_3209_);
lean_dec(v_stop_3209_);
v_res_3219_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3207_, v_i_boxed_3217_, v_stop_boxed_3218_, v_b_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
lean_dec(v___y_3215_);
lean_dec_ref(v___y_3214_);
lean_dec(v___y_3213_);
lean_dec_ref(v___y_3212_);
lean_dec(v___y_3211_);
lean_dec_ref(v_as_3207_);
return v_res_3219_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3223_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_3224_ = lean_unsigned_to_nat(14u);
v___x_3225_ = lean_unsigned_to_nat(22u);
v___x_3226_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_3227_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_3228_ = l_mkPanicMessageWithDecl(v___x_3227_, v___x_3226_, v___x_3225_, v___x_3224_, v___x_3223_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_3229_, lean_object* v_doms_3230_, lean_object* v_body_3231_, lean_object* v_a_3232_, lean_object* v_a_3233_, lean_object* v_a_3234_, lean_object* v_a_3235_, lean_object* v_a_3236_, lean_object* v_a_3237_){
_start:
{
lean_object* v_lctx_3239_; lean_object* v_expr_3240_; uint8_t v___x_3241_; uint8_t v___x_3242_; lean_object* v___x_3243_; lean_object* v_a_3245_; uint8_t v___x_3250_; 
v_lctx_3239_ = lean_ctor_get(v_a_3234_, 2);
v_expr_3240_ = lean_ctor_get(v_body_3231_, 0);
v___x_3241_ = 1;
v___x_3242_ = 0;
lean_inc_ref(v_lctx_3239_);
v___x_3243_ = l_Lean_LocalContext_mkForall(v_lctx_3239_, v_fvars_3229_, v_expr_3240_, v___x_3241_, v___x_3242_);
v___x_3250_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3232_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3259_; 
v_isSharedCheck_3259_ = !lean_is_exclusive(v_body_3231_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; lean_object* v_unused_3261_; 
v_unused_3260_ = lean_ctor_get(v_body_3231_, 1);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_body_3231_, 0);
lean_dec(v_unused_3261_);
v___x_3252_ = v_body_3231_;
v_isShared_3253_ = v_isSharedCheck_3259_;
goto v_resetjp_3251_;
}
else
{
lean_dec(v_body_3231_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3259_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3254_; lean_object* v___x_3256_; 
v___x_3254_ = lean_box(0);
if (v_isShared_3253_ == 0)
{
lean_ctor_set(v___x_3252_, 1, v___x_3254_);
lean_ctor_set(v___x_3252_, 0, v___x_3243_);
v___x_3256_ = v___x_3252_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3258_, 1, v___x_3254_);
v___x_3256_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
lean_object* v___x_3257_; 
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
return v___x_3257_;
}
}
}
else
{
lean_object* v___x_3262_; 
v___x_3262_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_3231_, v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___y_3265_; lean_object* v_type_x3f_3282_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v_type_x3f_3282_ = lean_ctor_get(v_a_3263_, 1);
lean_inc(v_type_x3f_3282_);
lean_dec(v_a_3263_);
if (lean_obj_tag(v_type_x3f_3282_) == 0)
{
lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3283_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3284_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3283_);
v___y_3265_ = v___x_3284_;
goto v___jp_3264_;
}
else
{
lean_object* v_val_3285_; 
v_val_3285_ = lean_ctor_get(v_type_x3f_3282_, 0);
lean_inc(v_val_3285_);
lean_dec_ref_known(v_type_x3f_3282_, 1);
v___y_3265_ = v_val_3285_;
goto v___jp_3264_;
}
v___jp_3264_:
{
lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3266_ = l_Lean_Expr_sortLevel_x21(v___y_3265_);
lean_dec_ref(v___y_3265_);
v___x_3267_ = lean_array_get_size(v_doms_3230_);
v___x_3268_ = lean_unsigned_to_nat(0u);
v___x_3269_ = lean_nat_dec_lt(v___x_3268_, v___x_3267_);
if (v___x_3269_ == 0)
{
v_a_3245_ = v___x_3266_;
goto v___jp_3244_;
}
else
{
size_t v___x_3270_; size_t v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = lean_usize_of_nat(v___x_3267_);
v___x_3271_ = ((size_t)0ULL);
v___x_3272_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_3230_, v___x_3270_, v___x_3271_, v___x_3266_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_);
if (lean_obj_tag(v___x_3272_) == 0)
{
lean_object* v_a_3273_; 
v_a_3273_ = lean_ctor_get(v___x_3272_, 0);
lean_inc(v_a_3273_);
lean_dec_ref_known(v___x_3272_, 1);
v_a_3245_ = v_a_3273_;
goto v___jp_3244_;
}
else
{
lean_object* v_a_3274_; lean_object* v___x_3276_; uint8_t v_isShared_3277_; uint8_t v_isSharedCheck_3281_; 
lean_dec_ref(v___x_3243_);
v_a_3274_ = lean_ctor_get(v___x_3272_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3272_);
if (v_isSharedCheck_3281_ == 0)
{
v___x_3276_ = v___x_3272_;
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
else
{
lean_inc(v_a_3274_);
lean_dec(v___x_3272_);
v___x_3276_ = lean_box(0);
v_isShared_3277_ = v_isSharedCheck_3281_;
goto v_resetjp_3275_;
}
v_resetjp_3275_:
{
lean_object* v___x_3279_; 
if (v_isShared_3277_ == 0)
{
v___x_3279_ = v___x_3276_;
goto v_reusejp_3278_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_a_3274_);
v___x_3279_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3278_;
}
v_reusejp_3278_:
{
return v___x_3279_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3243_);
return v___x_3262_;
}
}
v___jp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v___x_3246_ = l_Lean_Expr_sort___override(v_a_3245_);
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
v___x_3248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3248_, 0, v___x_3243_);
lean_ctor_set(v___x_3248_, 1, v___x_3247_);
v___x_3249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
return v___x_3249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3286_, lean_object* v_doms_3287_, lean_object* v_body_3288_, lean_object* v_a_3289_, lean_object* v_a_3290_, lean_object* v_a_3291_, lean_object* v_a_3292_, lean_object* v_a_3293_, lean_object* v_a_3294_, lean_object* v_a_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3286_, v_doms_3287_, v_body_3288_, v_a_3289_, v_a_3290_, v_a_3291_, v_a_3292_, v_a_3293_, v_a_3294_);
lean_dec(v_a_3294_);
lean_dec_ref(v_a_3293_);
lean_dec(v_a_3292_);
lean_dec_ref(v_a_3291_);
lean_dec(v_a_3290_);
lean_dec(v_a_3289_);
lean_dec_ref(v_doms_3287_);
lean_dec_ref(v_fvars_3286_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3297_, size_t v_i_3298_, size_t v_stop_3299_, lean_object* v_b_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v___x_3308_; 
v___x_3308_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3297_, v_i_3298_, v_stop_3299_, v_b_3300_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3309_, lean_object* v_i_3310_, lean_object* v_stop_3311_, lean_object* v_b_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
size_t v_i_boxed_3320_; size_t v_stop_boxed_3321_; lean_object* v_res_3322_; 
v_i_boxed_3320_ = lean_unbox_usize(v_i_3310_);
lean_dec(v_i_3310_);
v_stop_boxed_3321_ = lean_unbox_usize(v_stop_3311_);
lean_dec(v_stop_3311_);
v_res_3322_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3309_, v_i_boxed_3320_, v_stop_boxed_3321_, v_b_3312_, v___y_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec(v___y_3316_);
lean_dec_ref(v___y_3315_);
lean_dec(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v_as_3309_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3323_){
_start:
{
if (lean_obj_tag(v_x_3323_) == 0)
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
v_a_3325_ = lean_ctor_get(v_x_3323_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v_x_3323_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v_x_3323_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v_x_3323_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
lean_ctor_set_tag(v___x_3327_, 1);
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
else
{
lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3340_; 
v_a_3333_ = lean_ctor_get(v_x_3323_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_x_3323_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3335_ = v_x_3323_;
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v_x_3323_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3340_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
lean_ctor_set_tag(v___x_3335_, 0);
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v_a_3333_);
v___x_3338_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
return v___x_3338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3341_);
return v_res_3343_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3344_, lean_object* v_opt_3345_){
_start:
{
lean_object* v_name_3346_; lean_object* v_defValue_3347_; lean_object* v_map_3348_; lean_object* v___x_3349_; 
v_name_3346_ = lean_ctor_get(v_opt_3345_, 0);
v_defValue_3347_ = lean_ctor_get(v_opt_3345_, 1);
v_map_3348_ = lean_ctor_get(v_opts_3344_, 0);
v___x_3349_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3348_, v_name_3346_);
if (lean_obj_tag(v___x_3349_) == 0)
{
uint8_t v___x_3350_; 
v___x_3350_ = lean_unbox(v_defValue_3347_);
return v___x_3350_;
}
else
{
lean_object* v_val_3351_; 
v_val_3351_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_val_3351_);
lean_dec_ref_known(v___x_3349_, 1);
if (lean_obj_tag(v_val_3351_) == 1)
{
uint8_t v_v_3352_; 
v_v_3352_ = lean_ctor_get_uint8(v_val_3351_, 0);
lean_dec_ref_known(v_val_3351_, 0);
return v_v_3352_;
}
else
{
uint8_t v___x_3353_; 
lean_dec(v_val_3351_);
v___x_3353_ = lean_unbox(v_defValue_3347_);
return v___x_3353_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3354_, lean_object* v_opt_3355_){
_start:
{
uint8_t v_res_3356_; lean_object* v_r_3357_; 
v_res_3356_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3354_, v_opt_3355_);
lean_dec_ref(v_opt_3355_);
lean_dec_ref(v_opts_3354_);
v_r_3357_ = lean_box(v_res_3356_);
return v_r_3357_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3358_){
_start:
{
if (lean_obj_tag(v_e_3358_) == 0)
{
uint8_t v___x_3359_; 
v___x_3359_ = 2;
return v___x_3359_;
}
else
{
uint8_t v___x_3360_; 
v___x_3360_ = 0;
return v___x_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3361_){
_start:
{
uint8_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3361_);
lean_dec_ref(v_e_3361_);
v_r_3363_ = lean_box(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3364_, lean_object* v_opt_3365_){
_start:
{
lean_object* v_name_3366_; lean_object* v_defValue_3367_; lean_object* v_map_3368_; lean_object* v___x_3369_; 
v_name_3366_ = lean_ctor_get(v_opt_3365_, 0);
v_defValue_3367_ = lean_ctor_get(v_opt_3365_, 1);
v_map_3368_ = lean_ctor_get(v_opts_3364_, 0);
v___x_3369_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3368_, v_name_3366_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_inc(v_defValue_3367_);
return v_defValue_3367_;
}
else
{
lean_object* v_val_3370_; 
v_val_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_val_3370_);
lean_dec_ref_known(v___x_3369_, 1);
if (lean_obj_tag(v_val_3370_) == 3)
{
lean_object* v_v_3371_; 
v_v_3371_ = lean_ctor_get(v_val_3370_, 0);
lean_inc(v_v_3371_);
lean_dec_ref_known(v_val_3370_, 1);
return v_v_3371_;
}
else
{
lean_dec(v_val_3370_);
lean_inc(v_defValue_3367_);
return v_defValue_3367_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3372_, lean_object* v_opt_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3372_, v_opt_3373_);
lean_dec_ref(v_opt_3373_);
lean_dec_ref(v_opts_3372_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3375_, size_t v_i_3376_, lean_object* v_bs_3377_){
_start:
{
uint8_t v___x_3378_; 
v___x_3378_ = lean_usize_dec_lt(v_i_3376_, v_sz_3375_);
if (v___x_3378_ == 0)
{
return v_bs_3377_;
}
else
{
lean_object* v_v_3379_; lean_object* v_msg_3380_; lean_object* v___x_3381_; lean_object* v_bs_x27_3382_; size_t v___x_3383_; size_t v___x_3384_; lean_object* v___x_3385_; 
v_v_3379_ = lean_array_uget_borrowed(v_bs_3377_, v_i_3376_);
v_msg_3380_ = lean_ctor_get(v_v_3379_, 1);
lean_inc_ref(v_msg_3380_);
v___x_3381_ = lean_unsigned_to_nat(0u);
v_bs_x27_3382_ = lean_array_uset(v_bs_3377_, v_i_3376_, v___x_3381_);
v___x_3383_ = ((size_t)1ULL);
v___x_3384_ = lean_usize_add(v_i_3376_, v___x_3383_);
v___x_3385_ = lean_array_uset(v_bs_x27_3382_, v_i_3376_, v_msg_3380_);
v_i_3376_ = v___x_3384_;
v_bs_3377_ = v___x_3385_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3387_, lean_object* v_i_3388_, lean_object* v_bs_3389_){
_start:
{
size_t v_sz_boxed_3390_; size_t v_i_boxed_3391_; lean_object* v_res_3392_; 
v_sz_boxed_3390_ = lean_unbox_usize(v_sz_3387_);
lean_dec(v_sz_3387_);
v_i_boxed_3391_ = lean_unbox_usize(v_i_3388_);
lean_dec(v_i_3388_);
v_res_3392_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3390_, v_i_boxed_3391_, v_bs_3389_);
return v_res_3392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3393_, lean_object* v_data_3394_, lean_object* v_ref_3395_, lean_object* v_msg_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_fileName_3402_; lean_object* v_fileMap_3403_; lean_object* v_options_3404_; lean_object* v_currRecDepth_3405_; lean_object* v_maxRecDepth_3406_; lean_object* v_ref_3407_; lean_object* v_currNamespace_3408_; lean_object* v_openDecls_3409_; lean_object* v_initHeartbeats_3410_; lean_object* v_maxHeartbeats_3411_; lean_object* v_quotContext_3412_; lean_object* v_currMacroScope_3413_; uint8_t v_diag_3414_; lean_object* v_cancelTk_x3f_3415_; uint8_t v_suppressElabErrors_3416_; lean_object* v_inheritedTraceOptions_3417_; lean_object* v___x_3418_; lean_object* v_traceState_3419_; lean_object* v_traces_3420_; lean_object* v_ref_3421_; lean_object* v___x_3422_; lean_object* v___x_3423_; size_t v_sz_3424_; size_t v___x_3425_; lean_object* v___x_3426_; lean_object* v_msg_3427_; lean_object* v___x_3428_; lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3466_; 
v_fileName_3402_ = lean_ctor_get(v___y_3399_, 0);
v_fileMap_3403_ = lean_ctor_get(v___y_3399_, 1);
v_options_3404_ = lean_ctor_get(v___y_3399_, 2);
v_currRecDepth_3405_ = lean_ctor_get(v___y_3399_, 3);
v_maxRecDepth_3406_ = lean_ctor_get(v___y_3399_, 4);
v_ref_3407_ = lean_ctor_get(v___y_3399_, 5);
v_currNamespace_3408_ = lean_ctor_get(v___y_3399_, 6);
v_openDecls_3409_ = lean_ctor_get(v___y_3399_, 7);
v_initHeartbeats_3410_ = lean_ctor_get(v___y_3399_, 8);
v_maxHeartbeats_3411_ = lean_ctor_get(v___y_3399_, 9);
v_quotContext_3412_ = lean_ctor_get(v___y_3399_, 10);
v_currMacroScope_3413_ = lean_ctor_get(v___y_3399_, 11);
v_diag_3414_ = lean_ctor_get_uint8(v___y_3399_, sizeof(void*)*14);
v_cancelTk_x3f_3415_ = lean_ctor_get(v___y_3399_, 12);
v_suppressElabErrors_3416_ = lean_ctor_get_uint8(v___y_3399_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3417_ = lean_ctor_get(v___y_3399_, 13);
v___x_3418_ = lean_st_ref_get(v___y_3400_);
v_traceState_3419_ = lean_ctor_get(v___x_3418_, 4);
lean_inc_ref(v_traceState_3419_);
lean_dec(v___x_3418_);
v_traces_3420_ = lean_ctor_get(v_traceState_3419_, 0);
lean_inc_ref(v_traces_3420_);
lean_dec_ref(v_traceState_3419_);
v_ref_3421_ = l_Lean_replaceRef(v_ref_3395_, v_ref_3407_);
lean_inc_ref(v_inheritedTraceOptions_3417_);
lean_inc(v_cancelTk_x3f_3415_);
lean_inc(v_currMacroScope_3413_);
lean_inc(v_quotContext_3412_);
lean_inc(v_maxHeartbeats_3411_);
lean_inc(v_initHeartbeats_3410_);
lean_inc(v_openDecls_3409_);
lean_inc(v_currNamespace_3408_);
lean_inc(v_maxRecDepth_3406_);
lean_inc(v_currRecDepth_3405_);
lean_inc_ref(v_options_3404_);
lean_inc_ref(v_fileMap_3403_);
lean_inc_ref(v_fileName_3402_);
v___x_3422_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3422_, 0, v_fileName_3402_);
lean_ctor_set(v___x_3422_, 1, v_fileMap_3403_);
lean_ctor_set(v___x_3422_, 2, v_options_3404_);
lean_ctor_set(v___x_3422_, 3, v_currRecDepth_3405_);
lean_ctor_set(v___x_3422_, 4, v_maxRecDepth_3406_);
lean_ctor_set(v___x_3422_, 5, v_ref_3421_);
lean_ctor_set(v___x_3422_, 6, v_currNamespace_3408_);
lean_ctor_set(v___x_3422_, 7, v_openDecls_3409_);
lean_ctor_set(v___x_3422_, 8, v_initHeartbeats_3410_);
lean_ctor_set(v___x_3422_, 9, v_maxHeartbeats_3411_);
lean_ctor_set(v___x_3422_, 10, v_quotContext_3412_);
lean_ctor_set(v___x_3422_, 11, v_currMacroScope_3413_);
lean_ctor_set(v___x_3422_, 12, v_cancelTk_x3f_3415_);
lean_ctor_set(v___x_3422_, 13, v_inheritedTraceOptions_3417_);
lean_ctor_set_uint8(v___x_3422_, sizeof(void*)*14, v_diag_3414_);
lean_ctor_set_uint8(v___x_3422_, sizeof(void*)*14 + 1, v_suppressElabErrors_3416_);
v___x_3423_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3420_);
lean_dec_ref(v_traces_3420_);
v_sz_3424_ = lean_array_size(v___x_3423_);
v___x_3425_ = ((size_t)0ULL);
v___x_3426_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3424_, v___x_3425_, v___x_3423_);
v_msg_3427_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3427_, 0, v_data_3394_);
lean_ctor_set(v_msg_3427_, 1, v_msg_3396_);
lean_ctor_set(v_msg_3427_, 2, v___x_3426_);
v___x_3428_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3427_, v___y_3397_, v___y_3398_, v___x_3422_, v___y_3400_);
lean_dec_ref_known(v___x_3422_, 14);
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3431_ = v___x_3428_;
v_isShared_3432_ = v_isSharedCheck_3466_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3428_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3466_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3433_; lean_object* v_traceState_3434_; lean_object* v_env_3435_; lean_object* v_nextMacroScope_3436_; lean_object* v_ngen_3437_; lean_object* v_auxDeclNGen_3438_; lean_object* v_cache_3439_; lean_object* v_messages_3440_; lean_object* v_infoState_3441_; lean_object* v_snapshotTasks_3442_; lean_object* v___x_3444_; uint8_t v_isShared_3445_; uint8_t v_isSharedCheck_3465_; 
v___x_3433_ = lean_st_ref_take(v___y_3400_);
v_traceState_3434_ = lean_ctor_get(v___x_3433_, 4);
v_env_3435_ = lean_ctor_get(v___x_3433_, 0);
v_nextMacroScope_3436_ = lean_ctor_get(v___x_3433_, 1);
v_ngen_3437_ = lean_ctor_get(v___x_3433_, 2);
v_auxDeclNGen_3438_ = lean_ctor_get(v___x_3433_, 3);
v_cache_3439_ = lean_ctor_get(v___x_3433_, 5);
v_messages_3440_ = lean_ctor_get(v___x_3433_, 6);
v_infoState_3441_ = lean_ctor_get(v___x_3433_, 7);
v_snapshotTasks_3442_ = lean_ctor_get(v___x_3433_, 8);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3444_ = v___x_3433_;
v_isShared_3445_ = v_isSharedCheck_3465_;
goto v_resetjp_3443_;
}
else
{
lean_inc(v_snapshotTasks_3442_);
lean_inc(v_infoState_3441_);
lean_inc(v_messages_3440_);
lean_inc(v_cache_3439_);
lean_inc(v_traceState_3434_);
lean_inc(v_auxDeclNGen_3438_);
lean_inc(v_ngen_3437_);
lean_inc(v_nextMacroScope_3436_);
lean_inc(v_env_3435_);
lean_dec(v___x_3433_);
v___x_3444_ = lean_box(0);
v_isShared_3445_ = v_isSharedCheck_3465_;
goto v_resetjp_3443_;
}
v_resetjp_3443_:
{
uint64_t v_tid_3446_; lean_object* v___x_3448_; uint8_t v_isShared_3449_; uint8_t v_isSharedCheck_3463_; 
v_tid_3446_ = lean_ctor_get_uint64(v_traceState_3434_, sizeof(void*)*1);
v_isSharedCheck_3463_ = !lean_is_exclusive(v_traceState_3434_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v_traceState_3434_, 0);
lean_dec(v_unused_3464_);
v___x_3448_ = v_traceState_3434_;
v_isShared_3449_ = v_isSharedCheck_3463_;
goto v_resetjp_3447_;
}
else
{
lean_dec(v_traceState_3434_);
v___x_3448_ = lean_box(0);
v_isShared_3449_ = v_isSharedCheck_3463_;
goto v_resetjp_3447_;
}
v_resetjp_3447_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3453_; 
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v_ref_3395_);
lean_ctor_set(v___x_3450_, 1, v_a_3429_);
v___x_3451_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3393_, v___x_3450_);
if (v_isShared_3449_ == 0)
{
lean_ctor_set(v___x_3448_, 0, v___x_3451_);
v___x_3453_ = v___x_3448_;
goto v_reusejp_3452_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3451_);
lean_ctor_set_uint64(v_reuseFailAlloc_3462_, sizeof(void*)*1, v_tid_3446_);
v___x_3453_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3452_;
}
v_reusejp_3452_:
{
lean_object* v___x_3455_; 
if (v_isShared_3445_ == 0)
{
lean_ctor_set(v___x_3444_, 4, v___x_3453_);
v___x_3455_ = v___x_3444_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v_env_3435_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_nextMacroScope_3436_);
lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_ngen_3437_);
lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_auxDeclNGen_3438_);
lean_ctor_set(v_reuseFailAlloc_3461_, 4, v___x_3453_);
lean_ctor_set(v_reuseFailAlloc_3461_, 5, v_cache_3439_);
lean_ctor_set(v_reuseFailAlloc_3461_, 6, v_messages_3440_);
lean_ctor_set(v_reuseFailAlloc_3461_, 7, v_infoState_3441_);
lean_ctor_set(v_reuseFailAlloc_3461_, 8, v_snapshotTasks_3442_);
v___x_3455_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
v___x_3456_ = lean_st_ref_put(v___y_3400_, v___x_3455_);
v___x_3457_ = lean_box(0);
if (v_isShared_3432_ == 0)
{
lean_ctor_set(v___x_3431_, 0, v___x_3457_);
v___x_3459_ = v___x_3431_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3460_; 
v_reuseFailAlloc_3460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3460_, 0, v___x_3457_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3467_, lean_object* v_data_3468_, lean_object* v_ref_3469_, lean_object* v_msg_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3467_, v_data_3468_, v_ref_3469_, v_msg_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec(v___y_3472_);
lean_dec_ref(v___y_3471_);
return v_res_3476_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3479_ = l_Lean_stringToMessageData(v___x_3478_);
return v___x_3479_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3480_; double v___x_3481_; 
v___x_3480_ = lean_unsigned_to_nat(1000u);
v___x_3481_ = lean_float_of_nat(v___x_3480_);
return v___x_3481_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3482_, uint8_t v_collapsed_3483_, lean_object* v_tag_3484_, lean_object* v_opts_3485_, uint8_t v_clsEnabled_3486_, lean_object* v_oldTraces_3487_, lean_object* v_msg_3488_, lean_object* v_resStartStop_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_){
_start:
{
lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v_data_3502_; lean_object* v_fst_3513_; lean_object* v_snd_3514_; lean_object* v___x_3515_; uint8_t v___x_3516_; lean_object* v___y_3518_; lean_object* v_a_3519_; uint8_t v___y_3534_; double v___y_3565_; 
v_fst_3497_ = lean_ctor_get(v_resStartStop_3489_, 0);
lean_inc(v_fst_3497_);
v_snd_3498_ = lean_ctor_get(v_resStartStop_3489_, 1);
lean_inc(v_snd_3498_);
lean_dec_ref(v_resStartStop_3489_);
v_fst_3513_ = lean_ctor_get(v_snd_3498_, 0);
lean_inc(v_fst_3513_);
v_snd_3514_ = lean_ctor_get(v_snd_3498_, 1);
lean_inc(v_snd_3514_);
lean_dec(v_snd_3498_);
v___x_3515_ = l_Lean_trace_profiler;
v___x_3516_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3485_, v___x_3515_);
if (v___x_3516_ == 0)
{
v___y_3534_ = v___x_3516_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3570_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3571_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3485_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; double v___x_3574_; double v___x_3575_; double v___x_3576_; 
v___x_3572_ = l_Lean_trace_profiler_threshold;
v___x_3573_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3485_, v___x_3572_);
v___x_3574_ = lean_float_of_nat(v___x_3573_);
v___x_3575_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3576_ = lean_float_div(v___x_3574_, v___x_3575_);
v___y_3565_ = v___x_3576_;
goto v___jp_3564_;
}
else
{
lean_object* v___x_3577_; lean_object* v___x_3578_; double v___x_3579_; 
v___x_3577_ = l_Lean_trace_profiler_threshold;
v___x_3578_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3485_, v___x_3577_);
v___x_3579_ = lean_float_of_nat(v___x_3578_);
v___y_3565_ = v___x_3579_;
goto v___jp_3564_;
}
}
v___jp_3499_:
{
lean_object* v___x_3503_; 
lean_inc(v___y_3500_);
v___x_3503_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3487_, v_data_3502_, v___y_3500_, v___y_3501_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v___x_3504_; 
lean_dec_ref_known(v___x_3503_, 1);
v___x_3504_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3497_);
return v___x_3504_;
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_fst_3497_);
v_a_3505_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3503_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3503_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
v___jp_3517_:
{
uint8_t v_result_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; double v___x_3523_; lean_object* v_data_3524_; 
v_result_3520_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3497_);
v___x_3521_ = lean_box(v_result_3520_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___x_3523_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3484_);
lean_inc_ref(v___x_3522_);
lean_inc(v_cls_3482_);
v_data_3524_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3524_, 0, v_cls_3482_);
lean_ctor_set(v_data_3524_, 1, v___x_3522_);
lean_ctor_set(v_data_3524_, 2, v_tag_3484_);
lean_ctor_set_float(v_data_3524_, sizeof(void*)*3, v___x_3523_);
lean_ctor_set_float(v_data_3524_, sizeof(void*)*3 + 8, v___x_3523_);
lean_ctor_set_uint8(v_data_3524_, sizeof(void*)*3 + 16, v_collapsed_3483_);
if (v___x_3516_ == 0)
{
lean_dec_ref_known(v___x_3522_, 1);
lean_dec(v_snd_3514_);
lean_dec(v_fst_3513_);
lean_dec_ref(v_tag_3484_);
lean_dec(v_cls_3482_);
v___y_3500_ = v___y_3518_;
v___y_3501_ = v_a_3519_;
v_data_3502_ = v_data_3524_;
goto v___jp_3499_;
}
else
{
lean_object* v_data_3525_; double v___x_3526_; double v___x_3527_; 
lean_dec_ref_known(v_data_3524_, 3);
v_data_3525_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3525_, 0, v_cls_3482_);
lean_ctor_set(v_data_3525_, 1, v___x_3522_);
lean_ctor_set(v_data_3525_, 2, v_tag_3484_);
v___x_3526_ = lean_unbox_float(v_fst_3513_);
lean_dec(v_fst_3513_);
lean_ctor_set_float(v_data_3525_, sizeof(void*)*3, v___x_3526_);
v___x_3527_ = lean_unbox_float(v_snd_3514_);
lean_dec(v_snd_3514_);
lean_ctor_set_float(v_data_3525_, sizeof(void*)*3 + 8, v___x_3527_);
lean_ctor_set_uint8(v_data_3525_, sizeof(void*)*3 + 16, v_collapsed_3483_);
v___y_3500_ = v___y_3518_;
v___y_3501_ = v_a_3519_;
v_data_3502_ = v_data_3525_;
goto v___jp_3499_;
}
}
v___jp_3528_:
{
lean_object* v_ref_3529_; lean_object* v___x_3530_; 
v_ref_3529_ = lean_ctor_get(v___y_3494_, 5);
lean_inc(v___y_3495_);
lean_inc_ref(v___y_3494_);
lean_inc(v___y_3493_);
lean_inc_ref(v___y_3492_);
lean_inc(v___y_3491_);
lean_inc(v___y_3490_);
lean_inc(v_fst_3497_);
v___x_3530_ = lean_apply_8(v_msg_3488_, v_fst_3497_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_, v___y_3494_, v___y_3495_, lean_box(0));
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
lean_inc(v_a_3531_);
lean_dec_ref_known(v___x_3530_, 1);
v___y_3518_ = v_ref_3529_;
v_a_3519_ = v_a_3531_;
goto v___jp_3517_;
}
else
{
lean_object* v___x_3532_; 
lean_dec_ref_known(v___x_3530_, 1);
v___x_3532_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3518_ = v_ref_3529_;
v_a_3519_ = v___x_3532_;
goto v___jp_3517_;
}
}
v___jp_3533_:
{
if (v_clsEnabled_3486_ == 0)
{
if (v___y_3534_ == 0)
{
lean_object* v___x_3535_; lean_object* v_traceState_3536_; lean_object* v_env_3537_; lean_object* v_nextMacroScope_3538_; lean_object* v_ngen_3539_; lean_object* v_auxDeclNGen_3540_; lean_object* v_cache_3541_; lean_object* v_messages_3542_; lean_object* v_infoState_3543_; lean_object* v_snapshotTasks_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3563_; 
lean_dec(v_snd_3514_);
lean_dec(v_fst_3513_);
lean_dec_ref(v_msg_3488_);
lean_dec_ref(v_tag_3484_);
lean_dec(v_cls_3482_);
v___x_3535_ = lean_st_ref_take(v___y_3495_);
v_traceState_3536_ = lean_ctor_get(v___x_3535_, 4);
v_env_3537_ = lean_ctor_get(v___x_3535_, 0);
v_nextMacroScope_3538_ = lean_ctor_get(v___x_3535_, 1);
v_ngen_3539_ = lean_ctor_get(v___x_3535_, 2);
v_auxDeclNGen_3540_ = lean_ctor_get(v___x_3535_, 3);
v_cache_3541_ = lean_ctor_get(v___x_3535_, 5);
v_messages_3542_ = lean_ctor_get(v___x_3535_, 6);
v_infoState_3543_ = lean_ctor_get(v___x_3535_, 7);
v_snapshotTasks_3544_ = lean_ctor_get(v___x_3535_, 8);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3546_ = v___x_3535_;
v_isShared_3547_ = v_isSharedCheck_3563_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_snapshotTasks_3544_);
lean_inc(v_infoState_3543_);
lean_inc(v_messages_3542_);
lean_inc(v_cache_3541_);
lean_inc(v_traceState_3536_);
lean_inc(v_auxDeclNGen_3540_);
lean_inc(v_ngen_3539_);
lean_inc(v_nextMacroScope_3538_);
lean_inc(v_env_3537_);
lean_dec(v___x_3535_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3563_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
uint64_t v_tid_3548_; lean_object* v_traces_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3562_; 
v_tid_3548_ = lean_ctor_get_uint64(v_traceState_3536_, sizeof(void*)*1);
v_traces_3549_ = lean_ctor_get(v_traceState_3536_, 0);
v_isSharedCheck_3562_ = !lean_is_exclusive(v_traceState_3536_);
if (v_isSharedCheck_3562_ == 0)
{
v___x_3551_ = v_traceState_3536_;
v_isShared_3552_ = v_isSharedCheck_3562_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_traces_3549_);
lean_dec(v_traceState_3536_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3562_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3553_; lean_object* v___x_3555_; 
v___x_3553_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3487_, v_traces_3549_);
lean_dec_ref(v_traces_3549_);
if (v_isShared_3552_ == 0)
{
lean_ctor_set(v___x_3551_, 0, v___x_3553_);
v___x_3555_ = v___x_3551_;
goto v_reusejp_3554_;
}
else
{
lean_object* v_reuseFailAlloc_3561_; 
v_reuseFailAlloc_3561_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3561_, 0, v___x_3553_);
lean_ctor_set_uint64(v_reuseFailAlloc_3561_, sizeof(void*)*1, v_tid_3548_);
v___x_3555_ = v_reuseFailAlloc_3561_;
goto v_reusejp_3554_;
}
v_reusejp_3554_:
{
lean_object* v___x_3557_; 
if (v_isShared_3547_ == 0)
{
lean_ctor_set(v___x_3546_, 4, v___x_3555_);
v___x_3557_ = v___x_3546_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v_env_3537_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_nextMacroScope_3538_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_ngen_3539_);
lean_ctor_set(v_reuseFailAlloc_3560_, 3, v_auxDeclNGen_3540_);
lean_ctor_set(v_reuseFailAlloc_3560_, 4, v___x_3555_);
lean_ctor_set(v_reuseFailAlloc_3560_, 5, v_cache_3541_);
lean_ctor_set(v_reuseFailAlloc_3560_, 6, v_messages_3542_);
lean_ctor_set(v_reuseFailAlloc_3560_, 7, v_infoState_3543_);
lean_ctor_set(v_reuseFailAlloc_3560_, 8, v_snapshotTasks_3544_);
v___x_3557_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_st_ref_put(v___y_3495_, v___x_3557_);
v___x_3559_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3497_);
return v___x_3559_;
}
}
}
}
}
else
{
goto v___jp_3528_;
}
}
else
{
goto v___jp_3528_;
}
}
v___jp_3564_:
{
double v___x_3566_; double v___x_3567_; double v___x_3568_; uint8_t v___x_3569_; 
v___x_3566_ = lean_unbox_float(v_snd_3514_);
v___x_3567_ = lean_unbox_float(v_fst_3513_);
v___x_3568_ = lean_float_sub(v___x_3566_, v___x_3567_);
v___x_3569_ = lean_float_decLt(v___y_3565_, v___x_3568_);
v___y_3534_ = v___x_3569_;
goto v___jp_3533_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3580_, lean_object* v_collapsed_3581_, lean_object* v_tag_3582_, lean_object* v_opts_3583_, lean_object* v_clsEnabled_3584_, lean_object* v_oldTraces_3585_, lean_object* v_msg_3586_, lean_object* v_resStartStop_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
uint8_t v_collapsed_boxed_3595_; uint8_t v_clsEnabled_boxed_3596_; lean_object* v_res_3597_; 
v_collapsed_boxed_3595_ = lean_unbox(v_collapsed_3581_);
v_clsEnabled_boxed_3596_ = lean_unbox(v_clsEnabled_3584_);
v_res_3597_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3580_, v_collapsed_boxed_3595_, v_tag_3582_, v_opts_3583_, v_clsEnabled_boxed_3596_, v_oldTraces_3585_, v_msg_3586_, v_resStartStop_3587_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
lean_dec(v___y_3593_);
lean_dec_ref(v___y_3592_);
lean_dec(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v_opts_3583_);
return v_res_3597_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3598_ = lean_unsigned_to_nat(32u);
v___x_3599_ = lean_mk_empty_array_with_capacity(v___x_3598_);
v___x_3600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3599_);
return v___x_3600_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3601_ = ((size_t)5ULL);
v___x_3602_ = lean_unsigned_to_nat(0u);
v___x_3603_ = lean_unsigned_to_nat(32u);
v___x_3604_ = lean_mk_empty_array_with_capacity(v___x_3603_);
v___x_3605_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3606_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___x_3604_);
lean_ctor_set(v___x_3606_, 2, v___x_3602_);
lean_ctor_set(v___x_3606_, 3, v___x_3602_);
lean_ctor_set_usize(v___x_3606_, 4, v___x_3601_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3607_){
_start:
{
lean_object* v___x_3609_; lean_object* v_traceState_3610_; lean_object* v_traces_3611_; lean_object* v___x_3612_; lean_object* v_traceState_3613_; lean_object* v_env_3614_; lean_object* v_nextMacroScope_3615_; lean_object* v_ngen_3616_; lean_object* v_auxDeclNGen_3617_; lean_object* v_cache_3618_; lean_object* v_messages_3619_; lean_object* v_infoState_3620_; lean_object* v_snapshotTasks_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3640_; 
v___x_3609_ = lean_st_ref_get(v___y_3607_);
v_traceState_3610_ = lean_ctor_get(v___x_3609_, 4);
lean_inc_ref(v_traceState_3610_);
lean_dec(v___x_3609_);
v_traces_3611_ = lean_ctor_get(v_traceState_3610_, 0);
lean_inc_ref(v_traces_3611_);
lean_dec_ref(v_traceState_3610_);
v___x_3612_ = lean_st_ref_take(v___y_3607_);
v_traceState_3613_ = lean_ctor_get(v___x_3612_, 4);
v_env_3614_ = lean_ctor_get(v___x_3612_, 0);
v_nextMacroScope_3615_ = lean_ctor_get(v___x_3612_, 1);
v_ngen_3616_ = lean_ctor_get(v___x_3612_, 2);
v_auxDeclNGen_3617_ = lean_ctor_get(v___x_3612_, 3);
v_cache_3618_ = lean_ctor_get(v___x_3612_, 5);
v_messages_3619_ = lean_ctor_get(v___x_3612_, 6);
v_infoState_3620_ = lean_ctor_get(v___x_3612_, 7);
v_snapshotTasks_3621_ = lean_ctor_get(v___x_3612_, 8);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3623_ = v___x_3612_;
v_isShared_3624_ = v_isSharedCheck_3640_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_snapshotTasks_3621_);
lean_inc(v_infoState_3620_);
lean_inc(v_messages_3619_);
lean_inc(v_cache_3618_);
lean_inc(v_traceState_3613_);
lean_inc(v_auxDeclNGen_3617_);
lean_inc(v_ngen_3616_);
lean_inc(v_nextMacroScope_3615_);
lean_inc(v_env_3614_);
lean_dec(v___x_3612_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3640_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
uint64_t v_tid_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3638_; 
v_tid_3625_ = lean_ctor_get_uint64(v_traceState_3613_, sizeof(void*)*1);
v_isSharedCheck_3638_ = !lean_is_exclusive(v_traceState_3613_);
if (v_isSharedCheck_3638_ == 0)
{
lean_object* v_unused_3639_; 
v_unused_3639_ = lean_ctor_get(v_traceState_3613_, 0);
lean_dec(v_unused_3639_);
v___x_3627_ = v_traceState_3613_;
v_isShared_3628_ = v_isSharedCheck_3638_;
goto v_resetjp_3626_;
}
else
{
lean_dec(v_traceState_3613_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3638_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3629_; lean_object* v___x_3631_; 
v___x_3629_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3628_ == 0)
{
lean_ctor_set(v___x_3627_, 0, v___x_3629_);
v___x_3631_ = v___x_3627_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3629_);
lean_ctor_set_uint64(v_reuseFailAlloc_3637_, sizeof(void*)*1, v_tid_3625_);
v___x_3631_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
lean_object* v___x_3633_; 
if (v_isShared_3624_ == 0)
{
lean_ctor_set(v___x_3623_, 4, v___x_3631_);
v___x_3633_ = v___x_3623_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3636_; 
v_reuseFailAlloc_3636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3636_, 0, v_env_3614_);
lean_ctor_set(v_reuseFailAlloc_3636_, 1, v_nextMacroScope_3615_);
lean_ctor_set(v_reuseFailAlloc_3636_, 2, v_ngen_3616_);
lean_ctor_set(v_reuseFailAlloc_3636_, 3, v_auxDeclNGen_3617_);
lean_ctor_set(v_reuseFailAlloc_3636_, 4, v___x_3631_);
lean_ctor_set(v_reuseFailAlloc_3636_, 5, v_cache_3618_);
lean_ctor_set(v_reuseFailAlloc_3636_, 6, v_messages_3619_);
lean_ctor_set(v_reuseFailAlloc_3636_, 7, v_infoState_3620_);
lean_ctor_set(v_reuseFailAlloc_3636_, 8, v_snapshotTasks_3621_);
v___x_3633_ = v_reuseFailAlloc_3636_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; 
v___x_3634_ = lean_st_ref_put(v___y_3607_, v___x_3633_);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_traces_3611_);
return v___x_3635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
lean_object* v_res_3643_; 
v_res_3643_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3641_);
lean_dec(v___y_3641_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
lean_object* v___x_3652_; 
lean_inc(v___y_3646_);
lean_inc(v___y_3645_);
v___x_3652_ = lean_apply_7(v_x_3644_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_, lean_box(0));
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3653_, lean_object* v___y_3654_, lean_object* v___y_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v_res_3661_; 
v_res_3661_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3653_, v___y_3654_, v___y_3655_, v___y_3656_, v___y_3657_, v___y_3658_, v___y_3659_);
lean_dec(v___y_3655_);
lean_dec(v___y_3654_);
return v_res_3661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3662_, lean_object* v_localInsts_3663_, lean_object* v_x_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_){
_start:
{
lean_object* v___f_3672_; lean_object* v___x_3673_; 
lean_inc(v___y_3666_);
lean_inc(v___y_3665_);
v___f_3672_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3672_, 0, v_x_3664_);
lean_closure_set(v___f_3672_, 1, v___y_3665_);
lean_closure_set(v___f_3672_, 2, v___y_3666_);
v___x_3673_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3662_, v_localInsts_3663_, v___f_3672_, v___y_3667_, v___y_3668_, v___y_3669_, v___y_3670_);
if (lean_obj_tag(v___x_3673_) == 0)
{
return v___x_3673_;
}
else
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3681_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3681_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3681_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3679_; 
if (v_isShared_3677_ == 0)
{
v___x_3679_ = v___x_3676_;
goto v_reusejp_3678_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v_a_3674_);
v___x_3679_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3678_;
}
v_reusejp_3678_:
{
return v___x_3679_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3682_, lean_object* v_localInsts_3683_, lean_object* v_x_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3682_, v_localInsts_3683_, v_x_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec(v___y_3685_);
return v_res_3692_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3693_){
_start:
{
lean_object* v___x_3695_; lean_object* v_ngen_3696_; lean_object* v_namePrefix_3697_; lean_object* v_idx_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3727_; 
v___x_3695_ = lean_st_ref_get(v___y_3693_);
v_ngen_3696_ = lean_ctor_get(v___x_3695_, 2);
lean_inc_ref(v_ngen_3696_);
lean_dec(v___x_3695_);
v_namePrefix_3697_ = lean_ctor_get(v_ngen_3696_, 0);
v_idx_3698_ = lean_ctor_get(v_ngen_3696_, 1);
v_isSharedCheck_3727_ = !lean_is_exclusive(v_ngen_3696_);
if (v_isSharedCheck_3727_ == 0)
{
v___x_3700_ = v_ngen_3696_;
v_isShared_3701_ = v_isSharedCheck_3727_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_idx_3698_);
lean_inc(v_namePrefix_3697_);
lean_dec(v_ngen_3696_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3727_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3702_; lean_object* v_env_3703_; lean_object* v_nextMacroScope_3704_; lean_object* v_auxDeclNGen_3705_; lean_object* v_traceState_3706_; lean_object* v_cache_3707_; lean_object* v_messages_3708_; lean_object* v_infoState_3709_; lean_object* v_snapshotTasks_3710_; lean_object* v___x_3712_; uint8_t v_isShared_3713_; uint8_t v_isSharedCheck_3725_; 
v___x_3702_ = lean_st_ref_take(v___y_3693_);
v_env_3703_ = lean_ctor_get(v___x_3702_, 0);
v_nextMacroScope_3704_ = lean_ctor_get(v___x_3702_, 1);
v_auxDeclNGen_3705_ = lean_ctor_get(v___x_3702_, 3);
v_traceState_3706_ = lean_ctor_get(v___x_3702_, 4);
v_cache_3707_ = lean_ctor_get(v___x_3702_, 5);
v_messages_3708_ = lean_ctor_get(v___x_3702_, 6);
v_infoState_3709_ = lean_ctor_get(v___x_3702_, 7);
v_snapshotTasks_3710_ = lean_ctor_get(v___x_3702_, 8);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3725_ == 0)
{
lean_object* v_unused_3726_; 
v_unused_3726_ = lean_ctor_get(v___x_3702_, 2);
lean_dec(v_unused_3726_);
v___x_3712_ = v___x_3702_;
v_isShared_3713_ = v_isSharedCheck_3725_;
goto v_resetjp_3711_;
}
else
{
lean_inc(v_snapshotTasks_3710_);
lean_inc(v_infoState_3709_);
lean_inc(v_messages_3708_);
lean_inc(v_cache_3707_);
lean_inc(v_traceState_3706_);
lean_inc(v_auxDeclNGen_3705_);
lean_inc(v_nextMacroScope_3704_);
lean_inc(v_env_3703_);
lean_dec(v___x_3702_);
v___x_3712_ = lean_box(0);
v_isShared_3713_ = v_isSharedCheck_3725_;
goto v_resetjp_3711_;
}
v_resetjp_3711_:
{
lean_object* v_r_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3718_; 
lean_inc(v_idx_3698_);
lean_inc(v_namePrefix_3697_);
v_r_3714_ = l_Lean_Name_num___override(v_namePrefix_3697_, v_idx_3698_);
v___x_3715_ = lean_unsigned_to_nat(1u);
v___x_3716_ = lean_nat_add(v_idx_3698_, v___x_3715_);
lean_dec(v_idx_3698_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 1, v___x_3716_);
v___x_3718_ = v___x_3700_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_namePrefix_3697_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3716_);
v___x_3718_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
lean_object* v___x_3720_; 
if (v_isShared_3713_ == 0)
{
lean_ctor_set(v___x_3712_, 2, v___x_3718_);
v___x_3720_ = v___x_3712_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v_env_3703_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_nextMacroScope_3704_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v___x_3718_);
lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_auxDeclNGen_3705_);
lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_traceState_3706_);
lean_ctor_set(v_reuseFailAlloc_3723_, 5, v_cache_3707_);
lean_ctor_set(v_reuseFailAlloc_3723_, 6, v_messages_3708_);
lean_ctor_set(v_reuseFailAlloc_3723_, 7, v_infoState_3709_);
lean_ctor_set(v_reuseFailAlloc_3723_, 8, v_snapshotTasks_3710_);
v___x_3720_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3721_; lean_object* v___x_3722_; 
v___x_3721_ = lean_st_ref_put(v___y_3693_, v___x_3720_);
v___x_3722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3722_, 0, v_r_3714_);
return v___x_3722_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
lean_object* v_res_3730_; 
v_res_3730_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3728_);
lean_dec(v___y_3728_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_){
_start:
{
lean_object* v___x_3738_; lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
v___x_3738_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3736_);
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_){
_start:
{
lean_object* v_res_3754_; 
v_res_3754_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_, v___y_3751_, v___y_3752_);
lean_dec(v___y_3752_);
lean_dec_ref(v___y_3751_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec(v___y_3747_);
return v_res_3754_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3756_; lean_object* v___x_3757_; 
v___x_3756_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3757_ = l_Lean_stringToMessageData(v___x_3756_);
return v___x_3757_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3759_; lean_object* v___x_3760_; 
v___x_3759_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3760_ = l_Lean_stringToMessageData(v___x_3759_);
return v___x_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3763_, lean_object* v_x_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; lean_object* v___y_3774_; uint8_t v___x_3783_; 
v___x_3772_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3783_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3765_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3774_ = v___x_3784_;
goto v___jp_3773_;
}
else
{
lean_object* v___x_3785_; 
v___x_3785_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3774_ = v___x_3785_;
goto v___jp_3773_;
}
v___jp_3773_:
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
lean_inc_ref(v___y_3774_);
v___x_3775_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3775_, 0, v___y_3774_);
v___x_3776_ = l_Lean_MessageData_ofFormat(v___x_3775_);
v___x_3777_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3772_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
v___x_3778_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3777_);
lean_ctor_set(v___x_3779_, 1, v___x_3778_);
v___x_3780_ = l_Lean_indentExpr(v_e_3763_);
v___x_3781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3781_, 0, v___x_3779_);
lean_ctor_set(v___x_3781_, 1, v___x_3780_);
v___x_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3781_);
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3786_, lean_object* v_x_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
lean_object* v_res_3795_; 
v_res_3795_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3786_, v_x_3787_, v___y_3788_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_, v___y_3793_);
lean_dec(v___y_3793_);
lean_dec_ref(v___y_3792_);
lean_dec(v___y_3791_);
lean_dec_ref(v___y_3790_);
lean_dec(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v_x_3787_);
return v_res_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3796_, lean_object* v_x_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v_keyedConfig_3805_; uint8_t v_trackZetaDelta_3806_; lean_object* v_zetaDeltaSet_3807_; lean_object* v_localInstances_3808_; lean_object* v_defEqCtx_x3f_3809_; lean_object* v_synthPendingDepth_3810_; lean_object* v_customCanUnfoldPredicate_x3f_3811_; uint8_t v_univApprox_3812_; uint8_t v_inTypeClassResolution_3813_; uint8_t v_cacheInferType_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
v_keyedConfig_3805_ = lean_ctor_get(v___y_3800_, 0);
v_trackZetaDelta_3806_ = lean_ctor_get_uint8(v___y_3800_, sizeof(void*)*7);
v_zetaDeltaSet_3807_ = lean_ctor_get(v___y_3800_, 1);
v_localInstances_3808_ = lean_ctor_get(v___y_3800_, 3);
v_defEqCtx_x3f_3809_ = lean_ctor_get(v___y_3800_, 4);
v_synthPendingDepth_3810_ = lean_ctor_get(v___y_3800_, 5);
v_customCanUnfoldPredicate_x3f_3811_ = lean_ctor_get(v___y_3800_, 6);
v_univApprox_3812_ = lean_ctor_get_uint8(v___y_3800_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3813_ = lean_ctor_get_uint8(v___y_3800_, sizeof(void*)*7 + 2);
v_cacheInferType_3814_ = lean_ctor_get_uint8(v___y_3800_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3811_);
lean_inc(v_synthPendingDepth_3810_);
lean_inc(v_defEqCtx_x3f_3809_);
lean_inc_ref(v_localInstances_3808_);
lean_inc(v_zetaDeltaSet_3807_);
lean_inc_ref(v_keyedConfig_3805_);
v___x_3815_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3815_, 0, v_keyedConfig_3805_);
lean_ctor_set(v___x_3815_, 1, v_zetaDeltaSet_3807_);
lean_ctor_set(v___x_3815_, 2, v_lctx_3796_);
lean_ctor_set(v___x_3815_, 3, v_localInstances_3808_);
lean_ctor_set(v___x_3815_, 4, v_defEqCtx_x3f_3809_);
lean_ctor_set(v___x_3815_, 5, v_synthPendingDepth_3810_);
lean_ctor_set(v___x_3815_, 6, v_customCanUnfoldPredicate_x3f_3811_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*7, v_trackZetaDelta_3806_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*7 + 1, v_univApprox_3812_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3813_);
lean_ctor_set_uint8(v___x_3815_, sizeof(void*)*7 + 3, v_cacheInferType_3814_);
lean_inc(v___y_3803_);
lean_inc_ref(v___y_3802_);
lean_inc(v___y_3801_);
lean_inc(v___y_3799_);
lean_inc(v___y_3798_);
v___x_3816_ = lean_apply_7(v_x_3797_, v___y_3798_, v___y_3799_, v___x_3815_, v___y_3801_, v___y_3802_, v___y_3803_, lean_box(0));
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_object* v_a_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3824_; 
v_a_3817_ = lean_ctor_get(v___x_3816_, 0);
v_isSharedCheck_3824_ = !lean_is_exclusive(v___x_3816_);
if (v_isSharedCheck_3824_ == 0)
{
v___x_3819_ = v___x_3816_;
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_a_3817_);
lean_dec(v___x_3816_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3824_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3822_; 
if (v_isShared_3820_ == 0)
{
v___x_3822_ = v___x_3819_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3823_; 
v_reuseFailAlloc_3823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
v___x_3822_ = v_reuseFailAlloc_3823_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
return v___x_3822_;
}
}
}
else
{
return v___x_3816_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3825_, lean_object* v_x_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
lean_object* v_res_3834_; 
v_res_3834_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3825_, v_x_3826_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
lean_dec(v___y_3827_);
return v_res_3834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3837_, lean_object* v_letFVars_3838_, lean_object* v_lctx_3839_, lean_object* v_v_3840_, lean_object* v_e_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_){
_start:
{
lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3849_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3850_ = lean_expr_instantiate_rev(v_e_3841_, v_fvars_3837_);
v___x_3851_ = lean_apply_1(v_v_3840_, v___x_3850_);
v___x_3852_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3852_, 0, lean_box(0));
lean_closure_set(v___x_3852_, 1, v_letFVars_3838_);
lean_closure_set(v___x_3852_, 2, v___x_3851_);
v___x_3853_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3839_, v___x_3849_, v___x_3852_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
return v___x_3853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3854_, lean_object* v_letFVars_3855_, lean_object* v_lctx_3856_, lean_object* v_v_3857_, lean_object* v_e_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3854_, v_letFVars_3855_, v_lctx_3856_, v_v_3857_, v_e_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_, v___y_3864_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v_e_3858_);
lean_dec_ref(v_fvars_3854_);
return v_res_3866_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3868_; lean_object* v___x_3869_; 
v___x_3868_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3869_ = l_Lean_stringToMessageData(v___x_3868_);
return v___x_3869_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; 
lean_inc_ref(v_a_3870_);
v___x_3879_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3870_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v_expr_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3931_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v_expr_3881_ = lean_ctor_get(v_a_3871_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_a_3871_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_a_3871_, 1);
lean_dec(v_unused_3932_);
v___x_3883_ = v_a_3871_;
v_isShared_3884_ = v_isSharedCheck_3931_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_expr_3881_);
lean_dec(v_a_3871_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3931_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; 
lean_inc(v_a_3880_);
lean_inc_ref(v_expr_3881_);
v___x_3885_ = l_Lean_Meta_isExprDefEq(v_expr_3881_, v_a_3880_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3922_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3888_ = v___x_3885_;
v_isShared_3889_ = v_isSharedCheck_3922_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3922_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
uint8_t v___x_3890_; 
v___x_3890_ = lean_unbox(v_a_3886_);
lean_dec(v_a_3886_);
if (v___x_3890_ == 0)
{
lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
lean_del_object(v___x_3888_);
v___x_3891_ = lean_box(0);
v___x_3892_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3893_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3880_, v_expr_3881_, v___x_3891_, v___x_3892_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v_expr_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3908_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc(v_a_3894_);
lean_dec_ref_known(v___x_3893_, 1);
v_expr_3895_ = lean_ctor_get(v_a_3870_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v_a_3870_);
if (v_isSharedCheck_3908_ == 0)
{
lean_object* v_unused_3909_; 
v_unused_3909_ = lean_ctor_get(v_a_3870_, 1);
lean_dec(v_unused_3909_);
v___x_3897_ = v_a_3870_;
v_isShared_3898_ = v_isSharedCheck_3908_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_expr_3895_);
lean_dec(v_a_3870_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3908_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3902_; 
v___x_3899_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3900_ = l_Lean_indentExpr(v_expr_3895_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set_tag(v___x_3897_, 7);
lean_ctor_set(v___x_3897_, 1, v___x_3900_);
lean_ctor_set(v___x_3897_, 0, v___x_3899_);
v___x_3902_ = v___x_3897_;
goto v_reusejp_3901_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3899_);
lean_ctor_set(v_reuseFailAlloc_3907_, 1, v___x_3900_);
v___x_3902_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3901_;
}
v_reusejp_3901_:
{
lean_object* v___x_3904_; 
if (v_isShared_3884_ == 0)
{
lean_ctor_set_tag(v___x_3883_, 7);
lean_ctor_set(v___x_3883_, 1, v_a_3894_);
lean_ctor_set(v___x_3883_, 0, v___x_3902_);
v___x_3904_ = v___x_3883_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v___x_3902_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_a_3894_);
v___x_3904_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; 
v___x_3905_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3904_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
return v___x_3905_;
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3912_; uint8_t v_isShared_3913_; uint8_t v_isSharedCheck_3917_; 
lean_del_object(v___x_3883_);
lean_dec_ref(v_a_3870_);
v_a_3910_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3912_ = v___x_3893_;
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
else
{
lean_inc(v_a_3910_);
lean_dec(v___x_3893_);
v___x_3912_ = lean_box(0);
v_isShared_3913_ = v_isSharedCheck_3917_;
goto v_resetjp_3911_;
}
v_resetjp_3911_:
{
lean_object* v___x_3915_; 
if (v_isShared_3913_ == 0)
{
v___x_3915_ = v___x_3912_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v_a_3910_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
else
{
lean_object* v___x_3918_; lean_object* v___x_3920_; 
lean_del_object(v___x_3883_);
lean_dec_ref(v_expr_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3870_);
v___x_3918_ = lean_box(0);
if (v_isShared_3889_ == 0)
{
lean_ctor_set(v___x_3888_, 0, v___x_3918_);
v___x_3920_ = v___x_3888_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3918_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_del_object(v___x_3883_);
lean_dec_ref(v_expr_3881_);
lean_dec(v_a_3880_);
lean_dec_ref(v_a_3870_);
v_a_3923_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3885_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3885_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_dec_ref(v_a_3871_);
lean_dec_ref(v_a_3870_);
v_a_3933_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3879_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3879_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3941_, lean_object* v_a_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_){
_start:
{
lean_object* v_res_3950_; 
v_res_3950_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3941_, v_a_3942_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
lean_dec(v___y_3948_);
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec(v___y_3943_);
return v_res_3950_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3952_; lean_object* v___x_3953_; 
v___x_3952_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3953_ = l_Lean_stringToMessageData(v___x_3952_);
return v___x_3953_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_){
_start:
{
if (lean_obj_tag(v_e_3954_) == 5)
{
lean_object* v_fn_3962_; lean_object* v_arg_3963_; lean_object* v___x_3964_; 
v_fn_3962_ = lean_ctor_get(v_e_3954_, 0);
v_arg_3963_ = lean_ctor_get(v_e_3954_, 1);
lean_inc_ref(v_fn_3962_);
v___x_3964_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3962_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
if (lean_obj_tag(v___x_3964_) == 0)
{
lean_object* v_a_3965_; lean_object* v___x_3966_; 
v_a_3965_ = lean_ctor_get(v___x_3964_, 0);
lean_inc(v_a_3965_);
lean_dec_ref_known(v___x_3964_, 1);
lean_inc_ref(v_arg_3963_);
v___x_3966_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3963_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
if (lean_obj_tag(v___x_3966_) == 0)
{
lean_object* v_a_3967_; lean_object* v___x_3969_; uint8_t v_isShared_3970_; uint8_t v_isSharedCheck_3987_; 
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3969_ = v___x_3966_;
v_isShared_3970_ = v_isSharedCheck_3987_;
goto v_resetjp_3968_;
}
else
{
lean_inc(v_a_3967_);
lean_dec(v___x_3966_);
v___x_3969_ = lean_box(0);
v_isShared_3970_ = v_isSharedCheck_3987_;
goto v_resetjp_3968_;
}
v_resetjp_3968_:
{
lean_object* v_expr_3971_; uint8_t v___y_3973_; size_t v___x_3981_; size_t v___x_3982_; uint8_t v___x_3983_; 
v_expr_3971_ = lean_ctor_get(v_a_3967_, 0);
lean_inc_ref(v_expr_3971_);
lean_dec(v_a_3967_);
v___x_3981_ = lean_ptr_addr(v_fn_3962_);
v___x_3982_ = lean_ptr_addr(v_a_3965_);
v___x_3983_ = lean_usize_dec_eq(v___x_3981_, v___x_3982_);
if (v___x_3983_ == 0)
{
v___y_3973_ = v___x_3983_;
goto v___jp_3972_;
}
else
{
size_t v___x_3984_; size_t v___x_3985_; uint8_t v___x_3986_; 
v___x_3984_ = lean_ptr_addr(v_arg_3963_);
v___x_3985_ = lean_ptr_addr(v_expr_3971_);
v___x_3986_ = lean_usize_dec_eq(v___x_3984_, v___x_3985_);
v___y_3973_ = v___x_3986_;
goto v___jp_3972_;
}
v___jp_3972_:
{
if (v___y_3973_ == 0)
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
lean_dec_ref_known(v_e_3954_, 2);
v___x_3974_ = l_Lean_Expr_app___override(v_a_3965_, v_expr_3971_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v___x_3974_);
v___x_3976_ = v___x_3969_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3977_; 
v_reuseFailAlloc_3977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3977_, 0, v___x_3974_);
v___x_3976_ = v_reuseFailAlloc_3977_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
return v___x_3976_;
}
}
else
{
lean_object* v___x_3979_; 
lean_dec_ref(v_expr_3971_);
lean_dec(v_a_3965_);
if (v_isShared_3970_ == 0)
{
lean_ctor_set(v___x_3969_, 0, v_e_3954_);
v___x_3979_ = v___x_3969_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_e_3954_);
v___x_3979_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
return v___x_3979_;
}
}
}
}
}
else
{
lean_object* v_a_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3995_; 
lean_dec(v_a_3965_);
lean_dec_ref_known(v_e_3954_, 2);
v_a_3988_ = lean_ctor_get(v___x_3966_, 0);
v_isSharedCheck_3995_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3995_ == 0)
{
v___x_3990_ = v___x_3966_;
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_a_3988_);
lean_dec(v___x_3966_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3995_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3993_; 
if (v_isShared_3991_ == 0)
{
v___x_3993_ = v___x_3990_;
goto v_reusejp_3992_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
v___x_3993_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3992_;
}
v_reusejp_3992_:
{
return v___x_3993_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3954_, 2);
return v___x_3964_;
}
}
else
{
lean_object* v___x_3996_; 
v___x_3996_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3954_, v_a_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_);
if (lean_obj_tag(v___x_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4005_; 
v_a_3997_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3999_ = v___x_3996_;
v_isShared_4000_ = v_isSharedCheck_4005_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4005_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v_expr_4001_; lean_object* v___x_4003_; 
v_expr_4001_ = lean_ctor_get(v_a_3997_, 0);
lean_inc_ref(v_expr_4001_);
lean_dec(v_a_3997_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v_expr_4001_);
v___x_4003_ = v___x_3999_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_expr_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
v_a_4006_ = lean_ctor_get(v___x_3996_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___x_3996_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___x_3996_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec(v_a_4016_);
lean_dec(v_a_4015_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_){
_start:
{
if (lean_obj_tag(v_e_4023_) == 5)
{
lean_object* v_fn_4031_; lean_object* v_arg_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_fn_4031_ = lean_ctor_get(v_e_4023_, 0);
v_arg_4032_ = lean_ctor_get(v_e_4023_, 1);
lean_inc_ref_n(v_fn_4031_, 2);
v___x_4033_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_4033_, 0, v_fn_4031_);
v___x_4034_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_4031_, v___x_4033_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4036_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
lean_inc_ref(v_arg_4032_);
v___x_4036_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_4032_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4038_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v___x_4038_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_4023_, v_a_4035_, v_a_4037_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
return v___x_4038_;
}
else
{
lean_dec(v_a_4035_);
lean_dec_ref_known(v_e_4023_, 2);
return v___x_4036_;
}
}
else
{
lean_dec_ref_known(v_e_4023_, 2);
return v___x_4034_;
}
}
else
{
lean_object* v___x_4039_; 
v___x_4039_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_, v_a_4028_, v_a_4029_);
return v___x_4039_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_4040_, lean_object* v_a_4041_, lean_object* v_a_4042_, lean_object* v_a_4043_, lean_object* v_a_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_){
_start:
{
uint8_t v___x_4048_; 
v___x_4048_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_4041_);
if (v___x_4048_ == 0)
{
lean_object* v___x_4049_; 
v___x_4049_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4059_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4059_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4057_; 
v___x_4054_ = lean_box(0);
v___x_4055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4055_, 0, v_a_4050_);
lean_ctor_set(v___x_4055_, 1, v___x_4054_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4055_);
v___x_4057_ = v___x_4052_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v___x_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4049_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4049_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
else
{
lean_object* v___x_4068_; 
v___x_4068_ = l_Lean_Expr_getAppFn(v_e_4040_);
if (lean_obj_tag(v___x_4068_) == 2)
{
lean_object* v_mvarId_4069_; lean_object* v_dummy_4070_; lean_object* v_nargs_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_mvarId_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc(v_mvarId_4069_);
lean_dec_ref_known(v___x_4068_, 1);
v_dummy_4070_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_4071_ = l_Lean_Expr_getAppNumArgs(v_e_4040_);
lean_inc(v_nargs_4071_);
v___x_4072_ = lean_mk_array(v_nargs_4071_, v_dummy_4070_);
v___x_4073_ = lean_unsigned_to_nat(1u);
v___x_4074_ = lean_nat_sub(v_nargs_4071_, v___x_4073_);
lean_dec(v_nargs_4071_);
lean_inc_ref(v_e_4040_);
v___x_4075_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4040_, v___x_4072_, v___x_4074_);
v___x_4076_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_4069_, v___x_4075_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
lean_dec(v_mvarId_4069_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v___x_4077_; 
lean_dec_ref_known(v___x_4076_, 1);
v___x_4077_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
return v___x_4077_;
}
else
{
lean_object* v_a_4078_; lean_object* v___x_4080_; uint8_t v_isShared_4081_; uint8_t v_isSharedCheck_4085_; 
lean_dec_ref(v_e_4040_);
v_a_4078_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4085_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4085_ == 0)
{
v___x_4080_ = v___x_4076_;
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
else
{
lean_inc(v_a_4078_);
lean_dec(v___x_4076_);
v___x_4080_ = lean_box(0);
v_isShared_4081_ = v_isSharedCheck_4085_;
goto v_resetjp_4079_;
}
v_resetjp_4079_:
{
lean_object* v___x_4083_; 
if (v_isShared_4081_ == 0)
{
v___x_4083_ = v___x_4080_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4084_; 
v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
v___x_4083_ = v_reuseFailAlloc_4084_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
return v___x_4083_;
}
}
}
}
else
{
lean_object* v___x_4086_; 
lean_dec_ref(v___x_4068_);
v___x_4086_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_, v_a_4046_);
return v___x_4086_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_4087_, v_a_4088_, v_a_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
lean_dec(v_a_4089_);
lean_dec(v_a_4088_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_4096_, lean_object* v_a_4097_, lean_object* v_a_4098_, lean_object* v_a_4099_, lean_object* v_a_4100_, lean_object* v_a_4101_, lean_object* v_a_4102_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4096_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4106_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
lean_inc(v_a_4105_);
lean_dec_ref_known(v___x_4104_, 1);
v___x_4106_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_4105_, v_a_4097_, v_a_4098_, v_a_4099_, v_a_4100_, v_a_4101_, v_a_4102_);
return v___x_4106_;
}
else
{
return v___x_4104_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_4107_, lean_object* v_a_4108_, lean_object* v_a_4109_, lean_object* v_a_4110_, lean_object* v_a_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_4107_, v_a_4108_, v_a_4109_, v_a_4110_, v_a_4111_, v_a_4112_, v_a_4113_);
lean_dec(v_a_4113_);
lean_dec_ref(v_a_4112_);
lean_dec(v_a_4111_);
lean_dec_ref(v_a_4110_);
lean_dec(v_a_4109_);
lean_dec(v_a_4108_);
return v_res_4115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_4116_, lean_object* v_fvars_4117_, lean_object* v_doms_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___x_4126_; 
v___x_4126_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_4116_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
if (lean_obj_tag(v___x_4126_) == 0)
{
lean_object* v_a_4127_; lean_object* v___x_4128_; 
v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc(v_a_4127_);
lean_dec_ref_known(v___x_4126_, 1);
v___x_4128_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_4117_, v_doms_4118_, v_a_4127_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
return v___x_4128_;
}
else
{
return v___x_4126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_4129_, lean_object* v_fvars_4130_, lean_object* v_doms_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_, lean_object* v___y_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_){
_start:
{
lean_object* v_res_4139_; 
v_res_4139_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_4129_, v_fvars_4130_, v_doms_4131_, v___y_4132_, v___y_4133_, v___y_4134_, v___y_4135_, v___y_4136_, v___y_4137_);
lean_dec(v___y_4137_);
lean_dec_ref(v___y_4136_);
lean_dec(v___y_4135_);
lean_dec_ref(v___y_4134_);
lean_dec(v___y_4133_);
lean_dec(v___y_4132_);
lean_dec_ref(v_doms_4131_);
lean_dec_ref(v_fvars_4130_);
return v_res_4139_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_4140_, lean_object* v_fvars_4141_, lean_object* v_doms_4142_, lean_object* v_e_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_4143_, v_a_4145_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
if (lean_obj_tag(v_a_4152_) == 1)
{
lean_object* v_val_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
lean_dec_ref(v_e_4143_);
v_val_4153_ = lean_ctor_get(v_a_4152_, 0);
lean_inc(v_val_4153_);
lean_dec_ref_known(v_a_4152_, 1);
v___x_4154_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_4155_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_4155_, 0, v_fvars_4141_);
lean_closure_set(v___x_4155_, 1, v_doms_4142_);
lean_closure_set(v___x_4155_, 2, v_val_4153_);
v___x_4156_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4140_, v___x_4154_, v___x_4155_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
return v___x_4156_;
}
else
{
lean_dec(v_a_4152_);
if (lean_obj_tag(v_e_4143_) == 7)
{
lean_object* v_binderName_4157_; lean_object* v_binderType_4158_; lean_object* v_body_4159_; uint8_t v_binderInfo_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_binderName_4157_ = lean_ctor_get(v_e_4143_, 0);
lean_inc(v_binderName_4157_);
v_binderType_4158_ = lean_ctor_get(v_e_4143_, 1);
lean_inc_ref(v_binderType_4158_);
v_body_4159_ = lean_ctor_get(v_e_4143_, 2);
lean_inc_ref(v_body_4159_);
v_binderInfo_4160_ = lean_ctor_get_uint8(v_e_4143_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4143_, 3);
v___x_4161_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_4162_ = lean_expr_instantiate_rev(v_binderType_4158_, v_fvars_4141_);
lean_dec_ref(v_binderType_4158_);
v___x_4163_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_4163_, 0, v___x_4162_);
lean_inc_ref(v_lctx_4140_);
v___x_4164_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4140_, v___x_4161_, v___x_4163_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
if (lean_obj_tag(v___x_4164_) == 0)
{
lean_object* v_a_4165_; lean_object* v___x_4166_; 
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
lean_inc(v_a_4165_);
lean_dec_ref_known(v___x_4164_, 1);
v___x_4166_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
if (lean_obj_tag(v___x_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v_expr_4168_; uint8_t v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; 
v_a_4167_ = lean_ctor_get(v___x_4166_, 0);
lean_inc_n(v_a_4167_, 2);
lean_dec_ref_known(v___x_4166_, 1);
v_expr_4168_ = lean_ctor_get(v_a_4165_, 0);
v___x_4169_ = 0;
lean_inc_ref(v_expr_4168_);
v___x_4170_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4140_, v_a_4167_, v_binderName_4157_, v_expr_4168_, v_binderInfo_4160_, v___x_4169_);
v___x_4171_ = l_Lean_Expr_fvar___override(v_a_4167_);
v___x_4172_ = lean_array_push(v_fvars_4141_, v___x_4171_);
v___x_4173_ = lean_array_push(v_doms_4142_, v_a_4165_);
v_lctx_4140_ = v___x_4170_;
v_fvars_4141_ = v___x_4172_;
v_doms_4142_ = v___x_4173_;
v_e_4143_ = v_body_4159_;
goto _start;
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_dec(v_a_4165_);
lean_dec_ref(v_body_4159_);
lean_dec(v_binderName_4157_);
lean_dec_ref(v_doms_4142_);
lean_dec_ref(v_fvars_4141_);
lean_dec_ref(v_lctx_4140_);
v_a_4175_ = lean_ctor_get(v___x_4166_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4166_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4166_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4166_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_dec_ref(v_body_4159_);
lean_dec(v_binderName_4157_);
lean_dec_ref(v_doms_4142_);
lean_dec_ref(v_fvars_4141_);
lean_dec_ref(v_lctx_4140_);
return v___x_4164_;
}
}
else
{
lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___f_4185_; lean_object* v___x_4186_; 
v___x_4183_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_4184_ = lean_expr_instantiate_rev(v_e_4143_, v_fvars_4141_);
lean_dec_ref(v_e_4143_);
v___f_4185_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_4185_, 0, v___x_4184_);
lean_closure_set(v___f_4185_, 1, v_fvars_4141_);
lean_closure_set(v___f_4185_, 2, v_doms_4142_);
v___x_4186_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4140_, v___x_4183_, v___f_4185_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
return v___x_4186_;
}
}
}
else
{
lean_object* v_a_4187_; lean_object* v___x_4189_; uint8_t v_isShared_4190_; uint8_t v_isSharedCheck_4194_; 
lean_dec_ref(v_e_4143_);
lean_dec_ref(v_doms_4142_);
lean_dec_ref(v_fvars_4141_);
lean_dec_ref(v_lctx_4140_);
v_a_4187_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4194_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4194_ == 0)
{
v___x_4189_ = v___x_4151_;
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
else
{
lean_inc(v_a_4187_);
lean_dec(v___x_4151_);
v___x_4189_ = lean_box(0);
v_isShared_4190_ = v_isSharedCheck_4194_;
goto v_resetjp_4188_;
}
v_resetjp_4188_:
{
lean_object* v___x_4192_; 
if (v_isShared_4190_ == 0)
{
v___x_4192_ = v___x_4189_;
goto v_reusejp_4191_;
}
else
{
lean_object* v_reuseFailAlloc_4193_; 
v_reuseFailAlloc_4193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4193_, 0, v_a_4187_);
v___x_4192_ = v_reuseFailAlloc_4193_;
goto v_reusejp_4191_;
}
v_reusejp_4191_:
{
return v___x_4192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_4195_, lean_object* v_a_4196_, lean_object* v_a_4197_, lean_object* v_a_4198_, lean_object* v_a_4199_, lean_object* v_a_4200_, lean_object* v_a_4201_){
_start:
{
uint32_t v___x_4203_; uint8_t v___x_4204_; 
v___x_4203_ = 5;
v___x_4204_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4195_, v___x_4203_);
if (v___x_4204_ == 0)
{
lean_object* v_lctx_4205_; lean_object* v___x_4206_; lean_object* v___x_4207_; 
v_lctx_4205_ = lean_ctor_get(v_a_4198_, 2);
v___x_4206_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_4205_);
v___x_4207_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4205_, v___x_4206_, v___x_4206_, v_e_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_);
return v___x_4207_;
}
else
{
lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
v___x_4208_ = lean_box(0);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v_e_4195_);
lean_ctor_set(v___x_4209_, 1, v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
return v___x_4210_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_){
_start:
{
lean_object* v_res_4219_; 
v_res_4219_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_4211_, v_a_4212_, v_a_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_);
lean_dec(v_a_4217_);
lean_dec_ref(v_a_4216_);
lean_dec(v_a_4215_);
lean_dec_ref(v_a_4214_);
lean_dec(v_a_4213_);
lean_dec(v_a_4212_);
return v_res_4219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_4220_, lean_object* v_e_4221_, lean_object* v_typeName_4222_, lean_object* v_idx_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_res_4231_; 
v_res_4231_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_4220_, v_e_4221_, v_typeName_4222_, v_idx_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
lean_dec(v___y_4229_);
lean_dec_ref(v___y_4228_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec(v___y_4224_);
return v_res_4231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_4232_, lean_object* v_a_4233_, lean_object* v_a_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4232_, v_a_4233_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
lean_dec(v_a_4234_);
lean_dec(v_a_4233_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_){
_start:
{
lean_object* v___x_4250_; 
v___x_4250_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v_a_4251_; lean_object* v___x_4252_; 
v_a_4251_ = lean_ctor_get(v___x_4250_, 0);
lean_inc(v_a_4251_);
lean_dec_ref_known(v___x_4250_, 1);
v___x_4252_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4241_, v_a_4251_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_, v___y_4247_, v___y_4248_);
return v___x_4252_;
}
else
{
lean_dec_ref(v_fvars_4241_);
return v___x_4250_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_){
_start:
{
lean_object* v_res_4262_; 
v_res_4262_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_, v___y_4260_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
lean_dec(v___y_4258_);
lean_dec_ref(v___y_4257_);
lean_dec(v___y_4256_);
lean_dec(v___y_4255_);
return v_res_4262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4263_, lean_object* v_fvars_4264_, lean_object* v_e_4265_, lean_object* v_letFVars_4266_, lean_object* v_a_4267_, lean_object* v_a_4268_, lean_object* v_a_4269_, lean_object* v_a_4270_, lean_object* v_a_4271_, lean_object* v_a_4272_){
_start:
{
switch(lean_obj_tag(v_e_4265_))
{
case 6:
{
lean_object* v_binderName_4274_; lean_object* v_binderType_4275_; lean_object* v_body_4276_; uint8_t v_binderInfo_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; 
v_binderName_4274_ = lean_ctor_get(v_e_4265_, 0);
lean_inc(v_binderName_4274_);
v_binderType_4275_ = lean_ctor_get(v_e_4265_, 1);
lean_inc_ref(v_binderType_4275_);
v_body_4276_ = lean_ctor_get(v_e_4265_, 2);
lean_inc_ref(v_body_4276_);
v_binderInfo_4277_ = lean_ctor_get_uint8(v_e_4265_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4265_, 3);
v___x_4278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4263_);
lean_inc(v_letFVars_4266_);
v___x_4279_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4264_, v_letFVars_4266_, v_lctx_4263_, v___x_4278_, v_binderType_4275_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec_ref(v_binderType_4275_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v_a_4280_; lean_object* v___x_4281_; 
v_a_4280_ = lean_ctor_get(v___x_4279_, 0);
lean_inc(v_a_4280_);
lean_dec_ref_known(v___x_4279_, 1);
v___x_4281_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; lean_object* v_expr_4283_; uint8_t v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc_n(v_a_4282_, 2);
lean_dec_ref_known(v___x_4281_, 1);
v_expr_4283_ = lean_ctor_get(v_a_4280_, 0);
lean_inc_ref(v_expr_4283_);
lean_dec(v_a_4280_);
v___x_4284_ = 0;
v___x_4285_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4263_, v_a_4282_, v_binderName_4274_, v_expr_4283_, v_binderInfo_4277_, v___x_4284_);
v___x_4286_ = l_Lean_Expr_fvar___override(v_a_4282_);
v___x_4287_ = lean_array_push(v_fvars_4264_, v___x_4286_);
v_lctx_4263_ = v___x_4285_;
v_fvars_4264_ = v___x_4287_;
v_e_4265_ = v_body_4276_;
goto _start;
}
else
{
lean_object* v_a_4289_; lean_object* v___x_4291_; uint8_t v_isShared_4292_; uint8_t v_isSharedCheck_4296_; 
lean_dec(v_a_4280_);
lean_dec_ref(v_body_4276_);
lean_dec(v_binderName_4274_);
lean_dec(v_letFVars_4266_);
lean_dec_ref(v_fvars_4264_);
lean_dec_ref(v_lctx_4263_);
v_a_4289_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4296_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4296_ == 0)
{
v___x_4291_ = v___x_4281_;
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
else
{
lean_inc(v_a_4289_);
lean_dec(v___x_4281_);
v___x_4291_ = lean_box(0);
v_isShared_4292_ = v_isSharedCheck_4296_;
goto v_resetjp_4290_;
}
v_resetjp_4290_:
{
lean_object* v___x_4294_; 
if (v_isShared_4292_ == 0)
{
v___x_4294_ = v___x_4291_;
goto v_reusejp_4293_;
}
else
{
lean_object* v_reuseFailAlloc_4295_; 
v_reuseFailAlloc_4295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4295_, 0, v_a_4289_);
v___x_4294_ = v_reuseFailAlloc_4295_;
goto v_reusejp_4293_;
}
v_reusejp_4293_:
{
return v___x_4294_;
}
}
}
}
else
{
lean_dec_ref(v_body_4276_);
lean_dec(v_binderName_4274_);
lean_dec(v_letFVars_4266_);
lean_dec_ref(v_fvars_4264_);
lean_dec_ref(v_lctx_4263_);
return v___x_4279_;
}
}
case 8:
{
lean_object* v_declName_4297_; lean_object* v_type_4298_; lean_object* v_value_4299_; lean_object* v_body_4300_; uint8_t v_nondep_4301_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4307_; lean_object* v___y_4308_; lean_object* v___y_4309_; lean_object* v___y_4310_; lean_object* v___y_4311_; lean_object* v___x_4315_; lean_object* v___x_4316_; 
v_declName_4297_ = lean_ctor_get(v_e_4265_, 0);
lean_inc(v_declName_4297_);
v_type_4298_ = lean_ctor_get(v_e_4265_, 1);
lean_inc_ref(v_type_4298_);
v_value_4299_ = lean_ctor_get(v_e_4265_, 2);
lean_inc_ref(v_value_4299_);
v_body_4300_ = lean_ctor_get(v_e_4265_, 3);
lean_inc_ref(v_body_4300_);
v_nondep_4301_ = lean_ctor_get_uint8(v_e_4265_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4265_, 4);
v___x_4315_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4263_);
lean_inc(v_letFVars_4266_);
v___x_4316_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4264_, v_letFVars_4266_, v_lctx_4263_, v___x_4315_, v_type_4298_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec_ref(v_type_4298_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4263_);
lean_inc(v_letFVars_4266_);
v___x_4319_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4264_, v_letFVars_4266_, v_lctx_4263_, v___x_4318_, v_value_4299_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec_ref(v_value_4299_);
if (lean_obj_tag(v___x_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; uint8_t v___x_4350_; 
v_a_4320_ = lean_ctor_get(v___x_4319_, 0);
lean_inc(v_a_4320_);
lean_dec_ref_known(v___x_4319_, 1);
v___x_4350_ = l_List_isEmpty___redArg(v_letFVars_4266_);
if (v___x_4350_ == 0)
{
lean_object* v___f_4351_; lean_object* v___x_4352_; 
lean_inc(v_a_4317_);
lean_inc(v_a_4320_);
v___f_4351_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4351_, 0, v_a_4320_);
lean_closure_set(v___f_4351_, 1, v_a_4317_);
lean_inc_ref(v_lctx_4263_);
v___x_4352_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4263_, v___f_4351_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_dec_ref_known(v___x_4352_, 1);
v___y_4322_ = v_a_4267_;
v___y_4323_ = v_a_4268_;
v___y_4324_ = v_a_4269_;
v___y_4325_ = v_a_4270_;
v___y_4326_ = v_a_4271_;
v___y_4327_ = v_a_4272_;
goto v___jp_4321_;
}
else
{
lean_object* v_a_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4360_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4317_);
lean_dec_ref(v_body_4300_);
lean_dec(v_declName_4297_);
lean_dec(v_letFVars_4266_);
lean_dec_ref(v_fvars_4264_);
lean_dec_ref(v_lctx_4263_);
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4355_ = v___x_4352_;
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_a_4353_);
lean_dec(v___x_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4360_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4358_; 
if (v_isShared_4356_ == 0)
{
v___x_4358_ = v___x_4355_;
goto v_reusejp_4357_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v_a_4353_);
v___x_4358_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4357_;
}
v_reusejp_4357_:
{
return v___x_4358_;
}
}
}
}
else
{
v___y_4322_ = v_a_4267_;
v___y_4323_ = v_a_4268_;
v___y_4324_ = v_a_4269_;
v___y_4325_ = v_a_4270_;
v___y_4326_ = v_a_4271_;
v___y_4327_ = v_a_4272_;
goto v___jp_4321_;
}
v___jp_4321_:
{
lean_object* v___x_4328_; 
v___x_4328_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_, v___y_4326_, v___y_4327_);
if (lean_obj_tag(v___x_4328_) == 0)
{
lean_object* v_a_4329_; lean_object* v_expr_4330_; lean_object* v_expr_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4340_; 
v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
lean_inc(v_a_4329_);
lean_dec_ref_known(v___x_4328_, 1);
v_expr_4330_ = lean_ctor_get(v_a_4317_, 0);
lean_inc_ref(v_expr_4330_);
lean_dec(v_a_4317_);
v_expr_4331_ = lean_ctor_get(v_a_4320_, 0);
v_isSharedCheck_4340_ = !lean_is_exclusive(v_a_4320_);
if (v_isSharedCheck_4340_ == 0)
{
lean_object* v_unused_4341_; 
v_unused_4341_ = lean_ctor_get(v_a_4320_, 1);
lean_dec(v_unused_4341_);
v___x_4333_ = v_a_4320_;
v_isShared_4334_ = v_isSharedCheck_4340_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_expr_4331_);
lean_dec(v_a_4320_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4340_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
uint8_t v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = 0;
lean_inc(v_a_4329_);
v___x_4336_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4263_, v_a_4329_, v_declName_4297_, v_expr_4330_, v_expr_4331_, v_nondep_4301_, v___x_4335_);
if (v_nondep_4301_ == 0)
{
lean_object* v___x_4338_; 
lean_inc(v_a_4329_);
if (v_isShared_4334_ == 0)
{
lean_ctor_set_tag(v___x_4333_, 1);
lean_ctor_set(v___x_4333_, 1, v_letFVars_4266_);
lean_ctor_set(v___x_4333_, 0, v_a_4329_);
v___x_4338_ = v___x_4333_;
goto v_reusejp_4337_;
}
else
{
lean_object* v_reuseFailAlloc_4339_; 
v_reuseFailAlloc_4339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4339_, 0, v_a_4329_);
lean_ctor_set(v_reuseFailAlloc_4339_, 1, v_letFVars_4266_);
v___x_4338_ = v_reuseFailAlloc_4339_;
goto v_reusejp_4337_;
}
v_reusejp_4337_:
{
v___y_4303_ = v___y_4326_;
v___y_4304_ = v___x_4336_;
v___y_4305_ = v___y_4323_;
v___y_4306_ = v___y_4322_;
v___y_4307_ = v___y_4327_;
v___y_4308_ = v_a_4329_;
v___y_4309_ = v___y_4325_;
v___y_4310_ = v___y_4324_;
v___y_4311_ = v___x_4338_;
goto v___jp_4302_;
}
}
else
{
lean_del_object(v___x_4333_);
v___y_4303_ = v___y_4326_;
v___y_4304_ = v___x_4336_;
v___y_4305_ = v___y_4323_;
v___y_4306_ = v___y_4322_;
v___y_4307_ = v___y_4327_;
v___y_4308_ = v_a_4329_;
v___y_4309_ = v___y_4325_;
v___y_4310_ = v___y_4324_;
v___y_4311_ = v_letFVars_4266_;
goto v___jp_4302_;
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
lean_dec(v_a_4320_);
lean_dec(v_a_4317_);
lean_dec_ref(v_body_4300_);
lean_dec(v_declName_4297_);
lean_dec(v_letFVars_4266_);
lean_dec_ref(v_fvars_4264_);
lean_dec_ref(v_lctx_4263_);
v_a_4342_ = lean_ctor_get(v___x_4328_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4328_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4328_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4328_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
}
else
{
lean_dec(v_a_4317_);
lean_dec_ref(v_body_4300_);
lean_dec(v_declName_4297_);
lean_dec(v_letFVars_4266_);
lean_dec_ref(v_fvars_4264_);
lean_dec_ref(v_lctx_4263_);
return v___x_4319_;
}
}
else
{
lean_dec_ref(v_body_4300_);
lean_dec_ref(v_value_4299_);
lean_dec(v_declName_4297_);
lean_dec(v_letFVars_4266_);
lean_dec_ref(v_fvars_4264_);
lean_dec_ref(v_lctx_4263_);
return v___x_4316_;
}
v___jp_4302_:
{
lean_object* v___x_4312_; lean_object* v___x_4313_; 
v___x_4312_ = l_Lean_Expr_fvar___override(v___y_4308_);
v___x_4313_ = lean_array_push(v_fvars_4264_, v___x_4312_);
v_lctx_4263_ = v___y_4304_;
v_fvars_4264_ = v___x_4313_;
v_e_4265_ = v_body_4300_;
v_letFVars_4266_ = v___y_4311_;
v_a_4267_ = v___y_4306_;
v_a_4268_ = v___y_4305_;
v_a_4269_ = v___y_4310_;
v_a_4270_ = v___y_4309_;
v_a_4271_ = v___y_4303_;
v_a_4272_ = v___y_4307_;
goto _start;
}
}
default: 
{
lean_object* v___f_4361_; lean_object* v___x_4362_; 
lean_inc_ref(v_fvars_4264_);
v___f_4361_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4361_, 0, v_fvars_4264_);
v___x_4362_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4264_, v_letFVars_4266_, v_lctx_4263_, v___f_4361_, v_e_4265_, v_a_4267_, v_a_4268_, v_a_4269_, v_a_4270_, v_a_4271_, v_a_4272_);
lean_dec_ref(v_e_4265_);
lean_dec_ref(v_fvars_4264_);
return v___x_4362_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_, lean_object* v_a_4366_, lean_object* v_a_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_){
_start:
{
uint32_t v___x_4371_; uint8_t v___x_4372_; 
v___x_4371_ = 5;
v___x_4372_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4363_, v___x_4371_);
if (v___x_4372_ == 0)
{
lean_object* v_lctx_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; 
v_lctx_4373_ = lean_ctor_get(v_a_4366_, 2);
v___x_4374_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4364_);
lean_inc_ref(v_lctx_4373_);
v___x_4375_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4373_, v___x_4374_, v_e_4363_, v_a_4364_, v_a_4364_, v_a_4365_, v_a_4366_, v_a_4367_, v_a_4368_, v_a_4369_);
return v___x_4375_;
}
else
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4376_ = lean_box(0);
v___x_4377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4377_, 0, v_e_4363_);
lean_ctor_set(v___x_4377_, 1, v___x_4376_);
v___x_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4378_, 0, v___x_4377_);
return v___x_4378_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4379_, lean_object* v_a_4380_, lean_object* v_a_4381_, lean_object* v_a_4382_, lean_object* v_a_4383_, lean_object* v_a_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_){
_start:
{
lean_object* v_res_4387_; 
v_res_4387_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_);
lean_dec(v_a_4385_);
lean_dec_ref(v_a_4384_);
lean_dec(v_a_4383_);
lean_dec_ref(v_a_4382_);
lean_dec(v_a_4381_);
lean_dec(v_a_4380_);
return v_res_4387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_){
_start:
{
switch(lean_obj_tag(v_e_4388_))
{
case 0:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; 
v___x_4396_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4397_ = l_Lean_MessageData_ofExpr(v_e_4388_);
v___x_4398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4396_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4398_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4399_;
}
case 1:
{
lean_object* v___x_4400_; 
v___x_4400_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4388_, v___y_4391_, v___y_4393_, v___y_4394_);
return v___x_4400_;
}
case 2:
{
lean_object* v___x_4401_; 
v___x_4401_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4401_;
}
case 3:
{
lean_object* v_u_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; 
v_u_4402_ = lean_ctor_get(v_e_4388_, 0);
lean_inc(v_u_4402_);
v___x_4403_ = l_Lean_Level_succ___override(v_u_4402_);
v___x_4404_ = l_Lean_Expr_sort___override(v___x_4403_);
v___x_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4405_, 0, v___x_4404_);
v___x_4406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4406_, 0, v_e_4388_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4406_);
return v___x_4407_;
}
case 4:
{
lean_object* v___x_4408_; 
v___x_4408_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4408_;
}
case 5:
{
lean_object* v___x_4409_; lean_object* v___x_4410_; 
lean_inc_ref(v_e_4388_);
v___x_4409_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4409_, 0, v_e_4388_);
v___x_4410_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4388_, v___x_4409_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4410_;
}
case 7:
{
lean_object* v___x_4411_; lean_object* v___x_4412_; 
lean_inc_ref(v_e_4388_);
v___x_4411_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4411_, 0, v_e_4388_);
v___x_4412_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4388_, v___x_4411_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4412_;
}
case 9:
{
lean_object* v_a_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; 
v_a_4413_ = lean_ctor_get(v_e_4388_, 0);
v___x_4414_ = l_Lean_Literal_type(v_a_4413_);
v___x_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4415_, 0, v___x_4414_);
v___x_4416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4416_, 0, v_e_4388_);
lean_ctor_set(v___x_4416_, 1, v___x_4415_);
v___x_4417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4417_, 0, v___x_4416_);
return v___x_4417_;
}
case 10:
{
lean_object* v_data_4418_; lean_object* v_expr_4419_; lean_object* v___x_4420_; 
v_data_4418_ = lean_ctor_get(v_e_4388_, 0);
v_expr_4419_ = lean_ctor_get(v_e_4388_, 1);
lean_inc_ref(v_expr_4419_);
v___x_4420_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4419_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4443_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4423_ = v___x_4420_;
v_isShared_4424_ = v_isSharedCheck_4443_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4443_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v_expr_4425_; lean_object* v_type_x3f_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4442_; 
v_expr_4425_ = lean_ctor_get(v_a_4421_, 0);
v_type_x3f_4426_ = lean_ctor_get(v_a_4421_, 1);
v_isSharedCheck_4442_ = !lean_is_exclusive(v_a_4421_);
if (v_isSharedCheck_4442_ == 0)
{
v___x_4428_ = v_a_4421_;
v_isShared_4429_ = v_isSharedCheck_4442_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_type_x3f_4426_);
lean_inc(v_expr_4425_);
lean_dec(v_a_4421_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4442_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___y_4431_; size_t v___x_4438_; size_t v___x_4439_; uint8_t v___x_4440_; 
v___x_4438_ = lean_ptr_addr(v_expr_4419_);
v___x_4439_ = lean_ptr_addr(v_expr_4425_);
v___x_4440_ = lean_usize_dec_eq(v___x_4438_, v___x_4439_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; 
lean_inc(v_data_4418_);
lean_dec_ref_known(v_e_4388_, 2);
v___x_4441_ = l_Lean_Expr_mdata___override(v_data_4418_, v_expr_4425_);
v___y_4431_ = v___x_4441_;
goto v___jp_4430_;
}
else
{
lean_dec_ref(v_expr_4425_);
v___y_4431_ = v_e_4388_;
goto v___jp_4430_;
}
v___jp_4430_:
{
lean_object* v___x_4433_; 
if (v_isShared_4429_ == 0)
{
lean_ctor_set(v___x_4428_, 0, v___y_4431_);
v___x_4433_ = v___x_4428_;
goto v_reusejp_4432_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v___y_4431_);
lean_ctor_set(v_reuseFailAlloc_4437_, 1, v_type_x3f_4426_);
v___x_4433_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4432_;
}
v_reusejp_4432_:
{
lean_object* v___x_4435_; 
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 0, v___x_4433_);
v___x_4435_ = v___x_4423_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v___x_4433_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4388_, 2);
return v___x_4420_;
}
}
case 11:
{
lean_object* v_typeName_4444_; lean_object* v_idx_4445_; lean_object* v_struct_4446_; lean_object* v___f_4447_; lean_object* v___x_4448_; 
v_typeName_4444_ = lean_ctor_get(v_e_4388_, 0);
v_idx_4445_ = lean_ctor_get(v_e_4388_, 1);
v_struct_4446_ = lean_ctor_get(v_e_4388_, 2);
lean_inc(v_idx_4445_);
lean_inc(v_typeName_4444_);
lean_inc_ref(v_e_4388_);
lean_inc_ref(v_struct_4446_);
v___f_4447_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4447_, 0, v_struct_4446_);
lean_closure_set(v___f_4447_, 1, v_e_4388_);
lean_closure_set(v___f_4447_, 2, v_typeName_4444_);
lean_closure_set(v___f_4447_, 3, v_idx_4445_);
v___x_4448_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4388_, v___f_4447_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4448_;
}
default: 
{
lean_object* v___x_4449_; lean_object* v___x_4450_; 
lean_inc_ref(v_e_4388_);
v___x_4449_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4449_, 0, v_e_4388_);
v___x_4450_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4388_, v___x_4449_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
return v___x_4450_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4451_; double v___x_4452_; 
v___x_4451_ = lean_unsigned_to_nat(1000000000u);
v___x_4452_ = lean_float_of_nat(v___x_4451_);
return v___x_4452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_, lean_object* v_a_4457_, lean_object* v_a_4458_, lean_object* v_a_4459_){
_start:
{
lean_object* v_options_4461_; uint8_t v_hasTrace_4462_; 
v_options_4461_ = lean_ctor_get(v_a_4458_, 2);
v_hasTrace_4462_ = lean_ctor_get_uint8(v_options_4461_, sizeof(void*)*1);
if (v_hasTrace_4462_ == 0)
{
lean_object* v___x_4463_; 
v___x_4463_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
return v___x_4463_;
}
else
{
lean_object* v_inheritedTraceOptions_4464_; lean_object* v___f_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; uint8_t v___x_4469_; lean_object* v___y_4471_; lean_object* v___y_4472_; lean_object* v_a_4473_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v_a_4488_; 
v_inheritedTraceOptions_4464_ = lean_ctor_get(v_a_4458_, 13);
lean_inc_ref(v_e_4453_);
v___f_4465_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4465_, 0, v_e_4453_);
v___x_4466_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4467_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4468_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4469_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4464_, v_options_4461_, v___x_4468_);
if (v___x_4469_ == 0)
{
lean_object* v___x_4546_; uint8_t v___x_4547_; 
v___x_4546_ = l_Lean_trace_profiler;
v___x_4547_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4461_, v___x_4546_);
if (v___x_4547_ == 0)
{
lean_object* v___x_4548_; 
lean_dec_ref(v___f_4465_);
v___x_4548_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
return v___x_4548_;
}
else
{
goto v___jp_4497_;
}
}
else
{
goto v___jp_4497_;
}
v___jp_4470_:
{
lean_object* v___x_4474_; double v___x_4475_; double v___x_4476_; double v___x_4477_; double v___x_4478_; double v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; 
v___x_4474_ = lean_io_mono_nanos_now();
v___x_4475_ = lean_float_of_nat(v___y_4472_);
v___x_4476_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4477_ = lean_float_div(v___x_4475_, v___x_4476_);
v___x_4478_ = lean_float_of_nat(v___x_4474_);
v___x_4479_ = lean_float_div(v___x_4478_, v___x_4476_);
v___x_4480_ = lean_box_float(v___x_4477_);
v___x_4481_ = lean_box_float(v___x_4479_);
v___x_4482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4483_, 0, v_a_4473_);
lean_ctor_set(v___x_4483_, 1, v___x_4482_);
v___x_4484_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4466_, v_hasTrace_4462_, v___x_4467_, v_options_4461_, v___x_4469_, v___y_4471_, v___f_4465_, v___x_4483_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
return v___x_4484_;
}
v___jp_4485_:
{
lean_object* v___x_4489_; double v___x_4490_; double v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; 
v___x_4489_ = lean_io_get_num_heartbeats();
v___x_4490_ = lean_float_of_nat(v___y_4486_);
v___x_4491_ = lean_float_of_nat(v___x_4489_);
v___x_4492_ = lean_box_float(v___x_4490_);
v___x_4493_ = lean_box_float(v___x_4491_);
v___x_4494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4494_, 0, v___x_4492_);
lean_ctor_set(v___x_4494_, 1, v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v_a_4488_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
v___x_4496_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4466_, v_hasTrace_4462_, v___x_4467_, v_options_4461_, v___x_4469_, v___y_4487_, v___f_4465_, v___x_4495_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
return v___x_4496_;
}
v___jp_4497_:
{
lean_object* v___x_4498_; 
v___x_4498_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4459_);
if (lean_obj_tag(v___x_4498_) == 0)
{
lean_object* v_a_4499_; lean_object* v___x_4500_; uint8_t v___x_4501_; 
v_a_4499_ = lean_ctor_get(v___x_4498_, 0);
lean_inc(v_a_4499_);
lean_dec_ref_known(v___x_4498_, 1);
v___x_4500_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4501_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4461_, v___x_4500_);
if (v___x_4501_ == 0)
{
lean_object* v___x_4502_; lean_object* v___x_4503_; 
v___x_4502_ = lean_io_mono_nanos_now();
v___x_4503_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4503_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4503_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
lean_ctor_set_tag(v___x_4506_, 1);
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
v___y_4471_ = v_a_4499_;
v___y_4472_ = v___x_4502_;
v_a_4473_ = v___x_4509_;
goto v___jp_4470_;
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
v_a_4512_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4503_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4503_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
lean_ctor_set_tag(v___x_4514_, 0);
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
v___y_4471_ = v_a_4499_;
v___y_4472_ = v___x_4502_;
v_a_4473_ = v___x_4517_;
goto v___jp_4470_;
}
}
}
}
else
{
lean_object* v___x_4520_; lean_object* v___x_4521_; 
v___x_4520_ = lean_io_get_num_heartbeats();
v___x_4521_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4453_, v_a_4454_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_, v_a_4459_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4524_; uint8_t v_isShared_4525_; uint8_t v_isSharedCheck_4529_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4529_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4529_ == 0)
{
v___x_4524_ = v___x_4521_;
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
else
{
lean_inc(v_a_4522_);
lean_dec(v___x_4521_);
v___x_4524_ = lean_box(0);
v_isShared_4525_ = v_isSharedCheck_4529_;
goto v_resetjp_4523_;
}
v_resetjp_4523_:
{
lean_object* v___x_4527_; 
if (v_isShared_4525_ == 0)
{
lean_ctor_set_tag(v___x_4524_, 1);
v___x_4527_ = v___x_4524_;
goto v_reusejp_4526_;
}
else
{
lean_object* v_reuseFailAlloc_4528_; 
v_reuseFailAlloc_4528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4528_, 0, v_a_4522_);
v___x_4527_ = v_reuseFailAlloc_4528_;
goto v_reusejp_4526_;
}
v_reusejp_4526_:
{
v___y_4486_ = v___x_4520_;
v___y_4487_ = v_a_4499_;
v_a_4488_ = v___x_4527_;
goto v___jp_4485_;
}
}
}
else
{
lean_object* v_a_4530_; lean_object* v___x_4532_; uint8_t v_isShared_4533_; uint8_t v_isSharedCheck_4537_; 
v_a_4530_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4532_ = v___x_4521_;
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
else
{
lean_inc(v_a_4530_);
lean_dec(v___x_4521_);
v___x_4532_ = lean_box(0);
v_isShared_4533_ = v_isSharedCheck_4537_;
goto v_resetjp_4531_;
}
v_resetjp_4531_:
{
lean_object* v___x_4535_; 
if (v_isShared_4533_ == 0)
{
lean_ctor_set_tag(v___x_4532_, 0);
v___x_4535_ = v___x_4532_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v_a_4530_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
v___y_4486_ = v___x_4520_;
v___y_4487_ = v_a_4499_;
v_a_4488_ = v___x_4535_;
goto v___jp_4485_;
}
}
}
}
}
else
{
lean_object* v_a_4538_; lean_object* v___x_4540_; uint8_t v_isShared_4541_; uint8_t v_isSharedCheck_4545_; 
lean_dec_ref(v___f_4465_);
lean_dec_ref(v_e_4453_);
v_a_4538_ = lean_ctor_get(v___x_4498_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4498_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4540_ = v___x_4498_;
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
else
{
lean_inc(v_a_4538_);
lean_dec(v___x_4498_);
v___x_4540_ = lean_box(0);
v_isShared_4541_ = v_isSharedCheck_4545_;
goto v_resetjp_4539_;
}
v_resetjp_4539_:
{
lean_object* v___x_4543_; 
if (v_isShared_4541_ == 0)
{
v___x_4543_ = v___x_4540_;
goto v_reusejp_4542_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_a_4538_);
v___x_4543_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4542_;
}
v_reusejp_4542_:
{
return v___x_4543_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4549_, lean_object* v_e_4550_, lean_object* v_typeName_4551_, lean_object* v_idx_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v___x_4560_; 
v___x_4560_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4549_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4562_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref_known(v___x_4560_, 1);
v___x_4562_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4550_, v_typeName_4551_, v_idx_4552_, v_a_4561_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
return v___x_4562_;
}
else
{
lean_dec(v_idx_4552_);
lean_dec(v_typeName_4551_);
lean_dec_ref(v_e_4550_);
return v___x_4560_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_, lean_object* v_a_4567_, lean_object* v_a_4568_, lean_object* v_a_4569_, lean_object* v_a_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4563_, v_a_4564_, v_a_4565_, v_a_4566_, v_a_4567_, v_a_4568_, v_a_4569_);
lean_dec(v_a_4569_);
lean_dec_ref(v_a_4568_);
lean_dec(v_a_4567_);
lean_dec_ref(v_a_4566_);
lean_dec(v_a_4565_);
lean_dec(v_a_4564_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4572_, lean_object* v_fvars_4573_, lean_object* v_doms_4574_, lean_object* v_e_4575_, lean_object* v_a_4576_, lean_object* v_a_4577_, lean_object* v_a_4578_, lean_object* v_a_4579_, lean_object* v_a_4580_, lean_object* v_a_4581_, lean_object* v_a_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4572_, v_fvars_4573_, v_doms_4574_, v_e_4575_, v_a_4576_, v_a_4577_, v_a_4578_, v_a_4579_, v_a_4580_, v_a_4581_);
lean_dec(v_a_4581_);
lean_dec_ref(v_a_4580_);
lean_dec(v_a_4579_);
lean_dec_ref(v_a_4578_);
lean_dec(v_a_4577_);
lean_dec(v_a_4576_);
return v_res_4583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
lean_object* v_res_4592_; 
v_res_4592_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4584_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4586_);
lean_dec(v___y_4585_);
return v_res_4592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4593_, lean_object* v_fvars_4594_, lean_object* v_e_4595_, lean_object* v_letFVars_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_, lean_object* v_a_4603_){
_start:
{
lean_object* v_res_4604_; 
v_res_4604_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4593_, v_fvars_4594_, v_e_4595_, v_letFVars_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_, v_a_4602_);
lean_dec(v_a_4602_);
lean_dec_ref(v_a_4601_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec(v_a_4597_);
return v_res_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4605_, lean_object* v_lctx_4606_, lean_object* v_localInsts_4607_, lean_object* v_x_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4606_, v_localInsts_4607_, v_x_4608_, v___y_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4617_, lean_object* v_lctx_4618_, lean_object* v_localInsts_4619_, lean_object* v_x_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_){
_start:
{
lean_object* v_res_4628_; 
v_res_4628_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4617_, v_lctx_4618_, v_localInsts_4619_, v_x_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec(v___y_4621_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4629_, lean_object* v_lctx_4630_, lean_object* v_x_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
lean_object* v___x_4639_; 
v___x_4639_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4630_, v_x_4631_, v___y_4632_, v___y_4633_, v___y_4634_, v___y_4635_, v___y_4636_, v___y_4637_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4640_, lean_object* v_lctx_4641_, lean_object* v_x_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4640_, v_lctx_4641_, v_x_4642_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec(v___y_4644_);
lean_dec(v___y_4643_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v___x_4658_; 
v___x_4658_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4656_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec(v___y_4660_);
lean_dec(v___y_4659_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v___x_4674_; 
v___x_4674_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4672_);
return v___x_4674_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_, v___y_4679_, v___y_4680_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v___y_4678_);
lean_dec_ref(v___y_4677_);
lean_dec(v___y_4676_);
lean_dec(v___y_4675_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4683_, lean_object* v_x_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v___x_4692_; 
v___x_4692_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4684_);
return v___x_4692_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4693_, lean_object* v_x_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_, lean_object* v___y_4701_){
_start:
{
lean_object* v_res_4702_; 
v_res_4702_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4693_, v_x_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_, v___y_4700_);
lean_dec(v___y_4700_);
lean_dec_ref(v___y_4699_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec(v___y_4695_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4703_, lean_object* v_data_4704_, lean_object* v_ref_4705_, lean_object* v_msg_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v___x_4714_; 
v___x_4714_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4703_, v_data_4704_, v_ref_4705_, v_msg_4706_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4715_, lean_object* v_data_4716_, lean_object* v_ref_4717_, lean_object* v_msg_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_){
_start:
{
lean_object* v_res_4726_; 
v_res_4726_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4715_, v_data_4716_, v_ref_4717_, v_msg_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_, v___y_4723_, v___y_4724_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___y_4722_);
lean_dec_ref(v___y_4721_);
lean_dec(v___y_4720_);
lean_dec(v___y_4719_);
return v_res_4726_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; lean_object* v_traceState_4730_; lean_object* v_traces_4731_; lean_object* v___x_4732_; lean_object* v_traceState_4733_; lean_object* v_env_4734_; lean_object* v_nextMacroScope_4735_; lean_object* v_ngen_4736_; lean_object* v_auxDeclNGen_4737_; lean_object* v_cache_4738_; lean_object* v_messages_4739_; lean_object* v_infoState_4740_; lean_object* v_snapshotTasks_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4762_; 
v___x_4729_ = lean_st_ref_get(v___y_4727_);
v_traceState_4730_ = lean_ctor_get(v___x_4729_, 4);
lean_inc_ref(v_traceState_4730_);
lean_dec(v___x_4729_);
v_traces_4731_ = lean_ctor_get(v_traceState_4730_, 0);
lean_inc_ref(v_traces_4731_);
lean_dec_ref(v_traceState_4730_);
v___x_4732_ = lean_st_ref_take(v___y_4727_);
v_traceState_4733_ = lean_ctor_get(v___x_4732_, 4);
v_env_4734_ = lean_ctor_get(v___x_4732_, 0);
v_nextMacroScope_4735_ = lean_ctor_get(v___x_4732_, 1);
v_ngen_4736_ = lean_ctor_get(v___x_4732_, 2);
v_auxDeclNGen_4737_ = lean_ctor_get(v___x_4732_, 3);
v_cache_4738_ = lean_ctor_get(v___x_4732_, 5);
v_messages_4739_ = lean_ctor_get(v___x_4732_, 6);
v_infoState_4740_ = lean_ctor_get(v___x_4732_, 7);
v_snapshotTasks_4741_ = lean_ctor_get(v___x_4732_, 8);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4743_ = v___x_4732_;
v_isShared_4744_ = v_isSharedCheck_4762_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_snapshotTasks_4741_);
lean_inc(v_infoState_4740_);
lean_inc(v_messages_4739_);
lean_inc(v_cache_4738_);
lean_inc(v_traceState_4733_);
lean_inc(v_auxDeclNGen_4737_);
lean_inc(v_ngen_4736_);
lean_inc(v_nextMacroScope_4735_);
lean_inc(v_env_4734_);
lean_dec(v___x_4732_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4762_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
uint64_t v_tid_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4760_; 
v_tid_4745_ = lean_ctor_get_uint64(v_traceState_4733_, sizeof(void*)*1);
v_isSharedCheck_4760_ = !lean_is_exclusive(v_traceState_4733_);
if (v_isSharedCheck_4760_ == 0)
{
lean_object* v_unused_4761_; 
v_unused_4761_ = lean_ctor_get(v_traceState_4733_, 0);
lean_dec(v_unused_4761_);
v___x_4747_ = v_traceState_4733_;
v_isShared_4748_ = v_isSharedCheck_4760_;
goto v_resetjp_4746_;
}
else
{
lean_dec(v_traceState_4733_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4760_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4753_; 
v___x_4749_ = lean_unsigned_to_nat(32u);
v___x_4750_ = lean_mk_empty_array_with_capacity(v___x_4749_);
lean_dec_ref(v___x_4750_);
v___x_4751_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 0, v___x_4751_);
v___x_4753_ = v___x_4747_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v___x_4751_);
lean_ctor_set_uint64(v_reuseFailAlloc_4759_, sizeof(void*)*1, v_tid_4745_);
v___x_4753_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4755_; 
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 4, v___x_4753_);
v___x_4755_ = v___x_4743_;
goto v_reusejp_4754_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_env_4734_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_nextMacroScope_4735_);
lean_ctor_set(v_reuseFailAlloc_4758_, 2, v_ngen_4736_);
lean_ctor_set(v_reuseFailAlloc_4758_, 3, v_auxDeclNGen_4737_);
lean_ctor_set(v_reuseFailAlloc_4758_, 4, v___x_4753_);
lean_ctor_set(v_reuseFailAlloc_4758_, 5, v_cache_4738_);
lean_ctor_set(v_reuseFailAlloc_4758_, 6, v_messages_4739_);
lean_ctor_set(v_reuseFailAlloc_4758_, 7, v_infoState_4740_);
lean_ctor_set(v_reuseFailAlloc_4758_, 8, v_snapshotTasks_4741_);
v___x_4755_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4754_;
}
v_reusejp_4754_:
{
lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4756_ = lean_st_ref_put(v___y_4727_, v___x_4755_);
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v_traces_4731_);
return v___x_4757_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4763_);
lean_dec(v___y_4763_);
return v_res_4765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_, lean_object* v___y_4769_){
_start:
{
lean_object* v___x_4771_; 
v___x_4771_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4769_);
return v___x_4771_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v_res_4777_; 
v_res_4777_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_);
lean_dec(v___y_4775_);
lean_dec_ref(v___y_4774_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
return v_res_4777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4778_, lean_object* v_zetaDeltaFVarIds_4779_, lean_object* v_a_x3f_4780_){
_start:
{
lean_object* v___x_4782_; lean_object* v_mctx_4783_; lean_object* v_cache_4784_; lean_object* v_postponed_4785_; lean_object* v_diag_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4796_; 
v___x_4782_ = lean_st_ref_take(v___y_4778_);
v_mctx_4783_ = lean_ctor_get(v___x_4782_, 0);
v_cache_4784_ = lean_ctor_get(v___x_4782_, 1);
v_postponed_4785_ = lean_ctor_get(v___x_4782_, 3);
v_diag_4786_ = lean_ctor_get(v___x_4782_, 4);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4782_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; 
v_unused_4797_ = lean_ctor_get(v___x_4782_, 2);
lean_dec(v_unused_4797_);
v___x_4788_ = v___x_4782_;
v_isShared_4789_ = v_isSharedCheck_4796_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_diag_4786_);
lean_inc(v_postponed_4785_);
lean_inc(v_cache_4784_);
lean_inc(v_mctx_4783_);
lean_dec(v___x_4782_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4796_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4791_; 
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 2, v_zetaDeltaFVarIds_4779_);
v___x_4791_ = v___x_4788_;
goto v_reusejp_4790_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v_mctx_4783_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_cache_4784_);
lean_ctor_set(v_reuseFailAlloc_4795_, 2, v_zetaDeltaFVarIds_4779_);
lean_ctor_set(v_reuseFailAlloc_4795_, 3, v_postponed_4785_);
lean_ctor_set(v_reuseFailAlloc_4795_, 4, v_diag_4786_);
v___x_4791_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4790_;
}
v_reusejp_4790_:
{
lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4792_ = lean_st_ref_put(v___y_4778_, v___x_4791_);
v___x_4793_ = lean_box(0);
v___x_4794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4793_);
return v___x_4794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4798_, lean_object* v_zetaDeltaFVarIds_4799_, lean_object* v_a_x3f_4800_, lean_object* v___y_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4798_, v_zetaDeltaFVarIds_4799_, v_a_x3f_4800_);
lean_dec(v_a_x3f_4800_);
lean_dec(v___y_4798_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4803_, lean_object* v_msg_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_){
_start:
{
lean_object* v_ref_4810_; lean_object* v___x_4811_; lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4856_; 
v_ref_4810_ = lean_ctor_get(v___y_4807_, 5);
v___x_4811_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4804_, v___y_4805_, v___y_4806_, v___y_4807_, v___y_4808_);
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
v_isSharedCheck_4856_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4814_ = v___x_4811_;
v_isShared_4815_ = v_isSharedCheck_4856_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4811_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4856_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
lean_object* v___x_4816_; lean_object* v_traceState_4817_; lean_object* v_env_4818_; lean_object* v_nextMacroScope_4819_; lean_object* v_ngen_4820_; lean_object* v_auxDeclNGen_4821_; lean_object* v_cache_4822_; lean_object* v_messages_4823_; lean_object* v_infoState_4824_; lean_object* v_snapshotTasks_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4855_; 
v___x_4816_ = lean_st_ref_take(v___y_4808_);
v_traceState_4817_ = lean_ctor_get(v___x_4816_, 4);
v_env_4818_ = lean_ctor_get(v___x_4816_, 0);
v_nextMacroScope_4819_ = lean_ctor_get(v___x_4816_, 1);
v_ngen_4820_ = lean_ctor_get(v___x_4816_, 2);
v_auxDeclNGen_4821_ = lean_ctor_get(v___x_4816_, 3);
v_cache_4822_ = lean_ctor_get(v___x_4816_, 5);
v_messages_4823_ = lean_ctor_get(v___x_4816_, 6);
v_infoState_4824_ = lean_ctor_get(v___x_4816_, 7);
v_snapshotTasks_4825_ = lean_ctor_get(v___x_4816_, 8);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4827_ = v___x_4816_;
v_isShared_4828_ = v_isSharedCheck_4855_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_snapshotTasks_4825_);
lean_inc(v_infoState_4824_);
lean_inc(v_messages_4823_);
lean_inc(v_cache_4822_);
lean_inc(v_traceState_4817_);
lean_inc(v_auxDeclNGen_4821_);
lean_inc(v_ngen_4820_);
lean_inc(v_nextMacroScope_4819_);
lean_inc(v_env_4818_);
lean_dec(v___x_4816_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4855_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
uint64_t v_tid_4829_; lean_object* v_traces_4830_; lean_object* v___x_4832_; uint8_t v_isShared_4833_; uint8_t v_isSharedCheck_4854_; 
v_tid_4829_ = lean_ctor_get_uint64(v_traceState_4817_, sizeof(void*)*1);
v_traces_4830_ = lean_ctor_get(v_traceState_4817_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v_traceState_4817_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4832_ = v_traceState_4817_;
v_isShared_4833_ = v_isSharedCheck_4854_;
goto v_resetjp_4831_;
}
else
{
lean_inc(v_traces_4830_);
lean_dec(v_traceState_4817_);
v___x_4832_ = lean_box(0);
v_isShared_4833_ = v_isSharedCheck_4854_;
goto v_resetjp_4831_;
}
v_resetjp_4831_:
{
lean_object* v___x_4834_; double v___x_4835_; uint8_t v___x_4836_; lean_object* v___x_4837_; lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4844_; 
v___x_4834_ = lean_box(0);
v___x_4835_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4836_ = 0;
v___x_4837_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4838_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4838_, 0, v_cls_4803_);
lean_ctor_set(v___x_4838_, 1, v___x_4834_);
lean_ctor_set(v___x_4838_, 2, v___x_4837_);
lean_ctor_set_float(v___x_4838_, sizeof(void*)*3, v___x_4835_);
lean_ctor_set_float(v___x_4838_, sizeof(void*)*3 + 8, v___x_4835_);
lean_ctor_set_uint8(v___x_4838_, sizeof(void*)*3 + 16, v___x_4836_);
v___x_4839_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4840_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4838_);
lean_ctor_set(v___x_4840_, 1, v_a_4812_);
lean_ctor_set(v___x_4840_, 2, v___x_4839_);
lean_inc(v_ref_4810_);
v___x_4841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4841_, 0, v_ref_4810_);
lean_ctor_set(v___x_4841_, 1, v___x_4840_);
v___x_4842_ = l_Lean_PersistentArray_push___redArg(v_traces_4830_, v___x_4841_);
if (v_isShared_4833_ == 0)
{
lean_ctor_set(v___x_4832_, 0, v___x_4842_);
v___x_4844_ = v___x_4832_;
goto v_reusejp_4843_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4842_);
lean_ctor_set_uint64(v_reuseFailAlloc_4853_, sizeof(void*)*1, v_tid_4829_);
v___x_4844_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4843_;
}
v_reusejp_4843_:
{
lean_object* v___x_4846_; 
if (v_isShared_4828_ == 0)
{
lean_ctor_set(v___x_4827_, 4, v___x_4844_);
v___x_4846_ = v___x_4827_;
goto v_reusejp_4845_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_env_4818_);
lean_ctor_set(v_reuseFailAlloc_4852_, 1, v_nextMacroScope_4819_);
lean_ctor_set(v_reuseFailAlloc_4852_, 2, v_ngen_4820_);
lean_ctor_set(v_reuseFailAlloc_4852_, 3, v_auxDeclNGen_4821_);
lean_ctor_set(v_reuseFailAlloc_4852_, 4, v___x_4844_);
lean_ctor_set(v_reuseFailAlloc_4852_, 5, v_cache_4822_);
lean_ctor_set(v_reuseFailAlloc_4852_, 6, v_messages_4823_);
lean_ctor_set(v_reuseFailAlloc_4852_, 7, v_infoState_4824_);
lean_ctor_set(v_reuseFailAlloc_4852_, 8, v_snapshotTasks_4825_);
v___x_4846_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4845_;
}
v_reusejp_4845_:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; lean_object* v___x_4850_; 
v___x_4847_ = lean_st_ref_put(v___y_4808_, v___x_4846_);
v___x_4848_ = lean_box(0);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v___x_4848_);
v___x_4850_ = v___x_4814_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v___x_4848_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4857_, lean_object* v_msg_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4857_, v_msg_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
return v_res_4864_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4866_; lean_object* v___x_4867_; 
v___x_4866_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4867_ = l_Lean_stringToMessageData(v___x_4866_);
return v___x_4867_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4870_ = l_Lean_stringToMessageData(v___x_4869_);
return v___x_4870_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4872_; lean_object* v___x_4873_; 
v___x_4872_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4873_ = l_Lean_stringToMessageData(v___x_4872_);
return v___x_4873_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4876_ = l_Lean_stringToMessageData(v___x_4875_);
return v___x_4876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4877_, lean_object* v_e_4878_, lean_object* v___x_4879_, lean_object* v___x_4880_, lean_object* v_cls_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4887_ = lean_st_mk_ref(v___x_4877_);
v___x_4888_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4878_, v___x_4879_, v___x_4887_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4958_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4958_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4958_ == 0)
{
v___x_4891_ = v___x_4888_;
v_isShared_4892_ = v_isSharedCheck_4958_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4888_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4958_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
lean_object* v___x_4893_; lean_object* v_count_4894_; lean_object* v___x_4896_; uint8_t v_isShared_4897_; uint8_t v_isSharedCheck_4956_; 
v___x_4893_ = lean_st_ref_get(v___x_4887_);
lean_dec(v___x_4887_);
v_count_4894_ = lean_ctor_get(v___x_4893_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4893_);
if (v_isSharedCheck_4956_ == 0)
{
lean_object* v_unused_4957_; 
v_unused_4957_ = lean_ctor_get(v___x_4893_, 1);
lean_dec(v_unused_4957_);
v___x_4896_ = v___x_4893_;
v_isShared_4897_ = v_isSharedCheck_4956_;
goto v_resetjp_4895_;
}
else
{
lean_inc(v_count_4894_);
lean_dec(v___x_4893_);
v___x_4896_ = lean_box(0);
v_isShared_4897_ = v_isSharedCheck_4956_;
goto v_resetjp_4895_;
}
v_resetjp_4895_:
{
uint8_t v___x_4920_; 
v___x_4920_ = lean_nat_dec_eq(v_count_4894_, v___x_4880_);
if (v___x_4920_ == 0)
{
lean_object* v_options_4921_; uint8_t v_hasTrace_4922_; 
v_options_4921_ = lean_ctor_get(v___y_4884_, 2);
v_hasTrace_4922_ = lean_ctor_get_uint8(v_options_4921_, sizeof(void*)*1);
if (v_hasTrace_4922_ == 0)
{
lean_dec(v_cls_4881_);
goto v___jp_4898_;
}
else
{
lean_object* v_inheritedTraceOptions_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; uint8_t v___x_4926_; 
v_inheritedTraceOptions_4923_ = lean_ctor_get(v___y_4884_, 13);
v___x_4924_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4881_);
v___x_4925_ = l_Lean_Name_append(v___x_4924_, v_cls_4881_);
v___x_4926_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4923_, v_options_4921_, v___x_4925_);
lean_dec(v___x_4925_);
if (v___x_4926_ == 0)
{
lean_dec(v_cls_4881_);
goto v___jp_4898_;
}
else
{
lean_object* v_expr_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v_expr_4927_ = lean_ctor_get(v_a_4889_, 0);
v___x_4928_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4927_);
v___x_4929_ = l_Lean_indentExpr(v_expr_4927_);
v___x_4930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4930_, 0, v___x_4928_);
lean_ctor_set(v___x_4930_, 1, v___x_4929_);
v___x_4931_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4881_, v___x_4930_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
if (lean_obj_tag(v___x_4931_) == 0)
{
lean_dec_ref_known(v___x_4931_, 1);
goto v___jp_4898_;
}
else
{
lean_object* v_a_4932_; lean_object* v___x_4934_; uint8_t v_isShared_4935_; uint8_t v_isSharedCheck_4939_; 
lean_del_object(v___x_4896_);
lean_dec(v_count_4894_);
lean_del_object(v___x_4891_);
lean_dec(v_a_4889_);
v_a_4932_ = lean_ctor_get(v___x_4931_, 0);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4931_);
if (v_isSharedCheck_4939_ == 0)
{
v___x_4934_ = v___x_4931_;
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
else
{
lean_inc(v_a_4932_);
lean_dec(v___x_4931_);
v___x_4934_ = lean_box(0);
v_isShared_4935_ = v_isSharedCheck_4939_;
goto v_resetjp_4933_;
}
v_resetjp_4933_:
{
lean_object* v___x_4937_; 
if (v_isShared_4935_ == 0)
{
v___x_4937_ = v___x_4934_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v_a_4932_);
v___x_4937_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
return v___x_4937_;
}
}
}
}
}
}
else
{
lean_object* v_options_4940_; uint8_t v_hasTrace_4941_; 
v_options_4940_ = lean_ctor_get(v___y_4884_, 2);
v_hasTrace_4941_ = lean_ctor_get_uint8(v_options_4940_, sizeof(void*)*1);
if (v_hasTrace_4941_ == 0)
{
lean_dec(v_cls_4881_);
goto v___jp_4898_;
}
else
{
lean_object* v_inheritedTraceOptions_4942_; lean_object* v___x_4943_; lean_object* v___x_4944_; uint8_t v___x_4945_; 
v_inheritedTraceOptions_4942_ = lean_ctor_get(v___y_4884_, 13);
v___x_4943_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4881_);
v___x_4944_ = l_Lean_Name_append(v___x_4943_, v_cls_4881_);
v___x_4945_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4942_, v_options_4940_, v___x_4944_);
lean_dec(v___x_4944_);
if (v___x_4945_ == 0)
{
lean_dec(v_cls_4881_);
goto v___jp_4898_;
}
else
{
lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4946_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4947_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4881_, v___x_4946_, v___y_4882_, v___y_4883_, v___y_4884_, v___y_4885_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_dec_ref_known(v___x_4947_, 1);
goto v___jp_4898_;
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_del_object(v___x_4896_);
lean_dec(v_count_4894_);
lean_del_object(v___x_4891_);
lean_dec(v_a_4889_);
v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4947_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4947_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
}
}
v___jp_4898_:
{
lean_object* v_expr_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4918_; 
v_expr_4899_ = lean_ctor_get(v_a_4889_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v_a_4889_);
if (v_isSharedCheck_4918_ == 0)
{
lean_object* v_unused_4919_; 
v_unused_4919_ = lean_ctor_get(v_a_4889_, 1);
lean_dec(v_unused_4919_);
v___x_4901_ = v_a_4889_;
v_isShared_4902_ = v_isSharedCheck_4918_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_expr_4899_);
lean_dec(v_a_4889_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4918_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4908_; 
v___x_4903_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4904_ = l_Nat_reprFast(v_count_4894_);
v___x_4905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4904_);
v___x_4906_ = l_Lean_MessageData_ofFormat(v___x_4905_);
if (v_isShared_4902_ == 0)
{
lean_ctor_set_tag(v___x_4901_, 7);
lean_ctor_set(v___x_4901_, 1, v___x_4906_);
lean_ctor_set(v___x_4901_, 0, v___x_4903_);
v___x_4908_ = v___x_4901_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v___x_4903_);
lean_ctor_set(v_reuseFailAlloc_4917_, 1, v___x_4906_);
v___x_4908_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
lean_object* v___x_4909_; lean_object* v___x_4911_; 
v___x_4909_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4897_ == 0)
{
lean_ctor_set_tag(v___x_4896_, 7);
lean_ctor_set(v___x_4896_, 1, v___x_4909_);
lean_ctor_set(v___x_4896_, 0, v___x_4908_);
v___x_4911_ = v___x_4896_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v___x_4908_);
lean_ctor_set(v_reuseFailAlloc_4916_, 1, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
lean_object* v___x_4912_; lean_object* v___x_4914_; 
v___x_4912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4912_, 0, v_expr_4899_);
lean_ctor_set(v___x_4912_, 1, v___x_4911_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v___x_4912_);
v___x_4914_ = v___x_4891_;
goto v_reusejp_4913_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v___x_4912_);
v___x_4914_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4913_;
}
v_reusejp_4913_:
{
return v___x_4914_;
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
lean_object* v_a_4959_; lean_object* v___x_4961_; uint8_t v_isShared_4962_; uint8_t v_isSharedCheck_4966_; 
lean_dec(v___x_4887_);
lean_dec(v_cls_4881_);
v_a_4959_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4966_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4966_ == 0)
{
v___x_4961_ = v___x_4888_;
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
else
{
lean_inc(v_a_4959_);
lean_dec(v___x_4888_);
v___x_4961_ = lean_box(0);
v_isShared_4962_ = v_isSharedCheck_4966_;
goto v_resetjp_4960_;
}
v_resetjp_4960_:
{
lean_object* v___x_4964_; 
if (v_isShared_4962_ == 0)
{
v___x_4964_ = v___x_4961_;
goto v_reusejp_4963_;
}
else
{
lean_object* v_reuseFailAlloc_4965_; 
v_reuseFailAlloc_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4965_, 0, v_a_4959_);
v___x_4964_ = v_reuseFailAlloc_4965_;
goto v_reusejp_4963_;
}
v_reusejp_4963_:
{
return v___x_4964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4967_, lean_object* v_e_4968_, lean_object* v___x_4969_, lean_object* v___x_4970_, lean_object* v_cls_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_){
_start:
{
lean_object* v_res_4977_; 
v_res_4977_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4967_, v_e_4968_, v___x_4969_, v___x_4970_, v_cls_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___x_4970_);
lean_dec(v___x_4969_);
return v_res_4977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4978_, lean_object* v_cache_4979_, lean_object* v_a_x3f_4980_){
_start:
{
lean_object* v___x_4982_; lean_object* v_mctx_4983_; lean_object* v_zetaDeltaFVarIds_4984_; lean_object* v_postponed_4985_; lean_object* v_diag_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4996_; 
v___x_4982_ = lean_st_ref_take(v___y_4978_);
v_mctx_4983_ = lean_ctor_get(v___x_4982_, 0);
v_zetaDeltaFVarIds_4984_ = lean_ctor_get(v___x_4982_, 2);
v_postponed_4985_ = lean_ctor_get(v___x_4982_, 3);
v_diag_4986_ = lean_ctor_get(v___x_4982_, 4);
v_isSharedCheck_4996_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4996_ == 0)
{
lean_object* v_unused_4997_; 
v_unused_4997_ = lean_ctor_get(v___x_4982_, 1);
lean_dec(v_unused_4997_);
v___x_4988_ = v___x_4982_;
v_isShared_4989_ = v_isSharedCheck_4996_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_diag_4986_);
lean_inc(v_postponed_4985_);
lean_inc(v_zetaDeltaFVarIds_4984_);
lean_inc(v_mctx_4983_);
lean_dec(v___x_4982_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4996_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4991_; 
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 1, v_cache_4979_);
v___x_4991_ = v___x_4988_;
goto v_reusejp_4990_;
}
else
{
lean_object* v_reuseFailAlloc_4995_; 
v_reuseFailAlloc_4995_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4995_, 0, v_mctx_4983_);
lean_ctor_set(v_reuseFailAlloc_4995_, 1, v_cache_4979_);
lean_ctor_set(v_reuseFailAlloc_4995_, 2, v_zetaDeltaFVarIds_4984_);
lean_ctor_set(v_reuseFailAlloc_4995_, 3, v_postponed_4985_);
lean_ctor_set(v_reuseFailAlloc_4995_, 4, v_diag_4986_);
v___x_4991_ = v_reuseFailAlloc_4995_;
goto v_reusejp_4990_;
}
v_reusejp_4990_:
{
lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; 
v___x_4992_ = lean_st_ref_put(v___y_4978_, v___x_4991_);
v___x_4993_ = lean_box(0);
v___x_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4994_, 0, v___x_4993_);
return v___x_4994_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4998_, lean_object* v_cache_4999_, lean_object* v_a_x3f_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4998_, v_cache_4999_, v_a_x3f_5000_);
lean_dec(v_a_x3f_5000_);
lean_dec(v___y_4998_);
return v_res_5002_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2(void){
_start:
{
lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5006_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__1));
v___x_5007_ = l_Lean_MessageData_ofFormat(v___x_5006_);
return v___x_5007_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3(void){
_start:
{
lean_object* v___x_5008_; 
v___x_5008_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5008_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4(void){
_start:
{
lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___x_5009_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__3);
v___x_5010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
return v___x_5010_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5(void){
_start:
{
lean_object* v___x_5011_; lean_object* v___x_5012_; 
v___x_5011_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__4);
v___x_5012_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5012_, 0, v___x_5011_);
lean_ctor_set(v___x_5012_, 1, v___x_5011_);
lean_ctor_set(v___x_5012_, 2, v___x_5011_);
lean_ctor_set(v___x_5012_, 3, v___x_5011_);
lean_ctor_set(v___x_5012_, 4, v___x_5011_);
lean_ctor_set(v___x_5012_, 5, v___x_5011_);
return v___x_5012_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6(void){
_start:
{
lean_object* v_cellCount_5013_; lean_object* v___x_5014_; 
v_cellCount_5013_ = lean_unsigned_to_nat(16u);
v___x_5014_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_5013_);
return v___x_5014_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7(void){
_start:
{
lean_object* v___x_5015_; lean_object* v___x_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; 
v___x_5015_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__6);
v___x_5016_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0);
v___x_5017_ = lean_unsigned_to_nat(0u);
v___x_5018_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5017_);
lean_ctor_set(v___x_5018_, 1, v___x_5016_);
lean_ctor_set(v___x_5018_, 2, v___x_5015_);
return v___x_5018_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__8(void){
_start:
{
lean_object* v___x_5019_; lean_object* v___x_5020_; lean_object* v___x_5021_; 
v___x_5019_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__7);
v___x_5020_ = lean_unsigned_to_nat(0u);
v___x_5021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5021_, 0, v___x_5020_);
lean_ctor_set(v___x_5021_, 1, v___x_5019_);
return v___x_5021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_5022_, lean_object* v_e_5023_, uint8_t v___x_5024_, lean_object* v_cls_5025_, lean_object* v___y_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_){
_start:
{
if (v___x_5022_ == 0)
{
lean_object* v___x_5031_; lean_object* v___x_5032_; lean_object* v___x_5033_; 
lean_dec(v_cls_5025_);
v___x_5031_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__2);
v___x_5032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5032_, 0, v_e_5023_);
lean_ctor_set(v___x_5032_, 1, v___x_5031_);
v___x_5033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5033_, 0, v___x_5032_);
return v___x_5033_;
}
else
{
lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v_mctx_5036_; lean_object* v_zetaDeltaFVarIds_5037_; lean_object* v_postponed_5038_; lean_object* v_diag_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5165_; 
v___x_5034_ = lean_st_ref_get(v___y_5027_);
v___x_5035_ = lean_st_ref_take(v___y_5027_);
v_mctx_5036_ = lean_ctor_get(v___x_5035_, 0);
v_zetaDeltaFVarIds_5037_ = lean_ctor_get(v___x_5035_, 2);
v_postponed_5038_ = lean_ctor_get(v___x_5035_, 3);
v_diag_5039_ = lean_ctor_get(v___x_5035_, 4);
v_isSharedCheck_5165_ = !lean_is_exclusive(v___x_5035_);
if (v_isSharedCheck_5165_ == 0)
{
lean_object* v_unused_5166_; 
v_unused_5166_ = lean_ctor_get(v___x_5035_, 1);
lean_dec(v_unused_5166_);
v___x_5041_ = v___x_5035_;
v_isShared_5042_ = v_isSharedCheck_5165_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_diag_5039_);
lean_inc(v_postponed_5038_);
lean_inc(v_zetaDeltaFVarIds_5037_);
lean_inc(v_mctx_5036_);
lean_dec(v___x_5035_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5165_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5043_; lean_object* v___x_5045_; 
v___x_5043_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__5);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 1, v___x_5043_);
v___x_5045_ = v___x_5041_;
goto v_reusejp_5044_;
}
else
{
lean_object* v_reuseFailAlloc_5164_; 
v_reuseFailAlloc_5164_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5164_, 0, v_mctx_5036_);
lean_ctor_set(v_reuseFailAlloc_5164_, 1, v___x_5043_);
lean_ctor_set(v_reuseFailAlloc_5164_, 2, v_zetaDeltaFVarIds_5037_);
lean_ctor_set(v_reuseFailAlloc_5164_, 3, v_postponed_5038_);
lean_ctor_set(v_reuseFailAlloc_5164_, 4, v_diag_5039_);
v___x_5045_ = v_reuseFailAlloc_5164_;
goto v_reusejp_5044_;
}
v_reusejp_5044_:
{
lean_object* v___x_5046_; lean_object* v___x_5047_; lean_object* v_mctx_5048_; lean_object* v_cache_5049_; lean_object* v_zetaDeltaFVarIds_5050_; lean_object* v_postponed_5051_; lean_object* v_diag_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5163_; 
v___x_5046_ = lean_st_ref_put(v___y_5027_, v___x_5045_);
v___x_5047_ = lean_st_ref_take(v___y_5027_);
v_mctx_5048_ = lean_ctor_get(v___x_5047_, 0);
v_cache_5049_ = lean_ctor_get(v___x_5047_, 1);
v_zetaDeltaFVarIds_5050_ = lean_ctor_get(v___x_5047_, 2);
v_postponed_5051_ = lean_ctor_get(v___x_5047_, 3);
v_diag_5052_ = lean_ctor_get(v___x_5047_, 4);
v_isSharedCheck_5163_ = !lean_is_exclusive(v___x_5047_);
if (v_isSharedCheck_5163_ == 0)
{
v___x_5054_ = v___x_5047_;
v_isShared_5055_ = v_isSharedCheck_5163_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_diag_5052_);
lean_inc(v_postponed_5051_);
lean_inc(v_zetaDeltaFVarIds_5050_);
lean_inc(v_cache_5049_);
lean_inc(v_mctx_5048_);
lean_dec(v___x_5047_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5163_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5056_; lean_object* v___x_5058_; 
v___x_5056_ = lean_box(1);
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 2, v___x_5056_);
v___x_5058_ = v___x_5054_;
goto v_reusejp_5057_;
}
else
{
lean_object* v_reuseFailAlloc_5162_; 
v_reuseFailAlloc_5162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5162_, 0, v_mctx_5048_);
lean_ctor_set(v_reuseFailAlloc_5162_, 1, v_cache_5049_);
lean_ctor_set(v_reuseFailAlloc_5162_, 2, v___x_5056_);
lean_ctor_set(v_reuseFailAlloc_5162_, 3, v_postponed_5051_);
lean_ctor_set(v_reuseFailAlloc_5162_, 4, v_diag_5052_);
v___x_5058_ = v_reuseFailAlloc_5162_;
goto v_reusejp_5057_;
}
v_reusejp_5057_:
{
lean_object* v___x_5059_; lean_object* v_cache_5060_; lean_object* v_keyedConfig_5061_; lean_object* v_zetaDeltaSet_5062_; lean_object* v_lctx_5063_; lean_object* v_localInstances_5064_; lean_object* v_defEqCtx_x3f_5065_; lean_object* v_synthPendingDepth_5066_; lean_object* v_customCanUnfoldPredicate_x3f_5067_; uint8_t v_univApprox_5068_; uint8_t v_inTypeClassResolution_5069_; uint8_t v_cacheInferType_5070_; uint8_t v___x_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; uint8_t v_transparency_5075_; lean_object* v___x_5076_; lean_object* v___x_5077_; lean_object* v___x_5078_; lean_object* v_a_5080_; lean_object* v___y_5092_; lean_object* v___y_5115_; uint8_t v___y_5144_; uint8_t v___x_5160_; uint8_t v___x_5161_; 
v___x_5059_ = lean_st_ref_put(v___y_5027_, v___x_5058_);
v_cache_5060_ = lean_ctor_get(v___x_5034_, 1);
lean_inc_ref(v_cache_5060_);
lean_dec(v___x_5034_);
v_keyedConfig_5061_ = lean_ctor_get(v___y_5026_, 0);
v_zetaDeltaSet_5062_ = lean_ctor_get(v___y_5026_, 1);
v_lctx_5063_ = lean_ctor_get(v___y_5026_, 2);
v_localInstances_5064_ = lean_ctor_get(v___y_5026_, 3);
v_defEqCtx_x3f_5065_ = lean_ctor_get(v___y_5026_, 4);
v_synthPendingDepth_5066_ = lean_ctor_get(v___y_5026_, 5);
v_customCanUnfoldPredicate_x3f_5067_ = lean_ctor_get(v___y_5026_, 6);
v_univApprox_5068_ = lean_ctor_get_uint8(v___y_5026_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5069_ = lean_ctor_get_uint8(v___y_5026_, sizeof(void*)*7 + 2);
v_cacheInferType_5070_ = lean_ctor_get_uint8(v___y_5026_, sizeof(void*)*7 + 3);
v___x_5071_ = 0;
lean_inc_ref(v_keyedConfig_5061_);
v___x_5072_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_5071_, v_keyedConfig_5061_);
lean_inc(v_customCanUnfoldPredicate_x3f_5067_);
lean_inc(v_synthPendingDepth_5066_);
lean_inc(v_defEqCtx_x3f_5065_);
lean_inc_ref(v_localInstances_5064_);
lean_inc_ref(v_lctx_5063_);
lean_inc(v_zetaDeltaSet_5062_);
lean_inc_ref(v___x_5072_);
v___x_5073_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5073_, 0, v___x_5072_);
lean_ctor_set(v___x_5073_, 1, v_zetaDeltaSet_5062_);
lean_ctor_set(v___x_5073_, 2, v_lctx_5063_);
lean_ctor_set(v___x_5073_, 3, v_localInstances_5064_);
lean_ctor_set(v___x_5073_, 4, v_defEqCtx_x3f_5065_);
lean_ctor_set(v___x_5073_, 5, v_synthPendingDepth_5066_);
lean_ctor_set(v___x_5073_, 6, v_customCanUnfoldPredicate_x3f_5067_);
lean_ctor_set_uint8(v___x_5073_, sizeof(void*)*7, v___x_5024_);
lean_ctor_set_uint8(v___x_5073_, sizeof(void*)*7 + 1, v_univApprox_5068_);
lean_ctor_set_uint8(v___x_5073_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5069_);
lean_ctor_set_uint8(v___x_5073_, sizeof(void*)*7 + 3, v_cacheInferType_5070_);
v___x_5074_ = l_Lean_Meta_Context_config(v___x_5073_);
lean_dec_ref_known(v___x_5073_, 7);
v_transparency_5075_ = lean_ctor_get_uint8(v___x_5074_, 9);
lean_dec_ref(v___x_5074_);
v___x_5076_ = lean_unsigned_to_nat(0u);
v___x_5077_ = lean_box(0);
v___x_5078_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__8);
v___x_5160_ = 1;
v___x_5161_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_5075_, v___x_5160_);
if (v___x_5161_ == 0)
{
v___y_5144_ = v_transparency_5075_;
goto v___jp_5143_;
}
else
{
v___y_5144_ = v___x_5160_;
goto v___jp_5143_;
}
v___jp_5079_:
{
lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
v___x_5081_ = lean_box(0);
v___x_5082_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_5027_, v_cache_5060_, v___x_5081_);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5082_);
if (v_isSharedCheck_5089_ == 0)
{
lean_object* v_unused_5090_; 
v_unused_5090_ = lean_ctor_get(v___x_5082_, 0);
lean_dec(v_unused_5090_);
v___x_5084_ = v___x_5082_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_dec(v___x_5082_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
lean_ctor_set_tag(v___x_5084_, 1);
lean_ctor_set(v___x_5084_, 0, v_a_5080_);
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5080_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
v___jp_5091_:
{
if (lean_obj_tag(v___y_5092_) == 0)
{
lean_object* v_a_5093_; lean_object* v___x_5095_; uint8_t v_isShared_5096_; uint8_t v_isSharedCheck_5110_; 
v_a_5093_ = lean_ctor_get(v___y_5092_, 0);
v_isSharedCheck_5110_ = !lean_is_exclusive(v___y_5092_);
if (v_isSharedCheck_5110_ == 0)
{
v___x_5095_ = v___y_5092_;
v_isShared_5096_ = v_isSharedCheck_5110_;
goto v_resetjp_5094_;
}
else
{
lean_inc(v_a_5093_);
lean_dec(v___y_5092_);
v___x_5095_ = lean_box(0);
v_isShared_5096_ = v_isSharedCheck_5110_;
goto v_resetjp_5094_;
}
v_resetjp_5094_:
{
lean_object* v___x_5098_; 
lean_inc(v_a_5093_);
if (v_isShared_5096_ == 0)
{
lean_ctor_set_tag(v___x_5095_, 1);
v___x_5098_ = v___x_5095_;
goto v_reusejp_5097_;
}
else
{
lean_object* v_reuseFailAlloc_5109_; 
v_reuseFailAlloc_5109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5109_, 0, v_a_5093_);
v___x_5098_ = v_reuseFailAlloc_5109_;
goto v_reusejp_5097_;
}
v_reusejp_5097_:
{
lean_object* v___x_5099_; lean_object* v___x_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
v___x_5099_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_5027_, v_zetaDeltaFVarIds_5050_, v___x_5098_);
lean_dec_ref(v___x_5099_);
v___x_5100_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_5027_, v_cache_5060_, v___x_5098_);
lean_dec_ref(v___x_5098_);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5100_);
if (v_isSharedCheck_5107_ == 0)
{
lean_object* v_unused_5108_; 
v_unused_5108_ = lean_ctor_get(v___x_5100_, 0);
lean_dec(v_unused_5108_);
v___x_5102_ = v___x_5100_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_dec(v___x_5100_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
lean_ctor_set(v___x_5102_, 0, v_a_5093_);
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5093_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
}
}
else
{
lean_object* v_a_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v_a_5111_ = lean_ctor_get(v___y_5092_, 0);
lean_inc(v_a_5111_);
lean_dec_ref_known(v___y_5092_, 1);
v___x_5112_ = lean_box(0);
v___x_5113_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_5027_, v_zetaDeltaFVarIds_5050_, v___x_5112_);
lean_dec_ref(v___x_5113_);
v_a_5080_ = v_a_5111_;
goto v___jp_5079_;
}
}
v___jp_5114_:
{
lean_object* v___x_5116_; uint8_t v_foApprox_5117_; uint8_t v_ctxApprox_5118_; uint8_t v_quasiPatternApprox_5119_; uint8_t v_constApprox_5120_; uint8_t v_isDefEqStuckEx_5121_; uint8_t v_unificationHints_5122_; uint8_t v_proofIrrelevance_5123_; uint8_t v_assignSyntheticOpaque_5124_; uint8_t v_offsetCnstrs_5125_; uint8_t v_transparency_5126_; uint8_t v_univApprox_5127_; uint8_t v_zetaUnused_5128_; uint8_t v_canUnfoldPredicateConfig_5129_; lean_object* v___x_5131_; uint8_t v_isShared_5132_; uint8_t v_isSharedCheck_5142_; 
v___x_5116_ = l_Lean_Meta_Context_config(v___y_5115_);
lean_dec_ref(v___y_5115_);
v_foApprox_5117_ = lean_ctor_get_uint8(v___x_5116_, 0);
v_ctxApprox_5118_ = lean_ctor_get_uint8(v___x_5116_, 1);
v_quasiPatternApprox_5119_ = lean_ctor_get_uint8(v___x_5116_, 2);
v_constApprox_5120_ = lean_ctor_get_uint8(v___x_5116_, 3);
v_isDefEqStuckEx_5121_ = lean_ctor_get_uint8(v___x_5116_, 4);
v_unificationHints_5122_ = lean_ctor_get_uint8(v___x_5116_, 5);
v_proofIrrelevance_5123_ = lean_ctor_get_uint8(v___x_5116_, 6);
v_assignSyntheticOpaque_5124_ = lean_ctor_get_uint8(v___x_5116_, 7);
v_offsetCnstrs_5125_ = lean_ctor_get_uint8(v___x_5116_, 8);
v_transparency_5126_ = lean_ctor_get_uint8(v___x_5116_, 9);
v_univApprox_5127_ = lean_ctor_get_uint8(v___x_5116_, 11);
v_zetaUnused_5128_ = lean_ctor_get_uint8(v___x_5116_, 17);
v_canUnfoldPredicateConfig_5129_ = lean_ctor_get_uint8(v___x_5116_, 19);
v_isSharedCheck_5142_ = !lean_is_exclusive(v___x_5116_);
if (v_isSharedCheck_5142_ == 0)
{
v___x_5131_ = v___x_5116_;
v_isShared_5132_ = v_isSharedCheck_5142_;
goto v_resetjp_5130_;
}
else
{
lean_dec(v___x_5116_);
v___x_5131_ = lean_box(0);
v_isShared_5132_ = v_isSharedCheck_5142_;
goto v_resetjp_5130_;
}
v_resetjp_5130_:
{
uint8_t v___x_5133_; uint8_t v___x_5134_; lean_object* v___x_5136_; 
v___x_5133_ = 0;
v___x_5134_ = 2;
if (v_isShared_5132_ == 0)
{
v___x_5136_ = v___x_5131_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5141_; 
v_reuseFailAlloc_5141_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 0, v_foApprox_5117_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 1, v_ctxApprox_5118_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 2, v_quasiPatternApprox_5119_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 3, v_constApprox_5120_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 4, v_isDefEqStuckEx_5121_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 5, v_unificationHints_5122_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 6, v_proofIrrelevance_5123_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 7, v_assignSyntheticOpaque_5124_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 8, v_offsetCnstrs_5125_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 9, v_transparency_5126_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 11, v_univApprox_5127_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 17, v_zetaUnused_5128_);
lean_ctor_set_uint8(v_reuseFailAlloc_5141_, 19, v_canUnfoldPredicateConfig_5129_);
v___x_5136_ = v_reuseFailAlloc_5141_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
uint64_t v___x_5137_; lean_object* v___x_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; 
lean_ctor_set_uint8(v___x_5136_, 10, v___x_5133_);
lean_ctor_set_uint8(v___x_5136_, 12, v___x_5024_);
lean_ctor_set_uint8(v___x_5136_, 13, v___x_5024_);
lean_ctor_set_uint8(v___x_5136_, 14, v___x_5134_);
lean_ctor_set_uint8(v___x_5136_, 15, v___x_5024_);
lean_ctor_set_uint8(v___x_5136_, 16, v___x_5024_);
lean_ctor_set_uint8(v___x_5136_, 18, v___x_5024_);
v___x_5137_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5136_);
v___x_5138_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5138_, 0, v___x_5136_);
lean_ctor_set_uint64(v___x_5138_, sizeof(void*)*1, v___x_5137_);
lean_inc(v_customCanUnfoldPredicate_x3f_5067_);
lean_inc(v_synthPendingDepth_5066_);
lean_inc(v_defEqCtx_x3f_5065_);
lean_inc_ref(v_localInstances_5064_);
lean_inc_ref(v_lctx_5063_);
lean_inc(v_zetaDeltaSet_5062_);
v___x_5139_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5139_, 0, v___x_5138_);
lean_ctor_set(v___x_5139_, 1, v_zetaDeltaSet_5062_);
lean_ctor_set(v___x_5139_, 2, v_lctx_5063_);
lean_ctor_set(v___x_5139_, 3, v_localInstances_5064_);
lean_ctor_set(v___x_5139_, 4, v_defEqCtx_x3f_5065_);
lean_ctor_set(v___x_5139_, 5, v_synthPendingDepth_5066_);
lean_ctor_set(v___x_5139_, 6, v_customCanUnfoldPredicate_x3f_5067_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*7, v___x_5024_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*7 + 1, v_univApprox_5068_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5069_);
lean_ctor_set_uint8(v___x_5139_, sizeof(void*)*7 + 3, v_cacheInferType_5070_);
v___x_5140_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_5078_, v_e_5023_, v___x_5077_, v___x_5076_, v_cls_5025_, v___x_5139_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec_ref_known(v___x_5139_, 7);
v___y_5092_ = v___x_5140_;
goto v___jp_5091_;
}
}
}
v___jp_5143_:
{
lean_object* v___x_5145_; lean_object* v___x_5146_; lean_object* v___x_5147_; uint8_t v_beta_5148_; 
v___x_5145_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___y_5144_, v___x_5072_);
lean_inc(v_customCanUnfoldPredicate_x3f_5067_);
lean_inc(v_synthPendingDepth_5066_);
lean_inc(v_defEqCtx_x3f_5065_);
lean_inc_ref(v_localInstances_5064_);
lean_inc_ref(v_lctx_5063_);
lean_inc(v_zetaDeltaSet_5062_);
v___x_5146_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5146_, 0, v___x_5145_);
lean_ctor_set(v___x_5146_, 1, v_zetaDeltaSet_5062_);
lean_ctor_set(v___x_5146_, 2, v_lctx_5063_);
lean_ctor_set(v___x_5146_, 3, v_localInstances_5064_);
lean_ctor_set(v___x_5146_, 4, v_defEqCtx_x3f_5065_);
lean_ctor_set(v___x_5146_, 5, v_synthPendingDepth_5066_);
lean_ctor_set(v___x_5146_, 6, v_customCanUnfoldPredicate_x3f_5067_);
lean_ctor_set_uint8(v___x_5146_, sizeof(void*)*7, v___x_5024_);
lean_ctor_set_uint8(v___x_5146_, sizeof(void*)*7 + 1, v_univApprox_5068_);
lean_ctor_set_uint8(v___x_5146_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5069_);
lean_ctor_set_uint8(v___x_5146_, sizeof(void*)*7 + 3, v_cacheInferType_5070_);
v___x_5147_ = l_Lean_Meta_Context_config(v___x_5146_);
v_beta_5148_ = lean_ctor_get_uint8(v___x_5147_, 13);
if (v_beta_5148_ == 0)
{
lean_dec_ref(v___x_5147_);
v___y_5115_ = v___x_5146_;
goto v___jp_5114_;
}
else
{
uint8_t v_iota_5149_; 
v_iota_5149_ = lean_ctor_get_uint8(v___x_5147_, 12);
if (v_iota_5149_ == 0)
{
lean_dec_ref(v___x_5147_);
v___y_5115_ = v___x_5146_;
goto v___jp_5114_;
}
else
{
uint8_t v_zeta_5150_; 
v_zeta_5150_ = lean_ctor_get_uint8(v___x_5147_, 15);
if (v_zeta_5150_ == 0)
{
lean_dec_ref(v___x_5147_);
v___y_5115_ = v___x_5146_;
goto v___jp_5114_;
}
else
{
uint8_t v_zetaHave_5151_; 
v_zetaHave_5151_ = lean_ctor_get_uint8(v___x_5147_, 18);
if (v_zetaHave_5151_ == 0)
{
lean_dec_ref(v___x_5147_);
v___y_5115_ = v___x_5146_;
goto v___jp_5114_;
}
else
{
uint8_t v_zetaDelta_5152_; 
v_zetaDelta_5152_ = lean_ctor_get_uint8(v___x_5147_, 16);
if (v_zetaDelta_5152_ == 0)
{
lean_dec_ref(v___x_5147_);
v___y_5115_ = v___x_5146_;
goto v___jp_5114_;
}
else
{
uint8_t v_etaStruct_5153_; uint8_t v_proj_5154_; uint8_t v___x_5155_; uint8_t v___x_5156_; 
v_etaStruct_5153_ = lean_ctor_get_uint8(v___x_5147_, 10);
v_proj_5154_ = lean_ctor_get_uint8(v___x_5147_, 14);
lean_dec_ref(v___x_5147_);
v___x_5155_ = 2;
v___x_5156_ = l_Lean_Meta_instDecidableEqProjReductionKind(v_proj_5154_, v___x_5155_);
if (v___x_5156_ == 0)
{
v___y_5115_ = v___x_5146_;
goto v___jp_5114_;
}
else
{
uint8_t v___x_5157_; uint8_t v___x_5158_; 
v___x_5157_ = 0;
v___x_5158_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_5153_, v___x_5157_);
if (v___x_5158_ == 0)
{
v___y_5115_ = v___x_5146_;
goto v___jp_5114_;
}
else
{
lean_object* v___x_5159_; 
v___x_5159_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_5078_, v_e_5023_, v___x_5077_, v___x_5076_, v_cls_5025_, v___x_5146_, v___y_5027_, v___y_5028_, v___y_5029_);
lean_dec_ref_known(v___x_5146_, 7);
v___y_5092_ = v___x_5159_;
goto v___jp_5091_;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_5167_, lean_object* v_e_5168_, lean_object* v___x_5169_, lean_object* v_cls_5170_, lean_object* v___y_5171_, lean_object* v___y_5172_, lean_object* v___y_5173_, lean_object* v___y_5174_, lean_object* v___y_5175_){
_start:
{
uint8_t v___x_14427__boxed_5176_; uint8_t v___x_14428__boxed_5177_; lean_object* v_res_5178_; 
v___x_14427__boxed_5176_ = lean_unbox(v___x_5167_);
v___x_14428__boxed_5177_ = lean_unbox(v___x_5169_);
v_res_5178_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_14427__boxed_5176_, v_e_5168_, v___x_14428__boxed_5177_, v_cls_5170_, v___y_5171_, v___y_5172_, v___y_5173_, v___y_5174_);
lean_dec(v___y_5174_);
lean_dec_ref(v___y_5173_);
lean_dec(v___y_5172_);
lean_dec_ref(v___y_5171_);
return v_res_5178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_5179_, lean_object* v___y_5180_, lean_object* v___y_5181_, lean_object* v___y_5182_, lean_object* v___y_5183_){
_start:
{
if (lean_obj_tag(v_x_5179_) == 0)
{
lean_object* v_a_5185_; lean_object* v___x_5187_; uint8_t v_isShared_5188_; uint8_t v_isSharedCheck_5193_; 
v_a_5185_ = lean_ctor_get(v_x_5179_, 0);
v_isSharedCheck_5193_ = !lean_is_exclusive(v_x_5179_);
if (v_isSharedCheck_5193_ == 0)
{
v___x_5187_ = v_x_5179_;
v_isShared_5188_ = v_isSharedCheck_5193_;
goto v_resetjp_5186_;
}
else
{
lean_inc(v_a_5185_);
lean_dec(v_x_5179_);
v___x_5187_ = lean_box(0);
v_isShared_5188_ = v_isSharedCheck_5193_;
goto v_resetjp_5186_;
}
v_resetjp_5186_:
{
lean_object* v___x_5189_; lean_object* v___x_5191_; 
v___x_5189_ = l_Lean_Exception_toMessageData(v_a_5185_);
if (v_isShared_5188_ == 0)
{
lean_ctor_set(v___x_5187_, 0, v___x_5189_);
v___x_5191_ = v___x_5187_;
goto v_reusejp_5190_;
}
else
{
lean_object* v_reuseFailAlloc_5192_; 
v_reuseFailAlloc_5192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5192_, 0, v___x_5189_);
v___x_5191_ = v_reuseFailAlloc_5192_;
goto v_reusejp_5190_;
}
v_reusejp_5190_:
{
return v___x_5191_;
}
}
}
else
{
lean_object* v_a_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5202_; 
v_a_5194_ = lean_ctor_get(v_x_5179_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v_x_5179_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5196_ = v_x_5179_;
v_isShared_5197_ = v_isSharedCheck_5202_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_a_5194_);
lean_dec(v_x_5179_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5202_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v_snd_5198_; lean_object* v___x_5200_; 
v_snd_5198_ = lean_ctor_get(v_a_5194_, 1);
lean_inc(v_snd_5198_);
lean_dec(v_a_5194_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set_tag(v___x_5196_, 0);
lean_ctor_set(v___x_5196_, 0, v_snd_5198_);
v___x_5200_ = v___x_5196_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_snd_5198_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5210_){
_start:
{
if (lean_obj_tag(v_x_5210_) == 0)
{
lean_object* v_a_5212_; lean_object* v___x_5214_; uint8_t v_isShared_5215_; uint8_t v_isSharedCheck_5219_; 
v_a_5212_ = lean_ctor_get(v_x_5210_, 0);
v_isSharedCheck_5219_ = !lean_is_exclusive(v_x_5210_);
if (v_isSharedCheck_5219_ == 0)
{
v___x_5214_ = v_x_5210_;
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
else
{
lean_inc(v_a_5212_);
lean_dec(v_x_5210_);
v___x_5214_ = lean_box(0);
v_isShared_5215_ = v_isSharedCheck_5219_;
goto v_resetjp_5213_;
}
v_resetjp_5213_:
{
lean_object* v___x_5217_; 
if (v_isShared_5215_ == 0)
{
lean_ctor_set_tag(v___x_5214_, 1);
v___x_5217_ = v___x_5214_;
goto v_reusejp_5216_;
}
else
{
lean_object* v_reuseFailAlloc_5218_; 
v_reuseFailAlloc_5218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5218_, 0, v_a_5212_);
v___x_5217_ = v_reuseFailAlloc_5218_;
goto v_reusejp_5216_;
}
v_reusejp_5216_:
{
return v___x_5217_;
}
}
}
else
{
lean_object* v_a_5220_; lean_object* v___x_5222_; uint8_t v_isShared_5223_; uint8_t v_isSharedCheck_5227_; 
v_a_5220_ = lean_ctor_get(v_x_5210_, 0);
v_isSharedCheck_5227_ = !lean_is_exclusive(v_x_5210_);
if (v_isSharedCheck_5227_ == 0)
{
v___x_5222_ = v_x_5210_;
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
else
{
lean_inc(v_a_5220_);
lean_dec(v_x_5210_);
v___x_5222_ = lean_box(0);
v_isShared_5223_ = v_isSharedCheck_5227_;
goto v_resetjp_5221_;
}
v_resetjp_5221_:
{
lean_object* v___x_5225_; 
if (v_isShared_5223_ == 0)
{
lean_ctor_set_tag(v___x_5222_, 0);
v___x_5225_ = v___x_5222_;
goto v_reusejp_5224_;
}
else
{
lean_object* v_reuseFailAlloc_5226_; 
v_reuseFailAlloc_5226_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5228_, lean_object* v___y_5229_){
_start:
{
lean_object* v_res_5230_; 
v_res_5230_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5228_);
return v_res_5230_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5231_){
_start:
{
if (lean_obj_tag(v_e_5231_) == 0)
{
uint8_t v___x_5232_; 
v___x_5232_ = 2;
return v___x_5232_;
}
else
{
uint8_t v___x_5233_; 
v___x_5233_ = 0;
return v___x_5233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5234_){
_start:
{
uint8_t v_res_5235_; lean_object* v_r_5236_; 
v_res_5235_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5234_);
lean_dec_ref(v_e_5234_);
v_r_5236_ = lean_box(v_res_5235_);
return v_r_5236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5237_, lean_object* v_data_5238_, lean_object* v_ref_5239_, lean_object* v_msg_5240_, lean_object* v___y_5241_, lean_object* v___y_5242_, lean_object* v___y_5243_, lean_object* v___y_5244_){
_start:
{
lean_object* v_fileName_5246_; lean_object* v_fileMap_5247_; lean_object* v_options_5248_; lean_object* v_currRecDepth_5249_; lean_object* v_maxRecDepth_5250_; lean_object* v_ref_5251_; lean_object* v_currNamespace_5252_; lean_object* v_openDecls_5253_; lean_object* v_initHeartbeats_5254_; lean_object* v_maxHeartbeats_5255_; lean_object* v_quotContext_5256_; lean_object* v_currMacroScope_5257_; uint8_t v_diag_5258_; lean_object* v_cancelTk_x3f_5259_; uint8_t v_suppressElabErrors_5260_; lean_object* v_inheritedTraceOptions_5261_; lean_object* v___x_5262_; lean_object* v_traceState_5263_; lean_object* v_traces_5264_; lean_object* v_ref_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; size_t v_sz_5268_; size_t v___x_5269_; lean_object* v___x_5270_; lean_object* v_msg_5271_; lean_object* v___x_5272_; lean_object* v_a_5273_; lean_object* v___x_5275_; uint8_t v_isShared_5276_; uint8_t v_isSharedCheck_5310_; 
v_fileName_5246_ = lean_ctor_get(v___y_5243_, 0);
v_fileMap_5247_ = lean_ctor_get(v___y_5243_, 1);
v_options_5248_ = lean_ctor_get(v___y_5243_, 2);
v_currRecDepth_5249_ = lean_ctor_get(v___y_5243_, 3);
v_maxRecDepth_5250_ = lean_ctor_get(v___y_5243_, 4);
v_ref_5251_ = lean_ctor_get(v___y_5243_, 5);
v_currNamespace_5252_ = lean_ctor_get(v___y_5243_, 6);
v_openDecls_5253_ = lean_ctor_get(v___y_5243_, 7);
v_initHeartbeats_5254_ = lean_ctor_get(v___y_5243_, 8);
v_maxHeartbeats_5255_ = lean_ctor_get(v___y_5243_, 9);
v_quotContext_5256_ = lean_ctor_get(v___y_5243_, 10);
v_currMacroScope_5257_ = lean_ctor_get(v___y_5243_, 11);
v_diag_5258_ = lean_ctor_get_uint8(v___y_5243_, sizeof(void*)*14);
v_cancelTk_x3f_5259_ = lean_ctor_get(v___y_5243_, 12);
v_suppressElabErrors_5260_ = lean_ctor_get_uint8(v___y_5243_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_5261_ = lean_ctor_get(v___y_5243_, 13);
v___x_5262_ = lean_st_ref_get(v___y_5244_);
v_traceState_5263_ = lean_ctor_get(v___x_5262_, 4);
lean_inc_ref(v_traceState_5263_);
lean_dec(v___x_5262_);
v_traces_5264_ = lean_ctor_get(v_traceState_5263_, 0);
lean_inc_ref(v_traces_5264_);
lean_dec_ref(v_traceState_5263_);
v_ref_5265_ = l_Lean_replaceRef(v_ref_5239_, v_ref_5251_);
lean_inc_ref(v_inheritedTraceOptions_5261_);
lean_inc(v_cancelTk_x3f_5259_);
lean_inc(v_currMacroScope_5257_);
lean_inc(v_quotContext_5256_);
lean_inc(v_maxHeartbeats_5255_);
lean_inc(v_initHeartbeats_5254_);
lean_inc(v_openDecls_5253_);
lean_inc(v_currNamespace_5252_);
lean_inc(v_maxRecDepth_5250_);
lean_inc(v_currRecDepth_5249_);
lean_inc_ref(v_options_5248_);
lean_inc_ref(v_fileMap_5247_);
lean_inc_ref(v_fileName_5246_);
v___x_5266_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_5266_, 0, v_fileName_5246_);
lean_ctor_set(v___x_5266_, 1, v_fileMap_5247_);
lean_ctor_set(v___x_5266_, 2, v_options_5248_);
lean_ctor_set(v___x_5266_, 3, v_currRecDepth_5249_);
lean_ctor_set(v___x_5266_, 4, v_maxRecDepth_5250_);
lean_ctor_set(v___x_5266_, 5, v_ref_5265_);
lean_ctor_set(v___x_5266_, 6, v_currNamespace_5252_);
lean_ctor_set(v___x_5266_, 7, v_openDecls_5253_);
lean_ctor_set(v___x_5266_, 8, v_initHeartbeats_5254_);
lean_ctor_set(v___x_5266_, 9, v_maxHeartbeats_5255_);
lean_ctor_set(v___x_5266_, 10, v_quotContext_5256_);
lean_ctor_set(v___x_5266_, 11, v_currMacroScope_5257_);
lean_ctor_set(v___x_5266_, 12, v_cancelTk_x3f_5259_);
lean_ctor_set(v___x_5266_, 13, v_inheritedTraceOptions_5261_);
lean_ctor_set_uint8(v___x_5266_, sizeof(void*)*14, v_diag_5258_);
lean_ctor_set_uint8(v___x_5266_, sizeof(void*)*14 + 1, v_suppressElabErrors_5260_);
v___x_5267_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5264_);
lean_dec_ref(v_traces_5264_);
v_sz_5268_ = lean_array_size(v___x_5267_);
v___x_5269_ = ((size_t)0ULL);
v___x_5270_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5268_, v___x_5269_, v___x_5267_);
v_msg_5271_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5271_, 0, v_data_5238_);
lean_ctor_set(v_msg_5271_, 1, v_msg_5240_);
lean_ctor_set(v_msg_5271_, 2, v___x_5270_);
v___x_5272_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5271_, v___y_5241_, v___y_5242_, v___x_5266_, v___y_5244_);
lean_dec_ref_known(v___x_5266_, 14);
v_a_5273_ = lean_ctor_get(v___x_5272_, 0);
v_isSharedCheck_5310_ = !lean_is_exclusive(v___x_5272_);
if (v_isSharedCheck_5310_ == 0)
{
v___x_5275_ = v___x_5272_;
v_isShared_5276_ = v_isSharedCheck_5310_;
goto v_resetjp_5274_;
}
else
{
lean_inc(v_a_5273_);
lean_dec(v___x_5272_);
v___x_5275_ = lean_box(0);
v_isShared_5276_ = v_isSharedCheck_5310_;
goto v_resetjp_5274_;
}
v_resetjp_5274_:
{
lean_object* v___x_5277_; lean_object* v_traceState_5278_; lean_object* v_env_5279_; lean_object* v_nextMacroScope_5280_; lean_object* v_ngen_5281_; lean_object* v_auxDeclNGen_5282_; lean_object* v_cache_5283_; lean_object* v_messages_5284_; lean_object* v_infoState_5285_; lean_object* v_snapshotTasks_5286_; lean_object* v___x_5288_; uint8_t v_isShared_5289_; uint8_t v_isSharedCheck_5309_; 
v___x_5277_ = lean_st_ref_take(v___y_5244_);
v_traceState_5278_ = lean_ctor_get(v___x_5277_, 4);
v_env_5279_ = lean_ctor_get(v___x_5277_, 0);
v_nextMacroScope_5280_ = lean_ctor_get(v___x_5277_, 1);
v_ngen_5281_ = lean_ctor_get(v___x_5277_, 2);
v_auxDeclNGen_5282_ = lean_ctor_get(v___x_5277_, 3);
v_cache_5283_ = lean_ctor_get(v___x_5277_, 5);
v_messages_5284_ = lean_ctor_get(v___x_5277_, 6);
v_infoState_5285_ = lean_ctor_get(v___x_5277_, 7);
v_snapshotTasks_5286_ = lean_ctor_get(v___x_5277_, 8);
v_isSharedCheck_5309_ = !lean_is_exclusive(v___x_5277_);
if (v_isSharedCheck_5309_ == 0)
{
v___x_5288_ = v___x_5277_;
v_isShared_5289_ = v_isSharedCheck_5309_;
goto v_resetjp_5287_;
}
else
{
lean_inc(v_snapshotTasks_5286_);
lean_inc(v_infoState_5285_);
lean_inc(v_messages_5284_);
lean_inc(v_cache_5283_);
lean_inc(v_traceState_5278_);
lean_inc(v_auxDeclNGen_5282_);
lean_inc(v_ngen_5281_);
lean_inc(v_nextMacroScope_5280_);
lean_inc(v_env_5279_);
lean_dec(v___x_5277_);
v___x_5288_ = lean_box(0);
v_isShared_5289_ = v_isSharedCheck_5309_;
goto v_resetjp_5287_;
}
v_resetjp_5287_:
{
uint64_t v_tid_5290_; lean_object* v___x_5292_; uint8_t v_isShared_5293_; uint8_t v_isSharedCheck_5307_; 
v_tid_5290_ = lean_ctor_get_uint64(v_traceState_5278_, sizeof(void*)*1);
v_isSharedCheck_5307_ = !lean_is_exclusive(v_traceState_5278_);
if (v_isSharedCheck_5307_ == 0)
{
lean_object* v_unused_5308_; 
v_unused_5308_ = lean_ctor_get(v_traceState_5278_, 0);
lean_dec(v_unused_5308_);
v___x_5292_ = v_traceState_5278_;
v_isShared_5293_ = v_isSharedCheck_5307_;
goto v_resetjp_5291_;
}
else
{
lean_dec(v_traceState_5278_);
v___x_5292_ = lean_box(0);
v_isShared_5293_ = v_isSharedCheck_5307_;
goto v_resetjp_5291_;
}
v_resetjp_5291_:
{
lean_object* v___x_5294_; lean_object* v___x_5295_; lean_object* v___x_5297_; 
v___x_5294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5294_, 0, v_ref_5239_);
lean_ctor_set(v___x_5294_, 1, v_a_5273_);
v___x_5295_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5237_, v___x_5294_);
if (v_isShared_5293_ == 0)
{
lean_ctor_set(v___x_5292_, 0, v___x_5295_);
v___x_5297_ = v___x_5292_;
goto v_reusejp_5296_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v___x_5295_);
lean_ctor_set_uint64(v_reuseFailAlloc_5306_, sizeof(void*)*1, v_tid_5290_);
v___x_5297_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5296_;
}
v_reusejp_5296_:
{
lean_object* v___x_5299_; 
if (v_isShared_5289_ == 0)
{
lean_ctor_set(v___x_5288_, 4, v___x_5297_);
v___x_5299_ = v___x_5288_;
goto v_reusejp_5298_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v_env_5279_);
lean_ctor_set(v_reuseFailAlloc_5305_, 1, v_nextMacroScope_5280_);
lean_ctor_set(v_reuseFailAlloc_5305_, 2, v_ngen_5281_);
lean_ctor_set(v_reuseFailAlloc_5305_, 3, v_auxDeclNGen_5282_);
lean_ctor_set(v_reuseFailAlloc_5305_, 4, v___x_5297_);
lean_ctor_set(v_reuseFailAlloc_5305_, 5, v_cache_5283_);
lean_ctor_set(v_reuseFailAlloc_5305_, 6, v_messages_5284_);
lean_ctor_set(v_reuseFailAlloc_5305_, 7, v_infoState_5285_);
lean_ctor_set(v_reuseFailAlloc_5305_, 8, v_snapshotTasks_5286_);
v___x_5299_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5298_;
}
v_reusejp_5298_:
{
lean_object* v___x_5300_; lean_object* v___x_5301_; lean_object* v___x_5303_; 
v___x_5300_ = lean_st_ref_put(v___y_5244_, v___x_5299_);
v___x_5301_ = lean_box(0);
if (v_isShared_5276_ == 0)
{
lean_ctor_set(v___x_5275_, 0, v___x_5301_);
v___x_5303_ = v___x_5275_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5304_; 
v_reuseFailAlloc_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5304_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5304_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
return v___x_5303_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5311_, lean_object* v_data_5312_, lean_object* v_ref_5313_, lean_object* v_msg_5314_, lean_object* v___y_5315_, lean_object* v___y_5316_, lean_object* v___y_5317_, lean_object* v___y_5318_, lean_object* v___y_5319_){
_start:
{
lean_object* v_res_5320_; 
v_res_5320_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5311_, v_data_5312_, v_ref_5313_, v_msg_5314_, v___y_5315_, v___y_5316_, v___y_5317_, v___y_5318_);
lean_dec(v___y_5318_);
lean_dec_ref(v___y_5317_);
lean_dec(v___y_5316_);
lean_dec_ref(v___y_5315_);
return v_res_5320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5321_, uint8_t v_collapsed_5322_, lean_object* v_tag_5323_, lean_object* v_opts_5324_, uint8_t v_clsEnabled_5325_, lean_object* v_oldTraces_5326_, lean_object* v_msg_5327_, lean_object* v_resStartStop_5328_, lean_object* v___y_5329_, lean_object* v___y_5330_, lean_object* v___y_5331_, lean_object* v___y_5332_){
_start:
{
lean_object* v_fst_5334_; lean_object* v_snd_5335_; lean_object* v___y_5337_; lean_object* v___y_5338_; lean_object* v_data_5339_; lean_object* v_fst_5350_; lean_object* v_snd_5351_; lean_object* v___x_5352_; uint8_t v___x_5353_; lean_object* v___y_5355_; lean_object* v_a_5356_; uint8_t v___y_5371_; double v___y_5402_; 
v_fst_5334_ = lean_ctor_get(v_resStartStop_5328_, 0);
lean_inc(v_fst_5334_);
v_snd_5335_ = lean_ctor_get(v_resStartStop_5328_, 1);
lean_inc(v_snd_5335_);
lean_dec_ref(v_resStartStop_5328_);
v_fst_5350_ = lean_ctor_get(v_snd_5335_, 0);
lean_inc(v_fst_5350_);
v_snd_5351_ = lean_ctor_get(v_snd_5335_, 1);
lean_inc(v_snd_5351_);
lean_dec(v_snd_5335_);
v___x_5352_ = l_Lean_trace_profiler;
v___x_5353_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5324_, v___x_5352_);
if (v___x_5353_ == 0)
{
v___y_5371_ = v___x_5353_;
goto v___jp_5370_;
}
else
{
lean_object* v___x_5407_; uint8_t v___x_5408_; 
v___x_5407_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5408_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5324_, v___x_5407_);
if (v___x_5408_ == 0)
{
lean_object* v___x_5409_; lean_object* v___x_5410_; double v___x_5411_; double v___x_5412_; double v___x_5413_; 
v___x_5409_ = l_Lean_trace_profiler_threshold;
v___x_5410_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5324_, v___x_5409_);
v___x_5411_ = lean_float_of_nat(v___x_5410_);
v___x_5412_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5413_ = lean_float_div(v___x_5411_, v___x_5412_);
v___y_5402_ = v___x_5413_;
goto v___jp_5401_;
}
else
{
lean_object* v___x_5414_; lean_object* v___x_5415_; double v___x_5416_; 
v___x_5414_ = l_Lean_trace_profiler_threshold;
v___x_5415_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5324_, v___x_5414_);
v___x_5416_ = lean_float_of_nat(v___x_5415_);
v___y_5402_ = v___x_5416_;
goto v___jp_5401_;
}
}
v___jp_5336_:
{
lean_object* v___x_5340_; 
lean_inc(v___y_5338_);
v___x_5340_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5326_, v_data_5339_, v___y_5338_, v___y_5337_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
if (lean_obj_tag(v___x_5340_) == 0)
{
lean_object* v___x_5341_; 
lean_dec_ref_known(v___x_5340_, 1);
v___x_5341_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5334_);
return v___x_5341_;
}
else
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5349_; 
lean_dec(v_fst_5334_);
v_a_5342_ = lean_ctor_get(v___x_5340_, 0);
v_isSharedCheck_5349_ = !lean_is_exclusive(v___x_5340_);
if (v_isSharedCheck_5349_ == 0)
{
v___x_5344_ = v___x_5340_;
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5340_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5349_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
lean_object* v___x_5347_; 
if (v_isShared_5345_ == 0)
{
v___x_5347_ = v___x_5344_;
goto v_reusejp_5346_;
}
else
{
lean_object* v_reuseFailAlloc_5348_; 
v_reuseFailAlloc_5348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5348_, 0, v_a_5342_);
v___x_5347_ = v_reuseFailAlloc_5348_;
goto v_reusejp_5346_;
}
v_reusejp_5346_:
{
return v___x_5347_;
}
}
}
}
v___jp_5354_:
{
uint8_t v_result_5357_; lean_object* v___x_5358_; lean_object* v___x_5359_; double v___x_5360_; lean_object* v_data_5361_; 
v_result_5357_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5334_);
v___x_5358_ = lean_box(v_result_5357_);
v___x_5359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5359_, 0, v___x_5358_);
v___x_5360_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5323_);
lean_inc_ref(v___x_5359_);
lean_inc(v_cls_5321_);
v_data_5361_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5361_, 0, v_cls_5321_);
lean_ctor_set(v_data_5361_, 1, v___x_5359_);
lean_ctor_set(v_data_5361_, 2, v_tag_5323_);
lean_ctor_set_float(v_data_5361_, sizeof(void*)*3, v___x_5360_);
lean_ctor_set_float(v_data_5361_, sizeof(void*)*3 + 8, v___x_5360_);
lean_ctor_set_uint8(v_data_5361_, sizeof(void*)*3 + 16, v_collapsed_5322_);
if (v___x_5353_ == 0)
{
lean_dec_ref_known(v___x_5359_, 1);
lean_dec(v_snd_5351_);
lean_dec(v_fst_5350_);
lean_dec_ref(v_tag_5323_);
lean_dec(v_cls_5321_);
v___y_5337_ = v_a_5356_;
v___y_5338_ = v___y_5355_;
v_data_5339_ = v_data_5361_;
goto v___jp_5336_;
}
else
{
lean_object* v_data_5362_; double v___x_5363_; double v___x_5364_; 
lean_dec_ref_known(v_data_5361_, 3);
v_data_5362_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5362_, 0, v_cls_5321_);
lean_ctor_set(v_data_5362_, 1, v___x_5359_);
lean_ctor_set(v_data_5362_, 2, v_tag_5323_);
v___x_5363_ = lean_unbox_float(v_fst_5350_);
lean_dec(v_fst_5350_);
lean_ctor_set_float(v_data_5362_, sizeof(void*)*3, v___x_5363_);
v___x_5364_ = lean_unbox_float(v_snd_5351_);
lean_dec(v_snd_5351_);
lean_ctor_set_float(v_data_5362_, sizeof(void*)*3 + 8, v___x_5364_);
lean_ctor_set_uint8(v_data_5362_, sizeof(void*)*3 + 16, v_collapsed_5322_);
v___y_5337_ = v_a_5356_;
v___y_5338_ = v___y_5355_;
v_data_5339_ = v_data_5362_;
goto v___jp_5336_;
}
}
v___jp_5365_:
{
lean_object* v_ref_5366_; lean_object* v___x_5367_; 
v_ref_5366_ = lean_ctor_get(v___y_5331_, 5);
lean_inc(v___y_5332_);
lean_inc_ref(v___y_5331_);
lean_inc(v___y_5330_);
lean_inc_ref(v___y_5329_);
lean_inc(v_fst_5334_);
v___x_5367_ = lean_apply_6(v_msg_5327_, v_fst_5334_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_, lean_box(0));
if (lean_obj_tag(v___x_5367_) == 0)
{
lean_object* v_a_5368_; 
v_a_5368_ = lean_ctor_get(v___x_5367_, 0);
lean_inc(v_a_5368_);
lean_dec_ref_known(v___x_5367_, 1);
v___y_5355_ = v_ref_5366_;
v_a_5356_ = v_a_5368_;
goto v___jp_5354_;
}
else
{
lean_object* v___x_5369_; 
lean_dec_ref_known(v___x_5367_, 1);
v___x_5369_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5355_ = v_ref_5366_;
v_a_5356_ = v___x_5369_;
goto v___jp_5354_;
}
}
v___jp_5370_:
{
if (v_clsEnabled_5325_ == 0)
{
if (v___y_5371_ == 0)
{
lean_object* v___x_5372_; lean_object* v_traceState_5373_; lean_object* v_env_5374_; lean_object* v_nextMacroScope_5375_; lean_object* v_ngen_5376_; lean_object* v_auxDeclNGen_5377_; lean_object* v_cache_5378_; lean_object* v_messages_5379_; lean_object* v_infoState_5380_; lean_object* v_snapshotTasks_5381_; lean_object* v___x_5383_; uint8_t v_isShared_5384_; uint8_t v_isSharedCheck_5400_; 
lean_dec(v_snd_5351_);
lean_dec(v_fst_5350_);
lean_dec_ref(v_msg_5327_);
lean_dec_ref(v_tag_5323_);
lean_dec(v_cls_5321_);
v___x_5372_ = lean_st_ref_take(v___y_5332_);
v_traceState_5373_ = lean_ctor_get(v___x_5372_, 4);
v_env_5374_ = lean_ctor_get(v___x_5372_, 0);
v_nextMacroScope_5375_ = lean_ctor_get(v___x_5372_, 1);
v_ngen_5376_ = lean_ctor_get(v___x_5372_, 2);
v_auxDeclNGen_5377_ = lean_ctor_get(v___x_5372_, 3);
v_cache_5378_ = lean_ctor_get(v___x_5372_, 5);
v_messages_5379_ = lean_ctor_get(v___x_5372_, 6);
v_infoState_5380_ = lean_ctor_get(v___x_5372_, 7);
v_snapshotTasks_5381_ = lean_ctor_get(v___x_5372_, 8);
v_isSharedCheck_5400_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5400_ == 0)
{
v___x_5383_ = v___x_5372_;
v_isShared_5384_ = v_isSharedCheck_5400_;
goto v_resetjp_5382_;
}
else
{
lean_inc(v_snapshotTasks_5381_);
lean_inc(v_infoState_5380_);
lean_inc(v_messages_5379_);
lean_inc(v_cache_5378_);
lean_inc(v_traceState_5373_);
lean_inc(v_auxDeclNGen_5377_);
lean_inc(v_ngen_5376_);
lean_inc(v_nextMacroScope_5375_);
lean_inc(v_env_5374_);
lean_dec(v___x_5372_);
v___x_5383_ = lean_box(0);
v_isShared_5384_ = v_isSharedCheck_5400_;
goto v_resetjp_5382_;
}
v_resetjp_5382_:
{
uint64_t v_tid_5385_; lean_object* v_traces_5386_; lean_object* v___x_5388_; uint8_t v_isShared_5389_; uint8_t v_isSharedCheck_5399_; 
v_tid_5385_ = lean_ctor_get_uint64(v_traceState_5373_, sizeof(void*)*1);
v_traces_5386_ = lean_ctor_get(v_traceState_5373_, 0);
v_isSharedCheck_5399_ = !lean_is_exclusive(v_traceState_5373_);
if (v_isSharedCheck_5399_ == 0)
{
v___x_5388_ = v_traceState_5373_;
v_isShared_5389_ = v_isSharedCheck_5399_;
goto v_resetjp_5387_;
}
else
{
lean_inc(v_traces_5386_);
lean_dec(v_traceState_5373_);
v___x_5388_ = lean_box(0);
v_isShared_5389_ = v_isSharedCheck_5399_;
goto v_resetjp_5387_;
}
v_resetjp_5387_:
{
lean_object* v___x_5390_; lean_object* v___x_5392_; 
v___x_5390_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5326_, v_traces_5386_);
lean_dec_ref(v_traces_5386_);
if (v_isShared_5389_ == 0)
{
lean_ctor_set(v___x_5388_, 0, v___x_5390_);
v___x_5392_ = v___x_5388_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5398_; 
v_reuseFailAlloc_5398_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5398_, 0, v___x_5390_);
lean_ctor_set_uint64(v_reuseFailAlloc_5398_, sizeof(void*)*1, v_tid_5385_);
v___x_5392_ = v_reuseFailAlloc_5398_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
lean_object* v___x_5394_; 
if (v_isShared_5384_ == 0)
{
lean_ctor_set(v___x_5383_, 4, v___x_5392_);
v___x_5394_ = v___x_5383_;
goto v_reusejp_5393_;
}
else
{
lean_object* v_reuseFailAlloc_5397_; 
v_reuseFailAlloc_5397_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5397_, 0, v_env_5374_);
lean_ctor_set(v_reuseFailAlloc_5397_, 1, v_nextMacroScope_5375_);
lean_ctor_set(v_reuseFailAlloc_5397_, 2, v_ngen_5376_);
lean_ctor_set(v_reuseFailAlloc_5397_, 3, v_auxDeclNGen_5377_);
lean_ctor_set(v_reuseFailAlloc_5397_, 4, v___x_5392_);
lean_ctor_set(v_reuseFailAlloc_5397_, 5, v_cache_5378_);
lean_ctor_set(v_reuseFailAlloc_5397_, 6, v_messages_5379_);
lean_ctor_set(v_reuseFailAlloc_5397_, 7, v_infoState_5380_);
lean_ctor_set(v_reuseFailAlloc_5397_, 8, v_snapshotTasks_5381_);
v___x_5394_ = v_reuseFailAlloc_5397_;
goto v_reusejp_5393_;
}
v_reusejp_5393_:
{
lean_object* v___x_5395_; lean_object* v___x_5396_; 
v___x_5395_ = lean_st_ref_put(v___y_5332_, v___x_5394_);
v___x_5396_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5334_);
return v___x_5396_;
}
}
}
}
}
else
{
goto v___jp_5365_;
}
}
else
{
goto v___jp_5365_;
}
}
v___jp_5401_:
{
double v___x_5403_; double v___x_5404_; double v___x_5405_; uint8_t v___x_5406_; 
v___x_5403_ = lean_unbox_float(v_snd_5351_);
v___x_5404_ = lean_unbox_float(v_fst_5350_);
v___x_5405_ = lean_float_sub(v___x_5403_, v___x_5404_);
v___x_5406_ = lean_float_decLt(v___y_5402_, v___x_5405_);
v___y_5371_ = v___x_5406_;
goto v___jp_5370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5417_, lean_object* v_collapsed_5418_, lean_object* v_tag_5419_, lean_object* v_opts_5420_, lean_object* v_clsEnabled_5421_, lean_object* v_oldTraces_5422_, lean_object* v_msg_5423_, lean_object* v_resStartStop_5424_, lean_object* v___y_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_){
_start:
{
uint8_t v_collapsed_boxed_5430_; uint8_t v_clsEnabled_boxed_5431_; lean_object* v_res_5432_; 
v_collapsed_boxed_5430_ = lean_unbox(v_collapsed_5418_);
v_clsEnabled_boxed_5431_ = lean_unbox(v_clsEnabled_5421_);
v_res_5432_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5417_, v_collapsed_boxed_5430_, v_tag_5419_, v_opts_5420_, v_clsEnabled_boxed_5431_, v_oldTraces_5422_, v_msg_5423_, v_resStartStop_5424_, v___y_5425_, v___y_5426_, v___y_5427_, v___y_5428_);
lean_dec(v___y_5428_);
lean_dec_ref(v___y_5427_);
lean_dec(v___y_5426_);
lean_dec_ref(v___y_5425_);
lean_dec_ref(v_opts_5420_);
return v_res_5432_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5437_; lean_object* v___x_5438_; lean_object* v___x_5439_; 
v_cls_5437_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5438_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5439_ = l_Lean_Name_append(v___x_5438_, v_cls_5437_);
return v___x_5439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5440_, lean_object* v_a_5441_, lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v___y_5447_; lean_object* v_options_5465_; lean_object* v_inheritedTraceOptions_5466_; uint8_t v_hasTrace_5467_; lean_object* v_cls_5468_; uint8_t v___x_5469_; uint8_t v___x_5470_; 
v_options_5465_ = lean_ctor_get(v_a_5443_, 2);
v_inheritedTraceOptions_5466_ = lean_ctor_get(v_a_5443_, 13);
v_hasTrace_5467_ = lean_ctor_get_uint8(v_options_5465_, sizeof(void*)*1);
v_cls_5468_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5469_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5440_);
v___x_5470_ = 1;
if (v_hasTrace_5467_ == 0)
{
lean_object* v___x_5471_; 
v___x_5471_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5469_, v_e_5440_, v___x_5470_, v_cls_5468_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
v___y_5447_ = v___x_5471_;
goto v___jp_5446_;
}
else
{
lean_object* v___f_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; uint8_t v___x_5475_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v_a_5479_; lean_object* v___y_5492_; lean_object* v___y_5493_; lean_object* v_a_5494_; 
v___f_5472_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5473_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5474_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5475_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5466_, v_options_5465_, v___x_5474_);
if (v___x_5475_ == 0)
{
lean_object* v___x_5544_; uint8_t v___x_5545_; 
v___x_5544_ = l_Lean_trace_profiler;
v___x_5545_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5465_, v___x_5544_);
if (v___x_5545_ == 0)
{
lean_object* v___x_5546_; 
v___x_5546_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5469_, v_e_5440_, v___x_5470_, v_cls_5468_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
v___y_5447_ = v___x_5546_;
goto v___jp_5446_;
}
else
{
goto v___jp_5503_;
}
}
else
{
goto v___jp_5503_;
}
v___jp_5476_:
{
lean_object* v___x_5480_; double v___x_5481_; double v___x_5482_; double v___x_5483_; double v___x_5484_; double v___x_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5480_ = lean_io_mono_nanos_now();
v___x_5481_ = lean_float_of_nat(v___y_5478_);
v___x_5482_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5483_ = lean_float_div(v___x_5481_, v___x_5482_);
v___x_5484_ = lean_float_of_nat(v___x_5480_);
v___x_5485_ = lean_float_div(v___x_5484_, v___x_5482_);
v___x_5486_ = lean_box_float(v___x_5483_);
v___x_5487_ = lean_box_float(v___x_5485_);
v___x_5488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5488_, 0, v___x_5486_);
lean_ctor_set(v___x_5488_, 1, v___x_5487_);
v___x_5489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5489_, 0, v_a_5479_);
lean_ctor_set(v___x_5489_, 1, v___x_5488_);
v___x_5490_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5468_, v___x_5470_, v___x_5473_, v_options_5465_, v___x_5475_, v___y_5477_, v___f_5472_, v___x_5489_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
v___y_5447_ = v___x_5490_;
goto v___jp_5446_;
}
v___jp_5491_:
{
lean_object* v___x_5495_; double v___x_5496_; double v___x_5497_; lean_object* v___x_5498_; lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5502_; 
v___x_5495_ = lean_io_get_num_heartbeats();
v___x_5496_ = lean_float_of_nat(v___y_5493_);
v___x_5497_ = lean_float_of_nat(v___x_5495_);
v___x_5498_ = lean_box_float(v___x_5496_);
v___x_5499_ = lean_box_float(v___x_5497_);
v___x_5500_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5500_, 0, v___x_5498_);
lean_ctor_set(v___x_5500_, 1, v___x_5499_);
v___x_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5501_, 0, v_a_5494_);
lean_ctor_set(v___x_5501_, 1, v___x_5500_);
v___x_5502_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5468_, v___x_5470_, v___x_5473_, v_options_5465_, v___x_5475_, v___y_5492_, v___f_5472_, v___x_5501_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
v___y_5447_ = v___x_5502_;
goto v___jp_5446_;
}
v___jp_5503_:
{
lean_object* v___x_5504_; lean_object* v_a_5505_; lean_object* v___x_5506_; uint8_t v___x_5507_; 
v___x_5504_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5444_);
v_a_5505_ = lean_ctor_get(v___x_5504_, 0);
lean_inc(v_a_5505_);
lean_dec_ref(v___x_5504_);
v___x_5506_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5507_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5465_, v___x_5506_);
if (v___x_5507_ == 0)
{
lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5508_ = lean_io_mono_nanos_now();
v___x_5509_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5469_, v_e_5440_, v___x_5470_, v_cls_5468_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
if (lean_obj_tag(v___x_5509_) == 0)
{
lean_object* v_a_5510_; lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5517_; 
v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5517_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5517_ == 0)
{
v___x_5512_ = v___x_5509_;
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
else
{
lean_inc(v_a_5510_);
lean_dec(v___x_5509_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5517_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v___x_5515_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set_tag(v___x_5512_, 1);
v___x_5515_ = v___x_5512_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_a_5510_);
v___x_5515_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
v___y_5477_ = v_a_5505_;
v___y_5478_ = v___x_5508_;
v_a_5479_ = v___x_5515_;
goto v___jp_5476_;
}
}
}
else
{
lean_object* v_a_5518_; lean_object* v___x_5520_; uint8_t v_isShared_5521_; uint8_t v_isSharedCheck_5525_; 
v_a_5518_ = lean_ctor_get(v___x_5509_, 0);
v_isSharedCheck_5525_ = !lean_is_exclusive(v___x_5509_);
if (v_isSharedCheck_5525_ == 0)
{
v___x_5520_ = v___x_5509_;
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
else
{
lean_inc(v_a_5518_);
lean_dec(v___x_5509_);
v___x_5520_ = lean_box(0);
v_isShared_5521_ = v_isSharedCheck_5525_;
goto v_resetjp_5519_;
}
v_resetjp_5519_:
{
lean_object* v___x_5523_; 
if (v_isShared_5521_ == 0)
{
lean_ctor_set_tag(v___x_5520_, 0);
v___x_5523_ = v___x_5520_;
goto v_reusejp_5522_;
}
else
{
lean_object* v_reuseFailAlloc_5524_; 
v_reuseFailAlloc_5524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
v___x_5523_ = v_reuseFailAlloc_5524_;
goto v_reusejp_5522_;
}
v_reusejp_5522_:
{
v___y_5477_ = v_a_5505_;
v___y_5478_ = v___x_5508_;
v_a_5479_ = v___x_5523_;
goto v___jp_5476_;
}
}
}
}
else
{
lean_object* v___x_5526_; lean_object* v___x_5527_; 
v___x_5526_ = lean_io_get_num_heartbeats();
v___x_5527_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_5469_, v_e_5440_, v___x_5470_, v_cls_5468_, v_a_5441_, v_a_5442_, v_a_5443_, v_a_5444_);
if (lean_obj_tag(v___x_5527_) == 0)
{
lean_object* v_a_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5535_; 
v_a_5528_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5535_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5535_ == 0)
{
v___x_5530_ = v___x_5527_;
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_a_5528_);
lean_dec(v___x_5527_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5535_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5533_; 
if (v_isShared_5531_ == 0)
{
lean_ctor_set_tag(v___x_5530_, 1);
v___x_5533_ = v___x_5530_;
goto v_reusejp_5532_;
}
else
{
lean_object* v_reuseFailAlloc_5534_; 
v_reuseFailAlloc_5534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5534_, 0, v_a_5528_);
v___x_5533_ = v_reuseFailAlloc_5534_;
goto v_reusejp_5532_;
}
v_reusejp_5532_:
{
v___y_5492_ = v_a_5505_;
v___y_5493_ = v___x_5526_;
v_a_5494_ = v___x_5533_;
goto v___jp_5491_;
}
}
}
else
{
lean_object* v_a_5536_; lean_object* v___x_5538_; uint8_t v_isShared_5539_; uint8_t v_isSharedCheck_5543_; 
v_a_5536_ = lean_ctor_get(v___x_5527_, 0);
v_isSharedCheck_5543_ = !lean_is_exclusive(v___x_5527_);
if (v_isSharedCheck_5543_ == 0)
{
v___x_5538_ = v___x_5527_;
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
else
{
lean_inc(v_a_5536_);
lean_dec(v___x_5527_);
v___x_5538_ = lean_box(0);
v_isShared_5539_ = v_isSharedCheck_5543_;
goto v_resetjp_5537_;
}
v_resetjp_5537_:
{
lean_object* v___x_5541_; 
if (v_isShared_5539_ == 0)
{
lean_ctor_set_tag(v___x_5538_, 0);
v___x_5541_ = v___x_5538_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v_a_5536_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
v___y_5492_ = v_a_5505_;
v___y_5493_ = v___x_5526_;
v_a_5494_ = v___x_5541_;
goto v___jp_5491_;
}
}
}
}
}
}
v___jp_5446_:
{
if (lean_obj_tag(v___y_5447_) == 0)
{
lean_object* v_a_5448_; lean_object* v___x_5450_; uint8_t v_isShared_5451_; uint8_t v_isSharedCheck_5456_; 
v_a_5448_ = lean_ctor_get(v___y_5447_, 0);
v_isSharedCheck_5456_ = !lean_is_exclusive(v___y_5447_);
if (v_isSharedCheck_5456_ == 0)
{
v___x_5450_ = v___y_5447_;
v_isShared_5451_ = v_isSharedCheck_5456_;
goto v_resetjp_5449_;
}
else
{
lean_inc(v_a_5448_);
lean_dec(v___y_5447_);
v___x_5450_ = lean_box(0);
v_isShared_5451_ = v_isSharedCheck_5456_;
goto v_resetjp_5449_;
}
v_resetjp_5449_:
{
lean_object* v_fst_5452_; lean_object* v___x_5454_; 
v_fst_5452_ = lean_ctor_get(v_a_5448_, 0);
lean_inc(v_fst_5452_);
lean_dec(v_a_5448_);
if (v_isShared_5451_ == 0)
{
lean_ctor_set(v___x_5450_, 0, v_fst_5452_);
v___x_5454_ = v___x_5450_;
goto v_reusejp_5453_;
}
else
{
lean_object* v_reuseFailAlloc_5455_; 
v_reuseFailAlloc_5455_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5455_, 0, v_fst_5452_);
v___x_5454_ = v_reuseFailAlloc_5455_;
goto v_reusejp_5453_;
}
v_reusejp_5453_:
{
return v___x_5454_;
}
}
}
else
{
lean_object* v_a_5457_; lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5464_; 
v_a_5457_ = lean_ctor_get(v___y_5447_, 0);
v_isSharedCheck_5464_ = !lean_is_exclusive(v___y_5447_);
if (v_isSharedCheck_5464_ == 0)
{
v___x_5459_ = v___y_5447_;
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
else
{
lean_inc(v_a_5457_);
lean_dec(v___y_5447_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5464_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v___x_5462_; 
if (v_isShared_5460_ == 0)
{
v___x_5462_ = v___x_5459_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v_a_5457_);
v___x_5462_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
return v___x_5462_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5547_, lean_object* v_a_5548_, lean_object* v_a_5549_, lean_object* v_a_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_){
_start:
{
lean_object* v_res_5553_; 
v_res_5553_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5547_, v_a_5548_, v_a_5549_, v_a_5550_, v_a_5551_);
lean_dec(v_a_5551_);
lean_dec_ref(v_a_5550_);
lean_dec(v_a_5549_);
lean_dec_ref(v_a_5548_);
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5554_, lean_object* v_x_5555_, lean_object* v___y_5556_, lean_object* v___y_5557_, lean_object* v___y_5558_, lean_object* v___y_5559_){
_start:
{
lean_object* v___x_5561_; 
v___x_5561_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5555_);
return v___x_5561_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5562_, lean_object* v_x_5563_, lean_object* v___y_5564_, lean_object* v___y_5565_, lean_object* v___y_5566_, lean_object* v___y_5567_, lean_object* v___y_5568_){
_start:
{
lean_object* v_res_5569_; 
v_res_5569_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5562_, v_x_5563_, v___y_5564_, v___y_5565_, v___y_5566_, v___y_5567_);
lean_dec(v___y_5567_);
lean_dec_ref(v___y_5566_);
lean_dec(v___y_5565_);
lean_dec_ref(v___y_5564_);
return v_res_5569_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5570_, lean_object* v___y_5571_){
_start:
{
uint8_t v___x_5573_; 
v___x_5573_ = l_Lean_Expr_hasMVar(v_e_5570_);
if (v___x_5573_ == 0)
{
lean_object* v___x_5574_; 
v___x_5574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5574_, 0, v_e_5570_);
return v___x_5574_;
}
else
{
lean_object* v___x_5575_; lean_object* v_mctx_5576_; lean_object* v___x_5577_; lean_object* v_fst_5578_; lean_object* v_snd_5579_; lean_object* v___x_5580_; lean_object* v_cache_5581_; lean_object* v_zetaDeltaFVarIds_5582_; lean_object* v_postponed_5583_; lean_object* v_diag_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5593_; 
v___x_5575_ = lean_st_ref_get(v___y_5571_);
v_mctx_5576_ = lean_ctor_get(v___x_5575_, 0);
lean_inc_ref(v_mctx_5576_);
lean_dec(v___x_5575_);
v___x_5577_ = l_Lean_instantiateMVarsCore(v_mctx_5576_, v_e_5570_);
v_fst_5578_ = lean_ctor_get(v___x_5577_, 0);
lean_inc(v_fst_5578_);
v_snd_5579_ = lean_ctor_get(v___x_5577_, 1);
lean_inc(v_snd_5579_);
lean_dec_ref(v___x_5577_);
v___x_5580_ = lean_st_ref_take(v___y_5571_);
v_cache_5581_ = lean_ctor_get(v___x_5580_, 1);
v_zetaDeltaFVarIds_5582_ = lean_ctor_get(v___x_5580_, 2);
v_postponed_5583_ = lean_ctor_get(v___x_5580_, 3);
v_diag_5584_ = lean_ctor_get(v___x_5580_, 4);
v_isSharedCheck_5593_ = !lean_is_exclusive(v___x_5580_);
if (v_isSharedCheck_5593_ == 0)
{
lean_object* v_unused_5594_; 
v_unused_5594_ = lean_ctor_get(v___x_5580_, 0);
lean_dec(v_unused_5594_);
v___x_5586_ = v___x_5580_;
v_isShared_5587_ = v_isSharedCheck_5593_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_diag_5584_);
lean_inc(v_postponed_5583_);
lean_inc(v_zetaDeltaFVarIds_5582_);
lean_inc(v_cache_5581_);
lean_dec(v___x_5580_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5593_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v___x_5589_; 
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 0, v_snd_5579_);
v___x_5589_ = v___x_5586_;
goto v_reusejp_5588_;
}
else
{
lean_object* v_reuseFailAlloc_5592_; 
v_reuseFailAlloc_5592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5592_, 0, v_snd_5579_);
lean_ctor_set(v_reuseFailAlloc_5592_, 1, v_cache_5581_);
lean_ctor_set(v_reuseFailAlloc_5592_, 2, v_zetaDeltaFVarIds_5582_);
lean_ctor_set(v_reuseFailAlloc_5592_, 3, v_postponed_5583_);
lean_ctor_set(v_reuseFailAlloc_5592_, 4, v_diag_5584_);
v___x_5589_ = v_reuseFailAlloc_5592_;
goto v_reusejp_5588_;
}
v_reusejp_5588_:
{
lean_object* v___x_5590_; lean_object* v___x_5591_; 
v___x_5590_ = lean_st_ref_put(v___y_5571_, v___x_5589_);
v___x_5591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5591_, 0, v_fst_5578_);
return v___x_5591_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_){
_start:
{
lean_object* v_res_5598_; 
v_res_5598_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5595_, v___y_5596_);
lean_dec(v___y_5596_);
return v_res_5598_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5599_, lean_object* v___y_5600_, lean_object* v___y_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_){
_start:
{
lean_object* v___x_5605_; 
v___x_5605_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5599_, v___y_5601_);
return v___x_5605_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
lean_object* v_res_5612_; 
v_res_5612_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
lean_dec(v___y_5610_);
lean_dec_ref(v___y_5609_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
return v_res_5612_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5613_, lean_object* v_opts_5614_, lean_object* v_act_5615_, lean_object* v_decl_5616_, lean_object* v___y_5617_, lean_object* v___y_5618_, lean_object* v___y_5619_, lean_object* v___y_5620_){
_start:
{
lean_object* v___x_5622_; lean_object* v___x_5623_; 
lean_inc(v___y_5620_);
lean_inc_ref(v___y_5619_);
lean_inc(v___y_5618_);
lean_inc_ref(v___y_5617_);
v___x_5622_ = lean_apply_4(v_act_5615_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_);
v___x_5623_ = l_Lean_profileitIOUnsafe___redArg(v_category_5613_, v_opts_5614_, v___x_5622_, v_decl_5616_);
return v___x_5623_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5624_, lean_object* v_opts_5625_, lean_object* v_act_5626_, lean_object* v_decl_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_, lean_object* v___y_5630_, lean_object* v___y_5631_, lean_object* v___y_5632_){
_start:
{
lean_object* v_res_5633_; 
v_res_5633_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5624_, v_opts_5625_, v_act_5626_, v_decl_5627_, v___y_5628_, v___y_5629_, v___y_5630_, v___y_5631_);
lean_dec(v___y_5631_);
lean_dec_ref(v___y_5630_);
lean_dec(v___y_5629_);
lean_dec_ref(v___y_5628_);
lean_dec_ref(v_opts_5625_);
lean_dec_ref(v_category_5624_);
return v_res_5633_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5634_, lean_object* v_category_5635_, lean_object* v_opts_5636_, lean_object* v_act_5637_, lean_object* v_decl_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_){
_start:
{
lean_object* v___x_5644_; 
v___x_5644_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5635_, v_opts_5636_, v_act_5637_, v_decl_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
return v___x_5644_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5645_, lean_object* v_category_5646_, lean_object* v_opts_5647_, lean_object* v_act_5648_, lean_object* v_decl_5649_, lean_object* v___y_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_){
_start:
{
lean_object* v_res_5655_; 
v_res_5655_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5645_, v_category_5646_, v_opts_5647_, v_act_5648_, v_decl_5649_, v___y_5650_, v___y_5651_, v___y_5652_, v___y_5653_);
lean_dec(v___y_5653_);
lean_dec_ref(v___y_5652_);
lean_dec(v___y_5651_);
lean_dec_ref(v___y_5650_);
lean_dec_ref(v_opts_5647_);
lean_dec_ref(v_category_5646_);
return v_res_5655_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5656_, uint8_t v_isExporting_5657_, lean_object* v___x_5658_, lean_object* v___y_5659_, lean_object* v___x_5660_, lean_object* v_a_x3f_5661_){
_start:
{
lean_object* v___x_5663_; lean_object* v_env_5664_; lean_object* v_nextMacroScope_5665_; lean_object* v_ngen_5666_; lean_object* v_auxDeclNGen_5667_; lean_object* v_traceState_5668_; lean_object* v_messages_5669_; lean_object* v_infoState_5670_; lean_object* v_snapshotTasks_5671_; lean_object* v___x_5673_; uint8_t v_isShared_5674_; uint8_t v_isSharedCheck_5696_; 
v___x_5663_ = lean_st_ref_take(v___y_5656_);
v_env_5664_ = lean_ctor_get(v___x_5663_, 0);
v_nextMacroScope_5665_ = lean_ctor_get(v___x_5663_, 1);
v_ngen_5666_ = lean_ctor_get(v___x_5663_, 2);
v_auxDeclNGen_5667_ = lean_ctor_get(v___x_5663_, 3);
v_traceState_5668_ = lean_ctor_get(v___x_5663_, 4);
v_messages_5669_ = lean_ctor_get(v___x_5663_, 6);
v_infoState_5670_ = lean_ctor_get(v___x_5663_, 7);
v_snapshotTasks_5671_ = lean_ctor_get(v___x_5663_, 8);
v_isSharedCheck_5696_ = !lean_is_exclusive(v___x_5663_);
if (v_isSharedCheck_5696_ == 0)
{
lean_object* v_unused_5697_; 
v_unused_5697_ = lean_ctor_get(v___x_5663_, 5);
lean_dec(v_unused_5697_);
v___x_5673_ = v___x_5663_;
v_isShared_5674_ = v_isSharedCheck_5696_;
goto v_resetjp_5672_;
}
else
{
lean_inc(v_snapshotTasks_5671_);
lean_inc(v_infoState_5670_);
lean_inc(v_messages_5669_);
lean_inc(v_traceState_5668_);
lean_inc(v_auxDeclNGen_5667_);
lean_inc(v_ngen_5666_);
lean_inc(v_nextMacroScope_5665_);
lean_inc(v_env_5664_);
lean_dec(v___x_5663_);
v___x_5673_ = lean_box(0);
v_isShared_5674_ = v_isSharedCheck_5696_;
goto v_resetjp_5672_;
}
v_resetjp_5672_:
{
lean_object* v___x_5675_; lean_object* v___x_5677_; 
v___x_5675_ = l_Lean_Environment_setExporting(v_env_5664_, v_isExporting_5657_);
if (v_isShared_5674_ == 0)
{
lean_ctor_set(v___x_5673_, 5, v___x_5658_);
lean_ctor_set(v___x_5673_, 0, v___x_5675_);
v___x_5677_ = v___x_5673_;
goto v_reusejp_5676_;
}
else
{
lean_object* v_reuseFailAlloc_5695_; 
v_reuseFailAlloc_5695_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5695_, 0, v___x_5675_);
lean_ctor_set(v_reuseFailAlloc_5695_, 1, v_nextMacroScope_5665_);
lean_ctor_set(v_reuseFailAlloc_5695_, 2, v_ngen_5666_);
lean_ctor_set(v_reuseFailAlloc_5695_, 3, v_auxDeclNGen_5667_);
lean_ctor_set(v_reuseFailAlloc_5695_, 4, v_traceState_5668_);
lean_ctor_set(v_reuseFailAlloc_5695_, 5, v___x_5658_);
lean_ctor_set(v_reuseFailAlloc_5695_, 6, v_messages_5669_);
lean_ctor_set(v_reuseFailAlloc_5695_, 7, v_infoState_5670_);
lean_ctor_set(v_reuseFailAlloc_5695_, 8, v_snapshotTasks_5671_);
v___x_5677_ = v_reuseFailAlloc_5695_;
goto v_reusejp_5676_;
}
v_reusejp_5676_:
{
lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v_mctx_5680_; lean_object* v_zetaDeltaFVarIds_5681_; lean_object* v_postponed_5682_; lean_object* v_diag_5683_; lean_object* v___x_5685_; uint8_t v_isShared_5686_; uint8_t v_isSharedCheck_5693_; 
v___x_5678_ = lean_st_ref_put(v___y_5656_, v___x_5677_);
v___x_5679_ = lean_st_ref_take(v___y_5659_);
v_mctx_5680_ = lean_ctor_get(v___x_5679_, 0);
v_zetaDeltaFVarIds_5681_ = lean_ctor_get(v___x_5679_, 2);
v_postponed_5682_ = lean_ctor_get(v___x_5679_, 3);
v_diag_5683_ = lean_ctor_get(v___x_5679_, 4);
v_isSharedCheck_5693_ = !lean_is_exclusive(v___x_5679_);
if (v_isSharedCheck_5693_ == 0)
{
lean_object* v_unused_5694_; 
v_unused_5694_ = lean_ctor_get(v___x_5679_, 1);
lean_dec(v_unused_5694_);
v___x_5685_ = v___x_5679_;
v_isShared_5686_ = v_isSharedCheck_5693_;
goto v_resetjp_5684_;
}
else
{
lean_inc(v_diag_5683_);
lean_inc(v_postponed_5682_);
lean_inc(v_zetaDeltaFVarIds_5681_);
lean_inc(v_mctx_5680_);
lean_dec(v___x_5679_);
v___x_5685_ = lean_box(0);
v_isShared_5686_ = v_isSharedCheck_5693_;
goto v_resetjp_5684_;
}
v_resetjp_5684_:
{
lean_object* v___x_5688_; 
if (v_isShared_5686_ == 0)
{
lean_ctor_set(v___x_5685_, 1, v___x_5660_);
v___x_5688_ = v___x_5685_;
goto v_reusejp_5687_;
}
else
{
lean_object* v_reuseFailAlloc_5692_; 
v_reuseFailAlloc_5692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5692_, 0, v_mctx_5680_);
lean_ctor_set(v_reuseFailAlloc_5692_, 1, v___x_5660_);
lean_ctor_set(v_reuseFailAlloc_5692_, 2, v_zetaDeltaFVarIds_5681_);
lean_ctor_set(v_reuseFailAlloc_5692_, 3, v_postponed_5682_);
lean_ctor_set(v_reuseFailAlloc_5692_, 4, v_diag_5683_);
v___x_5688_ = v_reuseFailAlloc_5692_;
goto v_reusejp_5687_;
}
v_reusejp_5687_:
{
lean_object* v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; 
v___x_5689_ = lean_st_ref_put(v___y_5659_, v___x_5688_);
v___x_5690_ = lean_box(0);
v___x_5691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
return v___x_5691_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5698_, lean_object* v_isExporting_5699_, lean_object* v___x_5700_, lean_object* v___y_5701_, lean_object* v___x_5702_, lean_object* v_a_x3f_5703_, lean_object* v___y_5704_){
_start:
{
uint8_t v_isExporting_boxed_5705_; lean_object* v_res_5706_; 
v_isExporting_boxed_5705_ = lean_unbox(v_isExporting_5699_);
v_res_5706_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5698_, v_isExporting_boxed_5705_, v___x_5700_, v___y_5701_, v___x_5702_, v_a_x3f_5703_);
lean_dec(v_a_x3f_5703_);
lean_dec(v___y_5701_);
lean_dec(v___y_5698_);
return v_res_5706_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5707_; 
v___x_5707_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5707_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5708_; lean_object* v___x_5709_; 
v___x_5708_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5709_, 0, v___x_5708_);
return v___x_5709_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5710_; lean_object* v___x_5711_; 
v___x_5710_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5711_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5711_, 0, v___x_5710_);
lean_ctor_set(v___x_5711_, 1, v___x_5710_);
return v___x_5711_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5712_; lean_object* v___x_5713_; 
v___x_5712_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5713_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5712_);
lean_ctor_set(v___x_5713_, 1, v___x_5712_);
lean_ctor_set(v___x_5713_, 2, v___x_5712_);
lean_ctor_set(v___x_5713_, 3, v___x_5712_);
lean_ctor_set(v___x_5713_, 4, v___x_5712_);
lean_ctor_set(v___x_5713_, 5, v___x_5712_);
return v___x_5713_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5714_, uint8_t v_isExporting_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_){
_start:
{
lean_object* v___x_5721_; lean_object* v_env_5722_; uint8_t v_isExporting_5723_; lean_object* v___x_5789_; uint8_t v_isModule_5790_; 
v___x_5721_ = lean_st_ref_get(v___y_5719_);
v_env_5722_ = lean_ctor_get(v___x_5721_, 0);
lean_inc_ref(v_env_5722_);
lean_dec(v___x_5721_);
v_isExporting_5723_ = lean_ctor_get_uint8(v_env_5722_, sizeof(void*)*8);
v___x_5789_ = l_Lean_Environment_header(v_env_5722_);
lean_dec_ref(v_env_5722_);
v_isModule_5790_ = lean_ctor_get_uint8(v___x_5789_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5789_);
if (v_isModule_5790_ == 0)
{
lean_object* v___x_5791_; 
lean_inc(v___y_5719_);
lean_inc_ref(v___y_5718_);
lean_inc(v___y_5717_);
lean_inc_ref(v___y_5716_);
v___x_5791_ = lean_apply_5(v_x_5714_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, lean_box(0));
return v___x_5791_;
}
else
{
if (v_isExporting_5723_ == 0)
{
if (v_isExporting_5715_ == 0)
{
lean_object* v___x_5792_; 
lean_inc(v___y_5719_);
lean_inc_ref(v___y_5718_);
lean_inc(v___y_5717_);
lean_inc_ref(v___y_5716_);
v___x_5792_ = lean_apply_5(v_x_5714_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, lean_box(0));
return v___x_5792_;
}
else
{
goto v___jp_5724_;
}
}
else
{
if (v_isExporting_5715_ == 0)
{
goto v___jp_5724_;
}
else
{
lean_object* v___x_5793_; 
lean_inc(v___y_5719_);
lean_inc_ref(v___y_5718_);
lean_inc(v___y_5717_);
lean_inc_ref(v___y_5716_);
v___x_5793_ = lean_apply_5(v_x_5714_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, lean_box(0));
return v___x_5793_;
}
}
}
v___jp_5724_:
{
lean_object* v___x_5725_; lean_object* v_env_5726_; lean_object* v_nextMacroScope_5727_; lean_object* v_ngen_5728_; lean_object* v_auxDeclNGen_5729_; lean_object* v_traceState_5730_; lean_object* v_messages_5731_; lean_object* v_infoState_5732_; lean_object* v_snapshotTasks_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5787_; 
v___x_5725_ = lean_st_ref_take(v___y_5719_);
v_env_5726_ = lean_ctor_get(v___x_5725_, 0);
v_nextMacroScope_5727_ = lean_ctor_get(v___x_5725_, 1);
v_ngen_5728_ = lean_ctor_get(v___x_5725_, 2);
v_auxDeclNGen_5729_ = lean_ctor_get(v___x_5725_, 3);
v_traceState_5730_ = lean_ctor_get(v___x_5725_, 4);
v_messages_5731_ = lean_ctor_get(v___x_5725_, 6);
v_infoState_5732_ = lean_ctor_get(v___x_5725_, 7);
v_snapshotTasks_5733_ = lean_ctor_get(v___x_5725_, 8);
v_isSharedCheck_5787_ = !lean_is_exclusive(v___x_5725_);
if (v_isSharedCheck_5787_ == 0)
{
lean_object* v_unused_5788_; 
v_unused_5788_ = lean_ctor_get(v___x_5725_, 5);
lean_dec(v_unused_5788_);
v___x_5735_ = v___x_5725_;
v_isShared_5736_ = v_isSharedCheck_5787_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_snapshotTasks_5733_);
lean_inc(v_infoState_5732_);
lean_inc(v_messages_5731_);
lean_inc(v_traceState_5730_);
lean_inc(v_auxDeclNGen_5729_);
lean_inc(v_ngen_5728_);
lean_inc(v_nextMacroScope_5727_);
lean_inc(v_env_5726_);
lean_dec(v___x_5725_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5787_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v___x_5737_; lean_object* v___x_5738_; lean_object* v___x_5740_; 
v___x_5737_ = l_Lean_Environment_setExporting(v_env_5726_, v_isExporting_5715_);
v___x_5738_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 5, v___x_5738_);
lean_ctor_set(v___x_5735_, 0, v___x_5737_);
v___x_5740_ = v___x_5735_;
goto v_reusejp_5739_;
}
else
{
lean_object* v_reuseFailAlloc_5786_; 
v_reuseFailAlloc_5786_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5786_, 0, v___x_5737_);
lean_ctor_set(v_reuseFailAlloc_5786_, 1, v_nextMacroScope_5727_);
lean_ctor_set(v_reuseFailAlloc_5786_, 2, v_ngen_5728_);
lean_ctor_set(v_reuseFailAlloc_5786_, 3, v_auxDeclNGen_5729_);
lean_ctor_set(v_reuseFailAlloc_5786_, 4, v_traceState_5730_);
lean_ctor_set(v_reuseFailAlloc_5786_, 5, v___x_5738_);
lean_ctor_set(v_reuseFailAlloc_5786_, 6, v_messages_5731_);
lean_ctor_set(v_reuseFailAlloc_5786_, 7, v_infoState_5732_);
lean_ctor_set(v_reuseFailAlloc_5786_, 8, v_snapshotTasks_5733_);
v___x_5740_ = v_reuseFailAlloc_5786_;
goto v_reusejp_5739_;
}
v_reusejp_5739_:
{
lean_object* v___x_5741_; lean_object* v___x_5742_; lean_object* v_mctx_5743_; lean_object* v_zetaDeltaFVarIds_5744_; lean_object* v_postponed_5745_; lean_object* v_diag_5746_; lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5784_; 
v___x_5741_ = lean_st_ref_put(v___y_5719_, v___x_5740_);
v___x_5742_ = lean_st_ref_take(v___y_5717_);
v_mctx_5743_ = lean_ctor_get(v___x_5742_, 0);
v_zetaDeltaFVarIds_5744_ = lean_ctor_get(v___x_5742_, 2);
v_postponed_5745_ = lean_ctor_get(v___x_5742_, 3);
v_diag_5746_ = lean_ctor_get(v___x_5742_, 4);
v_isSharedCheck_5784_ = !lean_is_exclusive(v___x_5742_);
if (v_isSharedCheck_5784_ == 0)
{
lean_object* v_unused_5785_; 
v_unused_5785_ = lean_ctor_get(v___x_5742_, 1);
lean_dec(v_unused_5785_);
v___x_5748_ = v___x_5742_;
v_isShared_5749_ = v_isSharedCheck_5784_;
goto v_resetjp_5747_;
}
else
{
lean_inc(v_diag_5746_);
lean_inc(v_postponed_5745_);
lean_inc(v_zetaDeltaFVarIds_5744_);
lean_inc(v_mctx_5743_);
lean_dec(v___x_5742_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5784_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5750_; lean_object* v___x_5752_; 
v___x_5750_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5749_ == 0)
{
lean_ctor_set(v___x_5748_, 1, v___x_5750_);
v___x_5752_ = v___x_5748_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5783_; 
v_reuseFailAlloc_5783_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5783_, 0, v_mctx_5743_);
lean_ctor_set(v_reuseFailAlloc_5783_, 1, v___x_5750_);
lean_ctor_set(v_reuseFailAlloc_5783_, 2, v_zetaDeltaFVarIds_5744_);
lean_ctor_set(v_reuseFailAlloc_5783_, 3, v_postponed_5745_);
lean_ctor_set(v_reuseFailAlloc_5783_, 4, v_diag_5746_);
v___x_5752_ = v_reuseFailAlloc_5783_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
lean_object* v___x_5753_; lean_object* v_r_5754_; 
v___x_5753_ = lean_st_ref_put(v___y_5717_, v___x_5752_);
lean_inc(v___y_5719_);
lean_inc_ref(v___y_5718_);
lean_inc(v___y_5717_);
lean_inc_ref(v___y_5716_);
v_r_5754_ = lean_apply_5(v_x_5714_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_, lean_box(0));
if (lean_obj_tag(v_r_5754_) == 0)
{
lean_object* v_a_5755_; lean_object* v___x_5757_; uint8_t v_isShared_5758_; uint8_t v_isSharedCheck_5771_; 
v_a_5755_ = lean_ctor_get(v_r_5754_, 0);
v_isSharedCheck_5771_ = !lean_is_exclusive(v_r_5754_);
if (v_isSharedCheck_5771_ == 0)
{
v___x_5757_ = v_r_5754_;
v_isShared_5758_ = v_isSharedCheck_5771_;
goto v_resetjp_5756_;
}
else
{
lean_inc(v_a_5755_);
lean_dec(v_r_5754_);
v___x_5757_ = lean_box(0);
v_isShared_5758_ = v_isSharedCheck_5771_;
goto v_resetjp_5756_;
}
v_resetjp_5756_:
{
lean_object* v___x_5760_; 
lean_inc(v_a_5755_);
if (v_isShared_5758_ == 0)
{
lean_ctor_set_tag(v___x_5757_, 1);
v___x_5760_ = v___x_5757_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5770_; 
v_reuseFailAlloc_5770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5770_, 0, v_a_5755_);
v___x_5760_ = v_reuseFailAlloc_5770_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
lean_object* v___x_5761_; lean_object* v___x_5763_; uint8_t v_isShared_5764_; uint8_t v_isSharedCheck_5768_; 
v___x_5761_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5719_, v_isExporting_5723_, v___x_5738_, v___y_5717_, v___x_5750_, v___x_5760_);
lean_dec_ref(v___x_5760_);
v_isSharedCheck_5768_ = !lean_is_exclusive(v___x_5761_);
if (v_isSharedCheck_5768_ == 0)
{
lean_object* v_unused_5769_; 
v_unused_5769_ = lean_ctor_get(v___x_5761_, 0);
lean_dec(v_unused_5769_);
v___x_5763_ = v___x_5761_;
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
else
{
lean_dec(v___x_5761_);
v___x_5763_ = lean_box(0);
v_isShared_5764_ = v_isSharedCheck_5768_;
goto v_resetjp_5762_;
}
v_resetjp_5762_:
{
lean_object* v___x_5766_; 
if (v_isShared_5764_ == 0)
{
lean_ctor_set(v___x_5763_, 0, v_a_5755_);
v___x_5766_ = v___x_5763_;
goto v_reusejp_5765_;
}
else
{
lean_object* v_reuseFailAlloc_5767_; 
v_reuseFailAlloc_5767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5767_, 0, v_a_5755_);
v___x_5766_ = v_reuseFailAlloc_5767_;
goto v_reusejp_5765_;
}
v_reusejp_5765_:
{
return v___x_5766_;
}
}
}
}
}
else
{
lean_object* v_a_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; lean_object* v___x_5776_; uint8_t v_isShared_5777_; uint8_t v_isSharedCheck_5781_; 
v_a_5772_ = lean_ctor_get(v_r_5754_, 0);
lean_inc(v_a_5772_);
lean_dec_ref_known(v_r_5754_, 1);
v___x_5773_ = lean_box(0);
v___x_5774_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5719_, v_isExporting_5723_, v___x_5738_, v___y_5717_, v___x_5750_, v___x_5773_);
v_isSharedCheck_5781_ = !lean_is_exclusive(v___x_5774_);
if (v_isSharedCheck_5781_ == 0)
{
lean_object* v_unused_5782_; 
v_unused_5782_ = lean_ctor_get(v___x_5774_, 0);
lean_dec(v_unused_5782_);
v___x_5776_ = v___x_5774_;
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
else
{
lean_dec(v___x_5774_);
v___x_5776_ = lean_box(0);
v_isShared_5777_ = v_isSharedCheck_5781_;
goto v_resetjp_5775_;
}
v_resetjp_5775_:
{
lean_object* v___x_5779_; 
if (v_isShared_5777_ == 0)
{
lean_ctor_set_tag(v___x_5776_, 1);
lean_ctor_set(v___x_5776_, 0, v_a_5772_);
v___x_5779_ = v___x_5776_;
goto v_reusejp_5778_;
}
else
{
lean_object* v_reuseFailAlloc_5780_; 
v_reuseFailAlloc_5780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_a_5772_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5794_, lean_object* v_isExporting_5795_, lean_object* v___y_5796_, lean_object* v___y_5797_, lean_object* v___y_5798_, lean_object* v___y_5799_, lean_object* v___y_5800_){
_start:
{
uint8_t v_isExporting_boxed_5801_; lean_object* v_res_5802_; 
v_isExporting_boxed_5801_ = lean_unbox(v_isExporting_5795_);
v_res_5802_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5794_, v_isExporting_boxed_5801_, v___y_5796_, v___y_5797_, v___y_5798_, v___y_5799_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec(v___y_5797_);
lean_dec_ref(v___y_5796_);
return v_res_5802_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5803_, uint8_t v_when_5804_, lean_object* v___y_5805_, lean_object* v___y_5806_, lean_object* v___y_5807_, lean_object* v___y_5808_){
_start:
{
if (v_when_5804_ == 0)
{
lean_object* v___x_5810_; 
lean_inc(v___y_5808_);
lean_inc_ref(v___y_5807_);
lean_inc(v___y_5806_);
lean_inc_ref(v___y_5805_);
v___x_5810_ = lean_apply_5(v_x_5803_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_, lean_box(0));
return v___x_5810_;
}
else
{
uint8_t v___x_5811_; lean_object* v___x_5812_; 
v___x_5811_ = 0;
v___x_5812_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5803_, v___x_5811_, v___y_5805_, v___y_5806_, v___y_5807_, v___y_5808_);
return v___x_5812_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5813_, lean_object* v_when_5814_, lean_object* v___y_5815_, lean_object* v___y_5816_, lean_object* v___y_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_){
_start:
{
uint8_t v_when_boxed_5820_; lean_object* v_res_5821_; 
v_when_boxed_5820_ = lean_unbox(v_when_5814_);
v_res_5821_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5813_, v_when_boxed_5820_, v___y_5815_, v___y_5816_, v___y_5817_, v___y_5818_);
lean_dec(v___y_5818_);
lean_dec_ref(v___y_5817_);
lean_dec(v___y_5816_);
lean_dec_ref(v___y_5815_);
return v_res_5821_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5822_, lean_object* v___y_5823_, lean_object* v___y_5824_, lean_object* v___y_5825_, lean_object* v___y_5826_){
_start:
{
lean_object* v___x_5828_; lean_object* v_a_5829_; lean_object* v___x_5830_; uint8_t v___x_5831_; lean_object* v___x_5832_; 
v___x_5828_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5822_, v___y_5824_);
v_a_5829_ = lean_ctor_get(v___x_5828_, 0);
lean_inc(v_a_5829_);
lean_dec_ref(v___x_5828_);
v___x_5830_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5830_, 0, v_a_5829_);
v___x_5831_ = 1;
v___x_5832_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5830_, v___x_5831_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_);
return v___x_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_){
_start:
{
lean_object* v_res_5839_; 
v_res_5839_ = l_Lean_Meta_letToHave___lam__0(v_e_5833_, v___y_5834_, v___y_5835_, v___y_5836_, v___y_5837_);
lean_dec(v___y_5837_);
lean_dec_ref(v___y_5836_);
lean_dec(v___y_5835_);
lean_dec_ref(v___y_5834_);
return v_res_5839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5841_, lean_object* v_a_5842_, lean_object* v_a_5843_, lean_object* v_a_5844_, lean_object* v_a_5845_){
_start:
{
lean_object* v_options_5847_; lean_object* v___f_5848_; lean_object* v___x_5849_; lean_object* v___x_5850_; lean_object* v___x_5851_; 
v_options_5847_ = lean_ctor_get(v_a_5844_, 2);
v___f_5848_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5848_, 0, v_e_5841_);
v___x_5849_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5850_ = lean_box(0);
v___x_5851_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5849_, v_options_5847_, v___f_5848_, v___x_5850_, v_a_5842_, v_a_5843_, v_a_5844_, v_a_5845_);
return v___x_5851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5852_, lean_object* v_a_5853_, lean_object* v_a_5854_, lean_object* v_a_5855_, lean_object* v_a_5856_, lean_object* v_a_5857_){
_start:
{
lean_object* v_res_5858_; 
v_res_5858_ = l_Lean_Meta_letToHave(v_e_5852_, v_a_5853_, v_a_5854_, v_a_5855_, v_a_5856_);
lean_dec(v_a_5856_);
lean_dec_ref(v_a_5855_);
lean_dec(v_a_5854_);
lean_dec_ref(v_a_5853_);
return v_res_5858_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5859_, lean_object* v_x_5860_, uint8_t v_isExporting_5861_, lean_object* v___y_5862_, lean_object* v___y_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_){
_start:
{
lean_object* v___x_5867_; 
v___x_5867_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5860_, v_isExporting_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_);
return v___x_5867_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5868_, lean_object* v_x_5869_, lean_object* v_isExporting_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_, lean_object* v___y_5873_, lean_object* v___y_5874_, lean_object* v___y_5875_){
_start:
{
uint8_t v_isExporting_boxed_5876_; lean_object* v_res_5877_; 
v_isExporting_boxed_5876_ = lean_unbox(v_isExporting_5870_);
v_res_5877_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5868_, v_x_5869_, v_isExporting_boxed_5876_, v___y_5871_, v___y_5872_, v___y_5873_, v___y_5874_);
lean_dec(v___y_5874_);
lean_dec_ref(v___y_5873_);
lean_dec(v___y_5872_);
lean_dec_ref(v___y_5871_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5878_, lean_object* v_x_5879_, uint8_t v_when_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_){
_start:
{
lean_object* v___x_5886_; 
v___x_5886_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5879_, v_when_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_);
return v___x_5886_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5887_, lean_object* v_x_5888_, lean_object* v_when_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_, lean_object* v___y_5894_){
_start:
{
uint8_t v_when_boxed_5895_; lean_object* v_res_5896_; 
v_when_boxed_5895_ = lean_unbox(v_when_5889_);
v_res_5896_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5887_, v_x_5888_, v_when_boxed_5895_, v___y_5890_, v___y_5891_, v___y_5892_, v___y_5893_);
lean_dec(v___y_5893_);
lean_dec_ref(v___y_5892_);
lean_dec(v___y_5891_);
lean_dec_ref(v___y_5890_);
return v_res_5896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5953_; uint8_t v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; 
v___x_5953_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5954_ = 0;
v___x_5955_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5956_ = l_Lean_registerTraceClass(v___x_5953_, v___x_5954_, v___x_5955_);
if (lean_obj_tag(v___x_5956_) == 0)
{
lean_object* v___x_5957_; lean_object* v___x_5958_; 
lean_dec_ref_known(v___x_5956_, 1);
v___x_5957_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5958_ = l_Lean_registerTraceClass(v___x_5957_, v___x_5954_, v___x_5955_);
return v___x_5958_;
}
else
{
return v___x_5956_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5959_){
_start:
{
lean_object* v_res_5960_; 
v_res_5960_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5960_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_LetToHave(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
