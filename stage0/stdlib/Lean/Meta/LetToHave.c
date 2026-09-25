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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* l_instMonadEIO___redArg();
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_ProjReductionKind_ctorIdx(uint8_t);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadOptionsCoreM_checkedOptions(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "transformed "};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = " `let` expressions into `have` expressions"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "result:"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5;
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "result: (no change)"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "no `let` expressions"};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__0 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1 = (const lean_object*)&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1_value;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4;
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v_nbuckets_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_107_ = lean_array_get_size(v_data_106_);
v___x_108_ = lean_unsigned_to_nat(2u);
v_nbuckets_109_ = lean_nat_mul(v___x_107_, v___x_108_);
v___x_110_ = lean_unsigned_to_nat(0u);
v___x_111_ = lean_box(0);
v___x_112_ = lean_mk_array(v_nbuckets_109_, v___x_111_);
v___x_113_ = lean_array_propagate_mark(v_data_106_, v___x_112_);
v___x_114_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v___x_110_, v_data_106_, v___x_113_);
return v___x_114_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(lean_object* v_a_115_, lean_object* v_x_116_){
_start:
{
if (lean_obj_tag(v_x_116_) == 0)
{
uint8_t v___x_117_; 
v___x_117_ = 0;
return v___x_117_;
}
else
{
lean_object* v_key_118_; lean_object* v_tail_119_; uint8_t v___x_120_; 
v_key_118_ = lean_ctor_get(v_x_116_, 0);
v_tail_119_ = lean_ctor_get(v_x_116_, 2);
v___x_120_ = l_Lean_ExprStructEq_beq(v_key_118_, v_a_115_);
if (v___x_120_ == 0)
{
v_x_116_ = v_tail_119_;
goto _start;
}
else
{
return v___x_120_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg___boxed(lean_object* v_a_122_, lean_object* v_x_123_){
_start:
{
uint8_t v_res_124_; lean_object* v_r_125_; 
v_res_124_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_122_, v_x_123_);
lean_dec(v_x_123_);
lean_dec_ref(v_a_122_);
v_r_125_ = lean_box(v_res_124_);
return v_r_125_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(lean_object* v_m_126_, lean_object* v_a_127_, lean_object* v_b_128_){
_start:
{
lean_object* v_size_129_; lean_object* v_buckets_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_173_; 
v_size_129_ = lean_ctor_get(v_m_126_, 0);
v_buckets_130_ = lean_ctor_get(v_m_126_, 1);
v_isSharedCheck_173_ = !lean_is_exclusive(v_m_126_);
if (v_isSharedCheck_173_ == 0)
{
v___x_132_ = v_m_126_;
v_isShared_133_ = v_isSharedCheck_173_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_buckets_130_);
lean_inc(v_size_129_);
lean_dec(v_m_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_173_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; uint64_t v___x_135_; uint64_t v___x_136_; uint64_t v___x_137_; uint64_t v_fold_138_; uint64_t v___x_139_; uint64_t v___x_140_; uint64_t v___x_141_; size_t v___x_142_; size_t v___x_143_; size_t v___x_144_; size_t v___x_145_; size_t v___x_146_; lean_object* v_bkt_147_; uint8_t v___x_148_; 
v___x_134_ = lean_array_get_size(v_buckets_130_);
v___x_135_ = l_Lean_ExprStructEq_hash(v_a_127_);
v___x_136_ = 32ULL;
v___x_137_ = lean_uint64_shift_right(v___x_135_, v___x_136_);
v_fold_138_ = lean_uint64_xor(v___x_135_, v___x_137_);
v___x_139_ = 16ULL;
v___x_140_ = lean_uint64_shift_right(v_fold_138_, v___x_139_);
v___x_141_ = lean_uint64_xor(v_fold_138_, v___x_140_);
v___x_142_ = lean_uint64_to_usize(v___x_141_);
v___x_143_ = lean_usize_of_nat(v___x_134_);
v___x_144_ = ((size_t)1ULL);
v___x_145_ = lean_usize_sub(v___x_143_, v___x_144_);
v___x_146_ = lean_usize_land(v___x_142_, v___x_145_);
v_bkt_147_ = lean_array_uget_borrowed(v_buckets_130_, v___x_146_);
v___x_148_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_127_, v_bkt_147_);
if (v___x_148_ == 0)
{
lean_object* v___x_149_; lean_object* v_size_x27_150_; lean_object* v___x_151_; lean_object* v_buckets_x27_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v___x_149_ = lean_unsigned_to_nat(1u);
v_size_x27_150_ = lean_nat_add(v_size_129_, v___x_149_);
lean_dec(v_size_129_);
lean_inc(v_bkt_147_);
v___x_151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_151_, 0, v_a_127_);
lean_ctor_set(v___x_151_, 1, v_b_128_);
lean_ctor_set(v___x_151_, 2, v_bkt_147_);
v_buckets_x27_152_ = lean_array_uset(v_buckets_130_, v___x_146_, v___x_151_);
v___x_153_ = lean_unsigned_to_nat(4u);
v___x_154_ = lean_nat_mul(v_size_x27_150_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(3u);
v___x_156_ = lean_nat_div(v___x_154_, v___x_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_array_get_size(v_buckets_x27_152_);
v___x_158_ = lean_nat_dec_le(v___x_156_, v___x_157_);
lean_dec(v___x_156_);
if (v___x_158_ == 0)
{
lean_object* v_val_159_; lean_object* v___x_161_; 
v_val_159_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_buckets_x27_152_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_val_159_);
lean_ctor_set(v___x_132_, 0, v_size_x27_150_);
v___x_161_ = v___x_132_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_size_x27_150_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v_val_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
else
{
lean_object* v___x_164_; 
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v_buckets_x27_152_);
lean_ctor_set(v___x_132_, 0, v_size_x27_150_);
v___x_164_ = v___x_132_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_size_x27_150_);
lean_ctor_set(v_reuseFailAlloc_165_, 1, v_buckets_x27_152_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
else
{
lean_object* v___x_166_; lean_object* v_buckets_x27_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
lean_inc(v_bkt_147_);
v___x_166_ = lean_box(0);
v_buckets_x27_167_ = lean_array_uset(v_buckets_130_, v___x_146_, v___x_166_);
v___x_168_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_127_, v_b_128_, v_bkt_147_);
v___x_169_ = lean_array_uset(v_buckets_x27_167_, v___x_146_, v___x_168_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_169_);
v___x_171_ = v___x_132_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v_size_129_);
lean_ctor_set(v_reuseFailAlloc_172_, 1, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(lean_object* v_r_174_, lean_object* v_a_175_, lean_object* v_a_176_, lean_object* v_a_177_, lean_object* v_a_178_, lean_object* v_a_179_){
_start:
{
lean_object* v_type_x3f_181_; 
v_type_x3f_181_ = lean_ctor_get(v_r_174_, 1);
lean_inc(v_type_x3f_181_);
if (lean_obj_tag(v_type_x3f_181_) == 1)
{
lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_r_174_);
v_val_182_ = lean_ctor_get(v_type_x3f_181_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v_type_x3f_181_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v_type_x3f_181_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_dec(v_type_x3f_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set_tag(v___x_184_, 0);
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_val_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
lean_object* v_expr_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_219_; 
lean_dec(v_type_x3f_181_);
v_expr_190_ = lean_ctor_get(v_r_174_, 0);
v_isSharedCheck_219_ = !lean_is_exclusive(v_r_174_);
if (v_isSharedCheck_219_ == 0)
{
lean_object* v_unused_220_; 
v_unused_220_ = lean_ctor_get(v_r_174_, 1);
lean_dec(v_unused_220_);
v___x_192_ = v_r_174_;
v_isShared_193_ = v_isSharedCheck_219_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_expr_190_);
lean_dec(v_r_174_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_219_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; 
lean_inc(v_a_179_);
lean_inc_ref(v_a_178_);
lean_inc(v_a_177_);
lean_inc_ref(v_a_176_);
lean_inc_ref(v_expr_190_);
v___x_194_ = lean_infer_type(v_expr_190_, v_a_176_, v_a_177_, v_a_178_, v_a_179_);
if (lean_obj_tag(v___x_194_) == 0)
{
lean_object* v_a_195_; lean_object* v___x_197_; uint8_t v_isShared_198_; uint8_t v_isSharedCheck_218_; 
v_a_195_ = lean_ctor_get(v___x_194_, 0);
v_isSharedCheck_218_ = !lean_is_exclusive(v___x_194_);
if (v_isSharedCheck_218_ == 0)
{
v___x_197_ = v___x_194_;
v_isShared_198_ = v_isSharedCheck_218_;
goto v_resetjp_196_;
}
else
{
lean_inc(v_a_195_);
lean_dec(v___x_194_);
v___x_197_ = lean_box(0);
v_isShared_198_ = v_isSharedCheck_218_;
goto v_resetjp_196_;
}
v_resetjp_196_:
{
lean_object* v___x_199_; lean_object* v___x_201_; 
lean_inc(v_a_195_);
v___x_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_199_, 0, v_a_195_);
lean_inc_ref(v_expr_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_199_);
v___x_201_ = v___x_192_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_expr_190_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v___x_199_);
v___x_201_ = v_reuseFailAlloc_217_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
lean_object* v___x_202_; lean_object* v_count_203_; lean_object* v_results_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_216_; 
v___x_202_ = lean_st_ref_take(v_a_175_);
v_count_203_ = lean_ctor_get(v___x_202_, 0);
v_results_204_ = lean_ctor_get(v___x_202_, 1);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_202_);
if (v_isSharedCheck_216_ == 0)
{
v___x_206_ = v___x_202_;
v_isShared_207_ = v_isSharedCheck_216_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_results_204_);
lean_inc(v_count_203_);
lean_dec(v___x_202_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_216_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_204_, v_expr_190_, v___x_201_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_count_203_);
lean_ctor_set(v_reuseFailAlloc_215_, 1, v___x_208_);
v___x_210_ = v_reuseFailAlloc_215_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
lean_object* v___x_211_; lean_object* v___x_213_; 
v___x_211_ = lean_st_ref_put(v_a_175_, v___x_210_);
if (v_isShared_198_ == 0)
{
v___x_213_ = v___x_197_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_214_; 
v_reuseFailAlloc_214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_214_, 0, v_a_195_);
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
}
}
else
{
lean_del_object(v___x_192_);
lean_dec_ref(v_expr_190_);
return v___x_194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg___boxed(lean_object* v_r_221_, lean_object* v_a_222_, lean_object* v_a_223_, lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_221_, v_a_222_, v_a_223_, v_a_224_, v_a_225_, v_a_226_);
lean_dec(v_a_226_);
lean_dec_ref(v_a_225_);
lean_dec(v_a_224_);
lean_dec_ref(v_a_223_);
lean_dec(v_a_222_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(lean_object* v_r_229_, lean_object* v_a_230_, lean_object* v_a_231_, lean_object* v_a_232_, lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_){
_start:
{
lean_object* v___x_237_; 
v___x_237_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_229_, v_a_231_, v_a_232_, v_a_233_, v_a_234_, v_a_235_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___boxed(lean_object* v_r_238_, lean_object* v_a_239_, lean_object* v_a_240_, lean_object* v_a_241_, lean_object* v_a_242_, lean_object* v_a_243_, lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type(v_r_238_, v_a_239_, v_a_240_, v_a_241_, v_a_242_, v_a_243_, v_a_244_);
lean_dec(v_a_244_);
lean_dec_ref(v_a_243_);
lean_dec(v_a_242_);
lean_dec_ref(v_a_241_);
lean_dec(v_a_240_);
lean_dec(v_a_239_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0(lean_object* v_00_u03b2_247_, lean_object* v_m_248_, lean_object* v_a_249_, lean_object* v_b_250_){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_m_248_, v_a_249_, v_b_250_);
return v___x_251_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(lean_object* v_00_u03b2_252_, lean_object* v_a_253_, lean_object* v_x_254_){
_start:
{
uint8_t v___x_255_; 
v___x_255_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___redArg(v_a_253_, v_x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0___boxed(lean_object* v_00_u03b2_256_, lean_object* v_a_257_, lean_object* v_x_258_){
_start:
{
uint8_t v_res_259_; lean_object* v_r_260_; 
v_res_259_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__0(v_00_u03b2_256_, v_a_257_, v_x_258_);
lean_dec(v_x_258_);
lean_dec_ref(v_a_257_);
v_r_260_ = lean_box(v_res_259_);
return v_r_260_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1(lean_object* v_00_u03b2_261_, lean_object* v_data_262_){
_start:
{
lean_object* v___x_263_; 
v___x_263_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1___redArg(v_data_262_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2(lean_object* v_00_u03b2_264_, lean_object* v_a_265_, lean_object* v_b_266_, lean_object* v_x_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__2___redArg(v_a_265_, v_b_266_, v_x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_269_, lean_object* v_i_270_, lean_object* v_source_271_, lean_object* v_target_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2___redArg(v_i_270_, v_source_271_, v_target_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_274_, lean_object* v_x_275_, lean_object* v_x_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0_spec__1_spec__2_spec__3___redArg(v_x_275_, v_x_276_);
return v___x_277_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(lean_object* v_ctx_278_){
_start:
{
uint8_t v___x_279_; 
v___x_279_ = l_List_isEmpty___redArg(v_ctx_278_);
if (v___x_279_ == 0)
{
uint8_t v___x_280_; 
v___x_280_ = 1;
return v___x_280_;
}
else
{
uint8_t v___x_281_; 
v___x_281_ = 0;
return v___x_281_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check___boxed(lean_object* v_ctx_282_){
_start:
{
uint8_t v_res_283_; lean_object* v_r_284_; 
v_res_283_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_ctx_282_);
lean_dec(v_ctx_282_);
v_r_284_ = lean_box(v_res_283_);
return v_r_284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(lean_object* v_e_285_, lean_object* v_m_286_, lean_object* v_a_287_, lean_object* v_a_288_, lean_object* v_a_289_, lean_object* v_a_290_, lean_object* v_a_291_, lean_object* v_a_292_){
_start:
{
uint8_t v___x_294_; 
v___x_294_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_287_);
if (v___x_294_ == 0)
{
lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
lean_dec_ref(v_m_286_);
v___x_295_ = lean_box(0);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v_e_285_);
lean_ctor_set(v___x_296_, 1, v___x_295_);
v___x_297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_297_, 0, v___x_296_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
lean_dec_ref(v_e_285_);
lean_inc(v_a_292_);
lean_inc_ref(v_a_291_);
lean_inc(v_a_290_);
lean_inc_ref(v_a_289_);
lean_inc(v_a_288_);
lean_inc(v_a_287_);
v___x_298_ = lean_apply_7(v_m_286_, v_a_287_, v_a_288_, v_a_289_, v_a_290_, v_a_291_, v_a_292_, lean_box(0));
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck___boxed(lean_object* v_e_299_, lean_object* v_m_300_, lean_object* v_a_301_, lean_object* v_a_302_, lean_object* v_a_303_, lean_object* v_a_304_, lean_object* v_a_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_299_, v_m_300_, v_a_301_, v_a_302_, v_a_303_, v_a_304_, v_a_305_, v_a_306_);
lean_dec(v_a_306_);
lean_dec_ref(v_a_305_);
lean_dec(v_a_304_);
lean_dec_ref(v_a_303_);
lean_dec(v_a_302_);
lean_dec(v_a_301_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(lean_object* v_fvars_309_, lean_object* v_m_310_, lean_object* v_a_311_, lean_object* v_a_312_, lean_object* v_a_313_, lean_object* v_a_314_, lean_object* v_a_315_){
_start:
{
lean_object* v___x_317_; 
lean_inc(v_a_315_);
lean_inc_ref(v_a_314_);
lean_inc(v_a_313_);
lean_inc_ref(v_a_312_);
lean_inc(v_a_311_);
v___x_317_ = lean_apply_7(v_m_310_, v_fvars_309_, v_a_311_, v_a_312_, v_a_313_, v_a_314_, v_a_315_, lean_box(0));
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg___boxed(lean_object* v_fvars_318_, lean_object* v_m_319_, lean_object* v_a_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_res_326_; 
v_res_326_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___redArg(v_fvars_318_, v_m_319_, v_a_320_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
lean_dec(v_a_324_);
lean_dec_ref(v_a_323_);
lean_dec(v_a_322_);
lean_dec_ref(v_a_321_);
lean_dec(v_a_320_);
return v_res_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(lean_object* v_00_u03b1_327_, lean_object* v_fvars_328_, lean_object* v_m_329_, lean_object* v_a_330_, lean_object* v_a_331_, lean_object* v_a_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_){
_start:
{
lean_object* v___x_337_; 
lean_inc(v_a_335_);
lean_inc_ref(v_a_334_);
lean_inc(v_a_333_);
lean_inc_ref(v_a_332_);
lean_inc(v_a_331_);
v___x_337_ = lean_apply_7(v_m_329_, v_fvars_328_, v_a_331_, v_a_332_, v_a_333_, v_a_334_, v_a_335_, lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed(lean_object* v_00_u03b1_338_, lean_object* v_fvars_339_, lean_object* v_m_340_, lean_object* v_a_341_, lean_object* v_a_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars(v_00_u03b1_338_, v_fvars_339_, v_m_340_, v_a_341_, v_a_342_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
lean_dec(v_a_346_);
lean_dec_ref(v_a_345_);
lean_dec(v_a_344_);
lean_dec_ref(v_a_343_);
lean_dec(v_a_342_);
lean_dec(v_a_341_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(lean_object* v_a_349_){
_start:
{
lean_object* v___x_351_; lean_object* v_count_352_; lean_object* v_results_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_365_; 
v___x_351_ = lean_st_ref_take(v_a_349_);
v_count_352_ = lean_ctor_get(v___x_351_, 0);
v_results_353_ = lean_ctor_get(v___x_351_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_365_ == 0)
{
v___x_355_ = v___x_351_;
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_results_353_);
lean_inc(v_count_352_);
lean_dec(v___x_351_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_357_ = lean_box(0);
v___x_358_ = lean_unsigned_to_nat(1u);
v___x_359_ = lean_nat_add(v_count_352_, v___x_358_);
lean_dec(v_count_352_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_359_);
v___x_361_ = v___x_355_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_results_353_);
v___x_361_ = v_reuseFailAlloc_364_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_362_ = lean_st_ref_put(v_a_349_, v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_357_);
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg___boxed(lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_366_);
lean_dec(v_a_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(lean_object* v_a_369_, lean_object* v_a_370_, lean_object* v_a_371_, lean_object* v_a_372_, lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v_a_370_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___boxed(lean_object* v_a_377_, lean_object* v_a_378_, lean_object* v_a_379_, lean_object* v_a_380_, lean_object* v_a_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount(v_a_377_, v_a_378_, v_a_379_, v_a_380_, v_a_381_, v_a_382_);
lean_dec(v_a_382_);
lean_dec_ref(v_a_381_);
lean_dec(v_a_380_);
lean_dec_ref(v_a_379_);
lean_dec(v_a_378_);
lean_dec(v_a_377_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(lean_object* v_a_385_, lean_object* v_x_386_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_object* v___x_387_; 
v___x_387_ = lean_box(0);
return v___x_387_;
}
else
{
lean_object* v_key_388_; lean_object* v_value_389_; lean_object* v_tail_390_; uint8_t v___x_391_; 
v_key_388_ = lean_ctor_get(v_x_386_, 0);
v_value_389_ = lean_ctor_get(v_x_386_, 1);
v_tail_390_ = lean_ctor_get(v_x_386_, 2);
v___x_391_ = l_Lean_ExprStructEq_beq(v_key_388_, v_a_385_);
if (v___x_391_ == 0)
{
v_x_386_ = v_tail_390_;
goto _start;
}
else
{
lean_object* v___x_393_; 
lean_inc(v_value_389_);
v___x_393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_393_, 0, v_value_389_);
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_394_, lean_object* v_x_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_394_, v_x_395_);
lean_dec(v_x_395_);
lean_dec_ref(v_a_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(lean_object* v_m_397_, lean_object* v_a_398_){
_start:
{
lean_object* v_buckets_399_; lean_object* v___x_400_; uint64_t v___x_401_; uint64_t v___x_402_; uint64_t v___x_403_; uint64_t v_fold_404_; uint64_t v___x_405_; uint64_t v___x_406_; uint64_t v___x_407_; size_t v___x_408_; size_t v___x_409_; size_t v___x_410_; size_t v___x_411_; size_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v_buckets_399_ = lean_ctor_get(v_m_397_, 1);
v___x_400_ = lean_array_get_size(v_buckets_399_);
v___x_401_ = l_Lean_ExprStructEq_hash(v_a_398_);
v___x_402_ = 32ULL;
v___x_403_ = lean_uint64_shift_right(v___x_401_, v___x_402_);
v_fold_404_ = lean_uint64_xor(v___x_401_, v___x_403_);
v___x_405_ = 16ULL;
v___x_406_ = lean_uint64_shift_right(v_fold_404_, v___x_405_);
v___x_407_ = lean_uint64_xor(v_fold_404_, v___x_406_);
v___x_408_ = lean_uint64_to_usize(v___x_407_);
v___x_409_ = lean_usize_of_nat(v___x_400_);
v___x_410_ = ((size_t)1ULL);
v___x_411_ = lean_usize_sub(v___x_409_, v___x_410_);
v___x_412_ = lean_usize_land(v___x_408_, v___x_411_);
v___x_413_ = lean_array_uget_borrowed(v_buckets_399_, v___x_412_);
v___x_414_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_398_, v___x_413_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg___boxed(lean_object* v_m_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_415_, v_a_416_);
lean_dec_ref(v_a_416_);
lean_dec_ref(v_m_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(lean_object* v_e_418_, lean_object* v_a_419_){
_start:
{
lean_object* v___x_421_; lean_object* v_results_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_421_ = lean_st_ref_get(v_a_419_);
v_results_422_ = lean_ctor_get(v___x_421_, 1);
lean_inc_ref(v_results_422_);
lean_dec(v___x_421_);
v___x_423_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_results_422_, v_e_418_);
lean_dec_ref(v_results_422_);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg___boxed(lean_object* v_e_425_, lean_object* v_a_426_, lean_object* v_a_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_425_, v_a_426_);
lean_dec(v_a_426_);
lean_dec_ref(v_e_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(lean_object* v_e_429_, lean_object* v_a_430_, lean_object* v_a_431_, lean_object* v_a_432_, lean_object* v_a_433_, lean_object* v_a_434_, lean_object* v_a_435_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_429_, v_a_431_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___boxed(lean_object* v_e_438_, lean_object* v_a_439_, lean_object* v_a_440_, lean_object* v_a_441_, lean_object* v_a_442_, lean_object* v_a_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f(v_e_438_, v_a_439_, v_a_440_, v_a_441_, v_a_442_, v_a_443_, v_a_444_);
lean_dec(v_a_444_);
lean_dec_ref(v_a_443_);
lean_dec(v_a_442_);
lean_dec_ref(v_a_441_);
lean_dec(v_a_440_);
lean_dec(v_a_439_);
lean_dec_ref(v_e_438_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(lean_object* v_00_u03b2_447_, lean_object* v_m_448_, lean_object* v_a_449_){
_start:
{
lean_object* v___x_450_; 
v___x_450_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___redArg(v_m_448_, v_a_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0___boxed(lean_object* v_00_u03b2_451_, lean_object* v_m_452_, lean_object* v_a_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0(v_00_u03b2_451_, v_m_452_, v_a_453_);
lean_dec_ref(v_a_453_);
lean_dec_ref(v_m_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(lean_object* v_00_u03b2_455_, lean_object* v_a_456_, lean_object* v_x_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___redArg(v_a_456_, v_x_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_459_, lean_object* v_a_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f_spec__0_spec__0(v_00_u03b2_459_, v_a_460_, v_x_461_);
lean_dec(v_x_461_);
lean_dec_ref(v_a_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(lean_object* v_e_463_, lean_object* v_m_464_, lean_object* v_a_465_, lean_object* v_a_466_, lean_object* v_a_467_, lean_object* v_a_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v_r_473_; lean_object* v___y_474_; lean_object* v___x_488_; lean_object* v_a_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_503_; 
v___x_488_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_463_, v_a_466_);
v_a_489_ = lean_ctor_get(v___x_488_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_488_);
if (v_isSharedCheck_503_ == 0)
{
v___x_491_ = v___x_488_;
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_a_489_);
lean_dec(v___x_488_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
v___jp_472_:
{
lean_object* v___x_475_; lean_object* v_count_476_; lean_object* v_results_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_487_; 
v___x_475_ = lean_st_ref_take(v___y_474_);
v_count_476_ = lean_ctor_get(v___x_475_, 0);
v_results_477_ = lean_ctor_get(v___x_475_, 1);
v_isSharedCheck_487_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_487_ == 0)
{
v___x_479_ = v___x_475_;
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_results_477_);
lean_inc(v_count_476_);
lean_dec(v___x_475_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_487_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; lean_object* v___x_483_; 
lean_inc_ref(v_r_473_);
v___x_481_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_477_, v_e_463_, v_r_473_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v___x_481_);
v___x_483_ = v___x_479_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_486_; 
v_reuseFailAlloc_486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_486_, 0, v_count_476_);
lean_ctor_set(v_reuseFailAlloc_486_, 1, v___x_481_);
v___x_483_ = v_reuseFailAlloc_486_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_st_ref_put(v___y_474_, v___x_483_);
v___x_485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_485_, 0, v_r_473_);
return v___x_485_;
}
}
}
v_resetjp_490_:
{
if (lean_obj_tag(v_a_489_) == 1)
{
lean_object* v_val_493_; lean_object* v___x_495_; 
lean_dec_ref(v_m_464_);
lean_dec_ref(v_e_463_);
v_val_493_ = lean_ctor_get(v_a_489_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v_a_489_, 1);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 0, v_val_493_);
v___x_495_ = v___x_491_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_val_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
uint32_t v___x_497_; uint8_t v___x_498_; 
lean_del_object(v___x_491_);
lean_dec(v_a_489_);
v___x_497_ = 2;
v___x_498_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_463_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; 
lean_inc(v_a_470_);
lean_inc_ref(v_a_469_);
lean_inc(v_a_468_);
lean_inc_ref(v_a_467_);
lean_inc(v_a_466_);
lean_inc(v_a_465_);
v___x_499_ = lean_apply_7(v_m_464_, v_a_465_, v_a_466_, v_a_467_, v_a_468_, v_a_469_, v_a_470_, lean_box(0));
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
v_r_473_ = v_a_500_;
v___y_474_ = v_a_466_;
goto v___jp_472_;
}
else
{
lean_dec_ref(v_e_463_);
return v___x_499_;
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
lean_dec_ref(v_m_464_);
v___x_501_ = lean_box(0);
lean_inc_ref(v_e_463_);
v___x_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_502_, 0, v_e_463_);
lean_ctor_set(v___x_502_, 1, v___x_501_);
v_r_473_ = v___x_502_;
v___y_474_ = v_a_466_;
goto v___jp_472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache___boxed(lean_object* v_e_504_, lean_object* v_m_505_, lean_object* v_a_506_, lean_object* v_a_507_, lean_object* v_a_508_, lean_object* v_a_509_, lean_object* v_a_510_, lean_object* v_a_511_, lean_object* v_a_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_504_, v_m_505_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_);
lean_dec(v_a_511_);
lean_dec_ref(v_a_510_);
lean_dec(v_a_509_);
lean_dec_ref(v_a_508_);
lean_dec(v_a_507_);
lean_dec(v_a_506_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(lean_object* v_e_514_, lean_object* v_a_515_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = l_Lean_Expr_hasLooseBVars(v_e_514_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCache_x3f___redArg(v_e_514_, v_a_515_);
return v___x_518_;
}
else
{
lean_object* v___x_519_; lean_object* v___x_520_; 
v___x_519_ = lean_box(0);
v___x_520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
return v___x_520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg___boxed(lean_object* v_e_521_, lean_object* v_a_522_, lean_object* v_a_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_521_, v_a_522_);
lean_dec(v_a_522_);
lean_dec_ref(v_e_521_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(lean_object* v_e_525_, lean_object* v_a_526_, lean_object* v_a_527_, lean_object* v_a_528_, lean_object* v_a_529_, lean_object* v_a_530_, lean_object* v_a_531_){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_525_, v_a_527_);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___boxed(lean_object* v_e_534_, lean_object* v_a_535_, lean_object* v_a_536_, lean_object* v_a_537_, lean_object* v_a_538_, lean_object* v_a_539_, lean_object* v_a_540_, lean_object* v_a_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f(v_e_534_, v_a_535_, v_a_536_, v_a_537_, v_a_538_, v_a_539_, v_a_540_);
lean_dec(v_a_540_);
lean_dec_ref(v_a_539_);
lean_dec(v_a_538_);
lean_dec_ref(v_a_537_);
lean_dec(v_a_536_);
lean_dec(v_a_535_);
lean_dec_ref(v_e_534_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(lean_object* v_e_543_, lean_object* v_a_544_, lean_object* v_a_545_, lean_object* v_a_546_){
_start:
{
lean_object* v___x_548_; lean_object* v___x_549_; 
v___x_548_ = l_Lean_Expr_fvarId_x21(v_e_543_);
lean_inc(v___x_548_);
v___x_549_ = l_Lean_FVarId_findDecl_x3f___redArg(v___x_548_, v_a_544_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_568_; 
v_a_550_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_568_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_568_ == 0)
{
v___x_552_ = v___x_549_;
v_isShared_553_ = v_isSharedCheck_568_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_549_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_568_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
if (lean_obj_tag(v_a_550_) == 1)
{
lean_object* v_val_554_; lean_object* v___x_556_; uint8_t v_isShared_557_; uint8_t v_isSharedCheck_566_; 
lean_dec(v___x_548_);
v_val_554_ = lean_ctor_get(v_a_550_, 0);
v_isSharedCheck_566_ = !lean_is_exclusive(v_a_550_);
if (v_isSharedCheck_566_ == 0)
{
v___x_556_ = v_a_550_;
v_isShared_557_ = v_isSharedCheck_566_;
goto v_resetjp_555_;
}
else
{
lean_inc(v_val_554_);
lean_dec(v_a_550_);
v___x_556_ = lean_box(0);
v_isShared_557_ = v_isSharedCheck_566_;
goto v_resetjp_555_;
}
v_resetjp_555_:
{
lean_object* v___x_558_; lean_object* v___x_560_; 
v___x_558_ = l_Lean_LocalDecl_type(v_val_554_);
lean_dec(v_val_554_);
if (v_isShared_557_ == 0)
{
lean_ctor_set(v___x_556_, 0, v___x_558_);
v___x_560_ = v___x_556_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v___x_558_);
v___x_560_ = v_reuseFailAlloc_565_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v___x_561_; lean_object* v___x_563_; 
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_e_543_);
lean_ctor_set(v___x_561_, 1, v___x_560_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v___x_561_);
v___x_563_ = v___x_552_;
goto v_reusejp_562_;
}
else
{
lean_object* v_reuseFailAlloc_564_; 
v_reuseFailAlloc_564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_564_, 0, v___x_561_);
v___x_563_ = v_reuseFailAlloc_564_;
goto v_reusejp_562_;
}
v_reusejp_562_:
{
return v___x_563_;
}
}
}
}
else
{
lean_object* v___x_567_; 
lean_del_object(v___x_552_);
lean_dec(v_a_550_);
lean_dec_ref(v_e_543_);
v___x_567_ = l_Lean_FVarId_throwUnknown___redArg(v___x_548_, v_a_545_, v_a_546_);
return v___x_567_;
}
}
}
else
{
lean_object* v_a_569_; lean_object* v___x_571_; uint8_t v_isShared_572_; uint8_t v_isSharedCheck_576_; 
lean_dec(v___x_548_);
lean_dec_ref(v_e_543_);
v_a_569_ = lean_ctor_get(v___x_549_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v___x_549_);
if (v_isSharedCheck_576_ == 0)
{
v___x_571_ = v___x_549_;
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
else
{
lean_inc(v_a_569_);
lean_dec(v___x_549_);
v___x_571_ = lean_box(0);
v_isShared_572_ = v_isSharedCheck_576_;
goto v_resetjp_570_;
}
v_resetjp_570_:
{
lean_object* v___x_574_; 
if (v_isShared_572_ == 0)
{
v___x_574_ = v___x_571_;
goto v_reusejp_573_;
}
else
{
lean_object* v_reuseFailAlloc_575_; 
v_reuseFailAlloc_575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_575_, 0, v_a_569_);
v___x_574_ = v_reuseFailAlloc_575_;
goto v_reusejp_573_;
}
v_reusejp_573_:
{
return v___x_574_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg___boxed(lean_object* v_e_577_, lean_object* v_a_578_, lean_object* v_a_579_, lean_object* v_a_580_, lean_object* v_a_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_577_, v_a_578_, v_a_579_, v_a_580_);
lean_dec(v_a_580_);
lean_dec_ref(v_a_579_);
lean_dec_ref(v_a_578_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(lean_object* v_e_583_, lean_object* v_a_584_, lean_object* v_a_585_, lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_583_, v_a_584_, v_a_586_, v_a_587_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___boxed(lean_object* v_e_590_, lean_object* v_a_591_, lean_object* v_a_592_, lean_object* v_a_593_, lean_object* v_a_594_, lean_object* v_a_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar(v_e_590_, v_a_591_, v_a_592_, v_a_593_, v_a_594_);
lean_dec(v_a_594_);
lean_dec_ref(v_a_593_);
lean_dec(v_a_592_);
lean_dec_ref(v_a_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(lean_object* v_e_597_, lean_object* v___y_598_){
_start:
{
uint8_t v___x_600_; 
v___x_600_ = l_Lean_Expr_hasMVar(v_e_597_);
if (v___x_600_ == 0)
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_601_, 0, v_e_597_);
return v___x_601_;
}
else
{
lean_object* v___x_602_; lean_object* v_mctx_603_; lean_object* v___x_604_; lean_object* v_fst_605_; lean_object* v_snd_606_; lean_object* v___x_607_; lean_object* v_cache_608_; lean_object* v_zetaDeltaFVarIds_609_; lean_object* v_postponed_610_; lean_object* v_diag_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_620_; 
v___x_602_ = lean_st_ref_get(v___y_598_);
v_mctx_603_ = lean_ctor_get(v___x_602_, 0);
lean_inc_ref(v_mctx_603_);
lean_dec(v___x_602_);
v___x_604_ = l_Lean_instantiateMVarsCore(v_mctx_603_, v_e_597_);
v_fst_605_ = lean_ctor_get(v___x_604_, 0);
lean_inc(v_fst_605_);
v_snd_606_ = lean_ctor_get(v___x_604_, 1);
lean_inc(v_snd_606_);
lean_dec_ref(v___x_604_);
v___x_607_ = lean_st_ref_take(v___y_598_);
v_cache_608_ = lean_ctor_get(v___x_607_, 1);
v_zetaDeltaFVarIds_609_ = lean_ctor_get(v___x_607_, 2);
v_postponed_610_ = lean_ctor_get(v___x_607_, 3);
v_diag_611_ = lean_ctor_get(v___x_607_, 4);
v_isSharedCheck_620_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_620_ == 0)
{
lean_object* v_unused_621_; 
v_unused_621_ = lean_ctor_get(v___x_607_, 0);
lean_dec(v_unused_621_);
v___x_613_ = v___x_607_;
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_diag_611_);
lean_inc(v_postponed_610_);
lean_inc(v_zetaDeltaFVarIds_609_);
lean_inc(v_cache_608_);
lean_dec(v___x_607_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_620_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v_snd_606_);
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_619_; 
v_reuseFailAlloc_619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_619_, 0, v_snd_606_);
lean_ctor_set(v_reuseFailAlloc_619_, 1, v_cache_608_);
lean_ctor_set(v_reuseFailAlloc_619_, 2, v_zetaDeltaFVarIds_609_);
lean_ctor_set(v_reuseFailAlloc_619_, 3, v_postponed_610_);
lean_ctor_set(v_reuseFailAlloc_619_, 4, v_diag_611_);
v___x_616_ = v_reuseFailAlloc_619_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = lean_st_ref_put(v___y_598_, v___x_616_);
v___x_618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_618_, 0, v_fst_605_);
return v___x_618_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg___boxed(lean_object* v_e_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_622_, v___y_623_);
lean_dec(v___y_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(lean_object* v_e_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v_e_626_, v___y_630_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___boxed(lean_object* v_e_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1(v_e_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec_ref(v___y_638_);
lean_dec(v___y_637_);
lean_dec(v___y_636_);
return v_res_643_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(lean_object* v_k_644_, lean_object* v_t_645_){
_start:
{
if (lean_obj_tag(v_t_645_) == 0)
{
lean_object* v_k_646_; lean_object* v_l_647_; lean_object* v_r_648_; uint8_t v___x_649_; 
v_k_646_ = lean_ctor_get(v_t_645_, 1);
v_l_647_ = lean_ctor_get(v_t_645_, 3);
v_r_648_ = lean_ctor_get(v_t_645_, 4);
v___x_649_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_644_, v_k_646_);
switch(v___x_649_)
{
case 0:
{
v_t_645_ = v_l_647_;
goto _start;
}
case 1:
{
uint8_t v___x_651_; 
v___x_651_ = 1;
return v___x_651_;
}
default: 
{
v_t_645_ = v_r_648_;
goto _start;
}
}
}
else
{
uint8_t v___x_653_; 
v___x_653_ = 0;
return v___x_653_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg___boxed(lean_object* v_k_654_, lean_object* v_t_655_){
_start:
{
uint8_t v_res_656_; lean_object* v_r_657_; 
v_res_656_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_654_, v_t_655_);
lean_dec(v_t_655_);
lean_dec(v_k_654_);
v_r_657_ = lean_box(v_res_656_);
return v_r_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(lean_object* v_as_658_, size_t v_sz_659_, size_t v_i_660_, lean_object* v_b_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
lean_object* v_a_668_; uint8_t v___x_672_; 
v___x_672_ = lean_usize_dec_lt(v_i_660_, v_sz_659_);
if (v___x_672_ == 0)
{
lean_object* v___x_673_; 
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v_b_661_);
return v___x_673_;
}
else
{
lean_object* v_fst_674_; lean_object* v_snd_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_723_; 
v_fst_674_ = lean_ctor_get(v_b_661_, 0);
v_snd_675_ = lean_ctor_get(v_b_661_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_b_661_);
if (v_isSharedCheck_723_ == 0)
{
v___x_677_ = v_b_661_;
v_isShared_678_ = v_isSharedCheck_723_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_snd_675_);
lean_inc(v_fst_674_);
lean_dec(v_b_661_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_723_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_a_679_; uint8_t v___x_680_; 
v_a_679_ = lean_array_uget_borrowed(v_as_658_, v_i_660_);
v___x_680_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_a_679_, v_fst_674_);
if (v___x_680_ == 0)
{
lean_object* v___x_681_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___x_700_; 
lean_inc_n(v_a_679_, 2);
v___x_681_ = l_Lean_FVarIdSet_insert(v_fst_674_, v_a_679_);
v___x_700_ = l_Lean_FVarId_isLetVar___redArg(v_a_679_, v___x_680_, v___y_662_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_700_) == 0)
{
lean_object* v_a_701_; uint8_t v___x_702_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
lean_inc(v_a_701_);
lean_dec_ref_known(v___x_700_, 1);
v___x_702_ = lean_unbox(v_a_701_);
lean_dec(v_a_701_);
if (v___x_702_ == 0)
{
v___y_683_ = v___y_662_;
v___y_684_ = v___y_664_;
v___y_685_ = v___y_665_;
goto v___jp_682_;
}
else
{
lean_object* v___x_703_; 
lean_inc(v_a_679_);
v___x_703_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_a_679_, v___y_663_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_dec_ref_known(v___x_703_, 1);
v___y_683_ = v___y_662_;
v___y_684_ = v___y_664_;
v___y_685_ = v___y_665_;
goto v___jp_682_;
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v___x_681_);
lean_del_object(v___x_677_);
lean_dec(v_snd_675_);
v_a_704_ = lean_ctor_get(v___x_703_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_703_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_703_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v___x_681_);
lean_del_object(v___x_677_);
lean_dec(v_snd_675_);
v_a_712_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_700_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_700_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
v___jp_682_:
{
lean_object* v___x_686_; 
lean_inc(v_a_679_);
v___x_686_ = l_Lean_FVarId_getType___redArg(v_a_679_, v___y_683_, v___y_684_, v___y_685_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v___x_688_; lean_object* v___x_690_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v___x_688_ = lean_array_push(v_snd_675_, v_a_687_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 1, v___x_688_);
lean_ctor_set(v___x_677_, 0, v___x_681_);
v___x_690_ = v___x_677_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_681_);
lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v_a_668_ = v___x_690_;
goto v___jp_667_;
}
}
else
{
lean_object* v_a_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_699_; 
lean_dec(v___x_681_);
lean_del_object(v___x_677_);
lean_dec(v_snd_675_);
v_a_692_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_699_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_699_ == 0)
{
v___x_694_ = v___x_686_;
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_a_692_);
lean_dec(v___x_686_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_699_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_697_; 
if (v_isShared_695_ == 0)
{
v___x_697_ = v___x_694_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_698_; 
v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_698_, 0, v_a_692_);
v___x_697_ = v_reuseFailAlloc_698_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
return v___x_697_;
}
}
}
}
}
else
{
lean_object* v___x_721_; 
if (v_isShared_678_ == 0)
{
v___x_721_ = v___x_677_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_fst_674_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_snd_675_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v_a_668_ = v___x_721_;
goto v___jp_667_;
}
}
}
}
v___jp_667_:
{
size_t v___x_669_; size_t v___x_670_; 
v___x_669_ = ((size_t)1ULL);
v___x_670_ = lean_usize_add(v_i_660_, v___x_669_);
v_i_660_ = v___x_670_;
v_b_661_ = v_a_668_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg___boxed(lean_object* v_as_724_, lean_object* v_sz_725_, lean_object* v_i_726_, lean_object* v_b_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_){
_start:
{
size_t v_sz_boxed_733_; size_t v_i_boxed_734_; lean_object* v_res_735_; 
v_sz_boxed_733_ = lean_unbox_usize(v_sz_725_);
lean_dec(v_sz_725_);
v_i_boxed_734_ = lean_unbox_usize(v_i_726_);
lean_dec(v_i_726_);
v_res_735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_724_, v_sz_boxed_733_, v_i_boxed_734_, v_b_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec_ref(v_as_724_);
return v_res_735_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_736_ = lean_box(0);
v___x_737_ = lean_unsigned_to_nat(16u);
v___x_738_ = lean_mk_array(v___x_737_, v___x_736_);
return v___x_738_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_739_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__0);
v___x_740_ = lean_unsigned_to_nat(0u);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
return v___x_741_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_744_; lean_object* v_visited_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_744_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__2));
v_visited_745_ = lean_box(1);
v___x_746_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_747_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_visited_745_);
lean_ctor_set(v___x_747_, 2, v___x_744_);
return v___x_747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(lean_object* v_a_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v_fst_756_; lean_object* v_snd_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_803_; 
v_fst_756_ = lean_ctor_get(v_a_748_, 0);
v_snd_757_ = lean_ctor_get(v_a_748_, 1);
v_isSharedCheck_803_ = !lean_is_exclusive(v_a_748_);
if (v_isSharedCheck_803_ == 0)
{
v___x_759_ = v_a_748_;
v_isShared_760_ = v_isSharedCheck_803_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_snd_757_);
lean_inc(v_fst_756_);
lean_dec(v_a_748_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_803_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v___x_761_; lean_object* v___x_762_; uint8_t v___x_763_; 
v___x_761_ = lean_array_get_size(v_snd_757_);
v___x_762_ = lean_unsigned_to_nat(0u);
v___x_763_ = lean_nat_dec_eq(v___x_761_, v___x_762_);
if (v___x_763_ == 0)
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_764_ = l_Lean_instInhabitedExpr;
v___x_765_ = lean_unsigned_to_nat(1u);
v___x_766_ = lean_nat_sub(v___x_761_, v___x_765_);
v___x_767_ = lean_array_get_borrowed(v___x_764_, v_snd_757_, v___x_766_);
lean_dec(v___x_766_);
lean_inc(v___x_767_);
v___x_768_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__1___redArg(v___x_767_, v___y_752_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v_fvarIds_772_; lean_object* v___x_773_; lean_object* v___x_775_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v___x_770_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__3);
v___x_771_ = l_Lean_collectFVars(v___x_770_, v_a_769_);
v_fvarIds_772_ = lean_ctor_get(v___x_771_, 2);
lean_inc_ref(v_fvarIds_772_);
lean_dec_ref(v___x_771_);
v___x_773_ = lean_array_pop(v_snd_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 1, v___x_773_);
v___x_775_ = v___x_759_;
goto v_reusejp_774_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_fst_756_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v___x_773_);
v___x_775_ = v_reuseFailAlloc_790_;
goto v_reusejp_774_;
}
v_reusejp_774_:
{
size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
v_sz_776_ = lean_array_size(v_fvarIds_772_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_fvarIds_772_, v_sz_776_, v___x_777_, v___x_775_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec_ref(v_fvarIds_772_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v_fst_780_; lean_object* v_snd_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_789_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
lean_inc(v_a_779_);
lean_dec_ref_known(v___x_778_, 1);
v_fst_780_ = lean_ctor_get(v_a_779_, 0);
v_snd_781_ = lean_ctor_get(v_a_779_, 1);
v_isSharedCheck_789_ = !lean_is_exclusive(v_a_779_);
if (v_isSharedCheck_789_ == 0)
{
v___x_783_ = v_a_779_;
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_snd_781_);
lean_inc(v_fst_780_);
lean_dec(v_a_779_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_789_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_784_ == 0)
{
v___x_786_ = v___x_783_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_fst_780_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_snd_781_);
v___x_786_ = v_reuseFailAlloc_788_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
v_a_748_ = v___x_786_;
goto _start;
}
}
}
else
{
return v___x_778_;
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
lean_del_object(v___x_759_);
lean_dec(v_snd_757_);
lean_dec(v_fst_756_);
v_a_791_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_768_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_768_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
else
{
lean_object* v___x_800_; 
if (v_isShared_760_ == 0)
{
v___x_800_ = v___x_759_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_802_; 
v_reuseFailAlloc_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_802_, 0, v_fst_756_);
lean_ctor_set(v_reuseFailAlloc_802_, 1, v_snd_757_);
v___x_800_ = v_reuseFailAlloc_802_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_801_; 
v___x_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_801_, 0, v___x_800_);
return v___x_801_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___boxed(lean_object* v_a_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec(v___y_805_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(lean_object* v_e_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v_visited_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_worklist_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_visited_821_ = lean_box(1);
v___x_822_ = lean_unsigned_to_nat(1u);
v___x_823_ = lean_mk_empty_array_with_capacity(v___x_822_);
v_worklist_824_ = lean_array_push(v___x_823_, v_e_813_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_visited_821_);
lean_ctor_set(v___x_825_, 1, v_worklist_824_);
v___x_826_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v___x_825_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v___x_828_; uint8_t v_isShared_829_; uint8_t v_isSharedCheck_834_; 
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_826_, 0);
lean_dec(v_unused_835_);
v___x_828_ = v___x_826_;
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
else
{
lean_dec(v___x_826_);
v___x_828_ = lean_box(0);
v_isShared_829_ = v_isSharedCheck_834_;
goto v_resetjp_827_;
}
v_resetjp_827_:
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_box(0);
if (v_isShared_829_ == 0)
{
lean_ctor_set(v___x_828_, 0, v___x_830_);
v___x_832_ = v___x_828_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
else
{
lean_object* v_a_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_843_; 
v_a_836_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_843_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_843_ == 0)
{
v___x_838_ = v___x_826_;
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_a_836_);
lean_dec(v___x_826_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_843_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_839_ == 0)
{
v___x_841_ = v___x_838_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_842_; 
v_reuseFailAlloc_842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_842_, 0, v_a_836_);
v___x_841_ = v_reuseFailAlloc_842_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
return v___x_841_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr___boxed(lean_object* v_e_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_, lean_object* v_a_849_, lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v_e_844_, v_a_845_, v_a_846_, v_a_847_, v_a_848_, v_a_849_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v_a_849_);
lean_dec(v_a_848_);
lean_dec_ref(v_a_847_);
lean_dec(v_a_846_);
lean_dec(v_a_845_);
return v_res_852_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(lean_object* v_00_u03b2_853_, lean_object* v_k_854_, lean_object* v_t_855_){
_start:
{
uint8_t v___x_856_; 
v___x_856_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_k_854_, v_t_855_);
return v___x_856_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___boxed(lean_object* v_00_u03b2_857_, lean_object* v_k_858_, lean_object* v_t_859_){
_start:
{
uint8_t v_res_860_; lean_object* v_r_861_; 
v_res_860_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0(v_00_u03b2_857_, v_k_858_, v_t_859_);
lean_dec(v_t_859_);
lean_dec(v_k_858_);
v_r_861_ = lean_box(v_res_860_);
return v_r_861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(lean_object* v_as_862_, size_t v_sz_863_, size_t v_i_864_, lean_object* v_b_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___redArg(v_as_862_, v_sz_863_, v_i_864_, v_b_865_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2___boxed(lean_object* v_as_874_, lean_object* v_sz_875_, lean_object* v_i_876_, lean_object* v_b_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
size_t v_sz_boxed_885_; size_t v_i_boxed_886_; lean_object* v_res_887_; 
v_sz_boxed_885_ = lean_unbox_usize(v_sz_875_);
lean_dec(v_sz_875_);
v_i_boxed_886_ = lean_unbox_usize(v_i_876_);
lean_dec(v_i_876_);
v_res_887_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__2(v_as_874_, v_sz_boxed_885_, v_i_boxed_886_, v_b_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v_as_874_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(lean_object* v_inst_888_, lean_object* v_a_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_){
_start:
{
lean_object* v___x_897_; 
v___x_897_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg(v_a_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_);
return v___x_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___boxed(lean_object* v_inst_898_, lean_object* v_a_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3(v_inst_898_, v_a_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_);
lean_dec(v___y_905_);
lean_dec_ref(v___y_904_);
lean_dec(v___y_903_);
lean_dec_ref(v___y_902_);
lean_dec(v___y_901_);
lean_dec(v___y_900_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(lean_object* v_mvarId_908_, lean_object* v___y_909_){
_start:
{
lean_object* v___x_911_; lean_object* v_mctx_912_; lean_object* v___x_913_; lean_object* v___x_914_; 
v___x_911_ = lean_st_ref_get(v___y_909_);
v_mctx_912_ = lean_ctor_get(v___x_911_, 0);
lean_inc_ref(v_mctx_912_);
lean_dec(v___x_911_);
v___x_913_ = l_Lean_MetavarContext_getDelayedMVarAssignmentCore_x3f(v_mctx_912_, v_mvarId_908_);
lean_dec_ref(v_mctx_912_);
v___x_914_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_914_, 0, v___x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg___boxed(lean_object* v_mvarId_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec(v_mvarId_915_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(lean_object* v_mvarId_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v___x_927_; 
v___x_927_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_919_, v___y_923_);
return v___x_927_;
}
}
LEAN_EXPORT lean_object* l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___boxed(lean_object* v_mvarId_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_res_936_; 
v_res_936_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0(v_mvarId_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
lean_dec(v___y_934_);
lean_dec_ref(v___y_933_);
lean_dec(v___y_932_);
lean_dec_ref(v___y_931_);
lean_dec(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v_mvarId_928_);
return v_res_936_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(lean_object* v_a_937_, lean_object* v_as_938_, size_t v_sz_939_, size_t v_i_940_, lean_object* v_b_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_){
_start:
{
lean_object* v_a_950_; uint8_t v___x_954_; 
v___x_954_ = lean_usize_dec_lt(v_i_940_, v_sz_939_);
if (v___x_954_ == 0)
{
lean_object* v___x_955_; 
lean_dec_ref(v_a_937_);
v___x_955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_955_, 0, v_b_941_);
return v___x_955_;
}
else
{
lean_object* v_array_956_; lean_object* v_start_957_; lean_object* v_stop_958_; uint8_t v___x_959_; 
v_array_956_ = lean_ctor_get(v_b_941_, 0);
v_start_957_ = lean_ctor_get(v_b_941_, 1);
v_stop_958_ = lean_ctor_get(v_b_941_, 2);
v___x_959_ = lean_nat_dec_lt(v_start_957_, v_stop_958_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; 
lean_dec_ref(v_a_937_);
v___x_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_960_, 0, v_b_941_);
return v___x_960_;
}
else
{
lean_object* v___x_962_; uint8_t v_isShared_963_; uint8_t v_isSharedCheck_984_; 
lean_inc(v_stop_958_);
lean_inc(v_start_957_);
lean_inc_ref(v_array_956_);
v_isSharedCheck_984_ = !lean_is_exclusive(v_b_941_);
if (v_isSharedCheck_984_ == 0)
{
lean_object* v_unused_985_; lean_object* v_unused_986_; lean_object* v_unused_987_; 
v_unused_985_ = lean_ctor_get(v_b_941_, 2);
lean_dec(v_unused_985_);
v_unused_986_ = lean_ctor_get(v_b_941_, 1);
lean_dec(v_unused_986_);
v_unused_987_ = lean_ctor_get(v_b_941_, 0);
lean_dec(v_unused_987_);
v___x_962_ = v_b_941_;
v_isShared_963_ = v_isSharedCheck_984_;
goto v_resetjp_961_;
}
else
{
lean_dec(v_b_941_);
v___x_962_ = lean_box(0);
v_isShared_963_ = v_isSharedCheck_984_;
goto v_resetjp_961_;
}
v_resetjp_961_:
{
lean_object* v_lctx_964_; lean_object* v___x_965_; lean_object* v_a_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v_lctx_964_ = lean_ctor_get(v_a_937_, 1);
v___x_965_ = lean_array_fget(v_array_956_, v_start_957_);
v_a_966_ = lean_array_uget_borrowed(v_as_938_, v_i_940_);
v___x_967_ = lean_unsigned_to_nat(1u);
v___x_968_ = lean_nat_add(v_start_957_, v___x_967_);
lean_dec(v_start_957_);
if (v_isShared_963_ == 0)
{
lean_ctor_set(v___x_962_, 1, v___x_968_);
v___x_970_ = v___x_962_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_array_956_);
lean_ctor_set(v_reuseFailAlloc_983_, 1, v___x_968_);
lean_ctor_set(v_reuseFailAlloc_983_, 2, v_stop_958_);
v___x_970_ = v_reuseFailAlloc_983_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
lean_object* v___x_971_; uint8_t v___x_972_; uint8_t v___x_973_; 
lean_inc_ref(v_lctx_964_);
v___x_971_ = l_Lean_LocalContext_getFVar_x21(v_lctx_964_, v_a_966_);
v___x_972_ = 0;
v___x_973_ = l_Lean_LocalDecl_isLet(v___x_971_, v___x_972_);
lean_dec_ref(v___x_971_);
if (v___x_973_ == 0)
{
lean_dec(v___x_965_);
v_a_950_ = v___x_970_;
goto v___jp_949_;
}
else
{
lean_object* v___x_974_; 
v___x_974_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr(v___x_965_, v___y_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_);
if (lean_obj_tag(v___x_974_) == 0)
{
lean_dec_ref_known(v___x_974_, 1);
v_a_950_ = v___x_970_;
goto v___jp_949_;
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec_ref(v___x_970_);
lean_dec_ref(v_a_937_);
v_a_975_ = lean_ctor_get(v___x_974_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_974_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_974_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_974_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
}
}
}
v___jp_949_:
{
size_t v___x_951_; size_t v___x_952_; 
v___x_951_ = ((size_t)1ULL);
v___x_952_ = lean_usize_add(v_i_940_, v___x_951_);
v_i_940_ = v___x_952_;
v_b_941_ = v_a_950_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2___boxed(lean_object* v_a_988_, lean_object* v_as_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_b_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
size_t v_sz_boxed_1000_; size_t v_i_boxed_1001_; lean_object* v_res_1002_; 
v_sz_boxed_1000_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_1001_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_988_, v_as_989_, v_sz_boxed_1000_, v_i_boxed_1001_, v_b_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
lean_dec(v___y_996_);
lean_dec_ref(v___y_995_);
lean_dec(v___y_994_);
lean_dec(v___y_993_);
lean_dec_ref(v_as_989_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(lean_object* v_as_1003_, lean_object* v___y_1004_){
_start:
{
if (lean_obj_tag(v_as_1003_) == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_box(0);
v___x_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1007_, 0, v___x_1006_);
return v___x_1007_;
}
else
{
lean_object* v_head_1008_; lean_object* v_tail_1009_; lean_object* v___x_1010_; 
v_head_1008_ = lean_ctor_get(v_as_1003_, 0);
lean_inc(v_head_1008_);
v_tail_1009_ = lean_ctor_get(v_as_1003_, 1);
lean_inc(v_tail_1009_);
lean_dec_ref_known(v_as_1003_, 2);
v___x_1010_ = l_Lean_Meta_addZetaDeltaFVarId___redArg(v_head_1008_, v___y_1004_);
if (lean_obj_tag(v___x_1010_) == 0)
{
lean_dec_ref_known(v___x_1010_, 1);
v_as_1003_ = v_tail_1009_;
goto _start;
}
else
{
lean_dec(v_tail_1009_);
return v___x_1010_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg___boxed(lean_object* v_as_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1012_, v___y_1013_);
lean_dec(v___y_1013_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(lean_object* v_mvarId_1016_, lean_object* v_args_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v___x_1025_; lean_object* v_a_1026_; lean_object* v___x_1028_; uint8_t v_isShared_1029_; uint8_t v_isSharedCheck_1082_; 
v___x_1025_ = l_Lean_getDelayedMVarAssignment_x3f___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__0___redArg(v_mvarId_1016_, v_a_1021_);
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1028_ = v___x_1025_;
v_isShared_1029_ = v_isSharedCheck_1082_;
goto v_resetjp_1027_;
}
else
{
lean_inc(v_a_1026_);
lean_dec(v___x_1025_);
v___x_1028_ = lean_box(0);
v_isShared_1029_ = v_isSharedCheck_1082_;
goto v_resetjp_1027_;
}
v_resetjp_1027_:
{
if (lean_obj_tag(v_a_1026_) == 1)
{
lean_object* v_val_1030_; lean_object* v_fvars_1031_; lean_object* v_mvarIdPending_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; uint8_t v___x_1035_; 
lean_del_object(v___x_1028_);
v_val_1030_ = lean_ctor_get(v_a_1026_, 0);
lean_inc(v_val_1030_);
lean_dec_ref_known(v_a_1026_, 1);
v_fvars_1031_ = lean_ctor_get(v_val_1030_, 0);
lean_inc_ref(v_fvars_1031_);
v_mvarIdPending_1032_ = lean_ctor_get(v_val_1030_, 1);
lean_inc(v_mvarIdPending_1032_);
lean_dec(v_val_1030_);
v___x_1033_ = lean_array_get_size(v_fvars_1031_);
v___x_1034_ = lean_array_get_size(v_args_1017_);
v___x_1035_ = lean_nat_dec_le(v___x_1033_, v___x_1034_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec(v_mvarIdPending_1032_);
lean_dec_ref(v_fvars_1031_);
lean_dec_ref(v_args_1017_);
lean_inc(v_a_1018_);
v___x_1036_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_a_1018_, v_a_1021_);
if (lean_obj_tag(v___x_1036_) == 0)
{
lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1044_; 
v_isSharedCheck_1044_ = !lean_is_exclusive(v___x_1036_);
if (v_isSharedCheck_1044_ == 0)
{
lean_object* v_unused_1045_; 
v_unused_1045_ = lean_ctor_get(v___x_1036_, 0);
lean_dec(v_unused_1045_);
v___x_1038_ = v___x_1036_;
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
else
{
lean_dec(v___x_1036_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1044_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1040_; lean_object* v___x_1042_; 
v___x_1040_ = lean_box(0);
if (v_isShared_1039_ == 0)
{
lean_ctor_set(v___x_1038_, 0, v___x_1040_);
v___x_1042_ = v___x_1038_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1043_; 
v_reuseFailAlloc_1043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1043_, 0, v___x_1040_);
v___x_1042_ = v_reuseFailAlloc_1043_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
return v___x_1042_;
}
}
}
else
{
return v___x_1036_;
}
}
else
{
lean_object* v___x_1046_; 
v___x_1046_ = l_Lean_MVarId_getDecl(v_mvarIdPending_1032_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
if (lean_obj_tag(v___x_1046_) == 0)
{
lean_object* v_a_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; size_t v_sz_1050_; size_t v___x_1051_; lean_object* v___x_1052_; 
v_a_1047_ = lean_ctor_get(v___x_1046_, 0);
lean_inc(v_a_1047_);
lean_dec_ref_known(v___x_1046_, 1);
v___x_1048_ = lean_unsigned_to_nat(0u);
v___x_1049_ = l_Array_toSubarray___redArg(v_args_1017_, v___x_1048_, v___x_1034_);
v_sz_1050_ = lean_array_size(v_fvars_1031_);
v___x_1051_ = ((size_t)0ULL);
v___x_1052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__2(v_a_1047_, v_fvars_1031_, v_sz_1050_, v___x_1051_, v___x_1049_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_, v_a_1023_);
lean_dec_ref(v_fvars_1031_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1060_; 
v_isSharedCheck_1060_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1060_ == 0)
{
lean_object* v_unused_1061_; 
v_unused_1061_ = lean_ctor_get(v___x_1052_, 0);
lean_dec(v_unused_1061_);
v___x_1054_ = v___x_1052_;
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
else
{
lean_dec(v___x_1052_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1060_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1056_; lean_object* v___x_1058_; 
v___x_1056_ = lean_box(0);
if (v_isShared_1055_ == 0)
{
lean_ctor_set(v___x_1054_, 0, v___x_1056_);
v___x_1058_ = v___x_1054_;
goto v_reusejp_1057_;
}
else
{
lean_object* v_reuseFailAlloc_1059_; 
v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
v___x_1058_ = v_reuseFailAlloc_1059_;
goto v_reusejp_1057_;
}
v_reusejp_1057_:
{
return v___x_1058_;
}
}
}
else
{
lean_object* v_a_1062_; lean_object* v___x_1064_; uint8_t v_isShared_1065_; uint8_t v_isSharedCheck_1069_; 
v_a_1062_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1069_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1069_ == 0)
{
v___x_1064_ = v___x_1052_;
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
else
{
lean_inc(v_a_1062_);
lean_dec(v___x_1052_);
v___x_1064_ = lean_box(0);
v_isShared_1065_ = v_isSharedCheck_1069_;
goto v_resetjp_1063_;
}
v_resetjp_1063_:
{
lean_object* v___x_1067_; 
if (v_isShared_1065_ == 0)
{
v___x_1067_ = v___x_1064_;
goto v_reusejp_1066_;
}
else
{
lean_object* v_reuseFailAlloc_1068_; 
v_reuseFailAlloc_1068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1068_, 0, v_a_1062_);
v___x_1067_ = v_reuseFailAlloc_1068_;
goto v_reusejp_1066_;
}
v_reusejp_1066_:
{
return v___x_1067_;
}
}
}
}
else
{
lean_object* v_a_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1077_; 
lean_dec_ref(v_fvars_1031_);
lean_dec_ref(v_args_1017_);
v_a_1070_ = lean_ctor_get(v___x_1046_, 0);
v_isSharedCheck_1077_ = !lean_is_exclusive(v___x_1046_);
if (v_isSharedCheck_1077_ == 0)
{
v___x_1072_ = v___x_1046_;
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_a_1070_);
lean_dec(v___x_1046_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1077_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v___x_1075_; 
if (v_isShared_1073_ == 0)
{
v___x_1075_ = v___x_1072_;
goto v_reusejp_1074_;
}
else
{
lean_object* v_reuseFailAlloc_1076_; 
v_reuseFailAlloc_1076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1076_, 0, v_a_1070_);
v___x_1075_ = v_reuseFailAlloc_1076_;
goto v_reusejp_1074_;
}
v_reusejp_1074_:
{
return v___x_1075_;
}
}
}
}
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
lean_dec(v_a_1026_);
lean_dec_ref(v_args_1017_);
v___x_1078_ = lean_box(0);
if (v_isShared_1029_ == 0)
{
lean_ctor_set(v___x_1028_, 0, v___x_1078_);
v___x_1080_ = v___x_1028_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar___boxed(lean_object* v_mvarId_1083_, lean_object* v_args_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_1083_, v_args_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1090_);
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1088_);
lean_dec_ref(v_a_1087_);
lean_dec(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec(v_mvarId_1083_);
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(lean_object* v_as_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_, lean_object* v___y_1098_, lean_object* v___y_1099_){
_start:
{
lean_object* v___x_1101_; 
v___x_1101_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___redArg(v_as_1093_, v___y_1097_);
return v___x_1101_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1___boxed(lean_object* v_as_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_, lean_object* v___y_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l_List_forM___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar_spec__1(v_as_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
lean_dec(v___y_1108_);
lean_dec_ref(v___y_1107_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec(v___y_1103_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(lean_object* v_e_1113_, lean_object* v_a_1114_, lean_object* v_a_1115_, lean_object* v_a_1116_, lean_object* v_a_1117_, lean_object* v_a_1118_, lean_object* v_a_1119_){
_start:
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
v___x_1121_ = l_Lean_Expr_mvarId_x21(v_e_1113_);
v___x_1122_ = l_Lean_MVarId_findDecl_x3f___redArg(v___x_1121_, v_a_1117_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1153_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1153_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1125_ = v___x_1122_;
v_isShared_1126_ = v_isSharedCheck_1153_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1122_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1153_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
if (lean_obj_tag(v_a_1123_) == 1)
{
lean_object* v_val_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1151_; 
v_val_1127_ = lean_ctor_get(v_a_1123_, 0);
v_isSharedCheck_1151_ = !lean_is_exclusive(v_a_1123_);
if (v_isSharedCheck_1151_ == 0)
{
v___x_1129_ = v_a_1123_;
v_isShared_1130_ = v_isSharedCheck_1151_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_val_1127_);
lean_dec(v_a_1123_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1151_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
uint8_t v___x_1140_; 
v___x_1140_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1114_);
if (v___x_1140_ == 0)
{
lean_dec(v___x_1121_);
goto v___jp_1131_;
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1141_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_1142_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v___x_1121_, v___x_1141_, v_a_1114_, v_a_1115_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
lean_dec(v___x_1121_);
if (lean_obj_tag(v___x_1142_) == 0)
{
lean_dec_ref_known(v___x_1142_, 1);
goto v___jp_1131_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1150_; 
lean_del_object(v___x_1129_);
lean_dec(v_val_1127_);
lean_del_object(v___x_1125_);
lean_dec_ref(v_e_1113_);
v_a_1143_ = lean_ctor_get(v___x_1142_, 0);
v_isSharedCheck_1150_ = !lean_is_exclusive(v___x_1142_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1145_ = v___x_1142_;
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_a_1143_);
lean_dec(v___x_1142_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1150_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1148_; 
if (v_isShared_1146_ == 0)
{
v___x_1148_ = v___x_1145_;
goto v_reusejp_1147_;
}
else
{
lean_object* v_reuseFailAlloc_1149_; 
v_reuseFailAlloc_1149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1149_, 0, v_a_1143_);
v___x_1148_ = v_reuseFailAlloc_1149_;
goto v_reusejp_1147_;
}
v_reusejp_1147_:
{
return v___x_1148_;
}
}
}
}
v___jp_1131_:
{
lean_object* v_type_1132_; lean_object* v___x_1134_; 
v_type_1132_ = lean_ctor_get(v_val_1127_, 2);
lean_inc_ref(v_type_1132_);
lean_dec(v_val_1127_);
if (v_isShared_1130_ == 0)
{
lean_ctor_set(v___x_1129_, 0, v_type_1132_);
v___x_1134_ = v___x_1129_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1139_; 
v_reuseFailAlloc_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1139_, 0, v_type_1132_);
v___x_1134_ = v_reuseFailAlloc_1139_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
lean_object* v___x_1135_; lean_object* v___x_1137_; 
v___x_1135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1135_, 0, v_e_1113_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 0, v___x_1135_);
v___x_1137_ = v___x_1125_;
goto v_reusejp_1136_;
}
else
{
lean_object* v_reuseFailAlloc_1138_; 
v_reuseFailAlloc_1138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1138_, 0, v___x_1135_);
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
}
else
{
lean_object* v___x_1152_; 
lean_del_object(v___x_1125_);
lean_dec(v_a_1123_);
lean_dec_ref(v_e_1113_);
v___x_1152_ = l_Lean_Meta_throwUnknownMVar___redArg(v___x_1121_, v_a_1116_, v_a_1117_, v_a_1118_, v_a_1119_);
return v___x_1152_;
}
}
}
else
{
lean_object* v_a_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1161_; 
lean_dec(v___x_1121_);
lean_dec_ref(v_e_1113_);
v_a_1154_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1161_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1161_ == 0)
{
v___x_1156_ = v___x_1122_;
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_a_1154_);
lean_dec(v___x_1122_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1161_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___x_1159_; 
if (v_isShared_1157_ == 0)
{
v___x_1159_ = v___x_1156_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_a_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___boxed(lean_object* v_e_1162_, lean_object* v_a_1163_, lean_object* v_a_1164_, lean_object* v_a_1165_, lean_object* v_a_1166_, lean_object* v_a_1167_, lean_object* v_a_1168_, lean_object* v_a_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_1162_, v_a_1163_, v_a_1164_, v_a_1165_, v_a_1166_, v_a_1167_, v_a_1168_);
lean_dec(v_a_1168_);
lean_dec_ref(v_a_1167_);
lean_dec(v_a_1166_);
lean_dec_ref(v_a_1165_);
lean_dec(v_a_1164_);
lean_dec(v_a_1163_);
return v_res_1170_;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1171_; 
v___x_1171_ = l_instMonadEIO___redArg();
return v___x_1171_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(lean_object* v_msg_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v_toApplicative_1186_; lean_object* v___x_1188_; uint8_t v_isShared_1189_; uint8_t v_isSharedCheck_1249_; 
v___x_1184_ = lean_obj_once(&l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0, &l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0_once, _init_l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__0);
v___x_1185_ = l_StateRefT_x27_instMonad___redArg(v___x_1184_);
v_toApplicative_1186_ = lean_ctor_get(v___x_1185_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1185_);
if (v_isSharedCheck_1249_ == 0)
{
lean_object* v_unused_1250_; 
v_unused_1250_ = lean_ctor_get(v___x_1185_, 1);
lean_dec(v_unused_1250_);
v___x_1188_ = v___x_1185_;
v_isShared_1189_ = v_isSharedCheck_1249_;
goto v_resetjp_1187_;
}
else
{
lean_inc(v_toApplicative_1186_);
lean_dec(v___x_1185_);
v___x_1188_ = lean_box(0);
v_isShared_1189_ = v_isSharedCheck_1249_;
goto v_resetjp_1187_;
}
v_resetjp_1187_:
{
lean_object* v_toFunctor_1190_; lean_object* v_toSeq_1191_; lean_object* v_toSeqLeft_1192_; lean_object* v_toSeqRight_1193_; lean_object* v___x_1195_; uint8_t v_isShared_1196_; uint8_t v_isSharedCheck_1247_; 
v_toFunctor_1190_ = lean_ctor_get(v_toApplicative_1186_, 0);
v_toSeq_1191_ = lean_ctor_get(v_toApplicative_1186_, 2);
v_toSeqLeft_1192_ = lean_ctor_get(v_toApplicative_1186_, 3);
v_toSeqRight_1193_ = lean_ctor_get(v_toApplicative_1186_, 4);
v_isSharedCheck_1247_ = !lean_is_exclusive(v_toApplicative_1186_);
if (v_isSharedCheck_1247_ == 0)
{
lean_object* v_unused_1248_; 
v_unused_1248_ = lean_ctor_get(v_toApplicative_1186_, 1);
lean_dec(v_unused_1248_);
v___x_1195_ = v_toApplicative_1186_;
v_isShared_1196_ = v_isSharedCheck_1247_;
goto v_resetjp_1194_;
}
else
{
lean_inc(v_toSeqRight_1193_);
lean_inc(v_toSeqLeft_1192_);
lean_inc(v_toSeq_1191_);
lean_inc(v_toFunctor_1190_);
lean_dec(v_toApplicative_1186_);
v___x_1195_ = lean_box(0);
v_isShared_1196_ = v_isSharedCheck_1247_;
goto v_resetjp_1194_;
}
v_resetjp_1194_:
{
lean_object* v___f_1197_; lean_object* v___f_1198_; lean_object* v___f_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; lean_object* v___f_1202_; lean_object* v___f_1203_; lean_object* v___f_1204_; lean_object* v___x_1206_; 
v___f_1197_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__1));
v___f_1198_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__2));
lean_inc_ref(v_toFunctor_1190_);
v___f_1199_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1199_, 0, v_toFunctor_1190_);
v___f_1200_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1200_, 0, v_toFunctor_1190_);
v___x_1201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1201_, 0, v___f_1199_);
lean_ctor_set(v___x_1201_, 1, v___f_1200_);
v___f_1202_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1202_, 0, v_toSeqRight_1193_);
v___f_1203_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1203_, 0, v_toSeqLeft_1192_);
v___f_1204_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1204_, 0, v_toSeq_1191_);
if (v_isShared_1196_ == 0)
{
lean_ctor_set(v___x_1195_, 4, v___f_1202_);
lean_ctor_set(v___x_1195_, 3, v___f_1203_);
lean_ctor_set(v___x_1195_, 2, v___f_1204_);
lean_ctor_set(v___x_1195_, 1, v___f_1197_);
lean_ctor_set(v___x_1195_, 0, v___x_1201_);
v___x_1206_ = v___x_1195_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1246_; 
v_reuseFailAlloc_1246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1246_, 0, v___x_1201_);
lean_ctor_set(v_reuseFailAlloc_1246_, 1, v___f_1197_);
lean_ctor_set(v_reuseFailAlloc_1246_, 2, v___f_1204_);
lean_ctor_set(v_reuseFailAlloc_1246_, 3, v___f_1203_);
lean_ctor_set(v_reuseFailAlloc_1246_, 4, v___f_1202_);
v___x_1206_ = v_reuseFailAlloc_1246_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
lean_object* v___x_1208_; 
if (v_isShared_1189_ == 0)
{
lean_ctor_set(v___x_1188_, 1, v___f_1198_);
lean_ctor_set(v___x_1188_, 0, v___x_1206_);
v___x_1208_ = v___x_1188_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___f_1198_);
v___x_1208_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; lean_object* v_toApplicative_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1243_; 
v___x_1209_ = l_StateRefT_x27_instMonad___redArg(v___x_1208_);
v_toApplicative_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1243_ == 0)
{
lean_object* v_unused_1244_; 
v_unused_1244_ = lean_ctor_get(v___x_1209_, 1);
lean_dec(v_unused_1244_);
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1243_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_toApplicative_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1243_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v_toFunctor_1214_; lean_object* v_toSeq_1215_; lean_object* v_toSeqLeft_1216_; lean_object* v_toSeqRight_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1241_; 
v_toFunctor_1214_ = lean_ctor_get(v_toApplicative_1210_, 0);
v_toSeq_1215_ = lean_ctor_get(v_toApplicative_1210_, 2);
v_toSeqLeft_1216_ = lean_ctor_get(v_toApplicative_1210_, 3);
v_toSeqRight_1217_ = lean_ctor_get(v_toApplicative_1210_, 4);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_toApplicative_1210_);
if (v_isSharedCheck_1241_ == 0)
{
lean_object* v_unused_1242_; 
v_unused_1242_ = lean_ctor_get(v_toApplicative_1210_, 1);
lean_dec(v_unused_1242_);
v___x_1219_ = v_toApplicative_1210_;
v_isShared_1220_ = v_isSharedCheck_1241_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_toSeqRight_1217_);
lean_inc(v_toSeqLeft_1216_);
lean_inc(v_toSeq_1215_);
lean_inc(v_toFunctor_1214_);
lean_dec(v_toApplicative_1210_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1241_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___f_1221_; lean_object* v___f_1222_; lean_object* v___f_1223_; lean_object* v___f_1224_; lean_object* v___x_1225_; lean_object* v___f_1226_; lean_object* v___f_1227_; lean_object* v___f_1228_; lean_object* v___x_1230_; 
v___f_1221_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__3));
v___f_1222_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___closed__4));
lean_inc_ref(v_toFunctor_1214_);
v___f_1223_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(v___f_1223_, 0, v_toFunctor_1214_);
v___f_1224_ = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1224_, 0, v_toFunctor_1214_);
v___x_1225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___f_1223_);
lean_ctor_set(v___x_1225_, 1, v___f_1224_);
v___f_1226_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_1226_, 0, v_toSeqRight_1217_);
v___f_1227_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(v___f_1227_, 0, v_toSeqLeft_1216_);
v___f_1228_ = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_1228_, 0, v_toSeq_1215_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 4, v___f_1226_);
lean_ctor_set(v___x_1219_, 3, v___f_1227_);
lean_ctor_set(v___x_1219_, 2, v___f_1228_);
lean_ctor_set(v___x_1219_, 1, v___f_1221_);
lean_ctor_set(v___x_1219_, 0, v___x_1225_);
v___x_1230_ = v___x_1219_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1225_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___f_1221_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v___f_1228_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v___f_1227_);
lean_ctor_set(v_reuseFailAlloc_1240_, 4, v___f_1226_);
v___x_1230_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
lean_object* v___x_1232_; 
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 1, v___f_1222_);
lean_ctor_set(v___x_1212_, 0, v___x_1230_);
v___x_1232_ = v___x_1212_;
goto v_reusejp_1231_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v___x_1230_);
lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___f_1222_);
v___x_1232_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1231_;
}
v_reusejp_1231_:
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___x_1420__overap_1237_; lean_object* v___x_1238_; 
v___x_1233_ = l_StateRefT_x27_instMonad___redArg(v___x_1232_);
v___x_1234_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1235_ = l_instInhabitedOfMonad___redArg(v___x_1233_, v___x_1234_);
v___f_1236_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1236_, 0, v___x_1235_);
v___x_1420__overap_1237_ = lean_panic_fn_borrowed(v___f_1236_, v_msg_1176_);
lean_dec_ref(v___f_1236_);
lean_inc(v___y_1182_);
lean_inc_ref(v___y_1181_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
lean_inc(v___y_1178_);
lean_inc(v___y_1177_);
v___x_1238_ = lean_apply_7(v___x_1420__overap_1237_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, lean_box(0));
return v___x_1238_;
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
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1___boxed(lean_object* v_msg_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_, lean_object* v___y_1258_){
_start:
{
lean_object* v_res_1259_; 
v_res_1259_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v_msg_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_, v___y_1257_);
lean_dec(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec(v___y_1252_);
return v_res_1259_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_1260_; 
v___x_1260_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_1262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1262_, 0, v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
v___x_1263_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1264_ = lean_unsigned_to_nat(0u);
v___x_1265_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1265_, 0, v___x_1264_);
lean_ctor_set(v___x_1265_, 1, v___x_1264_);
lean_ctor_set(v___x_1265_, 2, v___x_1264_);
lean_ctor_set(v___x_1265_, 3, v___x_1264_);
lean_ctor_set(v___x_1265_, 4, v___x_1263_);
lean_ctor_set(v___x_1265_, 5, v___x_1263_);
lean_ctor_set(v___x_1265_, 6, v___x_1263_);
lean_ctor_set(v___x_1265_, 7, v___x_1263_);
lean_ctor_set(v___x_1265_, 8, v___x_1263_);
lean_ctor_set(v___x_1265_, 9, v___x_1263_);
lean_ctor_set(v___x_1265_, 10, v___x_1263_);
return v___x_1265_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3(void){
_start:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = lean_unsigned_to_nat(32u);
v___x_1267_ = lean_mk_empty_array_with_capacity(v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
return v___x_1268_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4(void){
_start:
{
size_t v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1269_ = ((size_t)5ULL);
v___x_1270_ = lean_unsigned_to_nat(0u);
v___x_1271_ = lean_unsigned_to_nat(32u);
v___x_1272_ = lean_mk_empty_array_with_capacity(v___x_1271_);
v___x_1273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__3);
v___x_1274_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v___x_1272_);
lean_ctor_set(v___x_1274_, 2, v___x_1270_);
lean_ctor_set(v___x_1274_, 3, v___x_1270_);
lean_ctor_set_usize(v___x_1274_, 4, v___x_1269_);
return v___x_1274_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5(void){
_start:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1275_ = lean_box(1);
v___x_1276_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__4);
v___x_1277_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__1);
v___x_1278_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1278_, 0, v___x_1277_);
lean_ctor_set(v___x_1278_, 1, v___x_1276_);
lean_ctor_set(v___x_1278_, 2, v___x_1275_);
return v___x_1278_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7(void){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__6));
v___x_1281_ = l_Lean_stringToMessageData(v___x_1280_);
return v___x_1281_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9(void){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__8));
v___x_1284_ = l_Lean_stringToMessageData(v___x_1283_);
return v___x_1284_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11(void){
_start:
{
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__10));
v___x_1287_ = l_Lean_stringToMessageData(v___x_1286_);
return v___x_1287_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__12));
v___x_1290_ = l_Lean_stringToMessageData(v___x_1289_);
return v___x_1290_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__14));
v___x_1293_ = l_Lean_stringToMessageData(v___x_1292_);
return v___x_1293_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__16));
v___x_1296_ = l_Lean_stringToMessageData(v___x_1295_);
return v___x_1296_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19(void){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__18));
v___x_1299_ = l_Lean_stringToMessageData(v___x_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(lean_object* v_msg_1300_, lean_object* v_declHint_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v_env_1306_; uint8_t v___x_1307_; 
v___x_1304_ = lean_box(0);
v___x_1305_ = lean_st_ref_get(v___y_1302_);
v_env_1306_ = lean_ctor_get(v___x_1305_, 0);
lean_inc_ref(v_env_1306_);
lean_dec(v___x_1305_);
v___x_1307_ = l_Lean_Name_isAnonymous(v_declHint_1301_);
if (v___x_1307_ == 0)
{
uint8_t v_isExporting_1308_; 
v_isExporting_1308_ = lean_ctor_get_uint8(v_env_1306_, sizeof(void*)*8);
if (v_isExporting_1308_ == 0)
{
lean_object* v___x_1309_; 
lean_dec_ref(v_env_1306_);
lean_dec(v_declHint_1301_);
v___x_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1309_, 0, v_msg_1300_);
return v___x_1309_;
}
else
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
lean_inc_ref(v_env_1306_);
v___x_1310_ = l_Lean_Environment_setExporting(v_env_1306_, v___x_1307_);
lean_inc(v_declHint_1301_);
lean_inc_ref(v___x_1310_);
v___x_1311_ = l_Lean_Environment_contains(v___x_1310_, v_declHint_1301_, v_isExporting_1308_);
if (v___x_1311_ == 0)
{
lean_object* v___x_1312_; 
lean_dec_ref(v___x_1310_);
lean_dec_ref(v_env_1306_);
lean_dec(v_declHint_1301_);
v___x_1312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1312_, 0, v_msg_1300_);
return v___x_1312_;
}
else
{
lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v_c_1318_; lean_object* v___x_1319_; 
v___x_1313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1315_ = l_Lean_Options_empty;
v___x_1316_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1310_);
lean_ctor_set(v___x_1316_, 1, v___x_1313_);
lean_ctor_set(v___x_1316_, 2, v___x_1314_);
lean_ctor_set(v___x_1316_, 3, v___x_1315_);
lean_inc(v_declHint_1301_);
v___x_1317_ = l_Lean_MessageData_ofConstName(v_declHint_1301_, v___x_1307_);
v_c_1318_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1318_, 0, v___x_1316_);
lean_ctor_set(v_c_1318_, 1, v___x_1317_);
v___x_1319_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1306_, v_declHint_1301_);
if (lean_obj_tag(v___x_1319_) == 0)
{
lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; 
lean_dec_ref(v_env_1306_);
lean_dec(v_declHint_1301_);
v___x_1320_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1321_, 0, v___x_1320_);
lean_ctor_set(v___x_1321_, 1, v_c_1318_);
v___x_1322_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1323_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1321_);
lean_ctor_set(v___x_1323_, 1, v___x_1322_);
v___x_1324_ = l_Lean_MessageData_note(v___x_1323_);
v___x_1325_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1325_, 0, v_msg_1300_);
lean_ctor_set(v___x_1325_, 1, v___x_1324_);
v___x_1326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1326_, 0, v___x_1325_);
return v___x_1326_;
}
else
{
lean_object* v_val_1327_; lean_object* v___x_1329_; uint8_t v_isShared_1330_; uint8_t v_isSharedCheck_1361_; 
v_val_1327_ = lean_ctor_get(v___x_1319_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1319_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1329_ = v___x_1319_;
v_isShared_1330_ = v_isSharedCheck_1361_;
goto v_resetjp_1328_;
}
else
{
lean_inc(v_val_1327_);
lean_dec(v___x_1319_);
v___x_1329_ = lean_box(0);
v_isShared_1330_ = v_isSharedCheck_1361_;
goto v_resetjp_1328_;
}
v_resetjp_1328_:
{
lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_mod_1333_; uint8_t v___x_1334_; 
v___x_1331_ = l_Lean_Environment_header(v_env_1306_);
lean_dec_ref(v_env_1306_);
v___x_1332_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1331_);
v_mod_1333_ = lean_array_get(v___x_1304_, v___x_1332_, v_val_1327_);
lean_dec(v_val_1327_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = l_Lean_isPrivateName(v_declHint_1301_);
lean_dec(v_declHint_1301_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v_c_1318_);
v___x_1337_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__13);
v___x_1338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1336_);
lean_ctor_set(v___x_1338_, 1, v___x_1337_);
v___x_1339_ = l_Lean_MessageData_ofName(v_mod_1333_);
v___x_1340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1340_, 0, v___x_1338_);
lean_ctor_set(v___x_1340_, 1, v___x_1339_);
v___x_1341_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__15);
v___x_1342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1340_);
lean_ctor_set(v___x_1342_, 1, v___x_1341_);
v___x_1343_ = l_Lean_MessageData_note(v___x_1342_);
v___x_1344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1344_, 0, v_msg_1300_);
lean_ctor_set(v___x_1344_, 1, v___x_1343_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1344_);
v___x_1346_ = v___x_1329_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
else
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1359_; 
v___x_1348_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1349_, 0, v___x_1348_);
lean_ctor_set(v___x_1349_, 1, v_c_1318_);
v___x_1350_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__17);
v___x_1351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1349_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = l_Lean_MessageData_ofName(v_mod_1333_);
v___x_1353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1351_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
v___x_1354_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__19);
v___x_1355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1355_, 0, v___x_1353_);
lean_ctor_set(v___x_1355_, 1, v___x_1354_);
v___x_1356_ = l_Lean_MessageData_note(v___x_1355_);
v___x_1357_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1357_, 0, v_msg_1300_);
lean_ctor_set(v___x_1357_, 1, v___x_1356_);
if (v_isShared_1330_ == 0)
{
lean_ctor_set_tag(v___x_1329_, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1357_);
v___x_1359_ = v___x_1329_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v___x_1357_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1362_; 
lean_dec_ref(v_env_1306_);
lean_dec(v_declHint_1301_);
v___x_1362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1362_, 0, v_msg_1300_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___boxed(lean_object* v_msg_1363_, lean_object* v_declHint_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1363_, v_declHint_1364_, v___y_1365_);
lean_dec(v___y_1365_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(lean_object* v_msg_1368_, lean_object* v_declHint_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_){
_start:
{
lean_object* v___x_1377_; lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1387_; 
v___x_1377_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1368_, v_declHint_1369_, v___y_1375_);
v_a_1378_ = lean_ctor_get(v___x_1377_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1377_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1380_ = v___x_1377_;
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1377_);
v___x_1380_ = lean_box(0);
v_isShared_1381_ = v_isSharedCheck_1387_;
goto v_resetjp_1379_;
}
v_resetjp_1379_:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1382_ = l_Lean_unknownIdentifierMessageTag;
v___x_1383_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
lean_ctor_set(v___x_1383_, 1, v_a_1378_);
if (v_isShared_1381_ == 0)
{
lean_ctor_set(v___x_1380_, 0, v___x_1383_);
v___x_1385_ = v___x_1380_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v___x_1383_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4___boxed(lean_object* v_msg_1388_, lean_object* v_declHint_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1388_, v_declHint_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec(v___y_1390_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(lean_object* v_msgData_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v___x_1404_; lean_object* v_env_1405_; lean_object* v___x_1406_; lean_object* v_toCold_1407_; lean_object* v_mctx_1408_; lean_object* v_lctx_1409_; lean_object* v_options_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v___x_1404_ = lean_st_ref_get(v___y_1402_);
v_env_1405_ = lean_ctor_get(v___x_1404_, 0);
lean_inc_ref(v_env_1405_);
lean_dec(v___x_1404_);
v___x_1406_ = lean_st_ref_get(v___y_1400_);
v_toCold_1407_ = lean_ctor_get(v___y_1401_, 0);
v_mctx_1408_ = lean_ctor_get(v___x_1406_, 0);
lean_inc_ref(v_mctx_1408_);
lean_dec(v___x_1406_);
v_lctx_1409_ = lean_ctor_get(v___y_1399_, 2);
v_options_1410_ = lean_ctor_get(v_toCold_1407_, 2);
lean_inc_ref(v_options_1410_);
lean_inc_ref(v_lctx_1409_);
v___x_1411_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1411_, 0, v_env_1405_);
lean_ctor_set(v___x_1411_, 1, v_mctx_1408_);
lean_ctor_set(v___x_1411_, 2, v_lctx_1409_);
lean_ctor_set(v___x_1411_, 3, v_options_1410_);
v___x_1412_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v_msgData_1398_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
return v___x_1413_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8___boxed(lean_object* v_msgData_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msgData_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_);
lean_dec(v___y_1418_);
lean_dec_ref(v___y_1417_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(lean_object* v_msg_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_ref_1427_; lean_object* v___x_1428_; lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1437_; 
v_ref_1427_ = lean_ctor_get(v___y_1424_, 2);
v___x_1428_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1437_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1437_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1437_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1433_; lean_object* v___x_1435_; 
lean_inc(v_ref_1427_);
v___x_1433_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1433_, 0, v_ref_1427_);
lean_ctor_set(v___x_1433_, 1, v_a_1429_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set_tag(v___x_1431_, 1);
lean_ctor_set(v___x_1431_, 0, v___x_1433_);
v___x_1435_ = v___x_1431_;
goto v_reusejp_1434_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1433_);
v___x_1435_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1434_;
}
v_reusejp_1434_:
{
return v___x_1435_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg___boxed(lean_object* v_msg_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
lean_object* v_res_1444_; 
v_res_1444_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
lean_dec(v___y_1442_);
lean_dec_ref(v___y_1441_);
lean_dec(v___y_1440_);
lean_dec_ref(v___y_1439_);
return v_res_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(lean_object* v_ref_1445_, lean_object* v_msg_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_){
_start:
{
lean_object* v_toCold_1454_; lean_object* v_currRecDepth_1455_; lean_object* v_ref_1456_; uint16_t v_optionFlags_1457_; uint8_t v_suppressElabErrors_1458_; uint8_t v_isRecordingDeps_1459_; lean_object* v_ref_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v_toCold_1454_ = lean_ctor_get(v___y_1451_, 0);
v_currRecDepth_1455_ = lean_ctor_get(v___y_1451_, 1);
v_ref_1456_ = lean_ctor_get(v___y_1451_, 2);
v_optionFlags_1457_ = lean_ctor_get_uint16(v___y_1451_, sizeof(void*)*3);
v_suppressElabErrors_1458_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*3 + 2);
v_isRecordingDeps_1459_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*3 + 3);
v_ref_1460_ = l_Lean_replaceRef(v_ref_1445_, v_ref_1456_);
lean_inc(v_currRecDepth_1455_);
lean_inc_ref(v_toCold_1454_);
v___x_1461_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_1461_, 0, v_toCold_1454_);
lean_ctor_set(v___x_1461_, 1, v_currRecDepth_1455_);
lean_ctor_set(v___x_1461_, 2, v_ref_1460_);
lean_ctor_set_uint16(v___x_1461_, sizeof(void*)*3, v_optionFlags_1457_);
lean_ctor_set_uint8(v___x_1461_, sizeof(void*)*3 + 2, v_suppressElabErrors_1458_);
lean_ctor_set_uint8(v___x_1461_, sizeof(void*)*3 + 3, v_isRecordingDeps_1459_);
v___x_1462_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1446_, v___y_1449_, v___y_1450_, v___x_1461_, v___y_1452_);
lean_dec_ref_known(v___x_1461_, 3);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1463_, lean_object* v_msg_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_){
_start:
{
lean_object* v_res_1472_; 
v_res_1472_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1463_, v_msg_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_, v___y_1470_);
lean_dec(v___y_1470_);
lean_dec_ref(v___y_1469_);
lean_dec(v___y_1468_);
lean_dec_ref(v___y_1467_);
lean_dec(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v_ref_1463_);
return v_res_1472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1473_, lean_object* v_msg_1474_, lean_object* v_declHint_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v___x_1483_; lean_object* v_a_1484_; lean_object* v___x_1485_; 
v___x_1483_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1474_, v_declHint_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1473_, v_a_1484_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
return v___x_1485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1486_, lean_object* v_msg_1487_, lean_object* v_declHint_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1486_, v_msg_1487_, v_declHint_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v_ref_1486_);
return v_res_1496_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; 
v___x_1498_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1499_ = l_Lean_stringToMessageData(v___x_1498_);
return v___x_1499_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1502_ = l_Lean_stringToMessageData(v___x_1501_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1503_, lean_object* v_constName_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v___x_1512_; uint8_t v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1512_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1513_ = 0;
lean_inc(v_constName_1504_);
v___x_1514_ = l_Lean_MessageData_ofConstName(v_constName_1504_, v___x_1513_);
v___x_1515_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1512_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
v___x_1516_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1515_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
v___x_1518_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1503_, v___x_1517_, v_constName_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1519_, lean_object* v_constName_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_){
_start:
{
lean_object* v_res_1528_; 
v_res_1528_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1519_, v_constName_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_, v___y_1526_);
lean_dec(v___y_1526_);
lean_dec_ref(v___y_1525_);
lean_dec(v___y_1524_);
lean_dec_ref(v___y_1523_);
lean_dec(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec(v_ref_1519_);
return v_res_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_){
_start:
{
lean_object* v_ref_1537_; lean_object* v___x_1538_; 
v_ref_1537_ = lean_ctor_get(v___y_1534_, 2);
v___x_1538_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1537_, v_constName_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_, v___y_1535_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_, v___y_1545_);
lean_dec(v___y_1545_);
lean_dec_ref(v___y_1544_);
lean_dec(v___y_1543_);
lean_dec_ref(v___y_1542_);
lean_dec(v___y_1541_);
lean_dec(v___y_1540_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_){
_start:
{
lean_object* v___x_1556_; lean_object* v_env_1557_; uint8_t v___x_1558_; lean_object* v___x_1559_; 
v___x_1556_ = lean_st_ref_get(v___y_1554_);
v_env_1557_ = lean_ctor_get(v___x_1556_, 0);
lean_inc_ref(v_env_1557_);
lean_dec(v___x_1556_);
v___x_1558_ = 0;
lean_inc(v_constName_1548_);
v___x_1559_ = l_Lean_Environment_findConstVal_x3f(v_env_1557_, v_constName_1548_, v___x_1558_);
if (lean_obj_tag(v___x_1559_) == 0)
{
lean_object* v___x_1560_; 
v___x_1560_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
return v___x_1560_;
}
else
{
lean_object* v_val_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_dec(v_constName_1548_);
v_val_1561_ = lean_ctor_get(v___x_1559_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1559_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1559_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_val_1561_);
lean_dec(v___x_1559_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
lean_ctor_set_tag(v___x_1563_, 0);
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_val_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec(v___y_1570_);
return v_res_1577_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1581_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1582_ = lean_unsigned_to_nat(35u);
v___x_1583_ = lean_unsigned_to_nat(203u);
v___x_1584_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1585_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1586_ = l_mkPanicMessageWithDecl(v___x_1585_, v___x_1584_, v___x_1583_, v___x_1582_, v___x_1581_);
return v___x_1586_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
if (lean_obj_tag(v_e_1587_) == 4)
{
lean_object* v_declName_1595_; lean_object* v_us_1596_; lean_object* v___x_1597_; 
v_declName_1595_ = lean_ctor_get(v_e_1587_, 0);
v_us_1596_ = lean_ctor_get(v_e_1587_, 1);
lean_inc(v_declName_1595_);
v___x_1597_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1595_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
if (lean_obj_tag(v___x_1597_) == 0)
{
lean_object* v_a_1598_; lean_object* v_levelParams_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v_a_1598_ = lean_ctor_get(v___x_1597_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1597_, 1);
v_levelParams_1599_ = lean_ctor_get(v_a_1598_, 1);
v___x_1600_ = l_List_lengthTR___redArg(v_levelParams_1599_);
v___x_1601_ = l_List_lengthTR___redArg(v_us_1596_);
v___x_1602_ = lean_nat_dec_eq(v___x_1600_, v___x_1601_);
lean_dec(v___x_1601_);
lean_dec(v___x_1600_);
if (v___x_1602_ == 0)
{
lean_object* v___x_1603_; 
lean_inc(v_us_1596_);
lean_inc(v_declName_1595_);
lean_dec(v_a_1598_);
lean_dec_ref_known(v_e_1587_, 2);
v___x_1603_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1595_, v_us_1596_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; 
lean_inc(v_us_1596_);
v___x_1604_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1598_, v_us_1596_, v___y_1593_);
if (lean_obj_tag(v___x_1604_) == 0)
{
lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1614_; 
v_a_1605_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1614_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1614_ == 0)
{
v___x_1607_ = v___x_1604_;
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_dec(v___x_1604_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1614_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1612_; 
v___x_1609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1609_, 0, v_a_1605_);
v___x_1610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1610_, 0, v_e_1587_);
lean_ctor_set(v___x_1610_, 1, v___x_1609_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1610_);
v___x_1612_ = v___x_1607_;
goto v_reusejp_1611_;
}
else
{
lean_object* v_reuseFailAlloc_1613_; 
v_reuseFailAlloc_1613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1613_, 0, v___x_1610_);
v___x_1612_ = v_reuseFailAlloc_1613_;
goto v_reusejp_1611_;
}
v_reusejp_1611_:
{
return v___x_1612_;
}
}
}
else
{
lean_object* v_a_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1622_; 
lean_dec_ref_known(v_e_1587_, 2);
v_a_1615_ = lean_ctor_get(v___x_1604_, 0);
v_isSharedCheck_1622_ = !lean_is_exclusive(v___x_1604_);
if (v_isSharedCheck_1622_ == 0)
{
v___x_1617_ = v___x_1604_;
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
else
{
lean_inc(v_a_1615_);
lean_dec(v___x_1604_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1622_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1620_; 
if (v_isShared_1618_ == 0)
{
v___x_1620_ = v___x_1617_;
goto v_reusejp_1619_;
}
else
{
lean_object* v_reuseFailAlloc_1621_; 
v_reuseFailAlloc_1621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
v___x_1620_ = v_reuseFailAlloc_1621_;
goto v_reusejp_1619_;
}
v_reusejp_1619_:
{
return v___x_1620_;
}
}
}
}
}
else
{
lean_object* v_a_1623_; lean_object* v___x_1625_; uint8_t v_isShared_1626_; uint8_t v_isSharedCheck_1630_; 
lean_dec_ref_known(v_e_1587_, 2);
v_a_1623_ = lean_ctor_get(v___x_1597_, 0);
v_isSharedCheck_1630_ = !lean_is_exclusive(v___x_1597_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1625_ = v___x_1597_;
v_isShared_1626_ = v_isSharedCheck_1630_;
goto v_resetjp_1624_;
}
else
{
lean_inc(v_a_1623_);
lean_dec(v___x_1597_);
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
else
{
lean_object* v___x_1631_; lean_object* v___x_1632_; 
lean_dec_ref(v_e_1587_);
v___x_1631_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1632_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1631_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
lean_object* v_res_1641_; 
v_res_1641_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
lean_dec(v___y_1635_);
lean_dec(v___y_1634_);
return v_res_1641_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_){
_start:
{
lean_object* v___y_1650_; lean_object* v___x_1651_; 
lean_inc_ref(v_e_1642_);
v___y_1650_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1650_, 0, v_e_1642_);
v___x_1651_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1642_, v___y_1650_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_, v_a_1648_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_){
_start:
{
lean_object* v_res_1660_; 
v_res_1660_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_, v_a_1658_);
lean_dec(v_a_1658_);
lean_dec_ref(v_a_1657_);
lean_dec(v_a_1656_);
lean_dec_ref(v_a_1655_);
lean_dec(v_a_1654_);
lean_dec(v_a_1653_);
return v_res_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1661_, lean_object* v_constName_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_, v___y_1668_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1671_, lean_object* v_constName_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1671_, v_constName_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec(v___y_1673_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1681_, lean_object* v_ref_1682_, lean_object* v_constName_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_){
_start:
{
lean_object* v___x_1691_; 
v___x_1691_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1682_, v_constName_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1692_, lean_object* v_ref_1693_, lean_object* v_constName_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_){
_start:
{
lean_object* v_res_1702_; 
v_res_1702_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1692_, v_ref_1693_, v_constName_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_, v___y_1700_);
lean_dec(v___y_1700_);
lean_dec_ref(v___y_1699_);
lean_dec(v___y_1698_);
lean_dec_ref(v___y_1697_);
lean_dec(v___y_1696_);
lean_dec(v___y_1695_);
lean_dec(v_ref_1693_);
return v_res_1702_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1703_, lean_object* v_ref_1704_, lean_object* v_msg_1705_, lean_object* v_declHint_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_){
_start:
{
lean_object* v___x_1714_; 
v___x_1714_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1704_, v_msg_1705_, v_declHint_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
return v___x_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1715_, lean_object* v_ref_1716_, lean_object* v_msg_1717_, lean_object* v_declHint_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
lean_object* v_res_1726_; 
v_res_1726_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1715_, v_ref_1716_, v_msg_1717_, v_declHint_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v_ref_1716_);
return v_res_1726_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1727_, lean_object* v_declHint_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1727_, v_declHint_1728_, v___y_1734_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1737_, lean_object* v_declHint_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1737_, v_declHint_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec(v___y_1740_);
lean_dec(v___y_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1747_, lean_object* v_ref_1748_, lean_object* v_msg_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_){
_start:
{
lean_object* v___x_1757_; 
v___x_1757_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1748_, v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1758_, lean_object* v_ref_1759_, lean_object* v_msg_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_){
_start:
{
lean_object* v_res_1768_; 
v_res_1768_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1758_, v_ref_1759_, v_msg_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_, v___y_1766_);
lean_dec(v___y_1766_);
lean_dec_ref(v___y_1765_);
lean_dec(v___y_1764_);
lean_dec_ref(v___y_1763_);
lean_dec(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec(v_ref_1759_);
return v_res_1768_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1769_, lean_object* v_msg_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_){
_start:
{
lean_object* v___x_1778_; 
v___x_1778_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1770_, v___y_1773_, v___y_1774_, v___y_1775_, v___y_1776_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1779_, lean_object* v_msg_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1779_, v_msg_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_);
lean_dec(v___y_1786_);
lean_dec_ref(v___y_1785_);
lean_dec(v___y_1784_);
lean_dec_ref(v___y_1783_);
lean_dec(v___y_1782_);
lean_dec(v___y_1781_);
return v_res_1788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_){
_start:
{
uint8_t v___x_1797_; 
v___x_1797_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1790_);
if (v___x_1797_ == 0)
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1798_, 0, v_r_1789_);
return v___x_1798_;
}
else
{
lean_object* v___x_1799_; 
lean_inc_ref(v_r_1789_);
v___x_1799_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1789_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_object* v_a_1800_; lean_object* v___x_1802_; uint8_t v_isShared_1803_; uint8_t v_isSharedCheck_1852_; 
v_a_1800_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1852_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1852_ == 0)
{
v___x_1802_ = v___x_1799_;
v_isShared_1803_ = v_isSharedCheck_1852_;
goto v_resetjp_1801_;
}
else
{
lean_inc(v_a_1800_);
lean_dec(v___x_1799_);
v___x_1802_ = lean_box(0);
v_isShared_1803_ = v_isSharedCheck_1852_;
goto v_resetjp_1801_;
}
v_resetjp_1801_:
{
lean_object* v_expr_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1850_; 
v_expr_1804_ = lean_ctor_get(v_r_1789_, 0);
v_isSharedCheck_1850_ = !lean_is_exclusive(v_r_1789_);
if (v_isSharedCheck_1850_ == 0)
{
lean_object* v_unused_1851_; 
v_unused_1851_ = lean_ctor_get(v_r_1789_, 1);
lean_dec(v_unused_1851_);
v___x_1806_ = v_r_1789_;
v_isShared_1807_ = v_isSharedCheck_1850_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_expr_1804_);
lean_dec(v_r_1789_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1850_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
uint8_t v___x_1808_; 
v___x_1808_ = l_Lean_Expr_isSort(v_a_1800_);
if (v___x_1808_ == 0)
{
lean_object* v___x_1809_; 
lean_del_object(v___x_1802_);
lean_inc(v_a_1795_);
lean_inc_ref(v_a_1794_);
lean_inc(v_a_1793_);
lean_inc_ref(v_a_1792_);
v___x_1809_ = lean_whnf(v_a_1800_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1834_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1834_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1834_ == 0)
{
v___x_1812_ = v___x_1809_;
v_isShared_1813_ = v_isSharedCheck_1834_;
goto v_resetjp_1811_;
}
else
{
lean_inc(v_a_1810_);
lean_dec(v___x_1809_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1834_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
if (lean_obj_tag(v_a_1810_) == 3)
{
lean_object* v___x_1814_; lean_object* v___x_1816_; 
v___x_1814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1814_, 0, v_a_1810_);
lean_inc_ref(v_expr_1804_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v___x_1814_);
v___x_1816_ = v___x_1806_;
goto v_reusejp_1815_;
}
else
{
lean_object* v_reuseFailAlloc_1832_; 
v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1832_, 0, v_expr_1804_);
lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1814_);
v___x_1816_ = v_reuseFailAlloc_1832_;
goto v_reusejp_1815_;
}
v_reusejp_1815_:
{
lean_object* v___x_1817_; lean_object* v_count_1818_; lean_object* v_results_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1831_; 
v___x_1817_ = lean_st_ref_take(v_a_1791_);
v_count_1818_ = lean_ctor_get(v___x_1817_, 0);
v_results_1819_ = lean_ctor_get(v___x_1817_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1817_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1821_ = v___x_1817_;
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_results_1819_);
lean_inc(v_count_1818_);
lean_dec(v___x_1817_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1831_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_inc_ref(v___x_1816_);
v___x_1823_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1819_, v_expr_1804_, v___x_1816_);
if (v_isShared_1822_ == 0)
{
lean_ctor_set(v___x_1821_, 1, v___x_1823_);
v___x_1825_ = v___x_1821_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_count_1818_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; lean_object* v___x_1828_; 
v___x_1826_ = lean_st_ref_put(v_a_1791_, v___x_1825_);
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1816_);
v___x_1828_ = v___x_1812_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v___x_1816_);
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
}
else
{
lean_object* v___x_1833_; 
lean_del_object(v___x_1812_);
lean_dec(v_a_1810_);
lean_del_object(v___x_1806_);
v___x_1833_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1804_, v_a_1792_, v_a_1793_, v_a_1794_, v_a_1795_);
return v___x_1833_;
}
}
}
else
{
lean_object* v_a_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_1842_; 
lean_del_object(v___x_1806_);
lean_dec_ref(v_expr_1804_);
v_a_1835_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1842_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1842_ == 0)
{
v___x_1837_ = v___x_1809_;
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_a_1835_);
lean_dec(v___x_1809_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_1842_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1840_; 
if (v_isShared_1838_ == 0)
{
v___x_1840_ = v___x_1837_;
goto v_reusejp_1839_;
}
else
{
lean_object* v_reuseFailAlloc_1841_; 
v_reuseFailAlloc_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1841_, 0, v_a_1835_);
v___x_1840_ = v_reuseFailAlloc_1841_;
goto v_reusejp_1839_;
}
v_reusejp_1839_:
{
return v___x_1840_;
}
}
}
}
else
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_a_1800_);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 1, v___x_1843_);
v___x_1845_ = v___x_1806_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v_expr_1804_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
lean_object* v___x_1847_; 
if (v_isShared_1803_ == 0)
{
lean_ctor_set(v___x_1802_, 0, v___x_1845_);
v___x_1847_ = v___x_1802_;
goto v_reusejp_1846_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v___x_1845_);
v___x_1847_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1846_;
}
v_reusejp_1846_:
{
return v___x_1847_;
}
}
}
}
}
}
else
{
lean_object* v_a_1853_; lean_object* v___x_1855_; uint8_t v_isShared_1856_; uint8_t v_isSharedCheck_1860_; 
lean_dec_ref(v_r_1789_);
v_a_1853_ = lean_ctor_get(v___x_1799_, 0);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1855_ = v___x_1799_;
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
else
{
lean_inc(v_a_1853_);
lean_dec(v___x_1799_);
v___x_1855_ = lean_box(0);
v_isShared_1856_ = v_isSharedCheck_1860_;
goto v_resetjp_1854_;
}
v_resetjp_1854_:
{
lean_object* v___x_1858_; 
if (v_isShared_1856_ == 0)
{
v___x_1858_ = v___x_1855_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v_a_1853_);
v___x_1858_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
return v___x_1858_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_){
_start:
{
lean_object* v_res_1869_; 
v_res_1869_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_, v_a_1867_);
lean_dec(v_a_1867_);
lean_dec_ref(v_a_1866_);
lean_dec(v_a_1865_);
lean_dec_ref(v_a_1864_);
lean_dec(v_a_1863_);
lean_dec(v_a_1862_);
return v_res_1869_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1870_){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = l_Lean_instInhabitedExpr;
v___x_1872_ = lean_panic_fn_borrowed(v___x_1871_, v_msg_1870_);
return v___x_1872_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1876_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1877_ = lean_unsigned_to_nat(18u);
v___x_1878_ = lean_unsigned_to_nat(1846u);
v___x_1879_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1881_ = l_mkPanicMessageWithDecl(v___x_1880_, v___x_1879_, v___x_1878_, v___x_1877_, v___x_1876_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1882_, lean_object* v_f_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_){
_start:
{
lean_object* v___y_1893_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1900_; lean_object* v___y_1906_; lean_object* v_fType_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; uint8_t v___x_1967_; 
v___x_1967_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1885_);
if (v___x_1967_ == 0)
{
if (lean_obj_tag(v_e_1882_) == 5)
{
lean_object* v_expr_1968_; lean_object* v_expr_1969_; lean_object* v_fn_1970_; lean_object* v_arg_1971_; size_t v___x_1972_; size_t v___x_1973_; uint8_t v___x_1974_; 
v_expr_1968_ = lean_ctor_get(v_f_1883_, 0);
lean_inc_ref(v_expr_1968_);
lean_dec_ref(v_f_1883_);
v_expr_1969_ = lean_ctor_get(v_a_1884_, 0);
lean_inc_ref(v_expr_1969_);
lean_dec_ref(v_a_1884_);
v_fn_1970_ = lean_ctor_get(v_e_1882_, 0);
v_arg_1971_ = lean_ctor_get(v_e_1882_, 1);
v___x_1972_ = lean_ptr_addr(v_fn_1970_);
v___x_1973_ = lean_ptr_addr(v_expr_1968_);
v___x_1974_ = lean_usize_dec_eq(v___x_1972_, v___x_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec_ref_known(v_e_1882_, 2);
v___x_1975_ = l_Lean_Expr_app___override(v_expr_1968_, v_expr_1969_);
v___y_1893_ = v___x_1975_;
goto v___jp_1892_;
}
else
{
size_t v___x_1976_; size_t v___x_1977_; uint8_t v___x_1978_; 
v___x_1976_ = lean_ptr_addr(v_arg_1971_);
v___x_1977_ = lean_ptr_addr(v_expr_1969_);
v___x_1978_ = lean_usize_dec_eq(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref_known(v_e_1882_, 2);
v___x_1979_ = l_Lean_Expr_app___override(v_expr_1968_, v_expr_1969_);
v___y_1893_ = v___x_1979_;
goto v___jp_1892_;
}
else
{
lean_dec_ref(v_expr_1969_);
lean_dec_ref(v_expr_1968_);
v___y_1893_ = v_e_1882_;
goto v___jp_1892_;
}
}
}
else
{
lean_object* v___x_1980_; lean_object* v___x_1981_; 
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_f_1883_);
lean_dec_ref(v_e_1882_);
v___x_1980_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1981_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1980_);
v___y_1893_ = v___x_1981_;
goto v___jp_1892_;
}
}
else
{
lean_object* v___x_1982_; 
lean_inc_ref(v_f_1883_);
v___x_1982_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1883_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1982_) == 0)
{
lean_object* v_a_1983_; uint8_t v___x_1984_; 
v_a_1983_ = lean_ctor_get(v___x_1982_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1982_, 1);
v___x_1984_ = l_Lean_Expr_isForall(v_a_1983_);
if (v___x_1984_ == 0)
{
lean_object* v___x_1985_; 
lean_inc(v_a_1890_);
lean_inc_ref(v_a_1889_);
lean_inc(v_a_1888_);
lean_inc_ref(v_a_1887_);
v___x_1985_ = lean_whnf(v_a_1983_, v_a_1887_, v_a_1888_, v_a_1889_, v_a_1890_);
if (lean_obj_tag(v___x_1985_) == 0)
{
lean_object* v_a_1986_; 
v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
lean_inc(v_a_1986_);
lean_dec_ref_known(v___x_1985_, 1);
v_fType_1923_ = v_a_1986_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
v___y_1926_ = v_a_1888_;
v___y_1927_ = v_a_1889_;
v___y_1928_ = v_a_1890_;
goto v___jp_1922_;
}
else
{
lean_object* v_a_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_1994_; 
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_f_1883_);
lean_dec_ref(v_e_1882_);
v_a_1987_ = lean_ctor_get(v___x_1985_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1985_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1989_ = v___x_1985_;
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_a_1987_);
lean_dec(v___x_1985_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_1994_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
lean_object* v___x_1992_; 
if (v_isShared_1990_ == 0)
{
v___x_1992_ = v___x_1989_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_a_1987_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
v_fType_1923_ = v_a_1983_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
v___y_1926_ = v_a_1888_;
v___y_1927_ = v_a_1889_;
v___y_1928_ = v_a_1890_;
goto v___jp_1922_;
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_f_1883_);
lean_dec_ref(v_e_1882_);
v_a_1995_ = lean_ctor_get(v___x_1982_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1982_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1982_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1982_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
v___x_2000_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1999_;
}
v_reusejp_1999_:
{
return v___x_2000_;
}
}
}
}
v___jp_1892_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___y_1893_);
lean_ctor_set(v___x_1895_, 1, v___x_1894_);
v___x_1896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
return v___x_1896_;
}
v___jp_1897_:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1901_ = lean_expr_instantiate1(v___y_1898_, v___y_1899_);
lean_dec_ref(v___y_1899_);
lean_dec_ref(v___y_1898_);
v___x_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1903_, 0, v___y_1900_);
lean_ctor_set(v___x_1903_, 1, v___x_1902_);
v___x_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1904_, 0, v___x_1903_);
return v___x_1904_;
}
v___jp_1905_:
{
if (lean_obj_tag(v_e_1882_) == 5)
{
lean_object* v_expr_1907_; lean_object* v_expr_1908_; lean_object* v_fn_1909_; lean_object* v_arg_1910_; size_t v___x_1911_; size_t v___x_1912_; uint8_t v___x_1913_; 
v_expr_1907_ = lean_ctor_get(v_f_1883_, 0);
lean_inc_ref(v_expr_1907_);
lean_dec_ref(v_f_1883_);
v_expr_1908_ = lean_ctor_get(v_a_1884_, 0);
lean_inc_ref(v_expr_1908_);
lean_dec_ref(v_a_1884_);
v_fn_1909_ = lean_ctor_get(v_e_1882_, 0);
v_arg_1910_ = lean_ctor_get(v_e_1882_, 1);
v___x_1911_ = lean_ptr_addr(v_fn_1909_);
v___x_1912_ = lean_ptr_addr(v_expr_1907_);
v___x_1913_ = lean_usize_dec_eq(v___x_1911_, v___x_1912_);
if (v___x_1913_ == 0)
{
lean_object* v___x_1914_; 
lean_dec_ref_known(v_e_1882_, 2);
lean_inc_ref(v_expr_1908_);
v___x_1914_ = l_Lean_Expr_app___override(v_expr_1907_, v_expr_1908_);
v___y_1898_ = v___y_1906_;
v___y_1899_ = v_expr_1908_;
v___y_1900_ = v___x_1914_;
goto v___jp_1897_;
}
else
{
size_t v___x_1915_; size_t v___x_1916_; uint8_t v___x_1917_; 
v___x_1915_ = lean_ptr_addr(v_arg_1910_);
v___x_1916_ = lean_ptr_addr(v_expr_1908_);
v___x_1917_ = lean_usize_dec_eq(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref_known(v_e_1882_, 2);
lean_inc_ref(v_expr_1908_);
v___x_1918_ = l_Lean_Expr_app___override(v_expr_1907_, v_expr_1908_);
v___y_1898_ = v___y_1906_;
v___y_1899_ = v_expr_1908_;
v___y_1900_ = v___x_1918_;
goto v___jp_1897_;
}
else
{
lean_dec_ref(v_expr_1907_);
v___y_1898_ = v___y_1906_;
v___y_1899_ = v_expr_1908_;
v___y_1900_ = v_e_1882_;
goto v___jp_1897_;
}
}
}
else
{
lean_object* v_expr_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
lean_dec_ref(v_f_1883_);
lean_dec_ref(v_e_1882_);
v_expr_1919_ = lean_ctor_get(v_a_1884_, 0);
lean_inc_ref(v_expr_1919_);
lean_dec_ref(v_a_1884_);
v___x_1920_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1921_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1920_);
v___y_1898_ = v___y_1906_;
v___y_1899_ = v_expr_1919_;
v___y_1900_ = v___x_1921_;
goto v___jp_1897_;
}
}
v___jp_1922_:
{
if (lean_obj_tag(v_fType_1923_) == 7)
{
lean_object* v_binderType_1929_; lean_object* v_body_1930_; lean_object* v___x_1931_; 
v_binderType_1929_ = lean_ctor_get(v_fType_1923_, 1);
lean_inc_ref(v_binderType_1929_);
v_body_1930_ = lean_ctor_get(v_fType_1923_, 2);
lean_inc_ref(v_body_1930_);
lean_dec_ref_known(v_fType_1923_, 3);
lean_inc_ref(v_a_1884_);
v___x_1931_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1884_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
v___x_1933_ = l_Lean_Meta_isExprDefEq(v_binderType_1929_, v_a_1932_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v_a_1934_; uint8_t v___x_1935_; 
v_a_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1934_);
lean_dec_ref_known(v___x_1933_, 1);
v___x_1935_ = lean_unbox(v_a_1934_);
lean_dec(v_a_1934_);
if (v___x_1935_ == 0)
{
lean_object* v_expr_1936_; lean_object* v_expr_1937_; lean_object* v___x_1938_; 
v_expr_1936_ = lean_ctor_get(v_f_1883_, 0);
v_expr_1937_ = lean_ctor_get(v_a_1884_, 0);
lean_inc_ref(v_expr_1937_);
lean_inc_ref(v_expr_1936_);
v___x_1938_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1936_, v_expr_1937_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_dec_ref_known(v___x_1938_, 1);
v___y_1906_ = v_body_1930_;
goto v___jp_1905_;
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec_ref(v_body_1930_);
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_f_1883_);
lean_dec_ref(v_e_1882_);
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1938_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1938_);
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
v___y_1906_ = v_body_1930_;
goto v___jp_1905_;
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec_ref(v_body_1930_);
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_f_1883_);
lean_dec_ref(v_e_1882_);
v_a_1947_ = lean_ctor_get(v___x_1933_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1933_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1933_);
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
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec_ref(v_body_1930_);
lean_dec_ref(v_binderType_1929_);
lean_dec_ref(v_a_1884_);
lean_dec_ref(v_f_1883_);
lean_dec_ref(v_e_1882_);
v_a_1955_ = lean_ctor_get(v___x_1931_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1931_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1931_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1931_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_expr_1963_; lean_object* v_expr_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
lean_dec_ref(v_fType_1923_);
lean_dec_ref(v_e_1882_);
v_expr_1963_ = lean_ctor_get(v_f_1883_, 0);
lean_inc_ref(v_expr_1963_);
lean_dec_ref(v_f_1883_);
v_expr_1964_ = lean_ctor_get(v_a_1884_, 0);
lean_inc_ref(v_expr_1964_);
lean_dec_ref(v_a_1884_);
v___x_1965_ = l_Lean_Expr_app___override(v_expr_1963_, v_expr_1964_);
v___x_1966_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1965_, v___y_1925_, v___y_1926_, v___y_1927_, v___y_1928_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2003_, lean_object* v_f_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_){
_start:
{
lean_object* v_res_2013_; 
v_res_2013_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2003_, v_f_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_, v_a_2011_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
lean_dec(v_a_2009_);
lean_dec_ref(v_a_2008_);
lean_dec(v_a_2007_);
lean_dec(v_a_2006_);
return v_res_2013_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; 
v___x_2015_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2016_ = lean_unsigned_to_nat(37u);
v___x_2017_ = lean_unsigned_to_nat(345u);
v___x_2018_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2020_ = l_mkPanicMessageWithDecl(v___x_2019_, v___x_2018_, v___x_2017_, v___x_2016_, v___x_2015_);
return v___x_2020_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2021_, lean_object* v_i_2022_, lean_object* v_a_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_){
_start:
{
lean_object* v_zero_2031_; uint8_t v_isZero_2032_; 
v_zero_2031_ = lean_unsigned_to_nat(0u);
v_isZero_2032_ = lean_nat_dec_eq(v_i_2022_, v_zero_2031_);
if (v_isZero_2032_ == 1)
{
lean_object* v___x_2033_; 
lean_dec(v_i_2022_);
v___x_2033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2033_, 0, v_a_2023_);
return v___x_2033_;
}
else
{
lean_object* v_one_2034_; lean_object* v_n_2035_; lean_object* v___y_2037_; lean_object* v___y_2038_; lean_object* v___y_2042_; lean_object* v___y_2043_; lean_object* v___y_2046_; lean_object* v___x_2049_; 
v_one_2034_ = lean_unsigned_to_nat(1u);
v_n_2035_ = lean_nat_sub(v_i_2022_, v_one_2034_);
lean_dec(v_i_2022_);
v___x_2049_ = lean_array_fget_borrowed(v_fvars_2021_, v_n_2035_);
if (lean_obj_tag(v___x_2049_) == 1)
{
lean_object* v_fvarId_2050_; lean_object* v___x_2051_; 
v_fvarId_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_fvarId_2050_);
v___x_2051_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2050_, v___y_2026_);
if (lean_obj_tag(v___x_2051_) == 0)
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2051_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2051_, 1);
if (lean_obj_tag(v_a_2052_) == 1)
{
lean_object* v_val_2053_; 
v_val_2053_ = lean_ctor_get(v_a_2052_, 0);
lean_inc(v_val_2053_);
lean_dec_ref_known(v_a_2052_, 1);
if (lean_obj_tag(v_val_2053_) == 0)
{
lean_object* v_userName_2054_; lean_object* v_type_2055_; uint8_t v_bi_2056_; lean_object* v_expr_2057_; lean_object* v_type_x3f_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2079_; 
v_userName_2054_ = lean_ctor_get(v_val_2053_, 2);
lean_inc(v_userName_2054_);
v_type_2055_ = lean_ctor_get(v_val_2053_, 3);
lean_inc_ref(v_type_2055_);
v_bi_2056_ = lean_ctor_get_uint8(v_val_2053_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2053_, 4);
v_expr_2057_ = lean_ctor_get(v_a_2023_, 0);
v_type_x3f_2058_ = lean_ctor_get(v_a_2023_, 1);
v_isSharedCheck_2079_ = !lean_is_exclusive(v_a_2023_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2060_ = v_a_2023_;
v_isShared_2061_ = v_isSharedCheck_2079_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_type_x3f_2058_);
lean_inc(v_expr_2057_);
lean_dec(v_a_2023_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2079_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___y_2065_; 
v___x_2062_ = lean_expr_abstract_range(v_type_2055_, v_n_2035_, v_fvars_2021_);
lean_dec_ref(v_type_2055_);
lean_inc_ref(v___x_2062_);
lean_inc(v_userName_2054_);
v___x_2063_ = l_Lean_Expr_lam___override(v_userName_2054_, v___x_2062_, v_expr_2057_, v_bi_2056_);
if (lean_obj_tag(v_type_x3f_2058_) == 0)
{
lean_dec_ref(v___x_2062_);
lean_dec(v_userName_2054_);
v___y_2065_ = v_type_x3f_2058_;
goto v___jp_2064_;
}
else
{
lean_object* v_val_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2078_; 
v_val_2070_ = lean_ctor_get(v_type_x3f_2058_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_type_x3f_2058_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2072_ = v_type_x3f_2058_;
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_val_2070_);
lean_dec(v_type_x3f_2058_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2078_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2074_; lean_object* v___x_2076_; 
v___x_2074_ = l_Lean_Expr_forallE___override(v_userName_2054_, v___x_2062_, v_val_2070_, v_bi_2056_);
if (v_isShared_2073_ == 0)
{
lean_ctor_set(v___x_2072_, 0, v___x_2074_);
v___x_2076_ = v___x_2072_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v___x_2074_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
v___y_2065_ = v___x_2076_;
goto v___jp_2064_;
}
}
}
v___jp_2064_:
{
lean_object* v___x_2067_; 
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 1, v___y_2065_);
lean_ctor_set(v___x_2060_, 0, v___x_2063_);
v___x_2067_ = v___x_2060_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v___x_2063_);
lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___y_2065_);
v___x_2067_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
v_i_2022_ = v_n_2035_;
v_a_2023_ = v___x_2067_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2080_; lean_object* v_type_2081_; lean_object* v_value_2082_; uint8_t v_nondep_2083_; uint8_t v_nondep_2085_; lean_object* v___x_2095_; 
v_userName_2080_ = lean_ctor_get(v_val_2053_, 2);
lean_inc(v_userName_2080_);
v_type_2081_ = lean_ctor_get(v_val_2053_, 3);
lean_inc_ref(v_type_2081_);
v_value_2082_ = lean_ctor_get(v_val_2053_, 4);
lean_inc_ref(v_value_2082_);
v_nondep_2083_ = lean_ctor_get_uint8(v_val_2053_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2053_, 5);
v___x_2095_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2027_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; uint8_t v___x_2097_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
lean_inc(v_a_2096_);
lean_dec_ref_known(v___x_2095_, 1);
v___x_2097_ = 1;
if (v_nondep_2083_ == 0)
{
uint8_t v___x_2098_; 
v___x_2098_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2050_, v_a_2096_);
lean_dec(v_a_2096_);
if (v___x_2098_ == 0)
{
lean_object* v___x_2099_; 
v___x_2099_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2025_);
lean_dec_ref(v___x_2099_);
v_nondep_2085_ = v___x_2097_;
goto v___jp_2084_;
}
else
{
v_nondep_2085_ = v_nondep_2083_;
goto v___jp_2084_;
}
}
else
{
lean_dec(v_a_2096_);
v_nondep_2085_ = v___x_2097_;
goto v___jp_2084_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v_value_2082_);
lean_dec_ref(v_type_2081_);
lean_dec(v_userName_2080_);
lean_dec(v_n_2035_);
lean_dec_ref(v_a_2023_);
v_a_2100_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2095_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2095_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
v___jp_2084_:
{
lean_object* v_expr_2086_; lean_object* v_type_x3f_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; 
v_expr_2086_ = lean_ctor_get(v_a_2023_, 0);
lean_inc_ref(v_expr_2086_);
v_type_x3f_2087_ = lean_ctor_get(v_a_2023_, 1);
lean_inc(v_type_x3f_2087_);
lean_dec_ref(v_a_2023_);
v___x_2088_ = lean_expr_abstract_range(v_type_2081_, v_n_2035_, v_fvars_2021_);
lean_dec_ref(v_type_2081_);
v___x_2089_ = lean_expr_abstract_range(v_value_2082_, v_n_2035_, v_fvars_2021_);
lean_dec_ref(v_value_2082_);
lean_inc_ref(v___x_2089_);
lean_inc_ref(v___x_2088_);
lean_inc(v_userName_2080_);
v___x_2090_ = l_Lean_Expr_letE___override(v_userName_2080_, v___x_2088_, v___x_2089_, v_expr_2086_, v_nondep_2085_);
if (lean_obj_tag(v_type_x3f_2087_) == 0)
{
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v_userName_2080_);
v___y_2037_ = v___x_2090_;
v___y_2038_ = v_type_x3f_2087_;
goto v___jp_2036_;
}
else
{
lean_object* v_val_2091_; uint8_t v___x_2092_; 
v_val_2091_ = lean_ctor_get(v_type_x3f_2087_, 0);
lean_inc(v_val_2091_);
lean_dec_ref_known(v_type_x3f_2087_, 1);
v___x_2092_ = lean_expr_has_loose_bvar(v_val_2091_, v_zero_2031_);
if (v___x_2092_ == 0)
{
lean_object* v___x_2093_; 
lean_dec_ref(v___x_2089_);
lean_dec_ref(v___x_2088_);
lean_dec(v_userName_2080_);
v___x_2093_ = lean_expr_lower_loose_bvars(v_val_2091_, v_one_2034_, v_one_2034_);
lean_dec(v_val_2091_);
v___y_2042_ = v___x_2090_;
v___y_2043_ = v___x_2093_;
goto v___jp_2041_;
}
else
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_Expr_letE___override(v_userName_2080_, v___x_2088_, v___x_2089_, v_val_2091_, v_nondep_2085_);
v___y_2042_ = v___x_2090_;
v___y_2043_ = v___x_2094_;
goto v___jp_2041_;
}
}
}
}
}
else
{
lean_object* v___x_2108_; 
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2023_);
lean_inc(v_fvarId_2050_);
v___x_2108_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2050_, v___y_2028_, v___y_2029_);
v___y_2046_ = v___x_2108_;
goto v___jp_2045_;
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_n_2035_);
lean_dec_ref(v_a_2023_);
v_a_2109_ = lean_ctor_get(v___x_2051_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2051_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2051_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref(v_a_2023_);
v___x_2117_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2118_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2117_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_, v___y_2029_);
v___y_2046_ = v___x_2118_;
goto v___jp_2045_;
}
v___jp_2036_:
{
lean_object* v___x_2039_; 
v___x_2039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2039_, 0, v___y_2037_);
lean_ctor_set(v___x_2039_, 1, v___y_2038_);
v_i_2022_ = v_n_2035_;
v_a_2023_ = v___x_2039_;
goto _start;
}
v___jp_2041_:
{
lean_object* v___x_2044_; 
v___x_2044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2044_, 0, v___y_2043_);
v___y_2037_ = v___y_2042_;
v___y_2038_ = v___x_2044_;
goto v___jp_2036_;
}
v___jp_2045_:
{
if (lean_obj_tag(v___y_2046_) == 0)
{
lean_object* v_a_2047_; 
v_a_2047_ = lean_ctor_get(v___y_2046_, 0);
lean_inc(v_a_2047_);
lean_dec_ref_known(v___y_2046_, 1);
v_i_2022_ = v_n_2035_;
v_a_2023_ = v_a_2047_;
goto _start;
}
else
{
lean_dec(v_n_2035_);
return v___y_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2119_, lean_object* v_i_2120_, lean_object* v_a_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2119_, v_i_2120_, v_a_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_, v___y_2127_);
lean_dec(v___y_2127_);
lean_dec_ref(v___y_2126_);
lean_dec(v___y_2125_);
lean_dec_ref(v___y_2124_);
lean_dec(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec_ref(v_fvars_2119_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2130_, lean_object* v_a_2131_){
_start:
{
if (lean_obj_tag(v_a_2130_) == 0)
{
lean_object* v___x_2132_; 
v___x_2132_ = l_List_reverse___redArg(v_a_2131_);
return v___x_2132_;
}
else
{
lean_object* v_head_2133_; lean_object* v_tail_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2143_; 
v_head_2133_ = lean_ctor_get(v_a_2130_, 0);
v_tail_2134_ = lean_ctor_get(v_a_2130_, 1);
v_isSharedCheck_2143_ = !lean_is_exclusive(v_a_2130_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2136_ = v_a_2130_;
v_isShared_2137_ = v_isSharedCheck_2143_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_tail_2134_);
lean_inc(v_head_2133_);
lean_dec(v_a_2130_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2143_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2138_; lean_object* v___x_2140_; 
v___x_2138_ = l_Lean_MessageData_ofExpr(v_head_2133_);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 1, v_a_2131_);
lean_ctor_set(v___x_2136_, 0, v___x_2138_);
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v___x_2138_);
lean_ctor_set(v_reuseFailAlloc_2142_, 1, v_a_2131_);
v___x_2140_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
v_a_2130_ = v_tail_2134_;
v_a_2131_ = v___x_2140_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2144_; double v___x_2145_; 
v___x_2144_ = lean_unsigned_to_nat(0u);
v___x_2145_ = lean_float_of_nat(v___x_2144_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2149_, lean_object* v_msg_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
lean_object* v_ref_2156_; lean_object* v___x_2157_; lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2203_; 
v_ref_2156_ = lean_ctor_get(v___y_2153_, 2);
v___x_2157_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2150_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2203_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2203_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2203_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2203_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; lean_object* v_traceState_2163_; lean_object* v_env_2164_; lean_object* v_nextMacroScope_2165_; lean_object* v_ngen_2166_; lean_object* v_auxDeclNGen_2167_; lean_object* v_cache_2168_; lean_object* v_recordedDeps_2169_; lean_object* v_messages_2170_; lean_object* v_infoState_2171_; lean_object* v_snapshotTasks_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2202_; 
v___x_2162_ = lean_st_ref_take(v___y_2154_);
v_traceState_2163_ = lean_ctor_get(v___x_2162_, 4);
v_env_2164_ = lean_ctor_get(v___x_2162_, 0);
v_nextMacroScope_2165_ = lean_ctor_get(v___x_2162_, 1);
v_ngen_2166_ = lean_ctor_get(v___x_2162_, 2);
v_auxDeclNGen_2167_ = lean_ctor_get(v___x_2162_, 3);
v_cache_2168_ = lean_ctor_get(v___x_2162_, 5);
v_recordedDeps_2169_ = lean_ctor_get(v___x_2162_, 6);
v_messages_2170_ = lean_ctor_get(v___x_2162_, 7);
v_infoState_2171_ = lean_ctor_get(v___x_2162_, 8);
v_snapshotTasks_2172_ = lean_ctor_get(v___x_2162_, 9);
v_isSharedCheck_2202_ = !lean_is_exclusive(v___x_2162_);
if (v_isSharedCheck_2202_ == 0)
{
v___x_2174_ = v___x_2162_;
v_isShared_2175_ = v_isSharedCheck_2202_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_snapshotTasks_2172_);
lean_inc(v_infoState_2171_);
lean_inc(v_messages_2170_);
lean_inc(v_recordedDeps_2169_);
lean_inc(v_cache_2168_);
lean_inc(v_traceState_2163_);
lean_inc(v_auxDeclNGen_2167_);
lean_inc(v_ngen_2166_);
lean_inc(v_nextMacroScope_2165_);
lean_inc(v_env_2164_);
lean_dec(v___x_2162_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2202_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
uint64_t v_tid_2176_; lean_object* v_traces_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2201_; 
v_tid_2176_ = lean_ctor_get_uint64(v_traceState_2163_, sizeof(void*)*1);
v_traces_2177_ = lean_ctor_get(v_traceState_2163_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v_traceState_2163_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2179_ = v_traceState_2163_;
v_isShared_2180_ = v_isSharedCheck_2201_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_traces_2177_);
lean_dec(v_traceState_2163_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2201_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; double v___x_2183_; uint8_t v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2192_; 
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2184_ = 0;
v___x_2185_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2186_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2186_, 0, v_cls_2149_);
lean_ctor_set(v___x_2186_, 1, v___x_2182_);
lean_ctor_set(v___x_2186_, 2, v___x_2185_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3, v___x_2183_);
lean_ctor_set_float(v___x_2186_, sizeof(void*)*3 + 8, v___x_2183_);
lean_ctor_set_uint8(v___x_2186_, sizeof(void*)*3 + 16, v___x_2184_);
v___x_2187_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2188_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2186_);
lean_ctor_set(v___x_2188_, 1, v_a_2158_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_inc(v_ref_2156_);
v___x_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2189_, 0, v_ref_2156_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = l_Lean_PersistentArray_push___redArg(v_traces_2177_, v___x_2189_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2190_);
v___x_2192_ = v___x_2179_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2190_);
lean_ctor_set_uint64(v_reuseFailAlloc_2200_, sizeof(void*)*1, v_tid_2176_);
v___x_2192_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2194_; 
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 4, v___x_2192_);
v___x_2194_ = v___x_2174_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_env_2164_);
lean_ctor_set(v_reuseFailAlloc_2199_, 1, v_nextMacroScope_2165_);
lean_ctor_set(v_reuseFailAlloc_2199_, 2, v_ngen_2166_);
lean_ctor_set(v_reuseFailAlloc_2199_, 3, v_auxDeclNGen_2167_);
lean_ctor_set(v_reuseFailAlloc_2199_, 4, v___x_2192_);
lean_ctor_set(v_reuseFailAlloc_2199_, 5, v_cache_2168_);
lean_ctor_set(v_reuseFailAlloc_2199_, 6, v_recordedDeps_2169_);
lean_ctor_set(v_reuseFailAlloc_2199_, 7, v_messages_2170_);
lean_ctor_set(v_reuseFailAlloc_2199_, 8, v_infoState_2171_);
lean_ctor_set(v_reuseFailAlloc_2199_, 9, v_snapshotTasks_2172_);
v___x_2194_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2195_ = lean_st_ref_put(v___y_2154_, v___x_2194_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2181_);
v___x_2197_ = v___x_2160_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2181_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2204_, lean_object* v_msg_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v_res_2211_; 
v_res_2211_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2204_, v_msg_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
lean_dec(v___y_2209_);
lean_dec_ref(v___y_2208_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
return v_res_2211_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
v_cls_2222_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2223_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2224_ = l_Lean_Name_append(v___x_2223_, v_cls_2222_);
return v___x_2224_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2227_ = l_Lean_stringToMessageData(v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2233_ = l_Lean_stringToMessageData(v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2238_ = l_Lean_MessageData_ofFormat(v___x_2237_);
return v___x_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2239_, lean_object* v_body_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_){
_start:
{
lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v_toCold_2279_; lean_object* v_options_2280_; uint8_t v_hasTrace_2281_; 
v_toCold_2279_ = lean_ctor_get(v_a_2245_, 0);
v_options_2280_ = lean_ctor_get(v_toCold_2279_, 2);
v_hasTrace_2281_ = lean_ctor_get_uint8(v_options_2280_, sizeof(void*)*1);
if (v_hasTrace_2281_ == 0)
{
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
v___y_2264_ = v_a_2244_;
v___y_2265_ = v_a_2245_;
v___y_2266_ = v_a_2246_;
goto v___jp_2260_;
}
else
{
lean_object* v_inheritedTraceOptions_2282_; lean_object* v_cls_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; 
v_inheritedTraceOptions_2282_ = lean_ctor_get(v_toCold_2279_, 11);
v_cls_2283_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2284_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2285_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2282_, v_options_2280_, v___x_2284_);
if (v___x_2285_ == 0)
{
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
v___y_2264_ = v_a_2244_;
v___y_2265_ = v_a_2245_;
v___y_2266_ = v_a_2246_;
goto v___jp_2260_;
}
else
{
lean_object* v_expr_2286_; lean_object* v_type_x3f_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___y_2300_; 
v_expr_2286_ = lean_ctor_get(v_body_2240_, 0);
v_type_x3f_2287_ = lean_ctor_get(v_body_2240_, 1);
v___x_2288_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2239_);
v___x_2289_ = lean_array_to_list(v_fvars_2239_);
v___x_2290_ = lean_box(0);
v___x_2291_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2289_, v___x_2290_);
v___x_2292_ = l_Lean_MessageData_ofList(v___x_2291_);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2288_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2295_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2293_);
lean_ctor_set(v___x_2295_, 1, v___x_2294_);
lean_inc_ref(v_expr_2286_);
v___x_2296_ = l_Lean_MessageData_ofExpr(v_expr_2286_);
v___x_2297_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
if (lean_obj_tag(v_type_x3f_2287_) == 0)
{
lean_object* v___x_2313_; 
v___x_2313_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2300_ = v___x_2313_;
goto v___jp_2299_;
}
else
{
lean_object* v_val_2314_; lean_object* v___x_2315_; 
v_val_2314_ = lean_ctor_get(v_type_x3f_2287_, 0);
lean_inc(v_val_2314_);
v___x_2315_ = l_Lean_MessageData_ofExpr(v_val_2314_);
v___y_2300_ = v___x_2315_;
goto v___jp_2299_;
}
v___jp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2298_);
lean_ctor_set(v___x_2301_, 1, v___y_2300_);
v___x_2302_ = l_Lean_indentD(v___x_2301_);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2295_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2283_, v___x_2303_, v_a_2243_, v_a_2244_, v_a_2245_, v_a_2246_);
if (lean_obj_tag(v___x_2304_) == 0)
{
lean_dec_ref_known(v___x_2304_, 1);
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
v___y_2264_ = v_a_2244_;
v___y_2265_ = v_a_2245_;
v___y_2266_ = v_a_2246_;
goto v___jp_2260_;
}
else
{
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_dec_ref(v_body_2240_);
lean_dec_ref(v_fvars_2239_);
v_a_2305_ = lean_ctor_get(v___x_2304_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2304_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
}
}
v___jp_2248_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___y_2249_);
lean_ctor_set(v___x_2257_, 1, v___y_2256_);
v___x_2258_ = lean_array_get_size(v_fvars_2239_);
v___x_2259_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2239_, v___x_2258_, v___x_2257_, v___y_2252_, v___y_2251_, v___y_2250_, v___y_2253_, v___y_2254_, v___y_2255_);
lean_dec_ref(v_fvars_2239_);
return v___x_2259_;
}
v___jp_2260_:
{
lean_object* v_expr_2267_; lean_object* v_type_x3f_2268_; lean_object* v___x_2269_; 
v_expr_2267_ = lean_ctor_get(v_body_2240_, 0);
lean_inc_ref(v_expr_2267_);
v_type_x3f_2268_ = lean_ctor_get(v_body_2240_, 1);
lean_inc(v_type_x3f_2268_);
lean_dec_ref(v_body_2240_);
v___x_2269_ = lean_expr_abstract(v_expr_2267_, v_fvars_2239_);
lean_dec_ref(v_expr_2267_);
if (lean_obj_tag(v_type_x3f_2268_) == 0)
{
v___y_2249_ = v___x_2269_;
v___y_2250_ = v___y_2263_;
v___y_2251_ = v___y_2262_;
v___y_2252_ = v___y_2261_;
v___y_2253_ = v___y_2264_;
v___y_2254_ = v___y_2265_;
v___y_2255_ = v___y_2266_;
v___y_2256_ = v_type_x3f_2268_;
goto v___jp_2248_;
}
else
{
lean_object* v_val_2270_; lean_object* v___x_2272_; uint8_t v_isShared_2273_; uint8_t v_isSharedCheck_2278_; 
v_val_2270_ = lean_ctor_get(v_type_x3f_2268_, 0);
v_isSharedCheck_2278_ = !lean_is_exclusive(v_type_x3f_2268_);
if (v_isSharedCheck_2278_ == 0)
{
v___x_2272_ = v_type_x3f_2268_;
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
else
{
lean_inc(v_val_2270_);
lean_dec(v_type_x3f_2268_);
v___x_2272_ = lean_box(0);
v_isShared_2273_ = v_isSharedCheck_2278_;
goto v_resetjp_2271_;
}
v_resetjp_2271_:
{
lean_object* v___x_2274_; lean_object* v___x_2276_; 
v___x_2274_ = lean_expr_abstract(v_val_2270_, v_fvars_2239_);
lean_dec(v_val_2270_);
if (v_isShared_2273_ == 0)
{
lean_ctor_set(v___x_2272_, 0, v___x_2274_);
v___x_2276_ = v___x_2272_;
goto v_reusejp_2275_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2274_);
v___x_2276_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2275_;
}
v_reusejp_2275_:
{
v___y_2249_ = v___x_2269_;
v___y_2250_ = v___y_2263_;
v___y_2251_ = v___y_2262_;
v___y_2252_ = v___y_2261_;
v___y_2253_ = v___y_2264_;
v___y_2254_ = v___y_2265_;
v___y_2255_ = v___y_2266_;
v___y_2256_ = v___x_2276_;
goto v___jp_2248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2316_, lean_object* v_body_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_){
_start:
{
lean_object* v_res_2325_; 
v_res_2325_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2316_, v_body_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
lean_dec(v_a_2323_);
lean_dec_ref(v_a_2322_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec(v_a_2318_);
return v_res_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2326_, lean_object* v_n_2327_, lean_object* v_i_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2326_, v_i_2328_, v_a_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_, v___y_2335_, v___y_2336_);
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2339_, lean_object* v_n_2340_, lean_object* v_i_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_){
_start:
{
lean_object* v_res_2351_; 
v_res_2351_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2339_, v_n_2340_, v_i_2341_, v_a_2342_, v_a_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_, v___y_2349_);
lean_dec(v___y_2349_);
lean_dec_ref(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec(v___y_2344_);
lean_dec(v_n_2340_);
lean_dec_ref(v_fvars_2339_);
return v_res_2351_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2352_, lean_object* v_msg_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2352_, v_msg_2353_, v___y_2356_, v___y_2357_, v___y_2358_, v___y_2359_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2362_, lean_object* v_msg_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2362_, v_msg_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_);
lean_dec(v___y_2369_);
lean_dec_ref(v___y_2368_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec(v___y_2364_);
return v_res_2371_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2377_ = l_Lean_stringToMessageData(v___x_2376_);
return v___x_2377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2378_, lean_object* v_structName_2379_, lean_object* v_idx_2380_, lean_object* v_a_2381_, lean_object* v_00_u03b1_2382_, lean_object* v_x_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_){
_start:
{
lean_object* v_expr_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2406_; 
v_expr_2391_ = lean_ctor_get(v_struct_2378_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v_struct_2378_);
if (v_isSharedCheck_2406_ == 0)
{
lean_object* v_unused_2407_; 
v_unused_2407_ = lean_ctor_get(v_struct_2378_, 1);
lean_dec(v_unused_2407_);
v___x_2393_ = v_struct_2378_;
v_isShared_2394_ = v_isSharedCheck_2406_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_expr_2391_);
lean_dec(v_struct_2378_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2406_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2395_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2396_ = l_Lean_mkProj(v_structName_2379_, v_idx_2380_, v_expr_2391_);
v___x_2397_ = l_Lean_indentExpr(v___x_2396_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set_tag(v___x_2393_, 7);
lean_ctor_set(v___x_2393_, 1, v___x_2397_);
lean_ctor_set(v___x_2393_, 0, v___x_2395_);
v___x_2399_ = v___x_2393_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v___x_2395_);
lean_ctor_set(v_reuseFailAlloc_2405_, 1, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2400_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = l_Lean_indentExpr(v_a_2381_);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2403_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_);
return v___x_2404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2408_, lean_object* v_structName_2409_, lean_object* v_idx_2410_, lean_object* v_a_2411_, lean_object* v_00_u03b1_2412_, lean_object* v_x_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2408_, v_structName_2409_, v_idx_2410_, v_a_2411_, v_00_u03b1_2412_, v_x_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec(v___y_2414_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_){
_start:
{
lean_object* v___x_2430_; lean_object* v_env_2431_; uint8_t v___x_2432_; lean_object* v___x_2433_; 
v___x_2430_ = lean_st_ref_get(v___y_2428_);
v_env_2431_ = lean_ctor_get(v___x_2430_, 0);
lean_inc_ref(v_env_2431_);
lean_dec(v___x_2430_);
v___x_2432_ = 0;
lean_inc(v_constName_2422_);
v___x_2433_ = l_Lean_Environment_find_x3f(v_env_2431_, v_constName_2422_, v___x_2432_);
if (lean_obj_tag(v___x_2433_) == 0)
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_);
return v___x_2434_;
}
else
{
lean_object* v_val_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v_constName_2422_);
v_val_2435_ = lean_ctor_get(v___x_2433_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2433_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2433_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_val_2435_);
lean_dec(v___x_2433_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 0);
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_val_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec(v___y_2444_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2452_, lean_object* v_structName_2453_, lean_object* v_idx_2454_, lean_object* v_a_2455_, lean_object* v_00_u03b1_2456_, lean_object* v_x_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_){
_start:
{
lean_object* v_expr_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2480_; 
v_expr_2465_ = lean_ctor_get(v_struct_2452_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v_struct_2452_);
if (v_isSharedCheck_2480_ == 0)
{
lean_object* v_unused_2481_; 
v_unused_2481_ = lean_ctor_get(v_struct_2452_, 1);
lean_dec(v_unused_2481_);
v___x_2467_ = v_struct_2452_;
v_isShared_2468_ = v_isSharedCheck_2480_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_expr_2465_);
lean_dec(v_struct_2452_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2480_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
v___x_2469_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2470_ = l_Lean_mkProj(v_structName_2453_, v_idx_2454_, v_expr_2465_);
v___x_2471_ = l_Lean_indentExpr(v___x_2470_);
if (v_isShared_2468_ == 0)
{
lean_ctor_set_tag(v___x_2467_, 7);
lean_ctor_set(v___x_2467_, 1, v___x_2471_);
lean_ctor_set(v___x_2467_, 0, v___x_2469_);
v___x_2473_ = v___x_2467_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v___x_2469_);
lean_ctor_set(v_reuseFailAlloc_2479_, 1, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2474_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = l_Lean_indentExpr(v_a_2455_);
v___x_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2477_, 0, v___x_2475_);
lean_ctor_set(v___x_2477_, 1, v___x_2476_);
v___x_2478_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2477_, v___y_2460_, v___y_2461_, v___y_2462_, v___y_2463_);
return v___x_2478_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2482_, lean_object* v_structName_2483_, lean_object* v_idx_2484_, lean_object* v_a_2485_, lean_object* v_00_u03b1_2486_, lean_object* v_x_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2482_, v_structName_2483_, v_idx_2484_, v_a_2485_, v_00_u03b1_2486_, v_x_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec(v___y_2488_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2496_, lean_object* v_fst_2497_, lean_object* v_struct_2498_, lean_object* v_structName_2499_, uint8_t v_a_2500_, lean_object* v___f_2501_, lean_object* v_snd_2502_, lean_object* v_____r_2503_, lean_object* v_ctorType_2504_, lean_object* v_j_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
if (lean_obj_tag(v_ctorType_2504_) == 7)
{
lean_object* v_binderType_2513_; lean_object* v_body_2514_; lean_object* v___x_2515_; 
lean_dec(v_snd_2502_);
v_binderType_2513_ = lean_ctor_get(v_ctorType_2504_, 1);
lean_inc_ref(v_binderType_2513_);
v_body_2514_ = lean_ctor_get(v_ctorType_2504_, 2);
lean_inc_ref(v_body_2514_);
lean_dec_ref_known(v_ctorType_2504_, 3);
v___x_2515_ = lean_expr_instantiate_rev_range(v_binderType_2513_, v_j_2505_, v_a_2496_, v_fst_2497_);
lean_dec_ref(v_binderType_2513_);
if (v_a_2500_ == 0)
{
lean_dec_ref(v___f_2501_);
goto v___jp_2516_;
}
else
{
lean_object* v___x_2532_; 
lean_inc_ref(v___x_2515_);
v___x_2532_ = l_Lean_Meta_isProp(v___x_2515_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; uint8_t v___x_2534_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = lean_unbox(v_a_2533_);
lean_dec(v_a_2533_);
if (v___x_2534_ == 0)
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = lean_box(0);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc(v___y_2506_);
v___x_2536_ = lean_apply_9(v___f_2501_, lean_box(0), v___x_2535_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_dec_ref_known(v___x_2536_, 1);
goto v___jp_2516_;
}
else
{
lean_object* v_a_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2544_; 
lean_dec_ref(v___x_2515_);
lean_dec_ref(v_body_2514_);
lean_dec(v_structName_2499_);
lean_dec_ref(v_struct_2498_);
lean_dec(v_fst_2497_);
lean_dec(v_a_2496_);
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2544_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2544_ == 0)
{
v___x_2539_ = v___x_2536_;
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_a_2537_);
lean_dec(v___x_2536_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2544_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v___x_2542_; 
if (v_isShared_2540_ == 0)
{
v___x_2542_ = v___x_2539_;
goto v_reusejp_2541_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v_a_2537_);
v___x_2542_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2541_;
}
v_reusejp_2541_:
{
return v___x_2542_;
}
}
}
}
else
{
lean_dec_ref(v___f_2501_);
goto v___jp_2516_;
}
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v___x_2515_);
lean_dec_ref(v_body_2514_);
lean_dec_ref(v___f_2501_);
lean_dec(v_structName_2499_);
lean_dec_ref(v_struct_2498_);
lean_dec(v_fst_2497_);
lean_dec(v_a_2496_);
v_a_2545_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2532_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2532_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
v___jp_2516_:
{
lean_object* v_expr_2517_; lean_object* v___x_2519_; uint8_t v_isShared_2520_; uint8_t v_isSharedCheck_2530_; 
v_expr_2517_ = lean_ctor_get(v_struct_2498_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v_struct_2498_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v_struct_2498_, 1);
lean_dec(v_unused_2531_);
v___x_2519_ = v_struct_2498_;
v_isShared_2520_ = v_isSharedCheck_2530_;
goto v_resetjp_2518_;
}
else
{
lean_inc(v_expr_2517_);
lean_dec(v_struct_2498_);
v___x_2519_ = lean_box(0);
v_isShared_2520_ = v_isSharedCheck_2530_;
goto v_resetjp_2518_;
}
v_resetjp_2518_:
{
lean_object* v___x_2521_; lean_object* v___x_2522_; lean_object* v___x_2524_; 
v___x_2521_ = l_Lean_Expr_proj___override(v_structName_2499_, v_a_2496_, v_expr_2517_);
v___x_2522_ = lean_array_push(v_fst_2497_, v___x_2521_);
lean_inc(v_j_2505_);
if (v_isShared_2520_ == 0)
{
lean_ctor_set(v___x_2519_, 1, v___x_2515_);
lean_ctor_set(v___x_2519_, 0, v_j_2505_);
v___x_2524_ = v___x_2519_;
goto v_reusejp_2523_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_j_2505_);
lean_ctor_set(v_reuseFailAlloc_2529_, 1, v___x_2515_);
v___x_2524_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2523_;
}
v_reusejp_2523_:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2522_);
lean_ctor_set(v___x_2525_, 1, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2526_, 0, v_body_2514_);
lean_ctor_set(v___x_2526_, 1, v___x_2525_);
v___x_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2527_, 0, v___x_2526_);
v___x_2528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2527_);
return v___x_2528_;
}
}
}
}
else
{
lean_object* v___x_2553_; lean_object* v___x_2554_; 
lean_dec(v_structName_2499_);
lean_dec_ref(v_struct_2498_);
lean_dec(v_a_2496_);
v___x_2553_ = lean_box(0);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc(v___y_2506_);
v___x_2554_ = lean_apply_9(v___f_2501_, lean_box(0), v___x_2553_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2565_; 
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2554_, 0);
lean_dec(v_unused_2566_);
v___x_2556_ = v___x_2554_;
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
else
{
lean_dec(v___x_2554_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2565_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2563_; 
lean_inc(v_j_2505_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_j_2505_);
lean_ctor_set(v___x_2558_, 1, v_snd_2502_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v_fst_2497_);
lean_ctor_set(v___x_2559_, 1, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v_ctorType_2504_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v___x_2561_);
v___x_2563_ = v___x_2556_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___x_2561_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref(v_ctorType_2504_);
lean_dec(v_snd_2502_);
lean_dec(v_fst_2497_);
v_a_2567_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2554_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2554_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2575_ = _args[0];
lean_object* v_fst_2576_ = _args[1];
lean_object* v_struct_2577_ = _args[2];
lean_object* v_structName_2578_ = _args[3];
lean_object* v_a_2579_ = _args[4];
lean_object* v___f_2580_ = _args[5];
lean_object* v_snd_2581_ = _args[6];
lean_object* v_____r_2582_ = _args[7];
lean_object* v_ctorType_2583_ = _args[8];
lean_object* v_j_2584_ = _args[9];
lean_object* v___y_2585_ = _args[10];
lean_object* v___y_2586_ = _args[11];
lean_object* v___y_2587_ = _args[12];
lean_object* v___y_2588_ = _args[13];
lean_object* v___y_2589_ = _args[14];
lean_object* v___y_2590_ = _args[15];
lean_object* v___y_2591_ = _args[16];
_start:
{
uint8_t v_a_19035__boxed_2592_; lean_object* v_res_2593_; 
v_a_19035__boxed_2592_ = lean_unbox(v_a_2579_);
v_res_2593_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2575_, v_fst_2576_, v_struct_2577_, v_structName_2578_, v_a_19035__boxed_2592_, v___f_2580_, v_snd_2581_, v_____r_2582_, v_ctorType_2583_, v_j_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_, v___y_2589_, v___y_2590_);
lean_dec(v___y_2590_);
lean_dec_ref(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec(v___y_2585_);
lean_dec(v_j_2584_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2594_, lean_object* v_struct_2595_, lean_object* v_structName_2596_, uint8_t v_a_2597_, lean_object* v_idx_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_b_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___y_2610_; uint8_t v___x_2632_; 
v___x_2632_ = lean_nat_dec_le(v_a_2600_, v_upperBound_2594_);
if (v___x_2632_ == 0)
{
lean_object* v___x_2633_; 
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_idx_2598_);
lean_dec(v_structName_2596_);
lean_dec_ref(v_struct_2595_);
v___x_2633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2633_, 0, v_b_2601_);
return v___x_2633_;
}
else
{
lean_object* v_snd_2634_; lean_object* v_snd_2635_; lean_object* v_fst_2636_; lean_object* v_fst_2637_; lean_object* v_fst_2638_; lean_object* v_snd_2639_; lean_object* v___f_2640_; uint8_t v___x_2641_; 
v_snd_2634_ = lean_ctor_get(v_b_2601_, 1);
lean_inc(v_snd_2634_);
v_snd_2635_ = lean_ctor_get(v_snd_2634_, 1);
lean_inc(v_snd_2635_);
v_fst_2636_ = lean_ctor_get(v_b_2601_, 0);
lean_inc(v_fst_2636_);
lean_dec_ref(v_b_2601_);
v_fst_2637_ = lean_ctor_get(v_snd_2634_, 0);
lean_inc(v_fst_2637_);
lean_dec(v_snd_2634_);
v_fst_2638_ = lean_ctor_get(v_snd_2635_, 0);
lean_inc(v_fst_2638_);
v_snd_2639_ = lean_ctor_get(v_snd_2635_, 1);
lean_inc(v_snd_2639_);
lean_dec(v_snd_2635_);
lean_inc_ref(v_a_2599_);
lean_inc(v_idx_2598_);
lean_inc(v_structName_2596_);
lean_inc_ref(v_struct_2595_);
v___f_2640_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2640_, 0, v_struct_2595_);
lean_closure_set(v___f_2640_, 1, v_structName_2596_);
lean_closure_set(v___f_2640_, 2, v_idx_2598_);
lean_closure_set(v___f_2640_, 3, v_a_2599_);
v___x_2641_ = l_Lean_Expr_isForall(v_fst_2636_);
if (v___x_2641_ == 0)
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_expr_instantiate_rev_range(v_fst_2636_, v_fst_2638_, v_a_2600_, v_fst_2637_);
lean_dec(v_fst_2638_);
lean_dec(v_fst_2636_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
v___x_2643_ = lean_whnf(v___x_2642_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = lean_box(0);
lean_inc(v_structName_2596_);
lean_inc_ref(v_struct_2595_);
lean_inc(v_a_2600_);
v___x_2646_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2600_, v_fst_2637_, v_struct_2595_, v_structName_2596_, v_a_2597_, v___f_2640_, v_snd_2639_, v___x_2645_, v_a_2644_, v_a_2600_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
v___y_2610_ = v___x_2646_;
goto v___jp_2609_;
}
else
{
lean_object* v_a_2647_; lean_object* v___x_2649_; uint8_t v_isShared_2650_; uint8_t v_isSharedCheck_2654_; 
lean_dec_ref(v___f_2640_);
lean_dec(v_snd_2639_);
lean_dec(v_fst_2637_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_idx_2598_);
lean_dec(v_structName_2596_);
lean_dec_ref(v_struct_2595_);
v_a_2647_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2654_ == 0)
{
v___x_2649_ = v___x_2643_;
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
else
{
lean_inc(v_a_2647_);
lean_dec(v___x_2643_);
v___x_2649_ = lean_box(0);
v_isShared_2650_ = v_isSharedCheck_2654_;
goto v_resetjp_2648_;
}
v_resetjp_2648_:
{
lean_object* v___x_2652_; 
if (v_isShared_2650_ == 0)
{
v___x_2652_ = v___x_2649_;
goto v_reusejp_2651_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
v___x_2652_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2651_;
}
v_reusejp_2651_:
{
return v___x_2652_;
}
}
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_box(0);
lean_inc(v_structName_2596_);
lean_inc_ref(v_struct_2595_);
lean_inc(v_a_2600_);
v___x_2656_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2600_, v_fst_2637_, v_struct_2595_, v_structName_2596_, v_a_2597_, v___f_2640_, v_snd_2639_, v___x_2655_, v_fst_2636_, v_fst_2638_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v_fst_2638_);
v___y_2610_ = v___x_2656_;
goto v___jp_2609_;
}
}
v___jp_2609_:
{
if (lean_obj_tag(v___y_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2623_; 
v_a_2611_ = lean_ctor_get(v___y_2610_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___y_2610_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2613_ = v___y_2610_;
v_isShared_2614_ = v_isSharedCheck_2623_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___y_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2623_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
if (lean_obj_tag(v_a_2611_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; 
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_idx_2598_);
lean_dec(v_structName_2596_);
lean_dec_ref(v_struct_2595_);
v_a_2615_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v_a_2611_, 1);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v_a_2615_);
v___x_2617_ = v___x_2613_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2615_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; 
lean_del_object(v___x_2613_);
v_a_2619_ = lean_ctor_get(v_a_2611_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v_a_2611_, 1);
v___x_2620_ = lean_unsigned_to_nat(1u);
v___x_2621_ = lean_nat_add(v_a_2600_, v___x_2620_);
lean_dec(v_a_2600_);
v_a_2600_ = v___x_2621_;
v_b_2601_ = v_a_2619_;
goto _start;
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_idx_2598_);
lean_dec(v_structName_2596_);
lean_dec_ref(v_struct_2595_);
v_a_2624_ = lean_ctor_get(v___y_2610_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___y_2610_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___y_2610_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___y_2610_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2657_, lean_object* v_struct_2658_, lean_object* v_structName_2659_, lean_object* v_a_2660_, lean_object* v_idx_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_b_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_){
_start:
{
uint8_t v_a_19192__boxed_2672_; lean_object* v_res_2673_; 
v_a_19192__boxed_2672_ = lean_unbox(v_a_2660_);
v_res_2673_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2657_, v_struct_2658_, v_structName_2659_, v_a_19192__boxed_2672_, v_idx_2661_, v_a_2662_, v_a_2663_, v_b_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
lean_dec(v___y_2670_);
lean_dec_ref(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec(v___y_2665_);
lean_dec(v_upperBound_2657_);
return v_res_2673_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; 
v___x_2676_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2677_ = lean_unsigned_to_nat(18u);
v___x_2678_ = lean_unsigned_to_nat(1895u);
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2680_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2681_ = l_mkPanicMessageWithDecl(v___x_2680_, v___x_2679_, v___x_2678_, v___x_2677_, v___x_2676_);
return v___x_2681_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2682_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2683_);
lean_ctor_set(v___x_2684_, 1, v___x_2682_);
return v___x_2684_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2686_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
lean_ctor_set(v___x_2687_, 1, v___x_2685_);
return v___x_2687_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2688_; lean_object* v_dummy_2689_; 
v___x_2688_ = lean_box(0);
v_dummy_2689_ = l_Lean_Expr_sort___override(v___x_2688_);
return v_dummy_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2690_, lean_object* v_structName_2691_, lean_object* v_idx_2692_, lean_object* v_struct_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___y_2702_; lean_object* v___y_2703_; lean_object* v___y_2708_; uint8_t v___x_2712_; 
v___x_2712_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2694_);
if (v___x_2712_ == 0)
{
lean_dec(v_idx_2692_);
lean_dec(v_structName_2691_);
if (lean_obj_tag(v_e_2690_) == 11)
{
lean_object* v_expr_2713_; lean_object* v_typeName_2714_; lean_object* v_idx_2715_; lean_object* v_struct_2716_; size_t v___x_2717_; size_t v___x_2718_; uint8_t v___x_2719_; 
v_expr_2713_ = lean_ctor_get(v_struct_2693_, 0);
lean_inc_ref(v_expr_2713_);
lean_dec_ref(v_struct_2693_);
v_typeName_2714_ = lean_ctor_get(v_e_2690_, 0);
v_idx_2715_ = lean_ctor_get(v_e_2690_, 1);
v_struct_2716_ = lean_ctor_get(v_e_2690_, 2);
v___x_2717_ = lean_ptr_addr(v_struct_2716_);
v___x_2718_ = lean_ptr_addr(v_expr_2713_);
v___x_2719_ = lean_usize_dec_eq(v___x_2717_, v___x_2718_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
lean_inc(v_idx_2715_);
lean_inc(v_typeName_2714_);
lean_dec_ref_known(v_e_2690_, 3);
v___x_2720_ = l_Lean_Expr_proj___override(v_typeName_2714_, v_idx_2715_, v_expr_2713_);
v___y_2708_ = v___x_2720_;
goto v___jp_2707_;
}
else
{
lean_dec_ref(v_expr_2713_);
v___y_2708_ = v_e_2690_;
goto v___jp_2707_;
}
}
else
{
lean_object* v___x_2721_; lean_object* v___x_2722_; 
lean_dec_ref(v_struct_2693_);
lean_dec_ref(v_e_2690_);
v___x_2721_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2722_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2721_);
v___y_2708_ = v___x_2722_;
goto v___jp_2707_;
}
}
else
{
lean_object* v___x_2723_; 
lean_inc_ref(v_struct_2693_);
v___x_2723_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2693_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
lean_inc(v_a_2699_);
lean_inc_ref(v_a_2698_);
lean_inc(v_a_2697_);
lean_inc_ref(v_a_2696_);
v___x_2725_ = lean_whnf(v_a_2724_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc_n(v_a_2726_, 2);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = l_Lean_Meta_isProp(v_a_2726_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
if (lean_obj_tag(v___x_2727_) == 0)
{
lean_object* v_a_2728_; lean_object* v___x_2729_; 
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_a_2728_);
lean_dec_ref_known(v___x_2727_, 1);
v___x_2729_ = l_Lean_Expr_getAppFn(v_a_2726_);
if (lean_obj_tag(v___x_2729_) == 4)
{
lean_object* v_declName_2730_; lean_object* v_us_2731_; lean_object* v___x_2732_; lean_object* v_env_2736_; uint8_t v___x_2737_; lean_object* v___x_2738_; 
v_declName_2730_ = lean_ctor_get(v___x_2729_, 0);
lean_inc(v_declName_2730_);
v_us_2731_ = lean_ctor_get(v___x_2729_, 1);
lean_inc(v_us_2731_);
lean_dec_ref_known(v___x_2729_, 2);
v___x_2732_ = lean_st_ref_get(v_a_2699_);
v_env_2736_ = lean_ctor_get(v___x_2732_, 0);
lean_inc_ref(v_env_2736_);
lean_dec(v___x_2732_);
v___x_2737_ = 0;
v___x_2738_ = l_Lean_Environment_find_x3f(v_env_2736_, v_declName_2730_, v___x_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v___x_2739_; lean_object* v___x_2740_; 
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
v___x_2739_ = lean_box(0);
v___x_2740_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2693_, v_structName_2691_, v_idx_2692_, v_a_2726_, lean_box(0), v___x_2739_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
return v___x_2740_;
}
else
{
lean_object* v_val_2741_; 
v_val_2741_ = lean_ctor_get(v___x_2738_, 0);
lean_inc(v_val_2741_);
lean_dec_ref_known(v___x_2738_, 1);
if (lean_obj_tag(v_val_2741_) == 5)
{
lean_object* v_val_2742_; lean_object* v_ctors_2743_; 
v_val_2742_ = lean_ctor_get(v_val_2741_, 0);
lean_inc_ref(v_val_2742_);
lean_dec_ref_known(v_val_2741_, 1);
v_ctors_2743_ = lean_ctor_get(v_val_2742_, 4);
lean_inc(v_ctors_2743_);
if (lean_obj_tag(v_ctors_2743_) == 1)
{
lean_object* v_tail_2744_; 
v_tail_2744_ = lean_ctor_get(v_ctors_2743_, 1);
if (lean_obj_tag(v_tail_2744_) == 0)
{
lean_object* v_toConstantVal_2745_; lean_object* v_numParams_2746_; lean_object* v_numIndices_2747_; lean_object* v_head_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2857_; 
v_toConstantVal_2745_ = lean_ctor_get(v_val_2742_, 0);
lean_inc_ref(v_toConstantVal_2745_);
v_numParams_2746_ = lean_ctor_get(v_val_2742_, 1);
lean_inc(v_numParams_2746_);
v_numIndices_2747_ = lean_ctor_get(v_val_2742_, 2);
lean_inc(v_numIndices_2747_);
lean_dec_ref(v_val_2742_);
v_head_2748_ = lean_ctor_get(v_ctors_2743_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_ctors_2743_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; 
v_unused_2858_ = lean_ctor_get(v_ctors_2743_, 1);
lean_dec(v_unused_2858_);
v___x_2750_ = v_ctors_2743_;
v_isShared_2751_ = v_isSharedCheck_2857_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_head_2748_);
lean_dec(v_ctors_2743_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2857_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; 
v___x_2752_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2748_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; 
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
if (lean_obj_tag(v_a_2753_) == 6)
{
lean_object* v_val_2754_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v_name_2835_; uint8_t v___x_2836_; 
v_val_2754_ = lean_ctor_get(v_a_2753_, 0);
lean_inc_ref(v_val_2754_);
lean_dec_ref_known(v_a_2753_, 1);
v_name_2835_ = lean_ctor_get(v_toConstantVal_2745_, 0);
lean_inc(v_name_2835_);
lean_dec_ref(v_toConstantVal_2745_);
v___x_2836_ = lean_name_eq(v_name_2835_, v_structName_2691_);
lean_dec(v_name_2835_);
if (v___x_2836_ == 0)
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_dec_ref(v_val_2754_);
lean_del_object(v___x_2750_);
lean_dec(v_numIndices_2747_);
lean_dec(v_numParams_2746_);
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
v___x_2837_ = lean_box(0);
v___x_2838_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2693_, v_structName_2691_, v_idx_2692_, v_a_2726_, lean_box(0), v___x_2837_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
v___y_2810_ = v_a_2694_;
v___y_2811_ = v_a_2695_;
v___y_2812_ = v_a_2696_;
v___y_2813_ = v_a_2697_;
v___y_2814_ = v_a_2698_;
v___y_2815_ = v_a_2699_;
goto v___jp_2809_;
}
v___jp_2755_:
{
lean_object* v_toConstantVal_2763_; lean_object* v_name_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v_toConstantVal_2763_ = lean_ctor_get(v_val_2754_, 0);
lean_inc_ref(v_toConstantVal_2763_);
lean_dec_ref(v_val_2754_);
v_name_2764_ = lean_ctor_get(v_toConstantVal_2763_, 0);
lean_inc(v_name_2764_);
lean_dec_ref(v_toConstantVal_2763_);
v___x_2765_ = l_Lean_mkConst(v_name_2764_, v_us_2731_);
v___x_2766_ = lean_unsigned_to_nat(0u);
v___x_2767_ = l_Array_toSubarray___redArg(v___y_2756_, v___x_2766_, v_numParams_2746_);
v___x_2768_ = l_Subarray_copy___redArg(v___x_2767_);
v___x_2769_ = l_Lean_mkAppN(v___x_2765_, v___x_2768_);
lean_dec_ref(v___x_2768_);
lean_inc(v___y_2762_);
lean_inc_ref(v___y_2761_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
v___x_2770_ = lean_infer_type(v___x_2769_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2751_ == 0)
{
lean_ctor_set_tag(v___x_2750_, 0);
lean_ctor_set(v___x_2750_, 1, v___x_2772_);
lean_ctor_set(v___x_2750_, 0, v_a_2771_);
v___x_2774_ = v___x_2750_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2771_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
uint8_t v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = lean_unbox(v_a_2728_);
lean_dec(v_a_2728_);
lean_inc_ref(v_struct_2693_);
lean_inc(v_idx_2692_);
v___x_2776_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2692_, v_struct_2693_, v_structName_2691_, v___x_2775_, v_idx_2692_, v_a_2726_, v___x_2766_, v___x_2774_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v_idx_2692_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v_snd_2778_; lean_object* v_snd_2779_; lean_object* v_snd_2780_; lean_object* v_expr_2781_; lean_object* v___x_2782_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v_snd_2778_ = lean_ctor_get(v_a_2777_, 1);
lean_inc(v_snd_2778_);
lean_dec(v_a_2777_);
v_snd_2779_ = lean_ctor_get(v_snd_2778_, 1);
lean_inc(v_snd_2779_);
lean_dec(v_snd_2778_);
v_snd_2780_ = lean_ctor_get(v_snd_2779_, 1);
lean_inc(v_snd_2780_);
lean_dec(v_snd_2779_);
v_expr_2781_ = lean_ctor_get(v_struct_2693_, 0);
lean_inc_ref(v_expr_2781_);
lean_dec_ref(v_struct_2693_);
v___x_2782_ = l_Lean_Expr_cleanupAnnotations(v_snd_2780_);
if (lean_obj_tag(v_e_2690_) == 11)
{
lean_object* v_typeName_2783_; lean_object* v_idx_2784_; lean_object* v_struct_2785_; size_t v___x_2786_; size_t v___x_2787_; uint8_t v___x_2788_; 
v_typeName_2783_ = lean_ctor_get(v_e_2690_, 0);
v_idx_2784_ = lean_ctor_get(v_e_2690_, 1);
v_struct_2785_ = lean_ctor_get(v_e_2690_, 2);
v___x_2786_ = lean_ptr_addr(v_struct_2785_);
v___x_2787_ = lean_ptr_addr(v_expr_2781_);
v___x_2788_ = lean_usize_dec_eq(v___x_2786_, v___x_2787_);
if (v___x_2788_ == 0)
{
lean_object* v___x_2789_; 
lean_inc(v_idx_2784_);
lean_inc(v_typeName_2783_);
lean_dec_ref_known(v_e_2690_, 3);
v___x_2789_ = l_Lean_Expr_proj___override(v_typeName_2783_, v_idx_2784_, v_expr_2781_);
v___y_2702_ = v___x_2782_;
v___y_2703_ = v___x_2789_;
goto v___jp_2701_;
}
else
{
lean_dec_ref(v_expr_2781_);
v___y_2702_ = v___x_2782_;
v___y_2703_ = v_e_2690_;
goto v___jp_2701_;
}
}
else
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
lean_dec_ref(v_expr_2781_);
lean_dec_ref(v_e_2690_);
v___x_2790_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2791_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2790_);
v___y_2702_ = v___x_2782_;
v___y_2703_ = v___x_2791_;
goto v___jp_2701_;
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_dec_ref(v_struct_2693_);
lean_dec_ref(v_e_2690_);
v_a_2792_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2776_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2776_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_del_object(v___x_2750_);
lean_dec(v_a_2728_);
lean_dec(v_a_2726_);
lean_dec_ref(v_struct_2693_);
lean_dec(v_idx_2692_);
lean_dec(v_structName_2691_);
lean_dec_ref(v_e_2690_);
v_a_2801_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2770_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2770_);
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
v___jp_2809_:
{
lean_object* v_dummy_2816_; lean_object* v_nargs_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; 
v_dummy_2816_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2817_ = l_Lean_Expr_getAppNumArgs(v_a_2726_);
lean_inc(v_nargs_2817_);
v___x_2818_ = lean_mk_array(v_nargs_2817_, v_dummy_2816_);
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_nat_sub(v_nargs_2817_, v___x_2819_);
lean_dec(v_nargs_2817_);
lean_inc(v_a_2726_);
v___x_2821_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2726_, v___x_2818_, v___x_2820_);
v___x_2822_ = lean_nat_add(v_numParams_2746_, v_numIndices_2747_);
lean_dec(v_numIndices_2747_);
v___x_2823_ = lean_array_get_size(v___x_2821_);
v___x_2824_ = lean_nat_dec_eq(v___x_2822_, v___x_2823_);
lean_dec(v___x_2822_);
if (v___x_2824_ == 0)
{
if (v___x_2712_ == 0)
{
v___y_2756_ = v___x_2821_;
v___y_2757_ = v___y_2810_;
v___y_2758_ = v___y_2811_;
v___y_2759_ = v___y_2812_;
v___y_2760_ = v___y_2813_;
v___y_2761_ = v___y_2814_;
v___y_2762_ = v___y_2815_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_dec_ref(v___x_2821_);
lean_dec_ref(v_val_2754_);
lean_del_object(v___x_2750_);
lean_dec(v_numParams_2746_);
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
v___x_2825_ = lean_box(0);
v___x_2826_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2693_, v_structName_2691_, v_idx_2692_, v_a_2726_, lean_box(0), v___x_2825_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2826_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2826_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
v___y_2756_ = v___x_2821_;
v___y_2757_ = v___y_2810_;
v___y_2758_ = v___y_2811_;
v___y_2759_ = v___y_2812_;
v___y_2760_ = v___y_2813_;
v___y_2761_ = v___y_2814_;
v___y_2762_ = v___y_2815_;
goto v___jp_2755_;
}
}
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
lean_dec(v_a_2753_);
lean_del_object(v___x_2750_);
lean_dec(v_numIndices_2747_);
lean_dec(v_numParams_2746_);
lean_dec_ref(v_toConstantVal_2745_);
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
v___x_2847_ = lean_box(0);
v___x_2848_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2693_, v_structName_2691_, v_idx_2692_, v_a_2726_, lean_box(0), v___x_2847_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
return v___x_2848_;
}
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_del_object(v___x_2750_);
lean_dec(v_numIndices_2747_);
lean_dec(v_numParams_2746_);
lean_dec_ref(v_toConstantVal_2745_);
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec(v_a_2726_);
lean_dec_ref(v_struct_2693_);
lean_dec(v_idx_2692_);
lean_dec(v_structName_2691_);
lean_dec_ref(v_e_2690_);
v_a_2849_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2752_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2752_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2743_, 2);
lean_dec_ref(v_val_2742_);
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
goto v___jp_2733_;
}
}
else
{
lean_dec(v_ctors_2743_);
lean_dec_ref(v_val_2742_);
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
goto v___jp_2733_;
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_dec(v_val_2741_);
lean_dec(v_us_2731_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
v___x_2859_ = lean_box(0);
v___x_2860_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2693_, v_structName_2691_, v_idx_2692_, v_a_2726_, lean_box(0), v___x_2859_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
return v___x_2860_;
}
}
v___jp_2733_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2734_ = lean_box(0);
v___x_2735_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2693_, v_structName_2691_, v_idx_2692_, v_a_2726_, lean_box(0), v___x_2734_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
return v___x_2735_;
}
}
else
{
lean_object* v___x_2861_; lean_object* v___x_2862_; 
lean_dec_ref(v___x_2729_);
lean_dec(v_a_2728_);
lean_dec_ref(v_e_2690_);
v___x_2861_ = lean_box(0);
v___x_2862_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2693_, v_structName_2691_, v_idx_2692_, v_a_2726_, lean_box(0), v___x_2861_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_, v_a_2699_);
return v___x_2862_;
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2726_);
lean_dec_ref(v_struct_2693_);
lean_dec(v_idx_2692_);
lean_dec(v_structName_2691_);
lean_dec_ref(v_e_2690_);
v_a_2863_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2727_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2727_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v_struct_2693_);
lean_dec(v_idx_2692_);
lean_dec(v_structName_2691_);
lean_dec_ref(v_e_2690_);
v_a_2871_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2725_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2725_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec_ref(v_struct_2693_);
lean_dec(v_idx_2692_);
lean_dec(v_structName_2691_);
lean_dec_ref(v_e_2690_);
v_a_2879_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2723_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2723_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
v___jp_2701_:
{
lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___y_2702_);
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___y_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2705_);
return v___x_2706_;
}
v___jp_2707_:
{
lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v___x_2709_ = lean_box(0);
v___x_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___y_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
return v___x_2711_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2887_, lean_object* v_structName_2888_, lean_object* v_idx_2889_, lean_object* v_struct_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v_res_2898_; 
v_res_2898_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2887_, v_structName_2888_, v_idx_2889_, v_struct_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_, v_a_2895_, v_a_2896_);
lean_dec(v_a_2896_);
lean_dec_ref(v_a_2895_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec(v_a_2891_);
return v_res_2898_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2899_, lean_object* v_struct_2900_, lean_object* v_structName_2901_, uint8_t v_a_2902_, lean_object* v_idx_2903_, lean_object* v_a_2904_, lean_object* v_inst_2905_, lean_object* v_R_2906_, lean_object* v_a_2907_, lean_object* v_b_2908_, lean_object* v_c_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v___x_2917_; 
v___x_2917_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2899_, v_struct_2900_, v_structName_2901_, v_a_2902_, v_idx_2903_, v_a_2904_, v_a_2907_, v_b_2908_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_, v___y_2915_);
return v___x_2917_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2918_ = _args[0];
lean_object* v_struct_2919_ = _args[1];
lean_object* v_structName_2920_ = _args[2];
lean_object* v_a_2921_ = _args[3];
lean_object* v_idx_2922_ = _args[4];
lean_object* v_a_2923_ = _args[5];
lean_object* v_inst_2924_ = _args[6];
lean_object* v_R_2925_ = _args[7];
lean_object* v_a_2926_ = _args[8];
lean_object* v_b_2927_ = _args[9];
lean_object* v_c_2928_ = _args[10];
lean_object* v___y_2929_ = _args[11];
lean_object* v___y_2930_ = _args[12];
lean_object* v___y_2931_ = _args[13];
lean_object* v___y_2932_ = _args[14];
lean_object* v___y_2933_ = _args[15];
lean_object* v___y_2934_ = _args[16];
lean_object* v___y_2935_ = _args[17];
_start:
{
uint8_t v_a_19716__boxed_2936_; lean_object* v_res_2937_; 
v_a_19716__boxed_2936_ = lean_unbox(v_a_2921_);
v_res_2937_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2918_, v_struct_2919_, v_structName_2920_, v_a_19716__boxed_2936_, v_idx_2922_, v_a_2923_, v_inst_2924_, v_R_2925_, v_a_2926_, v_b_2927_, v_c_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec(v___y_2929_);
lean_dec(v_upperBound_2918_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2938_, size_t v_i_2939_, size_t v_stop_2940_, lean_object* v_b_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
uint8_t v___x_2948_; 
v___x_2948_ = lean_usize_dec_eq(v_i_2939_, v_stop_2940_);
if (v___x_2948_ == 0)
{
size_t v___x_2949_; size_t v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2949_ = ((size_t)1ULL);
v___x_2950_ = lean_usize_sub(v_i_2939_, v___x_2949_);
v___x_2951_ = lean_array_uget_borrowed(v_as_2938_, v___x_2950_);
lean_inc(v___x_2951_);
v___x_2952_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2951_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_, v___y_2946_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v___x_2954_ = l_Lean_Expr_sortLevel_x21(v_a_2953_);
lean_dec(v_a_2953_);
v___x_2955_ = l_Lean_mkLevelIMax_x27(v___x_2954_, v_b_2941_);
v_i_2939_ = v___x_2950_;
v_b_2941_ = v___x_2955_;
goto _start;
}
else
{
lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_b_2941_);
v_a_2957_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2952_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_dec(v___x_2952_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2965_, 0, v_b_2941_);
return v___x_2965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_2966_, lean_object* v_i_2967_, lean_object* v_stop_2968_, lean_object* v_b_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_){
_start:
{
size_t v_i_boxed_2976_; size_t v_stop_boxed_2977_; lean_object* v_res_2978_; 
v_i_boxed_2976_ = lean_unbox_usize(v_i_2967_);
lean_dec(v_i_2967_);
v_stop_boxed_2977_ = lean_unbox_usize(v_stop_2968_);
lean_dec(v_stop_2968_);
v_res_2978_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_2966_, v_i_boxed_2976_, v_stop_boxed_2977_, v_b_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
lean_dec(v___y_2974_);
lean_dec_ref(v___y_2973_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v_as_2966_);
return v_res_2978_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v___x_2982_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_2983_ = lean_unsigned_to_nat(14u);
v___x_2984_ = lean_unsigned_to_nat(22u);
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_2986_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_2987_ = l_mkPanicMessageWithDecl(v___x_2986_, v___x_2985_, v___x_2984_, v___x_2983_, v___x_2982_);
return v___x_2987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_2988_, lean_object* v_doms_2989_, lean_object* v_body_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_lctx_2998_; lean_object* v_expr_2999_; uint8_t v___x_3000_; uint8_t v___x_3001_; lean_object* v___x_3002_; lean_object* v_a_3004_; uint8_t v___x_3009_; 
v_lctx_2998_ = lean_ctor_get(v_a_2993_, 2);
v_expr_2999_ = lean_ctor_get(v_body_2990_, 0);
v___x_3000_ = 1;
v___x_3001_ = 0;
lean_inc_ref(v_lctx_2998_);
v___x_3002_ = l_Lean_LocalContext_mkForall(v_lctx_2998_, v_fvars_2988_, v_expr_2999_, v___x_3000_, v___x_3001_);
v___x_3009_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2991_);
if (v___x_3009_ == 0)
{
lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3018_; 
v_isSharedCheck_3018_ = !lean_is_exclusive(v_body_2990_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; lean_object* v_unused_3020_; 
v_unused_3019_ = lean_ctor_get(v_body_2990_, 1);
lean_dec(v_unused_3019_);
v_unused_3020_ = lean_ctor_get(v_body_2990_, 0);
lean_dec(v_unused_3020_);
v___x_3011_ = v_body_2990_;
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
else
{
lean_dec(v_body_2990_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; 
v___x_3013_ = lean_box(0);
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v___x_3013_);
lean_ctor_set(v___x_3011_, 0, v___x_3002_);
v___x_3015_ = v___x_3011_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3017_, 1, v___x_3013_);
v___x_3015_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3016_, 0, v___x_3015_);
return v___x_3016_;
}
}
}
else
{
lean_object* v___x_3021_; 
v___x_3021_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___y_3024_; lean_object* v_type_x3f_3041_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v_type_x3f_3041_ = lean_ctor_get(v_a_3022_, 1);
lean_inc(v_type_x3f_3041_);
lean_dec(v_a_3022_);
if (lean_obj_tag(v_type_x3f_3041_) == 0)
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3043_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3042_);
v___y_3024_ = v___x_3043_;
goto v___jp_3023_;
}
else
{
lean_object* v_val_3044_; 
v_val_3044_ = lean_ctor_get(v_type_x3f_3041_, 0);
lean_inc(v_val_3044_);
lean_dec_ref_known(v_type_x3f_3041_, 1);
v___y_3024_ = v_val_3044_;
goto v___jp_3023_;
}
v___jp_3023_:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3025_ = l_Lean_Expr_sortLevel_x21(v___y_3024_);
lean_dec_ref(v___y_3024_);
v___x_3026_ = lean_array_get_size(v_doms_2989_);
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = lean_nat_dec_lt(v___x_3027_, v___x_3026_);
if (v___x_3028_ == 0)
{
v_a_3004_ = v___x_3025_;
goto v___jp_3003_;
}
else
{
size_t v___x_3029_; size_t v___x_3030_; lean_object* v___x_3031_; 
v___x_3029_ = lean_usize_of_nat(v___x_3026_);
v___x_3030_ = ((size_t)0ULL);
v___x_3031_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_2989_, v___x_3029_, v___x_3030_, v___x_3025_, v_a_2992_, v_a_2993_, v_a_2994_, v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_3031_) == 0)
{
lean_object* v_a_3032_; 
v_a_3032_ = lean_ctor_get(v___x_3031_, 0);
lean_inc(v_a_3032_);
lean_dec_ref_known(v___x_3031_, 1);
v_a_3004_ = v_a_3032_;
goto v___jp_3003_;
}
else
{
lean_object* v_a_3033_; lean_object* v___x_3035_; uint8_t v_isShared_3036_; uint8_t v_isSharedCheck_3040_; 
lean_dec_ref(v___x_3002_);
v_a_3033_ = lean_ctor_get(v___x_3031_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_3035_ = v___x_3031_;
v_isShared_3036_ = v_isSharedCheck_3040_;
goto v_resetjp_3034_;
}
else
{
lean_inc(v_a_3033_);
lean_dec(v___x_3031_);
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
}
else
{
lean_dec_ref(v___x_3002_);
return v___x_3021_;
}
}
v___jp_3003_:
{
lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; 
v___x_3005_ = l_Lean_Expr_sort___override(v_a_3004_);
v___x_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
v___x_3007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3002_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
v___x_3008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3007_);
return v___x_3008_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3045_, lean_object* v_doms_3046_, lean_object* v_body_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_){
_start:
{
lean_object* v_res_3055_; 
v_res_3055_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3045_, v_doms_3046_, v_body_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_);
lean_dec(v_a_3053_);
lean_dec_ref(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec(v_a_3048_);
lean_dec_ref(v_doms_3046_);
lean_dec_ref(v_fvars_3045_);
return v_res_3055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3056_, size_t v_i_3057_, size_t v_stop_3058_, lean_object* v_b_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_){
_start:
{
lean_object* v___x_3067_; 
v___x_3067_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3056_, v_i_3057_, v_stop_3058_, v_b_3059_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_);
return v___x_3067_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3068_, lean_object* v_i_3069_, lean_object* v_stop_3070_, lean_object* v_b_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
size_t v_i_boxed_3079_; size_t v_stop_boxed_3080_; lean_object* v_res_3081_; 
v_i_boxed_3079_ = lean_unbox_usize(v_i_3069_);
lean_dec(v_i_3069_);
v_stop_boxed_3080_ = lean_unbox_usize(v_stop_3070_);
lean_dec(v_stop_3070_);
v_res_3081_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3068_, v_i_boxed_3079_, v_stop_boxed_3080_, v_b_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec(v___y_3072_);
lean_dec_ref(v_as_3068_);
return v_res_3081_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3082_, lean_object* v_opt_3083_){
_start:
{
lean_object* v_name_3084_; lean_object* v_defValue_3085_; lean_object* v_map_3086_; lean_object* v___x_3087_; 
v_name_3084_ = lean_ctor_get(v_opt_3083_, 0);
v_defValue_3085_ = lean_ctor_get(v_opt_3083_, 1);
v_map_3086_ = lean_ctor_get(v_opts_3082_, 0);
v___x_3087_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3086_, v_name_3084_);
if (lean_obj_tag(v___x_3087_) == 0)
{
uint8_t v___x_3088_; 
v___x_3088_ = lean_unbox(v_defValue_3085_);
return v___x_3088_;
}
else
{
lean_object* v_val_3089_; 
v_val_3089_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_val_3089_);
lean_dec_ref_known(v___x_3087_, 1);
if (lean_obj_tag(v_val_3089_) == 1)
{
uint8_t v_v_3090_; 
v_v_3090_ = lean_ctor_get_uint8(v_val_3089_, 0);
lean_dec_ref_known(v_val_3089_, 0);
return v_v_3090_;
}
else
{
uint8_t v___x_3091_; 
lean_dec(v_val_3089_);
v___x_3091_ = lean_unbox(v_defValue_3085_);
return v___x_3091_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3092_, lean_object* v_opt_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3092_, v_opt_3093_);
lean_dec_ref(v_opt_3093_);
lean_dec_ref(v_opts_3092_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3096_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v_a_3098_; lean_object* v___x_3100_; uint8_t v_isShared_3101_; uint8_t v_isSharedCheck_3105_; 
v_a_3098_ = lean_ctor_get(v_x_3096_, 0);
v_isSharedCheck_3105_ = !lean_is_exclusive(v_x_3096_);
if (v_isSharedCheck_3105_ == 0)
{
v___x_3100_ = v_x_3096_;
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
else
{
lean_inc(v_a_3098_);
lean_dec(v_x_3096_);
v___x_3100_ = lean_box(0);
v_isShared_3101_ = v_isSharedCheck_3105_;
goto v_resetjp_3099_;
}
v_resetjp_3099_:
{
lean_object* v___x_3103_; 
if (v_isShared_3101_ == 0)
{
lean_ctor_set_tag(v___x_3100_, 1);
v___x_3103_ = v___x_3100_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_a_3098_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3113_; 
v_a_3106_ = lean_ctor_get(v_x_3096_, 0);
v_isSharedCheck_3113_ = !lean_is_exclusive(v_x_3096_);
if (v_isSharedCheck_3113_ == 0)
{
v___x_3108_ = v_x_3096_;
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v_x_3096_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3113_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v___x_3111_; 
if (v_isShared_3109_ == 0)
{
lean_ctor_set_tag(v___x_3108_, 0);
v___x_3111_ = v___x_3108_;
goto v_reusejp_3110_;
}
else
{
lean_object* v_reuseFailAlloc_3112_; 
v_reuseFailAlloc_3112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3112_, 0, v_a_3106_);
v___x_3111_ = v_reuseFailAlloc_3112_;
goto v_reusejp_3110_;
}
v_reusejp_3110_:
{
return v___x_3111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v_res_3116_; 
v_res_3116_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3114_);
return v_res_3116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3117_){
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
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3120_){
_start:
{
uint8_t v_res_3121_; lean_object* v_r_3122_; 
v_res_3121_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3120_);
lean_dec_ref(v_e_3120_);
v_r_3122_ = lean_box(v_res_3121_);
return v_r_3122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3123_, lean_object* v_opt_3124_){
_start:
{
lean_object* v_name_3125_; lean_object* v_defValue_3126_; lean_object* v_map_3127_; lean_object* v___x_3128_; 
v_name_3125_ = lean_ctor_get(v_opt_3124_, 0);
v_defValue_3126_ = lean_ctor_get(v_opt_3124_, 1);
v_map_3127_ = lean_ctor_get(v_opts_3123_, 0);
v___x_3128_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3127_, v_name_3125_);
if (lean_obj_tag(v___x_3128_) == 0)
{
lean_inc(v_defValue_3126_);
return v_defValue_3126_;
}
else
{
lean_object* v_val_3129_; 
v_val_3129_ = lean_ctor_get(v___x_3128_, 0);
lean_inc(v_val_3129_);
lean_dec_ref_known(v___x_3128_, 1);
if (lean_obj_tag(v_val_3129_) == 3)
{
lean_object* v_v_3130_; 
v_v_3130_ = lean_ctor_get(v_val_3129_, 0);
lean_inc(v_v_3130_);
lean_dec_ref_known(v_val_3129_, 1);
return v_v_3130_;
}
else
{
lean_dec(v_val_3129_);
lean_inc(v_defValue_3126_);
return v_defValue_3126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3131_, lean_object* v_opt_3132_){
_start:
{
lean_object* v_res_3133_; 
v_res_3133_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3131_, v_opt_3132_);
lean_dec_ref(v_opt_3132_);
lean_dec_ref(v_opts_3131_);
return v_res_3133_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3134_, size_t v_i_3135_, lean_object* v_bs_3136_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3146_, lean_object* v_i_3147_, lean_object* v_bs_3148_){
_start:
{
size_t v_sz_boxed_3149_; size_t v_i_boxed_3150_; lean_object* v_res_3151_; 
v_sz_boxed_3149_ = lean_unbox_usize(v_sz_3146_);
lean_dec(v_sz_3146_);
v_i_boxed_3150_ = lean_unbox_usize(v_i_3147_);
lean_dec(v_i_3147_);
v_res_3151_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3149_, v_i_boxed_3150_, v_bs_3148_);
return v_res_3151_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3152_, lean_object* v_data_3153_, lean_object* v_ref_3154_, lean_object* v_msg_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_){
_start:
{
lean_object* v_toCold_3161_; lean_object* v_currRecDepth_3162_; lean_object* v_ref_3163_; uint16_t v_optionFlags_3164_; uint8_t v_suppressElabErrors_3165_; uint8_t v_isRecordingDeps_3166_; lean_object* v_ref_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v_traceState_3170_; lean_object* v_traces_3171_; lean_object* v___x_3172_; size_t v_sz_3173_; size_t v___x_3174_; lean_object* v___x_3175_; lean_object* v_msg_3176_; lean_object* v___x_3177_; lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3216_; 
v_toCold_3161_ = lean_ctor_get(v___y_3158_, 0);
v_currRecDepth_3162_ = lean_ctor_get(v___y_3158_, 1);
v_ref_3163_ = lean_ctor_get(v___y_3158_, 2);
v_optionFlags_3164_ = lean_ctor_get_uint16(v___y_3158_, sizeof(void*)*3);
v_suppressElabErrors_3165_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*3 + 2);
v_isRecordingDeps_3166_ = lean_ctor_get_uint8(v___y_3158_, sizeof(void*)*3 + 3);
v_ref_3167_ = l_Lean_replaceRef(v_ref_3154_, v_ref_3163_);
lean_inc(v_currRecDepth_3162_);
lean_inc_ref(v_toCold_3161_);
v___x_3168_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_3168_, 0, v_toCold_3161_);
lean_ctor_set(v___x_3168_, 1, v_currRecDepth_3162_);
lean_ctor_set(v___x_3168_, 2, v_ref_3167_);
lean_ctor_set_uint16(v___x_3168_, sizeof(void*)*3, v_optionFlags_3164_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*3 + 2, v_suppressElabErrors_3165_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*3 + 3, v_isRecordingDeps_3166_);
v___x_3169_ = lean_st_ref_get(v___y_3159_);
v_traceState_3170_ = lean_ctor_get(v___x_3169_, 4);
lean_inc_ref(v_traceState_3170_);
lean_dec(v___x_3169_);
v_traces_3171_ = lean_ctor_get(v_traceState_3170_, 0);
lean_inc_ref(v_traces_3171_);
lean_dec_ref(v_traceState_3170_);
v___x_3172_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3171_);
lean_dec_ref(v_traces_3171_);
v_sz_3173_ = lean_array_size(v___x_3172_);
v___x_3174_ = ((size_t)0ULL);
v___x_3175_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3173_, v___x_3174_, v___x_3172_);
v_msg_3176_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3176_, 0, v_data_3153_);
lean_ctor_set(v_msg_3176_, 1, v_msg_3155_);
lean_ctor_set(v_msg_3176_, 2, v___x_3175_);
v___x_3177_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3176_, v___y_3156_, v___y_3157_, v___x_3168_, v___y_3159_);
lean_dec_ref_known(v___x_3168_, 3);
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3216_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3216_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v_traceState_3183_; lean_object* v_env_3184_; lean_object* v_nextMacroScope_3185_; lean_object* v_ngen_3186_; lean_object* v_auxDeclNGen_3187_; lean_object* v_cache_3188_; lean_object* v_recordedDeps_3189_; lean_object* v_messages_3190_; lean_object* v_infoState_3191_; lean_object* v_snapshotTasks_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3215_; 
v___x_3182_ = lean_st_ref_take(v___y_3159_);
v_traceState_3183_ = lean_ctor_get(v___x_3182_, 4);
v_env_3184_ = lean_ctor_get(v___x_3182_, 0);
v_nextMacroScope_3185_ = lean_ctor_get(v___x_3182_, 1);
v_ngen_3186_ = lean_ctor_get(v___x_3182_, 2);
v_auxDeclNGen_3187_ = lean_ctor_get(v___x_3182_, 3);
v_cache_3188_ = lean_ctor_get(v___x_3182_, 5);
v_recordedDeps_3189_ = lean_ctor_get(v___x_3182_, 6);
v_messages_3190_ = lean_ctor_get(v___x_3182_, 7);
v_infoState_3191_ = lean_ctor_get(v___x_3182_, 8);
v_snapshotTasks_3192_ = lean_ctor_get(v___x_3182_, 9);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3194_ = v___x_3182_;
v_isShared_3195_ = v_isSharedCheck_3215_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_snapshotTasks_3192_);
lean_inc(v_infoState_3191_);
lean_inc(v_messages_3190_);
lean_inc(v_recordedDeps_3189_);
lean_inc(v_cache_3188_);
lean_inc(v_traceState_3183_);
lean_inc(v_auxDeclNGen_3187_);
lean_inc(v_ngen_3186_);
lean_inc(v_nextMacroScope_3185_);
lean_inc(v_env_3184_);
lean_dec(v___x_3182_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3215_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
uint64_t v_tid_3196_; lean_object* v___x_3198_; uint8_t v_isShared_3199_; uint8_t v_isSharedCheck_3213_; 
v_tid_3196_ = lean_ctor_get_uint64(v_traceState_3183_, sizeof(void*)*1);
v_isSharedCheck_3213_ = !lean_is_exclusive(v_traceState_3183_);
if (v_isSharedCheck_3213_ == 0)
{
lean_object* v_unused_3214_; 
v_unused_3214_ = lean_ctor_get(v_traceState_3183_, 0);
lean_dec(v_unused_3214_);
v___x_3198_ = v_traceState_3183_;
v_isShared_3199_ = v_isSharedCheck_3213_;
goto v_resetjp_3197_;
}
else
{
lean_dec(v_traceState_3183_);
v___x_3198_ = lean_box(0);
v_isShared_3199_ = v_isSharedCheck_3213_;
goto v_resetjp_3197_;
}
v_resetjp_3197_:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
v___x_3200_ = lean_box(0);
v___x_3201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3201_, 0, v_ref_3154_);
lean_ctor_set(v___x_3201_, 1, v_a_3178_);
v___x_3202_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3152_, v___x_3201_);
if (v_isShared_3199_ == 0)
{
lean_ctor_set(v___x_3198_, 0, v___x_3202_);
v___x_3204_ = v___x_3198_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v___x_3202_);
lean_ctor_set_uint64(v_reuseFailAlloc_3212_, sizeof(void*)*1, v_tid_3196_);
v___x_3204_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3206_; 
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 4, v___x_3204_);
v___x_3206_ = v___x_3194_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3211_; 
v_reuseFailAlloc_3211_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3211_, 0, v_env_3184_);
lean_ctor_set(v_reuseFailAlloc_3211_, 1, v_nextMacroScope_3185_);
lean_ctor_set(v_reuseFailAlloc_3211_, 2, v_ngen_3186_);
lean_ctor_set(v_reuseFailAlloc_3211_, 3, v_auxDeclNGen_3187_);
lean_ctor_set(v_reuseFailAlloc_3211_, 4, v___x_3204_);
lean_ctor_set(v_reuseFailAlloc_3211_, 5, v_cache_3188_);
lean_ctor_set(v_reuseFailAlloc_3211_, 6, v_recordedDeps_3189_);
lean_ctor_set(v_reuseFailAlloc_3211_, 7, v_messages_3190_);
lean_ctor_set(v_reuseFailAlloc_3211_, 8, v_infoState_3191_);
lean_ctor_set(v_reuseFailAlloc_3211_, 9, v_snapshotTasks_3192_);
v___x_3206_ = v_reuseFailAlloc_3211_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
lean_object* v___x_3207_; lean_object* v___x_3209_; 
v___x_3207_ = lean_st_ref_put(v___y_3159_, v___x_3206_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 0, v___x_3200_);
v___x_3209_ = v___x_3180_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v___x_3200_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3217_, lean_object* v_data_3218_, lean_object* v_ref_3219_, lean_object* v_msg_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_res_3226_; 
v_res_3226_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3217_, v_data_3218_, v_ref_3219_, v_msg_3220_, v___y_3221_, v___y_3222_, v___y_3223_, v___y_3224_);
lean_dec(v___y_3224_);
lean_dec_ref(v___y_3223_);
lean_dec(v___y_3222_);
lean_dec_ref(v___y_3221_);
return v_res_3226_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3229_ = l_Lean_stringToMessageData(v___x_3228_);
return v___x_3229_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3230_; double v___x_3231_; 
v___x_3230_ = lean_unsigned_to_nat(1000u);
v___x_3231_ = lean_float_of_nat(v___x_3230_);
return v___x_3231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3232_, uint8_t v_collapsed_3233_, lean_object* v_tag_3234_, lean_object* v_opts_3235_, uint8_t v_clsEnabled_3236_, lean_object* v_oldTraces_3237_, lean_object* v_msg_3238_, lean_object* v_resStartStop_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_fst_3247_; lean_object* v_snd_3248_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v_data_3252_; lean_object* v_fst_3263_; lean_object* v_snd_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; lean_object* v___y_3268_; lean_object* v_a_3269_; uint8_t v___y_3284_; double v___y_3316_; 
v_fst_3247_ = lean_ctor_get(v_resStartStop_3239_, 0);
lean_inc(v_fst_3247_);
v_snd_3248_ = lean_ctor_get(v_resStartStop_3239_, 1);
lean_inc(v_snd_3248_);
lean_dec_ref(v_resStartStop_3239_);
v_fst_3263_ = lean_ctor_get(v_snd_3248_, 0);
lean_inc(v_fst_3263_);
v_snd_3264_ = lean_ctor_get(v_snd_3248_, 1);
lean_inc(v_snd_3264_);
lean_dec(v_snd_3248_);
v___x_3265_ = l_Lean_trace_profiler;
v___x_3266_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3235_, v___x_3265_);
if (v___x_3266_ == 0)
{
v___y_3284_ = v___x_3266_;
goto v___jp_3283_;
}
else
{
lean_object* v___x_3321_; uint8_t v___x_3322_; 
v___x_3321_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3322_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3235_, v___x_3321_);
if (v___x_3322_ == 0)
{
lean_object* v___x_3323_; lean_object* v___x_3324_; double v___x_3325_; double v___x_3326_; double v___x_3327_; 
v___x_3323_ = l_Lean_trace_profiler_threshold;
v___x_3324_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3235_, v___x_3323_);
v___x_3325_ = lean_float_of_nat(v___x_3324_);
v___x_3326_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3327_ = lean_float_div(v___x_3325_, v___x_3326_);
v___y_3316_ = v___x_3327_;
goto v___jp_3315_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; double v___x_3330_; 
v___x_3328_ = l_Lean_trace_profiler_threshold;
v___x_3329_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3235_, v___x_3328_);
v___x_3330_ = lean_float_of_nat(v___x_3329_);
v___y_3316_ = v___x_3330_;
goto v___jp_3315_;
}
}
v___jp_3249_:
{
lean_object* v___x_3253_; 
lean_inc(v___y_3250_);
v___x_3253_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3237_, v_data_3252_, v___y_3250_, v___y_3251_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_);
if (lean_obj_tag(v___x_3253_) == 0)
{
lean_object* v___x_3254_; 
lean_dec_ref_known(v___x_3253_, 1);
v___x_3254_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3247_);
return v___x_3254_;
}
else
{
lean_object* v_a_3255_; lean_object* v___x_3257_; uint8_t v_isShared_3258_; uint8_t v_isSharedCheck_3262_; 
lean_dec(v_fst_3247_);
v_a_3255_ = lean_ctor_get(v___x_3253_, 0);
v_isSharedCheck_3262_ = !lean_is_exclusive(v___x_3253_);
if (v_isSharedCheck_3262_ == 0)
{
v___x_3257_ = v___x_3253_;
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
else
{
lean_inc(v_a_3255_);
lean_dec(v___x_3253_);
v___x_3257_ = lean_box(0);
v_isShared_3258_ = v_isSharedCheck_3262_;
goto v_resetjp_3256_;
}
v_resetjp_3256_:
{
lean_object* v___x_3260_; 
if (v_isShared_3258_ == 0)
{
v___x_3260_ = v___x_3257_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3261_; 
v_reuseFailAlloc_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3261_, 0, v_a_3255_);
v___x_3260_ = v_reuseFailAlloc_3261_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
return v___x_3260_;
}
}
}
}
v___jp_3267_:
{
uint8_t v_result_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; double v___x_3273_; lean_object* v_data_3274_; 
v_result_3270_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3247_);
v___x_3271_ = lean_box(v_result_3270_);
v___x_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
v___x_3273_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3234_);
lean_inc_ref(v___x_3272_);
lean_inc(v_cls_3232_);
v_data_3274_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3274_, 0, v_cls_3232_);
lean_ctor_set(v_data_3274_, 1, v___x_3272_);
lean_ctor_set(v_data_3274_, 2, v_tag_3234_);
lean_ctor_set_float(v_data_3274_, sizeof(void*)*3, v___x_3273_);
lean_ctor_set_float(v_data_3274_, sizeof(void*)*3 + 8, v___x_3273_);
lean_ctor_set_uint8(v_data_3274_, sizeof(void*)*3 + 16, v_collapsed_3233_);
if (v___x_3266_ == 0)
{
lean_dec_ref_known(v___x_3272_, 1);
lean_dec(v_snd_3264_);
lean_dec(v_fst_3263_);
lean_dec_ref(v_tag_3234_);
lean_dec(v_cls_3232_);
v___y_3250_ = v___y_3268_;
v___y_3251_ = v_a_3269_;
v_data_3252_ = v_data_3274_;
goto v___jp_3249_;
}
else
{
lean_object* v_data_3275_; double v___x_3276_; double v___x_3277_; 
lean_dec_ref_known(v_data_3274_, 3);
v_data_3275_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3275_, 0, v_cls_3232_);
lean_ctor_set(v_data_3275_, 1, v___x_3272_);
lean_ctor_set(v_data_3275_, 2, v_tag_3234_);
v___x_3276_ = lean_unbox_float(v_fst_3263_);
lean_dec(v_fst_3263_);
lean_ctor_set_float(v_data_3275_, sizeof(void*)*3, v___x_3276_);
v___x_3277_ = lean_unbox_float(v_snd_3264_);
lean_dec(v_snd_3264_);
lean_ctor_set_float(v_data_3275_, sizeof(void*)*3 + 8, v___x_3277_);
lean_ctor_set_uint8(v_data_3275_, sizeof(void*)*3 + 16, v_collapsed_3233_);
v___y_3250_ = v___y_3268_;
v___y_3251_ = v_a_3269_;
v_data_3252_ = v_data_3275_;
goto v___jp_3249_;
}
}
v___jp_3278_:
{
lean_object* v_ref_3279_; lean_object* v___x_3280_; 
v_ref_3279_ = lean_ctor_get(v___y_3244_, 2);
lean_inc(v___y_3245_);
lean_inc_ref(v___y_3244_);
lean_inc(v___y_3243_);
lean_inc_ref(v___y_3242_);
lean_inc(v___y_3241_);
lean_inc(v___y_3240_);
lean_inc(v_fst_3247_);
v___x_3280_ = lean_apply_8(v_msg_3238_, v_fst_3247_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_, v___y_3245_, lean_box(0));
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3280_, 1);
v___y_3268_ = v_ref_3279_;
v_a_3269_ = v_a_3281_;
goto v___jp_3267_;
}
else
{
lean_object* v___x_3282_; 
lean_dec_ref_known(v___x_3280_, 1);
v___x_3282_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3268_ = v_ref_3279_;
v_a_3269_ = v___x_3282_;
goto v___jp_3267_;
}
}
v___jp_3283_:
{
if (v_clsEnabled_3236_ == 0)
{
if (v___y_3284_ == 0)
{
lean_object* v___x_3285_; lean_object* v_traceState_3286_; lean_object* v_env_3287_; lean_object* v_nextMacroScope_3288_; lean_object* v_ngen_3289_; lean_object* v_auxDeclNGen_3290_; lean_object* v_cache_3291_; lean_object* v_recordedDeps_3292_; lean_object* v_messages_3293_; lean_object* v_infoState_3294_; lean_object* v_snapshotTasks_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v_snd_3264_);
lean_dec(v_fst_3263_);
lean_dec_ref(v_msg_3238_);
lean_dec_ref(v_tag_3234_);
lean_dec(v_cls_3232_);
v___x_3285_ = lean_st_ref_take(v___y_3245_);
v_traceState_3286_ = lean_ctor_get(v___x_3285_, 4);
v_env_3287_ = lean_ctor_get(v___x_3285_, 0);
v_nextMacroScope_3288_ = lean_ctor_get(v___x_3285_, 1);
v_ngen_3289_ = lean_ctor_get(v___x_3285_, 2);
v_auxDeclNGen_3290_ = lean_ctor_get(v___x_3285_, 3);
v_cache_3291_ = lean_ctor_get(v___x_3285_, 5);
v_recordedDeps_3292_ = lean_ctor_get(v___x_3285_, 6);
v_messages_3293_ = lean_ctor_get(v___x_3285_, 7);
v_infoState_3294_ = lean_ctor_get(v___x_3285_, 8);
v_snapshotTasks_3295_ = lean_ctor_get(v___x_3285_, 9);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3297_ = v___x_3285_;
v_isShared_3298_ = v_isSharedCheck_3314_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_snapshotTasks_3295_);
lean_inc(v_infoState_3294_);
lean_inc(v_messages_3293_);
lean_inc(v_recordedDeps_3292_);
lean_inc(v_cache_3291_);
lean_inc(v_traceState_3286_);
lean_inc(v_auxDeclNGen_3290_);
lean_inc(v_ngen_3289_);
lean_inc(v_nextMacroScope_3288_);
lean_inc(v_env_3287_);
lean_dec(v___x_3285_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3314_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
uint64_t v_tid_3299_; lean_object* v_traces_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3313_; 
v_tid_3299_ = lean_ctor_get_uint64(v_traceState_3286_, sizeof(void*)*1);
v_traces_3300_ = lean_ctor_get(v_traceState_3286_, 0);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_traceState_3286_);
if (v_isSharedCheck_3313_ == 0)
{
v___x_3302_ = v_traceState_3286_;
v_isShared_3303_ = v_isSharedCheck_3313_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_traces_3300_);
lean_dec(v_traceState_3286_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3313_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3304_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3237_, v_traces_3300_);
lean_dec_ref(v_traces_3300_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3304_);
v___x_3306_ = v___x_3302_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3304_);
lean_ctor_set_uint64(v_reuseFailAlloc_3312_, sizeof(void*)*1, v_tid_3299_);
v___x_3306_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3308_; 
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 4, v___x_3306_);
v___x_3308_ = v___x_3297_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_env_3287_);
lean_ctor_set(v_reuseFailAlloc_3311_, 1, v_nextMacroScope_3288_);
lean_ctor_set(v_reuseFailAlloc_3311_, 2, v_ngen_3289_);
lean_ctor_set(v_reuseFailAlloc_3311_, 3, v_auxDeclNGen_3290_);
lean_ctor_set(v_reuseFailAlloc_3311_, 4, v___x_3306_);
lean_ctor_set(v_reuseFailAlloc_3311_, 5, v_cache_3291_);
lean_ctor_set(v_reuseFailAlloc_3311_, 6, v_recordedDeps_3292_);
lean_ctor_set(v_reuseFailAlloc_3311_, 7, v_messages_3293_);
lean_ctor_set(v_reuseFailAlloc_3311_, 8, v_infoState_3294_);
lean_ctor_set(v_reuseFailAlloc_3311_, 9, v_snapshotTasks_3295_);
v___x_3308_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; 
v___x_3309_ = lean_st_ref_put(v___y_3245_, v___x_3308_);
v___x_3310_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3247_);
return v___x_3310_;
}
}
}
}
}
else
{
goto v___jp_3278_;
}
}
else
{
goto v___jp_3278_;
}
}
v___jp_3315_:
{
double v___x_3317_; double v___x_3318_; double v___x_3319_; uint8_t v___x_3320_; 
v___x_3317_ = lean_unbox_float(v_snd_3264_);
v___x_3318_ = lean_unbox_float(v_fst_3263_);
v___x_3319_ = lean_float_sub(v___x_3317_, v___x_3318_);
v___x_3320_ = lean_float_decLt(v___y_3316_, v___x_3319_);
v___y_3284_ = v___x_3320_;
goto v___jp_3283_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3331_, lean_object* v_collapsed_3332_, lean_object* v_tag_3333_, lean_object* v_opts_3334_, lean_object* v_clsEnabled_3335_, lean_object* v_oldTraces_3336_, lean_object* v_msg_3337_, lean_object* v_resStartStop_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
uint8_t v_collapsed_boxed_3346_; uint8_t v_clsEnabled_boxed_3347_; lean_object* v_res_3348_; 
v_collapsed_boxed_3346_ = lean_unbox(v_collapsed_3332_);
v_clsEnabled_boxed_3347_ = lean_unbox(v_clsEnabled_3335_);
v_res_3348_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3331_, v_collapsed_boxed_3346_, v_tag_3333_, v_opts_3334_, v_clsEnabled_boxed_3347_, v_oldTraces_3336_, v_msg_3337_, v_resStartStop_3338_, v___y_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_);
lean_dec(v___y_3344_);
lean_dec_ref(v___y_3343_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
lean_dec(v___y_3340_);
lean_dec(v___y_3339_);
lean_dec_ref(v_opts_3334_);
return v_res_3348_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3349_ = lean_unsigned_to_nat(32u);
v___x_3350_ = lean_mk_empty_array_with_capacity(v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
return v___x_3351_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3352_ = ((size_t)5ULL);
v___x_3353_ = lean_unsigned_to_nat(0u);
v___x_3354_ = lean_unsigned_to_nat(32u);
v___x_3355_ = lean_mk_empty_array_with_capacity(v___x_3354_);
v___x_3356_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3357_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3357_, 0, v___x_3356_);
lean_ctor_set(v___x_3357_, 1, v___x_3355_);
lean_ctor_set(v___x_3357_, 2, v___x_3353_);
lean_ctor_set(v___x_3357_, 3, v___x_3353_);
lean_ctor_set_usize(v___x_3357_, 4, v___x_3352_);
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3358_){
_start:
{
lean_object* v___x_3360_; lean_object* v_traceState_3361_; lean_object* v_traces_3362_; lean_object* v___x_3363_; lean_object* v_traceState_3364_; lean_object* v_env_3365_; lean_object* v_nextMacroScope_3366_; lean_object* v_ngen_3367_; lean_object* v_auxDeclNGen_3368_; lean_object* v_cache_3369_; lean_object* v_recordedDeps_3370_; lean_object* v_messages_3371_; lean_object* v_infoState_3372_; lean_object* v_snapshotTasks_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3392_; 
v___x_3360_ = lean_st_ref_get(v___y_3358_);
v_traceState_3361_ = lean_ctor_get(v___x_3360_, 4);
lean_inc_ref(v_traceState_3361_);
lean_dec(v___x_3360_);
v_traces_3362_ = lean_ctor_get(v_traceState_3361_, 0);
lean_inc_ref(v_traces_3362_);
lean_dec_ref(v_traceState_3361_);
v___x_3363_ = lean_st_ref_take(v___y_3358_);
v_traceState_3364_ = lean_ctor_get(v___x_3363_, 4);
v_env_3365_ = lean_ctor_get(v___x_3363_, 0);
v_nextMacroScope_3366_ = lean_ctor_get(v___x_3363_, 1);
v_ngen_3367_ = lean_ctor_get(v___x_3363_, 2);
v_auxDeclNGen_3368_ = lean_ctor_get(v___x_3363_, 3);
v_cache_3369_ = lean_ctor_get(v___x_3363_, 5);
v_recordedDeps_3370_ = lean_ctor_get(v___x_3363_, 6);
v_messages_3371_ = lean_ctor_get(v___x_3363_, 7);
v_infoState_3372_ = lean_ctor_get(v___x_3363_, 8);
v_snapshotTasks_3373_ = lean_ctor_get(v___x_3363_, 9);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3375_ = v___x_3363_;
v_isShared_3376_ = v_isSharedCheck_3392_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_snapshotTasks_3373_);
lean_inc(v_infoState_3372_);
lean_inc(v_messages_3371_);
lean_inc(v_recordedDeps_3370_);
lean_inc(v_cache_3369_);
lean_inc(v_traceState_3364_);
lean_inc(v_auxDeclNGen_3368_);
lean_inc(v_ngen_3367_);
lean_inc(v_nextMacroScope_3366_);
lean_inc(v_env_3365_);
lean_dec(v___x_3363_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3392_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
uint64_t v_tid_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3390_; 
v_tid_3377_ = lean_ctor_get_uint64(v_traceState_3364_, sizeof(void*)*1);
v_isSharedCheck_3390_ = !lean_is_exclusive(v_traceState_3364_);
if (v_isSharedCheck_3390_ == 0)
{
lean_object* v_unused_3391_; 
v_unused_3391_ = lean_ctor_get(v_traceState_3364_, 0);
lean_dec(v_unused_3391_);
v___x_3379_ = v_traceState_3364_;
v_isShared_3380_ = v_isSharedCheck_3390_;
goto v_resetjp_3378_;
}
else
{
lean_dec(v_traceState_3364_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3390_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3381_; lean_object* v___x_3383_; 
v___x_3381_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3380_ == 0)
{
lean_ctor_set(v___x_3379_, 0, v___x_3381_);
v___x_3383_ = v___x_3379_;
goto v_reusejp_3382_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3381_);
lean_ctor_set_uint64(v_reuseFailAlloc_3389_, sizeof(void*)*1, v_tid_3377_);
v___x_3383_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3382_;
}
v_reusejp_3382_:
{
lean_object* v___x_3385_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set(v___x_3375_, 4, v___x_3383_);
v___x_3385_ = v___x_3375_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_env_3365_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_nextMacroScope_3366_);
lean_ctor_set(v_reuseFailAlloc_3388_, 2, v_ngen_3367_);
lean_ctor_set(v_reuseFailAlloc_3388_, 3, v_auxDeclNGen_3368_);
lean_ctor_set(v_reuseFailAlloc_3388_, 4, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3388_, 5, v_cache_3369_);
lean_ctor_set(v_reuseFailAlloc_3388_, 6, v_recordedDeps_3370_);
lean_ctor_set(v_reuseFailAlloc_3388_, 7, v_messages_3371_);
lean_ctor_set(v_reuseFailAlloc_3388_, 8, v_infoState_3372_);
lean_ctor_set(v_reuseFailAlloc_3388_, 9, v_snapshotTasks_3373_);
v___x_3385_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_st_ref_put(v___y_3358_, v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3387_, 0, v_traces_3362_);
return v___x_3387_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3393_);
lean_dec(v___y_3393_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___x_3404_; 
lean_inc(v___y_3398_);
lean_inc(v___y_3397_);
v___x_3404_ = lean_apply_7(v_x_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, lean_box(0));
return v___x_3404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_){
_start:
{
lean_object* v_res_3413_; 
v_res_3413_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
lean_dec(v___y_3407_);
lean_dec(v___y_3406_);
return v_res_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3414_, lean_object* v_localInsts_3415_, lean_object* v_x_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v___f_3424_; lean_object* v___x_3425_; 
lean_inc(v___y_3418_);
lean_inc(v___y_3417_);
v___f_3424_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3424_, 0, v_x_3416_);
lean_closure_set(v___f_3424_, 1, v___y_3417_);
lean_closure_set(v___f_3424_, 2, v___y_3418_);
v___x_3425_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3414_, v_localInsts_3415_, v___f_3424_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
if (lean_obj_tag(v___x_3425_) == 0)
{
return v___x_3425_;
}
else
{
lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3425_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3425_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_dec(v___x_3425_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3434_, lean_object* v_localInsts_3435_, lean_object* v_x_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3434_, v_localInsts_3435_, v_x_3436_, v___y_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v___y_3438_);
lean_dec(v___y_3437_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3445_){
_start:
{
lean_object* v___x_3447_; lean_object* v_ngen_3448_; lean_object* v_namePrefix_3449_; lean_object* v_idx_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3480_; 
v___x_3447_ = lean_st_ref_get(v___y_3445_);
v_ngen_3448_ = lean_ctor_get(v___x_3447_, 2);
lean_inc_ref(v_ngen_3448_);
lean_dec(v___x_3447_);
v_namePrefix_3449_ = lean_ctor_get(v_ngen_3448_, 0);
v_idx_3450_ = lean_ctor_get(v_ngen_3448_, 1);
v_isSharedCheck_3480_ = !lean_is_exclusive(v_ngen_3448_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3452_ = v_ngen_3448_;
v_isShared_3453_ = v_isSharedCheck_3480_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_idx_3450_);
lean_inc(v_namePrefix_3449_);
lean_dec(v_ngen_3448_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3480_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v_r_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3458_; 
lean_inc(v_idx_3450_);
lean_inc(v_namePrefix_3449_);
v_r_3454_ = l_Lean_Name_num___override(v_namePrefix_3449_, v_idx_3450_);
v___x_3455_ = lean_unsigned_to_nat(1u);
v___x_3456_ = lean_nat_add(v_idx_3450_, v___x_3455_);
lean_dec(v_idx_3450_);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 1, v___x_3456_);
v___x_3458_ = v___x_3452_;
goto v_reusejp_3457_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_namePrefix_3449_);
lean_ctor_set(v_reuseFailAlloc_3479_, 1, v___x_3456_);
v___x_3458_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3457_;
}
v_reusejp_3457_:
{
lean_object* v___x_3459_; lean_object* v_env_3460_; lean_object* v_nextMacroScope_3461_; lean_object* v_auxDeclNGen_3462_; lean_object* v_traceState_3463_; lean_object* v_cache_3464_; lean_object* v_recordedDeps_3465_; lean_object* v_messages_3466_; lean_object* v_infoState_3467_; lean_object* v_snapshotTasks_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3477_; 
v___x_3459_ = lean_st_ref_take(v___y_3445_);
v_env_3460_ = lean_ctor_get(v___x_3459_, 0);
v_nextMacroScope_3461_ = lean_ctor_get(v___x_3459_, 1);
v_auxDeclNGen_3462_ = lean_ctor_get(v___x_3459_, 3);
v_traceState_3463_ = lean_ctor_get(v___x_3459_, 4);
v_cache_3464_ = lean_ctor_get(v___x_3459_, 5);
v_recordedDeps_3465_ = lean_ctor_get(v___x_3459_, 6);
v_messages_3466_ = lean_ctor_get(v___x_3459_, 7);
v_infoState_3467_ = lean_ctor_get(v___x_3459_, 8);
v_snapshotTasks_3468_ = lean_ctor_get(v___x_3459_, 9);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3459_, 2);
lean_dec(v_unused_3478_);
v___x_3470_ = v___x_3459_;
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snapshotTasks_3468_);
lean_inc(v_infoState_3467_);
lean_inc(v_messages_3466_);
lean_inc(v_recordedDeps_3465_);
lean_inc(v_cache_3464_);
lean_inc(v_traceState_3463_);
lean_inc(v_auxDeclNGen_3462_);
lean_inc(v_nextMacroScope_3461_);
lean_inc(v_env_3460_);
lean_dec(v___x_3459_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3477_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 2, v___x_3458_);
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_env_3460_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_nextMacroScope_3461_);
lean_ctor_set(v_reuseFailAlloc_3476_, 2, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3476_, 3, v_auxDeclNGen_3462_);
lean_ctor_set(v_reuseFailAlloc_3476_, 4, v_traceState_3463_);
lean_ctor_set(v_reuseFailAlloc_3476_, 5, v_cache_3464_);
lean_ctor_set(v_reuseFailAlloc_3476_, 6, v_recordedDeps_3465_);
lean_ctor_set(v_reuseFailAlloc_3476_, 7, v_messages_3466_);
lean_ctor_set(v_reuseFailAlloc_3476_, 8, v_infoState_3467_);
lean_ctor_set(v_reuseFailAlloc_3476_, 9, v_snapshotTasks_3468_);
v___x_3473_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3474_ = lean_st_ref_put(v___y_3445_, v___x_3473_);
v___x_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3475_, 0, v_r_3454_);
return v___x_3475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v_res_3483_; 
v_res_3483_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3481_);
lean_dec(v___y_3481_);
return v_res_3483_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3484_, lean_object* v___y_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v___x_3491_; lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
v___x_3491_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3489_);
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_, v___y_3505_);
lean_dec(v___y_3505_);
lean_dec_ref(v___y_3504_);
lean_dec(v___y_3503_);
lean_dec_ref(v___y_3502_);
lean_dec(v___y_3501_);
lean_dec(v___y_3500_);
return v_res_3507_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3509_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3510_ = l_Lean_stringToMessageData(v___x_3509_);
return v___x_3510_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
v___x_3512_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3513_ = l_Lean_stringToMessageData(v___x_3512_);
return v___x_3513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3516_, lean_object* v_x_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
lean_object* v___x_3525_; lean_object* v___y_3527_; uint8_t v___x_3536_; 
v___x_3525_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3536_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3518_);
if (v___x_3536_ == 0)
{
lean_object* v___x_3537_; 
v___x_3537_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3527_ = v___x_3537_;
goto v___jp_3526_;
}
else
{
lean_object* v___x_3538_; 
v___x_3538_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3527_ = v___x_3538_;
goto v___jp_3526_;
}
v___jp_3526_:
{
lean_object* v___x_3528_; lean_object* v___x_3529_; lean_object* v___x_3530_; lean_object* v___x_3531_; lean_object* v___x_3532_; lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; 
lean_inc_ref(v___y_3527_);
v___x_3528_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___y_3527_);
v___x_3529_ = l_Lean_MessageData_ofFormat(v___x_3528_);
v___x_3530_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3530_, 0, v___x_3525_);
lean_ctor_set(v___x_3530_, 1, v___x_3529_);
v___x_3531_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3532_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3532_, 0, v___x_3530_);
lean_ctor_set(v___x_3532_, 1, v___x_3531_);
v___x_3533_ = l_Lean_indentExpr(v_e_3516_);
v___x_3534_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3534_, 0, v___x_3532_);
lean_ctor_set(v___x_3534_, 1, v___x_3533_);
v___x_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3534_);
return v___x_3535_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3539_, lean_object* v_x_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
lean_object* v_res_3548_; 
v_res_3548_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3539_, v_x_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v_x_3540_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3549_, lean_object* v_x_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
lean_object* v_keyedConfig_3558_; uint8_t v_trackZetaDelta_3559_; lean_object* v_zetaDeltaSet_3560_; lean_object* v_localInstances_3561_; lean_object* v_defEqCtx_x3f_3562_; lean_object* v_synthPendingDepth_3563_; lean_object* v_customCanUnfoldPredicate_x3f_3564_; uint8_t v_univApprox_3565_; uint8_t v_inTypeClassResolution_3566_; uint8_t v_cacheInferType_3567_; lean_object* v___x_3568_; lean_object* v___x_3569_; 
v_keyedConfig_3558_ = lean_ctor_get(v___y_3553_, 0);
v_trackZetaDelta_3559_ = lean_ctor_get_uint8(v___y_3553_, sizeof(void*)*7);
v_zetaDeltaSet_3560_ = lean_ctor_get(v___y_3553_, 1);
v_localInstances_3561_ = lean_ctor_get(v___y_3553_, 3);
v_defEqCtx_x3f_3562_ = lean_ctor_get(v___y_3553_, 4);
v_synthPendingDepth_3563_ = lean_ctor_get(v___y_3553_, 5);
v_customCanUnfoldPredicate_x3f_3564_ = lean_ctor_get(v___y_3553_, 6);
v_univApprox_3565_ = lean_ctor_get_uint8(v___y_3553_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3566_ = lean_ctor_get_uint8(v___y_3553_, sizeof(void*)*7 + 2);
v_cacheInferType_3567_ = lean_ctor_get_uint8(v___y_3553_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3564_);
lean_inc(v_synthPendingDepth_3563_);
lean_inc(v_defEqCtx_x3f_3562_);
lean_inc_ref(v_localInstances_3561_);
lean_inc(v_zetaDeltaSet_3560_);
lean_inc_ref(v_keyedConfig_3558_);
v___x_3568_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3568_, 0, v_keyedConfig_3558_);
lean_ctor_set(v___x_3568_, 1, v_zetaDeltaSet_3560_);
lean_ctor_set(v___x_3568_, 2, v_lctx_3549_);
lean_ctor_set(v___x_3568_, 3, v_localInstances_3561_);
lean_ctor_set(v___x_3568_, 4, v_defEqCtx_x3f_3562_);
lean_ctor_set(v___x_3568_, 5, v_synthPendingDepth_3563_);
lean_ctor_set(v___x_3568_, 6, v_customCanUnfoldPredicate_x3f_3564_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*7, v_trackZetaDelta_3559_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*7 + 1, v_univApprox_3565_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3566_);
lean_ctor_set_uint8(v___x_3568_, sizeof(void*)*7 + 3, v_cacheInferType_3567_);
lean_inc(v___y_3556_);
lean_inc_ref(v___y_3555_);
lean_inc(v___y_3554_);
lean_inc(v___y_3552_);
lean_inc(v___y_3551_);
v___x_3569_ = lean_apply_7(v_x_3550_, v___y_3551_, v___y_3552_, v___x_3568_, v___y_3554_, v___y_3555_, v___y_3556_, lean_box(0));
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
else
{
return v___x_3569_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3578_, lean_object* v_x_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_){
_start:
{
lean_object* v_res_3587_; 
v_res_3587_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3578_, v_x_3579_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_, v___y_3585_);
lean_dec(v___y_3585_);
lean_dec_ref(v___y_3584_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec(v___y_3580_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3590_, lean_object* v_letFVars_3591_, lean_object* v_lctx_3592_, lean_object* v_v_3593_, lean_object* v_e_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3602_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3603_ = lean_expr_instantiate_rev(v_e_3594_, v_fvars_3590_);
v___x_3604_ = lean_apply_1(v_v_3593_, v___x_3603_);
v___x_3605_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3605_, 0, lean_box(0));
lean_closure_set(v___x_3605_, 1, v_letFVars_3591_);
lean_closure_set(v___x_3605_, 2, v___x_3604_);
v___x_3606_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3592_, v___x_3602_, v___x_3605_, v___y_3595_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3607_, lean_object* v_letFVars_3608_, lean_object* v_lctx_3609_, lean_object* v_v_3610_, lean_object* v_e_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_){
_start:
{
lean_object* v_res_3619_; 
v_res_3619_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3607_, v_letFVars_3608_, v_lctx_3609_, v_v_3610_, v_e_3611_, v___y_3612_, v___y_3613_, v___y_3614_, v___y_3615_, v___y_3616_, v___y_3617_);
lean_dec(v___y_3617_);
lean_dec_ref(v___y_3616_);
lean_dec(v___y_3615_);
lean_dec_ref(v___y_3614_);
lean_dec(v___y_3613_);
lean_dec(v___y_3612_);
lean_dec_ref(v_e_3611_);
lean_dec_ref(v_fvars_3607_);
return v_res_3619_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3622_ = l_Lean_stringToMessageData(v___x_3621_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3623_, lean_object* v_a_3624_, lean_object* v___y_3625_, lean_object* v___y_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___x_3632_; 
lean_inc_ref(v_a_3623_);
v___x_3632_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3623_, v___y_3626_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v_expr_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3684_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
lean_inc(v_a_3633_);
lean_dec_ref_known(v___x_3632_, 1);
v_expr_3634_ = lean_ctor_get(v_a_3624_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_a_3624_);
if (v_isSharedCheck_3684_ == 0)
{
lean_object* v_unused_3685_; 
v_unused_3685_ = lean_ctor_get(v_a_3624_, 1);
lean_dec(v_unused_3685_);
v___x_3636_ = v_a_3624_;
v_isShared_3637_ = v_isSharedCheck_3684_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_expr_3634_);
lean_dec(v_a_3624_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3684_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; 
lean_inc(v_a_3633_);
lean_inc_ref(v_expr_3634_);
v___x_3638_ = l_Lean_Meta_isExprDefEq(v_expr_3634_, v_a_3633_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3638_) == 0)
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3675_; 
v_a_3639_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3641_ = v___x_3638_;
v_isShared_3642_ = v_isSharedCheck_3675_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3638_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3675_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
uint8_t v___x_3643_; 
v___x_3643_ = lean_unbox(v_a_3639_);
lean_dec(v_a_3639_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
lean_del_object(v___x_3641_);
v___x_3644_ = lean_box(0);
v___x_3645_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3646_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3633_, v_expr_3634_, v___x_3644_, v___x_3645_, v___y_3627_);
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v_expr_3648_; lean_object* v___x_3650_; uint8_t v_isShared_3651_; uint8_t v_isSharedCheck_3661_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
lean_inc(v_a_3647_);
lean_dec_ref_known(v___x_3646_, 1);
v_expr_3648_ = lean_ctor_get(v_a_3623_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_a_3623_);
if (v_isSharedCheck_3661_ == 0)
{
lean_object* v_unused_3662_; 
v_unused_3662_ = lean_ctor_get(v_a_3623_, 1);
lean_dec(v_unused_3662_);
v___x_3650_ = v_a_3623_;
v_isShared_3651_ = v_isSharedCheck_3661_;
goto v_resetjp_3649_;
}
else
{
lean_inc(v_expr_3648_);
lean_dec(v_a_3623_);
v___x_3650_ = lean_box(0);
v_isShared_3651_ = v_isSharedCheck_3661_;
goto v_resetjp_3649_;
}
v_resetjp_3649_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3655_; 
v___x_3652_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3653_ = l_Lean_indentExpr(v_expr_3648_);
if (v_isShared_3651_ == 0)
{
lean_ctor_set_tag(v___x_3650_, 7);
lean_ctor_set(v___x_3650_, 1, v___x_3653_);
lean_ctor_set(v___x_3650_, 0, v___x_3652_);
v___x_3655_ = v___x_3650_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3660_; 
v_reuseFailAlloc_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3660_, 0, v___x_3652_);
lean_ctor_set(v_reuseFailAlloc_3660_, 1, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3660_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; 
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 7);
lean_ctor_set(v___x_3636_, 1, v_a_3647_);
lean_ctor_set(v___x_3636_, 0, v___x_3655_);
v___x_3657_ = v___x_3636_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_a_3647_);
v___x_3657_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3657_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3658_;
}
}
}
}
else
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
lean_del_object(v___x_3636_);
lean_dec_ref(v_a_3623_);
v_a_3663_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3670_ == 0)
{
v___x_3665_ = v___x_3646_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3646_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
}
else
{
lean_object* v___x_3671_; lean_object* v___x_3673_; 
lean_del_object(v___x_3636_);
lean_dec_ref(v_expr_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3623_);
v___x_3671_ = lean_box(0);
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 0, v___x_3671_);
v___x_3673_ = v___x_3641_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_del_object(v___x_3636_);
lean_dec_ref(v_expr_3634_);
lean_dec(v_a_3633_);
lean_dec_ref(v_a_3623_);
v_a_3676_ = lean_ctor_get(v___x_3638_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3638_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3638_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3638_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_dec_ref(v_a_3624_);
lean_dec_ref(v_a_3623_);
v_a_3686_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3632_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3632_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3694_, lean_object* v_a_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_){
_start:
{
lean_object* v_res_3703_; 
v_res_3703_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3694_, v_a_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_);
lean_dec(v___y_3701_);
lean_dec_ref(v___y_3700_);
lean_dec(v___y_3699_);
lean_dec_ref(v___y_3698_);
lean_dec(v___y_3697_);
lean_dec(v___y_3696_);
return v_res_3703_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
v___x_3705_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3706_ = l_Lean_stringToMessageData(v___x_3705_);
return v___x_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
if (lean_obj_tag(v_e_3707_) == 5)
{
lean_object* v_fn_3715_; lean_object* v_arg_3716_; lean_object* v___x_3717_; 
v_fn_3715_ = lean_ctor_get(v_e_3707_, 0);
v_arg_3716_ = lean_ctor_get(v_e_3707_, 1);
lean_inc_ref(v_fn_3715_);
v___x_3717_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3715_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; lean_object* v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
lean_inc_ref(v_arg_3716_);
v___x_3719_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3716_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3719_) == 0)
{
lean_object* v_a_3720_; lean_object* v___x_3722_; uint8_t v_isShared_3723_; uint8_t v_isSharedCheck_3742_; 
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3722_ = v___x_3719_;
v_isShared_3723_ = v_isSharedCheck_3742_;
goto v_resetjp_3721_;
}
else
{
lean_inc(v_a_3720_);
lean_dec(v___x_3719_);
v___x_3722_ = lean_box(0);
v_isShared_3723_ = v_isSharedCheck_3742_;
goto v_resetjp_3721_;
}
v_resetjp_3721_:
{
lean_object* v_expr_3724_; size_t v___x_3725_; size_t v___x_3726_; uint8_t v___x_3727_; 
v_expr_3724_ = lean_ctor_get(v_a_3720_, 0);
lean_inc_ref(v_expr_3724_);
lean_dec(v_a_3720_);
v___x_3725_ = lean_ptr_addr(v_fn_3715_);
v___x_3726_ = lean_ptr_addr(v_a_3718_);
v___x_3727_ = lean_usize_dec_eq(v___x_3725_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
lean_dec_ref_known(v_e_3707_, 2);
v___x_3728_ = l_Lean_Expr_app___override(v_a_3718_, v_expr_3724_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3728_);
v___x_3730_ = v___x_3722_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
else
{
size_t v___x_3732_; size_t v___x_3733_; uint8_t v___x_3734_; 
v___x_3732_ = lean_ptr_addr(v_arg_3716_);
v___x_3733_ = lean_ptr_addr(v_expr_3724_);
v___x_3734_ = lean_usize_dec_eq(v___x_3732_, v___x_3733_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; lean_object* v___x_3737_; 
lean_dec_ref_known(v_e_3707_, 2);
v___x_3735_ = l_Lean_Expr_app___override(v_a_3718_, v_expr_3724_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v___x_3735_);
v___x_3737_ = v___x_3722_;
goto v_reusejp_3736_;
}
else
{
lean_object* v_reuseFailAlloc_3738_; 
v_reuseFailAlloc_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3738_, 0, v___x_3735_);
v___x_3737_ = v_reuseFailAlloc_3738_;
goto v_reusejp_3736_;
}
v_reusejp_3736_:
{
return v___x_3737_;
}
}
else
{
lean_object* v___x_3740_; 
lean_dec_ref(v_expr_3724_);
lean_dec(v_a_3718_);
if (v_isShared_3723_ == 0)
{
lean_ctor_set(v___x_3722_, 0, v_e_3707_);
v___x_3740_ = v___x_3722_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_e_3707_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_a_3718_);
lean_dec_ref_known(v_e_3707_, 2);
v_a_3743_ = lean_ctor_get(v___x_3719_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3719_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3719_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3719_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3707_, 2);
return v___x_3717_;
}
}
else
{
lean_object* v___x_3751_; 
v___x_3751_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3707_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3760_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3754_ = v___x_3751_;
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3751_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3760_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v_expr_3756_; lean_object* v___x_3758_; 
v_expr_3756_ = lean_ctor_get(v_a_3752_, 0);
lean_inc_ref(v_expr_3756_);
lean_dec(v_a_3752_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set(v___x_3754_, 0, v_expr_3756_);
v___x_3758_ = v___x_3754_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_expr_3756_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v_a_3761_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3763_ = v___x_3751_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_inc(v_a_3761_);
lean_dec(v___x_3751_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3761_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3769_, lean_object* v_a_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v_res_3777_; 
v_res_3777_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3769_, v_a_3770_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_);
lean_dec(v_a_3775_);
lean_dec_ref(v_a_3774_);
lean_dec(v_a_3773_);
lean_dec_ref(v_a_3772_);
lean_dec(v_a_3771_);
lean_dec(v_a_3770_);
return v_res_3777_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_, lean_object* v_a_3783_, lean_object* v_a_3784_){
_start:
{
if (lean_obj_tag(v_e_3778_) == 5)
{
lean_object* v_fn_3786_; lean_object* v_arg_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; 
v_fn_3786_ = lean_ctor_get(v_e_3778_, 0);
v_arg_3787_ = lean_ctor_get(v_e_3778_, 1);
lean_inc_ref_n(v_fn_3786_, 2);
v___x_3788_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3788_, 0, v_fn_3786_);
v___x_3789_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3786_, v___x_3788_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
if (lean_obj_tag(v___x_3789_) == 0)
{
lean_object* v_a_3790_; lean_object* v___x_3791_; 
v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
lean_inc(v_a_3790_);
lean_dec_ref_known(v___x_3789_, 1);
lean_inc_ref(v_arg_3787_);
v___x_3791_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3787_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; lean_object* v___x_3793_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
v___x_3793_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3778_, v_a_3790_, v_a_3792_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
return v___x_3793_;
}
else
{
lean_dec(v_a_3790_);
lean_dec_ref_known(v_e_3778_, 2);
return v___x_3791_;
}
}
else
{
lean_dec_ref_known(v_e_3778_, 2);
return v___x_3789_;
}
}
else
{
lean_object* v___x_3794_; 
v___x_3794_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_);
return v___x_3794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3795_, lean_object* v_a_3796_, lean_object* v_a_3797_, lean_object* v_a_3798_, lean_object* v_a_3799_, lean_object* v_a_3800_, lean_object* v_a_3801_){
_start:
{
uint8_t v___x_3803_; 
v___x_3803_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3796_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; 
v___x_3804_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3814_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3814_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3814_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3814_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3814_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3809_ = lean_box(0);
v___x_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3810_, 0, v_a_3805_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3810_);
v___x_3812_ = v___x_3807_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3822_; 
v_a_3815_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3817_ = v___x_3804_;
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_a_3815_);
lean_dec(v___x_3804_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3822_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3820_; 
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
return v___x_3820_;
}
}
}
}
else
{
lean_object* v___x_3823_; 
v___x_3823_ = l_Lean_Expr_getAppFn(v_e_3795_);
if (lean_obj_tag(v___x_3823_) == 2)
{
lean_object* v_mvarId_3824_; lean_object* v_dummy_3825_; lean_object* v_nargs_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; 
v_mvarId_3824_ = lean_ctor_get(v___x_3823_, 0);
lean_inc(v_mvarId_3824_);
lean_dec_ref_known(v___x_3823_, 1);
v_dummy_3825_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3826_ = l_Lean_Expr_getAppNumArgs(v_e_3795_);
lean_inc(v_nargs_3826_);
v___x_3827_ = lean_mk_array(v_nargs_3826_, v_dummy_3825_);
v___x_3828_ = lean_unsigned_to_nat(1u);
v___x_3829_ = lean_nat_sub(v_nargs_3826_, v___x_3828_);
lean_dec(v_nargs_3826_);
lean_inc_ref(v_e_3795_);
v___x_3830_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3795_, v___x_3827_, v___x_3829_);
v___x_3831_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3824_, v___x_3830_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
lean_dec(v_mvarId_3824_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v___x_3832_; 
lean_dec_ref_known(v___x_3831_, 1);
v___x_3832_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
return v___x_3832_;
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3840_; 
lean_dec_ref(v_e_3795_);
v_a_3833_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3835_ = v___x_3831_;
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3831_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3840_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3838_; 
if (v_isShared_3836_ == 0)
{
v___x_3838_ = v___x_3835_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_a_3833_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
}
else
{
lean_object* v___x_3841_; 
lean_dec_ref(v___x_3823_);
v___x_3841_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_);
return v___x_3841_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec(v_a_3844_);
lean_dec(v_a_3843_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_){
_start:
{
lean_object* v___x_3859_; 
v___x_3859_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v___x_3861_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v___x_3859_, 1);
v___x_3861_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3860_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_);
return v___x_3861_;
}
else
{
return v___x_3859_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_, lean_object* v_a_3866_, lean_object* v_a_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_){
_start:
{
lean_object* v_res_3870_; 
v_res_3870_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3862_, v_a_3863_, v_a_3864_, v_a_3865_, v_a_3866_, v_a_3867_, v_a_3868_);
lean_dec(v_a_3868_);
lean_dec_ref(v_a_3867_);
lean_dec(v_a_3866_);
lean_dec_ref(v_a_3865_);
lean_dec(v_a_3864_);
lean_dec(v_a_3863_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3871_, lean_object* v_fvars_3872_, lean_object* v_doms_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_){
_start:
{
lean_object* v___x_3881_; 
v___x_3881_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3871_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
if (lean_obj_tag(v___x_3881_) == 0)
{
lean_object* v_a_3882_; lean_object* v___x_3883_; 
v_a_3882_ = lean_ctor_get(v___x_3881_, 0);
lean_inc(v_a_3882_);
lean_dec_ref_known(v___x_3881_, 1);
v___x_3883_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3872_, v_doms_3873_, v_a_3882_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_, v___y_3878_, v___y_3879_);
return v___x_3883_;
}
else
{
return v___x_3881_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3884_, lean_object* v_fvars_3885_, lean_object* v_doms_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
lean_object* v_res_3894_; 
v_res_3894_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3884_, v_fvars_3885_, v_doms_3886_, v___y_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec(v___y_3888_);
lean_dec(v___y_3887_);
lean_dec_ref(v_doms_3886_);
lean_dec_ref(v_fvars_3885_);
return v_res_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3895_, lean_object* v_fvars_3896_, lean_object* v_doms_3897_, lean_object* v_e_3898_, lean_object* v_a_3899_, lean_object* v_a_3900_, lean_object* v_a_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_){
_start:
{
lean_object* v___x_3906_; 
v___x_3906_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3898_, v_a_3900_);
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_object* v_a_3907_; 
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
if (lean_obj_tag(v_a_3907_) == 1)
{
lean_object* v_val_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
lean_dec_ref(v_e_3898_);
v_val_3908_ = lean_ctor_get(v_a_3907_, 0);
lean_inc(v_val_3908_);
lean_dec_ref_known(v_a_3907_, 1);
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3910_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3910_, 0, v_fvars_3896_);
lean_closure_set(v___x_3910_, 1, v_doms_3897_);
lean_closure_set(v___x_3910_, 2, v_val_3908_);
v___x_3911_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3895_, v___x_3909_, v___x_3910_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
return v___x_3911_;
}
else
{
lean_dec(v_a_3907_);
if (lean_obj_tag(v_e_3898_) == 7)
{
lean_object* v_binderName_3912_; lean_object* v_binderType_3913_; lean_object* v_body_3914_; uint8_t v_binderInfo_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; 
v_binderName_3912_ = lean_ctor_get(v_e_3898_, 0);
lean_inc(v_binderName_3912_);
v_binderType_3913_ = lean_ctor_get(v_e_3898_, 1);
lean_inc_ref(v_binderType_3913_);
v_body_3914_ = lean_ctor_get(v_e_3898_, 2);
lean_inc_ref(v_body_3914_);
v_binderInfo_3915_ = lean_ctor_get_uint8(v_e_3898_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3898_, 3);
v___x_3916_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3917_ = lean_expr_instantiate_rev(v_binderType_3913_, v_fvars_3896_);
lean_dec_ref(v_binderType_3913_);
v___x_3918_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3918_, 0, v___x_3917_);
lean_inc_ref(v_lctx_3895_);
v___x_3919_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3895_, v___x_3916_, v___x_3918_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v_a_3920_; lean_object* v___x_3921_; 
v_a_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc(v_a_3920_);
lean_dec_ref_known(v___x_3919_, 1);
v___x_3921_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
if (lean_obj_tag(v___x_3921_) == 0)
{
lean_object* v_a_3922_; lean_object* v_expr_3923_; uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; 
v_a_3922_ = lean_ctor_get(v___x_3921_, 0);
lean_inc_n(v_a_3922_, 2);
lean_dec_ref_known(v___x_3921_, 1);
v_expr_3923_ = lean_ctor_get(v_a_3920_, 0);
v___x_3924_ = 0;
lean_inc_ref(v_expr_3923_);
v___x_3925_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3895_, v_a_3922_, v_binderName_3912_, v_expr_3923_, v_binderInfo_3915_, v___x_3924_);
v___x_3926_ = l_Lean_Expr_fvar___override(v_a_3922_);
v___x_3927_ = lean_array_push(v_fvars_3896_, v___x_3926_);
v___x_3928_ = lean_array_push(v_doms_3897_, v_a_3920_);
v_lctx_3895_ = v___x_3925_;
v_fvars_3896_ = v___x_3927_;
v_doms_3897_ = v___x_3928_;
v_e_3898_ = v_body_3914_;
goto _start;
}
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_dec(v_a_3920_);
lean_dec_ref(v_body_3914_);
lean_dec(v_binderName_3912_);
lean_dec_ref(v_doms_3897_);
lean_dec_ref(v_fvars_3896_);
lean_dec_ref(v_lctx_3895_);
v_a_3930_ = lean_ctor_get(v___x_3921_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3921_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3921_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
else
{
lean_dec_ref(v_body_3914_);
lean_dec(v_binderName_3912_);
lean_dec_ref(v_doms_3897_);
lean_dec_ref(v_fvars_3896_);
lean_dec_ref(v_lctx_3895_);
return v___x_3919_;
}
}
else
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___f_3940_; lean_object* v___x_3941_; 
v___x_3938_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3939_ = lean_expr_instantiate_rev(v_e_3898_, v_fvars_3896_);
lean_dec_ref(v_e_3898_);
v___f_3940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3940_, 0, v___x_3939_);
lean_closure_set(v___f_3940_, 1, v_fvars_3896_);
lean_closure_set(v___f_3940_, 2, v_doms_3897_);
v___x_3941_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3895_, v___x_3938_, v___f_3940_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_, v_a_3903_, v_a_3904_);
return v___x_3941_;
}
}
}
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_dec_ref(v_e_3898_);
lean_dec_ref(v_doms_3897_);
lean_dec_ref(v_fvars_3896_);
lean_dec_ref(v_lctx_3895_);
v_a_3942_ = lean_ctor_get(v___x_3906_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3906_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3906_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3906_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3950_, lean_object* v_a_3951_, lean_object* v_a_3952_, lean_object* v_a_3953_, lean_object* v_a_3954_, lean_object* v_a_3955_, lean_object* v_a_3956_){
_start:
{
uint32_t v___x_3958_; uint8_t v___x_3959_; 
v___x_3958_ = 5;
v___x_3959_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3950_, v___x_3958_);
if (v___x_3959_ == 0)
{
lean_object* v_lctx_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v_lctx_3960_ = lean_ctor_get(v_a_3953_, 2);
v___x_3961_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3960_);
v___x_3962_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3960_, v___x_3961_, v___x_3961_, v_e_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_, v_a_3956_);
return v___x_3962_;
}
else
{
lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = lean_box(0);
v___x_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3964_, 0, v_e_3950_);
lean_ctor_set(v___x_3964_, 1, v___x_3963_);
v___x_3965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
return v___x_3965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3966_, lean_object* v_a_3967_, lean_object* v_a_3968_, lean_object* v_a_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3966_, v_a_3967_, v_a_3968_, v_a_3969_, v_a_3970_, v_a_3971_, v_a_3972_);
lean_dec(v_a_3972_);
lean_dec_ref(v_a_3971_);
lean_dec(v_a_3970_);
lean_dec_ref(v_a_3969_);
lean_dec(v_a_3968_);
lean_dec(v_a_3967_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_3975_, lean_object* v_e_3976_, lean_object* v_typeName_3977_, lean_object* v_idx_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_3975_, v_e_3976_, v_typeName_3977_, v_idx_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec(v___y_3979_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_3987_, lean_object* v_a_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_, v_a_3993_);
lean_dec(v_a_3993_);
lean_dec_ref(v_a_3992_);
lean_dec(v_a_3991_);
lean_dec_ref(v_a_3990_);
lean_dec(v_a_3989_);
lean_dec(v_a_3988_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_object* v_a_4006_; lean_object* v___x_4007_; 
v_a_4006_ = lean_ctor_get(v___x_4005_, 0);
lean_inc(v_a_4006_);
lean_dec_ref_known(v___x_4005_, 1);
v___x_4007_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_3996_, v_a_4006_, v___y_3998_, v___y_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
return v___x_4007_;
}
else
{
lean_dec_ref(v_fvars_3996_);
return v___x_4005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_res_4017_; 
v_res_4017_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_);
lean_dec(v___y_4015_);
lean_dec_ref(v___y_4014_);
lean_dec(v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec(v___y_4011_);
lean_dec(v___y_4010_);
return v_res_4017_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4018_, lean_object* v_fvars_4019_, lean_object* v_e_4020_, lean_object* v_letFVars_4021_, lean_object* v_a_4022_, lean_object* v_a_4023_, lean_object* v_a_4024_, lean_object* v_a_4025_, lean_object* v_a_4026_, lean_object* v_a_4027_){
_start:
{
switch(lean_obj_tag(v_e_4020_))
{
case 6:
{
lean_object* v_binderName_4029_; lean_object* v_binderType_4030_; lean_object* v_body_4031_; uint8_t v_binderInfo_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v_binderName_4029_ = lean_ctor_get(v_e_4020_, 0);
lean_inc(v_binderName_4029_);
v_binderType_4030_ = lean_ctor_get(v_e_4020_, 1);
lean_inc_ref(v_binderType_4030_);
v_body_4031_ = lean_ctor_get(v_e_4020_, 2);
lean_inc_ref(v_body_4031_);
v_binderInfo_4032_ = lean_ctor_get_uint8(v_e_4020_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4020_, 3);
v___x_4033_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4018_);
lean_inc(v_letFVars_4021_);
v___x_4034_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4019_, v_letFVars_4021_, v_lctx_4018_, v___x_4033_, v_binderType_4030_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec_ref(v_binderType_4030_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4036_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
v___x_4036_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v_expr_4038_; uint8_t v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc_n(v_a_4037_, 2);
lean_dec_ref_known(v___x_4036_, 1);
v_expr_4038_ = lean_ctor_get(v_a_4035_, 0);
lean_inc_ref(v_expr_4038_);
lean_dec(v_a_4035_);
v___x_4039_ = 0;
v___x_4040_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4018_, v_a_4037_, v_binderName_4029_, v_expr_4038_, v_binderInfo_4032_, v___x_4039_);
v___x_4041_ = l_Lean_Expr_fvar___override(v_a_4037_);
v___x_4042_ = lean_array_push(v_fvars_4019_, v___x_4041_);
v_lctx_4018_ = v___x_4040_;
v_fvars_4019_ = v___x_4042_;
v_e_4020_ = v_body_4031_;
goto _start;
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_dec(v_a_4035_);
lean_dec_ref(v_body_4031_);
lean_dec(v_binderName_4029_);
lean_dec(v_letFVars_4021_);
lean_dec_ref(v_fvars_4019_);
lean_dec_ref(v_lctx_4018_);
v_a_4044_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4036_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4036_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_dec_ref(v_body_4031_);
lean_dec(v_binderName_4029_);
lean_dec(v_letFVars_4021_);
lean_dec_ref(v_fvars_4019_);
lean_dec_ref(v_lctx_4018_);
return v___x_4034_;
}
}
case 8:
{
lean_object* v_declName_4052_; lean_object* v_type_4053_; lean_object* v_value_4054_; lean_object* v_body_4055_; uint8_t v_nondep_4056_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; lean_object* v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_declName_4052_ = lean_ctor_get(v_e_4020_, 0);
lean_inc(v_declName_4052_);
v_type_4053_ = lean_ctor_get(v_e_4020_, 1);
lean_inc_ref(v_type_4053_);
v_value_4054_ = lean_ctor_get(v_e_4020_, 2);
lean_inc_ref(v_value_4054_);
v_body_4055_ = lean_ctor_get(v_e_4020_, 3);
lean_inc_ref(v_body_4055_);
v_nondep_4056_ = lean_ctor_get_uint8(v_e_4020_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4020_, 4);
v___x_4070_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4018_);
lean_inc(v_letFVars_4021_);
v___x_4071_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4019_, v_letFVars_4021_, v_lctx_4018_, v___x_4070_, v_type_4053_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec_ref(v_type_4053_);
if (lean_obj_tag(v___x_4071_) == 0)
{
lean_object* v_a_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; 
v_a_4072_ = lean_ctor_get(v___x_4071_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4071_, 1);
v___x_4073_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4018_);
lean_inc(v_letFVars_4021_);
v___x_4074_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4019_, v_letFVars_4021_, v_lctx_4018_, v___x_4073_, v_value_4054_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec_ref(v_value_4054_);
if (lean_obj_tag(v___x_4074_) == 0)
{
lean_object* v_a_4075_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; uint8_t v___x_4105_; 
v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
lean_inc(v_a_4075_);
lean_dec_ref_known(v___x_4074_, 1);
v___x_4105_ = l_List_isEmpty___redArg(v_letFVars_4021_);
if (v___x_4105_ == 0)
{
lean_object* v___f_4106_; lean_object* v___x_4107_; 
lean_inc(v_a_4072_);
lean_inc(v_a_4075_);
v___f_4106_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4106_, 0, v_a_4075_);
lean_closure_set(v___f_4106_, 1, v_a_4072_);
lean_inc_ref(v_lctx_4018_);
v___x_4107_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4018_, v___f_4106_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_dec_ref_known(v___x_4107_, 1);
v___y_4077_ = v_a_4022_;
v___y_4078_ = v_a_4023_;
v___y_4079_ = v_a_4024_;
v___y_4080_ = v_a_4025_;
v___y_4081_ = v_a_4026_;
v___y_4082_ = v_a_4027_;
goto v___jp_4076_;
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_a_4075_);
lean_dec(v_a_4072_);
lean_dec_ref(v_body_4055_);
lean_dec(v_declName_4052_);
lean_dec(v_letFVars_4021_);
lean_dec_ref(v_fvars_4019_);
lean_dec_ref(v_lctx_4018_);
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
v___y_4077_ = v_a_4022_;
v___y_4078_ = v_a_4023_;
v___y_4079_ = v_a_4024_;
v___y_4080_ = v_a_4025_;
v___y_4081_ = v_a_4026_;
v___y_4082_ = v_a_4027_;
goto v___jp_4076_;
}
v___jp_4076_:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_, v___y_4082_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v_a_4084_; lean_object* v_expr_4085_; lean_object* v_expr_4086_; lean_object* v___x_4088_; uint8_t v_isShared_4089_; uint8_t v_isSharedCheck_4095_; 
v_a_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc(v_a_4084_);
lean_dec_ref_known(v___x_4083_, 1);
v_expr_4085_ = lean_ctor_get(v_a_4072_, 0);
lean_inc_ref(v_expr_4085_);
lean_dec(v_a_4072_);
v_expr_4086_ = lean_ctor_get(v_a_4075_, 0);
v_isSharedCheck_4095_ = !lean_is_exclusive(v_a_4075_);
if (v_isSharedCheck_4095_ == 0)
{
lean_object* v_unused_4096_; 
v_unused_4096_ = lean_ctor_get(v_a_4075_, 1);
lean_dec(v_unused_4096_);
v___x_4088_ = v_a_4075_;
v_isShared_4089_ = v_isSharedCheck_4095_;
goto v_resetjp_4087_;
}
else
{
lean_inc(v_expr_4086_);
lean_dec(v_a_4075_);
v___x_4088_ = lean_box(0);
v_isShared_4089_ = v_isSharedCheck_4095_;
goto v_resetjp_4087_;
}
v_resetjp_4087_:
{
uint8_t v___x_4090_; lean_object* v___x_4091_; 
v___x_4090_ = 0;
lean_inc(v_a_4084_);
v___x_4091_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4018_, v_a_4084_, v_declName_4052_, v_expr_4085_, v_expr_4086_, v_nondep_4056_, v___x_4090_);
if (v_nondep_4056_ == 0)
{
lean_object* v___x_4093_; 
lean_inc(v_a_4084_);
if (v_isShared_4089_ == 0)
{
lean_ctor_set_tag(v___x_4088_, 1);
lean_ctor_set(v___x_4088_, 1, v_letFVars_4021_);
lean_ctor_set(v___x_4088_, 0, v_a_4084_);
v___x_4093_ = v___x_4088_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v_a_4084_);
lean_ctor_set(v_reuseFailAlloc_4094_, 1, v_letFVars_4021_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
v___y_4058_ = v___y_4081_;
v___y_4059_ = v_a_4084_;
v___y_4060_ = v___y_4082_;
v___y_4061_ = v___y_4078_;
v___y_4062_ = v___y_4079_;
v___y_4063_ = v___y_4080_;
v___y_4064_ = v___y_4077_;
v___y_4065_ = v___x_4091_;
v___y_4066_ = v___x_4093_;
goto v___jp_4057_;
}
}
else
{
lean_del_object(v___x_4088_);
v___y_4058_ = v___y_4081_;
v___y_4059_ = v_a_4084_;
v___y_4060_ = v___y_4082_;
v___y_4061_ = v___y_4078_;
v___y_4062_ = v___y_4079_;
v___y_4063_ = v___y_4080_;
v___y_4064_ = v___y_4077_;
v___y_4065_ = v___x_4091_;
v___y_4066_ = v_letFVars_4021_;
goto v___jp_4057_;
}
}
}
else
{
lean_object* v_a_4097_; lean_object* v___x_4099_; uint8_t v_isShared_4100_; uint8_t v_isSharedCheck_4104_; 
lean_dec(v_a_4075_);
lean_dec(v_a_4072_);
lean_dec_ref(v_body_4055_);
lean_dec(v_declName_4052_);
lean_dec(v_letFVars_4021_);
lean_dec_ref(v_fvars_4019_);
lean_dec_ref(v_lctx_4018_);
v_a_4097_ = lean_ctor_get(v___x_4083_, 0);
v_isSharedCheck_4104_ = !lean_is_exclusive(v___x_4083_);
if (v_isSharedCheck_4104_ == 0)
{
v___x_4099_ = v___x_4083_;
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
else
{
lean_inc(v_a_4097_);
lean_dec(v___x_4083_);
v___x_4099_ = lean_box(0);
v_isShared_4100_ = v_isSharedCheck_4104_;
goto v_resetjp_4098_;
}
v_resetjp_4098_:
{
lean_object* v___x_4102_; 
if (v_isShared_4100_ == 0)
{
v___x_4102_ = v___x_4099_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v_a_4097_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
}
}
}
else
{
lean_dec(v_a_4072_);
lean_dec_ref(v_body_4055_);
lean_dec(v_declName_4052_);
lean_dec(v_letFVars_4021_);
lean_dec_ref(v_fvars_4019_);
lean_dec_ref(v_lctx_4018_);
return v___x_4074_;
}
}
else
{
lean_dec_ref(v_body_4055_);
lean_dec_ref(v_value_4054_);
lean_dec(v_declName_4052_);
lean_dec(v_letFVars_4021_);
lean_dec_ref(v_fvars_4019_);
lean_dec_ref(v_lctx_4018_);
return v___x_4071_;
}
v___jp_4057_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = l_Lean_Expr_fvar___override(v___y_4059_);
v___x_4068_ = lean_array_push(v_fvars_4019_, v___x_4067_);
v_lctx_4018_ = v___y_4065_;
v_fvars_4019_ = v___x_4068_;
v_e_4020_ = v_body_4055_;
v_letFVars_4021_ = v___y_4066_;
v_a_4022_ = v___y_4064_;
v_a_4023_ = v___y_4061_;
v_a_4024_ = v___y_4062_;
v_a_4025_ = v___y_4063_;
v_a_4026_ = v___y_4058_;
v_a_4027_ = v___y_4060_;
goto _start;
}
}
default: 
{
lean_object* v___f_4116_; lean_object* v___x_4117_; 
lean_inc_ref(v_fvars_4019_);
v___f_4116_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4116_, 0, v_fvars_4019_);
v___x_4117_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4019_, v_letFVars_4021_, v_lctx_4018_, v___f_4116_, v_e_4020_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_, v_a_4026_, v_a_4027_);
lean_dec_ref(v_e_4020_);
lean_dec_ref(v_fvars_4019_);
return v___x_4117_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4118_, lean_object* v_a_4119_, lean_object* v_a_4120_, lean_object* v_a_4121_, lean_object* v_a_4122_, lean_object* v_a_4123_, lean_object* v_a_4124_){
_start:
{
uint32_t v___x_4126_; uint8_t v___x_4127_; 
v___x_4126_ = 5;
v___x_4127_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4118_, v___x_4126_);
if (v___x_4127_ == 0)
{
lean_object* v_lctx_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_lctx_4128_ = lean_ctor_get(v_a_4121_, 2);
v___x_4129_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4119_);
lean_inc_ref(v_lctx_4128_);
v___x_4130_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4128_, v___x_4129_, v_e_4118_, v_a_4119_, v_a_4119_, v_a_4120_, v_a_4121_, v_a_4122_, v_a_4123_, v_a_4124_);
return v___x_4130_;
}
else
{
lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; 
v___x_4131_ = lean_box(0);
v___x_4132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4132_, 0, v_e_4118_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
v___x_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4133_, 0, v___x_4132_);
return v___x_4133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec(v_a_4135_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
switch(lean_obj_tag(v_e_4143_))
{
case 0:
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; 
v___x_4151_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4152_ = l_Lean_MessageData_ofExpr(v_e_4143_);
v___x_4153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4151_);
lean_ctor_set(v___x_4153_, 1, v___x_4152_);
v___x_4154_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4153_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4154_;
}
case 1:
{
lean_object* v___x_4155_; 
v___x_4155_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4143_, v___y_4146_, v___y_4148_, v___y_4149_);
return v___x_4155_;
}
case 2:
{
lean_object* v___x_4156_; 
v___x_4156_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4156_;
}
case 3:
{
lean_object* v_u_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_u_4157_ = lean_ctor_get(v_e_4143_, 0);
lean_inc(v_u_4157_);
v___x_4158_ = l_Lean_Level_succ___override(v_u_4157_);
v___x_4159_ = l_Lean_Expr_sort___override(v___x_4158_);
v___x_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v_e_4143_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
return v___x_4162_;
}
case 4:
{
lean_object* v___x_4163_; 
v___x_4163_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4143_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4163_;
}
case 5:
{
lean_object* v___x_4164_; lean_object* v___x_4165_; 
lean_inc_ref(v_e_4143_);
v___x_4164_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4164_, 0, v_e_4143_);
v___x_4165_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4143_, v___x_4164_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4165_;
}
case 7:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; 
lean_inc_ref(v_e_4143_);
v___x_4166_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4166_, 0, v_e_4143_);
v___x_4167_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4143_, v___x_4166_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4167_;
}
case 9:
{
lean_object* v_a_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v_a_4168_ = lean_ctor_get(v_e_4143_, 0);
v___x_4169_ = l_Lean_Literal_type(v_a_4168_);
v___x_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v_e_4143_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
return v___x_4172_;
}
case 10:
{
lean_object* v_data_4173_; lean_object* v_expr_4174_; lean_object* v___x_4175_; 
v_data_4173_ = lean_ctor_get(v_e_4143_, 0);
v_expr_4174_ = lean_ctor_get(v_e_4143_, 1);
lean_inc_ref(v_expr_4174_);
v___x_4175_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4174_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4198_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4178_ = v___x_4175_;
v_isShared_4179_ = v_isSharedCheck_4198_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4175_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4198_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v_expr_4180_; lean_object* v_type_x3f_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4197_; 
v_expr_4180_ = lean_ctor_get(v_a_4176_, 0);
v_type_x3f_4181_ = lean_ctor_get(v_a_4176_, 1);
v_isSharedCheck_4197_ = !lean_is_exclusive(v_a_4176_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4183_ = v_a_4176_;
v_isShared_4184_ = v_isSharedCheck_4197_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_type_x3f_4181_);
lean_inc(v_expr_4180_);
lean_dec(v_a_4176_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4197_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v___y_4186_; size_t v___x_4193_; size_t v___x_4194_; uint8_t v___x_4195_; 
v___x_4193_ = lean_ptr_addr(v_expr_4174_);
v___x_4194_ = lean_ptr_addr(v_expr_4180_);
v___x_4195_ = lean_usize_dec_eq(v___x_4193_, v___x_4194_);
if (v___x_4195_ == 0)
{
lean_object* v___x_4196_; 
lean_inc(v_data_4173_);
lean_dec_ref_known(v_e_4143_, 2);
v___x_4196_ = l_Lean_Expr_mdata___override(v_data_4173_, v_expr_4180_);
v___y_4186_ = v___x_4196_;
goto v___jp_4185_;
}
else
{
lean_dec_ref(v_expr_4180_);
v___y_4186_ = v_e_4143_;
goto v___jp_4185_;
}
v___jp_4185_:
{
lean_object* v___x_4188_; 
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v___y_4186_);
v___x_4188_ = v___x_4183_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4192_; 
v_reuseFailAlloc_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4192_, 0, v___y_4186_);
lean_ctor_set(v_reuseFailAlloc_4192_, 1, v_type_x3f_4181_);
v___x_4188_ = v_reuseFailAlloc_4192_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
lean_object* v___x_4190_; 
if (v_isShared_4179_ == 0)
{
lean_ctor_set(v___x_4178_, 0, v___x_4188_);
v___x_4190_ = v___x_4178_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v___x_4188_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
return v___x_4190_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4143_, 2);
return v___x_4175_;
}
}
case 11:
{
lean_object* v_typeName_4199_; lean_object* v_idx_4200_; lean_object* v_struct_4201_; lean_object* v___f_4202_; lean_object* v___x_4203_; 
v_typeName_4199_ = lean_ctor_get(v_e_4143_, 0);
v_idx_4200_ = lean_ctor_get(v_e_4143_, 1);
v_struct_4201_ = lean_ctor_get(v_e_4143_, 2);
lean_inc(v_idx_4200_);
lean_inc(v_typeName_4199_);
lean_inc_ref(v_e_4143_);
lean_inc_ref(v_struct_4201_);
v___f_4202_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4202_, 0, v_struct_4201_);
lean_closure_set(v___f_4202_, 1, v_e_4143_);
lean_closure_set(v___f_4202_, 2, v_typeName_4199_);
lean_closure_set(v___f_4202_, 3, v_idx_4200_);
v___x_4203_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4143_, v___f_4202_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4203_;
}
default: 
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
lean_inc_ref(v_e_4143_);
v___x_4204_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4204_, 0, v_e_4143_);
v___x_4205_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4143_, v___x_4204_, v___y_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4205_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4206_; double v___x_4207_; 
v___x_4206_ = lean_unsigned_to_nat(1000000000u);
v___x_4207_ = lean_float_of_nat(v___x_4206_);
return v___x_4207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v_toCold_4216_; lean_object* v_options_4217_; uint8_t v_hasTrace_4218_; 
v_toCold_4216_ = lean_ctor_get(v_a_4213_, 0);
v_options_4217_ = lean_ctor_get(v_toCold_4216_, 2);
v_hasTrace_4218_ = lean_ctor_get_uint8(v_options_4217_, sizeof(void*)*1);
if (v_hasTrace_4218_ == 0)
{
lean_object* v___x_4219_; 
v___x_4219_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
return v___x_4219_;
}
else
{
lean_object* v_inheritedTraceOptions_4220_; lean_object* v___f_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; uint8_t v___x_4225_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v_a_4229_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v_a_4244_; 
v_inheritedTraceOptions_4220_ = lean_ctor_get(v_toCold_4216_, 11);
lean_inc_ref(v_e_4208_);
v___f_4221_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4221_, 0, v_e_4208_);
v___x_4222_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4223_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4224_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4225_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4220_, v_options_4217_, v___x_4224_);
if (v___x_4225_ == 0)
{
lean_object* v___x_4302_; uint8_t v___x_4303_; 
v___x_4302_ = l_Lean_trace_profiler;
v___x_4303_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4217_, v___x_4302_);
if (v___x_4303_ == 0)
{
lean_object* v___x_4304_; 
lean_dec_ref(v___f_4221_);
v___x_4304_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
return v___x_4304_;
}
else
{
goto v___jp_4253_;
}
}
else
{
goto v___jp_4253_;
}
v___jp_4226_:
{
lean_object* v___x_4230_; double v___x_4231_; double v___x_4232_; double v___x_4233_; double v___x_4234_; double v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4230_ = lean_io_mono_nanos_now();
v___x_4231_ = lean_float_of_nat(v___y_4227_);
v___x_4232_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4233_ = lean_float_div(v___x_4231_, v___x_4232_);
v___x_4234_ = lean_float_of_nat(v___x_4230_);
v___x_4235_ = lean_float_div(v___x_4234_, v___x_4232_);
v___x_4236_ = lean_box_float(v___x_4233_);
v___x_4237_ = lean_box_float(v___x_4235_);
v___x_4238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4236_);
lean_ctor_set(v___x_4238_, 1, v___x_4237_);
v___x_4239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4239_, 0, v_a_4229_);
lean_ctor_set(v___x_4239_, 1, v___x_4238_);
v___x_4240_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4222_, v_hasTrace_4218_, v___x_4223_, v_options_4217_, v___x_4225_, v___y_4228_, v___f_4221_, v___x_4239_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
return v___x_4240_;
}
v___jp_4241_:
{
lean_object* v___x_4245_; double v___x_4246_; double v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4245_ = lean_io_get_num_heartbeats();
v___x_4246_ = lean_float_of_nat(v___y_4242_);
v___x_4247_ = lean_float_of_nat(v___x_4245_);
v___x_4248_ = lean_box_float(v___x_4246_);
v___x_4249_ = lean_box_float(v___x_4247_);
v___x_4250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4251_, 0, v_a_4244_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
v___x_4252_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4222_, v_hasTrace_4218_, v___x_4223_, v_options_4217_, v___x_4225_, v___y_4243_, v___f_4221_, v___x_4251_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
return v___x_4252_;
}
v___jp_4253_:
{
lean_object* v___x_4254_; 
v___x_4254_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4214_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4254_, 1);
v___x_4256_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4257_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4217_, v___x_4256_);
if (v___x_4257_ == 0)
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4258_ = lean_io_mono_nanos_now();
v___x_4259_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4259_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4259_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
lean_ctor_set_tag(v___x_4262_, 1);
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
v___y_4227_ = v___x_4258_;
v___y_4228_ = v_a_4255_;
v_a_4229_ = v___x_4265_;
goto v___jp_4226_;
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
v_a_4268_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4259_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4259_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
lean_ctor_set_tag(v___x_4270_, 0);
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
v___y_4227_ = v___x_4258_;
v___y_4228_ = v_a_4255_;
v_a_4229_ = v___x_4273_;
goto v___jp_4226_;
}
}
}
}
else
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = lean_io_get_num_heartbeats();
v___x_4277_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_, v_a_4214_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4277_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4277_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set_tag(v___x_4280_, 1);
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
v___y_4242_ = v___x_4276_;
v___y_4243_ = v_a_4255_;
v_a_4244_ = v___x_4283_;
goto v___jp_4241_;
}
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
v_a_4286_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4277_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4277_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
lean_ctor_set_tag(v___x_4288_, 0);
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
v___y_4242_ = v___x_4276_;
v___y_4243_ = v_a_4255_;
v_a_4244_ = v___x_4291_;
goto v___jp_4241_;
}
}
}
}
}
else
{
lean_object* v_a_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4301_; 
lean_dec_ref(v___f_4221_);
lean_dec_ref(v_e_4208_);
v_a_4294_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4301_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4301_ == 0)
{
v___x_4296_ = v___x_4254_;
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_a_4294_);
lean_dec(v___x_4254_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4301_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4299_; 
if (v_isShared_4297_ == 0)
{
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
return v___x_4299_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4305_, lean_object* v_e_4306_, lean_object* v_typeName_4307_, lean_object* v_idx_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_, lean_object* v___y_4314_){
_start:
{
lean_object* v___x_4316_; 
v___x_4316_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4305_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; lean_object* v___x_4318_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc(v_a_4317_);
lean_dec_ref_known(v___x_4316_, 1);
v___x_4318_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4306_, v_typeName_4307_, v_idx_4308_, v_a_4317_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_, v___y_4313_, v___y_4314_);
return v___x_4318_;
}
else
{
lean_dec(v_idx_4308_);
lean_dec(v_typeName_4307_);
lean_dec_ref(v_e_4306_);
return v___x_4316_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4319_, v_a_4320_, v_a_4321_, v_a_4322_, v_a_4323_, v_a_4324_, v_a_4325_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
lean_dec_ref(v_a_4322_);
lean_dec(v_a_4321_);
lean_dec(v_a_4320_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4328_, lean_object* v_fvars_4329_, lean_object* v_doms_4330_, lean_object* v_e_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4328_, v_fvars_4329_, v_doms_4330_, v_e_4331_, v_a_4332_, v_a_4333_, v_a_4334_, v_a_4335_, v_a_4336_, v_a_4337_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
lean_dec(v_a_4335_);
lean_dec_ref(v_a_4334_);
lean_dec(v_a_4333_);
lean_dec(v_a_4332_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_){
_start:
{
lean_object* v_res_4348_; 
v_res_4348_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_, v___y_4345_, v___y_4346_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec(v___y_4341_);
return v_res_4348_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4349_, lean_object* v_fvars_4350_, lean_object* v_e_4351_, lean_object* v_letFVars_4352_, lean_object* v_a_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4349_, v_fvars_4350_, v_e_4351_, v_letFVars_4352_, v_a_4353_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
lean_dec(v_a_4358_);
lean_dec_ref(v_a_4357_);
lean_dec(v_a_4356_);
lean_dec_ref(v_a_4355_);
lean_dec(v_a_4354_);
lean_dec(v_a_4353_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4361_, lean_object* v_lctx_4362_, lean_object* v_localInsts_4363_, lean_object* v_x_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; 
v___x_4372_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4362_, v_localInsts_4363_, v_x_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
return v___x_4372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4373_, lean_object* v_lctx_4374_, lean_object* v_localInsts_4375_, lean_object* v_x_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4373_, v_lctx_4374_, v_localInsts_4375_, v_x_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
lean_dec(v___y_4380_);
lean_dec_ref(v___y_4379_);
lean_dec(v___y_4378_);
lean_dec(v___y_4377_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4385_, lean_object* v_lctx_4386_, lean_object* v_x_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v___x_4395_; 
v___x_4395_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4386_, v_x_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
return v___x_4395_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4396_, lean_object* v_lctx_4397_, lean_object* v_x_4398_, lean_object* v___y_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v_res_4406_; 
v_res_4406_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4396_, v_lctx_4397_, v_x_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
lean_dec(v___y_4402_);
lean_dec_ref(v___y_4401_);
lean_dec(v___y_4400_);
lean_dec(v___y_4399_);
return v_res_4406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v___x_4414_; 
v___x_4414_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4412_);
return v___x_4414_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v_res_4422_; 
v_res_4422_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4415_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_, v___y_4420_);
lean_dec(v___y_4420_);
lean_dec_ref(v___y_4419_);
lean_dec(v___y_4418_);
lean_dec_ref(v___y_4417_);
lean_dec(v___y_4416_);
lean_dec(v___y_4415_);
return v_res_4422_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4428_);
return v___x_4430_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
lean_dec(v___y_4432_);
lean_dec(v___y_4431_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4439_, lean_object* v_x_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_){
_start:
{
lean_object* v___x_4448_; 
v___x_4448_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4440_);
return v___x_4448_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4449_, lean_object* v_x_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_){
_start:
{
lean_object* v_res_4458_; 
v_res_4458_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4449_, v_x_4450_, v___y_4451_, v___y_4452_, v___y_4453_, v___y_4454_, v___y_4455_, v___y_4456_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
lean_dec(v___y_4454_);
lean_dec_ref(v___y_4453_);
lean_dec(v___y_4452_);
lean_dec(v___y_4451_);
return v_res_4458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4459_, lean_object* v_data_4460_, lean_object* v_ref_4461_, lean_object* v_msg_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
lean_object* v___x_4470_; 
v___x_4470_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4459_, v_data_4460_, v_ref_4461_, v_msg_4462_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
return v___x_4470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4471_, lean_object* v_data_4472_, lean_object* v_ref_4473_, lean_object* v_msg_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_, lean_object* v___y_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_){
_start:
{
lean_object* v_res_4482_; 
v_res_4482_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4471_, v_data_4472_, v_ref_4473_, v_msg_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_, v___y_4479_, v___y_4480_);
lean_dec(v___y_4480_);
lean_dec_ref(v___y_4479_);
lean_dec(v___y_4478_);
lean_dec_ref(v___y_4477_);
lean_dec(v___y_4476_);
lean_dec(v___y_4475_);
return v_res_4482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; lean_object* v_traceState_4486_; lean_object* v_traces_4487_; lean_object* v___x_4488_; lean_object* v_traceState_4489_; lean_object* v_env_4490_; lean_object* v_nextMacroScope_4491_; lean_object* v_ngen_4492_; lean_object* v_auxDeclNGen_4493_; lean_object* v_cache_4494_; lean_object* v_recordedDeps_4495_; lean_object* v_messages_4496_; lean_object* v_infoState_4497_; lean_object* v_snapshotTasks_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4519_; 
v___x_4485_ = lean_st_ref_get(v___y_4483_);
v_traceState_4486_ = lean_ctor_get(v___x_4485_, 4);
lean_inc_ref(v_traceState_4486_);
lean_dec(v___x_4485_);
v_traces_4487_ = lean_ctor_get(v_traceState_4486_, 0);
lean_inc_ref(v_traces_4487_);
lean_dec_ref(v_traceState_4486_);
v___x_4488_ = lean_st_ref_take(v___y_4483_);
v_traceState_4489_ = lean_ctor_get(v___x_4488_, 4);
v_env_4490_ = lean_ctor_get(v___x_4488_, 0);
v_nextMacroScope_4491_ = lean_ctor_get(v___x_4488_, 1);
v_ngen_4492_ = lean_ctor_get(v___x_4488_, 2);
v_auxDeclNGen_4493_ = lean_ctor_get(v___x_4488_, 3);
v_cache_4494_ = lean_ctor_get(v___x_4488_, 5);
v_recordedDeps_4495_ = lean_ctor_get(v___x_4488_, 6);
v_messages_4496_ = lean_ctor_get(v___x_4488_, 7);
v_infoState_4497_ = lean_ctor_get(v___x_4488_, 8);
v_snapshotTasks_4498_ = lean_ctor_get(v___x_4488_, 9);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4488_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4500_ = v___x_4488_;
v_isShared_4501_ = v_isSharedCheck_4519_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_snapshotTasks_4498_);
lean_inc(v_infoState_4497_);
lean_inc(v_messages_4496_);
lean_inc(v_recordedDeps_4495_);
lean_inc(v_cache_4494_);
lean_inc(v_traceState_4489_);
lean_inc(v_auxDeclNGen_4493_);
lean_inc(v_ngen_4492_);
lean_inc(v_nextMacroScope_4491_);
lean_inc(v_env_4490_);
lean_dec(v___x_4488_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4519_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
uint64_t v_tid_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4517_; 
v_tid_4502_ = lean_ctor_get_uint64(v_traceState_4489_, sizeof(void*)*1);
v_isSharedCheck_4517_ = !lean_is_exclusive(v_traceState_4489_);
if (v_isSharedCheck_4517_ == 0)
{
lean_object* v_unused_4518_; 
v_unused_4518_ = lean_ctor_get(v_traceState_4489_, 0);
lean_dec(v_unused_4518_);
v___x_4504_ = v_traceState_4489_;
v_isShared_4505_ = v_isSharedCheck_4517_;
goto v_resetjp_4503_;
}
else
{
lean_dec(v_traceState_4489_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4517_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4510_; 
v___x_4506_ = lean_unsigned_to_nat(32u);
v___x_4507_ = lean_mk_empty_array_with_capacity(v___x_4506_);
lean_dec_ref(v___x_4507_);
v___x_4508_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 0, v___x_4508_);
v___x_4510_ = v___x_4504_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v___x_4508_);
lean_ctor_set_uint64(v_reuseFailAlloc_4516_, sizeof(void*)*1, v_tid_4502_);
v___x_4510_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
lean_object* v___x_4512_; 
if (v_isShared_4501_ == 0)
{
lean_ctor_set(v___x_4500_, 4, v___x_4510_);
v___x_4512_ = v___x_4500_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_env_4490_);
lean_ctor_set(v_reuseFailAlloc_4515_, 1, v_nextMacroScope_4491_);
lean_ctor_set(v_reuseFailAlloc_4515_, 2, v_ngen_4492_);
lean_ctor_set(v_reuseFailAlloc_4515_, 3, v_auxDeclNGen_4493_);
lean_ctor_set(v_reuseFailAlloc_4515_, 4, v___x_4510_);
lean_ctor_set(v_reuseFailAlloc_4515_, 5, v_cache_4494_);
lean_ctor_set(v_reuseFailAlloc_4515_, 6, v_recordedDeps_4495_);
lean_ctor_set(v_reuseFailAlloc_4515_, 7, v_messages_4496_);
lean_ctor_set(v_reuseFailAlloc_4515_, 8, v_infoState_4497_);
lean_ctor_set(v_reuseFailAlloc_4515_, 9, v_snapshotTasks_4498_);
v___x_4512_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = lean_st_ref_put(v___y_4483_, v___x_4512_);
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v_traces_4487_);
return v___x_4514_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4520_);
lean_dec(v___y_4520_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___x_4528_; 
v___x_4528_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4526_);
return v___x_4528_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4535_, lean_object* v_msg_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v_ref_4542_; lean_object* v___x_4543_; lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4589_; 
v_ref_4542_ = lean_ctor_get(v___y_4539_, 2);
v___x_4543_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
v_a_4544_ = lean_ctor_get(v___x_4543_, 0);
v_isSharedCheck_4589_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4589_ == 0)
{
v___x_4546_ = v___x_4543_;
v_isShared_4547_ = v_isSharedCheck_4589_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4543_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4589_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4548_; lean_object* v_traceState_4549_; lean_object* v_env_4550_; lean_object* v_nextMacroScope_4551_; lean_object* v_ngen_4552_; lean_object* v_auxDeclNGen_4553_; lean_object* v_cache_4554_; lean_object* v_recordedDeps_4555_; lean_object* v_messages_4556_; lean_object* v_infoState_4557_; lean_object* v_snapshotTasks_4558_; lean_object* v___x_4560_; uint8_t v_isShared_4561_; uint8_t v_isSharedCheck_4588_; 
v___x_4548_ = lean_st_ref_take(v___y_4540_);
v_traceState_4549_ = lean_ctor_get(v___x_4548_, 4);
v_env_4550_ = lean_ctor_get(v___x_4548_, 0);
v_nextMacroScope_4551_ = lean_ctor_get(v___x_4548_, 1);
v_ngen_4552_ = lean_ctor_get(v___x_4548_, 2);
v_auxDeclNGen_4553_ = lean_ctor_get(v___x_4548_, 3);
v_cache_4554_ = lean_ctor_get(v___x_4548_, 5);
v_recordedDeps_4555_ = lean_ctor_get(v___x_4548_, 6);
v_messages_4556_ = lean_ctor_get(v___x_4548_, 7);
v_infoState_4557_ = lean_ctor_get(v___x_4548_, 8);
v_snapshotTasks_4558_ = lean_ctor_get(v___x_4548_, 9);
v_isSharedCheck_4588_ = !lean_is_exclusive(v___x_4548_);
if (v_isSharedCheck_4588_ == 0)
{
v___x_4560_ = v___x_4548_;
v_isShared_4561_ = v_isSharedCheck_4588_;
goto v_resetjp_4559_;
}
else
{
lean_inc(v_snapshotTasks_4558_);
lean_inc(v_infoState_4557_);
lean_inc(v_messages_4556_);
lean_inc(v_recordedDeps_4555_);
lean_inc(v_cache_4554_);
lean_inc(v_traceState_4549_);
lean_inc(v_auxDeclNGen_4553_);
lean_inc(v_ngen_4552_);
lean_inc(v_nextMacroScope_4551_);
lean_inc(v_env_4550_);
lean_dec(v___x_4548_);
v___x_4560_ = lean_box(0);
v_isShared_4561_ = v_isSharedCheck_4588_;
goto v_resetjp_4559_;
}
v_resetjp_4559_:
{
uint64_t v_tid_4562_; lean_object* v_traces_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4587_; 
v_tid_4562_ = lean_ctor_get_uint64(v_traceState_4549_, sizeof(void*)*1);
v_traces_4563_ = lean_ctor_get(v_traceState_4549_, 0);
v_isSharedCheck_4587_ = !lean_is_exclusive(v_traceState_4549_);
if (v_isSharedCheck_4587_ == 0)
{
v___x_4565_ = v_traceState_4549_;
v_isShared_4566_ = v_isSharedCheck_4587_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_traces_4563_);
lean_dec(v_traceState_4549_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4587_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4567_; lean_object* v___x_4568_; double v___x_4569_; uint8_t v___x_4570_; lean_object* v___x_4571_; lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4578_; 
v___x_4567_ = lean_box(0);
v___x_4568_ = lean_box(0);
v___x_4569_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4570_ = 0;
v___x_4571_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4572_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4572_, 0, v_cls_4535_);
lean_ctor_set(v___x_4572_, 1, v___x_4568_);
lean_ctor_set(v___x_4572_, 2, v___x_4571_);
lean_ctor_set_float(v___x_4572_, sizeof(void*)*3, v___x_4569_);
lean_ctor_set_float(v___x_4572_, sizeof(void*)*3 + 8, v___x_4569_);
lean_ctor_set_uint8(v___x_4572_, sizeof(void*)*3 + 16, v___x_4570_);
v___x_4573_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4574_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4572_);
lean_ctor_set(v___x_4574_, 1, v_a_4544_);
lean_ctor_set(v___x_4574_, 2, v___x_4573_);
lean_inc(v_ref_4542_);
v___x_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4575_, 0, v_ref_4542_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
v___x_4576_ = l_Lean_PersistentArray_push___redArg(v_traces_4563_, v___x_4575_);
if (v_isShared_4566_ == 0)
{
lean_ctor_set(v___x_4565_, 0, v___x_4576_);
v___x_4578_ = v___x_4565_;
goto v_reusejp_4577_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4576_);
lean_ctor_set_uint64(v_reuseFailAlloc_4586_, sizeof(void*)*1, v_tid_4562_);
v___x_4578_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4577_;
}
v_reusejp_4577_:
{
lean_object* v___x_4580_; 
if (v_isShared_4561_ == 0)
{
lean_ctor_set(v___x_4560_, 4, v___x_4578_);
v___x_4580_ = v___x_4560_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_env_4550_);
lean_ctor_set(v_reuseFailAlloc_4585_, 1, v_nextMacroScope_4551_);
lean_ctor_set(v_reuseFailAlloc_4585_, 2, v_ngen_4552_);
lean_ctor_set(v_reuseFailAlloc_4585_, 3, v_auxDeclNGen_4553_);
lean_ctor_set(v_reuseFailAlloc_4585_, 4, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4585_, 5, v_cache_4554_);
lean_ctor_set(v_reuseFailAlloc_4585_, 6, v_recordedDeps_4555_);
lean_ctor_set(v_reuseFailAlloc_4585_, 7, v_messages_4556_);
lean_ctor_set(v_reuseFailAlloc_4585_, 8, v_infoState_4557_);
lean_ctor_set(v_reuseFailAlloc_4585_, 9, v_snapshotTasks_4558_);
v___x_4580_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4581_ = lean_st_ref_put(v___y_4540_, v___x_4580_);
if (v_isShared_4547_ == 0)
{
lean_ctor_set(v___x_4546_, 0, v___x_4567_);
v___x_4583_ = v___x_4546_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4584_; 
v_reuseFailAlloc_4584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4584_, 0, v___x_4567_);
v___x_4583_ = v_reuseFailAlloc_4584_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
return v___x_4583_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4590_, lean_object* v_msg_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_){
_start:
{
lean_object* v_res_4597_; 
v_res_4597_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4590_, v_msg_4591_, v___y_4592_, v___y_4593_, v___y_4594_, v___y_4595_);
lean_dec(v___y_4595_);
lean_dec_ref(v___y_4594_);
lean_dec(v___y_4593_);
lean_dec_ref(v___y_4592_);
return v_res_4597_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__0));
v___x_4600_ = l_Lean_stringToMessageData(v___x_4599_);
return v___x_4600_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; 
v___x_4602_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__2));
v___x_4603_ = l_Lean_stringToMessageData(v___x_4602_);
return v___x_4603_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__4));
v___x_4606_ = l_Lean_stringToMessageData(v___x_4605_);
return v___x_4606_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7(void){
_start:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; 
v___x_4608_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__6));
v___x_4609_ = l_Lean_stringToMessageData(v___x_4608_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___x_4610_, lean_object* v_e_4611_, lean_object* v___x_4612_, lean_object* v___x_4613_, lean_object* v_cls_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_st_mk_ref(v___x_4610_);
v___x_4621_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4611_, v___x_4612_, v___x_4620_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4624_; uint8_t v_isShared_4625_; uint8_t v_isSharedCheck_4693_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4624_ = v___x_4621_;
v_isShared_4625_ = v_isSharedCheck_4693_;
goto v_resetjp_4623_;
}
else
{
lean_inc(v_a_4622_);
lean_dec(v___x_4621_);
v___x_4624_ = lean_box(0);
v_isShared_4625_ = v_isSharedCheck_4693_;
goto v_resetjp_4623_;
}
v_resetjp_4623_:
{
lean_object* v___x_4626_; lean_object* v_count_4627_; lean_object* v___x_4629_; uint8_t v_isShared_4630_; uint8_t v_isSharedCheck_4691_; 
v___x_4626_ = lean_st_ref_get(v___x_4620_);
lean_dec(v___x_4620_);
v_count_4627_ = lean_ctor_get(v___x_4626_, 0);
v_isSharedCheck_4691_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4691_ == 0)
{
lean_object* v_unused_4692_; 
v_unused_4692_ = lean_ctor_get(v___x_4626_, 1);
lean_dec(v_unused_4692_);
v___x_4629_ = v___x_4626_;
v_isShared_4630_ = v_isSharedCheck_4691_;
goto v_resetjp_4628_;
}
else
{
lean_inc(v_count_4627_);
lean_dec(v___x_4626_);
v___x_4629_ = lean_box(0);
v_isShared_4630_ = v_isSharedCheck_4691_;
goto v_resetjp_4628_;
}
v_resetjp_4628_:
{
uint8_t v___x_4653_; 
v___x_4653_ = lean_nat_dec_eq(v_count_4627_, v___x_4613_);
if (v___x_4653_ == 0)
{
lean_object* v_toCold_4654_; lean_object* v_options_4655_; uint8_t v_hasTrace_4656_; 
v_toCold_4654_ = lean_ctor_get(v___y_4617_, 0);
v_options_4655_ = lean_ctor_get(v_toCold_4654_, 2);
v_hasTrace_4656_ = lean_ctor_get_uint8(v_options_4655_, sizeof(void*)*1);
if (v_hasTrace_4656_ == 0)
{
lean_dec(v_cls_4614_);
goto v___jp_4631_;
}
else
{
lean_object* v_inheritedTraceOptions_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
v_inheritedTraceOptions_4657_ = lean_ctor_get(v_toCold_4654_, 11);
v___x_4658_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4614_);
v___x_4659_ = l_Lean_Name_append(v___x_4658_, v_cls_4614_);
v___x_4660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4657_, v_options_4655_, v___x_4659_);
lean_dec(v___x_4659_);
if (v___x_4660_ == 0)
{
lean_dec(v_cls_4614_);
goto v___jp_4631_;
}
else
{
lean_object* v_expr_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v_expr_4661_ = lean_ctor_get(v_a_4622_, 0);
v___x_4662_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__5);
lean_inc_ref(v_expr_4661_);
v___x_4663_ = l_Lean_indentExpr(v_expr_4661_);
v___x_4664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4662_);
lean_ctor_set(v___x_4664_, 1, v___x_4663_);
v___x_4665_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4614_, v___x_4664_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_dec_ref_known(v___x_4665_, 1);
goto v___jp_4631_;
}
else
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
lean_del_object(v___x_4629_);
lean_dec(v_count_4627_);
lean_del_object(v___x_4624_);
lean_dec(v_a_4622_);
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4674_; lean_object* v_options_4675_; uint8_t v_hasTrace_4676_; 
v_toCold_4674_ = lean_ctor_get(v___y_4617_, 0);
v_options_4675_ = lean_ctor_get(v_toCold_4674_, 2);
v_hasTrace_4676_ = lean_ctor_get_uint8(v_options_4675_, sizeof(void*)*1);
if (v_hasTrace_4676_ == 0)
{
lean_dec(v_cls_4614_);
goto v___jp_4631_;
}
else
{
lean_object* v_inheritedTraceOptions_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; uint8_t v___x_4680_; 
v_inheritedTraceOptions_4677_ = lean_ctor_get(v_toCold_4674_, 11);
v___x_4678_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4614_);
v___x_4679_ = l_Lean_Name_append(v___x_4678_, v_cls_4614_);
v___x_4680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4677_, v_options_4675_, v___x_4679_);
lean_dec(v___x_4679_);
if (v___x_4680_ == 0)
{
lean_dec(v_cls_4614_);
goto v___jp_4631_;
}
else
{
lean_object* v___x_4681_; lean_object* v___x_4682_; 
v___x_4681_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__7);
v___x_4682_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4614_, v___x_4681_, v___y_4615_, v___y_4616_, v___y_4617_, v___y_4618_);
if (lean_obj_tag(v___x_4682_) == 0)
{
lean_dec_ref_known(v___x_4682_, 1);
goto v___jp_4631_;
}
else
{
lean_object* v_a_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4690_; 
lean_del_object(v___x_4629_);
lean_dec(v_count_4627_);
lean_del_object(v___x_4624_);
lean_dec(v_a_4622_);
v_a_4683_ = lean_ctor_get(v___x_4682_, 0);
v_isSharedCheck_4690_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4690_ == 0)
{
v___x_4685_ = v___x_4682_;
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_a_4683_);
lean_dec(v___x_4682_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4690_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v___x_4688_; 
if (v_isShared_4686_ == 0)
{
v___x_4688_ = v___x_4685_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_a_4683_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
}
}
}
}
v___jp_4631_:
{
lean_object* v_expr_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4651_; 
v_expr_4632_ = lean_ctor_get(v_a_4622_, 0);
v_isSharedCheck_4651_ = !lean_is_exclusive(v_a_4622_);
if (v_isSharedCheck_4651_ == 0)
{
lean_object* v_unused_4652_; 
v_unused_4652_ = lean_ctor_get(v_a_4622_, 1);
lean_dec(v_unused_4652_);
v___x_4634_ = v_a_4622_;
v_isShared_4635_ = v_isSharedCheck_4651_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_expr_4632_);
lean_dec(v_a_4622_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4651_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; lean_object* v___x_4641_; 
v___x_4636_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__1);
v___x_4637_ = l_Nat_reprFast(v_count_4627_);
v___x_4638_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___x_4637_);
v___x_4639_ = l_Lean_MessageData_ofFormat(v___x_4638_);
if (v_isShared_4635_ == 0)
{
lean_ctor_set_tag(v___x_4634_, 7);
lean_ctor_set(v___x_4634_, 1, v___x_4639_);
lean_ctor_set(v___x_4634_, 0, v___x_4636_);
v___x_4641_ = v___x_4634_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4650_; 
v_reuseFailAlloc_4650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4650_, 0, v___x_4636_);
lean_ctor_set(v_reuseFailAlloc_4650_, 1, v___x_4639_);
v___x_4641_ = v_reuseFailAlloc_4650_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
lean_object* v___x_4642_; lean_object* v___x_4644_; 
v___x_4642_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___closed__3);
if (v_isShared_4630_ == 0)
{
lean_ctor_set_tag(v___x_4629_, 7);
lean_ctor_set(v___x_4629_, 1, v___x_4642_);
lean_ctor_set(v___x_4629_, 0, v___x_4641_);
v___x_4644_ = v___x_4629_;
goto v_reusejp_4643_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v___x_4642_);
v___x_4644_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4643_;
}
v_reusejp_4643_:
{
lean_object* v___x_4645_; lean_object* v___x_4647_; 
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v_expr_4632_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
if (v_isShared_4625_ == 0)
{
lean_ctor_set(v___x_4624_, 0, v___x_4645_);
v___x_4647_ = v___x_4624_;
goto v_reusejp_4646_;
}
else
{
lean_object* v_reuseFailAlloc_4648_; 
v_reuseFailAlloc_4648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4648_, 0, v___x_4645_);
v___x_4647_ = v_reuseFailAlloc_4648_;
goto v_reusejp_4646_;
}
v_reusejp_4646_:
{
return v___x_4647_;
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
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_dec(v___x_4620_);
lean_dec(v_cls_4614_);
v_a_4694_ = lean_ctor_get(v___x_4621_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4621_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4621_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4621_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___x_4702_, lean_object* v_e_4703_, lean_object* v___x_4704_, lean_object* v___x_4705_, lean_object* v_cls_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_){
_start:
{
lean_object* v_res_4712_; 
v_res_4712_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___x_4702_, v_e_4703_, v___x_4704_, v___x_4705_, v_cls_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec(v___y_4708_);
lean_dec_ref(v___y_4707_);
lean_dec(v___x_4705_);
lean_dec(v___x_4704_);
return v_res_4712_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0(void){
_start:
{
uint8_t v___x_4713_; lean_object* v___x_4714_; 
v___x_4713_ = 2;
v___x_4714_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_4713_);
return v___x_4714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(uint8_t v___x_4715_, lean_object* v___f_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v___x_4767_; uint8_t v_beta_4768_; 
v___x_4767_ = l_Lean_Meta_Context_config(v___y_4717_);
v_beta_4768_ = lean_ctor_get_uint8(v___x_4767_, 13);
if (v_beta_4768_ == 0)
{
lean_dec_ref(v___x_4767_);
goto v___jp_4722_;
}
else
{
uint8_t v_iota_4769_; 
v_iota_4769_ = lean_ctor_get_uint8(v___x_4767_, 12);
if (v_iota_4769_ == 0)
{
lean_dec_ref(v___x_4767_);
goto v___jp_4722_;
}
else
{
uint8_t v_zeta_4770_; 
v_zeta_4770_ = lean_ctor_get_uint8(v___x_4767_, 15);
if (v_zeta_4770_ == 0)
{
lean_dec_ref(v___x_4767_);
goto v___jp_4722_;
}
else
{
uint8_t v_zetaHave_4771_; 
v_zetaHave_4771_ = lean_ctor_get_uint8(v___x_4767_, 18);
if (v_zetaHave_4771_ == 0)
{
lean_dec_ref(v___x_4767_);
goto v___jp_4722_;
}
else
{
uint8_t v_zetaDelta_4772_; 
v_zetaDelta_4772_ = lean_ctor_get_uint8(v___x_4767_, 16);
if (v_zetaDelta_4772_ == 0)
{
lean_dec_ref(v___x_4767_);
goto v___jp_4722_;
}
else
{
uint8_t v_etaStruct_4773_; uint8_t v_proj_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; uint8_t v___x_4777_; 
v_etaStruct_4773_ = lean_ctor_get_uint8(v___x_4767_, 10);
v_proj_4774_ = lean_ctor_get_uint8(v___x_4767_, 14);
lean_dec_ref(v___x_4767_);
v___x_4775_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_4774_);
v___x_4776_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0);
v___x_4777_ = lean_nat_dec_eq(v___x_4775_, v___x_4776_);
lean_dec(v___x_4775_);
if (v___x_4777_ == 0)
{
goto v___jp_4722_;
}
else
{
uint8_t v___x_4778_; uint8_t v___x_4779_; 
v___x_4778_ = 0;
v___x_4779_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4773_, v___x_4778_);
if (v___x_4779_ == 0)
{
goto v___jp_4722_;
}
else
{
lean_object* v___x_4780_; 
v___x_4780_ = lean_apply_5(v___f_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_, lean_box(0));
return v___x_4780_;
}
}
}
}
}
}
}
v___jp_4722_:
{
lean_object* v___x_4723_; uint8_t v_foApprox_4724_; uint8_t v_ctxApprox_4725_; uint8_t v_quasiPatternApprox_4726_; uint8_t v_constApprox_4727_; uint8_t v_isDefEqStuckEx_4728_; uint8_t v_unificationHints_4729_; uint8_t v_proofIrrelevance_4730_; uint8_t v_assignSyntheticOpaque_4731_; uint8_t v_offsetCnstrs_4732_; uint8_t v_transparency_4733_; uint8_t v_univApprox_4734_; uint8_t v_zetaUnused_4735_; uint8_t v_canUnfoldPredicateConfig_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4766_; 
v___x_4723_ = l_Lean_Meta_Context_config(v___y_4717_);
v_foApprox_4724_ = lean_ctor_get_uint8(v___x_4723_, 0);
v_ctxApprox_4725_ = lean_ctor_get_uint8(v___x_4723_, 1);
v_quasiPatternApprox_4726_ = lean_ctor_get_uint8(v___x_4723_, 2);
v_constApprox_4727_ = lean_ctor_get_uint8(v___x_4723_, 3);
v_isDefEqStuckEx_4728_ = lean_ctor_get_uint8(v___x_4723_, 4);
v_unificationHints_4729_ = lean_ctor_get_uint8(v___x_4723_, 5);
v_proofIrrelevance_4730_ = lean_ctor_get_uint8(v___x_4723_, 6);
v_assignSyntheticOpaque_4731_ = lean_ctor_get_uint8(v___x_4723_, 7);
v_offsetCnstrs_4732_ = lean_ctor_get_uint8(v___x_4723_, 8);
v_transparency_4733_ = lean_ctor_get_uint8(v___x_4723_, 9);
v_univApprox_4734_ = lean_ctor_get_uint8(v___x_4723_, 11);
v_zetaUnused_4735_ = lean_ctor_get_uint8(v___x_4723_, 17);
v_canUnfoldPredicateConfig_4736_ = lean_ctor_get_uint8(v___x_4723_, 19);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4723_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4738_ = v___x_4723_;
v_isShared_4739_ = v_isSharedCheck_4766_;
goto v_resetjp_4737_;
}
else
{
lean_dec(v___x_4723_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4766_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
uint8_t v___x_4740_; uint8_t v___x_4741_; lean_object* v___x_4743_; 
v___x_4740_ = 0;
v___x_4741_ = 2;
if (v_isShared_4739_ == 0)
{
v___x_4743_ = v___x_4738_;
goto v_reusejp_4742_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 0, v_foApprox_4724_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 1, v_ctxApprox_4725_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 2, v_quasiPatternApprox_4726_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 3, v_constApprox_4727_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 4, v_isDefEqStuckEx_4728_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 5, v_unificationHints_4729_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 6, v_proofIrrelevance_4730_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 7, v_assignSyntheticOpaque_4731_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 8, v_offsetCnstrs_4732_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 9, v_transparency_4733_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 11, v_univApprox_4734_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 17, v_zetaUnused_4735_);
lean_ctor_set_uint8(v_reuseFailAlloc_4765_, 19, v_canUnfoldPredicateConfig_4736_);
v___x_4743_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4742_;
}
v_reusejp_4742_:
{
uint8_t v_trackZetaDelta_4744_; lean_object* v_zetaDeltaSet_4745_; lean_object* v_lctx_4746_; lean_object* v_localInstances_4747_; lean_object* v_defEqCtx_x3f_4748_; lean_object* v_synthPendingDepth_4749_; lean_object* v_customCanUnfoldPredicate_x3f_4750_; uint8_t v_univApprox_4751_; uint8_t v_inTypeClassResolution_4752_; uint8_t v_cacheInferType_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4763_; 
lean_ctor_set_uint8(v___x_4743_, 10, v___x_4740_);
lean_ctor_set_uint8(v___x_4743_, 12, v___x_4715_);
lean_ctor_set_uint8(v___x_4743_, 13, v___x_4715_);
lean_ctor_set_uint8(v___x_4743_, 14, v___x_4741_);
lean_ctor_set_uint8(v___x_4743_, 15, v___x_4715_);
lean_ctor_set_uint8(v___x_4743_, 16, v___x_4715_);
lean_ctor_set_uint8(v___x_4743_, 18, v___x_4715_);
v_trackZetaDelta_4744_ = lean_ctor_get_uint8(v___y_4717_, sizeof(void*)*7);
v_zetaDeltaSet_4745_ = lean_ctor_get(v___y_4717_, 1);
v_lctx_4746_ = lean_ctor_get(v___y_4717_, 2);
v_localInstances_4747_ = lean_ctor_get(v___y_4717_, 3);
v_defEqCtx_x3f_4748_ = lean_ctor_get(v___y_4717_, 4);
v_synthPendingDepth_4749_ = lean_ctor_get(v___y_4717_, 5);
v_customCanUnfoldPredicate_x3f_4750_ = lean_ctor_get(v___y_4717_, 6);
v_univApprox_4751_ = lean_ctor_get_uint8(v___y_4717_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4752_ = lean_ctor_get_uint8(v___y_4717_, sizeof(void*)*7 + 2);
v_cacheInferType_4753_ = lean_ctor_get_uint8(v___y_4717_, sizeof(void*)*7 + 3);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___y_4717_);
if (v_isSharedCheck_4763_ == 0)
{
lean_object* v_unused_4764_; 
v_unused_4764_ = lean_ctor_get(v___y_4717_, 0);
lean_dec(v_unused_4764_);
v___x_4755_ = v___y_4717_;
v_isShared_4756_ = v_isSharedCheck_4763_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4750_);
lean_inc(v_synthPendingDepth_4749_);
lean_inc(v_defEqCtx_x3f_4748_);
lean_inc(v_localInstances_4747_);
lean_inc(v_lctx_4746_);
lean_inc(v_zetaDeltaSet_4745_);
lean_dec(v___y_4717_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4763_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
uint64_t v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4760_; 
v___x_4757_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4743_);
v___x_4758_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4758_, 0, v___x_4743_);
lean_ctor_set_uint64(v___x_4758_, sizeof(void*)*1, v___x_4757_);
if (v_isShared_4756_ == 0)
{
lean_ctor_set(v___x_4755_, 0, v___x_4758_);
v___x_4760_ = v___x_4755_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v___x_4758_);
lean_ctor_set(v_reuseFailAlloc_4762_, 1, v_zetaDeltaSet_4745_);
lean_ctor_set(v_reuseFailAlloc_4762_, 2, v_lctx_4746_);
lean_ctor_set(v_reuseFailAlloc_4762_, 3, v_localInstances_4747_);
lean_ctor_set(v_reuseFailAlloc_4762_, 4, v_defEqCtx_x3f_4748_);
lean_ctor_set(v_reuseFailAlloc_4762_, 5, v_synthPendingDepth_4749_);
lean_ctor_set(v_reuseFailAlloc_4762_, 6, v_customCanUnfoldPredicate_x3f_4750_);
lean_ctor_set_uint8(v_reuseFailAlloc_4762_, sizeof(void*)*7, v_trackZetaDelta_4744_);
lean_ctor_set_uint8(v_reuseFailAlloc_4762_, sizeof(void*)*7 + 1, v_univApprox_4751_);
lean_ctor_set_uint8(v_reuseFailAlloc_4762_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4752_);
lean_ctor_set_uint8(v_reuseFailAlloc_4762_, sizeof(void*)*7 + 3, v_cacheInferType_4753_);
v___x_4760_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
lean_object* v___x_4761_; 
v___x_4761_ = lean_apply_5(v___f_4716_, v___x_4760_, v___y_4718_, v___y_4719_, v___y_4720_, lean_box(0));
return v___x_4761_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4781_, lean_object* v___f_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
uint8_t v___x_14056__boxed_4788_; lean_object* v_res_4789_; 
v___x_14056__boxed_4788_ = lean_unbox(v___x_4781_);
v_res_4789_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_14056__boxed_4788_, v___f_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
return v_res_4789_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4790_, lean_object* v_cache_4791_, lean_object* v_a_x3f_4792_){
_start:
{
lean_object* v___x_4794_; lean_object* v_mctx_4795_; lean_object* v_zetaDeltaFVarIds_4796_; lean_object* v_postponed_4797_; lean_object* v_diag_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4808_; 
v___x_4794_ = lean_st_ref_take(v___y_4790_);
v_mctx_4795_ = lean_ctor_get(v___x_4794_, 0);
v_zetaDeltaFVarIds_4796_ = lean_ctor_get(v___x_4794_, 2);
v_postponed_4797_ = lean_ctor_get(v___x_4794_, 3);
v_diag_4798_ = lean_ctor_get(v___x_4794_, 4);
v_isSharedCheck_4808_ = !lean_is_exclusive(v___x_4794_);
if (v_isSharedCheck_4808_ == 0)
{
lean_object* v_unused_4809_; 
v_unused_4809_ = lean_ctor_get(v___x_4794_, 1);
lean_dec(v_unused_4809_);
v___x_4800_ = v___x_4794_;
v_isShared_4801_ = v_isSharedCheck_4808_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_diag_4798_);
lean_inc(v_postponed_4797_);
lean_inc(v_zetaDeltaFVarIds_4796_);
lean_inc(v_mctx_4795_);
lean_dec(v___x_4794_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4808_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___x_4802_; lean_object* v___x_4804_; 
v___x_4802_ = lean_box(0);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 1, v_cache_4791_);
v___x_4804_ = v___x_4800_;
goto v_reusejp_4803_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_mctx_4795_);
lean_ctor_set(v_reuseFailAlloc_4807_, 1, v_cache_4791_);
lean_ctor_set(v_reuseFailAlloc_4807_, 2, v_zetaDeltaFVarIds_4796_);
lean_ctor_set(v_reuseFailAlloc_4807_, 3, v_postponed_4797_);
lean_ctor_set(v_reuseFailAlloc_4807_, 4, v_diag_4798_);
v___x_4804_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4803_;
}
v_reusejp_4803_:
{
lean_object* v___x_4805_; lean_object* v___x_4806_; 
v___x_4805_ = lean_st_ref_put(v___y_4790_, v___x_4804_);
v___x_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4802_);
return v___x_4806_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4810_, lean_object* v_cache_4811_, lean_object* v_a_x3f_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4810_, v_cache_4811_, v_a_x3f_4812_);
lean_dec(v_a_x3f_4812_);
lean_dec(v___y_4810_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(lean_object* v___y_4815_, lean_object* v_zetaDeltaFVarIds_4816_, lean_object* v_a_x3f_4817_){
_start:
{
lean_object* v___x_4819_; lean_object* v_mctx_4820_; lean_object* v_cache_4821_; lean_object* v_postponed_4822_; lean_object* v_diag_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4833_; 
v___x_4819_ = lean_st_ref_take(v___y_4815_);
v_mctx_4820_ = lean_ctor_get(v___x_4819_, 0);
v_cache_4821_ = lean_ctor_get(v___x_4819_, 1);
v_postponed_4822_ = lean_ctor_get(v___x_4819_, 3);
v_diag_4823_ = lean_ctor_get(v___x_4819_, 4);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4833_ == 0)
{
lean_object* v_unused_4834_; 
v_unused_4834_ = lean_ctor_get(v___x_4819_, 2);
lean_dec(v_unused_4834_);
v___x_4825_ = v___x_4819_;
v_isShared_4826_ = v_isSharedCheck_4833_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_diag_4823_);
lean_inc(v_postponed_4822_);
lean_inc(v_cache_4821_);
lean_inc(v_mctx_4820_);
lean_dec(v___x_4819_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4833_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4827_; lean_object* v___x_4829_; 
v___x_4827_ = lean_box(0);
if (v_isShared_4826_ == 0)
{
lean_ctor_set(v___x_4825_, 2, v_zetaDeltaFVarIds_4816_);
v___x_4829_ = v___x_4825_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_mctx_4820_);
lean_ctor_set(v_reuseFailAlloc_4832_, 1, v_cache_4821_);
lean_ctor_set(v_reuseFailAlloc_4832_, 2, v_zetaDeltaFVarIds_4816_);
lean_ctor_set(v_reuseFailAlloc_4832_, 3, v_postponed_4822_);
lean_ctor_set(v_reuseFailAlloc_4832_, 4, v_diag_4823_);
v___x_4829_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4830_ = lean_st_ref_put(v___y_4815_, v___x_4829_);
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4827_);
return v___x_4831_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___y_4835_, lean_object* v_zetaDeltaFVarIds_4836_, lean_object* v_a_x3f_4837_, lean_object* v___y_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4835_, v_zetaDeltaFVarIds_4836_, v_a_x3f_4837_);
lean_dec(v_a_x3f_4837_);
lean_dec(v___y_4835_);
return v_res_4839_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1));
v___x_4844_ = l_Lean_MessageData_ofFormat(v___x_4843_);
return v___x_4844_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4845_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4846_ = lean_unsigned_to_nat(0u);
v___x_4847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
lean_ctor_set(v___x_4847_, 1, v___x_4845_);
return v___x_4847_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_4849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
return v___x_4849_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; 
v___x_4850_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4851_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4851_, 0, v___x_4850_);
lean_ctor_set(v___x_4851_, 1, v___x_4850_);
lean_ctor_set(v___x_4851_, 2, v___x_4850_);
lean_ctor_set(v___x_4851_, 3, v___x_4850_);
lean_ctor_set(v___x_4851_, 4, v___x_4850_);
lean_ctor_set(v___x_4851_, 5, v___x_4850_);
return v___x_4851_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_4852_, lean_object* v_e_4853_, lean_object* v_cls_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
if (v___x_4852_ == 0)
{
lean_object* v___x_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; 
lean_dec(v_cls_4854_);
v___x_4860_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_4861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4861_, 0, v_e_4853_);
lean_ctor_set(v___x_4861_, 1, v___x_4860_);
v___x_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4862_, 0, v___x_4861_);
return v___x_4862_;
}
else
{
uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___f_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v_cache_4870_; lean_object* v_a_4872_; lean_object* v___x_4883_; lean_object* v_mctx_4884_; lean_object* v_zetaDeltaFVarIds_4885_; lean_object* v_postponed_4886_; lean_object* v_diag_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4965_; 
v___x_4863_ = 0;
v___x_4864_ = lean_box(0);
v___x_4865_ = lean_unsigned_to_nat(0u);
v___x_4866_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___f_4867_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed), 10, 5);
lean_closure_set(v___f_4867_, 0, v___x_4866_);
lean_closure_set(v___f_4867_, 1, v_e_4853_);
lean_closure_set(v___f_4867_, 2, v___x_4864_);
lean_closure_set(v___f_4867_, 3, v___x_4865_);
lean_closure_set(v___f_4867_, 4, v_cls_4854_);
v___x_4868_ = lean_box(1);
v___x_4869_ = lean_st_ref_get(v___y_4856_);
v_cache_4870_ = lean_ctor_get(v___x_4869_, 1);
lean_inc_ref(v_cache_4870_);
lean_dec(v___x_4869_);
v___x_4883_ = lean_st_ref_take(v___y_4856_);
v_mctx_4884_ = lean_ctor_get(v___x_4883_, 0);
v_zetaDeltaFVarIds_4885_ = lean_ctor_get(v___x_4883_, 2);
v_postponed_4886_ = lean_ctor_get(v___x_4883_, 3);
v_diag_4887_ = lean_ctor_get(v___x_4883_, 4);
v_isSharedCheck_4965_ = !lean_is_exclusive(v___x_4883_);
if (v_isSharedCheck_4965_ == 0)
{
lean_object* v_unused_4966_; 
v_unused_4966_ = lean_ctor_get(v___x_4883_, 1);
lean_dec(v_unused_4966_);
v___x_4889_ = v___x_4883_;
v_isShared_4890_ = v_isSharedCheck_4965_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_diag_4887_);
lean_inc(v_postponed_4886_);
lean_inc(v_zetaDeltaFVarIds_4885_);
lean_inc(v_mctx_4884_);
lean_dec(v___x_4883_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4965_;
goto v_resetjp_4888_;
}
v___jp_4871_:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; uint8_t v_isShared_4877_; uint8_t v_isSharedCheck_4881_; 
v___x_4873_ = lean_box(0);
v___x_4874_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4856_, v_cache_4870_, v___x_4873_);
v_isSharedCheck_4881_ = !lean_is_exclusive(v___x_4874_);
if (v_isSharedCheck_4881_ == 0)
{
lean_object* v_unused_4882_; 
v_unused_4882_ = lean_ctor_get(v___x_4874_, 0);
lean_dec(v_unused_4882_);
v___x_4876_ = v___x_4874_;
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
else
{
lean_dec(v___x_4874_);
v___x_4876_ = lean_box(0);
v_isShared_4877_ = v_isSharedCheck_4881_;
goto v_resetjp_4875_;
}
v_resetjp_4875_:
{
lean_object* v___x_4879_; 
if (v_isShared_4877_ == 0)
{
lean_ctor_set_tag(v___x_4876_, 1);
lean_ctor_set(v___x_4876_, 0, v_a_4872_);
v___x_4879_ = v___x_4876_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4872_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4893_; 
v___x_4891_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 1, v___x_4891_);
v___x_4893_ = v___x_4889_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4964_; 
v_reuseFailAlloc_4964_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4964_, 0, v_mctx_4884_);
lean_ctor_set(v_reuseFailAlloc_4964_, 1, v___x_4891_);
lean_ctor_set(v_reuseFailAlloc_4964_, 2, v_zetaDeltaFVarIds_4885_);
lean_ctor_set(v_reuseFailAlloc_4964_, 3, v_postponed_4886_);
lean_ctor_set(v_reuseFailAlloc_4964_, 4, v_diag_4887_);
v___x_4893_ = v_reuseFailAlloc_4964_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
lean_object* v___x_4894_; lean_object* v_keyedConfig_4895_; lean_object* v_zetaDeltaSet_4896_; lean_object* v_lctx_4897_; lean_object* v_localInstances_4898_; lean_object* v_defEqCtx_x3f_4899_; lean_object* v_synthPendingDepth_4900_; lean_object* v_customCanUnfoldPredicate_x3f_4901_; uint8_t v_univApprox_4902_; uint8_t v_inTypeClassResolution_4903_; uint8_t v_cacheInferType_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v_mctx_4907_; lean_object* v_cache_4908_; lean_object* v_zetaDeltaFVarIds_4909_; lean_object* v_postponed_4910_; lean_object* v_diag_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4963_; 
v___x_4894_ = lean_st_ref_put(v___y_4856_, v___x_4893_);
v_keyedConfig_4895_ = lean_ctor_get(v___y_4855_, 0);
v_zetaDeltaSet_4896_ = lean_ctor_get(v___y_4855_, 1);
v_lctx_4897_ = lean_ctor_get(v___y_4855_, 2);
v_localInstances_4898_ = lean_ctor_get(v___y_4855_, 3);
v_defEqCtx_x3f_4899_ = lean_ctor_get(v___y_4855_, 4);
v_synthPendingDepth_4900_ = lean_ctor_get(v___y_4855_, 5);
v_customCanUnfoldPredicate_x3f_4901_ = lean_ctor_get(v___y_4855_, 6);
v_univApprox_4902_ = lean_ctor_get_uint8(v___y_4855_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4903_ = lean_ctor_get_uint8(v___y_4855_, sizeof(void*)*7 + 2);
v_cacheInferType_4904_ = lean_ctor_get_uint8(v___y_4855_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_4901_);
lean_inc(v_synthPendingDepth_4900_);
lean_inc(v_defEqCtx_x3f_4899_);
lean_inc_ref(v_localInstances_4898_);
lean_inc_ref(v_lctx_4897_);
lean_inc(v_zetaDeltaSet_4896_);
lean_inc_ref(v_keyedConfig_4895_);
v___x_4905_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4905_, 0, v_keyedConfig_4895_);
lean_ctor_set(v___x_4905_, 1, v_zetaDeltaSet_4896_);
lean_ctor_set(v___x_4905_, 2, v_lctx_4897_);
lean_ctor_set(v___x_4905_, 3, v_localInstances_4898_);
lean_ctor_set(v___x_4905_, 4, v_defEqCtx_x3f_4899_);
lean_ctor_set(v___x_4905_, 5, v_synthPendingDepth_4900_);
lean_ctor_set(v___x_4905_, 6, v_customCanUnfoldPredicate_x3f_4901_);
lean_ctor_set_uint8(v___x_4905_, sizeof(void*)*7, v___x_4852_);
lean_ctor_set_uint8(v___x_4905_, sizeof(void*)*7 + 1, v_univApprox_4902_);
lean_ctor_set_uint8(v___x_4905_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4903_);
lean_ctor_set_uint8(v___x_4905_, sizeof(void*)*7 + 3, v_cacheInferType_4904_);
v___x_4906_ = lean_st_ref_take(v___y_4856_);
v_mctx_4907_ = lean_ctor_get(v___x_4906_, 0);
v_cache_4908_ = lean_ctor_get(v___x_4906_, 1);
v_zetaDeltaFVarIds_4909_ = lean_ctor_get(v___x_4906_, 2);
v_postponed_4910_ = lean_ctor_get(v___x_4906_, 3);
v_diag_4911_ = lean_ctor_get(v___x_4906_, 4);
v_isSharedCheck_4963_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4963_ == 0)
{
v___x_4913_ = v___x_4906_;
v_isShared_4914_ = v_isSharedCheck_4963_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_diag_4911_);
lean_inc(v_postponed_4910_);
lean_inc(v_zetaDeltaFVarIds_4909_);
lean_inc(v_cache_4908_);
lean_inc(v_mctx_4907_);
lean_dec(v___x_4906_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4963_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v_a_4916_; lean_object* v_a_4920_; lean_object* v___y_4933_; lean_object* v___y_4937_; lean_object* v___x_4941_; 
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 2, v___x_4868_);
v___x_4941_ = v___x_4913_;
goto v_reusejp_4940_;
}
else
{
lean_object* v_reuseFailAlloc_4962_; 
v_reuseFailAlloc_4962_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4962_, 0, v_mctx_4907_);
lean_ctor_set(v_reuseFailAlloc_4962_, 1, v_cache_4908_);
lean_ctor_set(v_reuseFailAlloc_4962_, 2, v___x_4868_);
lean_ctor_set(v_reuseFailAlloc_4962_, 3, v_postponed_4910_);
lean_ctor_set(v_reuseFailAlloc_4962_, 4, v_diag_4911_);
v___x_4941_ = v_reuseFailAlloc_4962_;
goto v_reusejp_4940_;
}
v___jp_4915_:
{
lean_object* v___x_4917_; lean_object* v___x_4918_; 
v___x_4917_ = lean_box(0);
v___x_4918_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4856_, v_zetaDeltaFVarIds_4909_, v___x_4917_);
lean_dec_ref(v___x_4918_);
v_a_4872_ = v_a_4916_;
goto v___jp_4871_;
}
v___jp_4919_:
{
lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4930_; 
lean_inc(v_a_4920_);
v___x_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4921_, 0, v_a_4920_);
v___x_4922_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___y_4856_, v_zetaDeltaFVarIds_4909_, v___x_4921_);
lean_dec_ref(v___x_4922_);
v___x_4923_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4856_, v_cache_4870_, v___x_4921_);
lean_dec_ref_known(v___x_4921_, 1);
v_isSharedCheck_4930_ = !lean_is_exclusive(v___x_4923_);
if (v_isSharedCheck_4930_ == 0)
{
lean_object* v_unused_4931_; 
v_unused_4931_ = lean_ctor_get(v___x_4923_, 0);
lean_dec(v_unused_4931_);
v___x_4925_ = v___x_4923_;
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
else
{
lean_dec(v___x_4923_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4930_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___x_4928_; 
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v_a_4920_);
v___x_4928_ = v___x_4925_;
goto v_reusejp_4927_;
}
else
{
lean_object* v_reuseFailAlloc_4929_; 
v_reuseFailAlloc_4929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4929_, 0, v_a_4920_);
v___x_4928_ = v_reuseFailAlloc_4929_;
goto v_reusejp_4927_;
}
v_reusejp_4927_:
{
return v___x_4928_;
}
}
}
v___jp_4932_:
{
if (lean_obj_tag(v___y_4933_) == 0)
{
lean_object* v_a_4934_; 
v_a_4934_ = lean_ctor_get(v___y_4933_, 0);
lean_inc(v_a_4934_);
lean_dec_ref_known(v___y_4933_, 1);
v_a_4920_ = v_a_4934_;
goto v___jp_4919_;
}
else
{
lean_object* v_a_4935_; 
v_a_4935_ = lean_ctor_get(v___y_4933_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___y_4933_, 1);
v_a_4916_ = v_a_4935_;
goto v___jp_4915_;
}
}
v___jp_4936_:
{
if (lean_obj_tag(v___y_4937_) == 0)
{
lean_object* v_a_4938_; 
v_a_4938_ = lean_ctor_get(v___y_4937_, 0);
lean_inc(v_a_4938_);
lean_dec_ref_known(v___y_4937_, 1);
v_a_4920_ = v_a_4938_;
goto v___jp_4919_;
}
else
{
lean_object* v_a_4939_; 
v_a_4939_ = lean_ctor_get(v___y_4937_, 0);
lean_inc(v_a_4939_);
lean_dec_ref_known(v___y_4937_, 1);
v_a_4916_ = v_a_4939_;
goto v___jp_4915_;
}
}
v_reusejp_4940_:
{
lean_object* v___x_4942_; lean_object* v___x_4943_; uint8_t v_transparency_4944_; uint8_t v___x_4945_; 
v___x_4942_ = lean_st_ref_put(v___y_4856_, v___x_4941_);
v___x_4943_ = l_Lean_Meta_Context_config(v___x_4905_);
v_transparency_4944_ = lean_ctor_get_uint8(v___x_4943_, 9);
lean_dec_ref(v___x_4943_);
v___x_4945_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4944_, v___x_4863_);
if (v___x_4945_ == 0)
{
lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; uint8_t v_transparency_4949_; uint8_t v___x_4950_; uint8_t v___x_4951_; 
lean_dec_ref_known(v___x_4905_, 7);
lean_inc_ref(v_keyedConfig_4895_);
v___x_4946_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4863_, v_keyedConfig_4895_);
lean_inc(v_customCanUnfoldPredicate_x3f_4901_);
lean_inc(v_synthPendingDepth_4900_);
lean_inc(v_defEqCtx_x3f_4899_);
lean_inc_ref(v_localInstances_4898_);
lean_inc_ref(v_lctx_4897_);
lean_inc(v_zetaDeltaSet_4896_);
lean_inc_ref(v___x_4946_);
v___x_4947_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4947_, 0, v___x_4946_);
lean_ctor_set(v___x_4947_, 1, v_zetaDeltaSet_4896_);
lean_ctor_set(v___x_4947_, 2, v_lctx_4897_);
lean_ctor_set(v___x_4947_, 3, v_localInstances_4898_);
lean_ctor_set(v___x_4947_, 4, v_defEqCtx_x3f_4899_);
lean_ctor_set(v___x_4947_, 5, v_synthPendingDepth_4900_);
lean_ctor_set(v___x_4947_, 6, v_customCanUnfoldPredicate_x3f_4901_);
lean_ctor_set_uint8(v___x_4947_, sizeof(void*)*7, v___x_4852_);
lean_ctor_set_uint8(v___x_4947_, sizeof(void*)*7 + 1, v_univApprox_4902_);
lean_ctor_set_uint8(v___x_4947_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4903_);
lean_ctor_set_uint8(v___x_4947_, sizeof(void*)*7 + 3, v_cacheInferType_4904_);
v___x_4948_ = l_Lean_Meta_Context_config(v___x_4947_);
v_transparency_4949_ = lean_ctor_get_uint8(v___x_4948_, 9);
lean_dec_ref(v___x_4948_);
v___x_4950_ = 1;
v___x_4951_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4949_, v___x_4950_);
if (v___x_4951_ == 0)
{
lean_object* v___x_4952_; 
lean_dec_ref(v___x_4946_);
lean_inc(v___y_4858_);
lean_inc_ref(v___y_4857_);
lean_inc(v___y_4856_);
v___x_4952_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4852_, v___f_4867_, v___x_4947_, v___y_4856_, v___y_4857_, v___y_4858_);
v___y_4933_ = v___x_4952_;
goto v___jp_4932_;
}
else
{
lean_object* v___x_4953_; lean_object* v___x_4954_; lean_object* v___x_4955_; 
lean_dec_ref_known(v___x_4947_, 7);
v___x_4953_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4950_, v___x_4946_);
lean_inc(v_customCanUnfoldPredicate_x3f_4901_);
lean_inc(v_synthPendingDepth_4900_);
lean_inc(v_defEqCtx_x3f_4899_);
lean_inc_ref(v_localInstances_4898_);
lean_inc_ref(v_lctx_4897_);
lean_inc(v_zetaDeltaSet_4896_);
v___x_4954_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4954_, 0, v___x_4953_);
lean_ctor_set(v___x_4954_, 1, v_zetaDeltaSet_4896_);
lean_ctor_set(v___x_4954_, 2, v_lctx_4897_);
lean_ctor_set(v___x_4954_, 3, v_localInstances_4898_);
lean_ctor_set(v___x_4954_, 4, v_defEqCtx_x3f_4899_);
lean_ctor_set(v___x_4954_, 5, v_synthPendingDepth_4900_);
lean_ctor_set(v___x_4954_, 6, v_customCanUnfoldPredicate_x3f_4901_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7, v___x_4852_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7 + 1, v_univApprox_4902_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4903_);
lean_ctor_set_uint8(v___x_4954_, sizeof(void*)*7 + 3, v_cacheInferType_4904_);
lean_inc(v___y_4858_);
lean_inc_ref(v___y_4857_);
lean_inc(v___y_4856_);
v___x_4955_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4852_, v___f_4867_, v___x_4954_, v___y_4856_, v___y_4857_, v___y_4858_);
v___y_4933_ = v___x_4955_;
goto v___jp_4932_;
}
}
else
{
uint8_t v___x_4956_; uint8_t v___x_4957_; 
v___x_4956_ = 1;
v___x_4957_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4944_, v___x_4956_);
if (v___x_4957_ == 0)
{
lean_object* v___x_4958_; 
lean_inc(v___y_4858_);
lean_inc_ref(v___y_4857_);
lean_inc(v___y_4856_);
v___x_4958_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4945_, v___f_4867_, v___x_4905_, v___y_4856_, v___y_4857_, v___y_4858_);
v___y_4937_ = v___x_4958_;
goto v___jp_4936_;
}
else
{
lean_object* v___x_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; 
lean_dec_ref_known(v___x_4905_, 7);
lean_inc_ref(v_keyedConfig_4895_);
v___x_4959_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4956_, v_keyedConfig_4895_);
lean_inc(v_customCanUnfoldPredicate_x3f_4901_);
lean_inc(v_synthPendingDepth_4900_);
lean_inc(v_defEqCtx_x3f_4899_);
lean_inc_ref(v_localInstances_4898_);
lean_inc_ref(v_lctx_4897_);
lean_inc(v_zetaDeltaSet_4896_);
v___x_4960_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4960_, 0, v___x_4959_);
lean_ctor_set(v___x_4960_, 1, v_zetaDeltaSet_4896_);
lean_ctor_set(v___x_4960_, 2, v_lctx_4897_);
lean_ctor_set(v___x_4960_, 3, v_localInstances_4898_);
lean_ctor_set(v___x_4960_, 4, v_defEqCtx_x3f_4899_);
lean_ctor_set(v___x_4960_, 5, v_synthPendingDepth_4900_);
lean_ctor_set(v___x_4960_, 6, v_customCanUnfoldPredicate_x3f_4901_);
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*7, v___x_4852_);
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*7 + 1, v_univApprox_4902_);
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4903_);
lean_ctor_set_uint8(v___x_4960_, sizeof(void*)*7 + 3, v_cacheInferType_4904_);
lean_inc(v___y_4858_);
lean_inc_ref(v___y_4857_);
lean_inc(v___y_4856_);
v___x_4961_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4945_, v___f_4867_, v___x_4960_, v___y_4856_, v___y_4857_, v___y_4858_);
v___y_4937_ = v___x_4961_;
goto v___jp_4936_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_4967_, lean_object* v_e_4968_, lean_object* v_cls_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_, lean_object* v___y_4974_){
_start:
{
uint8_t v___x_14238__boxed_4975_; lean_object* v_res_4976_; 
v___x_14238__boxed_4975_ = lean_unbox(v___x_4967_);
v_res_4976_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14238__boxed_4975_, v_e_4968_, v_cls_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_);
lean_dec(v___y_4973_);
lean_dec_ref(v___y_4972_);
lean_dec(v___y_4971_);
lean_dec_ref(v___y_4970_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
if (lean_obj_tag(v_x_4977_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; uint8_t v_isShared_4986_; uint8_t v_isSharedCheck_4991_; 
v_a_4983_ = lean_ctor_get(v_x_4977_, 0);
v_isSharedCheck_4991_ = !lean_is_exclusive(v_x_4977_);
if (v_isSharedCheck_4991_ == 0)
{
v___x_4985_ = v_x_4977_;
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
else
{
lean_inc(v_a_4983_);
lean_dec(v_x_4977_);
v___x_4985_ = lean_box(0);
v_isShared_4986_ = v_isSharedCheck_4991_;
goto v_resetjp_4984_;
}
v_resetjp_4984_:
{
lean_object* v___x_4987_; lean_object* v___x_4989_; 
v___x_4987_ = l_Lean_Exception_toMessageData(v_a_4983_);
if (v_isShared_4986_ == 0)
{
lean_ctor_set(v___x_4985_, 0, v___x_4987_);
v___x_4989_ = v___x_4985_;
goto v_reusejp_4988_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4987_);
v___x_4989_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4988_;
}
v_reusejp_4988_:
{
return v___x_4989_;
}
}
}
else
{
lean_object* v_a_4992_; lean_object* v___x_4994_; uint8_t v_isShared_4995_; uint8_t v_isSharedCheck_5000_; 
v_a_4992_ = lean_ctor_get(v_x_4977_, 0);
v_isSharedCheck_5000_ = !lean_is_exclusive(v_x_4977_);
if (v_isSharedCheck_5000_ == 0)
{
v___x_4994_ = v_x_4977_;
v_isShared_4995_ = v_isSharedCheck_5000_;
goto v_resetjp_4993_;
}
else
{
lean_inc(v_a_4992_);
lean_dec(v_x_4977_);
v___x_4994_ = lean_box(0);
v_isShared_4995_ = v_isSharedCheck_5000_;
goto v_resetjp_4993_;
}
v_resetjp_4993_:
{
lean_object* v_snd_4996_; lean_object* v___x_4998_; 
v_snd_4996_ = lean_ctor_get(v_a_4992_, 1);
lean_inc(v_snd_4996_);
lean_dec(v_a_4992_);
if (v_isShared_4995_ == 0)
{
lean_ctor_set_tag(v___x_4994_, 0);
lean_ctor_set(v___x_4994_, 0, v_snd_4996_);
v___x_4998_ = v___x_4994_;
goto v_reusejp_4997_;
}
else
{
lean_object* v_reuseFailAlloc_4999_; 
v_reuseFailAlloc_4999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4999_, 0, v_snd_4996_);
v___x_4998_ = v_reuseFailAlloc_4999_;
goto v_reusejp_4997_;
}
v_reusejp_4997_:
{
return v___x_4998_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5001_, v___y_5002_, v___y_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
return v_res_5007_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5008_){
_start:
{
if (lean_obj_tag(v_x_5008_) == 0)
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
v_a_5010_ = lean_ctor_get(v_x_5008_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v_x_5008_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v_x_5008_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v_x_5008_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
lean_ctor_set_tag(v___x_5012_, 1);
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_a_5010_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
v_a_5018_ = lean_ctor_get(v_x_5008_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v_x_5008_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v_x_5008_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v_x_5008_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
lean_ctor_set_tag(v___x_5020_, 0);
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5026_, lean_object* v___y_5027_){
_start:
{
lean_object* v_res_5028_; 
v_res_5028_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5026_);
return v_res_5028_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5029_){
_start:
{
if (lean_obj_tag(v_e_5029_) == 0)
{
uint8_t v___x_5030_; 
v___x_5030_ = 2;
return v___x_5030_;
}
else
{
uint8_t v___x_5031_; 
v___x_5031_ = 0;
return v___x_5031_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5032_){
_start:
{
uint8_t v_res_5033_; lean_object* v_r_5034_; 
v_res_5033_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5032_);
lean_dec_ref(v_e_5032_);
v_r_5034_ = lean_box(v_res_5033_);
return v_r_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5035_, lean_object* v_data_5036_, lean_object* v_ref_5037_, lean_object* v_msg_5038_, lean_object* v___y_5039_, lean_object* v___y_5040_, lean_object* v___y_5041_, lean_object* v___y_5042_){
_start:
{
lean_object* v_toCold_5044_; lean_object* v_currRecDepth_5045_; lean_object* v_ref_5046_; uint16_t v_optionFlags_5047_; uint8_t v_suppressElabErrors_5048_; uint8_t v_isRecordingDeps_5049_; lean_object* v_ref_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v_traceState_5053_; lean_object* v_traces_5054_; lean_object* v___x_5055_; size_t v_sz_5056_; size_t v___x_5057_; lean_object* v___x_5058_; lean_object* v_msg_5059_; lean_object* v___x_5060_; lean_object* v_a_5061_; lean_object* v___x_5063_; uint8_t v_isShared_5064_; uint8_t v_isSharedCheck_5099_; 
v_toCold_5044_ = lean_ctor_get(v___y_5041_, 0);
v_currRecDepth_5045_ = lean_ctor_get(v___y_5041_, 1);
v_ref_5046_ = lean_ctor_get(v___y_5041_, 2);
v_optionFlags_5047_ = lean_ctor_get_uint16(v___y_5041_, sizeof(void*)*3);
v_suppressElabErrors_5048_ = lean_ctor_get_uint8(v___y_5041_, sizeof(void*)*3 + 2);
v_isRecordingDeps_5049_ = lean_ctor_get_uint8(v___y_5041_, sizeof(void*)*3 + 3);
v_ref_5050_ = l_Lean_replaceRef(v_ref_5037_, v_ref_5046_);
lean_inc(v_currRecDepth_5045_);
lean_inc_ref(v_toCold_5044_);
v___x_5051_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_5051_, 0, v_toCold_5044_);
lean_ctor_set(v___x_5051_, 1, v_currRecDepth_5045_);
lean_ctor_set(v___x_5051_, 2, v_ref_5050_);
lean_ctor_set_uint16(v___x_5051_, sizeof(void*)*3, v_optionFlags_5047_);
lean_ctor_set_uint8(v___x_5051_, sizeof(void*)*3 + 2, v_suppressElabErrors_5048_);
lean_ctor_set_uint8(v___x_5051_, sizeof(void*)*3 + 3, v_isRecordingDeps_5049_);
v___x_5052_ = lean_st_ref_get(v___y_5042_);
v_traceState_5053_ = lean_ctor_get(v___x_5052_, 4);
lean_inc_ref(v_traceState_5053_);
lean_dec(v___x_5052_);
v_traces_5054_ = lean_ctor_get(v_traceState_5053_, 0);
lean_inc_ref(v_traces_5054_);
lean_dec_ref(v_traceState_5053_);
v___x_5055_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5054_);
lean_dec_ref(v_traces_5054_);
v_sz_5056_ = lean_array_size(v___x_5055_);
v___x_5057_ = ((size_t)0ULL);
v___x_5058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5056_, v___x_5057_, v___x_5055_);
v_msg_5059_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5059_, 0, v_data_5036_);
lean_ctor_set(v_msg_5059_, 1, v_msg_5038_);
lean_ctor_set(v_msg_5059_, 2, v___x_5058_);
v___x_5060_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5059_, v___y_5039_, v___y_5040_, v___x_5051_, v___y_5042_);
lean_dec_ref_known(v___x_5051_, 3);
v_a_5061_ = lean_ctor_get(v___x_5060_, 0);
v_isSharedCheck_5099_ = !lean_is_exclusive(v___x_5060_);
if (v_isSharedCheck_5099_ == 0)
{
v___x_5063_ = v___x_5060_;
v_isShared_5064_ = v_isSharedCheck_5099_;
goto v_resetjp_5062_;
}
else
{
lean_inc(v_a_5061_);
lean_dec(v___x_5060_);
v___x_5063_ = lean_box(0);
v_isShared_5064_ = v_isSharedCheck_5099_;
goto v_resetjp_5062_;
}
v_resetjp_5062_:
{
lean_object* v___x_5065_; lean_object* v_traceState_5066_; lean_object* v_env_5067_; lean_object* v_nextMacroScope_5068_; lean_object* v_ngen_5069_; lean_object* v_auxDeclNGen_5070_; lean_object* v_cache_5071_; lean_object* v_recordedDeps_5072_; lean_object* v_messages_5073_; lean_object* v_infoState_5074_; lean_object* v_snapshotTasks_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5098_; 
v___x_5065_ = lean_st_ref_take(v___y_5042_);
v_traceState_5066_ = lean_ctor_get(v___x_5065_, 4);
v_env_5067_ = lean_ctor_get(v___x_5065_, 0);
v_nextMacroScope_5068_ = lean_ctor_get(v___x_5065_, 1);
v_ngen_5069_ = lean_ctor_get(v___x_5065_, 2);
v_auxDeclNGen_5070_ = lean_ctor_get(v___x_5065_, 3);
v_cache_5071_ = lean_ctor_get(v___x_5065_, 5);
v_recordedDeps_5072_ = lean_ctor_get(v___x_5065_, 6);
v_messages_5073_ = lean_ctor_get(v___x_5065_, 7);
v_infoState_5074_ = lean_ctor_get(v___x_5065_, 8);
v_snapshotTasks_5075_ = lean_ctor_get(v___x_5065_, 9);
v_isSharedCheck_5098_ = !lean_is_exclusive(v___x_5065_);
if (v_isSharedCheck_5098_ == 0)
{
v___x_5077_ = v___x_5065_;
v_isShared_5078_ = v_isSharedCheck_5098_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_snapshotTasks_5075_);
lean_inc(v_infoState_5074_);
lean_inc(v_messages_5073_);
lean_inc(v_recordedDeps_5072_);
lean_inc(v_cache_5071_);
lean_inc(v_traceState_5066_);
lean_inc(v_auxDeclNGen_5070_);
lean_inc(v_ngen_5069_);
lean_inc(v_nextMacroScope_5068_);
lean_inc(v_env_5067_);
lean_dec(v___x_5065_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5098_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
uint64_t v_tid_5079_; lean_object* v___x_5081_; uint8_t v_isShared_5082_; uint8_t v_isSharedCheck_5096_; 
v_tid_5079_ = lean_ctor_get_uint64(v_traceState_5066_, sizeof(void*)*1);
v_isSharedCheck_5096_ = !lean_is_exclusive(v_traceState_5066_);
if (v_isSharedCheck_5096_ == 0)
{
lean_object* v_unused_5097_; 
v_unused_5097_ = lean_ctor_get(v_traceState_5066_, 0);
lean_dec(v_unused_5097_);
v___x_5081_ = v_traceState_5066_;
v_isShared_5082_ = v_isSharedCheck_5096_;
goto v_resetjp_5080_;
}
else
{
lean_dec(v_traceState_5066_);
v___x_5081_ = lean_box(0);
v_isShared_5082_ = v_isSharedCheck_5096_;
goto v_resetjp_5080_;
}
v_resetjp_5080_:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; lean_object* v___x_5087_; 
v___x_5083_ = lean_box(0);
v___x_5084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5084_, 0, v_ref_5037_);
lean_ctor_set(v___x_5084_, 1, v_a_5061_);
v___x_5085_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5035_, v___x_5084_);
if (v_isShared_5082_ == 0)
{
lean_ctor_set(v___x_5081_, 0, v___x_5085_);
v___x_5087_ = v___x_5081_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5095_; 
v_reuseFailAlloc_5095_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5095_, 0, v___x_5085_);
lean_ctor_set_uint64(v_reuseFailAlloc_5095_, sizeof(void*)*1, v_tid_5079_);
v___x_5087_ = v_reuseFailAlloc_5095_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
lean_object* v___x_5089_; 
if (v_isShared_5078_ == 0)
{
lean_ctor_set(v___x_5077_, 4, v___x_5087_);
v___x_5089_ = v___x_5077_;
goto v_reusejp_5088_;
}
else
{
lean_object* v_reuseFailAlloc_5094_; 
v_reuseFailAlloc_5094_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5094_, 0, v_env_5067_);
lean_ctor_set(v_reuseFailAlloc_5094_, 1, v_nextMacroScope_5068_);
lean_ctor_set(v_reuseFailAlloc_5094_, 2, v_ngen_5069_);
lean_ctor_set(v_reuseFailAlloc_5094_, 3, v_auxDeclNGen_5070_);
lean_ctor_set(v_reuseFailAlloc_5094_, 4, v___x_5087_);
lean_ctor_set(v_reuseFailAlloc_5094_, 5, v_cache_5071_);
lean_ctor_set(v_reuseFailAlloc_5094_, 6, v_recordedDeps_5072_);
lean_ctor_set(v_reuseFailAlloc_5094_, 7, v_messages_5073_);
lean_ctor_set(v_reuseFailAlloc_5094_, 8, v_infoState_5074_);
lean_ctor_set(v_reuseFailAlloc_5094_, 9, v_snapshotTasks_5075_);
v___x_5089_ = v_reuseFailAlloc_5094_;
goto v_reusejp_5088_;
}
v_reusejp_5088_:
{
lean_object* v___x_5090_; lean_object* v___x_5092_; 
v___x_5090_ = lean_st_ref_put(v___y_5042_, v___x_5089_);
if (v_isShared_5064_ == 0)
{
lean_ctor_set(v___x_5063_, 0, v___x_5083_);
v___x_5092_ = v___x_5063_;
goto v_reusejp_5091_;
}
else
{
lean_object* v_reuseFailAlloc_5093_; 
v_reuseFailAlloc_5093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5093_, 0, v___x_5083_);
v___x_5092_ = v_reuseFailAlloc_5093_;
goto v_reusejp_5091_;
}
v_reusejp_5091_:
{
return v___x_5092_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5100_, lean_object* v_data_5101_, lean_object* v_ref_5102_, lean_object* v_msg_5103_, lean_object* v___y_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_, lean_object* v___y_5108_){
_start:
{
lean_object* v_res_5109_; 
v_res_5109_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5100_, v_data_5101_, v_ref_5102_, v_msg_5103_, v___y_5104_, v___y_5105_, v___y_5106_, v___y_5107_);
lean_dec(v___y_5107_);
lean_dec_ref(v___y_5106_);
lean_dec(v___y_5105_);
lean_dec_ref(v___y_5104_);
return v_res_5109_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5110_, uint8_t v_collapsed_5111_, lean_object* v_tag_5112_, lean_object* v_opts_5113_, uint8_t v_clsEnabled_5114_, lean_object* v_oldTraces_5115_, lean_object* v_msg_5116_, lean_object* v_resStartStop_5117_, lean_object* v___y_5118_, lean_object* v___y_5119_, lean_object* v___y_5120_, lean_object* v___y_5121_){
_start:
{
lean_object* v_fst_5123_; lean_object* v_snd_5124_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v_data_5128_; lean_object* v_fst_5139_; lean_object* v_snd_5140_; lean_object* v___x_5141_; uint8_t v___x_5142_; lean_object* v___y_5144_; lean_object* v_a_5145_; uint8_t v___y_5160_; double v___y_5192_; 
v_fst_5123_ = lean_ctor_get(v_resStartStop_5117_, 0);
lean_inc(v_fst_5123_);
v_snd_5124_ = lean_ctor_get(v_resStartStop_5117_, 1);
lean_inc(v_snd_5124_);
lean_dec_ref(v_resStartStop_5117_);
v_fst_5139_ = lean_ctor_get(v_snd_5124_, 0);
lean_inc(v_fst_5139_);
v_snd_5140_ = lean_ctor_get(v_snd_5124_, 1);
lean_inc(v_snd_5140_);
lean_dec(v_snd_5124_);
v___x_5141_ = l_Lean_trace_profiler;
v___x_5142_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5113_, v___x_5141_);
if (v___x_5142_ == 0)
{
v___y_5160_ = v___x_5142_;
goto v___jp_5159_;
}
else
{
lean_object* v___x_5197_; uint8_t v___x_5198_; 
v___x_5197_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5198_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5113_, v___x_5197_);
if (v___x_5198_ == 0)
{
lean_object* v___x_5199_; lean_object* v___x_5200_; double v___x_5201_; double v___x_5202_; double v___x_5203_; 
v___x_5199_ = l_Lean_trace_profiler_threshold;
v___x_5200_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5113_, v___x_5199_);
v___x_5201_ = lean_float_of_nat(v___x_5200_);
v___x_5202_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5203_ = lean_float_div(v___x_5201_, v___x_5202_);
v___y_5192_ = v___x_5203_;
goto v___jp_5191_;
}
else
{
lean_object* v___x_5204_; lean_object* v___x_5205_; double v___x_5206_; 
v___x_5204_ = l_Lean_trace_profiler_threshold;
v___x_5205_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5113_, v___x_5204_);
v___x_5206_ = lean_float_of_nat(v___x_5205_);
v___y_5192_ = v___x_5206_;
goto v___jp_5191_;
}
}
v___jp_5125_:
{
lean_object* v___x_5129_; 
lean_inc(v___y_5127_);
v___x_5129_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5115_, v_data_5128_, v___y_5127_, v___y_5126_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_);
if (lean_obj_tag(v___x_5129_) == 0)
{
lean_object* v___x_5130_; 
lean_dec_ref_known(v___x_5129_, 1);
v___x_5130_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5123_);
return v___x_5130_;
}
else
{
lean_object* v_a_5131_; lean_object* v___x_5133_; uint8_t v_isShared_5134_; uint8_t v_isSharedCheck_5138_; 
lean_dec(v_fst_5123_);
v_a_5131_ = lean_ctor_get(v___x_5129_, 0);
v_isSharedCheck_5138_ = !lean_is_exclusive(v___x_5129_);
if (v_isSharedCheck_5138_ == 0)
{
v___x_5133_ = v___x_5129_;
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
else
{
lean_inc(v_a_5131_);
lean_dec(v___x_5129_);
v___x_5133_ = lean_box(0);
v_isShared_5134_ = v_isSharedCheck_5138_;
goto v_resetjp_5132_;
}
v_resetjp_5132_:
{
lean_object* v___x_5136_; 
if (v_isShared_5134_ == 0)
{
v___x_5136_ = v___x_5133_;
goto v_reusejp_5135_;
}
else
{
lean_object* v_reuseFailAlloc_5137_; 
v_reuseFailAlloc_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
v___x_5136_ = v_reuseFailAlloc_5137_;
goto v_reusejp_5135_;
}
v_reusejp_5135_:
{
return v___x_5136_;
}
}
}
}
v___jp_5143_:
{
uint8_t v_result_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; double v___x_5149_; lean_object* v_data_5150_; 
v_result_5146_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5123_);
v___x_5147_ = lean_box(v_result_5146_);
v___x_5148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5148_, 0, v___x_5147_);
v___x_5149_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5112_);
lean_inc_ref(v___x_5148_);
lean_inc(v_cls_5110_);
v_data_5150_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5150_, 0, v_cls_5110_);
lean_ctor_set(v_data_5150_, 1, v___x_5148_);
lean_ctor_set(v_data_5150_, 2, v_tag_5112_);
lean_ctor_set_float(v_data_5150_, sizeof(void*)*3, v___x_5149_);
lean_ctor_set_float(v_data_5150_, sizeof(void*)*3 + 8, v___x_5149_);
lean_ctor_set_uint8(v_data_5150_, sizeof(void*)*3 + 16, v_collapsed_5111_);
if (v___x_5142_ == 0)
{
lean_dec_ref_known(v___x_5148_, 1);
lean_dec(v_snd_5140_);
lean_dec(v_fst_5139_);
lean_dec_ref(v_tag_5112_);
lean_dec(v_cls_5110_);
v___y_5126_ = v_a_5145_;
v___y_5127_ = v___y_5144_;
v_data_5128_ = v_data_5150_;
goto v___jp_5125_;
}
else
{
lean_object* v_data_5151_; double v___x_5152_; double v___x_5153_; 
lean_dec_ref_known(v_data_5150_, 3);
v_data_5151_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5151_, 0, v_cls_5110_);
lean_ctor_set(v_data_5151_, 1, v___x_5148_);
lean_ctor_set(v_data_5151_, 2, v_tag_5112_);
v___x_5152_ = lean_unbox_float(v_fst_5139_);
lean_dec(v_fst_5139_);
lean_ctor_set_float(v_data_5151_, sizeof(void*)*3, v___x_5152_);
v___x_5153_ = lean_unbox_float(v_snd_5140_);
lean_dec(v_snd_5140_);
lean_ctor_set_float(v_data_5151_, sizeof(void*)*3 + 8, v___x_5153_);
lean_ctor_set_uint8(v_data_5151_, sizeof(void*)*3 + 16, v_collapsed_5111_);
v___y_5126_ = v_a_5145_;
v___y_5127_ = v___y_5144_;
v_data_5128_ = v_data_5151_;
goto v___jp_5125_;
}
}
v___jp_5154_:
{
lean_object* v_ref_5155_; lean_object* v___x_5156_; 
v_ref_5155_ = lean_ctor_get(v___y_5120_, 2);
lean_inc(v___y_5121_);
lean_inc_ref(v___y_5120_);
lean_inc(v___y_5119_);
lean_inc_ref(v___y_5118_);
lean_inc(v_fst_5123_);
v___x_5156_ = lean_apply_6(v_msg_5116_, v_fst_5123_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, lean_box(0));
if (lean_obj_tag(v___x_5156_) == 0)
{
lean_object* v_a_5157_; 
v_a_5157_ = lean_ctor_get(v___x_5156_, 0);
lean_inc(v_a_5157_);
lean_dec_ref_known(v___x_5156_, 1);
v___y_5144_ = v_ref_5155_;
v_a_5145_ = v_a_5157_;
goto v___jp_5143_;
}
else
{
lean_object* v___x_5158_; 
lean_dec_ref_known(v___x_5156_, 1);
v___x_5158_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5144_ = v_ref_5155_;
v_a_5145_ = v___x_5158_;
goto v___jp_5143_;
}
}
v___jp_5159_:
{
if (v_clsEnabled_5114_ == 0)
{
if (v___y_5160_ == 0)
{
lean_object* v___x_5161_; lean_object* v_traceState_5162_; lean_object* v_env_5163_; lean_object* v_nextMacroScope_5164_; lean_object* v_ngen_5165_; lean_object* v_auxDeclNGen_5166_; lean_object* v_cache_5167_; lean_object* v_recordedDeps_5168_; lean_object* v_messages_5169_; lean_object* v_infoState_5170_; lean_object* v_snapshotTasks_5171_; lean_object* v___x_5173_; uint8_t v_isShared_5174_; uint8_t v_isSharedCheck_5190_; 
lean_dec(v_snd_5140_);
lean_dec(v_fst_5139_);
lean_dec_ref(v_msg_5116_);
lean_dec_ref(v_tag_5112_);
lean_dec(v_cls_5110_);
v___x_5161_ = lean_st_ref_take(v___y_5121_);
v_traceState_5162_ = lean_ctor_get(v___x_5161_, 4);
v_env_5163_ = lean_ctor_get(v___x_5161_, 0);
v_nextMacroScope_5164_ = lean_ctor_get(v___x_5161_, 1);
v_ngen_5165_ = lean_ctor_get(v___x_5161_, 2);
v_auxDeclNGen_5166_ = lean_ctor_get(v___x_5161_, 3);
v_cache_5167_ = lean_ctor_get(v___x_5161_, 5);
v_recordedDeps_5168_ = lean_ctor_get(v___x_5161_, 6);
v_messages_5169_ = lean_ctor_get(v___x_5161_, 7);
v_infoState_5170_ = lean_ctor_get(v___x_5161_, 8);
v_snapshotTasks_5171_ = lean_ctor_get(v___x_5161_, 9);
v_isSharedCheck_5190_ = !lean_is_exclusive(v___x_5161_);
if (v_isSharedCheck_5190_ == 0)
{
v___x_5173_ = v___x_5161_;
v_isShared_5174_ = v_isSharedCheck_5190_;
goto v_resetjp_5172_;
}
else
{
lean_inc(v_snapshotTasks_5171_);
lean_inc(v_infoState_5170_);
lean_inc(v_messages_5169_);
lean_inc(v_recordedDeps_5168_);
lean_inc(v_cache_5167_);
lean_inc(v_traceState_5162_);
lean_inc(v_auxDeclNGen_5166_);
lean_inc(v_ngen_5165_);
lean_inc(v_nextMacroScope_5164_);
lean_inc(v_env_5163_);
lean_dec(v___x_5161_);
v___x_5173_ = lean_box(0);
v_isShared_5174_ = v_isSharedCheck_5190_;
goto v_resetjp_5172_;
}
v_resetjp_5172_:
{
uint64_t v_tid_5175_; lean_object* v_traces_5176_; lean_object* v___x_5178_; uint8_t v_isShared_5179_; uint8_t v_isSharedCheck_5189_; 
v_tid_5175_ = lean_ctor_get_uint64(v_traceState_5162_, sizeof(void*)*1);
v_traces_5176_ = lean_ctor_get(v_traceState_5162_, 0);
v_isSharedCheck_5189_ = !lean_is_exclusive(v_traceState_5162_);
if (v_isSharedCheck_5189_ == 0)
{
v___x_5178_ = v_traceState_5162_;
v_isShared_5179_ = v_isSharedCheck_5189_;
goto v_resetjp_5177_;
}
else
{
lean_inc(v_traces_5176_);
lean_dec(v_traceState_5162_);
v___x_5178_ = lean_box(0);
v_isShared_5179_ = v_isSharedCheck_5189_;
goto v_resetjp_5177_;
}
v_resetjp_5177_:
{
lean_object* v___x_5180_; lean_object* v___x_5182_; 
v___x_5180_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5115_, v_traces_5176_);
lean_dec_ref(v_traces_5176_);
if (v_isShared_5179_ == 0)
{
lean_ctor_set(v___x_5178_, 0, v___x_5180_);
v___x_5182_ = v___x_5178_;
goto v_reusejp_5181_;
}
else
{
lean_object* v_reuseFailAlloc_5188_; 
v_reuseFailAlloc_5188_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5188_, 0, v___x_5180_);
lean_ctor_set_uint64(v_reuseFailAlloc_5188_, sizeof(void*)*1, v_tid_5175_);
v___x_5182_ = v_reuseFailAlloc_5188_;
goto v_reusejp_5181_;
}
v_reusejp_5181_:
{
lean_object* v___x_5184_; 
if (v_isShared_5174_ == 0)
{
lean_ctor_set(v___x_5173_, 4, v___x_5182_);
v___x_5184_ = v___x_5173_;
goto v_reusejp_5183_;
}
else
{
lean_object* v_reuseFailAlloc_5187_; 
v_reuseFailAlloc_5187_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5187_, 0, v_env_5163_);
lean_ctor_set(v_reuseFailAlloc_5187_, 1, v_nextMacroScope_5164_);
lean_ctor_set(v_reuseFailAlloc_5187_, 2, v_ngen_5165_);
lean_ctor_set(v_reuseFailAlloc_5187_, 3, v_auxDeclNGen_5166_);
lean_ctor_set(v_reuseFailAlloc_5187_, 4, v___x_5182_);
lean_ctor_set(v_reuseFailAlloc_5187_, 5, v_cache_5167_);
lean_ctor_set(v_reuseFailAlloc_5187_, 6, v_recordedDeps_5168_);
lean_ctor_set(v_reuseFailAlloc_5187_, 7, v_messages_5169_);
lean_ctor_set(v_reuseFailAlloc_5187_, 8, v_infoState_5170_);
lean_ctor_set(v_reuseFailAlloc_5187_, 9, v_snapshotTasks_5171_);
v___x_5184_ = v_reuseFailAlloc_5187_;
goto v_reusejp_5183_;
}
v_reusejp_5183_:
{
lean_object* v___x_5185_; lean_object* v___x_5186_; 
v___x_5185_ = lean_st_ref_put(v___y_5121_, v___x_5184_);
v___x_5186_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5123_);
return v___x_5186_;
}
}
}
}
}
else
{
goto v___jp_5154_;
}
}
else
{
goto v___jp_5154_;
}
}
v___jp_5191_:
{
double v___x_5193_; double v___x_5194_; double v___x_5195_; uint8_t v___x_5196_; 
v___x_5193_ = lean_unbox_float(v_snd_5140_);
v___x_5194_ = lean_unbox_float(v_fst_5139_);
v___x_5195_ = lean_float_sub(v___x_5193_, v___x_5194_);
v___x_5196_ = lean_float_decLt(v___y_5192_, v___x_5195_);
v___y_5160_ = v___x_5196_;
goto v___jp_5159_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5207_, lean_object* v_collapsed_5208_, lean_object* v_tag_5209_, lean_object* v_opts_5210_, lean_object* v_clsEnabled_5211_, lean_object* v_oldTraces_5212_, lean_object* v_msg_5213_, lean_object* v_resStartStop_5214_, lean_object* v___y_5215_, lean_object* v___y_5216_, lean_object* v___y_5217_, lean_object* v___y_5218_, lean_object* v___y_5219_){
_start:
{
uint8_t v_collapsed_boxed_5220_; uint8_t v_clsEnabled_boxed_5221_; lean_object* v_res_5222_; 
v_collapsed_boxed_5220_ = lean_unbox(v_collapsed_5208_);
v_clsEnabled_boxed_5221_ = lean_unbox(v_clsEnabled_5211_);
v_res_5222_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5207_, v_collapsed_boxed_5220_, v_tag_5209_, v_opts_5210_, v_clsEnabled_boxed_5221_, v_oldTraces_5212_, v_msg_5213_, v_resStartStop_5214_, v___y_5215_, v___y_5216_, v___y_5217_, v___y_5218_);
lean_dec(v___y_5218_);
lean_dec_ref(v___y_5217_);
lean_dec(v___y_5216_);
lean_dec_ref(v___y_5215_);
lean_dec_ref(v_opts_5210_);
return v_res_5222_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5227_; lean_object* v___x_5228_; lean_object* v___x_5229_; 
v_cls_5227_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5228_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5229_ = l_Lean_Name_append(v___x_5228_, v_cls_5227_);
return v___x_5229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5230_, lean_object* v_a_5231_, lean_object* v_a_5232_, lean_object* v_a_5233_, lean_object* v_a_5234_){
_start:
{
lean_object* v___y_5237_; lean_object* v_toCold_5255_; lean_object* v_options_5256_; lean_object* v_inheritedTraceOptions_5257_; uint8_t v_hasTrace_5258_; lean_object* v_cls_5259_; uint8_t v___x_5260_; 
v_toCold_5255_ = lean_ctor_get(v_a_5233_, 0);
v_options_5256_ = lean_ctor_get(v_toCold_5255_, 2);
v_inheritedTraceOptions_5257_ = lean_ctor_get(v_toCold_5255_, 11);
v_hasTrace_5258_ = lean_ctor_get_uint8(v_options_5256_, sizeof(void*)*1);
v_cls_5259_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5260_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5230_);
if (v_hasTrace_5258_ == 0)
{
lean_object* v___x_5261_; 
v___x_5261_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5260_, v_e_5230_, v_cls_5259_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
v___y_5237_ = v___x_5261_;
goto v___jp_5236_;
}
else
{
lean_object* v___f_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; uint8_t v___x_5265_; lean_object* v___y_5267_; lean_object* v___y_5268_; lean_object* v_a_5269_; lean_object* v___y_5282_; lean_object* v___y_5283_; lean_object* v_a_5284_; 
v___f_5262_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5263_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5264_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5257_, v_options_5256_, v___x_5264_);
if (v___x_5265_ == 0)
{
lean_object* v___x_5334_; uint8_t v___x_5335_; 
v___x_5334_ = l_Lean_trace_profiler;
v___x_5335_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5256_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5336_; 
v___x_5336_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5260_, v_e_5230_, v_cls_5259_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
v___y_5237_ = v___x_5336_;
goto v___jp_5236_;
}
else
{
goto v___jp_5293_;
}
}
else
{
goto v___jp_5293_;
}
v___jp_5266_:
{
lean_object* v___x_5270_; double v___x_5271_; double v___x_5272_; double v___x_5273_; double v___x_5274_; double v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; 
v___x_5270_ = lean_io_mono_nanos_now();
v___x_5271_ = lean_float_of_nat(v___y_5267_);
v___x_5272_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5273_ = lean_float_div(v___x_5271_, v___x_5272_);
v___x_5274_ = lean_float_of_nat(v___x_5270_);
v___x_5275_ = lean_float_div(v___x_5274_, v___x_5272_);
v___x_5276_ = lean_box_float(v___x_5273_);
v___x_5277_ = lean_box_float(v___x_5275_);
v___x_5278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5276_);
lean_ctor_set(v___x_5278_, 1, v___x_5277_);
v___x_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5279_, 0, v_a_5269_);
lean_ctor_set(v___x_5279_, 1, v___x_5278_);
v___x_5280_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5259_, v_hasTrace_5258_, v___x_5263_, v_options_5256_, v___x_5265_, v___y_5268_, v___f_5262_, v___x_5279_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
v___y_5237_ = v___x_5280_;
goto v___jp_5236_;
}
v___jp_5281_:
{
lean_object* v___x_5285_; double v___x_5286_; double v___x_5287_; lean_object* v___x_5288_; lean_object* v___x_5289_; lean_object* v___x_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
v___x_5285_ = lean_io_get_num_heartbeats();
v___x_5286_ = lean_float_of_nat(v___y_5282_);
v___x_5287_ = lean_float_of_nat(v___x_5285_);
v___x_5288_ = lean_box_float(v___x_5286_);
v___x_5289_ = lean_box_float(v___x_5287_);
v___x_5290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5290_, 0, v___x_5288_);
lean_ctor_set(v___x_5290_, 1, v___x_5289_);
v___x_5291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5291_, 0, v_a_5284_);
lean_ctor_set(v___x_5291_, 1, v___x_5290_);
v___x_5292_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5259_, v_hasTrace_5258_, v___x_5263_, v_options_5256_, v___x_5265_, v___y_5283_, v___f_5262_, v___x_5291_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
v___y_5237_ = v___x_5292_;
goto v___jp_5236_;
}
v___jp_5293_:
{
lean_object* v___x_5294_; lean_object* v_a_5295_; lean_object* v___x_5296_; uint8_t v___x_5297_; 
v___x_5294_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5234_);
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref(v___x_5294_);
v___x_5296_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5297_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5256_, v___x_5296_);
if (v___x_5297_ == 0)
{
lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5298_ = lean_io_mono_nanos_now();
v___x_5299_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5260_, v_e_5230_, v_cls_5259_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; lean_object* v___x_5302_; uint8_t v_isShared_5303_; uint8_t v_isSharedCheck_5307_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5307_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5307_ == 0)
{
v___x_5302_ = v___x_5299_;
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
else
{
lean_inc(v_a_5300_);
lean_dec(v___x_5299_);
v___x_5302_ = lean_box(0);
v_isShared_5303_ = v_isSharedCheck_5307_;
goto v_resetjp_5301_;
}
v_resetjp_5301_:
{
lean_object* v___x_5305_; 
if (v_isShared_5303_ == 0)
{
lean_ctor_set_tag(v___x_5302_, 1);
v___x_5305_ = v___x_5302_;
goto v_reusejp_5304_;
}
else
{
lean_object* v_reuseFailAlloc_5306_; 
v_reuseFailAlloc_5306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5300_);
v___x_5305_ = v_reuseFailAlloc_5306_;
goto v_reusejp_5304_;
}
v_reusejp_5304_:
{
v___y_5267_ = v___x_5298_;
v___y_5268_ = v_a_5295_;
v_a_5269_ = v___x_5305_;
goto v___jp_5266_;
}
}
}
else
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
v_a_5308_ = lean_ctor_get(v___x_5299_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5299_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5299_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5299_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
lean_ctor_set_tag(v___x_5310_, 0);
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
v___y_5267_ = v___x_5298_;
v___y_5268_ = v_a_5295_;
v_a_5269_ = v___x_5313_;
goto v___jp_5266_;
}
}
}
}
else
{
lean_object* v___x_5316_; lean_object* v___x_5317_; 
v___x_5316_ = lean_io_get_num_heartbeats();
v___x_5317_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5260_, v_e_5230_, v_cls_5259_, v_a_5231_, v_a_5232_, v_a_5233_, v_a_5234_);
if (lean_obj_tag(v___x_5317_) == 0)
{
lean_object* v_a_5318_; lean_object* v___x_5320_; uint8_t v_isShared_5321_; uint8_t v_isSharedCheck_5325_; 
v_a_5318_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5325_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5325_ == 0)
{
v___x_5320_ = v___x_5317_;
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
else
{
lean_inc(v_a_5318_);
lean_dec(v___x_5317_);
v___x_5320_ = lean_box(0);
v_isShared_5321_ = v_isSharedCheck_5325_;
goto v_resetjp_5319_;
}
v_resetjp_5319_:
{
lean_object* v___x_5323_; 
if (v_isShared_5321_ == 0)
{
lean_ctor_set_tag(v___x_5320_, 1);
v___x_5323_ = v___x_5320_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v_a_5318_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
v___y_5282_ = v___x_5316_;
v___y_5283_ = v_a_5295_;
v_a_5284_ = v___x_5323_;
goto v___jp_5281_;
}
}
}
else
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5333_; 
v_a_5326_ = lean_ctor_get(v___x_5317_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5317_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5328_ = v___x_5317_;
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5317_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___x_5331_; 
if (v_isShared_5329_ == 0)
{
lean_ctor_set_tag(v___x_5328_, 0);
v___x_5331_ = v___x_5328_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
v___y_5282_ = v___x_5316_;
v___y_5283_ = v_a_5295_;
v_a_5284_ = v___x_5331_;
goto v___jp_5281_;
}
}
}
}
}
}
v___jp_5236_:
{
if (lean_obj_tag(v___y_5237_) == 0)
{
lean_object* v_a_5238_; lean_object* v___x_5240_; uint8_t v_isShared_5241_; uint8_t v_isSharedCheck_5246_; 
v_a_5238_ = lean_ctor_get(v___y_5237_, 0);
v_isSharedCheck_5246_ = !lean_is_exclusive(v___y_5237_);
if (v_isSharedCheck_5246_ == 0)
{
v___x_5240_ = v___y_5237_;
v_isShared_5241_ = v_isSharedCheck_5246_;
goto v_resetjp_5239_;
}
else
{
lean_inc(v_a_5238_);
lean_dec(v___y_5237_);
v___x_5240_ = lean_box(0);
v_isShared_5241_ = v_isSharedCheck_5246_;
goto v_resetjp_5239_;
}
v_resetjp_5239_:
{
lean_object* v_fst_5242_; lean_object* v___x_5244_; 
v_fst_5242_ = lean_ctor_get(v_a_5238_, 0);
lean_inc(v_fst_5242_);
lean_dec(v_a_5238_);
if (v_isShared_5241_ == 0)
{
lean_ctor_set(v___x_5240_, 0, v_fst_5242_);
v___x_5244_ = v___x_5240_;
goto v_reusejp_5243_;
}
else
{
lean_object* v_reuseFailAlloc_5245_; 
v_reuseFailAlloc_5245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5245_, 0, v_fst_5242_);
v___x_5244_ = v_reuseFailAlloc_5245_;
goto v_reusejp_5243_;
}
v_reusejp_5243_:
{
return v___x_5244_;
}
}
}
else
{
lean_object* v_a_5247_; lean_object* v___x_5249_; uint8_t v_isShared_5250_; uint8_t v_isSharedCheck_5254_; 
v_a_5247_ = lean_ctor_get(v___y_5237_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___y_5237_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5249_ = v___y_5237_;
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
else
{
lean_inc(v_a_5247_);
lean_dec(v___y_5237_);
v___x_5249_ = lean_box(0);
v_isShared_5250_ = v_isSharedCheck_5254_;
goto v_resetjp_5248_;
}
v_resetjp_5248_:
{
lean_object* v___x_5252_; 
if (v_isShared_5250_ == 0)
{
v___x_5252_ = v___x_5249_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_a_5247_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_, lean_object* v_a_5341_, lean_object* v_a_5342_){
_start:
{
lean_object* v_res_5343_; 
v_res_5343_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5337_, v_a_5338_, v_a_5339_, v_a_5340_, v_a_5341_);
lean_dec(v_a_5341_);
lean_dec_ref(v_a_5340_);
lean_dec(v_a_5339_);
lean_dec_ref(v_a_5338_);
return v_res_5343_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5344_, lean_object* v_x_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v___x_5351_; 
v___x_5351_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5345_);
return v___x_5351_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5352_, lean_object* v_x_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_, lean_object* v___y_5358_){
_start:
{
lean_object* v_res_5359_; 
v_res_5359_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5352_, v_x_5353_, v___y_5354_, v___y_5355_, v___y_5356_, v___y_5357_);
lean_dec(v___y_5357_);
lean_dec_ref(v___y_5356_);
lean_dec(v___y_5355_);
lean_dec_ref(v___y_5354_);
return v_res_5359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5360_, lean_object* v___y_5361_){
_start:
{
uint8_t v___x_5363_; 
v___x_5363_ = l_Lean_Expr_hasMVar(v_e_5360_);
if (v___x_5363_ == 0)
{
lean_object* v___x_5364_; 
v___x_5364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5364_, 0, v_e_5360_);
return v___x_5364_;
}
else
{
lean_object* v___x_5365_; lean_object* v_mctx_5366_; lean_object* v___x_5367_; lean_object* v_fst_5368_; lean_object* v_snd_5369_; lean_object* v___x_5370_; lean_object* v_cache_5371_; lean_object* v_zetaDeltaFVarIds_5372_; lean_object* v_postponed_5373_; lean_object* v_diag_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5383_; 
v___x_5365_ = lean_st_ref_get(v___y_5361_);
v_mctx_5366_ = lean_ctor_get(v___x_5365_, 0);
lean_inc_ref(v_mctx_5366_);
lean_dec(v___x_5365_);
v___x_5367_ = l_Lean_instantiateMVarsCore(v_mctx_5366_, v_e_5360_);
v_fst_5368_ = lean_ctor_get(v___x_5367_, 0);
lean_inc(v_fst_5368_);
v_snd_5369_ = lean_ctor_get(v___x_5367_, 1);
lean_inc(v_snd_5369_);
lean_dec_ref(v___x_5367_);
v___x_5370_ = lean_st_ref_take(v___y_5361_);
v_cache_5371_ = lean_ctor_get(v___x_5370_, 1);
v_zetaDeltaFVarIds_5372_ = lean_ctor_get(v___x_5370_, 2);
v_postponed_5373_ = lean_ctor_get(v___x_5370_, 3);
v_diag_5374_ = lean_ctor_get(v___x_5370_, 4);
v_isSharedCheck_5383_ = !lean_is_exclusive(v___x_5370_);
if (v_isSharedCheck_5383_ == 0)
{
lean_object* v_unused_5384_; 
v_unused_5384_ = lean_ctor_get(v___x_5370_, 0);
lean_dec(v_unused_5384_);
v___x_5376_ = v___x_5370_;
v_isShared_5377_ = v_isSharedCheck_5383_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_diag_5374_);
lean_inc(v_postponed_5373_);
lean_inc(v_zetaDeltaFVarIds_5372_);
lean_inc(v_cache_5371_);
lean_dec(v___x_5370_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5383_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v_snd_5369_);
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v_snd_5369_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v_cache_5371_);
lean_ctor_set(v_reuseFailAlloc_5382_, 2, v_zetaDeltaFVarIds_5372_);
lean_ctor_set(v_reuseFailAlloc_5382_, 3, v_postponed_5373_);
lean_ctor_set(v_reuseFailAlloc_5382_, 4, v_diag_5374_);
v___x_5379_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
lean_object* v___x_5380_; lean_object* v___x_5381_; 
v___x_5380_ = lean_st_ref_put(v___y_5361_, v___x_5379_);
v___x_5381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5381_, 0, v_fst_5368_);
return v___x_5381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_){
_start:
{
lean_object* v_res_5388_; 
v_res_5388_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5385_, v___y_5386_);
lean_dec(v___y_5386_);
return v_res_5388_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5389_, lean_object* v___y_5390_, lean_object* v___y_5391_, lean_object* v___y_5392_, lean_object* v___y_5393_){
_start:
{
lean_object* v___x_5395_; 
v___x_5395_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5389_, v___y_5391_);
return v___x_5395_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v_res_5402_; 
v_res_5402_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_);
lean_dec(v___y_5400_);
lean_dec_ref(v___y_5399_);
lean_dec(v___y_5398_);
lean_dec_ref(v___y_5397_);
return v_res_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5403_, lean_object* v_opts_5404_, lean_object* v_act_5405_, lean_object* v_decl_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_){
_start:
{
lean_object* v___x_5412_; lean_object* v___x_5413_; 
lean_inc(v___y_5410_);
lean_inc_ref(v___y_5409_);
lean_inc(v___y_5408_);
lean_inc_ref(v___y_5407_);
v___x_5412_ = lean_apply_4(v_act_5405_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
v___x_5413_ = l_Lean_profileitIOUnsafe___redArg(v_category_5403_, v_opts_5404_, v___x_5412_, v_decl_5406_);
return v___x_5413_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5414_, lean_object* v_opts_5415_, lean_object* v_act_5416_, lean_object* v_decl_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_, lean_object* v___y_5422_){
_start:
{
lean_object* v_res_5423_; 
v_res_5423_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5414_, v_opts_5415_, v_act_5416_, v_decl_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
lean_dec(v___y_5421_);
lean_dec_ref(v___y_5420_);
lean_dec(v___y_5419_);
lean_dec_ref(v___y_5418_);
lean_dec_ref(v_opts_5415_);
lean_dec_ref(v_category_5414_);
return v_res_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5424_, lean_object* v_category_5425_, lean_object* v_opts_5426_, lean_object* v_act_5427_, lean_object* v_decl_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_){
_start:
{
lean_object* v___x_5434_; 
v___x_5434_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5425_, v_opts_5426_, v_act_5427_, v_decl_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5435_, lean_object* v_category_5436_, lean_object* v_opts_5437_, lean_object* v_act_5438_, lean_object* v_decl_5439_, lean_object* v___y_5440_, lean_object* v___y_5441_, lean_object* v___y_5442_, lean_object* v___y_5443_, lean_object* v___y_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5435_, v_category_5436_, v_opts_5437_, v_act_5438_, v_decl_5439_, v___y_5440_, v___y_5441_, v___y_5442_, v___y_5443_);
lean_dec(v___y_5443_);
lean_dec_ref(v___y_5442_);
lean_dec(v___y_5441_);
lean_dec_ref(v___y_5440_);
lean_dec_ref(v_opts_5437_);
lean_dec_ref(v_category_5436_);
return v_res_5445_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5446_, uint8_t v_isExporting_5447_, lean_object* v___x_5448_, lean_object* v___y_5449_, lean_object* v___x_5450_, lean_object* v_a_x3f_5451_){
_start:
{
lean_object* v___x_5453_; lean_object* v_env_5454_; lean_object* v_nextMacroScope_5455_; lean_object* v_ngen_5456_; lean_object* v_auxDeclNGen_5457_; lean_object* v_traceState_5458_; lean_object* v_recordedDeps_5459_; lean_object* v_messages_5460_; lean_object* v_infoState_5461_; lean_object* v_snapshotTasks_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5487_; 
v___x_5453_ = lean_st_ref_take(v___y_5446_);
v_env_5454_ = lean_ctor_get(v___x_5453_, 0);
v_nextMacroScope_5455_ = lean_ctor_get(v___x_5453_, 1);
v_ngen_5456_ = lean_ctor_get(v___x_5453_, 2);
v_auxDeclNGen_5457_ = lean_ctor_get(v___x_5453_, 3);
v_traceState_5458_ = lean_ctor_get(v___x_5453_, 4);
v_recordedDeps_5459_ = lean_ctor_get(v___x_5453_, 6);
v_messages_5460_ = lean_ctor_get(v___x_5453_, 7);
v_infoState_5461_ = lean_ctor_get(v___x_5453_, 8);
v_snapshotTasks_5462_ = lean_ctor_get(v___x_5453_, 9);
v_isSharedCheck_5487_ = !lean_is_exclusive(v___x_5453_);
if (v_isSharedCheck_5487_ == 0)
{
lean_object* v_unused_5488_; 
v_unused_5488_ = lean_ctor_get(v___x_5453_, 5);
lean_dec(v_unused_5488_);
v___x_5464_ = v___x_5453_;
v_isShared_5465_ = v_isSharedCheck_5487_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_snapshotTasks_5462_);
lean_inc(v_infoState_5461_);
lean_inc(v_messages_5460_);
lean_inc(v_recordedDeps_5459_);
lean_inc(v_traceState_5458_);
lean_inc(v_auxDeclNGen_5457_);
lean_inc(v_ngen_5456_);
lean_inc(v_nextMacroScope_5455_);
lean_inc(v_env_5454_);
lean_dec(v___x_5453_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5487_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5466_; lean_object* v___x_5468_; 
v___x_5466_ = l_Lean_Environment_setExporting(v_env_5454_, v_isExporting_5447_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 5, v___x_5448_);
lean_ctor_set(v___x_5464_, 0, v___x_5466_);
v___x_5468_ = v___x_5464_;
goto v_reusejp_5467_;
}
else
{
lean_object* v_reuseFailAlloc_5486_; 
v_reuseFailAlloc_5486_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5486_, 0, v___x_5466_);
lean_ctor_set(v_reuseFailAlloc_5486_, 1, v_nextMacroScope_5455_);
lean_ctor_set(v_reuseFailAlloc_5486_, 2, v_ngen_5456_);
lean_ctor_set(v_reuseFailAlloc_5486_, 3, v_auxDeclNGen_5457_);
lean_ctor_set(v_reuseFailAlloc_5486_, 4, v_traceState_5458_);
lean_ctor_set(v_reuseFailAlloc_5486_, 5, v___x_5448_);
lean_ctor_set(v_reuseFailAlloc_5486_, 6, v_recordedDeps_5459_);
lean_ctor_set(v_reuseFailAlloc_5486_, 7, v_messages_5460_);
lean_ctor_set(v_reuseFailAlloc_5486_, 8, v_infoState_5461_);
lean_ctor_set(v_reuseFailAlloc_5486_, 9, v_snapshotTasks_5462_);
v___x_5468_ = v_reuseFailAlloc_5486_;
goto v_reusejp_5467_;
}
v_reusejp_5467_:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v_mctx_5471_; lean_object* v_zetaDeltaFVarIds_5472_; lean_object* v_postponed_5473_; lean_object* v_diag_5474_; lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5484_; 
v___x_5469_ = lean_st_ref_put(v___y_5446_, v___x_5468_);
v___x_5470_ = lean_st_ref_take(v___y_5449_);
v_mctx_5471_ = lean_ctor_get(v___x_5470_, 0);
v_zetaDeltaFVarIds_5472_ = lean_ctor_get(v___x_5470_, 2);
v_postponed_5473_ = lean_ctor_get(v___x_5470_, 3);
v_diag_5474_ = lean_ctor_get(v___x_5470_, 4);
v_isSharedCheck_5484_ = !lean_is_exclusive(v___x_5470_);
if (v_isSharedCheck_5484_ == 0)
{
lean_object* v_unused_5485_; 
v_unused_5485_ = lean_ctor_get(v___x_5470_, 1);
lean_dec(v_unused_5485_);
v___x_5476_ = v___x_5470_;
v_isShared_5477_ = v_isSharedCheck_5484_;
goto v_resetjp_5475_;
}
else
{
lean_inc(v_diag_5474_);
lean_inc(v_postponed_5473_);
lean_inc(v_zetaDeltaFVarIds_5472_);
lean_inc(v_mctx_5471_);
lean_dec(v___x_5470_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5484_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5478_; lean_object* v___x_5480_; 
v___x_5478_ = lean_box(0);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 1, v___x_5450_);
v___x_5480_ = v___x_5476_;
goto v_reusejp_5479_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_mctx_5471_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5483_, 2, v_zetaDeltaFVarIds_5472_);
lean_ctor_set(v_reuseFailAlloc_5483_, 3, v_postponed_5473_);
lean_ctor_set(v_reuseFailAlloc_5483_, 4, v_diag_5474_);
v___x_5480_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5479_;
}
v_reusejp_5479_:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; 
v___x_5481_ = lean_st_ref_put(v___y_5449_, v___x_5480_);
v___x_5482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5482_, 0, v___x_5478_);
return v___x_5482_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5489_, lean_object* v_isExporting_5490_, lean_object* v___x_5491_, lean_object* v___y_5492_, lean_object* v___x_5493_, lean_object* v_a_x3f_5494_, lean_object* v___y_5495_){
_start:
{
uint8_t v_isExporting_boxed_5496_; lean_object* v_res_5497_; 
v_isExporting_boxed_5496_ = lean_unbox(v_isExporting_5490_);
v_res_5497_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5489_, v_isExporting_boxed_5496_, v___x_5491_, v___y_5492_, v___x_5493_, v_a_x3f_5494_);
lean_dec(v_a_x3f_5494_);
lean_dec(v___y_5492_);
lean_dec(v___y_5489_);
return v_res_5497_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5498_; lean_object* v___x_5499_; 
v___x_5498_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__0);
v___x_5499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5499_, 0, v___x_5498_);
return v___x_5499_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5500_; lean_object* v___x_5501_; 
v___x_5500_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5501_, 0, v___x_5500_);
lean_ctor_set(v___x_5501_, 1, v___x_5500_);
return v___x_5501_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5502_; lean_object* v___x_5503_; 
v___x_5502_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5503_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5503_, 0, v___x_5502_);
lean_ctor_set(v___x_5503_, 1, v___x_5502_);
lean_ctor_set(v___x_5503_, 2, v___x_5502_);
lean_ctor_set(v___x_5503_, 3, v___x_5502_);
lean_ctor_set(v___x_5503_, 4, v___x_5502_);
lean_ctor_set(v___x_5503_, 5, v___x_5502_);
return v___x_5503_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5504_, uint8_t v_isExporting_5505_, lean_object* v___y_5506_, lean_object* v___y_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_){
_start:
{
lean_object* v___x_5511_; lean_object* v_env_5512_; lean_object* v___x_5513_; uint8_t v_isModule_5514_; 
v___x_5511_ = lean_st_ref_get(v___y_5509_);
v_env_5512_ = lean_ctor_get(v___x_5511_, 0);
lean_inc_ref(v_env_5512_);
lean_dec(v___x_5511_);
v___x_5513_ = l_Lean_Environment_header(v_env_5512_);
v_isModule_5514_ = lean_ctor_get_uint8(v___x_5513_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5513_);
if (v_isModule_5514_ == 0)
{
lean_object* v___x_5515_; 
lean_dec_ref(v_env_5512_);
lean_inc(v___y_5509_);
lean_inc_ref(v___y_5508_);
lean_inc(v___y_5507_);
lean_inc_ref(v___y_5506_);
v___x_5515_ = lean_apply_5(v_x_5504_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, lean_box(0));
return v___x_5515_;
}
else
{
uint8_t v_isExporting_5516_; 
v_isExporting_5516_ = lean_ctor_get_uint8(v_env_5512_, sizeof(void*)*8);
lean_dec_ref(v_env_5512_);
if (v_isExporting_5505_ == 0)
{
if (v_isExporting_5516_ == 0)
{
lean_object* v___x_5583_; 
lean_inc(v___y_5509_);
lean_inc_ref(v___y_5508_);
lean_inc(v___y_5507_);
lean_inc_ref(v___y_5506_);
v___x_5583_ = lean_apply_5(v_x_5504_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, lean_box(0));
return v___x_5583_;
}
else
{
goto v___jp_5517_;
}
}
else
{
if (v_isExporting_5516_ == 0)
{
goto v___jp_5517_;
}
else
{
lean_object* v___x_5584_; 
lean_inc(v___y_5509_);
lean_inc_ref(v___y_5508_);
lean_inc(v___y_5507_);
lean_inc_ref(v___y_5506_);
v___x_5584_ = lean_apply_5(v_x_5504_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, lean_box(0));
return v___x_5584_;
}
}
v___jp_5517_:
{
lean_object* v___x_5518_; lean_object* v_env_5519_; lean_object* v_nextMacroScope_5520_; lean_object* v_ngen_5521_; lean_object* v_auxDeclNGen_5522_; lean_object* v_traceState_5523_; lean_object* v_recordedDeps_5524_; lean_object* v_messages_5525_; lean_object* v_infoState_5526_; lean_object* v_snapshotTasks_5527_; lean_object* v___x_5529_; uint8_t v_isShared_5530_; uint8_t v_isSharedCheck_5581_; 
v___x_5518_ = lean_st_ref_take(v___y_5509_);
v_env_5519_ = lean_ctor_get(v___x_5518_, 0);
v_nextMacroScope_5520_ = lean_ctor_get(v___x_5518_, 1);
v_ngen_5521_ = lean_ctor_get(v___x_5518_, 2);
v_auxDeclNGen_5522_ = lean_ctor_get(v___x_5518_, 3);
v_traceState_5523_ = lean_ctor_get(v___x_5518_, 4);
v_recordedDeps_5524_ = lean_ctor_get(v___x_5518_, 6);
v_messages_5525_ = lean_ctor_get(v___x_5518_, 7);
v_infoState_5526_ = lean_ctor_get(v___x_5518_, 8);
v_snapshotTasks_5527_ = lean_ctor_get(v___x_5518_, 9);
v_isSharedCheck_5581_ = !lean_is_exclusive(v___x_5518_);
if (v_isSharedCheck_5581_ == 0)
{
lean_object* v_unused_5582_; 
v_unused_5582_ = lean_ctor_get(v___x_5518_, 5);
lean_dec(v_unused_5582_);
v___x_5529_ = v___x_5518_;
v_isShared_5530_ = v_isSharedCheck_5581_;
goto v_resetjp_5528_;
}
else
{
lean_inc(v_snapshotTasks_5527_);
lean_inc(v_infoState_5526_);
lean_inc(v_messages_5525_);
lean_inc(v_recordedDeps_5524_);
lean_inc(v_traceState_5523_);
lean_inc(v_auxDeclNGen_5522_);
lean_inc(v_ngen_5521_);
lean_inc(v_nextMacroScope_5520_);
lean_inc(v_env_5519_);
lean_dec(v___x_5518_);
v___x_5529_ = lean_box(0);
v_isShared_5530_ = v_isSharedCheck_5581_;
goto v_resetjp_5528_;
}
v_resetjp_5528_:
{
lean_object* v___x_5531_; lean_object* v___x_5532_; lean_object* v___x_5534_; 
v___x_5531_ = l_Lean_Environment_setExporting(v_env_5519_, v_isExporting_5505_);
v___x_5532_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
if (v_isShared_5530_ == 0)
{
lean_ctor_set(v___x_5529_, 5, v___x_5532_);
lean_ctor_set(v___x_5529_, 0, v___x_5531_);
v___x_5534_ = v___x_5529_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5580_; 
v_reuseFailAlloc_5580_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5580_, 0, v___x_5531_);
lean_ctor_set(v_reuseFailAlloc_5580_, 1, v_nextMacroScope_5520_);
lean_ctor_set(v_reuseFailAlloc_5580_, 2, v_ngen_5521_);
lean_ctor_set(v_reuseFailAlloc_5580_, 3, v_auxDeclNGen_5522_);
lean_ctor_set(v_reuseFailAlloc_5580_, 4, v_traceState_5523_);
lean_ctor_set(v_reuseFailAlloc_5580_, 5, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5580_, 6, v_recordedDeps_5524_);
lean_ctor_set(v_reuseFailAlloc_5580_, 7, v_messages_5525_);
lean_ctor_set(v_reuseFailAlloc_5580_, 8, v_infoState_5526_);
lean_ctor_set(v_reuseFailAlloc_5580_, 9, v_snapshotTasks_5527_);
v___x_5534_ = v_reuseFailAlloc_5580_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5535_; lean_object* v___x_5536_; lean_object* v_mctx_5537_; lean_object* v_zetaDeltaFVarIds_5538_; lean_object* v_postponed_5539_; lean_object* v_diag_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5578_; 
v___x_5535_ = lean_st_ref_put(v___y_5509_, v___x_5534_);
v___x_5536_ = lean_st_ref_take(v___y_5507_);
v_mctx_5537_ = lean_ctor_get(v___x_5536_, 0);
v_zetaDeltaFVarIds_5538_ = lean_ctor_get(v___x_5536_, 2);
v_postponed_5539_ = lean_ctor_get(v___x_5536_, 3);
v_diag_5540_ = lean_ctor_get(v___x_5536_, 4);
v_isSharedCheck_5578_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5578_ == 0)
{
lean_object* v_unused_5579_; 
v_unused_5579_ = lean_ctor_get(v___x_5536_, 1);
lean_dec(v_unused_5579_);
v___x_5542_ = v___x_5536_;
v_isShared_5543_ = v_isSharedCheck_5578_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_diag_5540_);
lean_inc(v_postponed_5539_);
lean_inc(v_zetaDeltaFVarIds_5538_);
lean_inc(v_mctx_5537_);
lean_dec(v___x_5536_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5578_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5544_; lean_object* v___x_5546_; 
v___x_5544_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5543_ == 0)
{
lean_ctor_set(v___x_5542_, 1, v___x_5544_);
v___x_5546_ = v___x_5542_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v_mctx_5537_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5577_, 2, v_zetaDeltaFVarIds_5538_);
lean_ctor_set(v_reuseFailAlloc_5577_, 3, v_postponed_5539_);
lean_ctor_set(v_reuseFailAlloc_5577_, 4, v_diag_5540_);
v___x_5546_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5547_; lean_object* v_r_5548_; 
v___x_5547_ = lean_st_ref_put(v___y_5507_, v___x_5546_);
lean_inc(v___y_5509_);
lean_inc_ref(v___y_5508_);
lean_inc(v___y_5507_);
lean_inc_ref(v___y_5506_);
v_r_5548_ = lean_apply_5(v_x_5504_, v___y_5506_, v___y_5507_, v___y_5508_, v___y_5509_, lean_box(0));
if (lean_obj_tag(v_r_5548_) == 0)
{
lean_object* v_a_5549_; lean_object* v___x_5551_; uint8_t v_isShared_5552_; uint8_t v_isSharedCheck_5565_; 
v_a_5549_ = lean_ctor_get(v_r_5548_, 0);
v_isSharedCheck_5565_ = !lean_is_exclusive(v_r_5548_);
if (v_isSharedCheck_5565_ == 0)
{
v___x_5551_ = v_r_5548_;
v_isShared_5552_ = v_isSharedCheck_5565_;
goto v_resetjp_5550_;
}
else
{
lean_inc(v_a_5549_);
lean_dec(v_r_5548_);
v___x_5551_ = lean_box(0);
v_isShared_5552_ = v_isSharedCheck_5565_;
goto v_resetjp_5550_;
}
v_resetjp_5550_:
{
lean_object* v___x_5554_; 
lean_inc(v_a_5549_);
if (v_isShared_5552_ == 0)
{
lean_ctor_set_tag(v___x_5551_, 1);
v___x_5554_ = v___x_5551_;
goto v_reusejp_5553_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v_a_5549_);
v___x_5554_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5553_;
}
v_reusejp_5553_:
{
lean_object* v___x_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5562_; 
v___x_5555_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5509_, v_isExporting_5516_, v___x_5532_, v___y_5507_, v___x_5544_, v___x_5554_);
lean_dec_ref(v___x_5554_);
v_isSharedCheck_5562_ = !lean_is_exclusive(v___x_5555_);
if (v_isSharedCheck_5562_ == 0)
{
lean_object* v_unused_5563_; 
v_unused_5563_ = lean_ctor_get(v___x_5555_, 0);
lean_dec(v_unused_5563_);
v___x_5557_ = v___x_5555_;
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
else
{
lean_dec(v___x_5555_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5562_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v___x_5560_; 
if (v_isShared_5558_ == 0)
{
lean_ctor_set(v___x_5557_, 0, v_a_5549_);
v___x_5560_ = v___x_5557_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5561_; 
v_reuseFailAlloc_5561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5561_, 0, v_a_5549_);
v___x_5560_ = v_reuseFailAlloc_5561_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
return v___x_5560_;
}
}
}
}
}
else
{
lean_object* v_a_5566_; lean_object* v___x_5567_; lean_object* v___x_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5575_; 
v_a_5566_ = lean_ctor_get(v_r_5548_, 0);
lean_inc(v_a_5566_);
lean_dec_ref_known(v_r_5548_, 1);
v___x_5567_ = lean_box(0);
v___x_5568_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5509_, v_isExporting_5516_, v___x_5532_, v___y_5507_, v___x_5544_, v___x_5567_);
v_isSharedCheck_5575_ = !lean_is_exclusive(v___x_5568_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; 
v_unused_5576_ = lean_ctor_get(v___x_5568_, 0);
lean_dec(v_unused_5576_);
v___x_5570_ = v___x_5568_;
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
else
{
lean_dec(v___x_5568_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5575_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5573_; 
if (v_isShared_5571_ == 0)
{
lean_ctor_set_tag(v___x_5570_, 1);
lean_ctor_set(v___x_5570_, 0, v_a_5566_);
v___x_5573_ = v___x_5570_;
goto v_reusejp_5572_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v_a_5566_);
v___x_5573_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5572_;
}
v_reusejp_5572_:
{
return v___x_5573_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5585_, lean_object* v_isExporting_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_){
_start:
{
uint8_t v_isExporting_boxed_5592_; lean_object* v_res_5593_; 
v_isExporting_boxed_5592_ = lean_unbox(v_isExporting_5586_);
v_res_5593_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5585_, v_isExporting_boxed_5592_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
return v_res_5593_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5594_, uint8_t v_when_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_, lean_object* v___y_5599_){
_start:
{
if (v_when_5595_ == 0)
{
lean_object* v___x_5601_; 
lean_inc(v___y_5599_);
lean_inc_ref(v___y_5598_);
lean_inc(v___y_5597_);
lean_inc_ref(v___y_5596_);
v___x_5601_ = lean_apply_5(v_x_5594_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_, lean_box(0));
return v___x_5601_;
}
else
{
uint8_t v___x_5602_; lean_object* v___x_5603_; 
v___x_5602_ = 0;
v___x_5603_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5594_, v___x_5602_, v___y_5596_, v___y_5597_, v___y_5598_, v___y_5599_);
return v___x_5603_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5604_, lean_object* v_when_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_){
_start:
{
uint8_t v_when_boxed_5611_; lean_object* v_res_5612_; 
v_when_boxed_5611_ = lean_unbox(v_when_5605_);
v_res_5612_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5604_, v_when_boxed_5611_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5608_);
lean_dec(v___y_5607_);
lean_dec_ref(v___y_5606_);
return v_res_5612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_){
_start:
{
lean_object* v___x_5619_; lean_object* v_a_5620_; lean_object* v___x_5621_; uint8_t v___x_5622_; lean_object* v___x_5623_; 
v___x_5619_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5613_, v___y_5615_);
v_a_5620_ = lean_ctor_get(v___x_5619_, 0);
lean_inc(v_a_5620_);
lean_dec_ref(v___x_5619_);
v___x_5621_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5621_, 0, v_a_5620_);
v___x_5622_ = 1;
v___x_5623_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5621_, v___x_5622_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_);
return v___x_5623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5624_, lean_object* v___y_5625_, lean_object* v___y_5626_, lean_object* v___y_5627_, lean_object* v___y_5628_, lean_object* v___y_5629_){
_start:
{
lean_object* v_res_5630_; 
v_res_5630_ = l_Lean_Meta_letToHave___lam__0(v_e_5624_, v___y_5625_, v___y_5626_, v___y_5627_, v___y_5628_);
lean_dec(v___y_5628_);
lean_dec_ref(v___y_5627_);
lean_dec(v___y_5626_);
lean_dec_ref(v___y_5625_);
return v_res_5630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_){
_start:
{
lean_object* v___f_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5642_; 
v___f_5638_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5638_, 0, v_e_5632_);
v___x_5639_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_5635_);
v___x_5640_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5641_ = lean_box(0);
v___x_5642_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5640_, v___x_5639_, v___f_5638_, v___x_5641_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_);
lean_dec_ref(v___x_5639_);
return v___x_5642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5643_, lean_object* v_a_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_, lean_object* v_a_5647_, lean_object* v_a_5648_){
_start:
{
lean_object* v_res_5649_; 
v_res_5649_ = l_Lean_Meta_letToHave(v_e_5643_, v_a_5644_, v_a_5645_, v_a_5646_, v_a_5647_);
lean_dec(v_a_5647_);
lean_dec_ref(v_a_5646_);
lean_dec(v_a_5645_);
lean_dec_ref(v_a_5644_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5650_, lean_object* v_x_5651_, uint8_t v_isExporting_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_, lean_object* v___y_5656_){
_start:
{
lean_object* v___x_5658_; 
v___x_5658_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5651_, v_isExporting_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_);
return v___x_5658_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5659_, lean_object* v_x_5660_, lean_object* v_isExporting_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_, lean_object* v___y_5665_, lean_object* v___y_5666_){
_start:
{
uint8_t v_isExporting_boxed_5667_; lean_object* v_res_5668_; 
v_isExporting_boxed_5667_ = lean_unbox(v_isExporting_5661_);
v_res_5668_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5659_, v_x_5660_, v_isExporting_boxed_5667_, v___y_5662_, v___y_5663_, v___y_5664_, v___y_5665_);
lean_dec(v___y_5665_);
lean_dec_ref(v___y_5664_);
lean_dec(v___y_5663_);
lean_dec_ref(v___y_5662_);
return v_res_5668_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5669_, lean_object* v_x_5670_, uint8_t v_when_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_, lean_object* v___y_5675_){
_start:
{
lean_object* v___x_5677_; 
v___x_5677_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5670_, v_when_5671_, v___y_5672_, v___y_5673_, v___y_5674_, v___y_5675_);
return v___x_5677_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5678_, lean_object* v_x_5679_, lean_object* v_when_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_, lean_object* v___y_5685_){
_start:
{
uint8_t v_when_boxed_5686_; lean_object* v_res_5687_; 
v_when_boxed_5686_ = lean_unbox(v_when_5680_);
v_res_5687_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5678_, v_x_5679_, v_when_boxed_5686_, v___y_5681_, v___y_5682_, v___y_5683_, v___y_5684_);
lean_dec(v___y_5684_);
lean_dec_ref(v___y_5683_);
lean_dec(v___y_5682_);
lean_dec_ref(v___y_5681_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5744_; uint8_t v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5747_; 
v___x_5744_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5745_ = 0;
v___x_5746_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5747_ = l_Lean_registerTraceClass(v___x_5744_, v___x_5745_, v___x_5746_);
if (lean_obj_tag(v___x_5747_) == 0)
{
lean_object* v___x_5748_; lean_object* v___x_5749_; 
lean_dec_ref_known(v___x_5747_, 1);
v___x_5748_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5749_ = l_Lean_registerTraceClass(v___x_5748_, v___x_5745_, v___x_5746_);
return v___x_5749_;
}
else
{
return v___x_5747_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5750_){
_start:
{
lean_object* v_res_5751_; 
v_res_5751_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5751_;
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
