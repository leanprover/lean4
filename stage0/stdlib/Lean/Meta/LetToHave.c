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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* l_Lean_Meta_ProjReductionKind_ctorIdx(uint8_t);
uint8_t l_Lean_Meta_instBEqEtaStructMode_beq(uint8_t, uint8_t);
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
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6;
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
lean_object* v___x_199_; lean_object* v_count_200_; lean_object* v_results_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_217_; 
v___x_199_ = lean_st_ref_take(v_a_175_);
v_count_200_ = lean_ctor_get(v___x_199_, 0);
v_results_201_ = lean_ctor_get(v___x_199_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_199_);
if (v_isSharedCheck_217_ == 0)
{
v___x_203_ = v___x_199_;
v_isShared_204_ = v_isSharedCheck_217_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_results_201_);
lean_inc(v_count_200_);
lean_dec(v___x_199_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_217_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_205_; lean_object* v___x_207_; 
lean_inc(v_a_195_);
v___x_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_205_, 0, v_a_195_);
lean_inc_ref(v_expr_190_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 1, v___x_205_);
v___x_207_ = v___x_192_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_expr_190_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v___x_205_);
v___x_207_ = v_reuseFailAlloc_216_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_201_, v_expr_190_, v___x_207_);
if (v_isShared_204_ == 0)
{
lean_ctor_set(v___x_203_, 1, v___x_208_);
v___x_210_ = v___x_203_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_count_200_);
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
lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_357_ = lean_unsigned_to_nat(1u);
v___x_358_ = lean_nat_add(v_count_352_, v___x_357_);
lean_dec(v_count_352_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 0, v___x_358_);
v___x_360_ = v___x_355_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_results_353_);
v___x_360_ = v_reuseFailAlloc_364_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; 
v___x_361_ = lean_st_ref_put(v_a_349_, v___x_360_);
v___x_362_ = lean_box(0);
v___x_363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
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
v___x_1171_ = l_instMonadEIO(lean_box(0));
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
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___f_1236_; lean_object* v___x_1419__overap_1237_; lean_object* v___x_1238_; 
v___x_1233_ = l_StateRefT_x27_instMonad___redArg(v___x_1232_);
v___x_1234_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1235_ = l_instInhabitedOfMonad___redArg(v___x_1233_, v___x_1234_);
v___f_1236_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1236_, 0, v___x_1235_);
v___x_1419__overap_1237_ = lean_panic_fn_borrowed(v___f_1236_, v_msg_1176_);
lean_dec_ref(v___f_1236_);
lean_inc(v___y_1182_);
lean_inc_ref(v___y_1181_);
lean_inc(v___y_1180_);
lean_inc_ref(v___y_1179_);
lean_inc(v___y_1178_);
lean_inc(v___y_1177_);
v___x_1238_ = lean_apply_7(v___x_1419__overap_1237_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_, lean_box(0));
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
v___x_1260_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v___x_1304_; lean_object* v_env_1305_; uint8_t v___x_1306_; 
v___x_1304_ = lean_st_ref_get(v___y_1302_);
v_env_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc_ref(v_env_1305_);
lean_dec(v___x_1304_);
v___x_1306_ = l_Lean_Name_isAnonymous(v_declHint_1301_);
if (v___x_1306_ == 0)
{
uint8_t v_isExporting_1307_; 
v_isExporting_1307_ = lean_ctor_get_uint8(v_env_1305_, sizeof(void*)*8);
if (v_isExporting_1307_ == 0)
{
lean_object* v___x_1308_; 
lean_dec_ref(v_env_1305_);
lean_dec(v_declHint_1301_);
v___x_1308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1308_, 0, v_msg_1300_);
return v___x_1308_;
}
else
{
lean_object* v___x_1309_; uint8_t v___x_1310_; 
lean_inc_ref(v_env_1305_);
v___x_1309_ = l_Lean_Environment_setExporting(v_env_1305_, v___x_1306_);
lean_inc(v_declHint_1301_);
lean_inc_ref(v___x_1309_);
v___x_1310_ = l_Lean_Environment_contains(v___x_1309_, v_declHint_1301_, v_isExporting_1307_);
if (v___x_1310_ == 0)
{
lean_object* v___x_1311_; 
lean_dec_ref(v___x_1309_);
lean_dec_ref(v_env_1305_);
lean_dec(v_declHint_1301_);
v___x_1311_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1311_, 0, v_msg_1300_);
return v___x_1311_;
}
else
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v_c_1317_; lean_object* v___x_1318_; 
v___x_1312_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__2);
v___x_1313_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__5);
v___x_1314_ = l_Lean_Options_empty;
v___x_1315_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1315_, 0, v___x_1309_);
lean_ctor_set(v___x_1315_, 1, v___x_1312_);
lean_ctor_set(v___x_1315_, 2, v___x_1313_);
lean_ctor_set(v___x_1315_, 3, v___x_1314_);
lean_inc(v_declHint_1301_);
v___x_1316_ = l_Lean_MessageData_ofConstName(v_declHint_1301_, v___x_1306_);
v_c_1317_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_1317_, 0, v___x_1315_);
lean_ctor_set(v_c_1317_, 1, v___x_1316_);
v___x_1318_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_1305_, v_declHint_1301_);
if (lean_obj_tag(v___x_1318_) == 0)
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; 
lean_dec_ref(v_env_1305_);
lean_dec(v_declHint_1301_);
v___x_1319_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__7);
v___x_1320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1320_, 0, v___x_1319_);
lean_ctor_set(v___x_1320_, 1, v_c_1317_);
v___x_1321_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__9);
v___x_1322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1322_, 0, v___x_1320_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
v___x_1323_ = l_Lean_MessageData_note(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1324_, 0, v_msg_1300_);
lean_ctor_set(v___x_1324_, 1, v___x_1323_);
v___x_1325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1325_, 0, v___x_1324_);
return v___x_1325_;
}
else
{
lean_object* v_val_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1361_; 
v_val_1326_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1328_ = v___x_1318_;
v_isShared_1329_ = v_isSharedCheck_1361_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_val_1326_);
lean_dec(v___x_1318_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1361_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v_mod_1333_; uint8_t v___x_1334_; 
v___x_1330_ = lean_box(0);
v___x_1331_ = l_Lean_Environment_header(v_env_1305_);
lean_dec_ref(v_env_1305_);
v___x_1332_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1331_);
v_mod_1333_ = lean_array_get(v___x_1330_, v___x_1332_, v_val_1326_);
lean_dec(v_val_1326_);
lean_dec_ref(v___x_1332_);
v___x_1334_ = l_Lean_isPrivateName(v_declHint_1301_);
lean_dec(v_declHint_1301_);
if (v___x_1334_ == 0)
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1335_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg___closed__11);
v___x_1336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1336_, 0, v___x_1335_);
lean_ctor_set(v___x_1336_, 1, v_c_1317_);
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
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1344_);
v___x_1346_ = v___x_1328_;
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
lean_ctor_set(v___x_1349_, 1, v_c_1317_);
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
if (v_isShared_1329_ == 0)
{
lean_ctor_set_tag(v___x_1328_, 0);
lean_ctor_set(v___x_1328_, 0, v___x_1357_);
v___x_1359_ = v___x_1328_;
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
lean_dec_ref(v_env_1305_);
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
lean_object* v_toCold_1454_; lean_object* v_currRecDepth_1455_; lean_object* v_ref_1456_; uint8_t v_diag_1457_; uint8_t v_suppressElabErrors_1458_; lean_object* v_ref_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v_toCold_1454_ = lean_ctor_get(v___y_1451_, 0);
v_currRecDepth_1455_ = lean_ctor_get(v___y_1451_, 1);
v_ref_1456_ = lean_ctor_get(v___y_1451_, 2);
v_diag_1457_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*3);
v_suppressElabErrors_1458_ = lean_ctor_get_uint8(v___y_1451_, sizeof(void*)*3 + 1);
v_ref_1459_ = l_Lean_replaceRef(v_ref_1445_, v_ref_1456_);
lean_inc(v_currRecDepth_1455_);
lean_inc_ref(v_toCold_1454_);
v___x_1460_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_1460_, 0, v_toCold_1454_);
lean_ctor_set(v___x_1460_, 1, v_currRecDepth_1455_);
lean_ctor_set(v___x_1460_, 2, v_ref_1459_);
lean_ctor_set_uint8(v___x_1460_, sizeof(void*)*3, v_diag_1457_);
lean_ctor_set_uint8(v___x_1460_, sizeof(void*)*3 + 1, v_suppressElabErrors_1458_);
v___x_1461_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1446_, v___y_1449_, v___y_1450_, v___x_1460_, v___y_1452_);
lean_dec_ref_known(v___x_1460_, 3);
return v___x_1461_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1462_, lean_object* v_msg_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1462_, v_msg_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_, v___y_1469_);
lean_dec(v___y_1469_);
lean_dec_ref(v___y_1468_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec(v___y_1464_);
lean_dec(v_ref_1462_);
return v_res_1471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1472_, lean_object* v_msg_1473_, lean_object* v_declHint_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_){
_start:
{
lean_object* v___x_1482_; lean_object* v_a_1483_; lean_object* v___x_1484_; 
v___x_1482_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1473_, v_declHint_1474_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
v_a_1483_ = lean_ctor_get(v___x_1482_, 0);
lean_inc(v_a_1483_);
lean_dec_ref(v___x_1482_);
v___x_1484_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1472_, v_a_1483_, v___y_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
return v___x_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1485_, lean_object* v_msg_1486_, lean_object* v_declHint_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1485_, v_msg_1486_, v_declHint_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
lean_dec(v___y_1493_);
lean_dec_ref(v___y_1492_);
lean_dec(v___y_1491_);
lean_dec_ref(v___y_1490_);
lean_dec(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec(v_ref_1485_);
return v_res_1495_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; 
v___x_1497_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1498_ = l_Lean_stringToMessageData(v___x_1497_);
return v___x_1498_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1501_ = l_Lean_stringToMessageData(v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1502_, lean_object* v_constName_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v___x_1511_; uint8_t v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1511_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1512_ = 0;
lean_inc(v_constName_1503_);
v___x_1513_ = l_Lean_MessageData_ofConstName(v_constName_1503_, v___x_1512_);
v___x_1514_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1511_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
v___x_1515_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1516_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1514_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
v___x_1517_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1502_, v___x_1516_, v_constName_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
return v___x_1517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1518_, lean_object* v_constName_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1518_, v_constName_1519_, v___y_1520_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_, v___y_1525_);
lean_dec(v___y_1525_);
lean_dec_ref(v___y_1524_);
lean_dec(v___y_1523_);
lean_dec_ref(v___y_1522_);
lean_dec(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec(v_ref_1518_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_, lean_object* v___y_1533_, lean_object* v___y_1534_){
_start:
{
lean_object* v_ref_1536_; lean_object* v___x_1537_; 
v_ref_1536_ = lean_ctor_get(v___y_1533_, 2);
v___x_1537_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1536_, v_constName_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_, v___y_1533_, v___y_1534_);
return v___x_1537_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1538_, lean_object* v___y_1539_, lean_object* v___y_1540_, lean_object* v___y_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v_res_1546_; 
v_res_1546_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1538_, v___y_1539_, v___y_1540_, v___y_1541_, v___y_1542_, v___y_1543_, v___y_1544_);
lean_dec(v___y_1544_);
lean_dec_ref(v___y_1543_);
lean_dec(v___y_1542_);
lean_dec_ref(v___y_1541_);
lean_dec(v___y_1540_);
lean_dec(v___y_1539_);
return v_res_1546_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; lean_object* v_env_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; 
v___x_1555_ = lean_st_ref_get(v___y_1553_);
v_env_1556_ = lean_ctor_get(v___x_1555_, 0);
lean_inc_ref(v_env_1556_);
lean_dec(v___x_1555_);
v___x_1557_ = 0;
lean_inc(v_constName_1547_);
v___x_1558_ = l_Lean_Environment_findConstVal_x3f(v_env_1556_, v_constName_1547_, v___x_1557_);
if (lean_obj_tag(v___x_1558_) == 0)
{
lean_object* v___x_1559_; 
v___x_1559_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1547_, v___y_1548_, v___y_1549_, v___y_1550_, v___y_1551_, v___y_1552_, v___y_1553_);
return v___x_1559_;
}
else
{
lean_object* v_val_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_dec(v_constName_1547_);
v_val_1560_ = lean_ctor_get(v___x_1558_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1558_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1558_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_val_1560_);
lean_dec(v___x_1558_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
lean_ctor_set_tag(v___x_1562_, 0);
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_val_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v_res_1576_; 
v_res_1576_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_, v___y_1574_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
lean_dec(v___y_1572_);
lean_dec_ref(v___y_1571_);
lean_dec(v___y_1570_);
lean_dec(v___y_1569_);
return v_res_1576_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1580_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1581_ = lean_unsigned_to_nat(35u);
v___x_1582_ = lean_unsigned_to_nat(203u);
v___x_1583_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1584_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1585_ = l_mkPanicMessageWithDecl(v___x_1584_, v___x_1583_, v___x_1582_, v___x_1581_, v___x_1580_);
return v___x_1585_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_){
_start:
{
if (lean_obj_tag(v_e_1586_) == 4)
{
lean_object* v_declName_1594_; lean_object* v_us_1595_; lean_object* v___x_1596_; 
v_declName_1594_ = lean_ctor_get(v_e_1586_, 0);
v_us_1595_ = lean_ctor_get(v_e_1586_, 1);
lean_inc(v_declName_1594_);
v___x_1596_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1594_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; lean_object* v_levelParams_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; uint8_t v___x_1601_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
v_levelParams_1598_ = lean_ctor_get(v_a_1597_, 1);
v___x_1599_ = l_List_lengthTR___redArg(v_levelParams_1598_);
v___x_1600_ = l_List_lengthTR___redArg(v_us_1595_);
v___x_1601_ = lean_nat_dec_eq(v___x_1599_, v___x_1600_);
lean_dec(v___x_1600_);
lean_dec(v___x_1599_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; 
lean_inc(v_us_1595_);
lean_inc(v_declName_1594_);
lean_dec(v_a_1597_);
lean_dec_ref_known(v_e_1586_, 2);
v___x_1602_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1594_, v_us_1595_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
return v___x_1602_;
}
else
{
lean_object* v___x_1603_; 
lean_inc(v_us_1595_);
v___x_1603_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1597_, v_us_1595_, v___y_1592_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1613_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1613_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1613_ == 0)
{
v___x_1606_ = v___x_1603_;
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1613_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1611_; 
v___x_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1608_, 0, v_a_1604_);
v___x_1609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1609_, 0, v_e_1586_);
lean_ctor_set(v___x_1609_, 1, v___x_1608_);
if (v_isShared_1607_ == 0)
{
lean_ctor_set(v___x_1606_, 0, v___x_1609_);
v___x_1611_ = v___x_1606_;
goto v_reusejp_1610_;
}
else
{
lean_object* v_reuseFailAlloc_1612_; 
v_reuseFailAlloc_1612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1612_, 0, v___x_1609_);
v___x_1611_ = v_reuseFailAlloc_1612_;
goto v_reusejp_1610_;
}
v_reusejp_1610_:
{
return v___x_1611_;
}
}
}
else
{
lean_object* v_a_1614_; lean_object* v___x_1616_; uint8_t v_isShared_1617_; uint8_t v_isSharedCheck_1621_; 
lean_dec_ref_known(v_e_1586_, 2);
v_a_1614_ = lean_ctor_get(v___x_1603_, 0);
v_isSharedCheck_1621_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1621_ == 0)
{
v___x_1616_ = v___x_1603_;
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
else
{
lean_inc(v_a_1614_);
lean_dec(v___x_1603_);
v___x_1616_ = lean_box(0);
v_isShared_1617_ = v_isSharedCheck_1621_;
goto v_resetjp_1615_;
}
v_resetjp_1615_:
{
lean_object* v___x_1619_; 
if (v_isShared_1617_ == 0)
{
v___x_1619_ = v___x_1616_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v_a_1614_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
lean_object* v_a_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1629_; 
lean_dec_ref_known(v_e_1586_, 2);
v_a_1622_ = lean_ctor_get(v___x_1596_, 0);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1596_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1624_ = v___x_1596_;
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_a_1622_);
lean_dec(v___x_1596_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1629_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
lean_object* v___x_1627_; 
if (v_isShared_1625_ == 0)
{
v___x_1627_ = v___x_1624_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v_a_1622_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_dec_ref(v_e_1586_);
v___x_1630_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1631_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1630_, v___y_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_, v___y_1592_);
return v___x_1631_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1632_, lean_object* v___y_1633_, lean_object* v___y_1634_, lean_object* v___y_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v_res_1640_; 
v_res_1640_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1632_, v___y_1633_, v___y_1634_, v___y_1635_, v___y_1636_, v___y_1637_, v___y_1638_);
lean_dec(v___y_1638_);
lean_dec_ref(v___y_1637_);
lean_dec(v___y_1636_);
lean_dec_ref(v___y_1635_);
lean_dec(v___y_1634_);
lean_dec(v___y_1633_);
return v_res_1640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1641_, lean_object* v_a_1642_, lean_object* v_a_1643_, lean_object* v_a_1644_, lean_object* v_a_1645_, lean_object* v_a_1646_, lean_object* v_a_1647_){
_start:
{
lean_object* v___y_1649_; lean_object* v___x_1650_; 
lean_inc_ref(v_e_1641_);
v___y_1649_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1649_, 0, v_e_1641_);
v___x_1650_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1641_, v___y_1649_, v_a_1642_, v_a_1643_, v_a_1644_, v_a_1645_, v_a_1646_, v_a_1647_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_, lean_object* v_a_1654_, lean_object* v_a_1655_, lean_object* v_a_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_){
_start:
{
lean_object* v_res_1659_; 
v_res_1659_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1651_, v_a_1652_, v_a_1653_, v_a_1654_, v_a_1655_, v_a_1656_, v_a_1657_);
lean_dec(v_a_1657_);
lean_dec_ref(v_a_1656_);
lean_dec(v_a_1655_);
lean_dec_ref(v_a_1654_);
lean_dec(v_a_1653_);
lean_dec(v_a_1652_);
return v_res_1659_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1660_, lean_object* v_constName_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_, lean_object* v___y_1667_){
_start:
{
lean_object* v___x_1669_; 
v___x_1669_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_, v___y_1667_);
return v___x_1669_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1670_, lean_object* v_constName_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_res_1679_; 
v_res_1679_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1670_, v_constName_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec(v___y_1672_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1680_, lean_object* v_ref_1681_, lean_object* v_constName_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
v___x_1690_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1681_, v_constName_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1691_, lean_object* v_ref_1692_, lean_object* v_constName_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_){
_start:
{
lean_object* v_res_1701_; 
v_res_1701_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1691_, v_ref_1692_, v_constName_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_, v___y_1698_, v___y_1699_);
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
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1702_, lean_object* v_ref_1703_, lean_object* v_msg_1704_, lean_object* v_declHint_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_){
_start:
{
lean_object* v___x_1713_; 
v___x_1713_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1703_, v_msg_1704_, v_declHint_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1714_, lean_object* v_ref_1715_, lean_object* v_msg_1716_, lean_object* v_declHint_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
lean_object* v_res_1725_; 
v_res_1725_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1714_, v_ref_1715_, v_msg_1716_, v_declHint_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
lean_dec(v___y_1719_);
lean_dec(v___y_1718_);
lean_dec(v_ref_1715_);
return v_res_1725_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1726_, lean_object* v_declHint_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_, lean_object* v___y_1733_){
_start:
{
lean_object* v___x_1735_; 
v___x_1735_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1726_, v_declHint_1727_, v___y_1733_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1736_, lean_object* v_declHint_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
lean_object* v_res_1745_; 
v_res_1745_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1736_, v_declHint_1737_, v___y_1738_, v___y_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec(v___y_1739_);
lean_dec(v___y_1738_);
return v_res_1745_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1746_, lean_object* v_ref_1747_, lean_object* v_msg_1748_, lean_object* v___y_1749_, lean_object* v___y_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1747_, v_msg_1748_, v___y_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_);
return v___x_1756_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1757_, lean_object* v_ref_1758_, lean_object* v_msg_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_){
_start:
{
lean_object* v_res_1767_; 
v_res_1767_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1757_, v_ref_1758_, v_msg_1759_, v___y_1760_, v___y_1761_, v___y_1762_, v___y_1763_, v___y_1764_, v___y_1765_);
lean_dec(v___y_1765_);
lean_dec_ref(v___y_1764_);
lean_dec(v___y_1763_);
lean_dec_ref(v___y_1762_);
lean_dec(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec(v_ref_1758_);
return v_res_1767_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1768_, lean_object* v_msg_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_, lean_object* v___y_1772_, lean_object* v___y_1773_, lean_object* v___y_1774_, lean_object* v___y_1775_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1769_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1778_, lean_object* v_msg_1779_, lean_object* v___y_1780_, lean_object* v___y_1781_, lean_object* v___y_1782_, lean_object* v___y_1783_, lean_object* v___y_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1778_, v_msg_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_);
lean_dec(v___y_1785_);
lean_dec_ref(v___y_1784_);
lean_dec(v___y_1783_);
lean_dec_ref(v___y_1782_);
lean_dec(v___y_1781_);
lean_dec(v___y_1780_);
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
uint8_t v___x_1796_; 
v___x_1796_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1789_);
if (v___x_1796_ == 0)
{
lean_object* v___x_1797_; 
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v_r_1788_);
return v___x_1797_;
}
else
{
lean_object* v___x_1798_; 
lean_inc_ref(v_r_1788_);
v___x_1798_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1788_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1851_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1851_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1851_ == 0)
{
v___x_1801_ = v___x_1798_;
v_isShared_1802_ = v_isSharedCheck_1851_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_dec(v___x_1798_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1851_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v_expr_1803_; lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1849_; 
v_expr_1803_ = lean_ctor_get(v_r_1788_, 0);
v_isSharedCheck_1849_ = !lean_is_exclusive(v_r_1788_);
if (v_isSharedCheck_1849_ == 0)
{
lean_object* v_unused_1850_; 
v_unused_1850_ = lean_ctor_get(v_r_1788_, 1);
lean_dec(v_unused_1850_);
v___x_1805_ = v_r_1788_;
v_isShared_1806_ = v_isSharedCheck_1849_;
goto v_resetjp_1804_;
}
else
{
lean_inc(v_expr_1803_);
lean_dec(v_r_1788_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1849_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
uint8_t v___x_1807_; 
v___x_1807_ = l_Lean_Expr_isSort(v_a_1799_);
if (v___x_1807_ == 0)
{
lean_object* v___x_1808_; 
lean_del_object(v___x_1801_);
lean_inc(v_a_1794_);
lean_inc_ref(v_a_1793_);
lean_inc(v_a_1792_);
lean_inc_ref(v_a_1791_);
v___x_1808_ = lean_whnf(v_a_1799_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1833_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1833_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1833_ == 0)
{
v___x_1811_ = v___x_1808_;
v_isShared_1812_ = v_isSharedCheck_1833_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_a_1809_);
lean_dec(v___x_1808_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1833_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
if (lean_obj_tag(v_a_1809_) == 3)
{
lean_object* v___x_1813_; lean_object* v_count_1814_; lean_object* v_results_1815_; lean_object* v___x_1817_; uint8_t v_isShared_1818_; uint8_t v_isSharedCheck_1831_; 
v___x_1813_ = lean_st_ref_take(v_a_1790_);
v_count_1814_ = lean_ctor_get(v___x_1813_, 0);
v_results_1815_ = lean_ctor_get(v___x_1813_, 1);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1817_ = v___x_1813_;
v_isShared_1818_ = v_isSharedCheck_1831_;
goto v_resetjp_1816_;
}
else
{
lean_inc(v_results_1815_);
lean_inc(v_count_1814_);
lean_dec(v___x_1813_);
v___x_1817_ = lean_box(0);
v_isShared_1818_ = v_isSharedCheck_1831_;
goto v_resetjp_1816_;
}
v_resetjp_1816_:
{
lean_object* v___x_1819_; lean_object* v___x_1821_; 
v___x_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1819_, 0, v_a_1809_);
lean_inc_ref(v_expr_1803_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1819_);
v___x_1821_ = v___x_1805_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_expr_1803_);
lean_ctor_set(v_reuseFailAlloc_1830_, 1, v___x_1819_);
v___x_1821_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
lean_inc_ref(v___x_1821_);
v___x_1822_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1815_, v_expr_1803_, v___x_1821_);
if (v_isShared_1818_ == 0)
{
lean_ctor_set(v___x_1817_, 1, v___x_1822_);
v___x_1824_ = v___x_1817_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_count_1814_);
lean_ctor_set(v_reuseFailAlloc_1829_, 1, v___x_1822_);
v___x_1824_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; lean_object* v___x_1827_; 
v___x_1825_ = lean_st_ref_put(v_a_1790_, v___x_1824_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1821_);
v___x_1827_ = v___x_1811_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1821_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
else
{
lean_object* v___x_1832_; 
lean_del_object(v___x_1811_);
lean_dec(v_a_1809_);
lean_del_object(v___x_1805_);
v___x_1832_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1803_, v_a_1791_, v_a_1792_, v_a_1793_, v_a_1794_);
return v___x_1832_;
}
}
}
else
{
lean_object* v_a_1834_; lean_object* v___x_1836_; uint8_t v_isShared_1837_; uint8_t v_isSharedCheck_1841_; 
lean_del_object(v___x_1805_);
lean_dec_ref(v_expr_1803_);
v_a_1834_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1836_ = v___x_1808_;
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
else
{
lean_inc(v_a_1834_);
lean_dec(v___x_1808_);
v___x_1836_ = lean_box(0);
v_isShared_1837_ = v_isSharedCheck_1841_;
goto v_resetjp_1835_;
}
v_resetjp_1835_:
{
lean_object* v___x_1839_; 
if (v_isShared_1837_ == 0)
{
v___x_1839_ = v___x_1836_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v_a_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
else
{
lean_object* v___x_1842_; lean_object* v___x_1844_; 
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_a_1799_);
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 1, v___x_1842_);
v___x_1844_ = v___x_1805_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1848_; 
v_reuseFailAlloc_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1848_, 0, v_expr_1803_);
lean_ctor_set(v_reuseFailAlloc_1848_, 1, v___x_1842_);
v___x_1844_ = v_reuseFailAlloc_1848_;
goto v_reusejp_1843_;
}
v_reusejp_1843_:
{
lean_object* v___x_1846_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 0, v___x_1844_);
v___x_1846_ = v___x_1801_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v___x_1844_);
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
else
{
lean_object* v_a_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1859_; 
lean_dec_ref(v_r_1788_);
v_a_1852_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1859_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1854_ = v___x_1798_;
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_a_1852_);
lean_dec(v___x_1798_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1859_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1857_; 
if (v_isShared_1855_ == 0)
{
v___x_1857_ = v___x_1854_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_a_1852_);
v___x_1857_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
return v___x_1857_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1860_, lean_object* v_a_1861_, lean_object* v_a_1862_, lean_object* v_a_1863_, lean_object* v_a_1864_, lean_object* v_a_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1860_, v_a_1861_, v_a_1862_, v_a_1863_, v_a_1864_, v_a_1865_, v_a_1866_);
lean_dec(v_a_1866_);
lean_dec_ref(v_a_1865_);
lean_dec(v_a_1864_);
lean_dec_ref(v_a_1863_);
lean_dec(v_a_1862_);
lean_dec(v_a_1861_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1869_){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1870_ = l_Lean_instInhabitedExpr;
v___x_1871_ = lean_panic_fn_borrowed(v___x_1870_, v_msg_1869_);
return v___x_1871_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1875_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1876_ = lean_unsigned_to_nat(18u);
v___x_1877_ = lean_unsigned_to_nat(1847u);
v___x_1878_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1879_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1880_ = l_mkPanicMessageWithDecl(v___x_1879_, v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1881_, lean_object* v_f_1882_, lean_object* v_a_1883_, lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_){
_start:
{
lean_object* v___y_1892_; lean_object* v___y_1897_; lean_object* v___y_1898_; lean_object* v___y_1899_; lean_object* v___y_1905_; lean_object* v_fType_1922_; lean_object* v___y_1923_; lean_object* v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; uint8_t v___x_1966_; 
v___x_1966_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1884_);
if (v___x_1966_ == 0)
{
if (lean_obj_tag(v_e_1881_) == 5)
{
lean_object* v_expr_1967_; lean_object* v_expr_1968_; lean_object* v_fn_1969_; lean_object* v_arg_1970_; size_t v___x_1971_; size_t v___x_1972_; uint8_t v___x_1973_; 
v_expr_1967_ = lean_ctor_get(v_f_1882_, 0);
lean_inc_ref(v_expr_1967_);
lean_dec_ref(v_f_1882_);
v_expr_1968_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_expr_1968_);
lean_dec_ref(v_a_1883_);
v_fn_1969_ = lean_ctor_get(v_e_1881_, 0);
v_arg_1970_ = lean_ctor_get(v_e_1881_, 1);
v___x_1971_ = lean_ptr_addr(v_fn_1969_);
v___x_1972_ = lean_ptr_addr(v_expr_1967_);
v___x_1973_ = lean_usize_dec_eq(v___x_1971_, v___x_1972_);
if (v___x_1973_ == 0)
{
lean_object* v___x_1974_; 
lean_dec_ref_known(v_e_1881_, 2);
v___x_1974_ = l_Lean_Expr_app___override(v_expr_1967_, v_expr_1968_);
v___y_1892_ = v___x_1974_;
goto v___jp_1891_;
}
else
{
size_t v___x_1975_; size_t v___x_1976_; uint8_t v___x_1977_; 
v___x_1975_ = lean_ptr_addr(v_arg_1970_);
v___x_1976_ = lean_ptr_addr(v_expr_1968_);
v___x_1977_ = lean_usize_dec_eq(v___x_1975_, v___x_1976_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec_ref_known(v_e_1881_, 2);
v___x_1978_ = l_Lean_Expr_app___override(v_expr_1967_, v_expr_1968_);
v___y_1892_ = v___x_1978_;
goto v___jp_1891_;
}
else
{
lean_dec_ref(v_expr_1968_);
lean_dec_ref(v_expr_1967_);
v___y_1892_ = v_e_1881_;
goto v___jp_1891_;
}
}
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec_ref(v_a_1883_);
lean_dec_ref(v_f_1882_);
lean_dec_ref(v_e_1881_);
v___x_1979_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1980_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1979_);
v___y_1892_ = v___x_1980_;
goto v___jp_1891_;
}
}
else
{
lean_object* v___x_1981_; 
lean_inc_ref(v_f_1882_);
v___x_1981_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1882_, v_a_1885_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; uint8_t v___x_1983_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
lean_inc(v_a_1982_);
lean_dec_ref_known(v___x_1981_, 1);
v___x_1983_ = l_Lean_Expr_isForall(v_a_1982_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1984_; 
lean_inc(v_a_1889_);
lean_inc_ref(v_a_1888_);
lean_inc(v_a_1887_);
lean_inc_ref(v_a_1886_);
v___x_1984_ = lean_whnf(v_a_1982_, v_a_1886_, v_a_1887_, v_a_1888_, v_a_1889_);
if (lean_obj_tag(v___x_1984_) == 0)
{
lean_object* v_a_1985_; 
v_a_1985_ = lean_ctor_get(v___x_1984_, 0);
lean_inc(v_a_1985_);
lean_dec_ref_known(v___x_1984_, 1);
v_fType_1922_ = v_a_1985_;
v___y_1923_ = v_a_1885_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
v___y_1926_ = v_a_1888_;
v___y_1927_ = v_a_1889_;
goto v___jp_1921_;
}
else
{
lean_object* v_a_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_1993_; 
lean_dec_ref(v_a_1883_);
lean_dec_ref(v_f_1882_);
lean_dec_ref(v_e_1881_);
v_a_1986_ = lean_ctor_get(v___x_1984_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1984_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1988_ = v___x_1984_;
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_a_1986_);
lean_dec(v___x_1984_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_1993_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
lean_object* v___x_1991_; 
if (v_isShared_1989_ == 0)
{
v___x_1991_ = v___x_1988_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_a_1986_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
v_fType_1922_ = v_a_1982_;
v___y_1923_ = v_a_1885_;
v___y_1924_ = v_a_1886_;
v___y_1925_ = v_a_1887_;
v___y_1926_ = v_a_1888_;
v___y_1927_ = v_a_1889_;
goto v___jp_1921_;
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec_ref(v_a_1883_);
lean_dec_ref(v_f_1882_);
lean_dec_ref(v_e_1881_);
v_a_1994_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1981_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1981_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
v___jp_1891_:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
v___x_1893_ = lean_box(0);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___y_1892_);
lean_ctor_set(v___x_1894_, 1, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
return v___x_1895_;
}
v___jp_1896_:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = lean_expr_instantiate1(v___y_1897_, v___y_1898_);
lean_dec_ref(v___y_1898_);
lean_dec_ref(v___y_1897_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___y_1899_);
lean_ctor_set(v___x_1902_, 1, v___x_1901_);
v___x_1903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1902_);
return v___x_1903_;
}
v___jp_1904_:
{
if (lean_obj_tag(v_e_1881_) == 5)
{
lean_object* v_expr_1906_; lean_object* v_expr_1907_; lean_object* v_fn_1908_; lean_object* v_arg_1909_; size_t v___x_1910_; size_t v___x_1911_; uint8_t v___x_1912_; 
v_expr_1906_ = lean_ctor_get(v_f_1882_, 0);
lean_inc_ref(v_expr_1906_);
lean_dec_ref(v_f_1882_);
v_expr_1907_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_expr_1907_);
lean_dec_ref(v_a_1883_);
v_fn_1908_ = lean_ctor_get(v_e_1881_, 0);
v_arg_1909_ = lean_ctor_get(v_e_1881_, 1);
v___x_1910_ = lean_ptr_addr(v_fn_1908_);
v___x_1911_ = lean_ptr_addr(v_expr_1906_);
v___x_1912_ = lean_usize_dec_eq(v___x_1910_, v___x_1911_);
if (v___x_1912_ == 0)
{
lean_object* v___x_1913_; 
lean_dec_ref_known(v_e_1881_, 2);
lean_inc_ref(v_expr_1907_);
v___x_1913_ = l_Lean_Expr_app___override(v_expr_1906_, v_expr_1907_);
v___y_1897_ = v___y_1905_;
v___y_1898_ = v_expr_1907_;
v___y_1899_ = v___x_1913_;
goto v___jp_1896_;
}
else
{
size_t v___x_1914_; size_t v___x_1915_; uint8_t v___x_1916_; 
v___x_1914_ = lean_ptr_addr(v_arg_1909_);
v___x_1915_ = lean_ptr_addr(v_expr_1907_);
v___x_1916_ = lean_usize_dec_eq(v___x_1914_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_dec_ref_known(v_e_1881_, 2);
lean_inc_ref(v_expr_1907_);
v___x_1917_ = l_Lean_Expr_app___override(v_expr_1906_, v_expr_1907_);
v___y_1897_ = v___y_1905_;
v___y_1898_ = v_expr_1907_;
v___y_1899_ = v___x_1917_;
goto v___jp_1896_;
}
else
{
lean_dec_ref(v_expr_1906_);
v___y_1897_ = v___y_1905_;
v___y_1898_ = v_expr_1907_;
v___y_1899_ = v_e_1881_;
goto v___jp_1896_;
}
}
}
else
{
lean_object* v_expr_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; 
lean_dec_ref(v_f_1882_);
lean_dec_ref(v_e_1881_);
v_expr_1918_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_expr_1918_);
lean_dec_ref(v_a_1883_);
v___x_1919_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1920_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1919_);
v___y_1897_ = v___y_1905_;
v___y_1898_ = v_expr_1918_;
v___y_1899_ = v___x_1920_;
goto v___jp_1896_;
}
}
v___jp_1921_:
{
if (lean_obj_tag(v_fType_1922_) == 7)
{
lean_object* v_binderType_1928_; lean_object* v_body_1929_; lean_object* v___x_1930_; 
v_binderType_1928_ = lean_ctor_get(v_fType_1922_, 1);
lean_inc_ref(v_binderType_1928_);
v_body_1929_ = lean_ctor_get(v_fType_1922_, 2);
lean_inc_ref(v_body_1929_);
lean_dec_ref_known(v_fType_1922_, 3);
lean_inc_ref(v_a_1883_);
v___x_1930_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1883_, v___y_1923_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; lean_object* v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = l_Lean_Meta_isExprDefEq(v_binderType_1928_, v_a_1931_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; uint8_t v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
v___x_1934_ = lean_unbox(v_a_1933_);
lean_dec(v_a_1933_);
if (v___x_1934_ == 0)
{
lean_object* v_expr_1935_; lean_object* v_expr_1936_; lean_object* v___x_1937_; 
v_expr_1935_ = lean_ctor_get(v_f_1882_, 0);
v_expr_1936_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_expr_1936_);
lean_inc_ref(v_expr_1935_);
v___x_1937_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1935_, v_expr_1936_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_dec_ref_known(v___x_1937_, 1);
v___y_1905_ = v_body_1929_;
goto v___jp_1904_;
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec_ref(v_body_1929_);
lean_dec_ref(v_a_1883_);
lean_dec_ref(v_f_1882_);
lean_dec_ref(v_e_1881_);
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1937_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1937_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
v___y_1905_ = v_body_1929_;
goto v___jp_1904_;
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec_ref(v_body_1929_);
lean_dec_ref(v_a_1883_);
lean_dec_ref(v_f_1882_);
lean_dec_ref(v_e_1881_);
v_a_1946_ = lean_ctor_get(v___x_1932_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1932_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1932_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1932_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec_ref(v_body_1929_);
lean_dec_ref(v_binderType_1928_);
lean_dec_ref(v_a_1883_);
lean_dec_ref(v_f_1882_);
lean_dec_ref(v_e_1881_);
v_a_1954_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1930_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1930_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_expr_1962_; lean_object* v_expr_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec_ref(v_fType_1922_);
lean_dec_ref(v_e_1881_);
v_expr_1962_ = lean_ctor_get(v_f_1882_, 0);
lean_inc_ref(v_expr_1962_);
lean_dec_ref(v_f_1882_);
v_expr_1963_ = lean_ctor_get(v_a_1883_, 0);
lean_inc_ref(v_expr_1963_);
lean_dec_ref(v_a_1883_);
v___x_1964_ = l_Lean_Expr_app___override(v_expr_1962_, v_expr_1963_);
v___x_1965_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1964_, v___y_1924_, v___y_1925_, v___y_1926_, v___y_1927_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2002_, lean_object* v_f_2003_, lean_object* v_a_2004_, lean_object* v_a_2005_, lean_object* v_a_2006_, lean_object* v_a_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v_res_2012_; 
v_res_2012_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2002_, v_f_2003_, v_a_2004_, v_a_2005_, v_a_2006_, v_a_2007_, v_a_2008_, v_a_2009_, v_a_2010_);
lean_dec(v_a_2010_);
lean_dec_ref(v_a_2009_);
lean_dec(v_a_2008_);
lean_dec_ref(v_a_2007_);
lean_dec(v_a_2006_);
lean_dec(v_a_2005_);
return v_res_2012_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; 
v___x_2014_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2015_ = lean_unsigned_to_nat(37u);
v___x_2016_ = lean_unsigned_to_nat(345u);
v___x_2017_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2018_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2019_ = l_mkPanicMessageWithDecl(v___x_2018_, v___x_2017_, v___x_2016_, v___x_2015_, v___x_2014_);
return v___x_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2020_, lean_object* v_i_2021_, lean_object* v_a_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_, lean_object* v___y_2027_, lean_object* v___y_2028_){
_start:
{
lean_object* v_zero_2030_; uint8_t v_isZero_2031_; 
v_zero_2030_ = lean_unsigned_to_nat(0u);
v_isZero_2031_ = lean_nat_dec_eq(v_i_2021_, v_zero_2030_);
if (v_isZero_2031_ == 1)
{
lean_object* v___x_2032_; 
lean_dec(v_i_2021_);
v___x_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2032_, 0, v_a_2022_);
return v___x_2032_;
}
else
{
lean_object* v_one_2033_; lean_object* v_n_2034_; lean_object* v___y_2036_; lean_object* v___y_2040_; lean_object* v___y_2041_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___x_2048_; 
v_one_2033_ = lean_unsigned_to_nat(1u);
v_n_2034_ = lean_nat_sub(v_i_2021_, v_one_2033_);
lean_dec(v_i_2021_);
v___x_2048_ = lean_array_fget_borrowed(v_fvars_2020_, v_n_2034_);
if (lean_obj_tag(v___x_2048_) == 1)
{
lean_object* v_fvarId_2049_; lean_object* v___x_2050_; 
v_fvarId_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc(v_fvarId_2049_);
v___x_2050_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2049_, v___y_2025_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref_known(v___x_2050_, 1);
if (lean_obj_tag(v_a_2051_) == 1)
{
lean_object* v_val_2052_; 
v_val_2052_ = lean_ctor_get(v_a_2051_, 0);
lean_inc(v_val_2052_);
lean_dec_ref_known(v_a_2051_, 1);
if (lean_obj_tag(v_val_2052_) == 0)
{
lean_object* v_userName_2053_; lean_object* v_type_2054_; uint8_t v_bi_2055_; lean_object* v_expr_2056_; lean_object* v_type_x3f_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2078_; 
v_userName_2053_ = lean_ctor_get(v_val_2052_, 2);
lean_inc(v_userName_2053_);
v_type_2054_ = lean_ctor_get(v_val_2052_, 3);
lean_inc_ref(v_type_2054_);
v_bi_2055_ = lean_ctor_get_uint8(v_val_2052_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2052_, 4);
v_expr_2056_ = lean_ctor_get(v_a_2022_, 0);
v_type_x3f_2057_ = lean_ctor_get(v_a_2022_, 1);
v_isSharedCheck_2078_ = !lean_is_exclusive(v_a_2022_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2059_ = v_a_2022_;
v_isShared_2060_ = v_isSharedCheck_2078_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_type_x3f_2057_);
lean_inc(v_expr_2056_);
lean_dec(v_a_2022_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2078_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___y_2064_; 
v___x_2061_ = lean_expr_abstract_range(v_type_2054_, v_n_2034_, v_fvars_2020_);
lean_dec_ref(v_type_2054_);
lean_inc_ref(v___x_2061_);
lean_inc(v_userName_2053_);
v___x_2062_ = l_Lean_Expr_lam___override(v_userName_2053_, v___x_2061_, v_expr_2056_, v_bi_2055_);
if (lean_obj_tag(v_type_x3f_2057_) == 0)
{
lean_dec_ref(v___x_2061_);
lean_dec(v_userName_2053_);
v___y_2064_ = v_type_x3f_2057_;
goto v___jp_2063_;
}
else
{
lean_object* v_val_2069_; lean_object* v___x_2071_; uint8_t v_isShared_2072_; uint8_t v_isSharedCheck_2077_; 
v_val_2069_ = lean_ctor_get(v_type_x3f_2057_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_type_x3f_2057_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2071_ = v_type_x3f_2057_;
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
else
{
lean_inc(v_val_2069_);
lean_dec(v_type_x3f_2057_);
v___x_2071_ = lean_box(0);
v_isShared_2072_ = v_isSharedCheck_2077_;
goto v_resetjp_2070_;
}
v_resetjp_2070_:
{
lean_object* v___x_2073_; lean_object* v___x_2075_; 
v___x_2073_ = l_Lean_Expr_forallE___override(v_userName_2053_, v___x_2061_, v_val_2069_, v_bi_2055_);
if (v_isShared_2072_ == 0)
{
lean_ctor_set(v___x_2071_, 0, v___x_2073_);
v___x_2075_ = v___x_2071_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v___x_2073_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
v___y_2064_ = v___x_2075_;
goto v___jp_2063_;
}
}
}
v___jp_2063_:
{
lean_object* v___x_2066_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 1, v___y_2064_);
lean_ctor_set(v___x_2059_, 0, v___x_2062_);
v___x_2066_ = v___x_2059_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2062_);
lean_ctor_set(v_reuseFailAlloc_2068_, 1, v___y_2064_);
v___x_2066_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
v_i_2021_ = v_n_2034_;
v_a_2022_ = v___x_2066_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2079_; lean_object* v_type_2080_; lean_object* v_value_2081_; uint8_t v_nondep_2082_; uint8_t v_nondep_2084_; lean_object* v___x_2094_; 
v_userName_2079_ = lean_ctor_get(v_val_2052_, 2);
lean_inc(v_userName_2079_);
v_type_2080_ = lean_ctor_get(v_val_2052_, 3);
lean_inc_ref(v_type_2080_);
v_value_2081_ = lean_ctor_get(v_val_2052_, 4);
lean_inc_ref(v_value_2081_);
v_nondep_2082_ = lean_ctor_get_uint8(v_val_2052_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2052_, 5);
v___x_2094_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2026_);
if (lean_obj_tag(v___x_2094_) == 0)
{
lean_object* v_a_2095_; uint8_t v___x_2096_; 
v_a_2095_ = lean_ctor_get(v___x_2094_, 0);
lean_inc(v_a_2095_);
lean_dec_ref_known(v___x_2094_, 1);
v___x_2096_ = 1;
if (v_nondep_2082_ == 0)
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2049_, v_a_2095_);
lean_dec(v_a_2095_);
if (v___x_2097_ == 0)
{
lean_object* v___x_2098_; 
v___x_2098_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2024_);
lean_dec_ref(v___x_2098_);
v_nondep_2084_ = v___x_2096_;
goto v___jp_2083_;
}
else
{
v_nondep_2084_ = v_nondep_2082_;
goto v___jp_2083_;
}
}
else
{
lean_dec(v_a_2095_);
v_nondep_2084_ = v___x_2096_;
goto v___jp_2083_;
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec_ref(v_value_2081_);
lean_dec_ref(v_type_2080_);
lean_dec(v_userName_2079_);
lean_dec(v_n_2034_);
lean_dec_ref(v_a_2022_);
v_a_2099_ = lean_ctor_get(v___x_2094_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2094_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2094_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2094_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
v___jp_2083_:
{
lean_object* v_expr_2085_; lean_object* v_type_x3f_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; 
v_expr_2085_ = lean_ctor_get(v_a_2022_, 0);
lean_inc_ref(v_expr_2085_);
v_type_x3f_2086_ = lean_ctor_get(v_a_2022_, 1);
lean_inc(v_type_x3f_2086_);
lean_dec_ref(v_a_2022_);
v___x_2087_ = lean_expr_abstract_range(v_type_2080_, v_n_2034_, v_fvars_2020_);
lean_dec_ref(v_type_2080_);
v___x_2088_ = lean_expr_abstract_range(v_value_2081_, v_n_2034_, v_fvars_2020_);
lean_dec_ref(v_value_2081_);
lean_inc_ref(v___x_2088_);
lean_inc_ref(v___x_2087_);
lean_inc(v_userName_2079_);
v___x_2089_ = l_Lean_Expr_letE___override(v_userName_2079_, v___x_2087_, v___x_2088_, v_expr_2085_, v_nondep_2084_);
if (lean_obj_tag(v_type_x3f_2086_) == 0)
{
lean_dec_ref(v___x_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_userName_2079_);
v___y_2040_ = v___x_2089_;
v___y_2041_ = v_type_x3f_2086_;
goto v___jp_2039_;
}
else
{
lean_object* v_val_2090_; uint8_t v___x_2091_; 
v_val_2090_ = lean_ctor_get(v_type_x3f_2086_, 0);
lean_inc(v_val_2090_);
lean_dec_ref_known(v_type_x3f_2086_, 1);
v___x_2091_ = lean_expr_has_loose_bvar(v_val_2090_, v_zero_2030_);
if (v___x_2091_ == 0)
{
lean_object* v___x_2092_; 
lean_dec_ref(v___x_2088_);
lean_dec_ref(v___x_2087_);
lean_dec(v_userName_2079_);
v___x_2092_ = lean_expr_lower_loose_bvars(v_val_2090_, v_one_2033_, v_one_2033_);
lean_dec(v_val_2090_);
v___y_2045_ = v___x_2089_;
v___y_2046_ = v___x_2092_;
goto v___jp_2044_;
}
else
{
lean_object* v___x_2093_; 
v___x_2093_ = l_Lean_Expr_letE___override(v_userName_2079_, v___x_2087_, v___x_2088_, v_val_2090_, v_nondep_2084_);
v___y_2045_ = v___x_2089_;
v___y_2046_ = v___x_2093_;
goto v___jp_2044_;
}
}
}
}
}
else
{
lean_object* v___x_2107_; 
lean_dec(v_a_2051_);
lean_dec_ref(v_a_2022_);
lean_inc(v_fvarId_2049_);
v___x_2107_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2049_, v___y_2027_, v___y_2028_);
v___y_2036_ = v___x_2107_;
goto v___jp_2035_;
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_n_2034_);
lean_dec_ref(v_a_2022_);
v_a_2108_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2050_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2050_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec_ref(v_a_2022_);
v___x_2116_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2117_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2116_, v___y_2023_, v___y_2024_, v___y_2025_, v___y_2026_, v___y_2027_, v___y_2028_);
v___y_2036_ = v___x_2117_;
goto v___jp_2035_;
}
v___jp_2035_:
{
if (lean_obj_tag(v___y_2036_) == 0)
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___y_2036_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___y_2036_, 1);
v_i_2021_ = v_n_2034_;
v_a_2022_ = v_a_2037_;
goto _start;
}
else
{
lean_dec(v_n_2034_);
return v___y_2036_;
}
}
v___jp_2039_:
{
lean_object* v___x_2042_; 
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___y_2040_);
lean_ctor_set(v___x_2042_, 1, v___y_2041_);
v_i_2021_ = v_n_2034_;
v_a_2022_ = v___x_2042_;
goto _start;
}
v___jp_2044_:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2047_, 0, v___y_2046_);
v___y_2040_ = v___y_2045_;
v___y_2041_ = v___x_2047_;
goto v___jp_2039_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2118_, lean_object* v_i_2119_, lean_object* v_a_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2118_, v_i_2119_, v_a_2120_, v___y_2121_, v___y_2122_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
lean_dec(v___y_2122_);
lean_dec(v___y_2121_);
lean_dec_ref(v_fvars_2118_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2129_, lean_object* v_a_2130_){
_start:
{
if (lean_obj_tag(v_a_2129_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = l_List_reverse___redArg(v_a_2130_);
return v___x_2131_;
}
else
{
lean_object* v_head_2132_; lean_object* v_tail_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2142_; 
v_head_2132_ = lean_ctor_get(v_a_2129_, 0);
v_tail_2133_ = lean_ctor_get(v_a_2129_, 1);
v_isSharedCheck_2142_ = !lean_is_exclusive(v_a_2129_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2135_ = v_a_2129_;
v_isShared_2136_ = v_isSharedCheck_2142_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_tail_2133_);
lean_inc(v_head_2132_);
lean_dec(v_a_2129_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2142_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v___x_2139_; 
v___x_2137_ = l_Lean_MessageData_ofExpr(v_head_2132_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 1, v_a_2130_);
lean_ctor_set(v___x_2135_, 0, v___x_2137_);
v___x_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2137_);
lean_ctor_set(v_reuseFailAlloc_2141_, 1, v_a_2130_);
v___x_2139_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
v_a_2129_ = v_tail_2133_;
v_a_2130_ = v___x_2139_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2143_; double v___x_2144_; 
v___x_2143_ = lean_unsigned_to_nat(0u);
v___x_2144_ = lean_float_of_nat(v___x_2143_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2148_, lean_object* v_msg_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_){
_start:
{
lean_object* v_ref_2155_; lean_object* v___x_2156_; lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2201_; 
v_ref_2155_ = lean_ctor_get(v___y_2152_, 2);
v___x_2156_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2149_, v___y_2150_, v___y_2151_, v___y_2152_, v___y_2153_);
v_a_2157_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2159_ = v___x_2156_;
v_isShared_2160_ = v_isSharedCheck_2201_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2156_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2201_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2161_; lean_object* v_traceState_2162_; lean_object* v_env_2163_; lean_object* v_nextMacroScope_2164_; lean_object* v_ngen_2165_; lean_object* v_auxDeclNGen_2166_; lean_object* v_cache_2167_; lean_object* v_messages_2168_; lean_object* v_infoState_2169_; lean_object* v_snapshotTasks_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2200_; 
v___x_2161_ = lean_st_ref_take(v___y_2153_);
v_traceState_2162_ = lean_ctor_get(v___x_2161_, 4);
v_env_2163_ = lean_ctor_get(v___x_2161_, 0);
v_nextMacroScope_2164_ = lean_ctor_get(v___x_2161_, 1);
v_ngen_2165_ = lean_ctor_get(v___x_2161_, 2);
v_auxDeclNGen_2166_ = lean_ctor_get(v___x_2161_, 3);
v_cache_2167_ = lean_ctor_get(v___x_2161_, 5);
v_messages_2168_ = lean_ctor_get(v___x_2161_, 6);
v_infoState_2169_ = lean_ctor_get(v___x_2161_, 7);
v_snapshotTasks_2170_ = lean_ctor_get(v___x_2161_, 8);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2172_ = v___x_2161_;
v_isShared_2173_ = v_isSharedCheck_2200_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_snapshotTasks_2170_);
lean_inc(v_infoState_2169_);
lean_inc(v_messages_2168_);
lean_inc(v_cache_2167_);
lean_inc(v_traceState_2162_);
lean_inc(v_auxDeclNGen_2166_);
lean_inc(v_ngen_2165_);
lean_inc(v_nextMacroScope_2164_);
lean_inc(v_env_2163_);
lean_dec(v___x_2161_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2200_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
uint64_t v_tid_2174_; lean_object* v_traces_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2199_; 
v_tid_2174_ = lean_ctor_get_uint64(v_traceState_2162_, sizeof(void*)*1);
v_traces_2175_ = lean_ctor_get(v_traceState_2162_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v_traceState_2162_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2177_ = v_traceState_2162_;
v_isShared_2178_ = v_isSharedCheck_2199_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_traces_2175_);
lean_dec(v_traceState_2162_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2199_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2179_; double v___x_2180_; uint8_t v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2189_; 
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2181_ = 0;
v___x_2182_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2183_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2183_, 0, v_cls_2148_);
lean_ctor_set(v___x_2183_, 1, v___x_2179_);
lean_ctor_set(v___x_2183_, 2, v___x_2182_);
lean_ctor_set_float(v___x_2183_, sizeof(void*)*3, v___x_2180_);
lean_ctor_set_float(v___x_2183_, sizeof(void*)*3 + 8, v___x_2180_);
lean_ctor_set_uint8(v___x_2183_, sizeof(void*)*3 + 16, v___x_2181_);
v___x_2184_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2185_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2185_, 0, v___x_2183_);
lean_ctor_set(v___x_2185_, 1, v_a_2157_);
lean_ctor_set(v___x_2185_, 2, v___x_2184_);
lean_inc(v_ref_2155_);
v___x_2186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2186_, 0, v_ref_2155_);
lean_ctor_set(v___x_2186_, 1, v___x_2185_);
v___x_2187_ = l_Lean_PersistentArray_push___redArg(v_traces_2175_, v___x_2186_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2187_);
v___x_2189_ = v___x_2177_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v___x_2187_);
lean_ctor_set_uint64(v_reuseFailAlloc_2198_, sizeof(void*)*1, v_tid_2174_);
v___x_2189_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2191_; 
if (v_isShared_2173_ == 0)
{
lean_ctor_set(v___x_2172_, 4, v___x_2189_);
v___x_2191_ = v___x_2172_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_env_2163_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v_nextMacroScope_2164_);
lean_ctor_set(v_reuseFailAlloc_2197_, 2, v_ngen_2165_);
lean_ctor_set(v_reuseFailAlloc_2197_, 3, v_auxDeclNGen_2166_);
lean_ctor_set(v_reuseFailAlloc_2197_, 4, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2197_, 5, v_cache_2167_);
lean_ctor_set(v_reuseFailAlloc_2197_, 6, v_messages_2168_);
lean_ctor_set(v_reuseFailAlloc_2197_, 7, v_infoState_2169_);
lean_ctor_set(v_reuseFailAlloc_2197_, 8, v_snapshotTasks_2170_);
v___x_2191_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
v___x_2192_ = lean_st_ref_put(v___y_2153_, v___x_2191_);
v___x_2193_ = lean_box(0);
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 0, v___x_2193_);
v___x_2195_ = v___x_2159_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2202_, lean_object* v_msg_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_){
_start:
{
lean_object* v_res_2209_; 
v_res_2209_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2202_, v_msg_2203_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
lean_dec(v___y_2207_);
lean_dec_ref(v___y_2206_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2209_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v_cls_2220_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2221_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2222_ = l_Lean_Name_append(v___x_2221_, v_cls_2220_);
return v___x_2222_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2225_ = l_Lean_stringToMessageData(v___x_2224_);
return v___x_2225_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2227_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2228_ = l_Lean_stringToMessageData(v___x_2227_);
return v___x_2228_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2231_ = l_Lean_stringToMessageData(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2236_ = l_Lean_MessageData_ofFormat(v___x_2235_);
return v___x_2236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2237_, lean_object* v_body_2238_, lean_object* v_a_2239_, lean_object* v_a_2240_, lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
lean_object* v___y_2247_; lean_object* v___y_2248_; lean_object* v___y_2249_; lean_object* v___y_2250_; lean_object* v___y_2251_; lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___y_2261_; lean_object* v___y_2262_; lean_object* v___y_2263_; lean_object* v___y_2264_; lean_object* v_toCold_2277_; lean_object* v_options_2278_; uint8_t v_hasTrace_2279_; 
v_toCold_2277_ = lean_ctor_get(v_a_2243_, 0);
v_options_2278_ = lean_ctor_get(v_toCold_2277_, 2);
v_hasTrace_2279_ = lean_ctor_get_uint8(v_options_2278_, sizeof(void*)*1);
if (v_hasTrace_2279_ == 0)
{
v___y_2259_ = v_a_2239_;
v___y_2260_ = v_a_2240_;
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
v___y_2264_ = v_a_2244_;
goto v___jp_2258_;
}
else
{
lean_object* v_inheritedTraceOptions_2280_; lean_object* v_cls_2281_; lean_object* v___x_2282_; uint8_t v___x_2283_; 
v_inheritedTraceOptions_2280_ = lean_ctor_get(v_toCold_2277_, 11);
v_cls_2281_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2282_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2283_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2280_, v_options_2278_, v___x_2282_);
if (v___x_2283_ == 0)
{
v___y_2259_ = v_a_2239_;
v___y_2260_ = v_a_2240_;
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
v___y_2264_ = v_a_2244_;
goto v___jp_2258_;
}
else
{
lean_object* v_expr_2284_; lean_object* v_type_x3f_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___y_2298_; 
v_expr_2284_ = lean_ctor_get(v_body_2238_, 0);
v_type_x3f_2285_ = lean_ctor_get(v_body_2238_, 1);
v___x_2286_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2237_);
v___x_2287_ = lean_array_to_list(v_fvars_2237_);
v___x_2288_ = lean_box(0);
v___x_2289_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2287_, v___x_2288_);
v___x_2290_ = l_Lean_MessageData_ofList(v___x_2289_);
v___x_2291_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2291_, 0, v___x_2286_);
lean_ctor_set(v___x_2291_, 1, v___x_2290_);
v___x_2292_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2293_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
lean_inc_ref(v_expr_2284_);
v___x_2294_ = l_Lean_MessageData_ofExpr(v_expr_2284_);
v___x_2295_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2294_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
if (lean_obj_tag(v_type_x3f_2285_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2298_ = v___x_2311_;
goto v___jp_2297_;
}
else
{
lean_object* v_val_2312_; lean_object* v___x_2313_; 
v_val_2312_ = lean_ctor_get(v_type_x3f_2285_, 0);
lean_inc(v_val_2312_);
v___x_2313_ = l_Lean_MessageData_ofExpr(v_val_2312_);
v___y_2298_ = v___x_2313_;
goto v___jp_2297_;
}
v___jp_2297_:
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2296_);
lean_ctor_set(v___x_2299_, 1, v___y_2298_);
v___x_2300_ = l_Lean_indentD(v___x_2299_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2293_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2281_, v___x_2301_, v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_dec_ref_known(v___x_2302_, 1);
v___y_2259_ = v_a_2239_;
v___y_2260_ = v_a_2240_;
v___y_2261_ = v_a_2241_;
v___y_2262_ = v_a_2242_;
v___y_2263_ = v_a_2243_;
v___y_2264_ = v_a_2244_;
goto v___jp_2258_;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec_ref(v_body_2238_);
lean_dec_ref(v_fvars_2237_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
v___jp_2246_:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___y_2253_);
lean_ctor_set(v___x_2255_, 1, v___y_2254_);
v___x_2256_ = lean_array_get_size(v_fvars_2237_);
v___x_2257_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2237_, v___x_2256_, v___x_2255_, v___y_2248_, v___y_2252_, v___y_2250_, v___y_2247_, v___y_2249_, v___y_2251_);
lean_dec_ref(v_fvars_2237_);
return v___x_2257_;
}
v___jp_2258_:
{
lean_object* v_expr_2265_; lean_object* v_type_x3f_2266_; lean_object* v___x_2267_; 
v_expr_2265_ = lean_ctor_get(v_body_2238_, 0);
lean_inc_ref(v_expr_2265_);
v_type_x3f_2266_ = lean_ctor_get(v_body_2238_, 1);
lean_inc(v_type_x3f_2266_);
lean_dec_ref(v_body_2238_);
v___x_2267_ = lean_expr_abstract(v_expr_2265_, v_fvars_2237_);
lean_dec_ref(v_expr_2265_);
if (lean_obj_tag(v_type_x3f_2266_) == 0)
{
v___y_2247_ = v___y_2262_;
v___y_2248_ = v___y_2259_;
v___y_2249_ = v___y_2263_;
v___y_2250_ = v___y_2261_;
v___y_2251_ = v___y_2264_;
v___y_2252_ = v___y_2260_;
v___y_2253_ = v___x_2267_;
v___y_2254_ = v_type_x3f_2266_;
goto v___jp_2246_;
}
else
{
lean_object* v_val_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2276_; 
v_val_2268_ = lean_ctor_get(v_type_x3f_2266_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v_type_x3f_2266_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2270_ = v_type_x3f_2266_;
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_val_2268_);
lean_dec(v_type_x3f_2266_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2276_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
v___x_2272_ = lean_expr_abstract(v_val_2268_, v_fvars_2237_);
lean_dec(v_val_2268_);
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 0, v___x_2272_);
v___x_2274_ = v___x_2270_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
v___y_2247_ = v___y_2262_;
v___y_2248_ = v___y_2259_;
v___y_2249_ = v___y_2263_;
v___y_2250_ = v___y_2261_;
v___y_2251_ = v___y_2264_;
v___y_2252_ = v___y_2260_;
v___y_2253_ = v___x_2267_;
v___y_2254_ = v___x_2274_;
goto v___jp_2246_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2314_, lean_object* v_body_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_){
_start:
{
lean_object* v_res_2323_; 
v_res_2323_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2314_, v_body_2315_, v_a_2316_, v_a_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
lean_dec(v_a_2321_);
lean_dec_ref(v_a_2320_);
lean_dec(v_a_2319_);
lean_dec_ref(v_a_2318_);
lean_dec(v_a_2317_);
lean_dec(v_a_2316_);
return v_res_2323_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2324_, lean_object* v_n_2325_, lean_object* v_i_2326_, lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_, lean_object* v___y_2334_){
_start:
{
lean_object* v___x_2336_; 
v___x_2336_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2324_, v_i_2326_, v_a_2328_, v___y_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_, v___y_2334_);
return v___x_2336_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2337_, lean_object* v_n_2338_, lean_object* v_i_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2337_, v_n_2338_, v_i_2339_, v_a_2340_, v_a_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_);
lean_dec(v___y_2347_);
lean_dec_ref(v___y_2346_);
lean_dec(v___y_2345_);
lean_dec_ref(v___y_2344_);
lean_dec(v___y_2343_);
lean_dec(v___y_2342_);
lean_dec(v_n_2338_);
lean_dec_ref(v_fvars_2337_);
return v_res_2349_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2350_, lean_object* v_msg_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v___x_2359_; 
v___x_2359_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2350_, v_msg_2351_, v___y_2354_, v___y_2355_, v___y_2356_, v___y_2357_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2360_, lean_object* v_msg_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_, lean_object* v___y_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2360_, v_msg_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_);
lean_dec(v___y_2367_);
lean_dec_ref(v___y_2366_);
lean_dec(v___y_2365_);
lean_dec_ref(v___y_2364_);
lean_dec(v___y_2363_);
lean_dec(v___y_2362_);
return v_res_2369_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; 
v___x_2371_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2372_ = l_Lean_stringToMessageData(v___x_2371_);
return v___x_2372_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; 
v___x_2374_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2375_ = l_Lean_stringToMessageData(v___x_2374_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2376_, lean_object* v_structName_2377_, lean_object* v_idx_2378_, lean_object* v_a_2379_, lean_object* v_00_u03b1_2380_, lean_object* v_x_2381_, lean_object* v___y_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_){
_start:
{
lean_object* v_expr_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2404_; 
v_expr_2389_ = lean_ctor_get(v_struct_2376_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_struct_2376_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v_struct_2376_, 1);
lean_dec(v_unused_2405_);
v___x_2391_ = v_struct_2376_;
v_isShared_2392_ = v_isSharedCheck_2404_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_expr_2389_);
lean_dec(v_struct_2376_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2404_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2393_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2394_ = l_Lean_mkProj(v_structName_2377_, v_idx_2378_, v_expr_2389_);
v___x_2395_ = l_Lean_indentExpr(v___x_2394_);
if (v_isShared_2392_ == 0)
{
lean_ctor_set_tag(v___x_2391_, 7);
lean_ctor_set(v___x_2391_, 1, v___x_2395_);
lean_ctor_set(v___x_2391_, 0, v___x_2393_);
v___x_2397_ = v___x_2391_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2393_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; 
v___x_2398_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2397_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = l_Lean_indentExpr(v_a_2379_);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2399_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2401_, v___y_2384_, v___y_2385_, v___y_2386_, v___y_2387_);
return v___x_2402_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2406_, lean_object* v_structName_2407_, lean_object* v_idx_2408_, lean_object* v_a_2409_, lean_object* v_00_u03b1_2410_, lean_object* v_x_2411_, lean_object* v___y_2412_, lean_object* v___y_2413_, lean_object* v___y_2414_, lean_object* v___y_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2406_, v_structName_2407_, v_idx_2408_, v_a_2409_, v_00_u03b1_2410_, v_x_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec(v___y_2412_);
return v_res_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v___x_2428_; lean_object* v_env_2429_; uint8_t v___x_2430_; lean_object* v___x_2431_; 
v___x_2428_ = lean_st_ref_get(v___y_2426_);
v_env_2429_ = lean_ctor_get(v___x_2428_, 0);
lean_inc_ref(v_env_2429_);
lean_dec(v___x_2428_);
v___x_2430_ = 0;
lean_inc(v_constName_2420_);
v___x_2431_ = l_Lean_Environment_find_x3f(v_env_2429_, v_constName_2420_, v___x_2430_);
if (lean_obj_tag(v___x_2431_) == 0)
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
return v___x_2432_;
}
else
{
lean_object* v_val_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_dec(v_constName_2420_);
v_val_2433_ = lean_ctor_get(v___x_2431_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2431_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_val_2433_);
lean_dec(v___x_2431_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
lean_ctor_set_tag(v___x_2435_, 0);
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_val_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_){
_start:
{
lean_object* v_res_2449_; 
v_res_2449_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2441_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_, v___y_2446_, v___y_2447_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
lean_dec(v___y_2445_);
lean_dec_ref(v___y_2444_);
lean_dec(v___y_2443_);
lean_dec(v___y_2442_);
return v_res_2449_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2450_, lean_object* v_structName_2451_, lean_object* v_idx_2452_, lean_object* v_a_2453_, lean_object* v_00_u03b1_2454_, lean_object* v_x_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_, lean_object* v___y_2461_){
_start:
{
lean_object* v_expr_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2478_; 
v_expr_2463_ = lean_ctor_get(v_struct_2450_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v_struct_2450_);
if (v_isSharedCheck_2478_ == 0)
{
lean_object* v_unused_2479_; 
v_unused_2479_ = lean_ctor_get(v_struct_2450_, 1);
lean_dec(v_unused_2479_);
v___x_2465_ = v_struct_2450_;
v_isShared_2466_ = v_isSharedCheck_2478_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_expr_2463_);
lean_dec(v_struct_2450_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2478_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2471_; 
v___x_2467_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2468_ = l_Lean_mkProj(v_structName_2451_, v_idx_2452_, v_expr_2463_);
v___x_2469_ = l_Lean_indentExpr(v___x_2468_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set_tag(v___x_2465_, 7);
lean_ctor_set(v___x_2465_, 1, v___x_2469_);
lean_ctor_set(v___x_2465_, 0, v___x_2467_);
v___x_2471_ = v___x_2465_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v___x_2467_);
lean_ctor_set(v_reuseFailAlloc_2477_, 1, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; 
v___x_2472_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = l_Lean_indentExpr(v_a_2453_);
v___x_2475_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
v___x_2476_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2475_, v___y_2458_, v___y_2459_, v___y_2460_, v___y_2461_);
return v___x_2476_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2480_, lean_object* v_structName_2481_, lean_object* v_idx_2482_, lean_object* v_a_2483_, lean_object* v_00_u03b1_2484_, lean_object* v_x_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2480_, v_structName_2481_, v_idx_2482_, v_a_2483_, v_00_u03b1_2484_, v_x_2485_, v___y_2486_, v___y_2487_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec(v___y_2489_);
lean_dec_ref(v___y_2488_);
lean_dec(v___y_2487_);
lean_dec(v___y_2486_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2494_, lean_object* v_fst_2495_, lean_object* v_struct_2496_, lean_object* v_structName_2497_, uint8_t v_a_2498_, lean_object* v___f_2499_, lean_object* v_snd_2500_, lean_object* v_____r_2501_, lean_object* v_ctorType_2502_, lean_object* v_j_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_){
_start:
{
if (lean_obj_tag(v_ctorType_2502_) == 7)
{
lean_object* v_binderType_2511_; lean_object* v_body_2512_; lean_object* v___x_2513_; 
lean_dec(v_snd_2500_);
v_binderType_2511_ = lean_ctor_get(v_ctorType_2502_, 1);
lean_inc_ref(v_binderType_2511_);
v_body_2512_ = lean_ctor_get(v_ctorType_2502_, 2);
lean_inc_ref(v_body_2512_);
lean_dec_ref_known(v_ctorType_2502_, 3);
v___x_2513_ = lean_expr_instantiate_rev_range(v_binderType_2511_, v_j_2503_, v_a_2494_, v_fst_2495_);
lean_dec_ref(v_binderType_2511_);
if (v_a_2498_ == 0)
{
lean_dec_ref(v___f_2499_);
goto v___jp_2514_;
}
else
{
lean_object* v___x_2530_; 
lean_inc_ref(v___x_2513_);
v___x_2530_ = l_Lean_Meta_isProp(v___x_2513_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; uint8_t v___x_2532_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
lean_inc(v_a_2531_);
lean_dec_ref_known(v___x_2530_, 1);
v___x_2532_ = lean_unbox(v_a_2531_);
lean_dec(v_a_2531_);
if (v___x_2532_ == 0)
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = lean_box(0);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc(v___y_2504_);
v___x_2534_ = lean_apply_9(v___f_2499_, lean_box(0), v___x_2533_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, lean_box(0));
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_dec_ref_known(v___x_2534_, 1);
goto v___jp_2514_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v___x_2513_);
lean_dec_ref(v_body_2512_);
lean_dec(v_structName_2497_);
lean_dec_ref(v_struct_2496_);
lean_dec(v_fst_2495_);
lean_dec(v_a_2494_);
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
}
else
{
lean_dec_ref(v___f_2499_);
goto v___jp_2514_;
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec_ref(v___x_2513_);
lean_dec_ref(v_body_2512_);
lean_dec_ref(v___f_2499_);
lean_dec(v_structName_2497_);
lean_dec_ref(v_struct_2496_);
lean_dec(v_fst_2495_);
lean_dec(v_a_2494_);
v_a_2543_ = lean_ctor_get(v___x_2530_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2530_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2530_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2548_; 
if (v_isShared_2546_ == 0)
{
v___x_2548_ = v___x_2545_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v_a_2543_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
v___jp_2514_:
{
lean_object* v_expr_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2528_; 
v_expr_2515_ = lean_ctor_get(v_struct_2496_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v_struct_2496_);
if (v_isSharedCheck_2528_ == 0)
{
lean_object* v_unused_2529_; 
v_unused_2529_ = lean_ctor_get(v_struct_2496_, 1);
lean_dec(v_unused_2529_);
v___x_2517_ = v_struct_2496_;
v_isShared_2518_ = v_isSharedCheck_2528_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_expr_2515_);
lean_dec(v_struct_2496_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2528_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2522_; 
v___x_2519_ = l_Lean_Expr_proj___override(v_structName_2497_, v_a_2494_, v_expr_2515_);
v___x_2520_ = lean_array_push(v_fst_2495_, v___x_2519_);
lean_inc(v_j_2503_);
if (v_isShared_2518_ == 0)
{
lean_ctor_set(v___x_2517_, 1, v___x_2513_);
lean_ctor_set(v___x_2517_, 0, v_j_2503_);
v___x_2522_ = v___x_2517_;
goto v_reusejp_2521_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_j_2503_);
lean_ctor_set(v_reuseFailAlloc_2527_, 1, v___x_2513_);
v___x_2522_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2521_;
}
v_reusejp_2521_:
{
lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2523_, 0, v___x_2520_);
lean_ctor_set(v___x_2523_, 1, v___x_2522_);
v___x_2524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2524_, 0, v_body_2512_);
lean_ctor_set(v___x_2524_, 1, v___x_2523_);
v___x_2525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
}
}
}
else
{
lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec(v_structName_2497_);
lean_dec_ref(v_struct_2496_);
lean_dec(v_a_2494_);
v___x_2551_ = lean_box(0);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc(v___y_2504_);
v___x_2552_ = lean_apply_9(v___f_2499_, lean_box(0), v___x_2551_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, v___y_2508_, v___y_2509_, lean_box(0));
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2563_; 
v_isSharedCheck_2563_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v___x_2552_, 0);
lean_dec(v_unused_2564_);
v___x_2554_ = v___x_2552_;
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
else
{
lean_dec(v___x_2552_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2563_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2561_; 
lean_inc(v_j_2503_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v_j_2503_);
lean_ctor_set(v___x_2556_, 1, v_snd_2500_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v_fst_2495_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_ctorType_2502_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v___x_2559_);
v___x_2561_ = v___x_2554_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_ctorType_2502_);
lean_dec(v_snd_2500_);
lean_dec(v_fst_2495_);
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
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2573_ = _args[0];
lean_object* v_fst_2574_ = _args[1];
lean_object* v_struct_2575_ = _args[2];
lean_object* v_structName_2576_ = _args[3];
lean_object* v_a_2577_ = _args[4];
lean_object* v___f_2578_ = _args[5];
lean_object* v_snd_2579_ = _args[6];
lean_object* v_____r_2580_ = _args[7];
lean_object* v_ctorType_2581_ = _args[8];
lean_object* v_j_2582_ = _args[9];
lean_object* v___y_2583_ = _args[10];
lean_object* v___y_2584_ = _args[11];
lean_object* v___y_2585_ = _args[12];
lean_object* v___y_2586_ = _args[13];
lean_object* v___y_2587_ = _args[14];
lean_object* v___y_2588_ = _args[15];
lean_object* v___y_2589_ = _args[16];
_start:
{
uint8_t v_a_19024__boxed_2590_; lean_object* v_res_2591_; 
v_a_19024__boxed_2590_ = lean_unbox(v_a_2577_);
v_res_2591_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2573_, v_fst_2574_, v_struct_2575_, v_structName_2576_, v_a_19024__boxed_2590_, v___f_2578_, v_snd_2579_, v_____r_2580_, v_ctorType_2581_, v_j_2582_, v___y_2583_, v___y_2584_, v___y_2585_, v___y_2586_, v___y_2587_, v___y_2588_);
lean_dec(v___y_2588_);
lean_dec_ref(v___y_2587_);
lean_dec(v___y_2586_);
lean_dec_ref(v___y_2585_);
lean_dec(v___y_2584_);
lean_dec(v___y_2583_);
lean_dec(v_j_2582_);
return v_res_2591_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2592_, lean_object* v_struct_2593_, lean_object* v_structName_2594_, uint8_t v_a_2595_, lean_object* v_idx_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_b_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_){
_start:
{
lean_object* v___y_2608_; uint8_t v___x_2630_; 
v___x_2630_ = lean_nat_dec_le(v_a_2598_, v_upperBound_2592_);
if (v___x_2630_ == 0)
{
lean_object* v___x_2631_; 
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_idx_2596_);
lean_dec(v_structName_2594_);
lean_dec_ref(v_struct_2593_);
v___x_2631_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2631_, 0, v_b_2599_);
return v___x_2631_;
}
else
{
lean_object* v_snd_2632_; lean_object* v_snd_2633_; lean_object* v_fst_2634_; lean_object* v_fst_2635_; lean_object* v_fst_2636_; lean_object* v_snd_2637_; lean_object* v___f_2638_; uint8_t v___x_2639_; 
v_snd_2632_ = lean_ctor_get(v_b_2599_, 1);
lean_inc(v_snd_2632_);
v_snd_2633_ = lean_ctor_get(v_snd_2632_, 1);
lean_inc(v_snd_2633_);
v_fst_2634_ = lean_ctor_get(v_b_2599_, 0);
lean_inc(v_fst_2634_);
lean_dec_ref(v_b_2599_);
v_fst_2635_ = lean_ctor_get(v_snd_2632_, 0);
lean_inc(v_fst_2635_);
lean_dec(v_snd_2632_);
v_fst_2636_ = lean_ctor_get(v_snd_2633_, 0);
lean_inc(v_fst_2636_);
v_snd_2637_ = lean_ctor_get(v_snd_2633_, 1);
lean_inc(v_snd_2637_);
lean_dec(v_snd_2633_);
lean_inc_ref(v_a_2597_);
lean_inc(v_idx_2596_);
lean_inc(v_structName_2594_);
lean_inc_ref(v_struct_2593_);
v___f_2638_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2638_, 0, v_struct_2593_);
lean_closure_set(v___f_2638_, 1, v_structName_2594_);
lean_closure_set(v___f_2638_, 2, v_idx_2596_);
lean_closure_set(v___f_2638_, 3, v_a_2597_);
v___x_2639_ = l_Lean_Expr_isForall(v_fst_2634_);
if (v___x_2639_ == 0)
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = lean_expr_instantiate_rev_range(v_fst_2634_, v_fst_2636_, v_a_2598_, v_fst_2635_);
lean_dec(v_fst_2636_);
lean_dec(v_fst_2634_);
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2604_);
lean_inc(v___y_2603_);
lean_inc_ref(v___y_2602_);
v___x_2641_ = lean_whnf(v___x_2640_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = lean_box(0);
lean_inc(v_structName_2594_);
lean_inc_ref(v_struct_2593_);
lean_inc(v_a_2598_);
v___x_2644_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2598_, v_fst_2635_, v_struct_2593_, v_structName_2594_, v_a_2595_, v___f_2638_, v_snd_2637_, v___x_2643_, v_a_2642_, v_a_2598_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
v___y_2608_ = v___x_2644_;
goto v___jp_2607_;
}
else
{
lean_object* v_a_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2652_; 
lean_dec_ref(v___f_2638_);
lean_dec(v_snd_2637_);
lean_dec(v_fst_2635_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_idx_2596_);
lean_dec(v_structName_2594_);
lean_dec_ref(v_struct_2593_);
v_a_2645_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2652_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2652_ == 0)
{
v___x_2647_ = v___x_2641_;
v_isShared_2648_ = v_isSharedCheck_2652_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_a_2645_);
lean_dec(v___x_2641_);
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
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_box(0);
lean_inc(v_structName_2594_);
lean_inc_ref(v_struct_2593_);
lean_inc(v_a_2598_);
v___x_2654_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2598_, v_fst_2635_, v_struct_2593_, v_structName_2594_, v_a_2595_, v___f_2638_, v_snd_2637_, v___x_2653_, v_fst_2634_, v_fst_2636_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_);
lean_dec(v_fst_2636_);
v___y_2608_ = v___x_2654_;
goto v___jp_2607_;
}
}
v___jp_2607_:
{
if (lean_obj_tag(v___y_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2621_; 
v_a_2609_ = lean_ctor_get(v___y_2608_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___y_2608_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2611_ = v___y_2608_;
v_isShared_2612_ = v_isSharedCheck_2621_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___y_2608_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2621_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
if (lean_obj_tag(v_a_2609_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2615_; 
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_idx_2596_);
lean_dec(v_structName_2594_);
lean_dec_ref(v_struct_2593_);
v_a_2613_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v_a_2609_, 1);
if (v_isShared_2612_ == 0)
{
lean_ctor_set(v___x_2611_, 0, v_a_2613_);
v___x_2615_ = v___x_2611_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2613_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
lean_del_object(v___x_2611_);
v_a_2617_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_a_2617_);
lean_dec_ref_known(v_a_2609_, 1);
v___x_2618_ = lean_unsigned_to_nat(1u);
v___x_2619_ = lean_nat_add(v_a_2598_, v___x_2618_);
lean_dec(v_a_2598_);
v_a_2598_ = v___x_2619_;
v_b_2599_ = v_a_2617_;
goto _start;
}
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2624_; uint8_t v_isShared_2625_; uint8_t v_isSharedCheck_2629_; 
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_idx_2596_);
lean_dec(v_structName_2594_);
lean_dec_ref(v_struct_2593_);
v_a_2622_ = lean_ctor_get(v___y_2608_, 0);
v_isSharedCheck_2629_ = !lean_is_exclusive(v___y_2608_);
if (v_isSharedCheck_2629_ == 0)
{
v___x_2624_ = v___y_2608_;
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
else
{
lean_inc(v_a_2622_);
lean_dec(v___y_2608_);
v___x_2624_ = lean_box(0);
v_isShared_2625_ = v_isSharedCheck_2629_;
goto v_resetjp_2623_;
}
v_resetjp_2623_:
{
lean_object* v___x_2627_; 
if (v_isShared_2625_ == 0)
{
v___x_2627_ = v___x_2624_;
goto v_reusejp_2626_;
}
else
{
lean_object* v_reuseFailAlloc_2628_; 
v_reuseFailAlloc_2628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2628_, 0, v_a_2622_);
v___x_2627_ = v_reuseFailAlloc_2628_;
goto v_reusejp_2626_;
}
v_reusejp_2626_:
{
return v___x_2627_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2655_, lean_object* v_struct_2656_, lean_object* v_structName_2657_, lean_object* v_a_2658_, lean_object* v_idx_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_b_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
uint8_t v_a_19181__boxed_2670_; lean_object* v_res_2671_; 
v_a_19181__boxed_2670_ = lean_unbox(v_a_2658_);
v_res_2671_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2655_, v_struct_2656_, v_structName_2657_, v_a_19181__boxed_2670_, v_idx_2659_, v_a_2660_, v_a_2661_, v_b_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_);
lean_dec(v___y_2668_);
lean_dec_ref(v___y_2667_);
lean_dec(v___y_2666_);
lean_dec_ref(v___y_2665_);
lean_dec(v___y_2664_);
lean_dec(v___y_2663_);
lean_dec(v_upperBound_2655_);
return v_res_2671_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2674_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2675_ = lean_unsigned_to_nat(18u);
v___x_2676_ = lean_unsigned_to_nat(1896u);
v___x_2677_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2678_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2679_ = l_mkPanicMessageWithDecl(v___x_2678_, v___x_2677_, v___x_2676_, v___x_2675_, v___x_2674_);
return v___x_2679_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2681_ = lean_unsigned_to_nat(0u);
v___x_2682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2682_, 0, v___x_2681_);
lean_ctor_set(v___x_2682_, 1, v___x_2680_);
return v___x_2682_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2683_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2684_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2685_, 0, v___x_2684_);
lean_ctor_set(v___x_2685_, 1, v___x_2683_);
return v___x_2685_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2686_; lean_object* v_dummy_2687_; 
v___x_2686_ = lean_box(0);
v_dummy_2687_ = l_Lean_Expr_sort___override(v___x_2686_);
return v_dummy_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2688_, lean_object* v_structName_2689_, lean_object* v_idx_2690_, lean_object* v_struct_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_){
_start:
{
lean_object* v___y_2700_; lean_object* v___y_2701_; lean_object* v___y_2706_; uint8_t v___x_2710_; 
v___x_2710_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2692_);
if (v___x_2710_ == 0)
{
lean_dec(v_idx_2690_);
lean_dec(v_structName_2689_);
if (lean_obj_tag(v_e_2688_) == 11)
{
lean_object* v_expr_2711_; lean_object* v_typeName_2712_; lean_object* v_idx_2713_; lean_object* v_struct_2714_; size_t v___x_2715_; size_t v___x_2716_; uint8_t v___x_2717_; 
v_expr_2711_ = lean_ctor_get(v_struct_2691_, 0);
lean_inc_ref(v_expr_2711_);
lean_dec_ref(v_struct_2691_);
v_typeName_2712_ = lean_ctor_get(v_e_2688_, 0);
v_idx_2713_ = lean_ctor_get(v_e_2688_, 1);
v_struct_2714_ = lean_ctor_get(v_e_2688_, 2);
v___x_2715_ = lean_ptr_addr(v_struct_2714_);
v___x_2716_ = lean_ptr_addr(v_expr_2711_);
v___x_2717_ = lean_usize_dec_eq(v___x_2715_, v___x_2716_);
if (v___x_2717_ == 0)
{
lean_object* v___x_2718_; 
lean_inc(v_idx_2713_);
lean_inc(v_typeName_2712_);
lean_dec_ref_known(v_e_2688_, 3);
v___x_2718_ = l_Lean_Expr_proj___override(v_typeName_2712_, v_idx_2713_, v_expr_2711_);
v___y_2706_ = v___x_2718_;
goto v___jp_2705_;
}
else
{
lean_dec_ref(v_expr_2711_);
v___y_2706_ = v_e_2688_;
goto v___jp_2705_;
}
}
else
{
lean_object* v___x_2719_; lean_object* v___x_2720_; 
lean_dec_ref(v_struct_2691_);
lean_dec_ref(v_e_2688_);
v___x_2719_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2720_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2719_);
v___y_2706_ = v___x_2720_;
goto v___jp_2705_;
}
}
else
{
lean_object* v___x_2721_; 
lean_inc_ref(v_struct_2691_);
v___x_2721_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2691_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2723_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2721_, 1);
lean_inc(v_a_2697_);
lean_inc_ref(v_a_2696_);
lean_inc(v_a_2695_);
lean_inc_ref(v_a_2694_);
v___x_2723_ = lean_whnf(v_a_2722_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2725_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc_n(v_a_2724_, 2);
lean_dec_ref_known(v___x_2723_, 1);
v___x_2725_ = l_Lean_Meta_isProp(v_a_2724_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2725_) == 0)
{
lean_object* v_a_2726_; lean_object* v___x_2727_; 
v_a_2726_ = lean_ctor_get(v___x_2725_, 0);
lean_inc(v_a_2726_);
lean_dec_ref_known(v___x_2725_, 1);
v___x_2727_ = l_Lean_Expr_getAppFn(v_a_2724_);
if (lean_obj_tag(v___x_2727_) == 4)
{
lean_object* v_declName_2728_; lean_object* v_us_2729_; lean_object* v___x_2730_; lean_object* v_env_2734_; uint8_t v___x_2735_; lean_object* v___x_2736_; 
v_declName_2728_ = lean_ctor_get(v___x_2727_, 0);
lean_inc(v_declName_2728_);
v_us_2729_ = lean_ctor_get(v___x_2727_, 1);
lean_inc(v_us_2729_);
lean_dec_ref_known(v___x_2727_, 2);
v___x_2730_ = lean_st_ref_get(v_a_2697_);
v_env_2734_ = lean_ctor_get(v___x_2730_, 0);
lean_inc_ref(v_env_2734_);
lean_dec(v___x_2730_);
v___x_2735_ = 0;
v___x_2736_ = l_Lean_Environment_find_x3f(v_env_2734_, v_declName_2728_, v___x_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
v___x_2737_ = lean_box(0);
v___x_2738_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2691_, v_structName_2689_, v_idx_2690_, v_a_2724_, lean_box(0), v___x_2737_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2738_;
}
else
{
lean_object* v_val_2739_; 
v_val_2739_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v___x_2736_, 1);
if (lean_obj_tag(v_val_2739_) == 5)
{
lean_object* v_val_2740_; lean_object* v_ctors_2741_; 
v_val_2740_ = lean_ctor_get(v_val_2739_, 0);
lean_inc_ref(v_val_2740_);
lean_dec_ref_known(v_val_2739_, 1);
v_ctors_2741_ = lean_ctor_get(v_val_2740_, 4);
lean_inc(v_ctors_2741_);
if (lean_obj_tag(v_ctors_2741_) == 1)
{
lean_object* v_tail_2742_; 
v_tail_2742_ = lean_ctor_get(v_ctors_2741_, 1);
if (lean_obj_tag(v_tail_2742_) == 0)
{
lean_object* v_toConstantVal_2743_; lean_object* v_numParams_2744_; lean_object* v_numIndices_2745_; lean_object* v_head_2746_; lean_object* v___x_2748_; uint8_t v_isShared_2749_; uint8_t v_isSharedCheck_2855_; 
v_toConstantVal_2743_ = lean_ctor_get(v_val_2740_, 0);
lean_inc_ref(v_toConstantVal_2743_);
v_numParams_2744_ = lean_ctor_get(v_val_2740_, 1);
lean_inc(v_numParams_2744_);
v_numIndices_2745_ = lean_ctor_get(v_val_2740_, 2);
lean_inc(v_numIndices_2745_);
lean_dec_ref(v_val_2740_);
v_head_2746_ = lean_ctor_get(v_ctors_2741_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_ctors_2741_);
if (v_isSharedCheck_2855_ == 0)
{
lean_object* v_unused_2856_; 
v_unused_2856_ = lean_ctor_get(v_ctors_2741_, 1);
lean_dec(v_unused_2856_);
v___x_2748_ = v_ctors_2741_;
v_isShared_2749_ = v_isSharedCheck_2855_;
goto v_resetjp_2747_;
}
else
{
lean_inc(v_head_2746_);
lean_dec(v_ctors_2741_);
v___x_2748_ = lean_box(0);
v_isShared_2749_ = v_isSharedCheck_2855_;
goto v_resetjp_2747_;
}
v_resetjp_2747_:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2746_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
if (lean_obj_tag(v_a_2751_) == 6)
{
lean_object* v_val_2752_; lean_object* v___y_2754_; lean_object* v___y_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v_name_2833_; uint8_t v___x_2834_; 
v_val_2752_ = lean_ctor_get(v_a_2751_, 0);
lean_inc_ref(v_val_2752_);
lean_dec_ref_known(v_a_2751_, 1);
v_name_2833_ = lean_ctor_get(v_toConstantVal_2743_, 0);
lean_inc(v_name_2833_);
lean_dec_ref(v_toConstantVal_2743_);
v___x_2834_ = lean_name_eq(v_name_2833_, v_structName_2689_);
lean_dec(v_name_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v_a_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2844_; 
lean_dec_ref(v_val_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_numIndices_2745_);
lean_dec(v_numParams_2744_);
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
v___x_2835_ = lean_box(0);
v___x_2836_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2691_, v_structName_2689_, v_idx_2690_, v_a_2724_, lean_box(0), v___x_2835_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2844_ == 0)
{
v___x_2839_ = v___x_2836_;
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_a_2837_);
lean_dec(v___x_2836_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2844_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2842_; 
if (v_isShared_2840_ == 0)
{
v___x_2842_ = v___x_2839_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
v___y_2808_ = v_a_2692_;
v___y_2809_ = v_a_2693_;
v___y_2810_ = v_a_2694_;
v___y_2811_ = v_a_2695_;
v___y_2812_ = v_a_2696_;
v___y_2813_ = v_a_2697_;
goto v___jp_2807_;
}
v___jp_2753_:
{
lean_object* v_toConstantVal_2761_; lean_object* v_name_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; 
v_toConstantVal_2761_ = lean_ctor_get(v_val_2752_, 0);
lean_inc_ref(v_toConstantVal_2761_);
lean_dec_ref(v_val_2752_);
v_name_2762_ = lean_ctor_get(v_toConstantVal_2761_, 0);
lean_inc(v_name_2762_);
lean_dec_ref(v_toConstantVal_2761_);
v___x_2763_ = l_Lean_mkConst(v_name_2762_, v_us_2729_);
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = l_Array_toSubarray___redArg(v___y_2754_, v___x_2764_, v_numParams_2744_);
v___x_2766_ = l_Subarray_copy___redArg(v___x_2765_);
v___x_2767_ = l_Lean_mkAppN(v___x_2763_, v___x_2766_);
lean_dec_ref(v___x_2766_);
lean_inc(v___y_2760_);
lean_inc_ref(v___y_2759_);
lean_inc(v___y_2758_);
lean_inc_ref(v___y_2757_);
v___x_2768_ = lean_infer_type(v___x_2767_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2770_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2749_ == 0)
{
lean_ctor_set_tag(v___x_2748_, 0);
lean_ctor_set(v___x_2748_, 1, v___x_2770_);
lean_ctor_set(v___x_2748_, 0, v_a_2769_);
v___x_2772_ = v___x_2748_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2769_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v___x_2770_);
v___x_2772_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
uint8_t v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = lean_unbox(v_a_2726_);
lean_dec(v_a_2726_);
lean_inc_ref(v_struct_2691_);
lean_inc(v_idx_2690_);
v___x_2774_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2690_, v_struct_2691_, v_structName_2689_, v___x_2773_, v_idx_2690_, v_a_2724_, v___x_2764_, v___x_2772_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v_idx_2690_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v_snd_2776_; lean_object* v_snd_2777_; lean_object* v_snd_2778_; lean_object* v_expr_2779_; lean_object* v___x_2780_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v_snd_2776_ = lean_ctor_get(v_a_2775_, 1);
lean_inc(v_snd_2776_);
lean_dec(v_a_2775_);
v_snd_2777_ = lean_ctor_get(v_snd_2776_, 1);
lean_inc(v_snd_2777_);
lean_dec(v_snd_2776_);
v_snd_2778_ = lean_ctor_get(v_snd_2777_, 1);
lean_inc(v_snd_2778_);
lean_dec(v_snd_2777_);
v_expr_2779_ = lean_ctor_get(v_struct_2691_, 0);
lean_inc_ref(v_expr_2779_);
lean_dec_ref(v_struct_2691_);
v___x_2780_ = l_Lean_Expr_cleanupAnnotations(v_snd_2778_);
if (lean_obj_tag(v_e_2688_) == 11)
{
lean_object* v_typeName_2781_; lean_object* v_idx_2782_; lean_object* v_struct_2783_; size_t v___x_2784_; size_t v___x_2785_; uint8_t v___x_2786_; 
v_typeName_2781_ = lean_ctor_get(v_e_2688_, 0);
v_idx_2782_ = lean_ctor_get(v_e_2688_, 1);
v_struct_2783_ = lean_ctor_get(v_e_2688_, 2);
v___x_2784_ = lean_ptr_addr(v_struct_2783_);
v___x_2785_ = lean_ptr_addr(v_expr_2779_);
v___x_2786_ = lean_usize_dec_eq(v___x_2784_, v___x_2785_);
if (v___x_2786_ == 0)
{
lean_object* v___x_2787_; 
lean_inc(v_idx_2782_);
lean_inc(v_typeName_2781_);
lean_dec_ref_known(v_e_2688_, 3);
v___x_2787_ = l_Lean_Expr_proj___override(v_typeName_2781_, v_idx_2782_, v_expr_2779_);
v___y_2700_ = v___x_2780_;
v___y_2701_ = v___x_2787_;
goto v___jp_2699_;
}
else
{
lean_dec_ref(v_expr_2779_);
v___y_2700_ = v___x_2780_;
v___y_2701_ = v_e_2688_;
goto v___jp_2699_;
}
}
else
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
lean_dec_ref(v_expr_2779_);
lean_dec_ref(v_e_2688_);
v___x_2788_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2789_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2788_);
v___y_2700_ = v___x_2780_;
v___y_2701_ = v___x_2789_;
goto v___jp_2699_;
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2797_; 
lean_dec_ref(v_struct_2691_);
lean_dec_ref(v_e_2688_);
v_a_2790_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2797_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2797_ == 0)
{
v___x_2792_ = v___x_2774_;
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2774_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2797_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2795_; 
if (v_isShared_2793_ == 0)
{
v___x_2795_ = v___x_2792_;
goto v_reusejp_2794_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_a_2790_);
v___x_2795_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2794_;
}
v_reusejp_2794_:
{
return v___x_2795_;
}
}
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2806_; 
lean_del_object(v___x_2748_);
lean_dec(v_a_2726_);
lean_dec(v_a_2724_);
lean_dec_ref(v_struct_2691_);
lean_dec(v_idx_2690_);
lean_dec(v_structName_2689_);
lean_dec_ref(v_e_2688_);
v_a_2799_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2806_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2806_ == 0)
{
v___x_2801_ = v___x_2768_;
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2768_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2806_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2804_; 
if (v_isShared_2802_ == 0)
{
v___x_2804_ = v___x_2801_;
goto v_reusejp_2803_;
}
else
{
lean_object* v_reuseFailAlloc_2805_; 
v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
v___x_2804_ = v_reuseFailAlloc_2805_;
goto v_reusejp_2803_;
}
v_reusejp_2803_:
{
return v___x_2804_;
}
}
}
}
v___jp_2807_:
{
lean_object* v_dummy_2814_; lean_object* v_nargs_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint8_t v___x_2822_; 
v_dummy_2814_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2815_ = l_Lean_Expr_getAppNumArgs(v_a_2724_);
lean_inc(v_nargs_2815_);
v___x_2816_ = lean_mk_array(v_nargs_2815_, v_dummy_2814_);
v___x_2817_ = lean_unsigned_to_nat(1u);
v___x_2818_ = lean_nat_sub(v_nargs_2815_, v___x_2817_);
lean_dec(v_nargs_2815_);
lean_inc(v_a_2724_);
v___x_2819_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2724_, v___x_2816_, v___x_2818_);
v___x_2820_ = lean_nat_add(v_numParams_2744_, v_numIndices_2745_);
lean_dec(v_numIndices_2745_);
v___x_2821_ = lean_array_get_size(v___x_2819_);
v___x_2822_ = lean_nat_dec_eq(v___x_2820_, v___x_2821_);
lean_dec(v___x_2820_);
if (v___x_2822_ == 0)
{
if (v___x_2710_ == 0)
{
v___y_2754_ = v___x_2819_;
v___y_2755_ = v___y_2808_;
v___y_2756_ = v___y_2809_;
v___y_2757_ = v___y_2810_;
v___y_2758_ = v___y_2811_;
v___y_2759_ = v___y_2812_;
v___y_2760_ = v___y_2813_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v_a_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
lean_dec_ref(v___x_2819_);
lean_dec_ref(v_val_2752_);
lean_del_object(v___x_2748_);
lean_dec(v_numParams_2744_);
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
v___x_2823_ = lean_box(0);
v___x_2824_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2691_, v_structName_2689_, v_idx_2690_, v_a_2724_, lean_box(0), v___x_2823_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2827_ = v___x_2824_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_inc(v_a_2825_);
lean_dec(v___x_2824_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2825_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
}
else
{
v___y_2754_ = v___x_2819_;
v___y_2755_ = v___y_2808_;
v___y_2756_ = v___y_2809_;
v___y_2757_ = v___y_2810_;
v___y_2758_ = v___y_2811_;
v___y_2759_ = v___y_2812_;
v___y_2760_ = v___y_2813_;
goto v___jp_2753_;
}
}
}
else
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
lean_dec(v_a_2751_);
lean_del_object(v___x_2748_);
lean_dec(v_numIndices_2745_);
lean_dec(v_numParams_2744_);
lean_dec_ref(v_toConstantVal_2743_);
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
v___x_2845_ = lean_box(0);
v___x_2846_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2691_, v_structName_2689_, v_idx_2690_, v_a_2724_, lean_box(0), v___x_2845_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2846_;
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_del_object(v___x_2748_);
lean_dec(v_numIndices_2745_);
lean_dec(v_numParams_2744_);
lean_dec_ref(v_toConstantVal_2743_);
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec(v_a_2724_);
lean_dec_ref(v_struct_2691_);
lean_dec(v_idx_2690_);
lean_dec(v_structName_2689_);
lean_dec_ref(v_e_2688_);
v_a_2847_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2750_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2750_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2741_, 2);
lean_dec_ref(v_val_2740_);
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
goto v___jp_2731_;
}
}
else
{
lean_dec(v_ctors_2741_);
lean_dec_ref(v_val_2740_);
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
goto v___jp_2731_;
}
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
lean_dec(v_val_2739_);
lean_dec(v_us_2729_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
v___x_2857_ = lean_box(0);
v___x_2858_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2691_, v_structName_2689_, v_idx_2690_, v_a_2724_, lean_box(0), v___x_2857_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2858_;
}
}
v___jp_2731_:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2732_ = lean_box(0);
v___x_2733_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2691_, v_structName_2689_, v_idx_2690_, v_a_2724_, lean_box(0), v___x_2732_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2733_;
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
lean_dec_ref(v___x_2727_);
lean_dec(v_a_2726_);
lean_dec_ref(v_e_2688_);
v___x_2859_ = lean_box(0);
v___x_2860_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2691_, v_structName_2689_, v_idx_2690_, v_a_2724_, lean_box(0), v___x_2859_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
return v___x_2860_;
}
}
else
{
lean_object* v_a_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2868_; 
lean_dec(v_a_2724_);
lean_dec_ref(v_struct_2691_);
lean_dec(v_idx_2690_);
lean_dec(v_structName_2689_);
lean_dec_ref(v_e_2688_);
v_a_2861_ = lean_ctor_get(v___x_2725_, 0);
v_isSharedCheck_2868_ = !lean_is_exclusive(v___x_2725_);
if (v_isSharedCheck_2868_ == 0)
{
v___x_2863_ = v___x_2725_;
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_a_2861_);
lean_dec(v___x_2725_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2868_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2866_; 
if (v_isShared_2864_ == 0)
{
v___x_2866_ = v___x_2863_;
goto v_reusejp_2865_;
}
else
{
lean_object* v_reuseFailAlloc_2867_; 
v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
v___x_2866_ = v_reuseFailAlloc_2867_;
goto v_reusejp_2865_;
}
v_reusejp_2865_:
{
return v___x_2866_;
}
}
}
}
else
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2876_; 
lean_dec_ref(v_struct_2691_);
lean_dec(v_idx_2690_);
lean_dec(v_structName_2689_);
lean_dec_ref(v_e_2688_);
v_a_2869_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2876_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2876_ == 0)
{
v___x_2871_ = v___x_2723_;
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2723_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2876_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v___x_2874_; 
if (v_isShared_2872_ == 0)
{
v___x_2874_ = v___x_2871_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_a_2869_);
v___x_2874_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
return v___x_2874_;
}
}
}
}
else
{
lean_object* v_a_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2884_; 
lean_dec_ref(v_struct_2691_);
lean_dec(v_idx_2690_);
lean_dec(v_structName_2689_);
lean_dec_ref(v_e_2688_);
v_a_2877_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2879_ = v___x_2721_;
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_a_2877_);
lean_dec(v___x_2721_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2884_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
lean_object* v___x_2882_; 
if (v_isShared_2880_ == 0)
{
v___x_2882_ = v___x_2879_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_a_2877_);
v___x_2882_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
return v___x_2882_;
}
}
}
}
v___jp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2702_, 0, v___y_2700_);
v___x_2703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2703_, 0, v___y_2701_);
lean_ctor_set(v___x_2703_, 1, v___x_2702_);
v___x_2704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
return v___x_2704_;
}
v___jp_2705_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_box(0);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___y_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2885_, lean_object* v_structName_2886_, lean_object* v_idx_2887_, lean_object* v_struct_2888_, lean_object* v_a_2889_, lean_object* v_a_2890_, lean_object* v_a_2891_, lean_object* v_a_2892_, lean_object* v_a_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_){
_start:
{
lean_object* v_res_2896_; 
v_res_2896_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2885_, v_structName_2886_, v_idx_2887_, v_struct_2888_, v_a_2889_, v_a_2890_, v_a_2891_, v_a_2892_, v_a_2893_, v_a_2894_);
lean_dec(v_a_2894_);
lean_dec_ref(v_a_2893_);
lean_dec(v_a_2892_);
lean_dec_ref(v_a_2891_);
lean_dec(v_a_2890_);
lean_dec(v_a_2889_);
return v_res_2896_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2897_, lean_object* v_struct_2898_, lean_object* v_structName_2899_, uint8_t v_a_2900_, lean_object* v_idx_2901_, lean_object* v_a_2902_, lean_object* v_inst_2903_, lean_object* v_R_2904_, lean_object* v_a_2905_, lean_object* v_b_2906_, lean_object* v_c_2907_, lean_object* v___y_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_){
_start:
{
lean_object* v___x_2915_; 
v___x_2915_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2897_, v_struct_2898_, v_structName_2899_, v_a_2900_, v_idx_2901_, v_a_2902_, v_a_2905_, v_b_2906_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2916_ = _args[0];
lean_object* v_struct_2917_ = _args[1];
lean_object* v_structName_2918_ = _args[2];
lean_object* v_a_2919_ = _args[3];
lean_object* v_idx_2920_ = _args[4];
lean_object* v_a_2921_ = _args[5];
lean_object* v_inst_2922_ = _args[6];
lean_object* v_R_2923_ = _args[7];
lean_object* v_a_2924_ = _args[8];
lean_object* v_b_2925_ = _args[9];
lean_object* v_c_2926_ = _args[10];
lean_object* v___y_2927_ = _args[11];
lean_object* v___y_2928_ = _args[12];
lean_object* v___y_2929_ = _args[13];
lean_object* v___y_2930_ = _args[14];
lean_object* v___y_2931_ = _args[15];
lean_object* v___y_2932_ = _args[16];
lean_object* v___y_2933_ = _args[17];
_start:
{
uint8_t v_a_19705__boxed_2934_; lean_object* v_res_2935_; 
v_a_19705__boxed_2934_ = lean_unbox(v_a_2919_);
v_res_2935_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2916_, v_struct_2917_, v_structName_2918_, v_a_19705__boxed_2934_, v_idx_2920_, v_a_2921_, v_inst_2922_, v_R_2923_, v_a_2924_, v_b_2925_, v_c_2926_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
lean_dec(v___y_2932_);
lean_dec_ref(v___y_2931_);
lean_dec(v___y_2930_);
lean_dec_ref(v___y_2929_);
lean_dec(v___y_2928_);
lean_dec(v___y_2927_);
lean_dec(v_upperBound_2916_);
return v_res_2935_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2936_, size_t v_i_2937_, size_t v_stop_2938_, lean_object* v_b_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_, lean_object* v___y_2943_, lean_object* v___y_2944_){
_start:
{
uint8_t v___x_2946_; 
v___x_2946_ = lean_usize_dec_eq(v_i_2937_, v_stop_2938_);
if (v___x_2946_ == 0)
{
size_t v___x_2947_; size_t v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2947_ = ((size_t)1ULL);
v___x_2948_ = lean_usize_sub(v_i_2937_, v___x_2947_);
v___x_2949_ = lean_array_uget_borrowed(v_as_2936_, v___x_2948_);
lean_inc(v___x_2949_);
v___x_2950_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2949_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_, v___y_2944_);
if (lean_obj_tag(v___x_2950_) == 0)
{
lean_object* v_a_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; 
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
lean_inc(v_a_2951_);
lean_dec_ref_known(v___x_2950_, 1);
v___x_2952_ = l_Lean_Expr_sortLevel_x21(v_a_2951_);
lean_dec(v_a_2951_);
v___x_2953_ = l_Lean_mkLevelIMax_x27(v___x_2952_, v_b_2939_);
v_i_2937_ = v___x_2948_;
v_b_2939_ = v___x_2953_;
goto _start;
}
else
{
lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec(v_b_2939_);
v_a_2955_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2950_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2950_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
}
else
{
lean_object* v___x_2963_; 
v___x_2963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2963_, 0, v_b_2939_);
return v___x_2963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_2964_, lean_object* v_i_2965_, lean_object* v_stop_2966_, lean_object* v_b_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_, lean_object* v___y_2973_){
_start:
{
size_t v_i_boxed_2974_; size_t v_stop_boxed_2975_; lean_object* v_res_2976_; 
v_i_boxed_2974_ = lean_unbox_usize(v_i_2965_);
lean_dec(v_i_2965_);
v_stop_boxed_2975_ = lean_unbox_usize(v_stop_2966_);
lean_dec(v_stop_2966_);
v_res_2976_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_2964_, v_i_boxed_2974_, v_stop_boxed_2975_, v_b_2967_, v___y_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_);
lean_dec(v___y_2972_);
lean_dec_ref(v___y_2971_);
lean_dec(v___y_2970_);
lean_dec_ref(v___y_2969_);
lean_dec(v___y_2968_);
lean_dec_ref(v_as_2964_);
return v_res_2976_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v___x_2985_; 
v___x_2980_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_2981_ = lean_unsigned_to_nat(14u);
v___x_2982_ = lean_unsigned_to_nat(22u);
v___x_2983_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_2984_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_2985_ = l_mkPanicMessageWithDecl(v___x_2984_, v___x_2983_, v___x_2982_, v___x_2981_, v___x_2980_);
return v___x_2985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_2986_, lean_object* v_doms_2987_, lean_object* v_body_2988_, lean_object* v_a_2989_, lean_object* v_a_2990_, lean_object* v_a_2991_, lean_object* v_a_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_){
_start:
{
lean_object* v_lctx_2996_; lean_object* v_expr_2997_; uint8_t v___x_2998_; uint8_t v___x_2999_; lean_object* v___x_3000_; lean_object* v_a_3002_; uint8_t v___x_3007_; 
v_lctx_2996_ = lean_ctor_get(v_a_2991_, 2);
v_expr_2997_ = lean_ctor_get(v_body_2988_, 0);
v___x_2998_ = 1;
v___x_2999_ = 0;
lean_inc_ref(v_lctx_2996_);
v___x_3000_ = l_Lean_LocalContext_mkForall(v_lctx_2996_, v_fvars_2986_, v_expr_2997_, v___x_2998_, v___x_2999_);
v___x_3007_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2989_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3016_; 
v_isSharedCheck_3016_ = !lean_is_exclusive(v_body_2988_);
if (v_isSharedCheck_3016_ == 0)
{
lean_object* v_unused_3017_; lean_object* v_unused_3018_; 
v_unused_3017_ = lean_ctor_get(v_body_2988_, 1);
lean_dec(v_unused_3017_);
v_unused_3018_ = lean_ctor_get(v_body_2988_, 0);
lean_dec(v_unused_3018_);
v___x_3009_ = v_body_2988_;
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
else
{
lean_dec(v_body_2988_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3016_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3011_; lean_object* v___x_3013_; 
v___x_3011_ = lean_box(0);
if (v_isShared_3010_ == 0)
{
lean_ctor_set(v___x_3009_, 1, v___x_3011_);
lean_ctor_set(v___x_3009_, 0, v___x_3000_);
v___x_3013_ = v___x_3009_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v___x_3000_);
lean_ctor_set(v_reuseFailAlloc_3015_, 1, v___x_3011_);
v___x_3013_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3013_);
return v___x_3014_;
}
}
}
else
{
lean_object* v___x_3019_; 
v___x_3019_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_2988_, v_a_2989_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___y_3022_; lean_object* v_type_x3f_3039_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v_type_x3f_3039_ = lean_ctor_get(v_a_3020_, 1);
lean_inc(v_type_x3f_3039_);
lean_dec(v_a_3020_);
if (lean_obj_tag(v_type_x3f_3039_) == 0)
{
lean_object* v___x_3040_; lean_object* v___x_3041_; 
v___x_3040_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3041_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3040_);
v___y_3022_ = v___x_3041_;
goto v___jp_3021_;
}
else
{
lean_object* v_val_3042_; 
v_val_3042_ = lean_ctor_get(v_type_x3f_3039_, 0);
lean_inc(v_val_3042_);
lean_dec_ref_known(v_type_x3f_3039_, 1);
v___y_3022_ = v_val_3042_;
goto v___jp_3021_;
}
v___jp_3021_:
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3023_ = l_Lean_Expr_sortLevel_x21(v___y_3022_);
lean_dec_ref(v___y_3022_);
v___x_3024_ = lean_array_get_size(v_doms_2987_);
v___x_3025_ = lean_unsigned_to_nat(0u);
v___x_3026_ = lean_nat_dec_lt(v___x_3025_, v___x_3024_);
if (v___x_3026_ == 0)
{
v_a_3002_ = v___x_3023_;
goto v___jp_3001_;
}
else
{
size_t v___x_3027_; size_t v___x_3028_; lean_object* v___x_3029_; 
v___x_3027_ = lean_usize_of_nat(v___x_3024_);
v___x_3028_ = ((size_t)0ULL);
v___x_3029_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_2987_, v___x_3027_, v___x_3028_, v___x_3023_, v_a_2990_, v_a_2991_, v_a_2992_, v_a_2993_, v_a_2994_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v_a_3002_ = v_a_3030_;
goto v___jp_3001_;
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v___x_3000_);
v_a_3031_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3029_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3029_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3000_);
return v___x_3019_;
}
}
v___jp_3001_:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3003_ = l_Lean_Expr_sort___override(v_a_3002_);
v___x_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3004_, 0, v___x_3003_);
v___x_3005_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3005_, 0, v___x_3000_);
lean_ctor_set(v___x_3005_, 1, v___x_3004_);
v___x_3006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3006_, 0, v___x_3005_);
return v___x_3006_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3043_, lean_object* v_doms_3044_, lean_object* v_body_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_, lean_object* v_a_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_){
_start:
{
lean_object* v_res_3053_; 
v_res_3053_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3043_, v_doms_3044_, v_body_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_);
lean_dec(v_a_3051_);
lean_dec_ref(v_a_3050_);
lean_dec(v_a_3049_);
lean_dec_ref(v_a_3048_);
lean_dec(v_a_3047_);
lean_dec(v_a_3046_);
lean_dec_ref(v_doms_3044_);
lean_dec_ref(v_fvars_3043_);
return v_res_3053_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3054_, size_t v_i_3055_, size_t v_stop_3056_, lean_object* v_b_3057_, lean_object* v___y_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v___x_3065_; 
v___x_3065_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3054_, v_i_3055_, v_stop_3056_, v_b_3057_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_);
return v___x_3065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3066_, lean_object* v_i_3067_, lean_object* v_stop_3068_, lean_object* v_b_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_){
_start:
{
size_t v_i_boxed_3077_; size_t v_stop_boxed_3078_; lean_object* v_res_3079_; 
v_i_boxed_3077_ = lean_unbox_usize(v_i_3067_);
lean_dec(v_i_3067_);
v_stop_boxed_3078_ = lean_unbox_usize(v_stop_3068_);
lean_dec(v_stop_3068_);
v_res_3079_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3066_, v_i_boxed_3077_, v_stop_boxed_3078_, v_b_3069_, v___y_3070_, v___y_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v___y_3073_);
lean_dec_ref(v___y_3072_);
lean_dec(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v_as_3066_);
return v_res_3079_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3080_, lean_object* v_opt_3081_){
_start:
{
lean_object* v_name_3082_; lean_object* v_defValue_3083_; lean_object* v_map_3084_; lean_object* v___x_3085_; 
v_name_3082_ = lean_ctor_get(v_opt_3081_, 0);
v_defValue_3083_ = lean_ctor_get(v_opt_3081_, 1);
v_map_3084_ = lean_ctor_get(v_opts_3080_, 0);
v___x_3085_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3084_, v_name_3082_);
if (lean_obj_tag(v___x_3085_) == 0)
{
uint8_t v___x_3086_; 
v___x_3086_ = lean_unbox(v_defValue_3083_);
return v___x_3086_;
}
else
{
lean_object* v_val_3087_; 
v_val_3087_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_val_3087_);
lean_dec_ref_known(v___x_3085_, 1);
if (lean_obj_tag(v_val_3087_) == 1)
{
uint8_t v_v_3088_; 
v_v_3088_ = lean_ctor_get_uint8(v_val_3087_, 0);
lean_dec_ref_known(v_val_3087_, 0);
return v_v_3088_;
}
else
{
uint8_t v___x_3089_; 
lean_dec(v_val_3087_);
v___x_3089_ = lean_unbox(v_defValue_3083_);
return v___x_3089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3090_, lean_object* v_opt_3091_){
_start:
{
uint8_t v_res_3092_; lean_object* v_r_3093_; 
v_res_3092_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3090_, v_opt_3091_);
lean_dec_ref(v_opt_3091_);
lean_dec_ref(v_opts_3090_);
v_r_3093_ = lean_box(v_res_3092_);
return v_r_3093_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3094_){
_start:
{
if (lean_obj_tag(v_x_3094_) == 0)
{
lean_object* v_a_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3103_; 
v_a_3096_ = lean_ctor_get(v_x_3094_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_x_3094_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3098_ = v_x_3094_;
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_a_3096_);
lean_dec(v_x_3094_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3103_;
goto v_resetjp_3097_;
}
v_resetjp_3097_:
{
lean_object* v___x_3101_; 
if (v_isShared_3099_ == 0)
{
lean_ctor_set_tag(v___x_3098_, 1);
v___x_3101_ = v___x_3098_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v_a_3096_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
v_a_3104_ = lean_ctor_get(v_x_3094_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v_x_3094_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v_x_3094_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v_x_3094_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 0);
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(0, 1, 0);
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
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v_res_3114_; 
v_res_3114_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3112_);
return v_res_3114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3115_){
_start:
{
if (lean_obj_tag(v_e_3115_) == 0)
{
uint8_t v___x_3116_; 
v___x_3116_ = 2;
return v___x_3116_;
}
else
{
uint8_t v___x_3117_; 
v___x_3117_ = 0;
return v___x_3117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3118_){
_start:
{
uint8_t v_res_3119_; lean_object* v_r_3120_; 
v_res_3119_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3118_);
lean_dec_ref(v_e_3118_);
v_r_3120_ = lean_box(v_res_3119_);
return v_r_3120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3121_, lean_object* v_opt_3122_){
_start:
{
lean_object* v_name_3123_; lean_object* v_defValue_3124_; lean_object* v_map_3125_; lean_object* v___x_3126_; 
v_name_3123_ = lean_ctor_get(v_opt_3122_, 0);
v_defValue_3124_ = lean_ctor_get(v_opt_3122_, 1);
v_map_3125_ = lean_ctor_get(v_opts_3121_, 0);
v___x_3126_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3125_, v_name_3123_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_inc(v_defValue_3124_);
return v_defValue_3124_;
}
else
{
lean_object* v_val_3127_; 
v_val_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_val_3127_);
lean_dec_ref_known(v___x_3126_, 1);
if (lean_obj_tag(v_val_3127_) == 3)
{
lean_object* v_v_3128_; 
v_v_3128_ = lean_ctor_get(v_val_3127_, 0);
lean_inc(v_v_3128_);
lean_dec_ref_known(v_val_3127_, 1);
return v_v_3128_;
}
else
{
lean_dec(v_val_3127_);
lean_inc(v_defValue_3124_);
return v_defValue_3124_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3129_, lean_object* v_opt_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3129_, v_opt_3130_);
lean_dec_ref(v_opt_3130_);
lean_dec_ref(v_opts_3129_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3132_, size_t v_i_3133_, lean_object* v_bs_3134_){
_start:
{
uint8_t v___x_3135_; 
v___x_3135_ = lean_usize_dec_lt(v_i_3133_, v_sz_3132_);
if (v___x_3135_ == 0)
{
return v_bs_3134_;
}
else
{
lean_object* v_v_3136_; lean_object* v_msg_3137_; lean_object* v___x_3138_; lean_object* v_bs_x27_3139_; size_t v___x_3140_; size_t v___x_3141_; lean_object* v___x_3142_; 
v_v_3136_ = lean_array_uget_borrowed(v_bs_3134_, v_i_3133_);
v_msg_3137_ = lean_ctor_get(v_v_3136_, 1);
lean_inc_ref(v_msg_3137_);
v___x_3138_ = lean_unsigned_to_nat(0u);
v_bs_x27_3139_ = lean_array_uset(v_bs_3134_, v_i_3133_, v___x_3138_);
v___x_3140_ = ((size_t)1ULL);
v___x_3141_ = lean_usize_add(v_i_3133_, v___x_3140_);
v___x_3142_ = lean_array_uset(v_bs_x27_3139_, v_i_3133_, v_msg_3137_);
v_i_3133_ = v___x_3141_;
v_bs_3134_ = v___x_3142_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3144_, lean_object* v_i_3145_, lean_object* v_bs_3146_){
_start:
{
size_t v_sz_boxed_3147_; size_t v_i_boxed_3148_; lean_object* v_res_3149_; 
v_sz_boxed_3147_ = lean_unbox_usize(v_sz_3144_);
lean_dec(v_sz_3144_);
v_i_boxed_3148_ = lean_unbox_usize(v_i_3145_);
lean_dec(v_i_3145_);
v_res_3149_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3147_, v_i_boxed_3148_, v_bs_3146_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3150_, lean_object* v_data_3151_, lean_object* v_ref_3152_, lean_object* v_msg_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_){
_start:
{
lean_object* v_toCold_3159_; lean_object* v_currRecDepth_3160_; lean_object* v_ref_3161_; uint8_t v_diag_3162_; uint8_t v_suppressElabErrors_3163_; lean_object* v___x_3164_; lean_object* v_traceState_3165_; lean_object* v_traces_3166_; lean_object* v_ref_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; size_t v_sz_3170_; size_t v___x_3171_; lean_object* v___x_3172_; lean_object* v_msg_3173_; lean_object* v___x_3174_; lean_object* v_a_3175_; lean_object* v___x_3177_; uint8_t v_isShared_3178_; uint8_t v_isSharedCheck_3212_; 
v_toCold_3159_ = lean_ctor_get(v___y_3156_, 0);
v_currRecDepth_3160_ = lean_ctor_get(v___y_3156_, 1);
v_ref_3161_ = lean_ctor_get(v___y_3156_, 2);
v_diag_3162_ = lean_ctor_get_uint8(v___y_3156_, sizeof(void*)*3);
v_suppressElabErrors_3163_ = lean_ctor_get_uint8(v___y_3156_, sizeof(void*)*3 + 1);
v___x_3164_ = lean_st_ref_get(v___y_3157_);
v_traceState_3165_ = lean_ctor_get(v___x_3164_, 4);
lean_inc_ref(v_traceState_3165_);
lean_dec(v___x_3164_);
v_traces_3166_ = lean_ctor_get(v_traceState_3165_, 0);
lean_inc_ref(v_traces_3166_);
lean_dec_ref(v_traceState_3165_);
v_ref_3167_ = l_Lean_replaceRef(v_ref_3152_, v_ref_3161_);
lean_inc(v_currRecDepth_3160_);
lean_inc_ref(v_toCold_3159_);
v___x_3168_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_3168_, 0, v_toCold_3159_);
lean_ctor_set(v___x_3168_, 1, v_currRecDepth_3160_);
lean_ctor_set(v___x_3168_, 2, v_ref_3167_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*3, v_diag_3162_);
lean_ctor_set_uint8(v___x_3168_, sizeof(void*)*3 + 1, v_suppressElabErrors_3163_);
v___x_3169_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3166_);
lean_dec_ref(v_traces_3166_);
v_sz_3170_ = lean_array_size(v___x_3169_);
v___x_3171_ = ((size_t)0ULL);
v___x_3172_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3170_, v___x_3171_, v___x_3169_);
v_msg_3173_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3173_, 0, v_data_3151_);
lean_ctor_set(v_msg_3173_, 1, v_msg_3153_);
lean_ctor_set(v_msg_3173_, 2, v___x_3172_);
v___x_3174_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3173_, v___y_3154_, v___y_3155_, v___x_3168_, v___y_3157_);
lean_dec_ref_known(v___x_3168_, 3);
v_a_3175_ = lean_ctor_get(v___x_3174_, 0);
v_isSharedCheck_3212_ = !lean_is_exclusive(v___x_3174_);
if (v_isSharedCheck_3212_ == 0)
{
v___x_3177_ = v___x_3174_;
v_isShared_3178_ = v_isSharedCheck_3212_;
goto v_resetjp_3176_;
}
else
{
lean_inc(v_a_3175_);
lean_dec(v___x_3174_);
v___x_3177_ = lean_box(0);
v_isShared_3178_ = v_isSharedCheck_3212_;
goto v_resetjp_3176_;
}
v_resetjp_3176_:
{
lean_object* v___x_3179_; lean_object* v_traceState_3180_; lean_object* v_env_3181_; lean_object* v_nextMacroScope_3182_; lean_object* v_ngen_3183_; lean_object* v_auxDeclNGen_3184_; lean_object* v_cache_3185_; lean_object* v_messages_3186_; lean_object* v_infoState_3187_; lean_object* v_snapshotTasks_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3211_; 
v___x_3179_ = lean_st_ref_take(v___y_3157_);
v_traceState_3180_ = lean_ctor_get(v___x_3179_, 4);
v_env_3181_ = lean_ctor_get(v___x_3179_, 0);
v_nextMacroScope_3182_ = lean_ctor_get(v___x_3179_, 1);
v_ngen_3183_ = lean_ctor_get(v___x_3179_, 2);
v_auxDeclNGen_3184_ = lean_ctor_get(v___x_3179_, 3);
v_cache_3185_ = lean_ctor_get(v___x_3179_, 5);
v_messages_3186_ = lean_ctor_get(v___x_3179_, 6);
v_infoState_3187_ = lean_ctor_get(v___x_3179_, 7);
v_snapshotTasks_3188_ = lean_ctor_get(v___x_3179_, 8);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___x_3179_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3190_ = v___x_3179_;
v_isShared_3191_ = v_isSharedCheck_3211_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_snapshotTasks_3188_);
lean_inc(v_infoState_3187_);
lean_inc(v_messages_3186_);
lean_inc(v_cache_3185_);
lean_inc(v_traceState_3180_);
lean_inc(v_auxDeclNGen_3184_);
lean_inc(v_ngen_3183_);
lean_inc(v_nextMacroScope_3182_);
lean_inc(v_env_3181_);
lean_dec(v___x_3179_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3211_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
uint64_t v_tid_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3209_; 
v_tid_3192_ = lean_ctor_get_uint64(v_traceState_3180_, sizeof(void*)*1);
v_isSharedCheck_3209_ = !lean_is_exclusive(v_traceState_3180_);
if (v_isSharedCheck_3209_ == 0)
{
lean_object* v_unused_3210_; 
v_unused_3210_ = lean_ctor_get(v_traceState_3180_, 0);
lean_dec(v_unused_3210_);
v___x_3194_ = v_traceState_3180_;
v_isShared_3195_ = v_isSharedCheck_3209_;
goto v_resetjp_3193_;
}
else
{
lean_dec(v_traceState_3180_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3209_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3196_; lean_object* v___x_3197_; lean_object* v___x_3199_; 
v___x_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3196_, 0, v_ref_3152_);
lean_ctor_set(v___x_3196_, 1, v_a_3175_);
v___x_3197_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3150_, v___x_3196_);
if (v_isShared_3195_ == 0)
{
lean_ctor_set(v___x_3194_, 0, v___x_3197_);
v___x_3199_ = v___x_3194_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3197_);
lean_ctor_set_uint64(v_reuseFailAlloc_3208_, sizeof(void*)*1, v_tid_3192_);
v___x_3199_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
lean_object* v___x_3201_; 
if (v_isShared_3191_ == 0)
{
lean_ctor_set(v___x_3190_, 4, v___x_3199_);
v___x_3201_ = v___x_3190_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_env_3181_);
lean_ctor_set(v_reuseFailAlloc_3207_, 1, v_nextMacroScope_3182_);
lean_ctor_set(v_reuseFailAlloc_3207_, 2, v_ngen_3183_);
lean_ctor_set(v_reuseFailAlloc_3207_, 3, v_auxDeclNGen_3184_);
lean_ctor_set(v_reuseFailAlloc_3207_, 4, v___x_3199_);
lean_ctor_set(v_reuseFailAlloc_3207_, 5, v_cache_3185_);
lean_ctor_set(v_reuseFailAlloc_3207_, 6, v_messages_3186_);
lean_ctor_set(v_reuseFailAlloc_3207_, 7, v_infoState_3187_);
lean_ctor_set(v_reuseFailAlloc_3207_, 8, v_snapshotTasks_3188_);
v___x_3201_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
lean_object* v___x_3202_; lean_object* v___x_3203_; lean_object* v___x_3205_; 
v___x_3202_ = lean_st_ref_put(v___y_3157_, v___x_3201_);
v___x_3203_ = lean_box(0);
if (v_isShared_3178_ == 0)
{
lean_ctor_set(v___x_3177_, 0, v___x_3203_);
v___x_3205_ = v___x_3177_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3213_, lean_object* v_data_3214_, lean_object* v_ref_3215_, lean_object* v_msg_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_){
_start:
{
lean_object* v_res_3222_; 
v_res_3222_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3213_, v_data_3214_, v_ref_3215_, v_msg_3216_, v___y_3217_, v___y_3218_, v___y_3219_, v___y_3220_);
lean_dec(v___y_3220_);
lean_dec_ref(v___y_3219_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
return v_res_3222_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3226_; double v___x_3227_; 
v___x_3226_ = lean_unsigned_to_nat(1000u);
v___x_3227_ = lean_float_of_nat(v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3228_, uint8_t v_collapsed_3229_, lean_object* v_tag_3230_, lean_object* v_opts_3231_, uint8_t v_clsEnabled_3232_, lean_object* v_oldTraces_3233_, lean_object* v_msg_3234_, lean_object* v_resStartStop_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_, lean_object* v___y_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_){
_start:
{
lean_object* v_fst_3243_; lean_object* v_snd_3244_; lean_object* v___y_3246_; lean_object* v___y_3247_; lean_object* v_data_3248_; lean_object* v_fst_3259_; lean_object* v_snd_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; lean_object* v___y_3264_; lean_object* v_a_3265_; uint8_t v___y_3280_; double v___y_3311_; 
v_fst_3243_ = lean_ctor_get(v_resStartStop_3235_, 0);
lean_inc(v_fst_3243_);
v_snd_3244_ = lean_ctor_get(v_resStartStop_3235_, 1);
lean_inc(v_snd_3244_);
lean_dec_ref(v_resStartStop_3235_);
v_fst_3259_ = lean_ctor_get(v_snd_3244_, 0);
lean_inc(v_fst_3259_);
v_snd_3260_ = lean_ctor_get(v_snd_3244_, 1);
lean_inc(v_snd_3260_);
lean_dec(v_snd_3244_);
v___x_3261_ = l_Lean_trace_profiler;
v___x_3262_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3231_, v___x_3261_);
if (v___x_3262_ == 0)
{
v___y_3280_ = v___x_3262_;
goto v___jp_3279_;
}
else
{
lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3316_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3317_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3231_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; lean_object* v___x_3319_; double v___x_3320_; double v___x_3321_; double v___x_3322_; 
v___x_3318_ = l_Lean_trace_profiler_threshold;
v___x_3319_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3231_, v___x_3318_);
v___x_3320_ = lean_float_of_nat(v___x_3319_);
v___x_3321_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3322_ = lean_float_div(v___x_3320_, v___x_3321_);
v___y_3311_ = v___x_3322_;
goto v___jp_3310_;
}
else
{
lean_object* v___x_3323_; lean_object* v___x_3324_; double v___x_3325_; 
v___x_3323_ = l_Lean_trace_profiler_threshold;
v___x_3324_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3231_, v___x_3323_);
v___x_3325_ = lean_float_of_nat(v___x_3324_);
v___y_3311_ = v___x_3325_;
goto v___jp_3310_;
}
}
v___jp_3245_:
{
lean_object* v___x_3249_; 
lean_inc(v___y_3247_);
v___x_3249_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3233_, v_data_3248_, v___y_3247_, v___y_3246_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v___x_3250_; 
lean_dec_ref_known(v___x_3249_, 1);
v___x_3250_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3243_);
return v___x_3250_;
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_fst_3243_);
v_a_3251_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3249_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
v___jp_3263_:
{
uint8_t v_result_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; double v___x_3269_; lean_object* v_data_3270_; 
v_result_3266_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3243_);
v___x_3267_ = lean_box(v_result_3266_);
v___x_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3268_, 0, v___x_3267_);
v___x_3269_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3230_);
lean_inc_ref(v___x_3268_);
lean_inc(v_cls_3228_);
v_data_3270_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3270_, 0, v_cls_3228_);
lean_ctor_set(v_data_3270_, 1, v___x_3268_);
lean_ctor_set(v_data_3270_, 2, v_tag_3230_);
lean_ctor_set_float(v_data_3270_, sizeof(void*)*3, v___x_3269_);
lean_ctor_set_float(v_data_3270_, sizeof(void*)*3 + 8, v___x_3269_);
lean_ctor_set_uint8(v_data_3270_, sizeof(void*)*3 + 16, v_collapsed_3229_);
if (v___x_3262_ == 0)
{
lean_dec_ref_known(v___x_3268_, 1);
lean_dec(v_snd_3260_);
lean_dec(v_fst_3259_);
lean_dec_ref(v_tag_3230_);
lean_dec(v_cls_3228_);
v___y_3246_ = v_a_3265_;
v___y_3247_ = v___y_3264_;
v_data_3248_ = v_data_3270_;
goto v___jp_3245_;
}
else
{
lean_object* v_data_3271_; double v___x_3272_; double v___x_3273_; 
lean_dec_ref_known(v_data_3270_, 3);
v_data_3271_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3271_, 0, v_cls_3228_);
lean_ctor_set(v_data_3271_, 1, v___x_3268_);
lean_ctor_set(v_data_3271_, 2, v_tag_3230_);
v___x_3272_ = lean_unbox_float(v_fst_3259_);
lean_dec(v_fst_3259_);
lean_ctor_set_float(v_data_3271_, sizeof(void*)*3, v___x_3272_);
v___x_3273_ = lean_unbox_float(v_snd_3260_);
lean_dec(v_snd_3260_);
lean_ctor_set_float(v_data_3271_, sizeof(void*)*3 + 8, v___x_3273_);
lean_ctor_set_uint8(v_data_3271_, sizeof(void*)*3 + 16, v_collapsed_3229_);
v___y_3246_ = v_a_3265_;
v___y_3247_ = v___y_3264_;
v_data_3248_ = v_data_3271_;
goto v___jp_3245_;
}
}
v___jp_3274_:
{
lean_object* v_ref_3275_; lean_object* v___x_3276_; 
v_ref_3275_ = lean_ctor_get(v___y_3240_, 2);
lean_inc(v___y_3241_);
lean_inc_ref(v___y_3240_);
lean_inc(v___y_3239_);
lean_inc_ref(v___y_3238_);
lean_inc(v___y_3237_);
lean_inc(v___y_3236_);
lean_inc(v_fst_3243_);
v___x_3276_ = lean_apply_8(v_msg_3234_, v_fst_3243_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_, v___y_3240_, v___y_3241_, lean_box(0));
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___y_3264_ = v_ref_3275_;
v_a_3265_ = v_a_3277_;
goto v___jp_3263_;
}
else
{
lean_object* v___x_3278_; 
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3264_ = v_ref_3275_;
v_a_3265_ = v___x_3278_;
goto v___jp_3263_;
}
}
v___jp_3279_:
{
if (v_clsEnabled_3232_ == 0)
{
if (v___y_3280_ == 0)
{
lean_object* v___x_3281_; lean_object* v_traceState_3282_; lean_object* v_env_3283_; lean_object* v_nextMacroScope_3284_; lean_object* v_ngen_3285_; lean_object* v_auxDeclNGen_3286_; lean_object* v_cache_3287_; lean_object* v_messages_3288_; lean_object* v_infoState_3289_; lean_object* v_snapshotTasks_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3309_; 
lean_dec(v_snd_3260_);
lean_dec(v_fst_3259_);
lean_dec_ref(v_msg_3234_);
lean_dec_ref(v_tag_3230_);
lean_dec(v_cls_3228_);
v___x_3281_ = lean_st_ref_take(v___y_3241_);
v_traceState_3282_ = lean_ctor_get(v___x_3281_, 4);
v_env_3283_ = lean_ctor_get(v___x_3281_, 0);
v_nextMacroScope_3284_ = lean_ctor_get(v___x_3281_, 1);
v_ngen_3285_ = lean_ctor_get(v___x_3281_, 2);
v_auxDeclNGen_3286_ = lean_ctor_get(v___x_3281_, 3);
v_cache_3287_ = lean_ctor_get(v___x_3281_, 5);
v_messages_3288_ = lean_ctor_get(v___x_3281_, 6);
v_infoState_3289_ = lean_ctor_get(v___x_3281_, 7);
v_snapshotTasks_3290_ = lean_ctor_get(v___x_3281_, 8);
v_isSharedCheck_3309_ = !lean_is_exclusive(v___x_3281_);
if (v_isSharedCheck_3309_ == 0)
{
v___x_3292_ = v___x_3281_;
v_isShared_3293_ = v_isSharedCheck_3309_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_snapshotTasks_3290_);
lean_inc(v_infoState_3289_);
lean_inc(v_messages_3288_);
lean_inc(v_cache_3287_);
lean_inc(v_traceState_3282_);
lean_inc(v_auxDeclNGen_3286_);
lean_inc(v_ngen_3285_);
lean_inc(v_nextMacroScope_3284_);
lean_inc(v_env_3283_);
lean_dec(v___x_3281_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3309_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
uint64_t v_tid_3294_; lean_object* v_traces_3295_; lean_object* v___x_3297_; uint8_t v_isShared_3298_; uint8_t v_isSharedCheck_3308_; 
v_tid_3294_ = lean_ctor_get_uint64(v_traceState_3282_, sizeof(void*)*1);
v_traces_3295_ = lean_ctor_get(v_traceState_3282_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v_traceState_3282_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3297_ = v_traceState_3282_;
v_isShared_3298_ = v_isSharedCheck_3308_;
goto v_resetjp_3296_;
}
else
{
lean_inc(v_traces_3295_);
lean_dec(v_traceState_3282_);
v___x_3297_ = lean_box(0);
v_isShared_3298_ = v_isSharedCheck_3308_;
goto v_resetjp_3296_;
}
v_resetjp_3296_:
{
lean_object* v___x_3299_; lean_object* v___x_3301_; 
v___x_3299_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3233_, v_traces_3295_);
lean_dec_ref(v_traces_3295_);
if (v_isShared_3298_ == 0)
{
lean_ctor_set(v___x_3297_, 0, v___x_3299_);
v___x_3301_ = v___x_3297_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3299_);
lean_ctor_set_uint64(v_reuseFailAlloc_3307_, sizeof(void*)*1, v_tid_3294_);
v___x_3301_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
lean_object* v___x_3303_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 4, v___x_3301_);
v___x_3303_ = v___x_3292_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3306_; 
v_reuseFailAlloc_3306_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3306_, 0, v_env_3283_);
lean_ctor_set(v_reuseFailAlloc_3306_, 1, v_nextMacroScope_3284_);
lean_ctor_set(v_reuseFailAlloc_3306_, 2, v_ngen_3285_);
lean_ctor_set(v_reuseFailAlloc_3306_, 3, v_auxDeclNGen_3286_);
lean_ctor_set(v_reuseFailAlloc_3306_, 4, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3306_, 5, v_cache_3287_);
lean_ctor_set(v_reuseFailAlloc_3306_, 6, v_messages_3288_);
lean_ctor_set(v_reuseFailAlloc_3306_, 7, v_infoState_3289_);
lean_ctor_set(v_reuseFailAlloc_3306_, 8, v_snapshotTasks_3290_);
v___x_3303_ = v_reuseFailAlloc_3306_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3304_ = lean_st_ref_put(v___y_3241_, v___x_3303_);
v___x_3305_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3243_);
return v___x_3305_;
}
}
}
}
}
else
{
goto v___jp_3274_;
}
}
else
{
goto v___jp_3274_;
}
}
v___jp_3310_:
{
double v___x_3312_; double v___x_3313_; double v___x_3314_; uint8_t v___x_3315_; 
v___x_3312_ = lean_unbox_float(v_snd_3260_);
v___x_3313_ = lean_unbox_float(v_fst_3259_);
v___x_3314_ = lean_float_sub(v___x_3312_, v___x_3313_);
v___x_3315_ = lean_float_decLt(v___y_3311_, v___x_3314_);
v___y_3280_ = v___x_3315_;
goto v___jp_3279_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3326_, lean_object* v_collapsed_3327_, lean_object* v_tag_3328_, lean_object* v_opts_3329_, lean_object* v_clsEnabled_3330_, lean_object* v_oldTraces_3331_, lean_object* v_msg_3332_, lean_object* v_resStartStop_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
uint8_t v_collapsed_boxed_3341_; uint8_t v_clsEnabled_boxed_3342_; lean_object* v_res_3343_; 
v_collapsed_boxed_3341_ = lean_unbox(v_collapsed_3327_);
v_clsEnabled_boxed_3342_ = lean_unbox(v_clsEnabled_3330_);
v_res_3343_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3326_, v_collapsed_boxed_3341_, v_tag_3328_, v_opts_3329_, v_clsEnabled_boxed_3342_, v_oldTraces_3331_, v_msg_3332_, v_resStartStop_3333_, v___y_3334_, v___y_3335_, v___y_3336_, v___y_3337_, v___y_3338_, v___y_3339_);
lean_dec(v___y_3339_);
lean_dec_ref(v___y_3338_);
lean_dec(v___y_3337_);
lean_dec_ref(v___y_3336_);
lean_dec(v___y_3335_);
lean_dec(v___y_3334_);
lean_dec_ref(v_opts_3329_);
return v_res_3343_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v___x_3344_ = lean_unsigned_to_nat(32u);
v___x_3345_ = lean_mk_empty_array_with_capacity(v___x_3344_);
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3345_);
return v___x_3346_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v___x_3347_ = ((size_t)5ULL);
v___x_3348_ = lean_unsigned_to_nat(0u);
v___x_3349_ = lean_unsigned_to_nat(32u);
v___x_3350_ = lean_mk_empty_array_with_capacity(v___x_3349_);
v___x_3351_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3352_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3352_, 0, v___x_3351_);
lean_ctor_set(v___x_3352_, 1, v___x_3350_);
lean_ctor_set(v___x_3352_, 2, v___x_3348_);
lean_ctor_set(v___x_3352_, 3, v___x_3348_);
lean_ctor_set_usize(v___x_3352_, 4, v___x_3347_);
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3353_){
_start:
{
lean_object* v___x_3355_; lean_object* v_traceState_3356_; lean_object* v_traces_3357_; lean_object* v___x_3358_; lean_object* v_traceState_3359_; lean_object* v_env_3360_; lean_object* v_nextMacroScope_3361_; lean_object* v_ngen_3362_; lean_object* v_auxDeclNGen_3363_; lean_object* v_cache_3364_; lean_object* v_messages_3365_; lean_object* v_infoState_3366_; lean_object* v_snapshotTasks_3367_; lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3386_; 
v___x_3355_ = lean_st_ref_get(v___y_3353_);
v_traceState_3356_ = lean_ctor_get(v___x_3355_, 4);
lean_inc_ref(v_traceState_3356_);
lean_dec(v___x_3355_);
v_traces_3357_ = lean_ctor_get(v_traceState_3356_, 0);
lean_inc_ref(v_traces_3357_);
lean_dec_ref(v_traceState_3356_);
v___x_3358_ = lean_st_ref_take(v___y_3353_);
v_traceState_3359_ = lean_ctor_get(v___x_3358_, 4);
v_env_3360_ = lean_ctor_get(v___x_3358_, 0);
v_nextMacroScope_3361_ = lean_ctor_get(v___x_3358_, 1);
v_ngen_3362_ = lean_ctor_get(v___x_3358_, 2);
v_auxDeclNGen_3363_ = lean_ctor_get(v___x_3358_, 3);
v_cache_3364_ = lean_ctor_get(v___x_3358_, 5);
v_messages_3365_ = lean_ctor_get(v___x_3358_, 6);
v_infoState_3366_ = lean_ctor_get(v___x_3358_, 7);
v_snapshotTasks_3367_ = lean_ctor_get(v___x_3358_, 8);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3358_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3369_ = v___x_3358_;
v_isShared_3370_ = v_isSharedCheck_3386_;
goto v_resetjp_3368_;
}
else
{
lean_inc(v_snapshotTasks_3367_);
lean_inc(v_infoState_3366_);
lean_inc(v_messages_3365_);
lean_inc(v_cache_3364_);
lean_inc(v_traceState_3359_);
lean_inc(v_auxDeclNGen_3363_);
lean_inc(v_ngen_3362_);
lean_inc(v_nextMacroScope_3361_);
lean_inc(v_env_3360_);
lean_dec(v___x_3358_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3386_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
uint64_t v_tid_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3384_; 
v_tid_3371_ = lean_ctor_get_uint64(v_traceState_3359_, sizeof(void*)*1);
v_isSharedCheck_3384_ = !lean_is_exclusive(v_traceState_3359_);
if (v_isSharedCheck_3384_ == 0)
{
lean_object* v_unused_3385_; 
v_unused_3385_ = lean_ctor_get(v_traceState_3359_, 0);
lean_dec(v_unused_3385_);
v___x_3373_ = v_traceState_3359_;
v_isShared_3374_ = v_isSharedCheck_3384_;
goto v_resetjp_3372_;
}
else
{
lean_dec(v_traceState_3359_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3384_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3375_);
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v___x_3375_);
lean_ctor_set_uint64(v_reuseFailAlloc_3383_, sizeof(void*)*1, v_tid_3371_);
v___x_3377_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
lean_object* v___x_3379_; 
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 4, v___x_3377_);
v___x_3379_ = v___x_3369_;
goto v_reusejp_3378_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_env_3360_);
lean_ctor_set(v_reuseFailAlloc_3382_, 1, v_nextMacroScope_3361_);
lean_ctor_set(v_reuseFailAlloc_3382_, 2, v_ngen_3362_);
lean_ctor_set(v_reuseFailAlloc_3382_, 3, v_auxDeclNGen_3363_);
lean_ctor_set(v_reuseFailAlloc_3382_, 4, v___x_3377_);
lean_ctor_set(v_reuseFailAlloc_3382_, 5, v_cache_3364_);
lean_ctor_set(v_reuseFailAlloc_3382_, 6, v_messages_3365_);
lean_ctor_set(v_reuseFailAlloc_3382_, 7, v_infoState_3366_);
lean_ctor_set(v_reuseFailAlloc_3382_, 8, v_snapshotTasks_3367_);
v___x_3379_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3378_;
}
v_reusejp_3378_:
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
v___x_3380_ = lean_st_ref_put(v___y_3353_, v___x_3379_);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v_traces_3357_);
return v___x_3381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v_res_3389_; 
v_res_3389_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3387_);
lean_dec(v___y_3387_);
return v_res_3389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___x_3398_; 
lean_inc(v___y_3392_);
lean_inc(v___y_3391_);
v___x_3398_ = lean_apply_7(v_x_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_, lean_box(0));
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3401_);
lean_dec(v___y_3400_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3408_, lean_object* v_localInsts_3409_, lean_object* v_x_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v___f_3418_; lean_object* v___x_3419_; 
lean_inc(v___y_3412_);
lean_inc(v___y_3411_);
v___f_3418_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3418_, 0, v_x_3410_);
lean_closure_set(v___f_3418_, 1, v___y_3411_);
lean_closure_set(v___f_3418_, 2, v___y_3412_);
v___x_3419_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3408_, v_localInsts_3409_, v___f_3418_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
if (lean_obj_tag(v___x_3419_) == 0)
{
return v___x_3419_;
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v_a_3420_ = lean_ctor_get(v___x_3419_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3419_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3419_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3419_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3428_, lean_object* v_localInsts_3429_, lean_object* v_x_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_, lean_object* v___y_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3428_, v_localInsts_3429_, v_x_3430_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
lean_dec(v___y_3436_);
lean_dec_ref(v___y_3435_);
lean_dec(v___y_3434_);
lean_dec_ref(v___y_3433_);
lean_dec(v___y_3432_);
lean_dec(v___y_3431_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3439_){
_start:
{
lean_object* v___x_3441_; lean_object* v_ngen_3442_; lean_object* v_namePrefix_3443_; lean_object* v_idx_3444_; lean_object* v___x_3446_; uint8_t v_isShared_3447_; uint8_t v_isSharedCheck_3473_; 
v___x_3441_ = lean_st_ref_get(v___y_3439_);
v_ngen_3442_ = lean_ctor_get(v___x_3441_, 2);
lean_inc_ref(v_ngen_3442_);
lean_dec(v___x_3441_);
v_namePrefix_3443_ = lean_ctor_get(v_ngen_3442_, 0);
v_idx_3444_ = lean_ctor_get(v_ngen_3442_, 1);
v_isSharedCheck_3473_ = !lean_is_exclusive(v_ngen_3442_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3446_ = v_ngen_3442_;
v_isShared_3447_ = v_isSharedCheck_3473_;
goto v_resetjp_3445_;
}
else
{
lean_inc(v_idx_3444_);
lean_inc(v_namePrefix_3443_);
lean_dec(v_ngen_3442_);
v___x_3446_ = lean_box(0);
v_isShared_3447_ = v_isSharedCheck_3473_;
goto v_resetjp_3445_;
}
v_resetjp_3445_:
{
lean_object* v___x_3448_; lean_object* v_env_3449_; lean_object* v_nextMacroScope_3450_; lean_object* v_auxDeclNGen_3451_; lean_object* v_traceState_3452_; lean_object* v_cache_3453_; lean_object* v_messages_3454_; lean_object* v_infoState_3455_; lean_object* v_snapshotTasks_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3471_; 
v___x_3448_ = lean_st_ref_take(v___y_3439_);
v_env_3449_ = lean_ctor_get(v___x_3448_, 0);
v_nextMacroScope_3450_ = lean_ctor_get(v___x_3448_, 1);
v_auxDeclNGen_3451_ = lean_ctor_get(v___x_3448_, 3);
v_traceState_3452_ = lean_ctor_get(v___x_3448_, 4);
v_cache_3453_ = lean_ctor_get(v___x_3448_, 5);
v_messages_3454_ = lean_ctor_get(v___x_3448_, 6);
v_infoState_3455_ = lean_ctor_get(v___x_3448_, 7);
v_snapshotTasks_3456_ = lean_ctor_get(v___x_3448_, 8);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3448_);
if (v_isSharedCheck_3471_ == 0)
{
lean_object* v_unused_3472_; 
v_unused_3472_ = lean_ctor_get(v___x_3448_, 2);
lean_dec(v_unused_3472_);
v___x_3458_ = v___x_3448_;
v_isShared_3459_ = v_isSharedCheck_3471_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_snapshotTasks_3456_);
lean_inc(v_infoState_3455_);
lean_inc(v_messages_3454_);
lean_inc(v_cache_3453_);
lean_inc(v_traceState_3452_);
lean_inc(v_auxDeclNGen_3451_);
lean_inc(v_nextMacroScope_3450_);
lean_inc(v_env_3449_);
lean_dec(v___x_3448_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3471_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_r_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_inc(v_idx_3444_);
lean_inc(v_namePrefix_3443_);
v_r_3460_ = l_Lean_Name_num___override(v_namePrefix_3443_, v_idx_3444_);
v___x_3461_ = lean_unsigned_to_nat(1u);
v___x_3462_ = lean_nat_add(v_idx_3444_, v___x_3461_);
lean_dec(v_idx_3444_);
if (v_isShared_3447_ == 0)
{
lean_ctor_set(v___x_3446_, 1, v___x_3462_);
v___x_3464_ = v___x_3446_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_namePrefix_3443_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3466_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 2, v___x_3464_);
v___x_3466_ = v___x_3458_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_env_3449_);
lean_ctor_set(v_reuseFailAlloc_3469_, 1, v_nextMacroScope_3450_);
lean_ctor_set(v_reuseFailAlloc_3469_, 2, v___x_3464_);
lean_ctor_set(v_reuseFailAlloc_3469_, 3, v_auxDeclNGen_3451_);
lean_ctor_set(v_reuseFailAlloc_3469_, 4, v_traceState_3452_);
lean_ctor_set(v_reuseFailAlloc_3469_, 5, v_cache_3453_);
lean_ctor_set(v_reuseFailAlloc_3469_, 6, v_messages_3454_);
lean_ctor_set(v_reuseFailAlloc_3469_, 7, v_infoState_3455_);
lean_ctor_set(v_reuseFailAlloc_3469_, 8, v_snapshotTasks_3456_);
v___x_3466_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; 
v___x_3467_ = lean_st_ref_put(v___y_3439_, v___x_3466_);
v___x_3468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3468_, 0, v_r_3460_);
return v___x_3468_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
lean_object* v_res_3476_; 
v_res_3476_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3474_);
lean_dec(v___y_3474_);
return v_res_3476_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
lean_object* v___x_3484_; lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
v___x_3484_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3482_);
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3484_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3484_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3484_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3493_, lean_object* v___y_3494_, lean_object* v___y_3495_, lean_object* v___y_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_){
_start:
{
lean_object* v_res_3500_; 
v_res_3500_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3493_, v___y_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
lean_dec(v___y_3496_);
lean_dec_ref(v___y_3495_);
lean_dec(v___y_3494_);
lean_dec(v___y_3493_);
return v_res_3500_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3502_; lean_object* v___x_3503_; 
v___x_3502_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3503_ = l_Lean_stringToMessageData(v___x_3502_);
return v___x_3503_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3505_; lean_object* v___x_3506_; 
v___x_3505_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3506_ = l_Lean_stringToMessageData(v___x_3505_);
return v___x_3506_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3509_, lean_object* v_x_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_, lean_object* v___y_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v___y_3520_; uint8_t v___x_3529_; 
v___x_3518_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3529_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3511_);
if (v___x_3529_ == 0)
{
lean_object* v___x_3530_; 
v___x_3530_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3520_ = v___x_3530_;
goto v___jp_3519_;
}
else
{
lean_object* v___x_3531_; 
v___x_3531_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3520_ = v___x_3531_;
goto v___jp_3519_;
}
v___jp_3519_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
lean_inc_ref(v___y_3520_);
v___x_3521_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___y_3520_);
v___x_3522_ = l_Lean_MessageData_ofFormat(v___x_3521_);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3518_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3525_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3523_);
lean_ctor_set(v___x_3525_, 1, v___x_3524_);
v___x_3526_ = l_Lean_indentExpr(v_e_3509_);
v___x_3527_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
v___x_3528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
return v___x_3528_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3532_, lean_object* v_x_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_){
_start:
{
lean_object* v_res_3541_; 
v_res_3541_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3532_, v_x_3533_, v___y_3534_, v___y_3535_, v___y_3536_, v___y_3537_, v___y_3538_, v___y_3539_);
lean_dec(v___y_3539_);
lean_dec_ref(v___y_3538_);
lean_dec(v___y_3537_);
lean_dec_ref(v___y_3536_);
lean_dec(v___y_3535_);
lean_dec(v___y_3534_);
lean_dec_ref(v_x_3533_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3542_, lean_object* v_x_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_){
_start:
{
lean_object* v_keyedConfig_3551_; uint8_t v_trackZetaDelta_3552_; lean_object* v_zetaDeltaSet_3553_; lean_object* v_localInstances_3554_; lean_object* v_defEqCtx_x3f_3555_; lean_object* v_synthPendingDepth_3556_; lean_object* v_customCanUnfoldPredicate_x3f_3557_; uint8_t v_univApprox_3558_; uint8_t v_inTypeClassResolution_3559_; uint8_t v_cacheInferType_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; 
v_keyedConfig_3551_ = lean_ctor_get(v___y_3546_, 0);
v_trackZetaDelta_3552_ = lean_ctor_get_uint8(v___y_3546_, sizeof(void*)*7);
v_zetaDeltaSet_3553_ = lean_ctor_get(v___y_3546_, 1);
v_localInstances_3554_ = lean_ctor_get(v___y_3546_, 3);
v_defEqCtx_x3f_3555_ = lean_ctor_get(v___y_3546_, 4);
v_synthPendingDepth_3556_ = lean_ctor_get(v___y_3546_, 5);
v_customCanUnfoldPredicate_x3f_3557_ = lean_ctor_get(v___y_3546_, 6);
v_univApprox_3558_ = lean_ctor_get_uint8(v___y_3546_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3559_ = lean_ctor_get_uint8(v___y_3546_, sizeof(void*)*7 + 2);
v_cacheInferType_3560_ = lean_ctor_get_uint8(v___y_3546_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3557_);
lean_inc(v_synthPendingDepth_3556_);
lean_inc(v_defEqCtx_x3f_3555_);
lean_inc_ref(v_localInstances_3554_);
lean_inc(v_zetaDeltaSet_3553_);
lean_inc_ref(v_keyedConfig_3551_);
v___x_3561_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3561_, 0, v_keyedConfig_3551_);
lean_ctor_set(v___x_3561_, 1, v_zetaDeltaSet_3553_);
lean_ctor_set(v___x_3561_, 2, v_lctx_3542_);
lean_ctor_set(v___x_3561_, 3, v_localInstances_3554_);
lean_ctor_set(v___x_3561_, 4, v_defEqCtx_x3f_3555_);
lean_ctor_set(v___x_3561_, 5, v_synthPendingDepth_3556_);
lean_ctor_set(v___x_3561_, 6, v_customCanUnfoldPredicate_x3f_3557_);
lean_ctor_set_uint8(v___x_3561_, sizeof(void*)*7, v_trackZetaDelta_3552_);
lean_ctor_set_uint8(v___x_3561_, sizeof(void*)*7 + 1, v_univApprox_3558_);
lean_ctor_set_uint8(v___x_3561_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3559_);
lean_ctor_set_uint8(v___x_3561_, sizeof(void*)*7 + 3, v_cacheInferType_3560_);
lean_inc(v___y_3549_);
lean_inc_ref(v___y_3548_);
lean_inc(v___y_3547_);
lean_inc(v___y_3545_);
lean_inc(v___y_3544_);
v___x_3562_ = lean_apply_7(v_x_3543_, v___y_3544_, v___y_3545_, v___x_3561_, v___y_3547_, v___y_3548_, v___y_3549_, lean_box(0));
if (lean_obj_tag(v___x_3562_) == 0)
{
lean_object* v_a_3563_; lean_object* v___x_3565_; uint8_t v_isShared_3566_; uint8_t v_isSharedCheck_3570_; 
v_a_3563_ = lean_ctor_get(v___x_3562_, 0);
v_isSharedCheck_3570_ = !lean_is_exclusive(v___x_3562_);
if (v_isSharedCheck_3570_ == 0)
{
v___x_3565_ = v___x_3562_;
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
else
{
lean_inc(v_a_3563_);
lean_dec(v___x_3562_);
v___x_3565_ = lean_box(0);
v_isShared_3566_ = v_isSharedCheck_3570_;
goto v_resetjp_3564_;
}
v_resetjp_3564_:
{
lean_object* v___x_3568_; 
if (v_isShared_3566_ == 0)
{
v___x_3568_ = v___x_3565_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
return v___x_3568_;
}
}
}
else
{
return v___x_3562_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3571_, lean_object* v_x_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_, lean_object* v___y_3578_, lean_object* v___y_3579_){
_start:
{
lean_object* v_res_3580_; 
v_res_3580_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3571_, v_x_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_, v___y_3577_, v___y_3578_);
lean_dec(v___y_3578_);
lean_dec_ref(v___y_3577_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec(v___y_3574_);
lean_dec(v___y_3573_);
return v_res_3580_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3583_, lean_object* v_letFVars_3584_, lean_object* v_lctx_3585_, lean_object* v_v_3586_, lean_object* v_e_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3595_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3596_ = lean_expr_instantiate_rev(v_e_3587_, v_fvars_3583_);
v___x_3597_ = lean_apply_1(v_v_3586_, v___x_3596_);
v___x_3598_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3598_, 0, lean_box(0));
lean_closure_set(v___x_3598_, 1, v_letFVars_3584_);
lean_closure_set(v___x_3598_, 2, v___x_3597_);
v___x_3599_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3585_, v___x_3595_, v___x_3598_, v___y_3588_, v___y_3589_, v___y_3590_, v___y_3591_, v___y_3592_, v___y_3593_);
return v___x_3599_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3600_, lean_object* v_letFVars_3601_, lean_object* v_lctx_3602_, lean_object* v_v_3603_, lean_object* v_e_3604_, lean_object* v___y_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3600_, v_letFVars_3601_, v_lctx_3602_, v_v_3603_, v_e_3604_, v___y_3605_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_, v___y_3610_);
lean_dec(v___y_3610_);
lean_dec_ref(v___y_3609_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
lean_dec(v___y_3606_);
lean_dec(v___y_3605_);
lean_dec_ref(v_e_3604_);
lean_dec_ref(v_fvars_3600_);
return v_res_3612_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3614_; lean_object* v___x_3615_; 
v___x_3614_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3615_ = l_Lean_stringToMessageData(v___x_3614_);
return v___x_3615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3616_, lean_object* v_a_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v___x_3625_; 
lean_inc_ref(v_a_3616_);
v___x_3625_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3616_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v_expr_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3677_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
v_expr_3627_ = lean_ctor_get(v_a_3617_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v_a_3617_);
if (v_isSharedCheck_3677_ == 0)
{
lean_object* v_unused_3678_; 
v_unused_3678_ = lean_ctor_get(v_a_3617_, 1);
lean_dec(v_unused_3678_);
v___x_3629_ = v_a_3617_;
v_isShared_3630_ = v_isSharedCheck_3677_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_expr_3627_);
lean_dec(v_a_3617_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3677_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; 
lean_inc(v_a_3626_);
lean_inc_ref(v_expr_3627_);
v___x_3631_ = l_Lean_Meta_isExprDefEq(v_expr_3627_, v_a_3626_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3668_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3668_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3668_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
uint8_t v___x_3636_; 
v___x_3636_ = lean_unbox(v_a_3632_);
lean_dec(v_a_3632_);
if (v___x_3636_ == 0)
{
lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; 
lean_del_object(v___x_3634_);
v___x_3637_ = lean_box(0);
v___x_3638_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3639_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3626_, v_expr_3627_, v___x_3637_, v___x_3638_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v_expr_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3654_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v_expr_3641_ = lean_ctor_get(v_a_3616_, 0);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_a_3616_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v_a_3616_, 1);
lean_dec(v_unused_3655_);
v___x_3643_ = v_a_3616_;
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_expr_3641_);
lean_dec(v_a_3616_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3654_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
v___x_3645_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3646_ = l_Lean_indentExpr(v_expr_3641_);
if (v_isShared_3644_ == 0)
{
lean_ctor_set_tag(v___x_3643_, 7);
lean_ctor_set(v___x_3643_, 1, v___x_3646_);
lean_ctor_set(v___x_3643_, 0, v___x_3645_);
v___x_3648_ = v___x_3643_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3645_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3650_; 
if (v_isShared_3630_ == 0)
{
lean_ctor_set_tag(v___x_3629_, 7);
lean_ctor_set(v___x_3629_, 1, v_a_3640_);
lean_ctor_set(v___x_3629_, 0, v___x_3648_);
v___x_3650_ = v___x_3629_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3648_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_a_3640_);
v___x_3650_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; 
v___x_3651_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3650_, v___y_3620_, v___y_3621_, v___y_3622_, v___y_3623_);
return v___x_3651_;
}
}
}
}
else
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3663_; 
lean_del_object(v___x_3629_);
lean_dec_ref(v_a_3616_);
v_a_3656_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3658_ = v___x_3639_;
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3639_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3663_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3661_; 
if (v_isShared_3659_ == 0)
{
v___x_3661_ = v___x_3658_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
return v___x_3661_;
}
}
}
}
else
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_del_object(v___x_3629_);
lean_dec_ref(v_expr_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3616_);
v___x_3664_ = lean_box(0);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3664_);
v___x_3666_ = v___x_3634_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
lean_del_object(v___x_3629_);
lean_dec_ref(v_expr_3627_);
lean_dec(v_a_3626_);
lean_dec_ref(v_a_3616_);
v_a_3669_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3631_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3631_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_dec_ref(v_a_3617_);
lean_dec_ref(v_a_3616_);
v_a_3679_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3625_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3625_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3687_, lean_object* v_a_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
lean_object* v_res_3696_; 
v_res_3696_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3687_, v_a_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec(v___y_3689_);
return v_res_3696_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3698_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3699_ = l_Lean_stringToMessageData(v___x_3698_);
return v___x_3699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3700_, lean_object* v_a_3701_, lean_object* v_a_3702_, lean_object* v_a_3703_, lean_object* v_a_3704_, lean_object* v_a_3705_, lean_object* v_a_3706_){
_start:
{
if (lean_obj_tag(v_e_3700_) == 5)
{
lean_object* v_fn_3708_; lean_object* v_arg_3709_; lean_object* v___x_3710_; 
v_fn_3708_ = lean_ctor_get(v_e_3700_, 0);
v_arg_3709_ = lean_ctor_get(v_e_3700_, 1);
lean_inc_ref(v_fn_3708_);
v___x_3710_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3708_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
lean_inc_ref(v_arg_3709_);
v___x_3712_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3709_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3735_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3735_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3735_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3735_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v_expr_3717_; size_t v___x_3718_; size_t v___x_3719_; uint8_t v___x_3720_; 
v_expr_3717_ = lean_ctor_get(v_a_3713_, 0);
lean_inc_ref(v_expr_3717_);
lean_dec(v_a_3713_);
v___x_3718_ = lean_ptr_addr(v_fn_3708_);
v___x_3719_ = lean_ptr_addr(v_a_3711_);
v___x_3720_ = lean_usize_dec_eq(v___x_3718_, v___x_3719_);
if (v___x_3720_ == 0)
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
lean_dec_ref_known(v_e_3700_, 2);
v___x_3721_ = l_Lean_Expr_app___override(v_a_3711_, v_expr_3717_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3721_);
v___x_3723_ = v___x_3715_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
else
{
size_t v___x_3725_; size_t v___x_3726_; uint8_t v___x_3727_; 
v___x_3725_ = lean_ptr_addr(v_arg_3709_);
v___x_3726_ = lean_ptr_addr(v_expr_3717_);
v___x_3727_ = lean_usize_dec_eq(v___x_3725_, v___x_3726_);
if (v___x_3727_ == 0)
{
lean_object* v___x_3728_; lean_object* v___x_3730_; 
lean_dec_ref_known(v_e_3700_, 2);
v___x_3728_ = l_Lean_Expr_app___override(v_a_3711_, v_expr_3717_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3728_);
v___x_3730_ = v___x_3715_;
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
lean_object* v___x_3733_; 
lean_dec_ref(v_expr_3717_);
lean_dec(v_a_3711_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v_e_3700_);
v___x_3733_ = v___x_3715_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_e_3700_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
}
}
else
{
lean_object* v_a_3736_; lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3743_; 
lean_dec(v_a_3711_);
lean_dec_ref_known(v_e_3700_, 2);
v_a_3736_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3743_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3743_ == 0)
{
v___x_3738_ = v___x_3712_;
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
else
{
lean_inc(v_a_3736_);
lean_dec(v___x_3712_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3743_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3741_; 
if (v_isShared_3739_ == 0)
{
v___x_3741_ = v___x_3738_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v_a_3736_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3700_, 2);
return v___x_3710_;
}
}
else
{
lean_object* v___x_3744_; 
v___x_3744_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3700_, v_a_3701_, v_a_3702_, v_a_3703_, v_a_3704_, v_a_3705_, v_a_3706_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3753_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3747_ = v___x_3744_;
v_isShared_3748_ = v_isSharedCheck_3753_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_a_3745_);
lean_dec(v___x_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3753_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v_expr_3749_; lean_object* v___x_3751_; 
v_expr_3749_ = lean_ctor_get(v_a_3745_, 0);
lean_inc_ref(v_expr_3749_);
lean_dec(v_a_3745_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v_expr_3749_);
v___x_3751_ = v___x_3747_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_expr_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
v_a_3754_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3744_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3744_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3762_, lean_object* v_a_3763_, lean_object* v_a_3764_, lean_object* v_a_3765_, lean_object* v_a_3766_, lean_object* v_a_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
lean_object* v_res_3770_; 
v_res_3770_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3762_, v_a_3763_, v_a_3764_, v_a_3765_, v_a_3766_, v_a_3767_, v_a_3768_);
lean_dec(v_a_3768_);
lean_dec_ref(v_a_3767_);
lean_dec(v_a_3766_);
lean_dec_ref(v_a_3765_);
lean_dec(v_a_3764_);
lean_dec(v_a_3763_);
return v_res_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_){
_start:
{
if (lean_obj_tag(v_e_3771_) == 5)
{
lean_object* v_fn_3779_; lean_object* v_arg_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; 
v_fn_3779_ = lean_ctor_get(v_e_3771_, 0);
v_arg_3780_ = lean_ctor_get(v_e_3771_, 1);
lean_inc_ref_n(v_fn_3779_, 2);
v___x_3781_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3781_, 0, v_fn_3779_);
v___x_3782_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3779_, v___x_3781_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v_a_3783_; lean_object* v___x_3784_; 
v_a_3783_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_a_3783_);
lean_dec_ref_known(v___x_3782_, 1);
lean_inc_ref(v_arg_3780_);
v___x_3784_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3780_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
v___x_3786_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3771_, v_a_3783_, v_a_3785_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
return v___x_3786_;
}
else
{
lean_dec(v_a_3783_);
lean_dec_ref_known(v_e_3771_, 2);
return v___x_3784_;
}
}
else
{
lean_dec_ref_known(v_e_3771_, 2);
return v___x_3782_;
}
}
else
{
lean_object* v___x_3787_; 
v___x_3787_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3771_, v_a_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_);
return v___x_3787_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3788_, lean_object* v_a_3789_, lean_object* v_a_3790_, lean_object* v_a_3791_, lean_object* v_a_3792_, lean_object* v_a_3793_, lean_object* v_a_3794_){
_start:
{
uint8_t v___x_3796_; 
v___x_3796_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3789_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; 
v___x_3797_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3807_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3800_ = v___x_3797_;
v_isShared_3801_ = v_isSharedCheck_3807_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_a_3798_);
lean_dec(v___x_3797_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3807_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3805_; 
v___x_3802_ = lean_box(0);
v___x_3803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3803_, 0, v_a_3798_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3803_);
v___x_3805_ = v___x_3800_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3797_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3797_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_Expr_getAppFn(v_e_3788_);
if (lean_obj_tag(v___x_3816_) == 2)
{
lean_object* v_mvarId_3817_; lean_object* v_dummy_3818_; lean_object* v_nargs_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v_mvarId_3817_ = lean_ctor_get(v___x_3816_, 0);
lean_inc(v_mvarId_3817_);
lean_dec_ref_known(v___x_3816_, 1);
v_dummy_3818_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3819_ = l_Lean_Expr_getAppNumArgs(v_e_3788_);
lean_inc(v_nargs_3819_);
v___x_3820_ = lean_mk_array(v_nargs_3819_, v_dummy_3818_);
v___x_3821_ = lean_unsigned_to_nat(1u);
v___x_3822_ = lean_nat_sub(v_nargs_3819_, v___x_3821_);
lean_dec(v_nargs_3819_);
lean_inc_ref(v_e_3788_);
v___x_3823_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3788_, v___x_3820_, v___x_3822_);
v___x_3824_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3817_, v___x_3823_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
lean_dec(v_mvarId_3817_);
if (lean_obj_tag(v___x_3824_) == 0)
{
lean_object* v___x_3825_; 
lean_dec_ref_known(v___x_3824_, 1);
v___x_3825_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
return v___x_3825_;
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_dec_ref(v_e_3788_);
v_a_3826_ = lean_ctor_get(v___x_3824_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3824_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3824_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3824_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
else
{
lean_object* v___x_3834_; 
lean_dec_ref(v___x_3816_);
v___x_3834_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3788_, v_a_3789_, v_a_3790_, v_a_3791_, v_a_3792_, v_a_3793_, v_a_3794_);
return v___x_3834_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3835_, lean_object* v_a_3836_, lean_object* v_a_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v_res_3843_; 
v_res_3843_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3835_, v_a_3836_, v_a_3837_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
lean_dec(v_a_3841_);
lean_dec_ref(v_a_3840_);
lean_dec(v_a_3839_);
lean_dec_ref(v_a_3838_);
lean_dec(v_a_3837_);
lean_dec(v_a_3836_);
return v_res_3843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_){
_start:
{
lean_object* v___x_3852_; 
v___x_3852_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
if (lean_obj_tag(v___x_3852_) == 0)
{
lean_object* v_a_3853_; lean_object* v___x_3854_; 
v_a_3853_ = lean_ctor_get(v___x_3852_, 0);
lean_inc(v_a_3853_);
lean_dec_ref_known(v___x_3852_, 1);
v___x_3854_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3853_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_, v_a_3849_, v_a_3850_);
return v___x_3854_;
}
else
{
return v___x_3852_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3855_, lean_object* v_a_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3855_, v_a_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec(v_a_3857_);
lean_dec(v_a_3856_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3864_, lean_object* v_fvars_3865_, lean_object* v_doms_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_){
_start:
{
lean_object* v___x_3874_; 
v___x_3874_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3864_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; lean_object* v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref_known(v___x_3874_, 1);
v___x_3876_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3865_, v_doms_3866_, v_a_3875_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
return v___x_3876_;
}
else
{
return v___x_3874_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3877_, lean_object* v_fvars_3878_, lean_object* v_doms_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3877_, v_fvars_3878_, v_doms_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v___y_3883_);
lean_dec_ref(v___y_3882_);
lean_dec(v___y_3881_);
lean_dec(v___y_3880_);
lean_dec_ref(v_doms_3879_);
lean_dec_ref(v_fvars_3878_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3888_, lean_object* v_fvars_3889_, lean_object* v_doms_3890_, lean_object* v_e_3891_, lean_object* v_a_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3891_, v_a_3893_);
if (lean_obj_tag(v___x_3899_) == 0)
{
lean_object* v_a_3900_; 
v_a_3900_ = lean_ctor_get(v___x_3899_, 0);
lean_inc(v_a_3900_);
lean_dec_ref_known(v___x_3899_, 1);
if (lean_obj_tag(v_a_3900_) == 1)
{
lean_object* v_val_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; 
lean_dec_ref(v_e_3891_);
v_val_3901_ = lean_ctor_get(v_a_3900_, 0);
lean_inc(v_val_3901_);
lean_dec_ref_known(v_a_3900_, 1);
v___x_3902_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3903_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3903_, 0, v_fvars_3889_);
lean_closure_set(v___x_3903_, 1, v_doms_3890_);
lean_closure_set(v___x_3903_, 2, v_val_3901_);
v___x_3904_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3888_, v___x_3902_, v___x_3903_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
return v___x_3904_;
}
else
{
lean_dec(v_a_3900_);
if (lean_obj_tag(v_e_3891_) == 7)
{
lean_object* v_binderName_3905_; lean_object* v_binderType_3906_; lean_object* v_body_3907_; uint8_t v_binderInfo_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_binderName_3905_ = lean_ctor_get(v_e_3891_, 0);
lean_inc(v_binderName_3905_);
v_binderType_3906_ = lean_ctor_get(v_e_3891_, 1);
lean_inc_ref(v_binderType_3906_);
v_body_3907_ = lean_ctor_get(v_e_3891_, 2);
lean_inc_ref(v_body_3907_);
v_binderInfo_3908_ = lean_ctor_get_uint8(v_e_3891_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3891_, 3);
v___x_3909_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3910_ = lean_expr_instantiate_rev(v_binderType_3906_, v_fvars_3889_);
lean_dec_ref(v_binderType_3906_);
v___x_3911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3911_, 0, v___x_3910_);
lean_inc_ref(v_lctx_3888_);
v___x_3912_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3888_, v___x_3909_, v___x_3911_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v_expr_3916_; uint8_t v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc_n(v_a_3915_, 2);
lean_dec_ref_known(v___x_3914_, 1);
v_expr_3916_ = lean_ctor_get(v_a_3913_, 0);
v___x_3917_ = 0;
lean_inc_ref(v_expr_3916_);
v___x_3918_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3888_, v_a_3915_, v_binderName_3905_, v_expr_3916_, v_binderInfo_3908_, v___x_3917_);
v___x_3919_ = l_Lean_Expr_fvar___override(v_a_3915_);
v___x_3920_ = lean_array_push(v_fvars_3889_, v___x_3919_);
v___x_3921_ = lean_array_push(v_doms_3890_, v_a_3913_);
v_lctx_3888_ = v___x_3918_;
v_fvars_3889_ = v___x_3920_;
v_doms_3890_ = v___x_3921_;
v_e_3891_ = v_body_3907_;
goto _start;
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_dec(v_a_3913_);
lean_dec_ref(v_body_3907_);
lean_dec(v_binderName_3905_);
lean_dec_ref(v_doms_3890_);
lean_dec_ref(v_fvars_3889_);
lean_dec_ref(v_lctx_3888_);
v_a_3923_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3914_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3914_);
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
else
{
lean_dec_ref(v_body_3907_);
lean_dec(v_binderName_3905_);
lean_dec_ref(v_doms_3890_);
lean_dec_ref(v_fvars_3889_);
lean_dec_ref(v_lctx_3888_);
return v___x_3912_;
}
}
else
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___f_3933_; lean_object* v___x_3934_; 
v___x_3931_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3932_ = lean_expr_instantiate_rev(v_e_3891_, v_fvars_3889_);
lean_dec_ref(v_e_3891_);
v___f_3933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3933_, 0, v___x_3932_);
lean_closure_set(v___f_3933_, 1, v_fvars_3889_);
lean_closure_set(v___f_3933_, 2, v_doms_3890_);
v___x_3934_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3888_, v___x_3931_, v___f_3933_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_);
return v___x_3934_;
}
}
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec_ref(v_e_3891_);
lean_dec_ref(v_doms_3890_);
lean_dec_ref(v_fvars_3889_);
lean_dec_ref(v_lctx_3888_);
v_a_3935_ = lean_ctor_get(v___x_3899_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3899_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3899_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3899_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3940_; 
if (v_isShared_3938_ == 0)
{
v___x_3940_ = v___x_3937_;
goto v_reusejp_3939_;
}
else
{
lean_object* v_reuseFailAlloc_3941_; 
v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
v___x_3940_ = v_reuseFailAlloc_3941_;
goto v_reusejp_3939_;
}
v_reusejp_3939_:
{
return v___x_3940_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3943_, lean_object* v_a_3944_, lean_object* v_a_3945_, lean_object* v_a_3946_, lean_object* v_a_3947_, lean_object* v_a_3948_, lean_object* v_a_3949_){
_start:
{
uint32_t v___x_3951_; uint8_t v___x_3952_; 
v___x_3951_ = 5;
v___x_3952_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3943_, v___x_3951_);
if (v___x_3952_ == 0)
{
lean_object* v_lctx_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_lctx_3953_ = lean_ctor_get(v_a_3946_, 2);
v___x_3954_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3953_);
v___x_3955_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3953_, v___x_3954_, v___x_3954_, v_e_3943_, v_a_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_);
return v___x_3955_;
}
else
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3956_ = lean_box(0);
v___x_3957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3957_, 0, v_e_3943_);
lean_ctor_set(v___x_3957_, 1, v___x_3956_);
v___x_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
return v___x_3958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_, lean_object* v_a_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v_res_3967_; 
v_res_3967_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3959_, v_a_3960_, v_a_3961_, v_a_3962_, v_a_3963_, v_a_3964_, v_a_3965_);
lean_dec(v_a_3965_);
lean_dec_ref(v_a_3964_);
lean_dec(v_a_3963_);
lean_dec_ref(v_a_3962_);
lean_dec(v_a_3961_);
lean_dec(v_a_3960_);
return v_res_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_3968_, lean_object* v_e_3969_, lean_object* v_typeName_3970_, lean_object* v_idx_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_3968_, v_e_3969_, v_typeName_3970_, v_idx_3971_, v___y_3972_, v___y_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
lean_dec_ref(v___y_3974_);
lean_dec(v___y_3973_);
lean_dec(v___y_3972_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_3980_, lean_object* v_a_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_, lean_object* v_a_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3980_, v_a_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_, v_a_3986_);
lean_dec(v_a_3986_);
lean_dec_ref(v_a_3985_);
lean_dec(v_a_3984_);
lean_dec_ref(v_a_3983_);
lean_dec(v_a_3982_);
lean_dec(v_a_3981_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v___x_3998_; 
v___x_3998_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_object* v_a_3999_; lean_object* v___x_4000_; 
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___x_4000_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_3989_, v_a_3999_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_, v___y_3995_, v___y_3996_);
return v___x_4000_;
}
else
{
lean_dec_ref(v_fvars_3989_);
return v___x_3998_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
lean_dec(v___y_4004_);
lean_dec(v___y_4003_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4011_, lean_object* v_fvars_4012_, lean_object* v_e_4013_, lean_object* v_letFVars_4014_, lean_object* v_a_4015_, lean_object* v_a_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_){
_start:
{
switch(lean_obj_tag(v_e_4013_))
{
case 6:
{
lean_object* v_binderName_4022_; lean_object* v_binderType_4023_; lean_object* v_body_4024_; uint8_t v_binderInfo_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v_binderName_4022_ = lean_ctor_get(v_e_4013_, 0);
lean_inc(v_binderName_4022_);
v_binderType_4023_ = lean_ctor_get(v_e_4013_, 1);
lean_inc_ref(v_binderType_4023_);
v_body_4024_ = lean_ctor_get(v_e_4013_, 2);
lean_inc_ref(v_body_4024_);
v_binderInfo_4025_ = lean_ctor_get_uint8(v_e_4013_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4013_, 3);
v___x_4026_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4011_);
lean_inc(v_letFVars_4014_);
v___x_4027_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4012_, v_letFVars_4014_, v_lctx_4011_, v___x_4026_, v_binderType_4023_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec_ref(v_binderType_4023_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4029_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
lean_inc(v_a_4028_);
lean_dec_ref_known(v___x_4027_, 1);
v___x_4029_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v_expr_4031_; uint8_t v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc_n(v_a_4030_, 2);
lean_dec_ref_known(v___x_4029_, 1);
v_expr_4031_ = lean_ctor_get(v_a_4028_, 0);
lean_inc_ref(v_expr_4031_);
lean_dec(v_a_4028_);
v___x_4032_ = 0;
v___x_4033_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4011_, v_a_4030_, v_binderName_4022_, v_expr_4031_, v_binderInfo_4025_, v___x_4032_);
v___x_4034_ = l_Lean_Expr_fvar___override(v_a_4030_);
v___x_4035_ = lean_array_push(v_fvars_4012_, v___x_4034_);
v_lctx_4011_ = v___x_4033_;
v_fvars_4012_ = v___x_4035_;
v_e_4013_ = v_body_4024_;
goto _start;
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_dec(v_a_4028_);
lean_dec_ref(v_body_4024_);
lean_dec(v_binderName_4022_);
lean_dec(v_letFVars_4014_);
lean_dec_ref(v_fvars_4012_);
lean_dec_ref(v_lctx_4011_);
v_a_4037_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4029_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4029_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_dec_ref(v_body_4024_);
lean_dec(v_binderName_4022_);
lean_dec(v_letFVars_4014_);
lean_dec_ref(v_fvars_4012_);
lean_dec_ref(v_lctx_4011_);
return v___x_4027_;
}
}
case 8:
{
lean_object* v_declName_4045_; lean_object* v_type_4046_; lean_object* v_value_4047_; lean_object* v_body_4048_; uint8_t v_nondep_4049_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v_declName_4045_ = lean_ctor_get(v_e_4013_, 0);
lean_inc(v_declName_4045_);
v_type_4046_ = lean_ctor_get(v_e_4013_, 1);
lean_inc_ref(v_type_4046_);
v_value_4047_ = lean_ctor_get(v_e_4013_, 2);
lean_inc_ref(v_value_4047_);
v_body_4048_ = lean_ctor_get(v_e_4013_, 3);
lean_inc_ref(v_body_4048_);
v_nondep_4049_ = lean_ctor_get_uint8(v_e_4013_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4013_, 4);
v___x_4063_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4011_);
lean_inc(v_letFVars_4014_);
v___x_4064_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4012_, v_letFVars_4014_, v_lctx_4011_, v___x_4063_, v_type_4046_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec_ref(v_type_4046_);
if (lean_obj_tag(v___x_4064_) == 0)
{
lean_object* v_a_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_a_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc(v_a_4065_);
lean_dec_ref_known(v___x_4064_, 1);
v___x_4066_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4011_);
lean_inc(v_letFVars_4014_);
v___x_4067_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4012_, v_letFVars_4014_, v_lctx_4011_, v___x_4066_, v_value_4047_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec_ref(v_value_4047_);
if (lean_obj_tag(v___x_4067_) == 0)
{
lean_object* v_a_4068_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; uint8_t v___x_4098_; 
v_a_4068_ = lean_ctor_get(v___x_4067_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4067_, 1);
v___x_4098_ = l_List_isEmpty___redArg(v_letFVars_4014_);
if (v___x_4098_ == 0)
{
lean_object* v___f_4099_; lean_object* v___x_4100_; 
lean_inc(v_a_4065_);
lean_inc(v_a_4068_);
v___f_4099_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4099_, 0, v_a_4068_);
lean_closure_set(v___f_4099_, 1, v_a_4065_);
lean_inc_ref(v_lctx_4011_);
v___x_4100_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4011_, v___f_4099_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_dec_ref_known(v___x_4100_, 1);
v___y_4070_ = v_a_4015_;
v___y_4071_ = v_a_4016_;
v___y_4072_ = v_a_4017_;
v___y_4073_ = v_a_4018_;
v___y_4074_ = v_a_4019_;
v___y_4075_ = v_a_4020_;
goto v___jp_4069_;
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_body_4048_);
lean_dec(v_declName_4045_);
lean_dec(v_letFVars_4014_);
lean_dec_ref(v_fvars_4012_);
lean_dec_ref(v_lctx_4011_);
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4100_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4100_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
v___y_4070_ = v_a_4015_;
v___y_4071_ = v_a_4016_;
v___y_4072_ = v_a_4017_;
v___y_4073_ = v_a_4018_;
v___y_4074_ = v_a_4019_;
v___y_4075_ = v_a_4020_;
goto v___jp_4069_;
}
v___jp_4069_:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v_expr_4078_; lean_object* v_expr_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4088_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
v_expr_4078_ = lean_ctor_get(v_a_4065_, 0);
lean_inc_ref(v_expr_4078_);
lean_dec(v_a_4065_);
v_expr_4079_ = lean_ctor_get(v_a_4068_, 0);
v_isSharedCheck_4088_ = !lean_is_exclusive(v_a_4068_);
if (v_isSharedCheck_4088_ == 0)
{
lean_object* v_unused_4089_; 
v_unused_4089_ = lean_ctor_get(v_a_4068_, 1);
lean_dec(v_unused_4089_);
v___x_4081_ = v_a_4068_;
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_expr_4079_);
lean_dec(v_a_4068_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4088_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
uint8_t v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = 0;
lean_inc(v_a_4077_);
v___x_4084_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4011_, v_a_4077_, v_declName_4045_, v_expr_4078_, v_expr_4079_, v_nondep_4049_, v___x_4083_);
if (v_nondep_4049_ == 0)
{
lean_object* v___x_4086_; 
lean_inc(v_a_4077_);
if (v_isShared_4082_ == 0)
{
lean_ctor_set_tag(v___x_4081_, 1);
lean_ctor_set(v___x_4081_, 1, v_letFVars_4014_);
lean_ctor_set(v___x_4081_, 0, v_a_4077_);
v___x_4086_ = v___x_4081_;
goto v_reusejp_4085_;
}
else
{
lean_object* v_reuseFailAlloc_4087_; 
v_reuseFailAlloc_4087_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4087_, 0, v_a_4077_);
lean_ctor_set(v_reuseFailAlloc_4087_, 1, v_letFVars_4014_);
v___x_4086_ = v_reuseFailAlloc_4087_;
goto v_reusejp_4085_;
}
v_reusejp_4085_:
{
v___y_4051_ = v___y_4073_;
v___y_4052_ = v___x_4084_;
v___y_4053_ = v___y_4074_;
v___y_4054_ = v___y_4070_;
v___y_4055_ = v___y_4075_;
v___y_4056_ = v___y_4071_;
v___y_4057_ = v___y_4072_;
v___y_4058_ = v_a_4077_;
v___y_4059_ = v___x_4086_;
goto v___jp_4050_;
}
}
else
{
lean_del_object(v___x_4081_);
v___y_4051_ = v___y_4073_;
v___y_4052_ = v___x_4084_;
v___y_4053_ = v___y_4074_;
v___y_4054_ = v___y_4070_;
v___y_4055_ = v___y_4075_;
v___y_4056_ = v___y_4071_;
v___y_4057_ = v___y_4072_;
v___y_4058_ = v_a_4077_;
v___y_4059_ = v_letFVars_4014_;
goto v___jp_4050_;
}
}
}
else
{
lean_object* v_a_4090_; lean_object* v___x_4092_; uint8_t v_isShared_4093_; uint8_t v_isSharedCheck_4097_; 
lean_dec(v_a_4068_);
lean_dec(v_a_4065_);
lean_dec_ref(v_body_4048_);
lean_dec(v_declName_4045_);
lean_dec(v_letFVars_4014_);
lean_dec_ref(v_fvars_4012_);
lean_dec_ref(v_lctx_4011_);
v_a_4090_ = lean_ctor_get(v___x_4076_, 0);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4076_);
if (v_isSharedCheck_4097_ == 0)
{
v___x_4092_ = v___x_4076_;
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
else
{
lean_inc(v_a_4090_);
lean_dec(v___x_4076_);
v___x_4092_ = lean_box(0);
v_isShared_4093_ = v_isSharedCheck_4097_;
goto v_resetjp_4091_;
}
v_resetjp_4091_:
{
lean_object* v___x_4095_; 
if (v_isShared_4093_ == 0)
{
v___x_4095_ = v___x_4092_;
goto v_reusejp_4094_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v_a_4090_);
v___x_4095_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4094_;
}
v_reusejp_4094_:
{
return v___x_4095_;
}
}
}
}
}
else
{
lean_dec(v_a_4065_);
lean_dec_ref(v_body_4048_);
lean_dec(v_declName_4045_);
lean_dec(v_letFVars_4014_);
lean_dec_ref(v_fvars_4012_);
lean_dec_ref(v_lctx_4011_);
return v___x_4067_;
}
}
else
{
lean_dec_ref(v_body_4048_);
lean_dec_ref(v_value_4047_);
lean_dec(v_declName_4045_);
lean_dec(v_letFVars_4014_);
lean_dec_ref(v_fvars_4012_);
lean_dec_ref(v_lctx_4011_);
return v___x_4064_;
}
v___jp_4050_:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4060_ = l_Lean_Expr_fvar___override(v___y_4058_);
v___x_4061_ = lean_array_push(v_fvars_4012_, v___x_4060_);
v_lctx_4011_ = v___y_4052_;
v_fvars_4012_ = v___x_4061_;
v_e_4013_ = v_body_4048_;
v_letFVars_4014_ = v___y_4059_;
v_a_4015_ = v___y_4054_;
v_a_4016_ = v___y_4056_;
v_a_4017_ = v___y_4057_;
v_a_4018_ = v___y_4051_;
v_a_4019_ = v___y_4053_;
v_a_4020_ = v___y_4055_;
goto _start;
}
}
default: 
{
lean_object* v___f_4109_; lean_object* v___x_4110_; 
lean_inc_ref(v_fvars_4012_);
v___f_4109_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4109_, 0, v_fvars_4012_);
v___x_4110_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4012_, v_letFVars_4014_, v_lctx_4011_, v___f_4109_, v_e_4013_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec_ref(v_e_4013_);
lean_dec_ref(v_fvars_4012_);
return v___x_4110_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4111_, lean_object* v_a_4112_, lean_object* v_a_4113_, lean_object* v_a_4114_, lean_object* v_a_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_){
_start:
{
uint32_t v___x_4119_; uint8_t v___x_4120_; 
v___x_4119_ = 5;
v___x_4120_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4111_, v___x_4119_);
if (v___x_4120_ == 0)
{
lean_object* v_lctx_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v_lctx_4121_ = lean_ctor_get(v_a_4114_, 2);
v___x_4122_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4112_);
lean_inc_ref(v_lctx_4121_);
v___x_4123_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4121_, v___x_4122_, v_e_4111_, v_a_4112_, v_a_4112_, v_a_4113_, v_a_4114_, v_a_4115_, v_a_4116_, v_a_4117_);
return v___x_4123_;
}
else
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v___x_4124_ = lean_box(0);
v___x_4125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4125_, 0, v_e_4111_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4125_);
return v___x_4126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v_res_4135_; 
v_res_4135_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4127_, v_a_4128_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_, v_a_4133_);
lean_dec(v_a_4133_);
lean_dec_ref(v_a_4132_);
lean_dec(v_a_4131_);
lean_dec_ref(v_a_4130_);
lean_dec(v_a_4129_);
lean_dec(v_a_4128_);
return v_res_4135_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
switch(lean_obj_tag(v_e_4136_))
{
case 0:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; 
v___x_4144_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4145_ = l_Lean_MessageData_ofExpr(v_e_4136_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4146_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4147_;
}
case 1:
{
lean_object* v___x_4148_; 
v___x_4148_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4136_, v___y_4139_, v___y_4141_, v___y_4142_);
return v___x_4148_;
}
case 2:
{
lean_object* v___x_4149_; 
v___x_4149_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4149_;
}
case 3:
{
lean_object* v_u_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v_u_4150_ = lean_ctor_get(v_e_4136_, 0);
lean_inc(v_u_4150_);
v___x_4151_ = l_Lean_Level_succ___override(v_u_4150_);
v___x_4152_ = l_Lean_Expr_sort___override(v___x_4151_);
v___x_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4153_, 0, v___x_4152_);
v___x_4154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4154_, 0, v_e_4136_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
return v___x_4155_;
}
case 4:
{
lean_object* v___x_4156_; 
v___x_4156_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4156_;
}
case 5:
{
lean_object* v___x_4157_; lean_object* v___x_4158_; 
lean_inc_ref(v_e_4136_);
v___x_4157_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4157_, 0, v_e_4136_);
v___x_4158_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4136_, v___x_4157_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4158_;
}
case 7:
{
lean_object* v___x_4159_; lean_object* v___x_4160_; 
lean_inc_ref(v_e_4136_);
v___x_4159_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4159_, 0, v_e_4136_);
v___x_4160_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4136_, v___x_4159_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4160_;
}
case 9:
{
lean_object* v_a_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; 
v_a_4161_ = lean_ctor_get(v_e_4136_, 0);
v___x_4162_ = l_Lean_Literal_type(v_a_4161_);
v___x_4163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
v___x_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4164_, 0, v_e_4136_);
lean_ctor_set(v___x_4164_, 1, v___x_4163_);
v___x_4165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
return v___x_4165_;
}
case 10:
{
lean_object* v_data_4166_; lean_object* v_expr_4167_; lean_object* v___x_4168_; 
v_data_4166_ = lean_ctor_get(v_e_4136_, 0);
v_expr_4167_ = lean_ctor_get(v_e_4136_, 1);
lean_inc_ref(v_expr_4167_);
v___x_4168_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4167_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
if (lean_obj_tag(v___x_4168_) == 0)
{
lean_object* v_a_4169_; lean_object* v___x_4171_; uint8_t v_isShared_4172_; uint8_t v_isSharedCheck_4191_; 
v_a_4169_ = lean_ctor_get(v___x_4168_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4168_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4171_ = v___x_4168_;
v_isShared_4172_ = v_isSharedCheck_4191_;
goto v_resetjp_4170_;
}
else
{
lean_inc(v_a_4169_);
lean_dec(v___x_4168_);
v___x_4171_ = lean_box(0);
v_isShared_4172_ = v_isSharedCheck_4191_;
goto v_resetjp_4170_;
}
v_resetjp_4170_:
{
lean_object* v_expr_4173_; lean_object* v_type_x3f_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4190_; 
v_expr_4173_ = lean_ctor_get(v_a_4169_, 0);
v_type_x3f_4174_ = lean_ctor_get(v_a_4169_, 1);
v_isSharedCheck_4190_ = !lean_is_exclusive(v_a_4169_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4176_ = v_a_4169_;
v_isShared_4177_ = v_isSharedCheck_4190_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_type_x3f_4174_);
lean_inc(v_expr_4173_);
lean_dec(v_a_4169_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4190_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___y_4179_; size_t v___x_4186_; size_t v___x_4187_; uint8_t v___x_4188_; 
v___x_4186_ = lean_ptr_addr(v_expr_4167_);
v___x_4187_ = lean_ptr_addr(v_expr_4173_);
v___x_4188_ = lean_usize_dec_eq(v___x_4186_, v___x_4187_);
if (v___x_4188_ == 0)
{
lean_object* v___x_4189_; 
lean_inc(v_data_4166_);
lean_dec_ref_known(v_e_4136_, 2);
v___x_4189_ = l_Lean_Expr_mdata___override(v_data_4166_, v_expr_4173_);
v___y_4179_ = v___x_4189_;
goto v___jp_4178_;
}
else
{
lean_dec_ref(v_expr_4173_);
v___y_4179_ = v_e_4136_;
goto v___jp_4178_;
}
v___jp_4178_:
{
lean_object* v___x_4181_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set(v___x_4176_, 0, v___y_4179_);
v___x_4181_ = v___x_4176_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4185_; 
v_reuseFailAlloc_4185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4185_, 0, v___y_4179_);
lean_ctor_set(v_reuseFailAlloc_4185_, 1, v_type_x3f_4174_);
v___x_4181_ = v_reuseFailAlloc_4185_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
lean_object* v___x_4183_; 
if (v_isShared_4172_ == 0)
{
lean_ctor_set(v___x_4171_, 0, v___x_4181_);
v___x_4183_ = v___x_4171_;
goto v_reusejp_4182_;
}
else
{
lean_object* v_reuseFailAlloc_4184_; 
v_reuseFailAlloc_4184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4184_, 0, v___x_4181_);
v___x_4183_ = v_reuseFailAlloc_4184_;
goto v_reusejp_4182_;
}
v_reusejp_4182_:
{
return v___x_4183_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4136_, 2);
return v___x_4168_;
}
}
case 11:
{
lean_object* v_typeName_4192_; lean_object* v_idx_4193_; lean_object* v_struct_4194_; lean_object* v___f_4195_; lean_object* v___x_4196_; 
v_typeName_4192_ = lean_ctor_get(v_e_4136_, 0);
v_idx_4193_ = lean_ctor_get(v_e_4136_, 1);
v_struct_4194_ = lean_ctor_get(v_e_4136_, 2);
lean_inc(v_idx_4193_);
lean_inc(v_typeName_4192_);
lean_inc_ref(v_e_4136_);
lean_inc_ref(v_struct_4194_);
v___f_4195_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4195_, 0, v_struct_4194_);
lean_closure_set(v___f_4195_, 1, v_e_4136_);
lean_closure_set(v___f_4195_, 2, v_typeName_4192_);
lean_closure_set(v___f_4195_, 3, v_idx_4193_);
v___x_4196_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4136_, v___f_4195_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4196_;
}
default: 
{
lean_object* v___x_4197_; lean_object* v___x_4198_; 
lean_inc_ref(v_e_4136_);
v___x_4197_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4197_, 0, v_e_4136_);
v___x_4198_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4136_, v___x_4197_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_, v___y_4142_);
return v___x_4198_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4199_; double v___x_4200_; 
v___x_4199_ = lean_unsigned_to_nat(1000000000u);
v___x_4200_ = lean_float_of_nat(v___x_4199_);
return v___x_4200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_, lean_object* v_a_4207_){
_start:
{
lean_object* v_toCold_4209_; lean_object* v_options_4210_; uint8_t v_hasTrace_4211_; 
v_toCold_4209_ = lean_ctor_get(v_a_4206_, 0);
v_options_4210_ = lean_ctor_get(v_toCold_4209_, 2);
v_hasTrace_4211_ = lean_ctor_get_uint8(v_options_4210_, sizeof(void*)*1);
if (v_hasTrace_4211_ == 0)
{
lean_object* v___x_4212_; 
v___x_4212_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4212_;
}
else
{
lean_object* v_inheritedTraceOptions_4213_; lean_object* v___f_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; uint8_t v___x_4218_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v_a_4222_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v_a_4237_; 
v_inheritedTraceOptions_4213_ = lean_ctor_get(v_toCold_4209_, 11);
lean_inc_ref(v_e_4201_);
v___f_4214_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4214_, 0, v_e_4201_);
v___x_4215_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4216_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4217_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4218_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4213_, v_options_4210_, v___x_4217_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4295_; uint8_t v___x_4296_; 
v___x_4295_ = l_Lean_trace_profiler;
v___x_4296_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4210_, v___x_4295_);
if (v___x_4296_ == 0)
{
lean_object* v___x_4297_; 
lean_dec_ref(v___f_4214_);
v___x_4297_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4297_;
}
else
{
goto v___jp_4246_;
}
}
else
{
goto v___jp_4246_;
}
v___jp_4219_:
{
lean_object* v___x_4223_; double v___x_4224_; double v___x_4225_; double v___x_4226_; double v___x_4227_; double v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
v___x_4223_ = lean_io_mono_nanos_now();
v___x_4224_ = lean_float_of_nat(v___y_4220_);
v___x_4225_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4226_ = lean_float_div(v___x_4224_, v___x_4225_);
v___x_4227_ = lean_float_of_nat(v___x_4223_);
v___x_4228_ = lean_float_div(v___x_4227_, v___x_4225_);
v___x_4229_ = lean_box_float(v___x_4226_);
v___x_4230_ = lean_box_float(v___x_4228_);
v___x_4231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4229_);
lean_ctor_set(v___x_4231_, 1, v___x_4230_);
v___x_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_a_4222_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4215_, v_hasTrace_4211_, v___x_4216_, v_options_4210_, v___x_4218_, v___y_4221_, v___f_4214_, v___x_4232_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4233_;
}
v___jp_4234_:
{
lean_object* v___x_4238_; double v___x_4239_; double v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4238_ = lean_io_get_num_heartbeats();
v___x_4239_ = lean_float_of_nat(v___y_4236_);
v___x_4240_ = lean_float_of_nat(v___x_4238_);
v___x_4241_ = lean_box_float(v___x_4239_);
v___x_4242_ = lean_box_float(v___x_4240_);
v___x_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4244_, 0, v_a_4237_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4215_, v_hasTrace_4211_, v___x_4216_, v_options_4210_, v___x_4218_, v___y_4235_, v___f_4214_, v___x_4244_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
return v___x_4245_;
}
v___jp_4246_:
{
lean_object* v___x_4247_; 
v___x_4247_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4207_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; lean_object* v___x_4249_; uint8_t v___x_4250_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
v___x_4249_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4250_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4210_, v___x_4249_);
if (v___x_4250_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
v___x_4251_ = lean_io_mono_nanos_now();
v___x_4252_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4252_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4252_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
lean_ctor_set_tag(v___x_4255_, 1);
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
v___y_4220_ = v___x_4251_;
v___y_4221_ = v_a_4248_;
v_a_4222_ = v___x_4258_;
goto v___jp_4219_;
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
v_a_4261_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4252_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4252_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
lean_ctor_set_tag(v___x_4263_, 0);
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
v___y_4220_ = v___x_4251_;
v___y_4221_ = v_a_4248_;
v_a_4222_ = v___x_4266_;
goto v___jp_4219_;
}
}
}
}
else
{
lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4269_ = lean_io_get_num_heartbeats();
v___x_4270_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_, v_a_4206_, v_a_4207_);
if (lean_obj_tag(v___x_4270_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
v_a_4271_ = lean_ctor_get(v___x_4270_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4270_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4270_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4270_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
lean_ctor_set_tag(v___x_4273_, 1);
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
v___y_4235_ = v_a_4248_;
v___y_4236_ = v___x_4269_;
v_a_4237_ = v___x_4276_;
goto v___jp_4234_;
}
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
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
if (v_isShared_4282_ == 0)
{
lean_ctor_set_tag(v___x_4281_, 0);
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
v___y_4235_ = v_a_4248_;
v___y_4236_ = v___x_4269_;
v_a_4237_ = v___x_4284_;
goto v___jp_4234_;
}
}
}
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v___f_4214_);
lean_dec_ref(v_e_4201_);
v_a_4287_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4247_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4247_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4298_, lean_object* v_e_4299_, lean_object* v_typeName_4300_, lean_object* v_idx_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; 
v___x_4309_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4298_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_object* v_a_4310_; lean_object* v___x_4311_; 
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref_known(v___x_4309_, 1);
v___x_4311_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4299_, v_typeName_4300_, v_idx_4301_, v_a_4310_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
return v___x_4311_;
}
else
{
lean_dec(v_idx_4301_);
lean_dec(v_typeName_4300_);
lean_dec_ref(v_e_4299_);
return v___x_4309_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4312_, v_a_4313_, v_a_4314_, v_a_4315_, v_a_4316_, v_a_4317_, v_a_4318_);
lean_dec(v_a_4318_);
lean_dec_ref(v_a_4317_);
lean_dec(v_a_4316_);
lean_dec_ref(v_a_4315_);
lean_dec(v_a_4314_);
lean_dec(v_a_4313_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4321_, lean_object* v_fvars_4322_, lean_object* v_doms_4323_, lean_object* v_e_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4321_, v_fvars_4322_, v_doms_4323_, v_e_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_a_4326_);
lean_dec(v_a_4325_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec(v___y_4334_);
return v_res_4341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4342_, lean_object* v_fvars_4343_, lean_object* v_e_4344_, lean_object* v_letFVars_4345_, lean_object* v_a_4346_, lean_object* v_a_4347_, lean_object* v_a_4348_, lean_object* v_a_4349_, lean_object* v_a_4350_, lean_object* v_a_4351_, lean_object* v_a_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4342_, v_fvars_4343_, v_e_4344_, v_letFVars_4345_, v_a_4346_, v_a_4347_, v_a_4348_, v_a_4349_, v_a_4350_, v_a_4351_);
lean_dec(v_a_4351_);
lean_dec_ref(v_a_4350_);
lean_dec(v_a_4349_);
lean_dec_ref(v_a_4348_);
lean_dec(v_a_4347_);
lean_dec(v_a_4346_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4354_, lean_object* v_lctx_4355_, lean_object* v_localInsts_4356_, lean_object* v_x_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_){
_start:
{
lean_object* v___x_4365_; 
v___x_4365_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4355_, v_localInsts_4356_, v_x_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
return v___x_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4366_, lean_object* v_lctx_4367_, lean_object* v_localInsts_4368_, lean_object* v_x_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v_res_4377_; 
v_res_4377_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4366_, v_lctx_4367_, v_localInsts_4368_, v_x_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
lean_dec(v___y_4375_);
lean_dec_ref(v___y_4374_);
lean_dec(v___y_4373_);
lean_dec_ref(v___y_4372_);
lean_dec(v___y_4371_);
lean_dec(v___y_4370_);
return v_res_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4378_, lean_object* v_lctx_4379_, lean_object* v_x_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_){
_start:
{
lean_object* v___x_4388_; 
v___x_4388_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4379_, v_x_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
return v___x_4388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4389_, lean_object* v_lctx_4390_, lean_object* v_x_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v_res_4399_; 
v_res_4399_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4389_, v_lctx_4390_, v_x_4391_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
lean_dec(v___y_4397_);
lean_dec_ref(v___y_4396_);
lean_dec(v___y_4395_);
lean_dec_ref(v___y_4394_);
lean_dec(v___y_4393_);
lean_dec(v___y_4392_);
return v_res_4399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_){
_start:
{
lean_object* v___x_4407_; 
v___x_4407_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4405_);
return v___x_4407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v_res_4415_; 
v_res_4415_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___y_4413_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec(v___y_4408_);
return v_res_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_){
_start:
{
lean_object* v___x_4423_; 
v___x_4423_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4421_);
return v___x_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_){
_start:
{
lean_object* v_res_4431_; 
v_res_4431_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_, v___y_4429_);
lean_dec(v___y_4429_);
lean_dec_ref(v___y_4428_);
lean_dec(v___y_4427_);
lean_dec_ref(v___y_4426_);
lean_dec(v___y_4425_);
lean_dec(v___y_4424_);
return v_res_4431_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4432_, lean_object* v_x_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_){
_start:
{
lean_object* v___x_4441_; 
v___x_4441_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4433_);
return v___x_4441_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4442_, lean_object* v_x_4443_, lean_object* v___y_4444_, lean_object* v___y_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_){
_start:
{
lean_object* v_res_4451_; 
v_res_4451_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4442_, v_x_4443_, v___y_4444_, v___y_4445_, v___y_4446_, v___y_4447_, v___y_4448_, v___y_4449_);
lean_dec(v___y_4449_);
lean_dec_ref(v___y_4448_);
lean_dec(v___y_4447_);
lean_dec_ref(v___y_4446_);
lean_dec(v___y_4445_);
lean_dec(v___y_4444_);
return v_res_4451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4452_, lean_object* v_data_4453_, lean_object* v_ref_4454_, lean_object* v_msg_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_){
_start:
{
lean_object* v___x_4463_; 
v___x_4463_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4452_, v_data_4453_, v_ref_4454_, v_msg_4455_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
return v___x_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4464_, lean_object* v_data_4465_, lean_object* v_ref_4466_, lean_object* v_msg_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_){
_start:
{
lean_object* v_res_4475_; 
v_res_4475_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4464_, v_data_4465_, v_ref_4466_, v_msg_4467_, v___y_4468_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
lean_dec(v___y_4473_);
lean_dec_ref(v___y_4472_);
lean_dec(v___y_4471_);
lean_dec_ref(v___y_4470_);
lean_dec(v___y_4469_);
lean_dec(v___y_4468_);
return v_res_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; lean_object* v_traceState_4479_; lean_object* v_traces_4480_; lean_object* v___x_4481_; lean_object* v_traceState_4482_; lean_object* v_env_4483_; lean_object* v_nextMacroScope_4484_; lean_object* v_ngen_4485_; lean_object* v_auxDeclNGen_4486_; lean_object* v_cache_4487_; lean_object* v_messages_4488_; lean_object* v_infoState_4489_; lean_object* v_snapshotTasks_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4511_; 
v___x_4478_ = lean_st_ref_get(v___y_4476_);
v_traceState_4479_ = lean_ctor_get(v___x_4478_, 4);
lean_inc_ref(v_traceState_4479_);
lean_dec(v___x_4478_);
v_traces_4480_ = lean_ctor_get(v_traceState_4479_, 0);
lean_inc_ref(v_traces_4480_);
lean_dec_ref(v_traceState_4479_);
v___x_4481_ = lean_st_ref_take(v___y_4476_);
v_traceState_4482_ = lean_ctor_get(v___x_4481_, 4);
v_env_4483_ = lean_ctor_get(v___x_4481_, 0);
v_nextMacroScope_4484_ = lean_ctor_get(v___x_4481_, 1);
v_ngen_4485_ = lean_ctor_get(v___x_4481_, 2);
v_auxDeclNGen_4486_ = lean_ctor_get(v___x_4481_, 3);
v_cache_4487_ = lean_ctor_get(v___x_4481_, 5);
v_messages_4488_ = lean_ctor_get(v___x_4481_, 6);
v_infoState_4489_ = lean_ctor_get(v___x_4481_, 7);
v_snapshotTasks_4490_ = lean_ctor_get(v___x_4481_, 8);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4492_ = v___x_4481_;
v_isShared_4493_ = v_isSharedCheck_4511_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_snapshotTasks_4490_);
lean_inc(v_infoState_4489_);
lean_inc(v_messages_4488_);
lean_inc(v_cache_4487_);
lean_inc(v_traceState_4482_);
lean_inc(v_auxDeclNGen_4486_);
lean_inc(v_ngen_4485_);
lean_inc(v_nextMacroScope_4484_);
lean_inc(v_env_4483_);
lean_dec(v___x_4481_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4511_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
uint64_t v_tid_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4509_; 
v_tid_4494_ = lean_ctor_get_uint64(v_traceState_4482_, sizeof(void*)*1);
v_isSharedCheck_4509_ = !lean_is_exclusive(v_traceState_4482_);
if (v_isSharedCheck_4509_ == 0)
{
lean_object* v_unused_4510_; 
v_unused_4510_ = lean_ctor_get(v_traceState_4482_, 0);
lean_dec(v_unused_4510_);
v___x_4496_ = v_traceState_4482_;
v_isShared_4497_ = v_isSharedCheck_4509_;
goto v_resetjp_4495_;
}
else
{
lean_dec(v_traceState_4482_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4509_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4502_; 
v___x_4498_ = lean_unsigned_to_nat(32u);
v___x_4499_ = lean_mk_empty_array_with_capacity(v___x_4498_);
lean_dec_ref(v___x_4499_);
v___x_4500_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v___x_4500_);
v___x_4502_ = v___x_4496_;
goto v_reusejp_4501_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v___x_4500_);
lean_ctor_set_uint64(v_reuseFailAlloc_4508_, sizeof(void*)*1, v_tid_4494_);
v___x_4502_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4501_;
}
v_reusejp_4501_:
{
lean_object* v___x_4504_; 
if (v_isShared_4493_ == 0)
{
lean_ctor_set(v___x_4492_, 4, v___x_4502_);
v___x_4504_ = v___x_4492_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_env_4483_);
lean_ctor_set(v_reuseFailAlloc_4507_, 1, v_nextMacroScope_4484_);
lean_ctor_set(v_reuseFailAlloc_4507_, 2, v_ngen_4485_);
lean_ctor_set(v_reuseFailAlloc_4507_, 3, v_auxDeclNGen_4486_);
lean_ctor_set(v_reuseFailAlloc_4507_, 4, v___x_4502_);
lean_ctor_set(v_reuseFailAlloc_4507_, 5, v_cache_4487_);
lean_ctor_set(v_reuseFailAlloc_4507_, 6, v_messages_4488_);
lean_ctor_set(v_reuseFailAlloc_4507_, 7, v_infoState_4489_);
lean_ctor_set(v_reuseFailAlloc_4507_, 8, v_snapshotTasks_4490_);
v___x_4504_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
lean_object* v___x_4505_; lean_object* v___x_4506_; 
v___x_4505_ = lean_st_ref_put(v___y_4476_, v___x_4504_);
v___x_4506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4506_, 0, v_traces_4480_);
return v___x_4506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v_res_4514_; 
v_res_4514_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4512_);
lean_dec(v___y_4512_);
return v_res_4514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
lean_object* v___x_4520_; 
v___x_4520_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4518_);
return v___x_4520_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4527_, lean_object* v_zetaDeltaFVarIds_4528_, lean_object* v_a_x3f_4529_){
_start:
{
lean_object* v___x_4531_; lean_object* v_mctx_4532_; lean_object* v_cache_4533_; lean_object* v_postponed_4534_; lean_object* v_diag_4535_; lean_object* v___x_4537_; uint8_t v_isShared_4538_; uint8_t v_isSharedCheck_4545_; 
v___x_4531_ = lean_st_ref_take(v___y_4527_);
v_mctx_4532_ = lean_ctor_get(v___x_4531_, 0);
v_cache_4533_ = lean_ctor_get(v___x_4531_, 1);
v_postponed_4534_ = lean_ctor_get(v___x_4531_, 3);
v_diag_4535_ = lean_ctor_get(v___x_4531_, 4);
v_isSharedCheck_4545_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4545_ == 0)
{
lean_object* v_unused_4546_; 
v_unused_4546_ = lean_ctor_get(v___x_4531_, 2);
lean_dec(v_unused_4546_);
v___x_4537_ = v___x_4531_;
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
else
{
lean_inc(v_diag_4535_);
lean_inc(v_postponed_4534_);
lean_inc(v_cache_4533_);
lean_inc(v_mctx_4532_);
lean_dec(v___x_4531_);
v___x_4537_ = lean_box(0);
v_isShared_4538_ = v_isSharedCheck_4545_;
goto v_resetjp_4536_;
}
v_resetjp_4536_:
{
lean_object* v___x_4540_; 
if (v_isShared_4538_ == 0)
{
lean_ctor_set(v___x_4537_, 2, v_zetaDeltaFVarIds_4528_);
v___x_4540_ = v___x_4537_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4544_; 
v_reuseFailAlloc_4544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4544_, 0, v_mctx_4532_);
lean_ctor_set(v_reuseFailAlloc_4544_, 1, v_cache_4533_);
lean_ctor_set(v_reuseFailAlloc_4544_, 2, v_zetaDeltaFVarIds_4528_);
lean_ctor_set(v_reuseFailAlloc_4544_, 3, v_postponed_4534_);
lean_ctor_set(v_reuseFailAlloc_4544_, 4, v_diag_4535_);
v___x_4540_ = v_reuseFailAlloc_4544_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4541_ = lean_st_ref_put(v___y_4527_, v___x_4540_);
v___x_4542_ = lean_box(0);
v___x_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4542_);
return v___x_4543_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4547_, lean_object* v_zetaDeltaFVarIds_4548_, lean_object* v_a_x3f_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4547_, v_zetaDeltaFVarIds_4548_, v_a_x3f_4549_);
lean_dec(v_a_x3f_4549_);
lean_dec(v___y_4547_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4552_, lean_object* v_msg_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_ref_4559_; lean_object* v___x_4560_; lean_object* v_a_4561_; lean_object* v___x_4563_; uint8_t v_isShared_4564_; uint8_t v_isSharedCheck_4605_; 
v_ref_4559_ = lean_ctor_get(v___y_4556_, 2);
v___x_4560_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4605_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4605_ == 0)
{
v___x_4563_ = v___x_4560_;
v_isShared_4564_ = v_isSharedCheck_4605_;
goto v_resetjp_4562_;
}
else
{
lean_inc(v_a_4561_);
lean_dec(v___x_4560_);
v___x_4563_ = lean_box(0);
v_isShared_4564_ = v_isSharedCheck_4605_;
goto v_resetjp_4562_;
}
v_resetjp_4562_:
{
lean_object* v___x_4565_; lean_object* v_traceState_4566_; lean_object* v_env_4567_; lean_object* v_nextMacroScope_4568_; lean_object* v_ngen_4569_; lean_object* v_auxDeclNGen_4570_; lean_object* v_cache_4571_; lean_object* v_messages_4572_; lean_object* v_infoState_4573_; lean_object* v_snapshotTasks_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4604_; 
v___x_4565_ = lean_st_ref_take(v___y_4557_);
v_traceState_4566_ = lean_ctor_get(v___x_4565_, 4);
v_env_4567_ = lean_ctor_get(v___x_4565_, 0);
v_nextMacroScope_4568_ = lean_ctor_get(v___x_4565_, 1);
v_ngen_4569_ = lean_ctor_get(v___x_4565_, 2);
v_auxDeclNGen_4570_ = lean_ctor_get(v___x_4565_, 3);
v_cache_4571_ = lean_ctor_get(v___x_4565_, 5);
v_messages_4572_ = lean_ctor_get(v___x_4565_, 6);
v_infoState_4573_ = lean_ctor_get(v___x_4565_, 7);
v_snapshotTasks_4574_ = lean_ctor_get(v___x_4565_, 8);
v_isSharedCheck_4604_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4604_ == 0)
{
v___x_4576_ = v___x_4565_;
v_isShared_4577_ = v_isSharedCheck_4604_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_snapshotTasks_4574_);
lean_inc(v_infoState_4573_);
lean_inc(v_messages_4572_);
lean_inc(v_cache_4571_);
lean_inc(v_traceState_4566_);
lean_inc(v_auxDeclNGen_4570_);
lean_inc(v_ngen_4569_);
lean_inc(v_nextMacroScope_4568_);
lean_inc(v_env_4567_);
lean_dec(v___x_4565_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4604_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
uint64_t v_tid_4578_; lean_object* v_traces_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4603_; 
v_tid_4578_ = lean_ctor_get_uint64(v_traceState_4566_, sizeof(void*)*1);
v_traces_4579_ = lean_ctor_get(v_traceState_4566_, 0);
v_isSharedCheck_4603_ = !lean_is_exclusive(v_traceState_4566_);
if (v_isSharedCheck_4603_ == 0)
{
v___x_4581_ = v_traceState_4566_;
v_isShared_4582_ = v_isSharedCheck_4603_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_traces_4579_);
lean_dec(v_traceState_4566_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4603_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4583_; double v___x_4584_; uint8_t v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4593_; 
v___x_4583_ = lean_box(0);
v___x_4584_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4585_ = 0;
v___x_4586_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4587_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4587_, 0, v_cls_4552_);
lean_ctor_set(v___x_4587_, 1, v___x_4583_);
lean_ctor_set(v___x_4587_, 2, v___x_4586_);
lean_ctor_set_float(v___x_4587_, sizeof(void*)*3, v___x_4584_);
lean_ctor_set_float(v___x_4587_, sizeof(void*)*3 + 8, v___x_4584_);
lean_ctor_set_uint8(v___x_4587_, sizeof(void*)*3 + 16, v___x_4585_);
v___x_4588_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4589_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4589_, 0, v___x_4587_);
lean_ctor_set(v___x_4589_, 1, v_a_4561_);
lean_ctor_set(v___x_4589_, 2, v___x_4588_);
lean_inc(v_ref_4559_);
v___x_4590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4590_, 0, v_ref_4559_);
lean_ctor_set(v___x_4590_, 1, v___x_4589_);
v___x_4591_ = l_Lean_PersistentArray_push___redArg(v_traces_4579_, v___x_4590_);
if (v_isShared_4582_ == 0)
{
lean_ctor_set(v___x_4581_, 0, v___x_4591_);
v___x_4593_ = v___x_4581_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4591_);
lean_ctor_set_uint64(v_reuseFailAlloc_4602_, sizeof(void*)*1, v_tid_4578_);
v___x_4593_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
lean_object* v___x_4595_; 
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 4, v___x_4593_);
v___x_4595_ = v___x_4576_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v_env_4567_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_nextMacroScope_4568_);
lean_ctor_set(v_reuseFailAlloc_4601_, 2, v_ngen_4569_);
lean_ctor_set(v_reuseFailAlloc_4601_, 3, v_auxDeclNGen_4570_);
lean_ctor_set(v_reuseFailAlloc_4601_, 4, v___x_4593_);
lean_ctor_set(v_reuseFailAlloc_4601_, 5, v_cache_4571_);
lean_ctor_set(v_reuseFailAlloc_4601_, 6, v_messages_4572_);
lean_ctor_set(v_reuseFailAlloc_4601_, 7, v_infoState_4573_);
lean_ctor_set(v_reuseFailAlloc_4601_, 8, v_snapshotTasks_4574_);
v___x_4595_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4599_; 
v___x_4596_ = lean_st_ref_put(v___y_4557_, v___x_4595_);
v___x_4597_ = lean_box(0);
if (v_isShared_4564_ == 0)
{
lean_ctor_set(v___x_4563_, 0, v___x_4597_);
v___x_4599_ = v___x_4563_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4606_, lean_object* v_msg_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_){
_start:
{
lean_object* v_res_4613_; 
v_res_4613_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4606_, v_msg_4607_, v___y_4608_, v___y_4609_, v___y_4610_, v___y_4611_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
lean_dec(v___y_4609_);
lean_dec_ref(v___y_4608_);
return v_res_4613_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4616_ = l_Lean_stringToMessageData(v___x_4615_);
return v___x_4616_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4618_; lean_object* v___x_4619_; 
v___x_4618_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4619_ = l_Lean_stringToMessageData(v___x_4618_);
return v___x_4619_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4621_; lean_object* v___x_4622_; 
v___x_4621_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4622_ = l_Lean_stringToMessageData(v___x_4621_);
return v___x_4622_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; 
v___x_4624_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4625_ = l_Lean_stringToMessageData(v___x_4624_);
return v___x_4625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4626_, lean_object* v_e_4627_, lean_object* v___x_4628_, lean_object* v___x_4629_, lean_object* v_cls_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = lean_st_mk_ref(v___x_4626_);
v___x_4637_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4627_, v___x_4628_, v___x_4636_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4637_) == 0)
{
lean_object* v_a_4638_; lean_object* v___x_4640_; uint8_t v_isShared_4641_; uint8_t v_isSharedCheck_4709_; 
v_a_4638_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4709_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4709_ == 0)
{
v___x_4640_ = v___x_4637_;
v_isShared_4641_ = v_isSharedCheck_4709_;
goto v_resetjp_4639_;
}
else
{
lean_inc(v_a_4638_);
lean_dec(v___x_4637_);
v___x_4640_ = lean_box(0);
v_isShared_4641_ = v_isSharedCheck_4709_;
goto v_resetjp_4639_;
}
v_resetjp_4639_:
{
lean_object* v___x_4642_; lean_object* v_count_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4707_; 
v___x_4642_ = lean_st_ref_get(v___x_4636_);
lean_dec(v___x_4636_);
v_count_4643_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; 
v_unused_4708_ = lean_ctor_get(v___x_4642_, 1);
lean_dec(v_unused_4708_);
v___x_4645_ = v___x_4642_;
v_isShared_4646_ = v_isSharedCheck_4707_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_count_4643_);
lean_dec(v___x_4642_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4707_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
uint8_t v___x_4669_; 
v___x_4669_ = lean_nat_dec_eq(v_count_4643_, v___x_4629_);
if (v___x_4669_ == 0)
{
lean_object* v_toCold_4670_; lean_object* v_options_4671_; uint8_t v_hasTrace_4672_; 
v_toCold_4670_ = lean_ctor_get(v___y_4633_, 0);
v_options_4671_ = lean_ctor_get(v_toCold_4670_, 2);
v_hasTrace_4672_ = lean_ctor_get_uint8(v_options_4671_, sizeof(void*)*1);
if (v_hasTrace_4672_ == 0)
{
lean_dec(v_cls_4630_);
goto v___jp_4647_;
}
else
{
lean_object* v_inheritedTraceOptions_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v_inheritedTraceOptions_4673_ = lean_ctor_get(v_toCold_4670_, 11);
v___x_4674_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4630_);
v___x_4675_ = l_Lean_Name_append(v___x_4674_, v_cls_4630_);
v___x_4676_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4673_, v_options_4671_, v___x_4675_);
lean_dec(v___x_4675_);
if (v___x_4676_ == 0)
{
lean_dec(v_cls_4630_);
goto v___jp_4647_;
}
else
{
lean_object* v_expr_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; lean_object* v___x_4680_; lean_object* v___x_4681_; 
v_expr_4677_ = lean_ctor_get(v_a_4638_, 0);
v___x_4678_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4677_);
v___x_4679_ = l_Lean_indentExpr(v_expr_4677_);
v___x_4680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4680_, 0, v___x_4678_);
lean_ctor_set(v___x_4680_, 1, v___x_4679_);
v___x_4681_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4630_, v___x_4680_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_dec_ref_known(v___x_4681_, 1);
goto v___jp_4647_;
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_del_object(v___x_4645_);
lean_dec(v_count_4643_);
lean_del_object(v___x_4640_);
lean_dec(v_a_4638_);
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
}
}
else
{
lean_object* v_toCold_4690_; lean_object* v_options_4691_; uint8_t v_hasTrace_4692_; 
v_toCold_4690_ = lean_ctor_get(v___y_4633_, 0);
v_options_4691_ = lean_ctor_get(v_toCold_4690_, 2);
v_hasTrace_4692_ = lean_ctor_get_uint8(v_options_4691_, sizeof(void*)*1);
if (v_hasTrace_4692_ == 0)
{
lean_dec(v_cls_4630_);
goto v___jp_4647_;
}
else
{
lean_object* v_inheritedTraceOptions_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; uint8_t v___x_4696_; 
v_inheritedTraceOptions_4693_ = lean_ctor_get(v_toCold_4690_, 11);
v___x_4694_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4630_);
v___x_4695_ = l_Lean_Name_append(v___x_4694_, v_cls_4630_);
v___x_4696_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4693_, v_options_4691_, v___x_4695_);
lean_dec(v___x_4695_);
if (v___x_4696_ == 0)
{
lean_dec(v_cls_4630_);
goto v___jp_4647_;
}
else
{
lean_object* v___x_4697_; lean_object* v___x_4698_; 
v___x_4697_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4698_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4630_, v___x_4697_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
if (lean_obj_tag(v___x_4698_) == 0)
{
lean_dec_ref_known(v___x_4698_, 1);
goto v___jp_4647_;
}
else
{
lean_object* v_a_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4706_; 
lean_del_object(v___x_4645_);
lean_dec(v_count_4643_);
lean_del_object(v___x_4640_);
lean_dec(v_a_4638_);
v_a_4699_ = lean_ctor_get(v___x_4698_, 0);
v_isSharedCheck_4706_ = !lean_is_exclusive(v___x_4698_);
if (v_isSharedCheck_4706_ == 0)
{
v___x_4701_ = v___x_4698_;
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_a_4699_);
lean_dec(v___x_4698_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4706_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
lean_object* v___x_4704_; 
if (v_isShared_4702_ == 0)
{
v___x_4704_ = v___x_4701_;
goto v_reusejp_4703_;
}
else
{
lean_object* v_reuseFailAlloc_4705_; 
v_reuseFailAlloc_4705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4705_, 0, v_a_4699_);
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
v___jp_4647_:
{
lean_object* v_expr_4648_; lean_object* v___x_4650_; uint8_t v_isShared_4651_; uint8_t v_isSharedCheck_4667_; 
v_expr_4648_ = lean_ctor_get(v_a_4638_, 0);
v_isSharedCheck_4667_ = !lean_is_exclusive(v_a_4638_);
if (v_isSharedCheck_4667_ == 0)
{
lean_object* v_unused_4668_; 
v_unused_4668_ = lean_ctor_get(v_a_4638_, 1);
lean_dec(v_unused_4668_);
v___x_4650_ = v_a_4638_;
v_isShared_4651_ = v_isSharedCheck_4667_;
goto v_resetjp_4649_;
}
else
{
lean_inc(v_expr_4648_);
lean_dec(v_a_4638_);
v___x_4650_ = lean_box(0);
v_isShared_4651_ = v_isSharedCheck_4667_;
goto v_resetjp_4649_;
}
v_resetjp_4649_:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; lean_object* v___x_4655_; lean_object* v___x_4657_; 
v___x_4652_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4653_ = l_Nat_reprFast(v_count_4643_);
v___x_4654_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4654_, 0, v___x_4653_);
v___x_4655_ = l_Lean_MessageData_ofFormat(v___x_4654_);
if (v_isShared_4651_ == 0)
{
lean_ctor_set_tag(v___x_4650_, 7);
lean_ctor_set(v___x_4650_, 1, v___x_4655_);
lean_ctor_set(v___x_4650_, 0, v___x_4652_);
v___x_4657_ = v___x_4650_;
goto v_reusejp_4656_;
}
else
{
lean_object* v_reuseFailAlloc_4666_; 
v_reuseFailAlloc_4666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4666_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4666_, 1, v___x_4655_);
v___x_4657_ = v_reuseFailAlloc_4666_;
goto v_reusejp_4656_;
}
v_reusejp_4656_:
{
lean_object* v___x_4658_; lean_object* v___x_4660_; 
v___x_4658_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4646_ == 0)
{
lean_ctor_set_tag(v___x_4645_, 7);
lean_ctor_set(v___x_4645_, 1, v___x_4658_);
lean_ctor_set(v___x_4645_, 0, v___x_4657_);
v___x_4660_ = v___x_4645_;
goto v_reusejp_4659_;
}
else
{
lean_object* v_reuseFailAlloc_4665_; 
v_reuseFailAlloc_4665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4665_, 0, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4665_, 1, v___x_4658_);
v___x_4660_ = v_reuseFailAlloc_4665_;
goto v_reusejp_4659_;
}
v_reusejp_4659_:
{
lean_object* v___x_4661_; lean_object* v___x_4663_; 
v___x_4661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4661_, 0, v_expr_4648_);
lean_ctor_set(v___x_4661_, 1, v___x_4660_);
if (v_isShared_4641_ == 0)
{
lean_ctor_set(v___x_4640_, 0, v___x_4661_);
v___x_4663_ = v___x_4640_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v___x_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
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
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4717_; 
lean_dec(v___x_4636_);
lean_dec(v_cls_4630_);
v_a_4710_ = lean_ctor_get(v___x_4637_, 0);
v_isSharedCheck_4717_ = !lean_is_exclusive(v___x_4637_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4712_ = v___x_4637_;
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4637_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4717_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4715_; 
if (v_isShared_4713_ == 0)
{
v___x_4715_ = v___x_4712_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v_a_4710_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4718_, lean_object* v_e_4719_, lean_object* v___x_4720_, lean_object* v___x_4721_, lean_object* v_cls_4722_, lean_object* v___y_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v_res_4728_; 
v_res_4728_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4718_, v_e_4719_, v___x_4720_, v___x_4721_, v_cls_4722_, v___y_4723_, v___y_4724_, v___y_4725_, v___y_4726_);
lean_dec(v___y_4726_);
lean_dec_ref(v___y_4725_);
lean_dec(v___y_4724_);
lean_dec_ref(v___y_4723_);
lean_dec(v___x_4721_);
lean_dec(v___x_4720_);
return v_res_4728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4729_, lean_object* v_cache_4730_, lean_object* v_a_x3f_4731_){
_start:
{
lean_object* v___x_4733_; lean_object* v_mctx_4734_; lean_object* v_zetaDeltaFVarIds_4735_; lean_object* v_postponed_4736_; lean_object* v_diag_4737_; lean_object* v___x_4739_; uint8_t v_isShared_4740_; uint8_t v_isSharedCheck_4747_; 
v___x_4733_ = lean_st_ref_take(v___y_4729_);
v_mctx_4734_ = lean_ctor_get(v___x_4733_, 0);
v_zetaDeltaFVarIds_4735_ = lean_ctor_get(v___x_4733_, 2);
v_postponed_4736_ = lean_ctor_get(v___x_4733_, 3);
v_diag_4737_ = lean_ctor_get(v___x_4733_, 4);
v_isSharedCheck_4747_ = !lean_is_exclusive(v___x_4733_);
if (v_isSharedCheck_4747_ == 0)
{
lean_object* v_unused_4748_; 
v_unused_4748_ = lean_ctor_get(v___x_4733_, 1);
lean_dec(v_unused_4748_);
v___x_4739_ = v___x_4733_;
v_isShared_4740_ = v_isSharedCheck_4747_;
goto v_resetjp_4738_;
}
else
{
lean_inc(v_diag_4737_);
lean_inc(v_postponed_4736_);
lean_inc(v_zetaDeltaFVarIds_4735_);
lean_inc(v_mctx_4734_);
lean_dec(v___x_4733_);
v___x_4739_ = lean_box(0);
v_isShared_4740_ = v_isSharedCheck_4747_;
goto v_resetjp_4738_;
}
v_resetjp_4738_:
{
lean_object* v___x_4742_; 
if (v_isShared_4740_ == 0)
{
lean_ctor_set(v___x_4739_, 1, v_cache_4730_);
v___x_4742_ = v___x_4739_;
goto v_reusejp_4741_;
}
else
{
lean_object* v_reuseFailAlloc_4746_; 
v_reuseFailAlloc_4746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4746_, 0, v_mctx_4734_);
lean_ctor_set(v_reuseFailAlloc_4746_, 1, v_cache_4730_);
lean_ctor_set(v_reuseFailAlloc_4746_, 2, v_zetaDeltaFVarIds_4735_);
lean_ctor_set(v_reuseFailAlloc_4746_, 3, v_postponed_4736_);
lean_ctor_set(v_reuseFailAlloc_4746_, 4, v_diag_4737_);
v___x_4742_ = v_reuseFailAlloc_4746_;
goto v_reusejp_4741_;
}
v_reusejp_4741_:
{
lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4743_ = lean_st_ref_put(v___y_4729_, v___x_4742_);
v___x_4744_ = lean_box(0);
v___x_4745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4745_, 0, v___x_4744_);
return v___x_4745_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4749_, lean_object* v_cache_4750_, lean_object* v_a_x3f_4751_, lean_object* v___y_4752_){
_start:
{
lean_object* v_res_4753_; 
v_res_4753_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4749_, v_cache_4750_, v_a_x3f_4751_);
lean_dec(v_a_x3f_4751_);
lean_dec(v___y_4749_);
return v_res_4753_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0(void){
_start:
{
uint8_t v___x_4754_; lean_object* v___x_4755_; 
v___x_4754_ = 2;
v___x_4755_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_4754_);
return v___x_4755_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_4756_, lean_object* v___f_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_, lean_object* v___y_4761_){
_start:
{
lean_object* v___x_4808_; uint8_t v_beta_4809_; 
v___x_4808_ = l_Lean_Meta_Context_config(v___y_4758_);
v_beta_4809_ = lean_ctor_get_uint8(v___x_4808_, 13);
if (v_beta_4809_ == 0)
{
lean_dec_ref(v___x_4808_);
goto v___jp_4763_;
}
else
{
uint8_t v_iota_4810_; 
v_iota_4810_ = lean_ctor_get_uint8(v___x_4808_, 12);
if (v_iota_4810_ == 0)
{
lean_dec_ref(v___x_4808_);
goto v___jp_4763_;
}
else
{
uint8_t v_zeta_4811_; 
v_zeta_4811_ = lean_ctor_get_uint8(v___x_4808_, 15);
if (v_zeta_4811_ == 0)
{
lean_dec_ref(v___x_4808_);
goto v___jp_4763_;
}
else
{
uint8_t v_zetaHave_4812_; 
v_zetaHave_4812_ = lean_ctor_get_uint8(v___x_4808_, 18);
if (v_zetaHave_4812_ == 0)
{
lean_dec_ref(v___x_4808_);
goto v___jp_4763_;
}
else
{
uint8_t v_zetaDelta_4813_; 
v_zetaDelta_4813_ = lean_ctor_get_uint8(v___x_4808_, 16);
if (v_zetaDelta_4813_ == 0)
{
lean_dec_ref(v___x_4808_);
goto v___jp_4763_;
}
else
{
uint8_t v_etaStruct_4814_; uint8_t v_proj_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; uint8_t v___x_4818_; 
v_etaStruct_4814_ = lean_ctor_get_uint8(v___x_4808_, 10);
v_proj_4815_ = lean_ctor_get_uint8(v___x_4808_, 14);
lean_dec_ref(v___x_4808_);
v___x_4816_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_4815_);
v___x_4817_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0);
v___x_4818_ = lean_nat_dec_eq(v___x_4816_, v___x_4817_);
lean_dec(v___x_4816_);
if (v___x_4818_ == 0)
{
goto v___jp_4763_;
}
else
{
uint8_t v___x_4819_; uint8_t v___x_4820_; 
v___x_4819_ = 0;
v___x_4820_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4814_, v___x_4819_);
if (v___x_4820_ == 0)
{
goto v___jp_4763_;
}
else
{
lean_object* v___x_4821_; 
v___x_4821_ = lean_apply_5(v___f_4757_, v___y_4758_, v___y_4759_, v___y_4760_, v___y_4761_, lean_box(0));
return v___x_4821_;
}
}
}
}
}
}
}
v___jp_4763_:
{
lean_object* v___x_4764_; uint8_t v_foApprox_4765_; uint8_t v_ctxApprox_4766_; uint8_t v_quasiPatternApprox_4767_; uint8_t v_constApprox_4768_; uint8_t v_isDefEqStuckEx_4769_; uint8_t v_unificationHints_4770_; uint8_t v_proofIrrelevance_4771_; uint8_t v_assignSyntheticOpaque_4772_; uint8_t v_offsetCnstrs_4773_; uint8_t v_transparency_4774_; uint8_t v_univApprox_4775_; uint8_t v_zetaUnused_4776_; uint8_t v_canUnfoldPredicateConfig_4777_; lean_object* v___x_4779_; uint8_t v_isShared_4780_; uint8_t v_isSharedCheck_4807_; 
v___x_4764_ = l_Lean_Meta_Context_config(v___y_4758_);
v_foApprox_4765_ = lean_ctor_get_uint8(v___x_4764_, 0);
v_ctxApprox_4766_ = lean_ctor_get_uint8(v___x_4764_, 1);
v_quasiPatternApprox_4767_ = lean_ctor_get_uint8(v___x_4764_, 2);
v_constApprox_4768_ = lean_ctor_get_uint8(v___x_4764_, 3);
v_isDefEqStuckEx_4769_ = lean_ctor_get_uint8(v___x_4764_, 4);
v_unificationHints_4770_ = lean_ctor_get_uint8(v___x_4764_, 5);
v_proofIrrelevance_4771_ = lean_ctor_get_uint8(v___x_4764_, 6);
v_assignSyntheticOpaque_4772_ = lean_ctor_get_uint8(v___x_4764_, 7);
v_offsetCnstrs_4773_ = lean_ctor_get_uint8(v___x_4764_, 8);
v_transparency_4774_ = lean_ctor_get_uint8(v___x_4764_, 9);
v_univApprox_4775_ = lean_ctor_get_uint8(v___x_4764_, 11);
v_zetaUnused_4776_ = lean_ctor_get_uint8(v___x_4764_, 17);
v_canUnfoldPredicateConfig_4777_ = lean_ctor_get_uint8(v___x_4764_, 19);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4764_);
if (v_isSharedCheck_4807_ == 0)
{
v___x_4779_ = v___x_4764_;
v_isShared_4780_ = v_isSharedCheck_4807_;
goto v_resetjp_4778_;
}
else
{
lean_dec(v___x_4764_);
v___x_4779_ = lean_box(0);
v_isShared_4780_ = v_isSharedCheck_4807_;
goto v_resetjp_4778_;
}
v_resetjp_4778_:
{
uint8_t v___x_4781_; uint8_t v___x_4782_; lean_object* v___x_4784_; 
v___x_4781_ = 0;
v___x_4782_ = 2;
if (v_isShared_4780_ == 0)
{
v___x_4784_ = v___x_4779_;
goto v_reusejp_4783_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 0, v_foApprox_4765_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 1, v_ctxApprox_4766_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 2, v_quasiPatternApprox_4767_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 3, v_constApprox_4768_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 4, v_isDefEqStuckEx_4769_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 5, v_unificationHints_4770_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 6, v_proofIrrelevance_4771_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 7, v_assignSyntheticOpaque_4772_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 8, v_offsetCnstrs_4773_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 9, v_transparency_4774_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 11, v_univApprox_4775_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 17, v_zetaUnused_4776_);
lean_ctor_set_uint8(v_reuseFailAlloc_4806_, 19, v_canUnfoldPredicateConfig_4777_);
v___x_4784_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4783_;
}
v_reusejp_4783_:
{
uint8_t v_trackZetaDelta_4785_; lean_object* v_zetaDeltaSet_4786_; lean_object* v_lctx_4787_; lean_object* v_localInstances_4788_; lean_object* v_defEqCtx_x3f_4789_; lean_object* v_synthPendingDepth_4790_; lean_object* v_customCanUnfoldPredicate_x3f_4791_; uint8_t v_univApprox_4792_; uint8_t v_inTypeClassResolution_4793_; uint8_t v_cacheInferType_4794_; lean_object* v___x_4796_; uint8_t v_isShared_4797_; uint8_t v_isSharedCheck_4804_; 
lean_ctor_set_uint8(v___x_4784_, 10, v___x_4781_);
lean_ctor_set_uint8(v___x_4784_, 12, v___x_4756_);
lean_ctor_set_uint8(v___x_4784_, 13, v___x_4756_);
lean_ctor_set_uint8(v___x_4784_, 14, v___x_4782_);
lean_ctor_set_uint8(v___x_4784_, 15, v___x_4756_);
lean_ctor_set_uint8(v___x_4784_, 16, v___x_4756_);
lean_ctor_set_uint8(v___x_4784_, 18, v___x_4756_);
v_trackZetaDelta_4785_ = lean_ctor_get_uint8(v___y_4758_, sizeof(void*)*7);
v_zetaDeltaSet_4786_ = lean_ctor_get(v___y_4758_, 1);
v_lctx_4787_ = lean_ctor_get(v___y_4758_, 2);
v_localInstances_4788_ = lean_ctor_get(v___y_4758_, 3);
v_defEqCtx_x3f_4789_ = lean_ctor_get(v___y_4758_, 4);
v_synthPendingDepth_4790_ = lean_ctor_get(v___y_4758_, 5);
v_customCanUnfoldPredicate_x3f_4791_ = lean_ctor_get(v___y_4758_, 6);
v_univApprox_4792_ = lean_ctor_get_uint8(v___y_4758_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4793_ = lean_ctor_get_uint8(v___y_4758_, sizeof(void*)*7 + 2);
v_cacheInferType_4794_ = lean_ctor_get_uint8(v___y_4758_, sizeof(void*)*7 + 3);
v_isSharedCheck_4804_ = !lean_is_exclusive(v___y_4758_);
if (v_isSharedCheck_4804_ == 0)
{
lean_object* v_unused_4805_; 
v_unused_4805_ = lean_ctor_get(v___y_4758_, 0);
lean_dec(v_unused_4805_);
v___x_4796_ = v___y_4758_;
v_isShared_4797_ = v_isSharedCheck_4804_;
goto v_resetjp_4795_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4791_);
lean_inc(v_synthPendingDepth_4790_);
lean_inc(v_defEqCtx_x3f_4789_);
lean_inc(v_localInstances_4788_);
lean_inc(v_lctx_4787_);
lean_inc(v_zetaDeltaSet_4786_);
lean_dec(v___y_4758_);
v___x_4796_ = lean_box(0);
v_isShared_4797_ = v_isSharedCheck_4804_;
goto v_resetjp_4795_;
}
v_resetjp_4795_:
{
uint64_t v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4801_; 
v___x_4798_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4784_);
v___x_4799_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4799_, 0, v___x_4784_);
lean_ctor_set_uint64(v___x_4799_, sizeof(void*)*1, v___x_4798_);
if (v_isShared_4797_ == 0)
{
lean_ctor_set(v___x_4796_, 0, v___x_4799_);
v___x_4801_ = v___x_4796_;
goto v_reusejp_4800_;
}
else
{
lean_object* v_reuseFailAlloc_4803_; 
v_reuseFailAlloc_4803_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4799_);
lean_ctor_set(v_reuseFailAlloc_4803_, 1, v_zetaDeltaSet_4786_);
lean_ctor_set(v_reuseFailAlloc_4803_, 2, v_lctx_4787_);
lean_ctor_set(v_reuseFailAlloc_4803_, 3, v_localInstances_4788_);
lean_ctor_set(v_reuseFailAlloc_4803_, 4, v_defEqCtx_x3f_4789_);
lean_ctor_set(v_reuseFailAlloc_4803_, 5, v_synthPendingDepth_4790_);
lean_ctor_set(v_reuseFailAlloc_4803_, 6, v_customCanUnfoldPredicate_x3f_4791_);
lean_ctor_set_uint8(v_reuseFailAlloc_4803_, sizeof(void*)*7, v_trackZetaDelta_4785_);
lean_ctor_set_uint8(v_reuseFailAlloc_4803_, sizeof(void*)*7 + 1, v_univApprox_4792_);
lean_ctor_set_uint8(v_reuseFailAlloc_4803_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4793_);
lean_ctor_set_uint8(v_reuseFailAlloc_4803_, sizeof(void*)*7 + 3, v_cacheInferType_4794_);
v___x_4801_ = v_reuseFailAlloc_4803_;
goto v_reusejp_4800_;
}
v_reusejp_4800_:
{
lean_object* v___x_4802_; 
v___x_4802_ = lean_apply_5(v___f_4757_, v___x_4801_, v___y_4759_, v___y_4760_, v___y_4761_, lean_box(0));
return v___x_4802_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_4822_, lean_object* v___f_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
uint8_t v___x_14004__boxed_4829_; lean_object* v_res_4830_; 
v___x_14004__boxed_4829_ = lean_unbox(v___x_4822_);
v_res_4830_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_14004__boxed_4829_, v___f_4823_, v___y_4824_, v___y_4825_, v___y_4826_, v___y_4827_);
return v_res_4830_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1));
v___x_4835_ = l_Lean_MessageData_ofFormat(v___x_4834_);
return v___x_4835_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3(void){
_start:
{
lean_object* v___x_4836_; 
v___x_4836_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4836_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4837_; lean_object* v___x_4838_; 
v___x_4837_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___x_4838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4838_, 0, v___x_4837_);
return v___x_4838_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4839_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4840_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
lean_ctor_set(v___x_4840_, 1, v___x_4839_);
lean_ctor_set(v___x_4840_, 2, v___x_4839_);
lean_ctor_set(v___x_4840_, 3, v___x_4839_);
lean_ctor_set(v___x_4840_, 4, v___x_4839_);
lean_ctor_set(v___x_4840_, 5, v___x_4839_);
return v___x_4840_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6(void){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4841_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4842_ = lean_unsigned_to_nat(0u);
v___x_4843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
lean_ctor_set(v___x_4843_, 1, v___x_4841_);
return v___x_4843_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_4844_, lean_object* v_e_4845_, lean_object* v_cls_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_, lean_object* v___y_4849_, lean_object* v___y_4850_){
_start:
{
if (v___x_4844_ == 0)
{
lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; 
lean_dec(v_cls_4846_);
v___x_4852_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_4853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4853_, 0, v_e_4845_);
lean_ctor_set(v___x_4853_, 1, v___x_4852_);
v___x_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
return v___x_4854_;
}
else
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v_mctx_4857_; lean_object* v_zetaDeltaFVarIds_4858_; lean_object* v_postponed_4859_; lean_object* v_diag_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4957_; 
v___x_4855_ = lean_st_ref_get(v___y_4848_);
v___x_4856_ = lean_st_ref_take(v___y_4848_);
v_mctx_4857_ = lean_ctor_get(v___x_4856_, 0);
v_zetaDeltaFVarIds_4858_ = lean_ctor_get(v___x_4856_, 2);
v_postponed_4859_ = lean_ctor_get(v___x_4856_, 3);
v_diag_4860_ = lean_ctor_get(v___x_4856_, 4);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v___x_4856_, 1);
lean_dec(v_unused_4958_);
v___x_4862_ = v___x_4856_;
v_isShared_4863_ = v_isSharedCheck_4957_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_diag_4860_);
lean_inc(v_postponed_4859_);
lean_inc(v_zetaDeltaFVarIds_4858_);
lean_inc(v_mctx_4857_);
lean_dec(v___x_4856_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4957_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4864_; lean_object* v___x_4866_; 
v___x_4864_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
if (v_isShared_4863_ == 0)
{
lean_ctor_set(v___x_4862_, 1, v___x_4864_);
v___x_4866_ = v___x_4862_;
goto v_reusejp_4865_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_mctx_4857_);
lean_ctor_set(v_reuseFailAlloc_4956_, 1, v___x_4864_);
lean_ctor_set(v_reuseFailAlloc_4956_, 2, v_zetaDeltaFVarIds_4858_);
lean_ctor_set(v_reuseFailAlloc_4956_, 3, v_postponed_4859_);
lean_ctor_set(v_reuseFailAlloc_4956_, 4, v_diag_4860_);
v___x_4866_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4865_;
}
v_reusejp_4865_:
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v_mctx_4869_; lean_object* v_cache_4870_; lean_object* v_zetaDeltaFVarIds_4871_; lean_object* v_postponed_4872_; lean_object* v_diag_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4955_; 
v___x_4867_ = lean_st_ref_put(v___y_4848_, v___x_4866_);
v___x_4868_ = lean_st_ref_take(v___y_4848_);
v_mctx_4869_ = lean_ctor_get(v___x_4868_, 0);
v_cache_4870_ = lean_ctor_get(v___x_4868_, 1);
v_zetaDeltaFVarIds_4871_ = lean_ctor_get(v___x_4868_, 2);
v_postponed_4872_ = lean_ctor_get(v___x_4868_, 3);
v_diag_4873_ = lean_ctor_get(v___x_4868_, 4);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4875_ = v___x_4868_;
v_isShared_4876_ = v_isSharedCheck_4955_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_diag_4873_);
lean_inc(v_postponed_4872_);
lean_inc(v_zetaDeltaFVarIds_4871_);
lean_inc(v_cache_4870_);
lean_inc(v_mctx_4869_);
lean_dec(v___x_4868_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4955_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4877_ = lean_box(1);
if (v_isShared_4876_ == 0)
{
lean_ctor_set(v___x_4875_, 2, v___x_4877_);
v___x_4879_ = v___x_4875_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_mctx_4869_);
lean_ctor_set(v_reuseFailAlloc_4954_, 1, v_cache_4870_);
lean_ctor_set(v_reuseFailAlloc_4954_, 2, v___x_4877_);
lean_ctor_set(v_reuseFailAlloc_4954_, 3, v_postponed_4872_);
lean_ctor_set(v_reuseFailAlloc_4954_, 4, v_diag_4873_);
v___x_4879_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
lean_object* v___x_4880_; lean_object* v_cache_4881_; lean_object* v_keyedConfig_4882_; lean_object* v_zetaDeltaSet_4883_; lean_object* v_lctx_4884_; lean_object* v_localInstances_4885_; lean_object* v_defEqCtx_x3f_4886_; lean_object* v_synthPendingDepth_4887_; lean_object* v_customCanUnfoldPredicate_x3f_4888_; uint8_t v_univApprox_4889_; uint8_t v_inTypeClassResolution_4890_; uint8_t v_cacheInferType_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; uint8_t v_transparency_4894_; lean_object* v___x_4895_; uint8_t v___x_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___f_4899_; lean_object* v_a_4901_; lean_object* v_a_4913_; lean_object* v_a_4926_; lean_object* v___y_4930_; lean_object* v___y_4934_; uint8_t v___x_4937_; 
v___x_4880_ = lean_st_ref_put(v___y_4848_, v___x_4879_);
v_cache_4881_ = lean_ctor_get(v___x_4855_, 1);
lean_inc_ref(v_cache_4881_);
lean_dec(v___x_4855_);
v_keyedConfig_4882_ = lean_ctor_get(v___y_4847_, 0);
v_zetaDeltaSet_4883_ = lean_ctor_get(v___y_4847_, 1);
v_lctx_4884_ = lean_ctor_get(v___y_4847_, 2);
v_localInstances_4885_ = lean_ctor_get(v___y_4847_, 3);
v_defEqCtx_x3f_4886_ = lean_ctor_get(v___y_4847_, 4);
v_synthPendingDepth_4887_ = lean_ctor_get(v___y_4847_, 5);
v_customCanUnfoldPredicate_x3f_4888_ = lean_ctor_get(v___y_4847_, 6);
v_univApprox_4889_ = lean_ctor_get_uint8(v___y_4847_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4890_ = lean_ctor_get_uint8(v___y_4847_, sizeof(void*)*7 + 2);
v_cacheInferType_4891_ = lean_ctor_get_uint8(v___y_4847_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_4888_);
lean_inc(v_synthPendingDepth_4887_);
lean_inc(v_defEqCtx_x3f_4886_);
lean_inc_ref(v_localInstances_4885_);
lean_inc_ref(v_lctx_4884_);
lean_inc(v_zetaDeltaSet_4883_);
lean_inc_ref(v_keyedConfig_4882_);
v___x_4892_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4892_, 0, v_keyedConfig_4882_);
lean_ctor_set(v___x_4892_, 1, v_zetaDeltaSet_4883_);
lean_ctor_set(v___x_4892_, 2, v_lctx_4884_);
lean_ctor_set(v___x_4892_, 3, v_localInstances_4885_);
lean_ctor_set(v___x_4892_, 4, v_defEqCtx_x3f_4886_);
lean_ctor_set(v___x_4892_, 5, v_synthPendingDepth_4887_);
lean_ctor_set(v___x_4892_, 6, v_customCanUnfoldPredicate_x3f_4888_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*7, v___x_4844_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*7 + 1, v_univApprox_4889_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4890_);
lean_ctor_set_uint8(v___x_4892_, sizeof(void*)*7 + 3, v_cacheInferType_4891_);
v___x_4893_ = l_Lean_Meta_Context_config(v___x_4892_);
v_transparency_4894_ = lean_ctor_get_uint8(v___x_4893_, 9);
lean_dec_ref(v___x_4893_);
v___x_4895_ = lean_unsigned_to_nat(0u);
v___x_4896_ = 0;
v___x_4897_ = lean_box(0);
v___x_4898_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
v___f_4899_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4899_, 0, v___x_4898_);
lean_closure_set(v___f_4899_, 1, v_e_4845_);
lean_closure_set(v___f_4899_, 2, v___x_4897_);
lean_closure_set(v___f_4899_, 3, v___x_4895_);
lean_closure_set(v___f_4899_, 4, v_cls_4846_);
v___x_4937_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4894_, v___x_4896_);
if (v___x_4937_ == 0)
{
lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; uint8_t v_transparency_4941_; uint8_t v___x_4942_; uint8_t v___x_4943_; 
lean_dec_ref_known(v___x_4892_, 7);
lean_inc_ref(v_keyedConfig_4882_);
v___x_4938_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4896_, v_keyedConfig_4882_);
lean_inc(v_customCanUnfoldPredicate_x3f_4888_);
lean_inc(v_synthPendingDepth_4887_);
lean_inc(v_defEqCtx_x3f_4886_);
lean_inc_ref(v_localInstances_4885_);
lean_inc_ref(v_lctx_4884_);
lean_inc(v_zetaDeltaSet_4883_);
lean_inc_ref(v___x_4938_);
v___x_4939_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4939_, 0, v___x_4938_);
lean_ctor_set(v___x_4939_, 1, v_zetaDeltaSet_4883_);
lean_ctor_set(v___x_4939_, 2, v_lctx_4884_);
lean_ctor_set(v___x_4939_, 3, v_localInstances_4885_);
lean_ctor_set(v___x_4939_, 4, v_defEqCtx_x3f_4886_);
lean_ctor_set(v___x_4939_, 5, v_synthPendingDepth_4887_);
lean_ctor_set(v___x_4939_, 6, v_customCanUnfoldPredicate_x3f_4888_);
lean_ctor_set_uint8(v___x_4939_, sizeof(void*)*7, v___x_4844_);
lean_ctor_set_uint8(v___x_4939_, sizeof(void*)*7 + 1, v_univApprox_4889_);
lean_ctor_set_uint8(v___x_4939_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4890_);
lean_ctor_set_uint8(v___x_4939_, sizeof(void*)*7 + 3, v_cacheInferType_4891_);
v___x_4940_ = l_Lean_Meta_Context_config(v___x_4939_);
v_transparency_4941_ = lean_ctor_get_uint8(v___x_4940_, 9);
lean_dec_ref(v___x_4940_);
v___x_4942_ = 1;
v___x_4943_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4941_, v___x_4942_);
if (v___x_4943_ == 0)
{
lean_object* v___x_4944_; 
lean_dec_ref(v___x_4938_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
v___x_4944_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4844_, v___f_4899_, v___x_4939_, v___y_4848_, v___y_4849_, v___y_4850_);
v___y_4934_ = v___x_4944_;
goto v___jp_4933_;
}
else
{
lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
lean_dec_ref_known(v___x_4939_, 7);
v___x_4945_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4942_, v___x_4938_);
lean_inc(v_customCanUnfoldPredicate_x3f_4888_);
lean_inc(v_synthPendingDepth_4887_);
lean_inc(v_defEqCtx_x3f_4886_);
lean_inc_ref(v_localInstances_4885_);
lean_inc_ref(v_lctx_4884_);
lean_inc(v_zetaDeltaSet_4883_);
v___x_4946_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4946_, 0, v___x_4945_);
lean_ctor_set(v___x_4946_, 1, v_zetaDeltaSet_4883_);
lean_ctor_set(v___x_4946_, 2, v_lctx_4884_);
lean_ctor_set(v___x_4946_, 3, v_localInstances_4885_);
lean_ctor_set(v___x_4946_, 4, v_defEqCtx_x3f_4886_);
lean_ctor_set(v___x_4946_, 5, v_synthPendingDepth_4887_);
lean_ctor_set(v___x_4946_, 6, v_customCanUnfoldPredicate_x3f_4888_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*7, v___x_4844_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*7 + 1, v_univApprox_4889_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4890_);
lean_ctor_set_uint8(v___x_4946_, sizeof(void*)*7 + 3, v_cacheInferType_4891_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
v___x_4947_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4844_, v___f_4899_, v___x_4946_, v___y_4848_, v___y_4849_, v___y_4850_);
v___y_4934_ = v___x_4947_;
goto v___jp_4933_;
}
}
else
{
uint8_t v___x_4948_; uint8_t v___x_4949_; 
v___x_4948_ = 1;
v___x_4949_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4894_, v___x_4948_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; 
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
v___x_4950_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4937_, v___f_4899_, v___x_4892_, v___y_4848_, v___y_4849_, v___y_4850_);
v___y_4930_ = v___x_4950_;
goto v___jp_4929_;
}
else
{
lean_object* v___x_4951_; lean_object* v___x_4952_; lean_object* v___x_4953_; 
lean_dec_ref_known(v___x_4892_, 7);
lean_inc_ref(v_keyedConfig_4882_);
v___x_4951_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4948_, v_keyedConfig_4882_);
lean_inc(v_customCanUnfoldPredicate_x3f_4888_);
lean_inc(v_synthPendingDepth_4887_);
lean_inc(v_defEqCtx_x3f_4886_);
lean_inc_ref(v_localInstances_4885_);
lean_inc_ref(v_lctx_4884_);
lean_inc(v_zetaDeltaSet_4883_);
v___x_4952_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4952_, 0, v___x_4951_);
lean_ctor_set(v___x_4952_, 1, v_zetaDeltaSet_4883_);
lean_ctor_set(v___x_4952_, 2, v_lctx_4884_);
lean_ctor_set(v___x_4952_, 3, v_localInstances_4885_);
lean_ctor_set(v___x_4952_, 4, v_defEqCtx_x3f_4886_);
lean_ctor_set(v___x_4952_, 5, v_synthPendingDepth_4887_);
lean_ctor_set(v___x_4952_, 6, v_customCanUnfoldPredicate_x3f_4888_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7, v___x_4844_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7 + 1, v_univApprox_4889_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4890_);
lean_ctor_set_uint8(v___x_4952_, sizeof(void*)*7 + 3, v_cacheInferType_4891_);
lean_inc(v___y_4850_);
lean_inc_ref(v___y_4849_);
lean_inc(v___y_4848_);
v___x_4953_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4937_, v___f_4899_, v___x_4952_, v___y_4848_, v___y_4849_, v___y_4850_);
v___y_4930_ = v___x_4953_;
goto v___jp_4929_;
}
}
v___jp_4900_:
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
v___x_4902_ = lean_box(0);
v___x_4903_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4848_, v_cache_4881_, v___x_4902_);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4910_ == 0)
{
lean_object* v_unused_4911_; 
v_unused_4911_ = lean_ctor_get(v___x_4903_, 0);
lean_dec(v_unused_4911_);
v___x_4905_ = v___x_4903_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_dec(v___x_4903_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
lean_ctor_set_tag(v___x_4905_, 1);
lean_ctor_set(v___x_4905_, 0, v_a_4901_);
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4901_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
v___jp_4912_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_inc(v_a_4913_);
v___x_4914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4914_, 0, v_a_4913_);
v___x_4915_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4848_, v_zetaDeltaFVarIds_4871_, v___x_4914_);
lean_dec_ref(v___x_4915_);
v___x_4916_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4848_, v_cache_4881_, v___x_4914_);
lean_dec_ref_known(v___x_4914_, 1);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4916_);
if (v_isSharedCheck_4923_ == 0)
{
lean_object* v_unused_4924_; 
v_unused_4924_ = lean_ctor_get(v___x_4916_, 0);
lean_dec(v_unused_4924_);
v___x_4918_ = v___x_4916_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_dec(v___x_4916_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
lean_ctor_set(v___x_4918_, 0, v_a_4913_);
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4913_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
v___jp_4925_:
{
lean_object* v___x_4927_; lean_object* v___x_4928_; 
v___x_4927_ = lean_box(0);
v___x_4928_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4848_, v_zetaDeltaFVarIds_4871_, v___x_4927_);
lean_dec_ref(v___x_4928_);
v_a_4901_ = v_a_4926_;
goto v___jp_4900_;
}
v___jp_4929_:
{
if (lean_obj_tag(v___y_4930_) == 0)
{
lean_object* v_a_4931_; 
v_a_4931_ = lean_ctor_get(v___y_4930_, 0);
lean_inc(v_a_4931_);
lean_dec_ref_known(v___y_4930_, 1);
v_a_4913_ = v_a_4931_;
goto v___jp_4912_;
}
else
{
lean_object* v_a_4932_; 
v_a_4932_ = lean_ctor_get(v___y_4930_, 0);
lean_inc(v_a_4932_);
lean_dec_ref_known(v___y_4930_, 1);
v_a_4926_ = v_a_4932_;
goto v___jp_4925_;
}
}
v___jp_4933_:
{
if (lean_obj_tag(v___y_4934_) == 0)
{
lean_object* v_a_4935_; 
v_a_4935_ = lean_ctor_get(v___y_4934_, 0);
lean_inc(v_a_4935_);
lean_dec_ref_known(v___y_4934_, 1);
v_a_4913_ = v_a_4935_;
goto v___jp_4912_;
}
else
{
lean_object* v_a_4936_; 
v_a_4936_ = lean_ctor_get(v___y_4934_, 0);
lean_inc(v_a_4936_);
lean_dec_ref_known(v___y_4934_, 1);
v_a_4926_ = v_a_4936_;
goto v___jp_4925_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_4959_, lean_object* v_e_4960_, lean_object* v_cls_4961_, lean_object* v___y_4962_, lean_object* v___y_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
uint8_t v___x_14127__boxed_4967_; lean_object* v_res_4968_; 
v___x_14127__boxed_4967_ = lean_unbox(v___x_4959_);
v_res_4968_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14127__boxed_4967_, v_e_4960_, v_cls_4961_, v___y_4962_, v___y_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v___y_4963_);
lean_dec_ref(v___y_4962_);
return v_res_4968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
if (lean_obj_tag(v_x_4969_) == 0)
{
lean_object* v_a_4975_; lean_object* v___x_4977_; uint8_t v_isShared_4978_; uint8_t v_isSharedCheck_4983_; 
v_a_4975_ = lean_ctor_get(v_x_4969_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v_x_4969_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4977_ = v_x_4969_;
v_isShared_4978_ = v_isSharedCheck_4983_;
goto v_resetjp_4976_;
}
else
{
lean_inc(v_a_4975_);
lean_dec(v_x_4969_);
v___x_4977_ = lean_box(0);
v_isShared_4978_ = v_isSharedCheck_4983_;
goto v_resetjp_4976_;
}
v_resetjp_4976_:
{
lean_object* v___x_4979_; lean_object* v___x_4981_; 
v___x_4979_ = l_Lean_Exception_toMessageData(v_a_4975_);
if (v_isShared_4978_ == 0)
{
lean_ctor_set(v___x_4977_, 0, v___x_4979_);
v___x_4981_ = v___x_4977_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v___x_4979_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
else
{
lean_object* v_a_4984_; lean_object* v___x_4986_; uint8_t v_isShared_4987_; uint8_t v_isSharedCheck_4992_; 
v_a_4984_ = lean_ctor_get(v_x_4969_, 0);
v_isSharedCheck_4992_ = !lean_is_exclusive(v_x_4969_);
if (v_isSharedCheck_4992_ == 0)
{
v___x_4986_ = v_x_4969_;
v_isShared_4987_ = v_isSharedCheck_4992_;
goto v_resetjp_4985_;
}
else
{
lean_inc(v_a_4984_);
lean_dec(v_x_4969_);
v___x_4986_ = lean_box(0);
v_isShared_4987_ = v_isSharedCheck_4992_;
goto v_resetjp_4985_;
}
v_resetjp_4985_:
{
lean_object* v_snd_4988_; lean_object* v___x_4990_; 
v_snd_4988_ = lean_ctor_get(v_a_4984_, 1);
lean_inc(v_snd_4988_);
lean_dec(v_a_4984_);
if (v_isShared_4987_ == 0)
{
lean_ctor_set_tag(v___x_4986_, 0);
lean_ctor_set(v___x_4986_, 0, v_snd_4988_);
v___x_4990_ = v___x_4986_;
goto v_reusejp_4989_;
}
else
{
lean_object* v_reuseFailAlloc_4991_; 
v_reuseFailAlloc_4991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4991_, 0, v_snd_4988_);
v___x_4990_ = v_reuseFailAlloc_4991_;
goto v_reusejp_4989_;
}
v_reusejp_4989_:
{
return v___x_4990_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_4993_, lean_object* v___y_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v_res_4999_; 
v_res_4999_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_4993_, v___y_4994_, v___y_4995_, v___y_4996_, v___y_4997_);
lean_dec(v___y_4997_);
lean_dec_ref(v___y_4996_);
lean_dec(v___y_4995_);
lean_dec_ref(v___y_4994_);
return v_res_4999_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5000_){
_start:
{
if (lean_obj_tag(v_x_5000_) == 0)
{
lean_object* v_a_5002_; lean_object* v___x_5004_; uint8_t v_isShared_5005_; uint8_t v_isSharedCheck_5009_; 
v_a_5002_ = lean_ctor_get(v_x_5000_, 0);
v_isSharedCheck_5009_ = !lean_is_exclusive(v_x_5000_);
if (v_isSharedCheck_5009_ == 0)
{
v___x_5004_ = v_x_5000_;
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
else
{
lean_inc(v_a_5002_);
lean_dec(v_x_5000_);
v___x_5004_ = lean_box(0);
v_isShared_5005_ = v_isSharedCheck_5009_;
goto v_resetjp_5003_;
}
v_resetjp_5003_:
{
lean_object* v___x_5007_; 
if (v_isShared_5005_ == 0)
{
lean_ctor_set_tag(v___x_5004_, 1);
v___x_5007_ = v___x_5004_;
goto v_reusejp_5006_;
}
else
{
lean_object* v_reuseFailAlloc_5008_; 
v_reuseFailAlloc_5008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5008_, 0, v_a_5002_);
v___x_5007_ = v_reuseFailAlloc_5008_;
goto v_reusejp_5006_;
}
v_reusejp_5006_:
{
return v___x_5007_;
}
}
}
else
{
lean_object* v_a_5010_; lean_object* v___x_5012_; uint8_t v_isShared_5013_; uint8_t v_isSharedCheck_5017_; 
v_a_5010_ = lean_ctor_get(v_x_5000_, 0);
v_isSharedCheck_5017_ = !lean_is_exclusive(v_x_5000_);
if (v_isSharedCheck_5017_ == 0)
{
v___x_5012_ = v_x_5000_;
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
else
{
lean_inc(v_a_5010_);
lean_dec(v_x_5000_);
v___x_5012_ = lean_box(0);
v_isShared_5013_ = v_isSharedCheck_5017_;
goto v_resetjp_5011_;
}
v_resetjp_5011_:
{
lean_object* v___x_5015_; 
if (v_isShared_5013_ == 0)
{
lean_ctor_set_tag(v___x_5012_, 0);
v___x_5015_ = v___x_5012_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5018_, lean_object* v___y_5019_){
_start:
{
lean_object* v_res_5020_; 
v_res_5020_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5018_);
return v_res_5020_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5021_){
_start:
{
if (lean_obj_tag(v_e_5021_) == 0)
{
uint8_t v___x_5022_; 
v___x_5022_ = 2;
return v___x_5022_;
}
else
{
uint8_t v___x_5023_; 
v___x_5023_ = 0;
return v___x_5023_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5024_){
_start:
{
uint8_t v_res_5025_; lean_object* v_r_5026_; 
v_res_5025_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5024_);
lean_dec_ref(v_e_5024_);
v_r_5026_ = lean_box(v_res_5025_);
return v_r_5026_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5027_, lean_object* v_data_5028_, lean_object* v_ref_5029_, lean_object* v_msg_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_toCold_5036_; lean_object* v_currRecDepth_5037_; lean_object* v_ref_5038_; uint8_t v_diag_5039_; uint8_t v_suppressElabErrors_5040_; lean_object* v___x_5041_; lean_object* v_traceState_5042_; lean_object* v_traces_5043_; lean_object* v_ref_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; size_t v_sz_5047_; size_t v___x_5048_; lean_object* v___x_5049_; lean_object* v_msg_5050_; lean_object* v___x_5051_; lean_object* v_a_5052_; lean_object* v___x_5054_; uint8_t v_isShared_5055_; uint8_t v_isSharedCheck_5089_; 
v_toCold_5036_ = lean_ctor_get(v___y_5033_, 0);
v_currRecDepth_5037_ = lean_ctor_get(v___y_5033_, 1);
v_ref_5038_ = lean_ctor_get(v___y_5033_, 2);
v_diag_5039_ = lean_ctor_get_uint8(v___y_5033_, sizeof(void*)*3);
v_suppressElabErrors_5040_ = lean_ctor_get_uint8(v___y_5033_, sizeof(void*)*3 + 1);
v___x_5041_ = lean_st_ref_get(v___y_5034_);
v_traceState_5042_ = lean_ctor_get(v___x_5041_, 4);
lean_inc_ref(v_traceState_5042_);
lean_dec(v___x_5041_);
v_traces_5043_ = lean_ctor_get(v_traceState_5042_, 0);
lean_inc_ref(v_traces_5043_);
lean_dec_ref(v_traceState_5042_);
v_ref_5044_ = l_Lean_replaceRef(v_ref_5029_, v_ref_5038_);
lean_inc(v_currRecDepth_5037_);
lean_inc_ref(v_toCold_5036_);
v___x_5045_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_5045_, 0, v_toCold_5036_);
lean_ctor_set(v___x_5045_, 1, v_currRecDepth_5037_);
lean_ctor_set(v___x_5045_, 2, v_ref_5044_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*3, v_diag_5039_);
lean_ctor_set_uint8(v___x_5045_, sizeof(void*)*3 + 1, v_suppressElabErrors_5040_);
v___x_5046_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5043_);
lean_dec_ref(v_traces_5043_);
v_sz_5047_ = lean_array_size(v___x_5046_);
v___x_5048_ = ((size_t)0ULL);
v___x_5049_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5047_, v___x_5048_, v___x_5046_);
v_msg_5050_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5050_, 0, v_data_5028_);
lean_ctor_set(v_msg_5050_, 1, v_msg_5030_);
lean_ctor_set(v_msg_5050_, 2, v___x_5049_);
v___x_5051_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5050_, v___y_5031_, v___y_5032_, v___x_5045_, v___y_5034_);
lean_dec_ref_known(v___x_5045_, 3);
v_a_5052_ = lean_ctor_get(v___x_5051_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5051_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5054_ = v___x_5051_;
v_isShared_5055_ = v_isSharedCheck_5089_;
goto v_resetjp_5053_;
}
else
{
lean_inc(v_a_5052_);
lean_dec(v___x_5051_);
v___x_5054_ = lean_box(0);
v_isShared_5055_ = v_isSharedCheck_5089_;
goto v_resetjp_5053_;
}
v_resetjp_5053_:
{
lean_object* v___x_5056_; lean_object* v_traceState_5057_; lean_object* v_env_5058_; lean_object* v_nextMacroScope_5059_; lean_object* v_ngen_5060_; lean_object* v_auxDeclNGen_5061_; lean_object* v_cache_5062_; lean_object* v_messages_5063_; lean_object* v_infoState_5064_; lean_object* v_snapshotTasks_5065_; lean_object* v___x_5067_; uint8_t v_isShared_5068_; uint8_t v_isSharedCheck_5088_; 
v___x_5056_ = lean_st_ref_take(v___y_5034_);
v_traceState_5057_ = lean_ctor_get(v___x_5056_, 4);
v_env_5058_ = lean_ctor_get(v___x_5056_, 0);
v_nextMacroScope_5059_ = lean_ctor_get(v___x_5056_, 1);
v_ngen_5060_ = lean_ctor_get(v___x_5056_, 2);
v_auxDeclNGen_5061_ = lean_ctor_get(v___x_5056_, 3);
v_cache_5062_ = lean_ctor_get(v___x_5056_, 5);
v_messages_5063_ = lean_ctor_get(v___x_5056_, 6);
v_infoState_5064_ = lean_ctor_get(v___x_5056_, 7);
v_snapshotTasks_5065_ = lean_ctor_get(v___x_5056_, 8);
v_isSharedCheck_5088_ = !lean_is_exclusive(v___x_5056_);
if (v_isSharedCheck_5088_ == 0)
{
v___x_5067_ = v___x_5056_;
v_isShared_5068_ = v_isSharedCheck_5088_;
goto v_resetjp_5066_;
}
else
{
lean_inc(v_snapshotTasks_5065_);
lean_inc(v_infoState_5064_);
lean_inc(v_messages_5063_);
lean_inc(v_cache_5062_);
lean_inc(v_traceState_5057_);
lean_inc(v_auxDeclNGen_5061_);
lean_inc(v_ngen_5060_);
lean_inc(v_nextMacroScope_5059_);
lean_inc(v_env_5058_);
lean_dec(v___x_5056_);
v___x_5067_ = lean_box(0);
v_isShared_5068_ = v_isSharedCheck_5088_;
goto v_resetjp_5066_;
}
v_resetjp_5066_:
{
uint64_t v_tid_5069_; lean_object* v___x_5071_; uint8_t v_isShared_5072_; uint8_t v_isSharedCheck_5086_; 
v_tid_5069_ = lean_ctor_get_uint64(v_traceState_5057_, sizeof(void*)*1);
v_isSharedCheck_5086_ = !lean_is_exclusive(v_traceState_5057_);
if (v_isSharedCheck_5086_ == 0)
{
lean_object* v_unused_5087_; 
v_unused_5087_ = lean_ctor_get(v_traceState_5057_, 0);
lean_dec(v_unused_5087_);
v___x_5071_ = v_traceState_5057_;
v_isShared_5072_ = v_isSharedCheck_5086_;
goto v_resetjp_5070_;
}
else
{
lean_dec(v_traceState_5057_);
v___x_5071_ = lean_box(0);
v_isShared_5072_ = v_isSharedCheck_5086_;
goto v_resetjp_5070_;
}
v_resetjp_5070_:
{
lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
v___x_5073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5073_, 0, v_ref_5029_);
lean_ctor_set(v___x_5073_, 1, v_a_5052_);
v___x_5074_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5027_, v___x_5073_);
if (v_isShared_5072_ == 0)
{
lean_ctor_set(v___x_5071_, 0, v___x_5074_);
v___x_5076_ = v___x_5071_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5085_; 
v_reuseFailAlloc_5085_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5085_, 0, v___x_5074_);
lean_ctor_set_uint64(v_reuseFailAlloc_5085_, sizeof(void*)*1, v_tid_5069_);
v___x_5076_ = v_reuseFailAlloc_5085_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
lean_object* v___x_5078_; 
if (v_isShared_5068_ == 0)
{
lean_ctor_set(v___x_5067_, 4, v___x_5076_);
v___x_5078_ = v___x_5067_;
goto v_reusejp_5077_;
}
else
{
lean_object* v_reuseFailAlloc_5084_; 
v_reuseFailAlloc_5084_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5084_, 0, v_env_5058_);
lean_ctor_set(v_reuseFailAlloc_5084_, 1, v_nextMacroScope_5059_);
lean_ctor_set(v_reuseFailAlloc_5084_, 2, v_ngen_5060_);
lean_ctor_set(v_reuseFailAlloc_5084_, 3, v_auxDeclNGen_5061_);
lean_ctor_set(v_reuseFailAlloc_5084_, 4, v___x_5076_);
lean_ctor_set(v_reuseFailAlloc_5084_, 5, v_cache_5062_);
lean_ctor_set(v_reuseFailAlloc_5084_, 6, v_messages_5063_);
lean_ctor_set(v_reuseFailAlloc_5084_, 7, v_infoState_5064_);
lean_ctor_set(v_reuseFailAlloc_5084_, 8, v_snapshotTasks_5065_);
v___x_5078_ = v_reuseFailAlloc_5084_;
goto v_reusejp_5077_;
}
v_reusejp_5077_:
{
lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v___x_5082_; 
v___x_5079_ = lean_st_ref_put(v___y_5034_, v___x_5078_);
v___x_5080_ = lean_box(0);
if (v_isShared_5055_ == 0)
{
lean_ctor_set(v___x_5054_, 0, v___x_5080_);
v___x_5082_ = v___x_5054_;
goto v_reusejp_5081_;
}
else
{
lean_object* v_reuseFailAlloc_5083_; 
v_reuseFailAlloc_5083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5083_, 0, v___x_5080_);
v___x_5082_ = v_reuseFailAlloc_5083_;
goto v_reusejp_5081_;
}
v_reusejp_5081_:
{
return v___x_5082_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5090_, lean_object* v_data_5091_, lean_object* v_ref_5092_, lean_object* v_msg_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v_res_5099_; 
v_res_5099_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5090_, v_data_5091_, v_ref_5092_, v_msg_5093_, v___y_5094_, v___y_5095_, v___y_5096_, v___y_5097_);
lean_dec(v___y_5097_);
lean_dec_ref(v___y_5096_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
return v_res_5099_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5100_, uint8_t v_collapsed_5101_, lean_object* v_tag_5102_, lean_object* v_opts_5103_, uint8_t v_clsEnabled_5104_, lean_object* v_oldTraces_5105_, lean_object* v_msg_5106_, lean_object* v_resStartStop_5107_, lean_object* v___y_5108_, lean_object* v___y_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_){
_start:
{
lean_object* v_fst_5113_; lean_object* v_snd_5114_; lean_object* v___y_5116_; lean_object* v___y_5117_; lean_object* v_data_5118_; lean_object* v_fst_5129_; lean_object* v_snd_5130_; lean_object* v___x_5131_; uint8_t v___x_5132_; lean_object* v___y_5134_; lean_object* v_a_5135_; uint8_t v___y_5150_; double v___y_5181_; 
v_fst_5113_ = lean_ctor_get(v_resStartStop_5107_, 0);
lean_inc(v_fst_5113_);
v_snd_5114_ = lean_ctor_get(v_resStartStop_5107_, 1);
lean_inc(v_snd_5114_);
lean_dec_ref(v_resStartStop_5107_);
v_fst_5129_ = lean_ctor_get(v_snd_5114_, 0);
lean_inc(v_fst_5129_);
v_snd_5130_ = lean_ctor_get(v_snd_5114_, 1);
lean_inc(v_snd_5130_);
lean_dec(v_snd_5114_);
v___x_5131_ = l_Lean_trace_profiler;
v___x_5132_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5103_, v___x_5131_);
if (v___x_5132_ == 0)
{
v___y_5150_ = v___x_5132_;
goto v___jp_5149_;
}
else
{
lean_object* v___x_5186_; uint8_t v___x_5187_; 
v___x_5186_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5187_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5103_, v___x_5186_);
if (v___x_5187_ == 0)
{
lean_object* v___x_5188_; lean_object* v___x_5189_; double v___x_5190_; double v___x_5191_; double v___x_5192_; 
v___x_5188_ = l_Lean_trace_profiler_threshold;
v___x_5189_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5103_, v___x_5188_);
v___x_5190_ = lean_float_of_nat(v___x_5189_);
v___x_5191_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5192_ = lean_float_div(v___x_5190_, v___x_5191_);
v___y_5181_ = v___x_5192_;
goto v___jp_5180_;
}
else
{
lean_object* v___x_5193_; lean_object* v___x_5194_; double v___x_5195_; 
v___x_5193_ = l_Lean_trace_profiler_threshold;
v___x_5194_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5103_, v___x_5193_);
v___x_5195_ = lean_float_of_nat(v___x_5194_);
v___y_5181_ = v___x_5195_;
goto v___jp_5180_;
}
}
v___jp_5115_:
{
lean_object* v___x_5119_; 
lean_inc(v___y_5116_);
v___x_5119_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5105_, v_data_5118_, v___y_5116_, v___y_5117_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_);
if (lean_obj_tag(v___x_5119_) == 0)
{
lean_object* v___x_5120_; 
lean_dec_ref_known(v___x_5119_, 1);
v___x_5120_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5113_);
return v___x_5120_;
}
else
{
lean_object* v_a_5121_; lean_object* v___x_5123_; uint8_t v_isShared_5124_; uint8_t v_isSharedCheck_5128_; 
lean_dec(v_fst_5113_);
v_a_5121_ = lean_ctor_get(v___x_5119_, 0);
v_isSharedCheck_5128_ = !lean_is_exclusive(v___x_5119_);
if (v_isSharedCheck_5128_ == 0)
{
v___x_5123_ = v___x_5119_;
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
else
{
lean_inc(v_a_5121_);
lean_dec(v___x_5119_);
v___x_5123_ = lean_box(0);
v_isShared_5124_ = v_isSharedCheck_5128_;
goto v_resetjp_5122_;
}
v_resetjp_5122_:
{
lean_object* v___x_5126_; 
if (v_isShared_5124_ == 0)
{
v___x_5126_ = v___x_5123_;
goto v_reusejp_5125_;
}
else
{
lean_object* v_reuseFailAlloc_5127_; 
v_reuseFailAlloc_5127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5127_, 0, v_a_5121_);
v___x_5126_ = v_reuseFailAlloc_5127_;
goto v_reusejp_5125_;
}
v_reusejp_5125_:
{
return v___x_5126_;
}
}
}
}
v___jp_5133_:
{
uint8_t v_result_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; double v___x_5139_; lean_object* v_data_5140_; 
v_result_5136_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5113_);
v___x_5137_ = lean_box(v_result_5136_);
v___x_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5137_);
v___x_5139_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5102_);
lean_inc_ref(v___x_5138_);
lean_inc(v_cls_5100_);
v_data_5140_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5140_, 0, v_cls_5100_);
lean_ctor_set(v_data_5140_, 1, v___x_5138_);
lean_ctor_set(v_data_5140_, 2, v_tag_5102_);
lean_ctor_set_float(v_data_5140_, sizeof(void*)*3, v___x_5139_);
lean_ctor_set_float(v_data_5140_, sizeof(void*)*3 + 8, v___x_5139_);
lean_ctor_set_uint8(v_data_5140_, sizeof(void*)*3 + 16, v_collapsed_5101_);
if (v___x_5132_ == 0)
{
lean_dec_ref_known(v___x_5138_, 1);
lean_dec(v_snd_5130_);
lean_dec(v_fst_5129_);
lean_dec_ref(v_tag_5102_);
lean_dec(v_cls_5100_);
v___y_5116_ = v___y_5134_;
v___y_5117_ = v_a_5135_;
v_data_5118_ = v_data_5140_;
goto v___jp_5115_;
}
else
{
lean_object* v_data_5141_; double v___x_5142_; double v___x_5143_; 
lean_dec_ref_known(v_data_5140_, 3);
v_data_5141_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5141_, 0, v_cls_5100_);
lean_ctor_set(v_data_5141_, 1, v___x_5138_);
lean_ctor_set(v_data_5141_, 2, v_tag_5102_);
v___x_5142_ = lean_unbox_float(v_fst_5129_);
lean_dec(v_fst_5129_);
lean_ctor_set_float(v_data_5141_, sizeof(void*)*3, v___x_5142_);
v___x_5143_ = lean_unbox_float(v_snd_5130_);
lean_dec(v_snd_5130_);
lean_ctor_set_float(v_data_5141_, sizeof(void*)*3 + 8, v___x_5143_);
lean_ctor_set_uint8(v_data_5141_, sizeof(void*)*3 + 16, v_collapsed_5101_);
v___y_5116_ = v___y_5134_;
v___y_5117_ = v_a_5135_;
v_data_5118_ = v_data_5141_;
goto v___jp_5115_;
}
}
v___jp_5144_:
{
lean_object* v_ref_5145_; lean_object* v___x_5146_; 
v_ref_5145_ = lean_ctor_get(v___y_5110_, 2);
lean_inc(v___y_5111_);
lean_inc_ref(v___y_5110_);
lean_inc(v___y_5109_);
lean_inc_ref(v___y_5108_);
lean_inc(v_fst_5113_);
v___x_5146_ = lean_apply_6(v_msg_5106_, v_fst_5113_, v___y_5108_, v___y_5109_, v___y_5110_, v___y_5111_, lean_box(0));
if (lean_obj_tag(v___x_5146_) == 0)
{
lean_object* v_a_5147_; 
v_a_5147_ = lean_ctor_get(v___x_5146_, 0);
lean_inc(v_a_5147_);
lean_dec_ref_known(v___x_5146_, 1);
v___y_5134_ = v_ref_5145_;
v_a_5135_ = v_a_5147_;
goto v___jp_5133_;
}
else
{
lean_object* v___x_5148_; 
lean_dec_ref_known(v___x_5146_, 1);
v___x_5148_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5134_ = v_ref_5145_;
v_a_5135_ = v___x_5148_;
goto v___jp_5133_;
}
}
v___jp_5149_:
{
if (v_clsEnabled_5104_ == 0)
{
if (v___y_5150_ == 0)
{
lean_object* v___x_5151_; lean_object* v_traceState_5152_; lean_object* v_env_5153_; lean_object* v_nextMacroScope_5154_; lean_object* v_ngen_5155_; lean_object* v_auxDeclNGen_5156_; lean_object* v_cache_5157_; lean_object* v_messages_5158_; lean_object* v_infoState_5159_; lean_object* v_snapshotTasks_5160_; lean_object* v___x_5162_; uint8_t v_isShared_5163_; uint8_t v_isSharedCheck_5179_; 
lean_dec(v_snd_5130_);
lean_dec(v_fst_5129_);
lean_dec_ref(v_msg_5106_);
lean_dec_ref(v_tag_5102_);
lean_dec(v_cls_5100_);
v___x_5151_ = lean_st_ref_take(v___y_5111_);
v_traceState_5152_ = lean_ctor_get(v___x_5151_, 4);
v_env_5153_ = lean_ctor_get(v___x_5151_, 0);
v_nextMacroScope_5154_ = lean_ctor_get(v___x_5151_, 1);
v_ngen_5155_ = lean_ctor_get(v___x_5151_, 2);
v_auxDeclNGen_5156_ = lean_ctor_get(v___x_5151_, 3);
v_cache_5157_ = lean_ctor_get(v___x_5151_, 5);
v_messages_5158_ = lean_ctor_get(v___x_5151_, 6);
v_infoState_5159_ = lean_ctor_get(v___x_5151_, 7);
v_snapshotTasks_5160_ = lean_ctor_get(v___x_5151_, 8);
v_isSharedCheck_5179_ = !lean_is_exclusive(v___x_5151_);
if (v_isSharedCheck_5179_ == 0)
{
v___x_5162_ = v___x_5151_;
v_isShared_5163_ = v_isSharedCheck_5179_;
goto v_resetjp_5161_;
}
else
{
lean_inc(v_snapshotTasks_5160_);
lean_inc(v_infoState_5159_);
lean_inc(v_messages_5158_);
lean_inc(v_cache_5157_);
lean_inc(v_traceState_5152_);
lean_inc(v_auxDeclNGen_5156_);
lean_inc(v_ngen_5155_);
lean_inc(v_nextMacroScope_5154_);
lean_inc(v_env_5153_);
lean_dec(v___x_5151_);
v___x_5162_ = lean_box(0);
v_isShared_5163_ = v_isSharedCheck_5179_;
goto v_resetjp_5161_;
}
v_resetjp_5161_:
{
uint64_t v_tid_5164_; lean_object* v_traces_5165_; lean_object* v___x_5167_; uint8_t v_isShared_5168_; uint8_t v_isSharedCheck_5178_; 
v_tid_5164_ = lean_ctor_get_uint64(v_traceState_5152_, sizeof(void*)*1);
v_traces_5165_ = lean_ctor_get(v_traceState_5152_, 0);
v_isSharedCheck_5178_ = !lean_is_exclusive(v_traceState_5152_);
if (v_isSharedCheck_5178_ == 0)
{
v___x_5167_ = v_traceState_5152_;
v_isShared_5168_ = v_isSharedCheck_5178_;
goto v_resetjp_5166_;
}
else
{
lean_inc(v_traces_5165_);
lean_dec(v_traceState_5152_);
v___x_5167_ = lean_box(0);
v_isShared_5168_ = v_isSharedCheck_5178_;
goto v_resetjp_5166_;
}
v_resetjp_5166_:
{
lean_object* v___x_5169_; lean_object* v___x_5171_; 
v___x_5169_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5105_, v_traces_5165_);
lean_dec_ref(v_traces_5165_);
if (v_isShared_5168_ == 0)
{
lean_ctor_set(v___x_5167_, 0, v___x_5169_);
v___x_5171_ = v___x_5167_;
goto v_reusejp_5170_;
}
else
{
lean_object* v_reuseFailAlloc_5177_; 
v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5177_, 0, v___x_5169_);
lean_ctor_set_uint64(v_reuseFailAlloc_5177_, sizeof(void*)*1, v_tid_5164_);
v___x_5171_ = v_reuseFailAlloc_5177_;
goto v_reusejp_5170_;
}
v_reusejp_5170_:
{
lean_object* v___x_5173_; 
if (v_isShared_5163_ == 0)
{
lean_ctor_set(v___x_5162_, 4, v___x_5171_);
v___x_5173_ = v___x_5162_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5176_; 
v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_env_5153_);
lean_ctor_set(v_reuseFailAlloc_5176_, 1, v_nextMacroScope_5154_);
lean_ctor_set(v_reuseFailAlloc_5176_, 2, v_ngen_5155_);
lean_ctor_set(v_reuseFailAlloc_5176_, 3, v_auxDeclNGen_5156_);
lean_ctor_set(v_reuseFailAlloc_5176_, 4, v___x_5171_);
lean_ctor_set(v_reuseFailAlloc_5176_, 5, v_cache_5157_);
lean_ctor_set(v_reuseFailAlloc_5176_, 6, v_messages_5158_);
lean_ctor_set(v_reuseFailAlloc_5176_, 7, v_infoState_5159_);
lean_ctor_set(v_reuseFailAlloc_5176_, 8, v_snapshotTasks_5160_);
v___x_5173_ = v_reuseFailAlloc_5176_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
lean_object* v___x_5174_; lean_object* v___x_5175_; 
v___x_5174_ = lean_st_ref_put(v___y_5111_, v___x_5173_);
v___x_5175_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5113_);
return v___x_5175_;
}
}
}
}
}
else
{
goto v___jp_5144_;
}
}
else
{
goto v___jp_5144_;
}
}
v___jp_5180_:
{
double v___x_5182_; double v___x_5183_; double v___x_5184_; uint8_t v___x_5185_; 
v___x_5182_ = lean_unbox_float(v_snd_5130_);
v___x_5183_ = lean_unbox_float(v_fst_5129_);
v___x_5184_ = lean_float_sub(v___x_5182_, v___x_5183_);
v___x_5185_ = lean_float_decLt(v___y_5181_, v___x_5184_);
v___y_5150_ = v___x_5185_;
goto v___jp_5149_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5196_, lean_object* v_collapsed_5197_, lean_object* v_tag_5198_, lean_object* v_opts_5199_, lean_object* v_clsEnabled_5200_, lean_object* v_oldTraces_5201_, lean_object* v_msg_5202_, lean_object* v_resStartStop_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_, lean_object* v___y_5207_, lean_object* v___y_5208_){
_start:
{
uint8_t v_collapsed_boxed_5209_; uint8_t v_clsEnabled_boxed_5210_; lean_object* v_res_5211_; 
v_collapsed_boxed_5209_ = lean_unbox(v_collapsed_5197_);
v_clsEnabled_boxed_5210_ = lean_unbox(v_clsEnabled_5200_);
v_res_5211_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5196_, v_collapsed_boxed_5209_, v_tag_5198_, v_opts_5199_, v_clsEnabled_boxed_5210_, v_oldTraces_5201_, v_msg_5202_, v_resStartStop_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_);
lean_dec(v___y_5207_);
lean_dec_ref(v___y_5206_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec_ref(v_opts_5199_);
return v_res_5211_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; 
v_cls_5216_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5217_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5218_ = l_Lean_Name_append(v___x_5217_, v_cls_5216_);
return v___x_5218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5219_, lean_object* v_a_5220_, lean_object* v_a_5221_, lean_object* v_a_5222_, lean_object* v_a_5223_){
_start:
{
lean_object* v___y_5226_; lean_object* v_toCold_5244_; lean_object* v_options_5245_; lean_object* v_inheritedTraceOptions_5246_; uint8_t v_hasTrace_5247_; lean_object* v_cls_5248_; uint8_t v___x_5249_; 
v_toCold_5244_ = lean_ctor_get(v_a_5222_, 0);
v_options_5245_ = lean_ctor_get(v_toCold_5244_, 2);
v_inheritedTraceOptions_5246_ = lean_ctor_get(v_toCold_5244_, 11);
v_hasTrace_5247_ = lean_ctor_get_uint8(v_options_5245_, sizeof(void*)*1);
v_cls_5248_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5249_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5219_);
if (v_hasTrace_5247_ == 0)
{
lean_object* v___x_5250_; 
v___x_5250_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5249_, v_e_5219_, v_cls_5248_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
v___y_5226_ = v___x_5250_;
goto v___jp_5225_;
}
else
{
lean_object* v___f_5251_; lean_object* v___x_5252_; lean_object* v___x_5253_; uint8_t v___x_5254_; lean_object* v___y_5256_; lean_object* v___y_5257_; lean_object* v_a_5258_; lean_object* v___y_5271_; lean_object* v___y_5272_; lean_object* v_a_5273_; 
v___f_5251_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5252_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5253_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5254_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5246_, v_options_5245_, v___x_5253_);
if (v___x_5254_ == 0)
{
lean_object* v___x_5323_; uint8_t v___x_5324_; 
v___x_5323_ = l_Lean_trace_profiler;
v___x_5324_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5245_, v___x_5323_);
if (v___x_5324_ == 0)
{
lean_object* v___x_5325_; 
v___x_5325_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5249_, v_e_5219_, v_cls_5248_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
v___y_5226_ = v___x_5325_;
goto v___jp_5225_;
}
else
{
goto v___jp_5282_;
}
}
else
{
goto v___jp_5282_;
}
v___jp_5255_:
{
lean_object* v___x_5259_; double v___x_5260_; double v___x_5261_; double v___x_5262_; double v___x_5263_; double v___x_5264_; lean_object* v___x_5265_; lean_object* v___x_5266_; lean_object* v___x_5267_; lean_object* v___x_5268_; lean_object* v___x_5269_; 
v___x_5259_ = lean_io_mono_nanos_now();
v___x_5260_ = lean_float_of_nat(v___y_5256_);
v___x_5261_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5262_ = lean_float_div(v___x_5260_, v___x_5261_);
v___x_5263_ = lean_float_of_nat(v___x_5259_);
v___x_5264_ = lean_float_div(v___x_5263_, v___x_5261_);
v___x_5265_ = lean_box_float(v___x_5262_);
v___x_5266_ = lean_box_float(v___x_5264_);
v___x_5267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5267_, 0, v___x_5265_);
lean_ctor_set(v___x_5267_, 1, v___x_5266_);
v___x_5268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5268_, 0, v_a_5258_);
lean_ctor_set(v___x_5268_, 1, v___x_5267_);
v___x_5269_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5248_, v_hasTrace_5247_, v___x_5252_, v_options_5245_, v___x_5254_, v___y_5257_, v___f_5251_, v___x_5268_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
v___y_5226_ = v___x_5269_;
goto v___jp_5225_;
}
v___jp_5270_:
{
lean_object* v___x_5274_; double v___x_5275_; double v___x_5276_; lean_object* v___x_5277_; lean_object* v___x_5278_; lean_object* v___x_5279_; lean_object* v___x_5280_; lean_object* v___x_5281_; 
v___x_5274_ = lean_io_get_num_heartbeats();
v___x_5275_ = lean_float_of_nat(v___y_5272_);
v___x_5276_ = lean_float_of_nat(v___x_5274_);
v___x_5277_ = lean_box_float(v___x_5275_);
v___x_5278_ = lean_box_float(v___x_5276_);
v___x_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5277_);
lean_ctor_set(v___x_5279_, 1, v___x_5278_);
v___x_5280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5280_, 0, v_a_5273_);
lean_ctor_set(v___x_5280_, 1, v___x_5279_);
v___x_5281_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5248_, v_hasTrace_5247_, v___x_5252_, v_options_5245_, v___x_5254_, v___y_5271_, v___f_5251_, v___x_5280_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
v___y_5226_ = v___x_5281_;
goto v___jp_5225_;
}
v___jp_5282_:
{
lean_object* v___x_5283_; lean_object* v_a_5284_; lean_object* v___x_5285_; uint8_t v___x_5286_; 
v___x_5283_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5223_);
v_a_5284_ = lean_ctor_get(v___x_5283_, 0);
lean_inc(v_a_5284_);
lean_dec_ref(v___x_5283_);
v___x_5285_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5286_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5245_, v___x_5285_);
if (v___x_5286_ == 0)
{
lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5287_ = lean_io_mono_nanos_now();
v___x_5288_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5249_, v_e_5219_, v_cls_5248_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5288_) == 0)
{
lean_object* v_a_5289_; lean_object* v___x_5291_; uint8_t v_isShared_5292_; uint8_t v_isSharedCheck_5296_; 
v_a_5289_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5296_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5296_ == 0)
{
v___x_5291_ = v___x_5288_;
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
else
{
lean_inc(v_a_5289_);
lean_dec(v___x_5288_);
v___x_5291_ = lean_box(0);
v_isShared_5292_ = v_isSharedCheck_5296_;
goto v_resetjp_5290_;
}
v_resetjp_5290_:
{
lean_object* v___x_5294_; 
if (v_isShared_5292_ == 0)
{
lean_ctor_set_tag(v___x_5291_, 1);
v___x_5294_ = v___x_5291_;
goto v_reusejp_5293_;
}
else
{
lean_object* v_reuseFailAlloc_5295_; 
v_reuseFailAlloc_5295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5295_, 0, v_a_5289_);
v___x_5294_ = v_reuseFailAlloc_5295_;
goto v_reusejp_5293_;
}
v_reusejp_5293_:
{
v___y_5256_ = v___x_5287_;
v___y_5257_ = v_a_5284_;
v_a_5258_ = v___x_5294_;
goto v___jp_5255_;
}
}
}
else
{
lean_object* v_a_5297_; lean_object* v___x_5299_; uint8_t v_isShared_5300_; uint8_t v_isSharedCheck_5304_; 
v_a_5297_ = lean_ctor_get(v___x_5288_, 0);
v_isSharedCheck_5304_ = !lean_is_exclusive(v___x_5288_);
if (v_isSharedCheck_5304_ == 0)
{
v___x_5299_ = v___x_5288_;
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
else
{
lean_inc(v_a_5297_);
lean_dec(v___x_5288_);
v___x_5299_ = lean_box(0);
v_isShared_5300_ = v_isSharedCheck_5304_;
goto v_resetjp_5298_;
}
v_resetjp_5298_:
{
lean_object* v___x_5302_; 
if (v_isShared_5300_ == 0)
{
lean_ctor_set_tag(v___x_5299_, 0);
v___x_5302_ = v___x_5299_;
goto v_reusejp_5301_;
}
else
{
lean_object* v_reuseFailAlloc_5303_; 
v_reuseFailAlloc_5303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_a_5297_);
v___x_5302_ = v_reuseFailAlloc_5303_;
goto v_reusejp_5301_;
}
v_reusejp_5301_:
{
v___y_5256_ = v___x_5287_;
v___y_5257_ = v_a_5284_;
v_a_5258_ = v___x_5302_;
goto v___jp_5255_;
}
}
}
}
else
{
lean_object* v___x_5305_; lean_object* v___x_5306_; 
v___x_5305_ = lean_io_get_num_heartbeats();
v___x_5306_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5249_, v_e_5219_, v_cls_5248_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5314_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5314_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5314_ == 0)
{
v___x_5309_ = v___x_5306_;
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5306_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5314_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v___x_5312_; 
if (v_isShared_5310_ == 0)
{
lean_ctor_set_tag(v___x_5309_, 1);
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
v___y_5271_ = v_a_5284_;
v___y_5272_ = v___x_5305_;
v_a_5273_ = v___x_5312_;
goto v___jp_5270_;
}
}
}
else
{
lean_object* v_a_5315_; lean_object* v___x_5317_; uint8_t v_isShared_5318_; uint8_t v_isSharedCheck_5322_; 
v_a_5315_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5322_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5322_ == 0)
{
v___x_5317_ = v___x_5306_;
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
else
{
lean_inc(v_a_5315_);
lean_dec(v___x_5306_);
v___x_5317_ = lean_box(0);
v_isShared_5318_ = v_isSharedCheck_5322_;
goto v_resetjp_5316_;
}
v_resetjp_5316_:
{
lean_object* v___x_5320_; 
if (v_isShared_5318_ == 0)
{
lean_ctor_set_tag(v___x_5317_, 0);
v___x_5320_ = v___x_5317_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5321_; 
v_reuseFailAlloc_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5321_, 0, v_a_5315_);
v___x_5320_ = v_reuseFailAlloc_5321_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
v___y_5271_ = v_a_5284_;
v___y_5272_ = v___x_5305_;
v_a_5273_ = v___x_5320_;
goto v___jp_5270_;
}
}
}
}
}
}
v___jp_5225_:
{
if (lean_obj_tag(v___y_5226_) == 0)
{
lean_object* v_a_5227_; lean_object* v___x_5229_; uint8_t v_isShared_5230_; uint8_t v_isSharedCheck_5235_; 
v_a_5227_ = lean_ctor_get(v___y_5226_, 0);
v_isSharedCheck_5235_ = !lean_is_exclusive(v___y_5226_);
if (v_isSharedCheck_5235_ == 0)
{
v___x_5229_ = v___y_5226_;
v_isShared_5230_ = v_isSharedCheck_5235_;
goto v_resetjp_5228_;
}
else
{
lean_inc(v_a_5227_);
lean_dec(v___y_5226_);
v___x_5229_ = lean_box(0);
v_isShared_5230_ = v_isSharedCheck_5235_;
goto v_resetjp_5228_;
}
v_resetjp_5228_:
{
lean_object* v_fst_5231_; lean_object* v___x_5233_; 
v_fst_5231_ = lean_ctor_get(v_a_5227_, 0);
lean_inc(v_fst_5231_);
lean_dec(v_a_5227_);
if (v_isShared_5230_ == 0)
{
lean_ctor_set(v___x_5229_, 0, v_fst_5231_);
v___x_5233_ = v___x_5229_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v_fst_5231_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
else
{
lean_object* v_a_5236_; lean_object* v___x_5238_; uint8_t v_isShared_5239_; uint8_t v_isSharedCheck_5243_; 
v_a_5236_ = lean_ctor_get(v___y_5226_, 0);
v_isSharedCheck_5243_ = !lean_is_exclusive(v___y_5226_);
if (v_isSharedCheck_5243_ == 0)
{
v___x_5238_ = v___y_5226_;
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
else
{
lean_inc(v_a_5236_);
lean_dec(v___y_5226_);
v___x_5238_ = lean_box(0);
v_isShared_5239_ = v_isSharedCheck_5243_;
goto v_resetjp_5237_;
}
v_resetjp_5237_:
{
lean_object* v___x_5241_; 
if (v_isShared_5239_ == 0)
{
v___x_5241_ = v___x_5238_;
goto v_reusejp_5240_;
}
else
{
lean_object* v_reuseFailAlloc_5242_; 
v_reuseFailAlloc_5242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5242_, 0, v_a_5236_);
v___x_5241_ = v_reuseFailAlloc_5242_;
goto v_reusejp_5240_;
}
v_reusejp_5240_:
{
return v___x_5241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_, lean_object* v_a_5329_, lean_object* v_a_5330_, lean_object* v_a_5331_){
_start:
{
lean_object* v_res_5332_; 
v_res_5332_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
lean_dec(v_a_5330_);
lean_dec_ref(v_a_5329_);
lean_dec(v_a_5328_);
lean_dec_ref(v_a_5327_);
return v_res_5332_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5333_, lean_object* v_x_5334_, lean_object* v___y_5335_, lean_object* v___y_5336_, lean_object* v___y_5337_, lean_object* v___y_5338_){
_start:
{
lean_object* v___x_5340_; 
v___x_5340_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5334_);
return v___x_5340_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5341_, lean_object* v_x_5342_, lean_object* v___y_5343_, lean_object* v___y_5344_, lean_object* v___y_5345_, lean_object* v___y_5346_, lean_object* v___y_5347_){
_start:
{
lean_object* v_res_5348_; 
v_res_5348_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5341_, v_x_5342_, v___y_5343_, v___y_5344_, v___y_5345_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec_ref(v___y_5345_);
lean_dec(v___y_5344_);
lean_dec_ref(v___y_5343_);
return v_res_5348_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5349_, lean_object* v___y_5350_){
_start:
{
uint8_t v___x_5352_; 
v___x_5352_ = l_Lean_Expr_hasMVar(v_e_5349_);
if (v___x_5352_ == 0)
{
lean_object* v___x_5353_; 
v___x_5353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5353_, 0, v_e_5349_);
return v___x_5353_;
}
else
{
lean_object* v___x_5354_; lean_object* v_mctx_5355_; lean_object* v___x_5356_; lean_object* v_fst_5357_; lean_object* v_snd_5358_; lean_object* v___x_5359_; lean_object* v_cache_5360_; lean_object* v_zetaDeltaFVarIds_5361_; lean_object* v_postponed_5362_; lean_object* v_diag_5363_; lean_object* v___x_5365_; uint8_t v_isShared_5366_; uint8_t v_isSharedCheck_5372_; 
v___x_5354_ = lean_st_ref_get(v___y_5350_);
v_mctx_5355_ = lean_ctor_get(v___x_5354_, 0);
lean_inc_ref(v_mctx_5355_);
lean_dec(v___x_5354_);
v___x_5356_ = l_Lean_instantiateMVarsCore(v_mctx_5355_, v_e_5349_);
v_fst_5357_ = lean_ctor_get(v___x_5356_, 0);
lean_inc(v_fst_5357_);
v_snd_5358_ = lean_ctor_get(v___x_5356_, 1);
lean_inc(v_snd_5358_);
lean_dec_ref(v___x_5356_);
v___x_5359_ = lean_st_ref_take(v___y_5350_);
v_cache_5360_ = lean_ctor_get(v___x_5359_, 1);
v_zetaDeltaFVarIds_5361_ = lean_ctor_get(v___x_5359_, 2);
v_postponed_5362_ = lean_ctor_get(v___x_5359_, 3);
v_diag_5363_ = lean_ctor_get(v___x_5359_, 4);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5359_);
if (v_isSharedCheck_5372_ == 0)
{
lean_object* v_unused_5373_; 
v_unused_5373_ = lean_ctor_get(v___x_5359_, 0);
lean_dec(v_unused_5373_);
v___x_5365_ = v___x_5359_;
v_isShared_5366_ = v_isSharedCheck_5372_;
goto v_resetjp_5364_;
}
else
{
lean_inc(v_diag_5363_);
lean_inc(v_postponed_5362_);
lean_inc(v_zetaDeltaFVarIds_5361_);
lean_inc(v_cache_5360_);
lean_dec(v___x_5359_);
v___x_5365_ = lean_box(0);
v_isShared_5366_ = v_isSharedCheck_5372_;
goto v_resetjp_5364_;
}
v_resetjp_5364_:
{
lean_object* v___x_5368_; 
if (v_isShared_5366_ == 0)
{
lean_ctor_set(v___x_5365_, 0, v_snd_5358_);
v___x_5368_ = v___x_5365_;
goto v_reusejp_5367_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_snd_5358_);
lean_ctor_set(v_reuseFailAlloc_5371_, 1, v_cache_5360_);
lean_ctor_set(v_reuseFailAlloc_5371_, 2, v_zetaDeltaFVarIds_5361_);
lean_ctor_set(v_reuseFailAlloc_5371_, 3, v_postponed_5362_);
lean_ctor_set(v_reuseFailAlloc_5371_, 4, v_diag_5363_);
v___x_5368_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5367_;
}
v_reusejp_5367_:
{
lean_object* v___x_5369_; lean_object* v___x_5370_; 
v___x_5369_ = lean_st_ref_put(v___y_5350_, v___x_5368_);
v___x_5370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5370_, 0, v_fst_5357_);
return v___x_5370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5374_, lean_object* v___y_5375_, lean_object* v___y_5376_){
_start:
{
lean_object* v_res_5377_; 
v_res_5377_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5374_, v___y_5375_);
lean_dec(v___y_5375_);
return v_res_5377_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5378_, lean_object* v___y_5379_, lean_object* v___y_5380_, lean_object* v___y_5381_, lean_object* v___y_5382_){
_start:
{
lean_object* v___x_5384_; 
v___x_5384_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5378_, v___y_5380_);
return v___x_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5385_, lean_object* v___y_5386_, lean_object* v___y_5387_, lean_object* v___y_5388_, lean_object* v___y_5389_, lean_object* v___y_5390_){
_start:
{
lean_object* v_res_5391_; 
v_res_5391_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5385_, v___y_5386_, v___y_5387_, v___y_5388_, v___y_5389_);
lean_dec(v___y_5389_);
lean_dec_ref(v___y_5388_);
lean_dec(v___y_5387_);
lean_dec_ref(v___y_5386_);
return v_res_5391_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5392_, lean_object* v_opts_5393_, lean_object* v_act_5394_, lean_object* v_decl_5395_, lean_object* v___y_5396_, lean_object* v___y_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_){
_start:
{
lean_object* v___x_5401_; lean_object* v___x_5402_; 
lean_inc(v___y_5399_);
lean_inc_ref(v___y_5398_);
lean_inc(v___y_5397_);
lean_inc_ref(v___y_5396_);
v___x_5401_ = lean_apply_4(v_act_5394_, v___y_5396_, v___y_5397_, v___y_5398_, v___y_5399_);
v___x_5402_ = l_Lean_profileitIOUnsafe___redArg(v_category_5392_, v_opts_5393_, v___x_5401_, v_decl_5395_);
return v___x_5402_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5403_, lean_object* v_opts_5404_, lean_object* v_act_5405_, lean_object* v_decl_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_, lean_object* v___y_5410_, lean_object* v___y_5411_){
_start:
{
lean_object* v_res_5412_; 
v_res_5412_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5403_, v_opts_5404_, v_act_5405_, v_decl_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_);
lean_dec(v___y_5410_);
lean_dec_ref(v___y_5409_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
lean_dec_ref(v_opts_5404_);
lean_dec_ref(v_category_5403_);
return v_res_5412_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5413_, lean_object* v_category_5414_, lean_object* v_opts_5415_, lean_object* v_act_5416_, lean_object* v_decl_5417_, lean_object* v___y_5418_, lean_object* v___y_5419_, lean_object* v___y_5420_, lean_object* v___y_5421_){
_start:
{
lean_object* v___x_5423_; 
v___x_5423_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5414_, v_opts_5415_, v_act_5416_, v_decl_5417_, v___y_5418_, v___y_5419_, v___y_5420_, v___y_5421_);
return v___x_5423_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5424_, lean_object* v_category_5425_, lean_object* v_opts_5426_, lean_object* v_act_5427_, lean_object* v_decl_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_, lean_object* v___y_5431_, lean_object* v___y_5432_, lean_object* v___y_5433_){
_start:
{
lean_object* v_res_5434_; 
v_res_5434_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5424_, v_category_5425_, v_opts_5426_, v_act_5427_, v_decl_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_);
lean_dec(v___y_5432_);
lean_dec_ref(v___y_5431_);
lean_dec(v___y_5430_);
lean_dec_ref(v___y_5429_);
lean_dec_ref(v_opts_5426_);
lean_dec_ref(v_category_5425_);
return v_res_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5435_, uint8_t v_isExporting_5436_, lean_object* v___x_5437_, lean_object* v___y_5438_, lean_object* v___x_5439_, lean_object* v_a_x3f_5440_){
_start:
{
lean_object* v___x_5442_; lean_object* v_env_5443_; lean_object* v_nextMacroScope_5444_; lean_object* v_ngen_5445_; lean_object* v_auxDeclNGen_5446_; lean_object* v_traceState_5447_; lean_object* v_messages_5448_; lean_object* v_infoState_5449_; lean_object* v_snapshotTasks_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5475_; 
v___x_5442_ = lean_st_ref_take(v___y_5435_);
v_env_5443_ = lean_ctor_get(v___x_5442_, 0);
v_nextMacroScope_5444_ = lean_ctor_get(v___x_5442_, 1);
v_ngen_5445_ = lean_ctor_get(v___x_5442_, 2);
v_auxDeclNGen_5446_ = lean_ctor_get(v___x_5442_, 3);
v_traceState_5447_ = lean_ctor_get(v___x_5442_, 4);
v_messages_5448_ = lean_ctor_get(v___x_5442_, 6);
v_infoState_5449_ = lean_ctor_get(v___x_5442_, 7);
v_snapshotTasks_5450_ = lean_ctor_get(v___x_5442_, 8);
v_isSharedCheck_5475_ = !lean_is_exclusive(v___x_5442_);
if (v_isSharedCheck_5475_ == 0)
{
lean_object* v_unused_5476_; 
v_unused_5476_ = lean_ctor_get(v___x_5442_, 5);
lean_dec(v_unused_5476_);
v___x_5452_ = v___x_5442_;
v_isShared_5453_ = v_isSharedCheck_5475_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_snapshotTasks_5450_);
lean_inc(v_infoState_5449_);
lean_inc(v_messages_5448_);
lean_inc(v_traceState_5447_);
lean_inc(v_auxDeclNGen_5446_);
lean_inc(v_ngen_5445_);
lean_inc(v_nextMacroScope_5444_);
lean_inc(v_env_5443_);
lean_dec(v___x_5442_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5475_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5454_; lean_object* v___x_5456_; 
v___x_5454_ = l_Lean_Environment_setExporting(v_env_5443_, v_isExporting_5436_);
if (v_isShared_5453_ == 0)
{
lean_ctor_set(v___x_5452_, 5, v___x_5437_);
lean_ctor_set(v___x_5452_, 0, v___x_5454_);
v___x_5456_ = v___x_5452_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v_nextMacroScope_5444_);
lean_ctor_set(v_reuseFailAlloc_5474_, 2, v_ngen_5445_);
lean_ctor_set(v_reuseFailAlloc_5474_, 3, v_auxDeclNGen_5446_);
lean_ctor_set(v_reuseFailAlloc_5474_, 4, v_traceState_5447_);
lean_ctor_set(v_reuseFailAlloc_5474_, 5, v___x_5437_);
lean_ctor_set(v_reuseFailAlloc_5474_, 6, v_messages_5448_);
lean_ctor_set(v_reuseFailAlloc_5474_, 7, v_infoState_5449_);
lean_ctor_set(v_reuseFailAlloc_5474_, 8, v_snapshotTasks_5450_);
v___x_5456_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
lean_object* v___x_5457_; lean_object* v___x_5458_; lean_object* v_mctx_5459_; lean_object* v_zetaDeltaFVarIds_5460_; lean_object* v_postponed_5461_; lean_object* v_diag_5462_; lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5472_; 
v___x_5457_ = lean_st_ref_put(v___y_5435_, v___x_5456_);
v___x_5458_ = lean_st_ref_take(v___y_5438_);
v_mctx_5459_ = lean_ctor_get(v___x_5458_, 0);
v_zetaDeltaFVarIds_5460_ = lean_ctor_get(v___x_5458_, 2);
v_postponed_5461_ = lean_ctor_get(v___x_5458_, 3);
v_diag_5462_ = lean_ctor_get(v___x_5458_, 4);
v_isSharedCheck_5472_ = !lean_is_exclusive(v___x_5458_);
if (v_isSharedCheck_5472_ == 0)
{
lean_object* v_unused_5473_; 
v_unused_5473_ = lean_ctor_get(v___x_5458_, 1);
lean_dec(v_unused_5473_);
v___x_5464_ = v___x_5458_;
v_isShared_5465_ = v_isSharedCheck_5472_;
goto v_resetjp_5463_;
}
else
{
lean_inc(v_diag_5462_);
lean_inc(v_postponed_5461_);
lean_inc(v_zetaDeltaFVarIds_5460_);
lean_inc(v_mctx_5459_);
lean_dec(v___x_5458_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5472_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v___x_5467_; 
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 1, v___x_5439_);
v___x_5467_ = v___x_5464_;
goto v_reusejp_5466_;
}
else
{
lean_object* v_reuseFailAlloc_5471_; 
v_reuseFailAlloc_5471_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5471_, 0, v_mctx_5459_);
lean_ctor_set(v_reuseFailAlloc_5471_, 1, v___x_5439_);
lean_ctor_set(v_reuseFailAlloc_5471_, 2, v_zetaDeltaFVarIds_5460_);
lean_ctor_set(v_reuseFailAlloc_5471_, 3, v_postponed_5461_);
lean_ctor_set(v_reuseFailAlloc_5471_, 4, v_diag_5462_);
v___x_5467_ = v_reuseFailAlloc_5471_;
goto v_reusejp_5466_;
}
v_reusejp_5466_:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; lean_object* v___x_5470_; 
v___x_5468_ = lean_st_ref_put(v___y_5438_, v___x_5467_);
v___x_5469_ = lean_box(0);
v___x_5470_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5470_, 0, v___x_5469_);
return v___x_5470_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5477_, lean_object* v_isExporting_5478_, lean_object* v___x_5479_, lean_object* v___y_5480_, lean_object* v___x_5481_, lean_object* v_a_x3f_5482_, lean_object* v___y_5483_){
_start:
{
uint8_t v_isExporting_boxed_5484_; lean_object* v_res_5485_; 
v_isExporting_boxed_5484_ = lean_unbox(v_isExporting_5478_);
v_res_5485_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5477_, v_isExporting_boxed_5484_, v___x_5479_, v___y_5480_, v___x_5481_, v_a_x3f_5482_);
lean_dec(v_a_x3f_5482_);
lean_dec(v___y_5480_);
lean_dec(v___y_5477_);
return v_res_5485_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5486_; 
v___x_5486_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5486_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; 
v___x_5487_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5488_, 0, v___x_5487_);
return v___x_5488_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5489_; lean_object* v___x_5490_; 
v___x_5489_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5490_, 0, v___x_5489_);
lean_ctor_set(v___x_5490_, 1, v___x_5489_);
return v___x_5490_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5491_; lean_object* v___x_5492_; 
v___x_5491_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5492_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5492_, 0, v___x_5491_);
lean_ctor_set(v___x_5492_, 1, v___x_5491_);
lean_ctor_set(v___x_5492_, 2, v___x_5491_);
lean_ctor_set(v___x_5492_, 3, v___x_5491_);
lean_ctor_set(v___x_5492_, 4, v___x_5491_);
lean_ctor_set(v___x_5492_, 5, v___x_5491_);
return v___x_5492_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5493_, uint8_t v_isExporting_5494_, lean_object* v___y_5495_, lean_object* v___y_5496_, lean_object* v___y_5497_, lean_object* v___y_5498_){
_start:
{
lean_object* v___x_5500_; lean_object* v_env_5501_; lean_object* v___x_5502_; uint8_t v_isModule_5503_; 
v___x_5500_ = lean_st_ref_get(v___y_5498_);
v_env_5501_ = lean_ctor_get(v___x_5500_, 0);
lean_inc_ref(v_env_5501_);
lean_dec(v___x_5500_);
v___x_5502_ = l_Lean_Environment_header(v_env_5501_);
v_isModule_5503_ = lean_ctor_get_uint8(v___x_5502_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5502_);
if (v_isModule_5503_ == 0)
{
lean_object* v___x_5504_; 
lean_dec_ref(v_env_5501_);
lean_inc(v___y_5498_);
lean_inc_ref(v___y_5497_);
lean_inc(v___y_5496_);
lean_inc_ref(v___y_5495_);
v___x_5504_ = lean_apply_5(v_x_5493_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, lean_box(0));
return v___x_5504_;
}
else
{
uint8_t v_isExporting_5505_; 
v_isExporting_5505_ = lean_ctor_get_uint8(v_env_5501_, sizeof(void*)*8);
lean_dec_ref(v_env_5501_);
if (v_isExporting_5494_ == 0)
{
if (v_isExporting_5505_ == 0)
{
lean_object* v___x_5571_; 
lean_inc(v___y_5498_);
lean_inc_ref(v___y_5497_);
lean_inc(v___y_5496_);
lean_inc_ref(v___y_5495_);
v___x_5571_ = lean_apply_5(v_x_5493_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, lean_box(0));
return v___x_5571_;
}
else
{
goto v___jp_5506_;
}
}
else
{
if (v_isExporting_5505_ == 0)
{
goto v___jp_5506_;
}
else
{
lean_object* v___x_5572_; 
lean_inc(v___y_5498_);
lean_inc_ref(v___y_5497_);
lean_inc(v___y_5496_);
lean_inc_ref(v___y_5495_);
v___x_5572_ = lean_apply_5(v_x_5493_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, lean_box(0));
return v___x_5572_;
}
}
v___jp_5506_:
{
lean_object* v___x_5507_; lean_object* v_env_5508_; lean_object* v_nextMacroScope_5509_; lean_object* v_ngen_5510_; lean_object* v_auxDeclNGen_5511_; lean_object* v_traceState_5512_; lean_object* v_messages_5513_; lean_object* v_infoState_5514_; lean_object* v_snapshotTasks_5515_; lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5569_; 
v___x_5507_ = lean_st_ref_take(v___y_5498_);
v_env_5508_ = lean_ctor_get(v___x_5507_, 0);
v_nextMacroScope_5509_ = lean_ctor_get(v___x_5507_, 1);
v_ngen_5510_ = lean_ctor_get(v___x_5507_, 2);
v_auxDeclNGen_5511_ = lean_ctor_get(v___x_5507_, 3);
v_traceState_5512_ = lean_ctor_get(v___x_5507_, 4);
v_messages_5513_ = lean_ctor_get(v___x_5507_, 6);
v_infoState_5514_ = lean_ctor_get(v___x_5507_, 7);
v_snapshotTasks_5515_ = lean_ctor_get(v___x_5507_, 8);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5507_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; 
v_unused_5570_ = lean_ctor_get(v___x_5507_, 5);
lean_dec(v_unused_5570_);
v___x_5517_ = v___x_5507_;
v_isShared_5518_ = v_isSharedCheck_5569_;
goto v_resetjp_5516_;
}
else
{
lean_inc(v_snapshotTasks_5515_);
lean_inc(v_infoState_5514_);
lean_inc(v_messages_5513_);
lean_inc(v_traceState_5512_);
lean_inc(v_auxDeclNGen_5511_);
lean_inc(v_ngen_5510_);
lean_inc(v_nextMacroScope_5509_);
lean_inc(v_env_5508_);
lean_dec(v___x_5507_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5569_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5519_; lean_object* v___x_5520_; lean_object* v___x_5522_; 
v___x_5519_ = l_Lean_Environment_setExporting(v_env_5508_, v_isExporting_5494_);
v___x_5520_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 5, v___x_5520_);
lean_ctor_set(v___x_5517_, 0, v___x_5519_);
v___x_5522_ = v___x_5517_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5519_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_nextMacroScope_5509_);
lean_ctor_set(v_reuseFailAlloc_5568_, 2, v_ngen_5510_);
lean_ctor_set(v_reuseFailAlloc_5568_, 3, v_auxDeclNGen_5511_);
lean_ctor_set(v_reuseFailAlloc_5568_, 4, v_traceState_5512_);
lean_ctor_set(v_reuseFailAlloc_5568_, 5, v___x_5520_);
lean_ctor_set(v_reuseFailAlloc_5568_, 6, v_messages_5513_);
lean_ctor_set(v_reuseFailAlloc_5568_, 7, v_infoState_5514_);
lean_ctor_set(v_reuseFailAlloc_5568_, 8, v_snapshotTasks_5515_);
v___x_5522_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
lean_object* v___x_5523_; lean_object* v___x_5524_; lean_object* v_mctx_5525_; lean_object* v_zetaDeltaFVarIds_5526_; lean_object* v_postponed_5527_; lean_object* v_diag_5528_; lean_object* v___x_5530_; uint8_t v_isShared_5531_; uint8_t v_isSharedCheck_5566_; 
v___x_5523_ = lean_st_ref_put(v___y_5498_, v___x_5522_);
v___x_5524_ = lean_st_ref_take(v___y_5496_);
v_mctx_5525_ = lean_ctor_get(v___x_5524_, 0);
v_zetaDeltaFVarIds_5526_ = lean_ctor_get(v___x_5524_, 2);
v_postponed_5527_ = lean_ctor_get(v___x_5524_, 3);
v_diag_5528_ = lean_ctor_get(v___x_5524_, 4);
v_isSharedCheck_5566_ = !lean_is_exclusive(v___x_5524_);
if (v_isSharedCheck_5566_ == 0)
{
lean_object* v_unused_5567_; 
v_unused_5567_ = lean_ctor_get(v___x_5524_, 1);
lean_dec(v_unused_5567_);
v___x_5530_ = v___x_5524_;
v_isShared_5531_ = v_isSharedCheck_5566_;
goto v_resetjp_5529_;
}
else
{
lean_inc(v_diag_5528_);
lean_inc(v_postponed_5527_);
lean_inc(v_zetaDeltaFVarIds_5526_);
lean_inc(v_mctx_5525_);
lean_dec(v___x_5524_);
v___x_5530_ = lean_box(0);
v_isShared_5531_ = v_isSharedCheck_5566_;
goto v_resetjp_5529_;
}
v_resetjp_5529_:
{
lean_object* v___x_5532_; lean_object* v___x_5534_; 
v___x_5532_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5531_ == 0)
{
lean_ctor_set(v___x_5530_, 1, v___x_5532_);
v___x_5534_ = v___x_5530_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5565_; 
v_reuseFailAlloc_5565_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_mctx_5525_);
lean_ctor_set(v_reuseFailAlloc_5565_, 1, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5565_, 2, v_zetaDeltaFVarIds_5526_);
lean_ctor_set(v_reuseFailAlloc_5565_, 3, v_postponed_5527_);
lean_ctor_set(v_reuseFailAlloc_5565_, 4, v_diag_5528_);
v___x_5534_ = v_reuseFailAlloc_5565_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5535_; lean_object* v_r_5536_; 
v___x_5535_ = lean_st_ref_put(v___y_5496_, v___x_5534_);
lean_inc(v___y_5498_);
lean_inc_ref(v___y_5497_);
lean_inc(v___y_5496_);
lean_inc_ref(v___y_5495_);
v_r_5536_ = lean_apply_5(v_x_5493_, v___y_5495_, v___y_5496_, v___y_5497_, v___y_5498_, lean_box(0));
if (lean_obj_tag(v_r_5536_) == 0)
{
lean_object* v_a_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5553_; 
v_a_5537_ = lean_ctor_get(v_r_5536_, 0);
v_isSharedCheck_5553_ = !lean_is_exclusive(v_r_5536_);
if (v_isSharedCheck_5553_ == 0)
{
v___x_5539_ = v_r_5536_;
v_isShared_5540_ = v_isSharedCheck_5553_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_a_5537_);
lean_dec(v_r_5536_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5553_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5542_; 
lean_inc(v_a_5537_);
if (v_isShared_5540_ == 0)
{
lean_ctor_set_tag(v___x_5539_, 1);
v___x_5542_ = v___x_5539_;
goto v_reusejp_5541_;
}
else
{
lean_object* v_reuseFailAlloc_5552_; 
v_reuseFailAlloc_5552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5552_, 0, v_a_5537_);
v___x_5542_ = v_reuseFailAlloc_5552_;
goto v_reusejp_5541_;
}
v_reusejp_5541_:
{
lean_object* v___x_5543_; lean_object* v___x_5545_; uint8_t v_isShared_5546_; uint8_t v_isSharedCheck_5550_; 
v___x_5543_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5498_, v_isExporting_5505_, v___x_5520_, v___y_5496_, v___x_5532_, v___x_5542_);
lean_dec_ref(v___x_5542_);
v_isSharedCheck_5550_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5550_ == 0)
{
lean_object* v_unused_5551_; 
v_unused_5551_ = lean_ctor_get(v___x_5543_, 0);
lean_dec(v_unused_5551_);
v___x_5545_ = v___x_5543_;
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
else
{
lean_dec(v___x_5543_);
v___x_5545_ = lean_box(0);
v_isShared_5546_ = v_isSharedCheck_5550_;
goto v_resetjp_5544_;
}
v_resetjp_5544_:
{
lean_object* v___x_5548_; 
if (v_isShared_5546_ == 0)
{
lean_ctor_set(v___x_5545_, 0, v_a_5537_);
v___x_5548_ = v___x_5545_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_a_5537_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
}
}
else
{
lean_object* v_a_5554_; lean_object* v___x_5555_; lean_object* v___x_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5563_; 
v_a_5554_ = lean_ctor_get(v_r_5536_, 0);
lean_inc(v_a_5554_);
lean_dec_ref_known(v_r_5536_, 1);
v___x_5555_ = lean_box(0);
v___x_5556_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5498_, v_isExporting_5505_, v___x_5520_, v___y_5496_, v___x_5532_, v___x_5555_);
v_isSharedCheck_5563_ = !lean_is_exclusive(v___x_5556_);
if (v_isSharedCheck_5563_ == 0)
{
lean_object* v_unused_5564_; 
v_unused_5564_ = lean_ctor_get(v___x_5556_, 0);
lean_dec(v_unused_5564_);
v___x_5558_ = v___x_5556_;
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
else
{
lean_dec(v___x_5556_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5563_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v___x_5561_; 
if (v_isShared_5559_ == 0)
{
lean_ctor_set_tag(v___x_5558_, 1);
lean_ctor_set(v___x_5558_, 0, v_a_5554_);
v___x_5561_ = v___x_5558_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5562_; 
v_reuseFailAlloc_5562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5562_, 0, v_a_5554_);
v___x_5561_ = v_reuseFailAlloc_5562_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
return v___x_5561_;
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
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5573_, lean_object* v_isExporting_5574_, lean_object* v___y_5575_, lean_object* v___y_5576_, lean_object* v___y_5577_, lean_object* v___y_5578_, lean_object* v___y_5579_){
_start:
{
uint8_t v_isExporting_boxed_5580_; lean_object* v_res_5581_; 
v_isExporting_boxed_5580_ = lean_unbox(v_isExporting_5574_);
v_res_5581_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5573_, v_isExporting_boxed_5580_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_);
lean_dec(v___y_5578_);
lean_dec_ref(v___y_5577_);
lean_dec(v___y_5576_);
lean_dec_ref(v___y_5575_);
return v_res_5581_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5582_, uint8_t v_when_5583_, lean_object* v___y_5584_, lean_object* v___y_5585_, lean_object* v___y_5586_, lean_object* v___y_5587_){
_start:
{
if (v_when_5583_ == 0)
{
lean_object* v___x_5589_; 
lean_inc(v___y_5587_);
lean_inc_ref(v___y_5586_);
lean_inc(v___y_5585_);
lean_inc_ref(v___y_5584_);
v___x_5589_ = lean_apply_5(v_x_5582_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_, lean_box(0));
return v___x_5589_;
}
else
{
uint8_t v___x_5590_; lean_object* v___x_5591_; 
v___x_5590_ = 0;
v___x_5591_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5582_, v___x_5590_, v___y_5584_, v___y_5585_, v___y_5586_, v___y_5587_);
return v___x_5591_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5592_, lean_object* v_when_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_){
_start:
{
uint8_t v_when_boxed_5599_; lean_object* v_res_5600_; 
v_when_boxed_5599_ = lean_unbox(v_when_5593_);
v_res_5600_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5592_, v_when_boxed_5599_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
return v_res_5600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5601_, lean_object* v___y_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_){
_start:
{
lean_object* v___x_5607_; lean_object* v_a_5608_; lean_object* v___x_5609_; uint8_t v___x_5610_; lean_object* v___x_5611_; 
v___x_5607_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5601_, v___y_5603_);
v_a_5608_ = lean_ctor_get(v___x_5607_, 0);
lean_inc(v_a_5608_);
lean_dec_ref(v___x_5607_);
v___x_5609_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5609_, 0, v_a_5608_);
v___x_5610_ = 1;
v___x_5611_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5609_, v___x_5610_, v___y_5602_, v___y_5603_, v___y_5604_, v___y_5605_);
return v___x_5611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_){
_start:
{
lean_object* v_res_5618_; 
v_res_5618_ = l_Lean_Meta_letToHave___lam__0(v_e_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_);
lean_dec(v___y_5616_);
lean_dec_ref(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v___y_5613_);
return v_res_5618_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_){
_start:
{
lean_object* v_toCold_5626_; lean_object* v_options_5627_; lean_object* v___f_5628_; lean_object* v___x_5629_; lean_object* v___x_5630_; lean_object* v___x_5631_; 
v_toCold_5626_ = lean_ctor_get(v_a_5623_, 0);
v_options_5627_ = lean_ctor_get(v_toCold_5626_, 2);
v___f_5628_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5628_, 0, v_e_5620_);
v___x_5629_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5630_ = lean_box(0);
v___x_5631_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5629_, v_options_5627_, v___f_5628_, v___x_5630_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
return v___x_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5632_, lean_object* v_a_5633_, lean_object* v_a_5634_, lean_object* v_a_5635_, lean_object* v_a_5636_, lean_object* v_a_5637_){
_start:
{
lean_object* v_res_5638_; 
v_res_5638_ = l_Lean_Meta_letToHave(v_e_5632_, v_a_5633_, v_a_5634_, v_a_5635_, v_a_5636_);
lean_dec(v_a_5636_);
lean_dec_ref(v_a_5635_);
lean_dec(v_a_5634_);
lean_dec_ref(v_a_5633_);
return v_res_5638_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5639_, lean_object* v_x_5640_, uint8_t v_isExporting_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_, lean_object* v___y_5645_){
_start:
{
lean_object* v___x_5647_; 
v___x_5647_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5640_, v_isExporting_5641_, v___y_5642_, v___y_5643_, v___y_5644_, v___y_5645_);
return v___x_5647_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5648_, lean_object* v_x_5649_, lean_object* v_isExporting_5650_, lean_object* v___y_5651_, lean_object* v___y_5652_, lean_object* v___y_5653_, lean_object* v___y_5654_, lean_object* v___y_5655_){
_start:
{
uint8_t v_isExporting_boxed_5656_; lean_object* v_res_5657_; 
v_isExporting_boxed_5656_ = lean_unbox(v_isExporting_5650_);
v_res_5657_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5648_, v_x_5649_, v_isExporting_boxed_5656_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_);
lean_dec(v___y_5654_);
lean_dec_ref(v___y_5653_);
lean_dec(v___y_5652_);
lean_dec_ref(v___y_5651_);
return v_res_5657_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5658_, lean_object* v_x_5659_, uint8_t v_when_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_, lean_object* v___y_5664_){
_start:
{
lean_object* v___x_5666_; 
v___x_5666_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5659_, v_when_5660_, v___y_5661_, v___y_5662_, v___y_5663_, v___y_5664_);
return v___x_5666_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5667_, lean_object* v_x_5668_, lean_object* v_when_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_, lean_object* v___y_5674_){
_start:
{
uint8_t v_when_boxed_5675_; lean_object* v_res_5676_; 
v_when_boxed_5675_ = lean_unbox(v_when_5669_);
v_res_5676_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5667_, v_x_5668_, v_when_boxed_5675_, v___y_5670_, v___y_5671_, v___y_5672_, v___y_5673_);
lean_dec(v___y_5673_);
lean_dec_ref(v___y_5672_);
lean_dec(v___y_5671_);
lean_dec_ref(v___y_5670_);
return v_res_5676_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5733_; uint8_t v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; 
v___x_5733_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5734_ = 0;
v___x_5735_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5736_ = l_Lean_registerTraceClass(v___x_5733_, v___x_5734_, v___x_5735_);
if (lean_obj_tag(v___x_5736_) == 0)
{
lean_object* v___x_5737_; lean_object* v___x_5738_; 
lean_dec_ref_known(v___x_5736_, 1);
v___x_5737_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5738_ = l_Lean_registerTraceClass(v___x_5737_, v___x_5734_, v___x_5735_);
return v___x_5738_;
}
else
{
return v___x_5736_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5739_){
_start:
{
lean_object* v_res_5740_; 
v_res_5740_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5740_;
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
