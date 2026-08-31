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
v___x_210_ = lean_st_ref_put(v_a_174_, v___x_209_);
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
v___x_360_ = lean_st_ref_put(v_a_348_, v___x_359_);
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
v___x_483_ = lean_st_ref_put(v___y_473_, v___x_482_);
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
v___x_616_ = lean_st_ref_put(v___y_597_, v___x_615_);
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
lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___f_1235_; lean_object* v___x_1419__overap_1236_; lean_object* v___x_1237_; 
v___x_1232_ = l_StateRefT_x27_instMonad___redArg(v___x_1231_);
v___x_1233_ = l_Lean_Meta_LetToHave_instInhabitedResult_default;
v___x_1234_ = l_instInhabitedOfMonad___redArg(v___x_1232_, v___x_1233_);
v___f_1235_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1235_, 0, v___x_1234_);
v___x_1419__overap_1236_ = lean_panic_fn_borrowed(v___f_1235_, v_msg_1175_);
lean_dec_ref(v___f_1235_);
lean_inc(v___y_1181_);
lean_inc_ref(v___y_1180_);
lean_inc(v___y_1179_);
lean_inc_ref(v___y_1178_);
lean_inc(v___y_1177_);
lean_inc(v___y_1176_);
v___x_1237_ = lean_apply_7(v___x_1419__overap_1236_, v___y_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_, lean_box(0));
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
v___x_1264_ = lean_alloc_ctor(0, 11, 0);
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
lean_ctor_set(v___x_1264_, 10, v___x_1262_);
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
v_options_1408_ = lean_ctor_get(v___y_1400_, 1);
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
v_ref_1425_ = lean_ctor_get(v___y_1422_, 4);
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
lean_object* v_toCold_1452_; lean_object* v_options_1453_; lean_object* v_currRecDepth_1454_; lean_object* v_maxRecDepth_1455_; lean_object* v_ref_1456_; lean_object* v_currNamespace_1457_; lean_object* v_openDecls_1458_; lean_object* v_initHeartbeats_1459_; lean_object* v_maxHeartbeats_1460_; lean_object* v_currMacroScope_1461_; uint8_t v_diag_1462_; uint8_t v_suppressElabErrors_1463_; lean_object* v_ref_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; 
v_toCold_1452_ = lean_ctor_get(v___y_1449_, 0);
v_options_1453_ = lean_ctor_get(v___y_1449_, 1);
v_currRecDepth_1454_ = lean_ctor_get(v___y_1449_, 2);
v_maxRecDepth_1455_ = lean_ctor_get(v___y_1449_, 3);
v_ref_1456_ = lean_ctor_get(v___y_1449_, 4);
v_currNamespace_1457_ = lean_ctor_get(v___y_1449_, 5);
v_openDecls_1458_ = lean_ctor_get(v___y_1449_, 6);
v_initHeartbeats_1459_ = lean_ctor_get(v___y_1449_, 7);
v_maxHeartbeats_1460_ = lean_ctor_get(v___y_1449_, 8);
v_currMacroScope_1461_ = lean_ctor_get(v___y_1449_, 9);
v_diag_1462_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*10);
v_suppressElabErrors_1463_ = lean_ctor_get_uint8(v___y_1449_, sizeof(void*)*10 + 1);
v_ref_1464_ = l_Lean_replaceRef(v_ref_1443_, v_ref_1456_);
lean_inc(v_currMacroScope_1461_);
lean_inc(v_maxHeartbeats_1460_);
lean_inc(v_initHeartbeats_1459_);
lean_inc(v_openDecls_1458_);
lean_inc(v_currNamespace_1457_);
lean_inc(v_maxRecDepth_1455_);
lean_inc(v_currRecDepth_1454_);
lean_inc_ref(v_options_1453_);
lean_inc_ref(v_toCold_1452_);
v___x_1465_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_1465_, 0, v_toCold_1452_);
lean_ctor_set(v___x_1465_, 1, v_options_1453_);
lean_ctor_set(v___x_1465_, 2, v_currRecDepth_1454_);
lean_ctor_set(v___x_1465_, 3, v_maxRecDepth_1455_);
lean_ctor_set(v___x_1465_, 4, v_ref_1464_);
lean_ctor_set(v___x_1465_, 5, v_currNamespace_1457_);
lean_ctor_set(v___x_1465_, 6, v_openDecls_1458_);
lean_ctor_set(v___x_1465_, 7, v_initHeartbeats_1459_);
lean_ctor_set(v___x_1465_, 8, v_maxHeartbeats_1460_);
lean_ctor_set(v___x_1465_, 9, v_currMacroScope_1461_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*10, v_diag_1462_);
lean_ctor_set_uint8(v___x_1465_, sizeof(void*)*10 + 1, v_suppressElabErrors_1463_);
v___x_1466_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1444_, v___y_1447_, v___y_1448_, v___x_1465_, v___y_1450_);
lean_dec_ref_known(v___x_1465_, 10);
return v___x_1466_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg___boxed(lean_object* v_ref_1467_, lean_object* v_msg_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_){
_start:
{
lean_object* v_res_1476_; 
v_res_1476_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1467_, v_msg_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
lean_dec(v___y_1474_);
lean_dec_ref(v___y_1473_);
lean_dec(v___y_1472_);
lean_dec_ref(v___y_1471_);
lean_dec(v___y_1470_);
lean_dec(v___y_1469_);
lean_dec(v_ref_1467_);
return v_res_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(lean_object* v_ref_1477_, lean_object* v_msg_1478_, lean_object* v_declHint_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v___x_1487_; lean_object* v_a_1488_; lean_object* v___x_1489_; 
v___x_1487_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4(v_msg_1478_, v_declHint_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
v_a_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_a_1488_);
lean_dec_ref(v___x_1487_);
v___x_1489_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1477_, v_a_1488_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_);
return v___x_1489_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg___boxed(lean_object* v_ref_1490_, lean_object* v_msg_1491_, lean_object* v_declHint_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v_res_1500_; 
v_res_1500_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1490_, v_msg_1491_, v_declHint_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
lean_dec_ref(v___y_1495_);
lean_dec(v___y_1494_);
lean_dec(v___y_1493_);
lean_dec(v_ref_1490_);
return v_res_1500_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; 
v___x_1502_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__0));
v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__2));
v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(lean_object* v_ref_1507_, lean_object* v_constName_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v___x_1516_; uint8_t v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1516_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_1517_ = 0;
lean_inc(v_constName_1508_);
v___x_1518_ = l_Lean_MessageData_ofConstName(v_constName_1508_, v___x_1517_);
v___x_1519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1516_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
v___x_1520_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___closed__3);
v___x_1521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1519_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1507_, v___x_1521_, v_constName_1508_, v___y_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_, v___y_1514_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_ref_1523_, lean_object* v_constName_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1523_, v_constName_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
lean_dec(v___y_1526_);
lean_dec(v___y_1525_);
lean_dec(v_ref_1523_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(lean_object* v_constName_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_, lean_object* v___y_1539_){
_start:
{
lean_object* v_ref_1541_; lean_object* v___x_1542_; 
v_ref_1541_ = lean_ctor_get(v___y_1538_, 4);
v___x_1542_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1541_, v_constName_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_, v___y_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg___boxed(lean_object* v_constName_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1543_, v___y_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
lean_dec(v___y_1544_);
return v_res_1551_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(lean_object* v_constName_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v___x_1560_; lean_object* v_env_1561_; uint8_t v___x_1562_; lean_object* v___x_1563_; 
v___x_1560_ = lean_st_ref_get(v___y_1558_);
v_env_1561_ = lean_ctor_get(v___x_1560_, 0);
lean_inc_ref(v_env_1561_);
lean_dec(v___x_1560_);
v___x_1562_ = 0;
lean_inc(v_constName_1552_);
v___x_1563_ = l_Lean_Environment_findConstVal_x3f(v_env_1561_, v_constName_1552_, v___x_1562_);
if (lean_obj_tag(v___x_1563_) == 0)
{
lean_object* v___x_1564_; 
v___x_1564_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1552_, v___y_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_, v___y_1558_);
return v___x_1564_;
}
else
{
lean_object* v_val_1565_; lean_object* v___x_1567_; uint8_t v_isShared_1568_; uint8_t v_isSharedCheck_1572_; 
lean_dec(v_constName_1552_);
v_val_1565_ = lean_ctor_get(v___x_1563_, 0);
v_isSharedCheck_1572_ = !lean_is_exclusive(v___x_1563_);
if (v_isSharedCheck_1572_ == 0)
{
v___x_1567_ = v___x_1563_;
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
else
{
lean_inc(v_val_1565_);
lean_dec(v___x_1563_);
v___x_1567_ = lean_box(0);
v_isShared_1568_ = v_isSharedCheck_1572_;
goto v_resetjp_1566_;
}
v_resetjp_1566_:
{
lean_object* v___x_1570_; 
if (v_isShared_1568_ == 0)
{
lean_ctor_set_tag(v___x_1567_, 0);
v___x_1570_ = v___x_1567_;
goto v_reusejp_1569_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_val_1565_);
v___x_1570_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1569_;
}
v_reusejp_1569_:
{
return v___x_1570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0___boxed(lean_object* v_constName_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_constName_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec(v___y_1574_);
return v_res_1581_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1585_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_1586_ = lean_unsigned_to_nat(35u);
v___x_1587_ = lean_unsigned_to_nat(203u);
v___x_1588_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__1));
v___x_1589_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_1590_ = l_mkPanicMessageWithDecl(v___x_1589_, v___x_1588_, v___x_1587_, v___x_1586_, v___x_1585_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(lean_object* v_e_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
if (lean_obj_tag(v_e_1591_) == 4)
{
lean_object* v_declName_1599_; lean_object* v_us_1600_; lean_object* v___x_1601_; 
v_declName_1599_ = lean_ctor_get(v_e_1591_, 0);
v_us_1600_ = lean_ctor_get(v_e_1591_, 1);
lean_inc(v_declName_1599_);
v___x_1601_ = l_Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0(v_declName_1599_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
if (lean_obj_tag(v___x_1601_) == 0)
{
lean_object* v_a_1602_; lean_object* v_levelParams_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_a_1602_ = lean_ctor_get(v___x_1601_, 0);
lean_inc(v_a_1602_);
lean_dec_ref_known(v___x_1601_, 1);
v_levelParams_1603_ = lean_ctor_get(v_a_1602_, 1);
v___x_1604_ = l_List_lengthTR___redArg(v_levelParams_1603_);
v___x_1605_ = l_List_lengthTR___redArg(v_us_1600_);
v___x_1606_ = lean_nat_dec_eq(v___x_1604_, v___x_1605_);
lean_dec(v___x_1605_);
lean_dec(v___x_1604_);
if (v___x_1606_ == 0)
{
lean_object* v___x_1607_; 
lean_inc(v_us_1600_);
lean_inc(v_declName_1599_);
lean_dec(v_a_1602_);
lean_dec_ref_known(v_e_1591_, 2);
v___x_1607_ = l_Lean_Meta_throwIncorrectNumberOfLevels___redArg(v_declName_1599_, v_us_1600_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1607_;
}
else
{
lean_object* v___x_1608_; 
lean_inc(v_us_1600_);
v___x_1608_ = l_Lean_Core_instantiateTypeLevelParams___redArg(v_a_1602_, v_us_1600_, v___y_1597_);
if (lean_obj_tag(v___x_1608_) == 0)
{
lean_object* v_a_1609_; lean_object* v___x_1611_; uint8_t v_isShared_1612_; uint8_t v_isSharedCheck_1618_; 
v_a_1609_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1618_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1618_ == 0)
{
v___x_1611_ = v___x_1608_;
v_isShared_1612_ = v_isSharedCheck_1618_;
goto v_resetjp_1610_;
}
else
{
lean_inc(v_a_1609_);
lean_dec(v___x_1608_);
v___x_1611_ = lean_box(0);
v_isShared_1612_ = v_isSharedCheck_1618_;
goto v_resetjp_1610_;
}
v_resetjp_1610_:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1616_; 
v___x_1613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1613_, 0, v_a_1609_);
v___x_1614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1614_, 0, v_e_1591_);
lean_ctor_set(v___x_1614_, 1, v___x_1613_);
if (v_isShared_1612_ == 0)
{
lean_ctor_set(v___x_1611_, 0, v___x_1614_);
v___x_1616_ = v___x_1611_;
goto v_reusejp_1615_;
}
else
{
lean_object* v_reuseFailAlloc_1617_; 
v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1617_, 0, v___x_1614_);
v___x_1616_ = v_reuseFailAlloc_1617_;
goto v_reusejp_1615_;
}
v_reusejp_1615_:
{
return v___x_1616_;
}
}
}
else
{
lean_object* v_a_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1626_; 
lean_dec_ref_known(v_e_1591_, 2);
v_a_1619_ = lean_ctor_get(v___x_1608_, 0);
v_isSharedCheck_1626_ = !lean_is_exclusive(v___x_1608_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1621_ = v___x_1608_;
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_a_1619_);
lean_dec(v___x_1608_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1626_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1624_; 
if (v_isShared_1622_ == 0)
{
v___x_1624_ = v___x_1621_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_a_1619_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
return v___x_1624_;
}
}
}
}
}
else
{
lean_object* v_a_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1634_; 
lean_dec_ref_known(v_e_1591_, 2);
v_a_1627_ = lean_ctor_get(v___x_1601_, 0);
v_isSharedCheck_1634_ = !lean_is_exclusive(v___x_1601_);
if (v_isSharedCheck_1634_ == 0)
{
v___x_1629_ = v___x_1601_;
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_a_1627_);
lean_dec(v___x_1601_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1634_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1632_; 
if (v_isShared_1630_ == 0)
{
v___x_1632_ = v___x_1629_;
goto v_reusejp_1631_;
}
else
{
lean_object* v_reuseFailAlloc_1633_; 
v_reuseFailAlloc_1633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1633_, 0, v_a_1627_);
v___x_1632_ = v_reuseFailAlloc_1633_;
goto v_reusejp_1631_;
}
v_reusejp_1631_:
{
return v___x_1632_;
}
}
}
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; 
lean_dec_ref(v_e_1591_);
v___x_1635_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__3);
v___x_1636_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_1635_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1636_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed(lean_object* v_e_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_, lean_object* v___y_1641_, lean_object* v___y_1642_, lean_object* v___y_1643_, lean_object* v___y_1644_){
_start:
{
lean_object* v_res_1645_; 
v_res_1645_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0(v_e_1637_, v___y_1638_, v___y_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_);
lean_dec(v___y_1643_);
lean_dec_ref(v___y_1642_);
lean_dec(v___y_1641_);
lean_dec_ref(v___y_1640_);
lean_dec(v___y_1639_);
lean_dec(v___y_1638_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(lean_object* v_e_1646_, lean_object* v_a_1647_, lean_object* v_a_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_){
_start:
{
lean_object* v___y_1654_; lean_object* v___x_1655_; 
lean_inc_ref(v_e_1646_);
v___y_1654_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___boxed), 8, 1);
lean_closure_set(v___y_1654_, 0, v_e_1646_);
v___x_1655_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_whenCheck(v_e_1646_, v___y_1654_, v_a_1647_, v_a_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___boxed(lean_object* v_e_1656_, lean_object* v_a_1657_, lean_object* v_a_1658_, lean_object* v_a_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_, lean_object* v_a_1663_){
_start:
{
lean_object* v_res_1664_; 
v_res_1664_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_1656_, v_a_1657_, v_a_1658_, v_a_1659_, v_a_1660_, v_a_1661_, v_a_1662_);
lean_dec(v_a_1662_);
lean_dec_ref(v_a_1661_);
lean_dec(v_a_1660_);
lean_dec_ref(v_a_1659_);
lean_dec(v_a_1658_);
lean_dec(v_a_1657_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(lean_object* v_00_u03b1_1665_, lean_object* v_constName_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_constName_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0(v_00_u03b1_1675_, v_constName_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec(v___y_1677_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_1685_, lean_object* v_ref_1686_, lean_object* v_constName_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_){
_start:
{
lean_object* v___x_1695_; 
v___x_1695_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___redArg(v_ref_1686_, v_constName_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
return v___x_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_1696_, lean_object* v_ref_1697_, lean_object* v_constName_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2(v_00_u03b1_1696_, v_ref_1697_, v_constName_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
lean_dec(v___y_1704_);
lean_dec_ref(v___y_1703_);
lean_dec(v___y_1702_);
lean_dec_ref(v___y_1701_);
lean_dec(v___y_1700_);
lean_dec(v___y_1699_);
lean_dec(v_ref_1697_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(lean_object* v_00_u03b1_1707_, lean_object* v_ref_1708_, lean_object* v_msg_1709_, lean_object* v_declHint_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___redArg(v_ref_1708_, v_msg_1709_, v_declHint_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_00_u03b1_1719_, lean_object* v_ref_1720_, lean_object* v_msg_1721_, lean_object* v_declHint_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3(v_00_u03b1_1719_, v_ref_1720_, v_msg_1721_, v_declHint_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
lean_dec(v___y_1726_);
lean_dec_ref(v___y_1725_);
lean_dec(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec(v_ref_1720_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(lean_object* v_msg_1731_, lean_object* v_declHint_1732_, lean_object* v___y_1733_, lean_object* v___y_1734_, lean_object* v___y_1735_, lean_object* v___y_1736_, lean_object* v___y_1737_, lean_object* v___y_1738_){
_start:
{
lean_object* v___x_1740_; 
v___x_1740_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___redArg(v_msg_1731_, v_declHint_1732_, v___y_1738_);
return v___x_1740_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5___boxed(lean_object* v_msg_1741_, lean_object* v_declHint_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_, lean_object* v___y_1748_, lean_object* v___y_1749_){
_start:
{
lean_object* v_res_1750_; 
v_res_1750_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__4_spec__5(v_msg_1741_, v_declHint_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_, v___y_1747_, v___y_1748_);
lean_dec(v___y_1748_);
lean_dec_ref(v___y_1747_);
lean_dec(v___y_1746_);
lean_dec_ref(v___y_1745_);
lean_dec(v___y_1744_);
lean_dec(v___y_1743_);
return v_res_1750_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(lean_object* v_00_u03b1_1751_, lean_object* v_ref_1752_, lean_object* v_msg_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_){
_start:
{
lean_object* v___x_1761_; 
v___x_1761_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___redArg(v_ref_1752_, v_msg_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5___boxed(lean_object* v_00_u03b1_1762_, lean_object* v_ref_1763_, lean_object* v_msg_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_, lean_object* v___y_1769_, lean_object* v___y_1770_, lean_object* v___y_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5(v_00_u03b1_1762_, v_ref_1763_, v_msg_1764_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_, v___y_1769_, v___y_1770_);
lean_dec(v___y_1770_);
lean_dec_ref(v___y_1769_);
lean_dec(v___y_1768_);
lean_dec_ref(v___y_1767_);
lean_dec(v___y_1766_);
lean_dec(v___y_1765_);
lean_dec(v_ref_1763_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(lean_object* v_00_u03b1_1773_, lean_object* v_msg_1774_, lean_object* v___y_1775_, lean_object* v___y_1776_, lean_object* v___y_1777_, lean_object* v___y_1778_, lean_object* v___y_1779_, lean_object* v___y_1780_){
_start:
{
lean_object* v___x_1782_; 
v___x_1782_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v_msg_1774_, v___y_1777_, v___y_1778_, v___y_1779_, v___y_1780_);
return v___x_1782_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1783_, lean_object* v_msg_1784_, lean_object* v___y_1785_, lean_object* v___y_1786_, lean_object* v___y_1787_, lean_object* v___y_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_){
_start:
{
lean_object* v_res_1792_; 
v_res_1792_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7(v_00_u03b1_1783_, v_msg_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
lean_dec(v___y_1790_);
lean_dec_ref(v___y_1789_);
lean_dec(v___y_1788_);
lean_dec_ref(v___y_1787_);
lean_dec(v___y_1786_);
lean_dec(v___y_1785_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(lean_object* v_r_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_, lean_object* v_a_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_){
_start:
{
uint8_t v___x_1801_; 
v___x_1801_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1794_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1802_, 0, v_r_1793_);
return v___x_1802_;
}
else
{
lean_object* v___x_1803_; 
lean_inc_ref(v_r_1793_);
v___x_1803_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_r_1793_, v_a_1795_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1856_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1806_ = v___x_1803_;
v_isShared_1807_ = v_isSharedCheck_1856_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1803_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1856_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v_expr_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1854_; 
v_expr_1808_ = lean_ctor_get(v_r_1793_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v_r_1793_);
if (v_isSharedCheck_1854_ == 0)
{
lean_object* v_unused_1855_; 
v_unused_1855_ = lean_ctor_get(v_r_1793_, 1);
lean_dec(v_unused_1855_);
v___x_1810_ = v_r_1793_;
v_isShared_1811_ = v_isSharedCheck_1854_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_expr_1808_);
lean_dec(v_r_1793_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1854_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
uint8_t v___x_1812_; 
v___x_1812_ = l_Lean_Expr_isSort(v_a_1804_);
if (v___x_1812_ == 0)
{
lean_object* v___x_1813_; 
lean_del_object(v___x_1806_);
lean_inc(v_a_1799_);
lean_inc_ref(v_a_1798_);
lean_inc(v_a_1797_);
lean_inc_ref(v_a_1796_);
v___x_1813_ = lean_whnf(v_a_1804_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v_a_1814_; lean_object* v___x_1816_; uint8_t v_isShared_1817_; uint8_t v_isSharedCheck_1838_; 
v_a_1814_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1816_ = v___x_1813_;
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
else
{
lean_inc(v_a_1814_);
lean_dec(v___x_1813_);
v___x_1816_ = lean_box(0);
v_isShared_1817_ = v_isSharedCheck_1838_;
goto v_resetjp_1815_;
}
v_resetjp_1815_:
{
if (lean_obj_tag(v_a_1814_) == 3)
{
lean_object* v___x_1818_; lean_object* v_count_1819_; lean_object* v_results_1820_; lean_object* v___x_1822_; uint8_t v_isShared_1823_; uint8_t v_isSharedCheck_1836_; 
v___x_1818_ = lean_st_ref_take(v_a_1795_);
v_count_1819_ = lean_ctor_get(v___x_1818_, 0);
v_results_1820_ = lean_ctor_get(v___x_1818_, 1);
v_isSharedCheck_1836_ = !lean_is_exclusive(v___x_1818_);
if (v_isSharedCheck_1836_ == 0)
{
v___x_1822_ = v___x_1818_;
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
else
{
lean_inc(v_results_1820_);
lean_inc(v_count_1819_);
lean_dec(v___x_1818_);
v___x_1822_ = lean_box(0);
v_isShared_1823_ = v_isSharedCheck_1836_;
goto v_resetjp_1821_;
}
v_resetjp_1821_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1814_);
lean_inc_ref(v_expr_1808_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1824_);
v___x_1826_ = v___x_1810_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v_expr_1808_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v___x_1824_);
v___x_1826_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; lean_object* v___x_1829_; 
lean_inc_ref(v___x_1826_);
v___x_1827_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type_spec__0___redArg(v_results_1820_, v_expr_1808_, v___x_1826_);
if (v_isShared_1823_ == 0)
{
lean_ctor_set(v___x_1822_, 1, v___x_1827_);
v___x_1829_ = v___x_1822_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_count_1819_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v___x_1827_);
v___x_1829_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = lean_st_ref_put(v_a_1795_, v___x_1829_);
if (v_isShared_1817_ == 0)
{
lean_ctor_set(v___x_1816_, 0, v___x_1826_);
v___x_1832_ = v___x_1816_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1833_; 
v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1833_, 0, v___x_1826_);
v___x_1832_ = v_reuseFailAlloc_1833_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
return v___x_1832_;
}
}
}
}
}
else
{
lean_object* v___x_1837_; 
lean_del_object(v___x_1816_);
lean_dec(v_a_1814_);
lean_del_object(v___x_1810_);
v___x_1837_ = l_Lean_Meta_throwTypeExpected___redArg(v_expr_1808_, v_a_1796_, v_a_1797_, v_a_1798_, v_a_1799_);
return v___x_1837_;
}
}
}
else
{
lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1846_; 
lean_del_object(v___x_1810_);
lean_dec_ref(v_expr_1808_);
v_a_1839_ = lean_ctor_get(v___x_1813_, 0);
v_isSharedCheck_1846_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1846_ == 0)
{
v___x_1841_ = v___x_1813_;
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1813_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1846_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1844_; 
if (v_isShared_1842_ == 0)
{
v___x_1844_ = v___x_1841_;
goto v_reusejp_1843_;
}
else
{
lean_object* v_reuseFailAlloc_1845_; 
v_reuseFailAlloc_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1845_, 0, v_a_1839_);
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
else
{
lean_object* v___x_1847_; lean_object* v___x_1849_; 
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_a_1804_);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1847_);
v___x_1849_ = v___x_1810_;
goto v_reusejp_1848_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v_expr_1808_);
lean_ctor_set(v_reuseFailAlloc_1853_, 1, v___x_1847_);
v___x_1849_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1848_;
}
v_reusejp_1848_:
{
lean_object* v___x_1851_; 
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 0, v___x_1849_);
v___x_1851_ = v___x_1806_;
goto v_reusejp_1850_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v___x_1849_);
v___x_1851_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1850_;
}
v_reusejp_1850_:
{
return v___x_1851_;
}
}
}
}
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec_ref(v_r_1793_);
v_a_1857_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1803_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1803_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType___boxed(lean_object* v_r_1865_, lean_object* v_a_1866_, lean_object* v_a_1867_, lean_object* v_a_1868_, lean_object* v_a_1869_, lean_object* v_a_1870_, lean_object* v_a_1871_, lean_object* v_a_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_r_1865_, v_a_1866_, v_a_1867_, v_a_1868_, v_a_1869_, v_a_1870_, v_a_1871_);
lean_dec(v_a_1871_);
lean_dec_ref(v_a_1870_);
lean_dec(v_a_1869_);
lean_dec_ref(v_a_1868_);
lean_dec(v_a_1867_);
lean_dec(v_a_1866_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(lean_object* v_msg_1874_){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = l_Lean_instInhabitedExpr;
v___x_1876_ = lean_panic_fn_borrowed(v___x_1875_, v_msg_1874_);
return v___x_1876_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1880_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__2));
v___x_1881_ = lean_unsigned_to_nat(18u);
v___x_1882_ = lean_unsigned_to_nat(1847u);
v___x_1883_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__1));
v___x_1884_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_1885_ = l_mkPanicMessageWithDecl(v___x_1884_, v___x_1883_, v___x_1882_, v___x_1881_, v___x_1880_);
return v___x_1885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(lean_object* v_e_1886_, lean_object* v_f_1887_, lean_object* v_a_1888_, lean_object* v_a_1889_, lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v___y_1897_; lean_object* v___y_1902_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1910_; lean_object* v_fType_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1931_; lean_object* v___y_1932_; uint8_t v___x_1971_; 
v___x_1971_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_1889_);
if (v___x_1971_ == 0)
{
if (lean_obj_tag(v_e_1886_) == 5)
{
lean_object* v_expr_1972_; lean_object* v_expr_1973_; lean_object* v_fn_1974_; lean_object* v_arg_1975_; size_t v___x_1976_; size_t v___x_1977_; uint8_t v___x_1978_; 
v_expr_1972_ = lean_ctor_get(v_f_1887_, 0);
lean_inc_ref(v_expr_1972_);
lean_dec_ref(v_f_1887_);
v_expr_1973_ = lean_ctor_get(v_a_1888_, 0);
lean_inc_ref(v_expr_1973_);
lean_dec_ref(v_a_1888_);
v_fn_1974_ = lean_ctor_get(v_e_1886_, 0);
v_arg_1975_ = lean_ctor_get(v_e_1886_, 1);
v___x_1976_ = lean_ptr_addr(v_fn_1974_);
v___x_1977_ = lean_ptr_addr(v_expr_1972_);
v___x_1978_ = lean_usize_dec_eq(v___x_1976_, v___x_1977_);
if (v___x_1978_ == 0)
{
lean_object* v___x_1979_; 
lean_dec_ref_known(v_e_1886_, 2);
v___x_1979_ = l_Lean_Expr_app___override(v_expr_1972_, v_expr_1973_);
v___y_1897_ = v___x_1979_;
goto v___jp_1896_;
}
else
{
size_t v___x_1980_; size_t v___x_1981_; uint8_t v___x_1982_; 
v___x_1980_ = lean_ptr_addr(v_arg_1975_);
v___x_1981_ = lean_ptr_addr(v_expr_1973_);
v___x_1982_ = lean_usize_dec_eq(v___x_1980_, v___x_1981_);
if (v___x_1982_ == 0)
{
lean_object* v___x_1983_; 
lean_dec_ref_known(v_e_1886_, 2);
v___x_1983_ = l_Lean_Expr_app___override(v_expr_1972_, v_expr_1973_);
v___y_1897_ = v___x_1983_;
goto v___jp_1896_;
}
else
{
lean_dec_ref(v_expr_1973_);
lean_dec_ref(v_expr_1972_);
v___y_1897_ = v_e_1886_;
goto v___jp_1896_;
}
}
}
else
{
lean_object* v___x_1984_; lean_object* v___x_1985_; 
lean_dec_ref(v_a_1888_);
lean_dec_ref(v_f_1887_);
lean_dec_ref(v_e_1886_);
v___x_1984_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1985_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1984_);
v___y_1897_ = v___x_1985_;
goto v___jp_1896_;
}
}
else
{
lean_object* v___x_1986_; 
lean_inc_ref(v_f_1887_);
v___x_1986_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_f_1887_, v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1986_) == 0)
{
lean_object* v_a_1987_; uint8_t v___x_1988_; 
v_a_1987_ = lean_ctor_get(v___x_1986_, 0);
lean_inc(v_a_1987_);
lean_dec_ref_known(v___x_1986_, 1);
v___x_1988_ = l_Lean_Expr_isForall(v_a_1987_);
if (v___x_1988_ == 0)
{
lean_object* v___x_1989_; 
lean_inc(v_a_1894_);
lean_inc_ref(v_a_1893_);
lean_inc(v_a_1892_);
lean_inc_ref(v_a_1891_);
v___x_1989_ = lean_whnf(v_a_1987_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_1990_);
lean_dec_ref_known(v___x_1989_, 1);
v_fType_1927_ = v_a_1990_;
v___y_1928_ = v_a_1890_;
v___y_1929_ = v_a_1891_;
v___y_1930_ = v_a_1892_;
v___y_1931_ = v_a_1893_;
v___y_1932_ = v_a_1894_;
goto v___jp_1926_;
}
else
{
lean_object* v_a_1991_; lean_object* v___x_1993_; uint8_t v_isShared_1994_; uint8_t v_isSharedCheck_1998_; 
lean_dec_ref(v_a_1888_);
lean_dec_ref(v_f_1887_);
lean_dec_ref(v_e_1886_);
v_a_1991_ = lean_ctor_get(v___x_1989_, 0);
v_isSharedCheck_1998_ = !lean_is_exclusive(v___x_1989_);
if (v_isSharedCheck_1998_ == 0)
{
v___x_1993_ = v___x_1989_;
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
else
{
lean_inc(v_a_1991_);
lean_dec(v___x_1989_);
v___x_1993_ = lean_box(0);
v_isShared_1994_ = v_isSharedCheck_1998_;
goto v_resetjp_1992_;
}
v_resetjp_1992_:
{
lean_object* v___x_1996_; 
if (v_isShared_1994_ == 0)
{
v___x_1996_ = v___x_1993_;
goto v_reusejp_1995_;
}
else
{
lean_object* v_reuseFailAlloc_1997_; 
v_reuseFailAlloc_1997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1997_, 0, v_a_1991_);
v___x_1996_ = v_reuseFailAlloc_1997_;
goto v_reusejp_1995_;
}
v_reusejp_1995_:
{
return v___x_1996_;
}
}
}
}
else
{
v_fType_1927_ = v_a_1987_;
v___y_1928_ = v_a_1890_;
v___y_1929_ = v_a_1891_;
v___y_1930_ = v_a_1892_;
v___y_1931_ = v_a_1893_;
v___y_1932_ = v_a_1894_;
goto v___jp_1926_;
}
}
else
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2006_; 
lean_dec_ref(v_a_1888_);
lean_dec_ref(v_f_1887_);
lean_dec_ref(v_e_1886_);
v_a_1999_ = lean_ctor_get(v___x_1986_, 0);
v_isSharedCheck_2006_ = !lean_is_exclusive(v___x_1986_);
if (v_isSharedCheck_2006_ == 0)
{
v___x_2001_ = v___x_1986_;
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1986_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2006_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v___x_2004_; 
if (v_isShared_2002_ == 0)
{
v___x_2004_ = v___x_2001_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2005_; 
v_reuseFailAlloc_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2005_, 0, v_a_1999_);
v___x_2004_ = v_reuseFailAlloc_2005_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
return v___x_2004_;
}
}
}
}
v___jp_1896_:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_box(0);
v___x_1899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1899_, 0, v___y_1897_);
lean_ctor_set(v___x_1899_, 1, v___x_1898_);
v___x_1900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
return v___x_1900_;
}
v___jp_1901_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1905_ = lean_expr_instantiate1(v___y_1902_, v___y_1903_);
lean_dec_ref(v___y_1903_);
lean_dec_ref(v___y_1902_);
v___x_1906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
v___x_1907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1907_, 0, v___y_1904_);
lean_ctor_set(v___x_1907_, 1, v___x_1906_);
v___x_1908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1907_);
return v___x_1908_;
}
v___jp_1909_:
{
if (lean_obj_tag(v_e_1886_) == 5)
{
lean_object* v_expr_1911_; lean_object* v_expr_1912_; lean_object* v_fn_1913_; lean_object* v_arg_1914_; size_t v___x_1915_; size_t v___x_1916_; uint8_t v___x_1917_; 
v_expr_1911_ = lean_ctor_get(v_f_1887_, 0);
lean_inc_ref(v_expr_1911_);
lean_dec_ref(v_f_1887_);
v_expr_1912_ = lean_ctor_get(v_a_1888_, 0);
lean_inc_ref(v_expr_1912_);
lean_dec_ref(v_a_1888_);
v_fn_1913_ = lean_ctor_get(v_e_1886_, 0);
v_arg_1914_ = lean_ctor_get(v_e_1886_, 1);
v___x_1915_ = lean_ptr_addr(v_fn_1913_);
v___x_1916_ = lean_ptr_addr(v_expr_1911_);
v___x_1917_ = lean_usize_dec_eq(v___x_1915_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
lean_dec_ref_known(v_e_1886_, 2);
lean_inc_ref(v_expr_1912_);
v___x_1918_ = l_Lean_Expr_app___override(v_expr_1911_, v_expr_1912_);
v___y_1902_ = v___y_1910_;
v___y_1903_ = v_expr_1912_;
v___y_1904_ = v___x_1918_;
goto v___jp_1901_;
}
else
{
size_t v___x_1919_; size_t v___x_1920_; uint8_t v___x_1921_; 
v___x_1919_ = lean_ptr_addr(v_arg_1914_);
v___x_1920_ = lean_ptr_addr(v_expr_1912_);
v___x_1921_ = lean_usize_dec_eq(v___x_1919_, v___x_1920_);
if (v___x_1921_ == 0)
{
lean_object* v___x_1922_; 
lean_dec_ref_known(v_e_1886_, 2);
lean_inc_ref(v_expr_1912_);
v___x_1922_ = l_Lean_Expr_app___override(v_expr_1911_, v_expr_1912_);
v___y_1902_ = v___y_1910_;
v___y_1903_ = v_expr_1912_;
v___y_1904_ = v___x_1922_;
goto v___jp_1901_;
}
else
{
lean_dec_ref(v_expr_1911_);
v___y_1902_ = v___y_1910_;
v___y_1903_ = v_expr_1912_;
v___y_1904_ = v_e_1886_;
goto v___jp_1901_;
}
}
}
else
{
lean_object* v_expr_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
lean_dec_ref(v_f_1887_);
lean_dec_ref(v_e_1886_);
v_expr_1923_ = lean_ctor_get(v_a_1888_, 0);
lean_inc_ref(v_expr_1923_);
lean_dec_ref(v_a_1888_);
v___x_1924_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__3);
v___x_1925_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_1924_);
v___y_1902_ = v___y_1910_;
v___y_1903_ = v_expr_1923_;
v___y_1904_ = v___x_1925_;
goto v___jp_1901_;
}
}
v___jp_1926_:
{
if (lean_obj_tag(v_fType_1927_) == 7)
{
lean_object* v_binderType_1933_; lean_object* v_body_1934_; lean_object* v___x_1935_; 
v_binderType_1933_ = lean_ctor_get(v_fType_1927_, 1);
lean_inc_ref(v_binderType_1933_);
v_body_1934_ = lean_ctor_get(v_fType_1927_, 2);
lean_inc_ref(v_body_1934_);
lean_dec_ref_known(v_fType_1927_, 3);
lean_inc_ref(v_a_1888_);
v___x_1935_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_1888_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = l_Lean_Meta_isExprDefEq(v_binderType_1933_, v_a_1936_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; uint8_t v___x_1939_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = lean_unbox(v_a_1938_);
lean_dec(v_a_1938_);
if (v___x_1939_ == 0)
{
lean_object* v_expr_1940_; lean_object* v_expr_1941_; lean_object* v___x_1942_; 
v_expr_1940_ = lean_ctor_get(v_f_1887_, 0);
v_expr_1941_ = lean_ctor_get(v_a_1888_, 0);
lean_inc_ref(v_expr_1941_);
lean_inc_ref(v_expr_1940_);
v___x_1942_ = l_Lean_Meta_throwAppTypeMismatch___redArg(v_expr_1940_, v_expr_1941_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
if (lean_obj_tag(v___x_1942_) == 0)
{
lean_dec_ref_known(v___x_1942_, 1);
v___y_1910_ = v_body_1934_;
goto v___jp_1909_;
}
else
{
lean_object* v_a_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1950_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_a_1888_);
lean_dec_ref(v_f_1887_);
lean_dec_ref(v_e_1886_);
v_a_1943_ = lean_ctor_get(v___x_1942_, 0);
v_isSharedCheck_1950_ = !lean_is_exclusive(v___x_1942_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1945_ = v___x_1942_;
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_a_1943_);
lean_dec(v___x_1942_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1950_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1948_; 
if (v_isShared_1946_ == 0)
{
v___x_1948_ = v___x_1945_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1949_; 
v_reuseFailAlloc_1949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1949_, 0, v_a_1943_);
v___x_1948_ = v_reuseFailAlloc_1949_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
return v___x_1948_;
}
}
}
}
else
{
v___y_1910_ = v_body_1934_;
goto v___jp_1909_;
}
}
else
{
lean_object* v_a_1951_; lean_object* v___x_1953_; uint8_t v_isShared_1954_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_a_1888_);
lean_dec_ref(v_f_1887_);
lean_dec_ref(v_e_1886_);
v_a_1951_ = lean_ctor_get(v___x_1937_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1937_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1953_ = v___x_1937_;
v_isShared_1954_ = v_isSharedCheck_1958_;
goto v_resetjp_1952_;
}
else
{
lean_inc(v_a_1951_);
lean_dec(v___x_1937_);
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
lean_object* v_a_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1966_; 
lean_dec_ref(v_body_1934_);
lean_dec_ref(v_binderType_1933_);
lean_dec_ref(v_a_1888_);
lean_dec_ref(v_f_1887_);
lean_dec_ref(v_e_1886_);
v_a_1959_ = lean_ctor_get(v___x_1935_, 0);
v_isSharedCheck_1966_ = !lean_is_exclusive(v___x_1935_);
if (v_isSharedCheck_1966_ == 0)
{
v___x_1961_ = v___x_1935_;
v_isShared_1962_ = v_isSharedCheck_1966_;
goto v_resetjp_1960_;
}
else
{
lean_inc(v_a_1959_);
lean_dec(v___x_1935_);
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
lean_object* v_expr_1967_; lean_object* v_expr_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec_ref(v_fType_1927_);
lean_dec_ref(v_e_1886_);
v_expr_1967_ = lean_ctor_get(v_f_1887_, 0);
lean_inc_ref(v_expr_1967_);
lean_dec_ref(v_f_1887_);
v_expr_1968_ = lean_ctor_get(v_a_1888_, 0);
lean_inc_ref(v_expr_1968_);
lean_dec_ref(v_a_1888_);
v___x_1969_ = l_Lean_Expr_app___override(v_expr_1967_, v_expr_1968_);
v___x_1970_ = l_Lean_Meta_throwFunctionExpected___redArg(v___x_1969_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_);
return v___x_1970_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___boxed(lean_object* v_e_2007_, lean_object* v_f_2008_, lean_object* v_a_2009_, lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v_res_2017_; 
v_res_2017_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_2007_, v_f_2008_, v_a_2009_, v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_, v_a_2015_);
lean_dec(v_a_2015_);
lean_dec_ref(v_a_2014_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec(v_a_2010_);
return v_res_2017_;
}
}
static lean_object* _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2019_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__2));
v___x_2020_ = lean_unsigned_to_nat(37u);
v___x_2021_ = lean_unsigned_to_nat(345u);
v___x_2022_ = ((lean_object*)(l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__0));
v___x_2023_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst___lam__0___closed__0));
v___x_2024_ = l_mkPanicMessageWithDecl(v___x_2023_, v___x_2022_, v___x_2021_, v___x_2020_, v___x_2019_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(lean_object* v_fvars_2025_, lean_object* v_i_2026_, lean_object* v_a_2027_, lean_object* v___y_2028_, lean_object* v___y_2029_, lean_object* v___y_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_, lean_object* v___y_2033_){
_start:
{
lean_object* v_zero_2035_; uint8_t v_isZero_2036_; 
v_zero_2035_ = lean_unsigned_to_nat(0u);
v_isZero_2036_ = lean_nat_dec_eq(v_i_2026_, v_zero_2035_);
if (v_isZero_2036_ == 1)
{
lean_object* v___x_2037_; 
lean_dec(v_i_2026_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v_a_2027_);
return v___x_2037_;
}
else
{
lean_object* v_one_2038_; lean_object* v_n_2039_; lean_object* v___y_2041_; lean_object* v___y_2045_; lean_object* v___y_2046_; lean_object* v___y_2050_; lean_object* v___y_2051_; lean_object* v___x_2053_; 
v_one_2038_ = lean_unsigned_to_nat(1u);
v_n_2039_ = lean_nat_sub(v_i_2026_, v_one_2038_);
lean_dec(v_i_2026_);
v___x_2053_ = lean_array_fget_borrowed(v_fvars_2025_, v_n_2039_);
if (lean_obj_tag(v___x_2053_) == 1)
{
lean_object* v_fvarId_2054_; lean_object* v___x_2055_; 
v_fvarId_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_fvarId_2054_);
v___x_2055_ = l_Lean_FVarId_findDecl_x3f___redArg(v_fvarId_2054_, v___y_2030_);
if (lean_obj_tag(v___x_2055_) == 0)
{
lean_object* v_a_2056_; 
v_a_2056_ = lean_ctor_get(v___x_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref_known(v___x_2055_, 1);
if (lean_obj_tag(v_a_2056_) == 1)
{
lean_object* v_val_2057_; 
v_val_2057_ = lean_ctor_get(v_a_2056_, 0);
lean_inc(v_val_2057_);
lean_dec_ref_known(v_a_2056_, 1);
if (lean_obj_tag(v_val_2057_) == 0)
{
lean_object* v_userName_2058_; lean_object* v_type_2059_; uint8_t v_bi_2060_; lean_object* v_expr_2061_; lean_object* v_type_x3f_2062_; lean_object* v___x_2064_; uint8_t v_isShared_2065_; uint8_t v_isSharedCheck_2083_; 
v_userName_2058_ = lean_ctor_get(v_val_2057_, 2);
lean_inc(v_userName_2058_);
v_type_2059_ = lean_ctor_get(v_val_2057_, 3);
lean_inc_ref(v_type_2059_);
v_bi_2060_ = lean_ctor_get_uint8(v_val_2057_, sizeof(void*)*4);
lean_dec_ref_known(v_val_2057_, 4);
v_expr_2061_ = lean_ctor_get(v_a_2027_, 0);
v_type_x3f_2062_ = lean_ctor_get(v_a_2027_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2027_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2064_ = v_a_2027_;
v_isShared_2065_ = v_isSharedCheck_2083_;
goto v_resetjp_2063_;
}
else
{
lean_inc(v_type_x3f_2062_);
lean_inc(v_expr_2061_);
lean_dec(v_a_2027_);
v___x_2064_ = lean_box(0);
v_isShared_2065_ = v_isSharedCheck_2083_;
goto v_resetjp_2063_;
}
v_resetjp_2063_:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___y_2069_; 
v___x_2066_ = lean_expr_abstract_range(v_type_2059_, v_n_2039_, v_fvars_2025_);
lean_dec_ref(v_type_2059_);
lean_inc_ref(v___x_2066_);
lean_inc(v_userName_2058_);
v___x_2067_ = l_Lean_Expr_lam___override(v_userName_2058_, v___x_2066_, v_expr_2061_, v_bi_2060_);
if (lean_obj_tag(v_type_x3f_2062_) == 0)
{
lean_dec_ref(v___x_2066_);
lean_dec(v_userName_2058_);
v___y_2069_ = v_type_x3f_2062_;
goto v___jp_2068_;
}
else
{
lean_object* v_val_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2082_; 
v_val_2074_ = lean_ctor_get(v_type_x3f_2062_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_type_x3f_2062_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2076_ = v_type_x3f_2062_;
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_val_2074_);
lean_dec(v_type_x3f_2062_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2082_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2078_; lean_object* v___x_2080_; 
v___x_2078_ = l_Lean_Expr_forallE___override(v_userName_2058_, v___x_2066_, v_val_2074_, v_bi_2060_);
if (v_isShared_2077_ == 0)
{
lean_ctor_set(v___x_2076_, 0, v___x_2078_);
v___x_2080_ = v___x_2076_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v___x_2078_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
v___y_2069_ = v___x_2080_;
goto v___jp_2068_;
}
}
}
v___jp_2068_:
{
lean_object* v___x_2071_; 
if (v_isShared_2065_ == 0)
{
lean_ctor_set(v___x_2064_, 1, v___y_2069_);
lean_ctor_set(v___x_2064_, 0, v___x_2067_);
v___x_2071_ = v___x_2064_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2073_, 1, v___y_2069_);
v___x_2071_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
v_i_2026_ = v_n_2039_;
v_a_2027_ = v___x_2071_;
goto _start;
}
}
}
}
else
{
lean_object* v_userName_2084_; lean_object* v_type_2085_; lean_object* v_value_2086_; uint8_t v_nondep_2087_; uint8_t v_nondep_2089_; lean_object* v___x_2099_; 
v_userName_2084_ = lean_ctor_get(v_val_2057_, 2);
lean_inc(v_userName_2084_);
v_type_2085_ = lean_ctor_get(v_val_2057_, 3);
lean_inc_ref(v_type_2085_);
v_value_2086_ = lean_ctor_get(v_val_2057_, 4);
lean_inc_ref(v_value_2086_);
v_nondep_2087_ = lean_ctor_get_uint8(v_val_2057_, sizeof(void*)*5);
lean_dec_ref_known(v_val_2057_, 5);
v___x_2099_ = l_Lean_Meta_getZetaDeltaFVarIds___redArg(v___y_2031_);
if (lean_obj_tag(v___x_2099_) == 0)
{
lean_object* v_a_2100_; uint8_t v___x_2101_; 
v_a_2100_ = lean_ctor_get(v___x_2099_, 0);
lean_inc(v_a_2100_);
lean_dec_ref_known(v___x_2099_, 1);
v___x_2101_ = 1;
if (v_nondep_2087_ == 0)
{
uint8_t v___x_2102_; 
v___x_2102_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__0___redArg(v_fvarId_2054_, v_a_2100_);
lean_dec(v_a_2100_);
if (v___x_2102_ == 0)
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_incCount___redArg(v___y_2029_);
lean_dec_ref(v___x_2103_);
v_nondep_2089_ = v___x_2101_;
goto v___jp_2088_;
}
else
{
v_nondep_2089_ = v_nondep_2087_;
goto v___jp_2088_;
}
}
else
{
lean_dec(v_a_2100_);
v_nondep_2089_ = v___x_2101_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_a_2104_; lean_object* v___x_2106_; uint8_t v_isShared_2107_; uint8_t v_isSharedCheck_2111_; 
lean_dec_ref(v_value_2086_);
lean_dec_ref(v_type_2085_);
lean_dec(v_userName_2084_);
lean_dec(v_n_2039_);
lean_dec_ref(v_a_2027_);
v_a_2104_ = lean_ctor_get(v___x_2099_, 0);
v_isSharedCheck_2111_ = !lean_is_exclusive(v___x_2099_);
if (v_isSharedCheck_2111_ == 0)
{
v___x_2106_ = v___x_2099_;
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
else
{
lean_inc(v_a_2104_);
lean_dec(v___x_2099_);
v___x_2106_ = lean_box(0);
v_isShared_2107_ = v_isSharedCheck_2111_;
goto v_resetjp_2105_;
}
v_resetjp_2105_:
{
lean_object* v___x_2109_; 
if (v_isShared_2107_ == 0)
{
v___x_2109_ = v___x_2106_;
goto v_reusejp_2108_;
}
else
{
lean_object* v_reuseFailAlloc_2110_; 
v_reuseFailAlloc_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2110_, 0, v_a_2104_);
v___x_2109_ = v_reuseFailAlloc_2110_;
goto v_reusejp_2108_;
}
v_reusejp_2108_:
{
return v___x_2109_;
}
}
}
v___jp_2088_:
{
lean_object* v_expr_2090_; lean_object* v_type_x3f_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; 
v_expr_2090_ = lean_ctor_get(v_a_2027_, 0);
lean_inc_ref(v_expr_2090_);
v_type_x3f_2091_ = lean_ctor_get(v_a_2027_, 1);
lean_inc(v_type_x3f_2091_);
lean_dec_ref(v_a_2027_);
v___x_2092_ = lean_expr_abstract_range(v_type_2085_, v_n_2039_, v_fvars_2025_);
lean_dec_ref(v_type_2085_);
v___x_2093_ = lean_expr_abstract_range(v_value_2086_, v_n_2039_, v_fvars_2025_);
lean_dec_ref(v_value_2086_);
lean_inc_ref(v___x_2093_);
lean_inc_ref(v___x_2092_);
lean_inc(v_userName_2084_);
v___x_2094_ = l_Lean_Expr_letE___override(v_userName_2084_, v___x_2092_, v___x_2093_, v_expr_2090_, v_nondep_2089_);
if (lean_obj_tag(v_type_x3f_2091_) == 0)
{
lean_dec_ref(v___x_2093_);
lean_dec_ref(v___x_2092_);
lean_dec(v_userName_2084_);
v___y_2045_ = v___x_2094_;
v___y_2046_ = v_type_x3f_2091_;
goto v___jp_2044_;
}
else
{
lean_object* v_val_2095_; uint8_t v___x_2096_; 
v_val_2095_ = lean_ctor_get(v_type_x3f_2091_, 0);
lean_inc(v_val_2095_);
lean_dec_ref_known(v_type_x3f_2091_, 1);
v___x_2096_ = lean_expr_has_loose_bvar(v_val_2095_, v_zero_2035_);
if (v___x_2096_ == 0)
{
lean_object* v___x_2097_; 
lean_dec_ref(v___x_2093_);
lean_dec_ref(v___x_2092_);
lean_dec(v_userName_2084_);
v___x_2097_ = lean_expr_lower_loose_bvars(v_val_2095_, v_one_2038_, v_one_2038_);
lean_dec(v_val_2095_);
v___y_2050_ = v___x_2094_;
v___y_2051_ = v___x_2097_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_Expr_letE___override(v_userName_2084_, v___x_2092_, v___x_2093_, v_val_2095_, v_nondep_2089_);
v___y_2050_ = v___x_2094_;
v___y_2051_ = v___x_2098_;
goto v___jp_2049_;
}
}
}
}
}
else
{
lean_object* v___x_2112_; 
lean_dec(v_a_2056_);
lean_dec_ref(v_a_2027_);
lean_inc(v_fvarId_2054_);
v___x_2112_ = l_Lean_FVarId_throwUnknown___redArg(v_fvarId_2054_, v___y_2032_, v___y_2033_);
v___y_2041_ = v___x_2112_;
goto v___jp_2040_;
}
}
else
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2120_; 
lean_dec(v_n_2039_);
lean_dec_ref(v_a_2027_);
v_a_2113_ = lean_ctor_get(v___x_2055_, 0);
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2120_ == 0)
{
v___x_2115_ = v___x_2055_;
v_isShared_2116_ = v_isSharedCheck_2120_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2055_);
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
}
else
{
lean_object* v___x_2121_; lean_object* v___x_2122_; 
lean_dec_ref(v_a_2027_);
v___x_2121_ = lean_obj_once(&l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1, &l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1_once, _init_l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___closed__1);
v___x_2122_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__1(v___x_2121_, v___y_2028_, v___y_2029_, v___y_2030_, v___y_2031_, v___y_2032_, v___y_2033_);
v___y_2041_ = v___x_2122_;
goto v___jp_2040_;
}
v___jp_2040_:
{
if (lean_obj_tag(v___y_2041_) == 0)
{
lean_object* v_a_2042_; 
v_a_2042_ = lean_ctor_get(v___y_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___y_2041_, 1);
v_i_2026_ = v_n_2039_;
v_a_2027_ = v_a_2042_;
goto _start;
}
else
{
lean_dec(v_n_2039_);
return v___y_2041_;
}
}
v___jp_2044_:
{
lean_object* v___x_2047_; 
v___x_2047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2047_, 0, v___y_2045_);
lean_ctor_set(v___x_2047_, 1, v___y_2046_);
v_i_2026_ = v_n_2039_;
v_a_2027_ = v___x_2047_;
goto _start;
}
v___jp_2049_:
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2052_, 0, v___y_2051_);
v___y_2045_ = v___y_2050_;
v___y_2046_ = v___x_2052_;
goto v___jp_2044_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg___boxed(lean_object* v_fvars_2123_, lean_object* v_i_2124_, lean_object* v_a_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2123_, v_i_2124_, v_a_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
lean_dec(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v_fvars_2123_);
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
if (lean_obj_tag(v_a_2134_) == 0)
{
lean_object* v___x_2136_; 
v___x_2136_ = l_List_reverse___redArg(v_a_2135_);
return v___x_2136_;
}
else
{
lean_object* v_head_2137_; lean_object* v_tail_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2147_; 
v_head_2137_ = lean_ctor_get(v_a_2134_, 0);
v_tail_2138_ = lean_ctor_get(v_a_2134_, 1);
v_isSharedCheck_2147_ = !lean_is_exclusive(v_a_2134_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2140_ = v_a_2134_;
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_tail_2138_);
lean_inc(v_head_2137_);
lean_dec(v_a_2134_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2147_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
v___x_2142_ = l_Lean_MessageData_ofExpr(v_head_2137_);
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 1, v_a_2135_);
lean_ctor_set(v___x_2140_, 0, v___x_2142_);
v___x_2144_ = v___x_2140_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2142_);
lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_a_2135_);
v___x_2144_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
v_a_2134_ = v_tail_2138_;
v_a_2135_ = v___x_2144_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_2148_; double v___x_2149_; 
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_float_of_nat(v___x_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(lean_object* v_cls_2153_, lean_object* v_msg_2154_, lean_object* v___y_2155_, lean_object* v___y_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_){
_start:
{
lean_object* v_ref_2160_; lean_object* v___x_2161_; lean_object* v_a_2162_; lean_object* v___x_2164_; uint8_t v_isShared_2165_; uint8_t v_isSharedCheck_2206_; 
v_ref_2160_ = lean_ctor_get(v___y_2157_, 4);
v___x_2161_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_2154_, v___y_2155_, v___y_2156_, v___y_2157_, v___y_2158_);
v_a_2162_ = lean_ctor_get(v___x_2161_, 0);
v_isSharedCheck_2206_ = !lean_is_exclusive(v___x_2161_);
if (v_isSharedCheck_2206_ == 0)
{
v___x_2164_ = v___x_2161_;
v_isShared_2165_ = v_isSharedCheck_2206_;
goto v_resetjp_2163_;
}
else
{
lean_inc(v_a_2162_);
lean_dec(v___x_2161_);
v___x_2164_ = lean_box(0);
v_isShared_2165_ = v_isSharedCheck_2206_;
goto v_resetjp_2163_;
}
v_resetjp_2163_:
{
lean_object* v___x_2166_; lean_object* v_traceState_2167_; lean_object* v_env_2168_; lean_object* v_nextMacroScope_2169_; lean_object* v_ngen_2170_; lean_object* v_auxDeclNGen_2171_; lean_object* v_cache_2172_; lean_object* v_messages_2173_; lean_object* v_infoState_2174_; lean_object* v_snapshotTasks_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2205_; 
v___x_2166_ = lean_st_ref_take(v___y_2158_);
v_traceState_2167_ = lean_ctor_get(v___x_2166_, 4);
v_env_2168_ = lean_ctor_get(v___x_2166_, 0);
v_nextMacroScope_2169_ = lean_ctor_get(v___x_2166_, 1);
v_ngen_2170_ = lean_ctor_get(v___x_2166_, 2);
v_auxDeclNGen_2171_ = lean_ctor_get(v___x_2166_, 3);
v_cache_2172_ = lean_ctor_get(v___x_2166_, 5);
v_messages_2173_ = lean_ctor_get(v___x_2166_, 6);
v_infoState_2174_ = lean_ctor_get(v___x_2166_, 7);
v_snapshotTasks_2175_ = lean_ctor_get(v___x_2166_, 8);
v_isSharedCheck_2205_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2205_ == 0)
{
v___x_2177_ = v___x_2166_;
v_isShared_2178_ = v_isSharedCheck_2205_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snapshotTasks_2175_);
lean_inc(v_infoState_2174_);
lean_inc(v_messages_2173_);
lean_inc(v_cache_2172_);
lean_inc(v_traceState_2167_);
lean_inc(v_auxDeclNGen_2171_);
lean_inc(v_ngen_2170_);
lean_inc(v_nextMacroScope_2169_);
lean_inc(v_env_2168_);
lean_dec(v___x_2166_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2205_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
uint64_t v_tid_2179_; lean_object* v_traces_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2204_; 
v_tid_2179_ = lean_ctor_get_uint64(v_traceState_2167_, sizeof(void*)*1);
v_traces_2180_ = lean_ctor_get(v_traceState_2167_, 0);
v_isSharedCheck_2204_ = !lean_is_exclusive(v_traceState_2167_);
if (v_isSharedCheck_2204_ == 0)
{
v___x_2182_ = v_traceState_2167_;
v_isShared_2183_ = v_isSharedCheck_2204_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_traces_2180_);
lean_dec(v_traceState_2167_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2204_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2184_; double v___x_2185_; uint8_t v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2194_; 
v___x_2184_ = lean_box(0);
v___x_2185_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_2186_ = 0;
v___x_2187_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_2188_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2188_, 0, v_cls_2153_);
lean_ctor_set(v___x_2188_, 1, v___x_2184_);
lean_ctor_set(v___x_2188_, 2, v___x_2187_);
lean_ctor_set_float(v___x_2188_, sizeof(void*)*3, v___x_2185_);
lean_ctor_set_float(v___x_2188_, sizeof(void*)*3 + 8, v___x_2185_);
lean_ctor_set_uint8(v___x_2188_, sizeof(void*)*3 + 16, v___x_2186_);
v___x_2189_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_2190_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2188_);
lean_ctor_set(v___x_2190_, 1, v_a_2162_);
lean_ctor_set(v___x_2190_, 2, v___x_2189_);
lean_inc(v_ref_2160_);
v___x_2191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2191_, 0, v_ref_2160_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
v___x_2192_ = l_Lean_PersistentArray_push___redArg(v_traces_2180_, v___x_2191_);
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 0, v___x_2192_);
v___x_2194_ = v___x_2182_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2192_);
lean_ctor_set_uint64(v_reuseFailAlloc_2203_, sizeof(void*)*1, v_tid_2179_);
v___x_2194_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2196_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 4, v___x_2194_);
v___x_2196_ = v___x_2177_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_env_2168_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_nextMacroScope_2169_);
lean_ctor_set(v_reuseFailAlloc_2202_, 2, v_ngen_2170_);
lean_ctor_set(v_reuseFailAlloc_2202_, 3, v_auxDeclNGen_2171_);
lean_ctor_set(v_reuseFailAlloc_2202_, 4, v___x_2194_);
lean_ctor_set(v_reuseFailAlloc_2202_, 5, v_cache_2172_);
lean_ctor_set(v_reuseFailAlloc_2202_, 6, v_messages_2173_);
lean_ctor_set(v_reuseFailAlloc_2202_, 7, v_infoState_2174_);
lean_ctor_set(v_reuseFailAlloc_2202_, 8, v_snapshotTasks_2175_);
v___x_2196_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2197_ = lean_st_ref_put(v___y_2158_, v___x_2196_);
v___x_2198_ = lean_box(0);
if (v_isShared_2165_ == 0)
{
lean_ctor_set(v___x_2164_, 0, v___x_2198_);
v___x_2200_ = v___x_2164_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2201_; 
v_reuseFailAlloc_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2201_, 0, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2201_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
return v___x_2200_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___boxed(lean_object* v_cls_2207_, lean_object* v_msg_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2207_, v_msg_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec(v___y_2210_);
lean_dec_ref(v___y_2209_);
return v_res_2214_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6(void){
_start:
{
lean_object* v_cls_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v_cls_2225_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2226_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_2227_ = l_Lean_Name_append(v___x_2226_, v_cls_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8(void){
_start:
{
lean_object* v___x_2229_; lean_object* v___x_2230_; 
v___x_2229_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__7));
v___x_2230_ = l_Lean_stringToMessageData(v___x_2229_);
return v___x_2230_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__9));
v___x_2233_ = l_Lean_stringToMessageData(v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12(void){
_start:
{
lean_object* v___x_2235_; lean_object* v___x_2236_; 
v___x_2235_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__11));
v___x_2236_ = l_Lean_stringToMessageData(v___x_2235_);
return v___x_2236_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2240_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__14));
v___x_2241_ = l_Lean_MessageData_ofFormat(v___x_2240_);
return v___x_2241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(lean_object* v_fvars_2242_, lean_object* v_body_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_, lean_object* v_a_2249_){
_start:
{
lean_object* v___y_2252_; lean_object* v___y_2253_; lean_object* v___y_2254_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2264_; lean_object* v___y_2265_; lean_object* v___y_2266_; lean_object* v___y_2267_; lean_object* v___y_2268_; lean_object* v___y_2269_; lean_object* v_options_2282_; uint8_t v_hasTrace_2283_; 
v_options_2282_ = lean_ctor_get(v_a_2248_, 1);
v_hasTrace_2283_ = lean_ctor_get_uint8(v_options_2282_, sizeof(void*)*1);
if (v_hasTrace_2283_ == 0)
{
v___y_2264_ = v_a_2244_;
v___y_2265_ = v_a_2245_;
v___y_2266_ = v_a_2246_;
v___y_2267_ = v_a_2247_;
v___y_2268_ = v_a_2248_;
v___y_2269_ = v_a_2249_;
goto v___jp_2263_;
}
else
{
lean_object* v_toCold_2284_; lean_object* v_inheritedTraceOptions_2285_; lean_object* v_cls_2286_; lean_object* v___x_2287_; uint8_t v___x_2288_; 
v_toCold_2284_ = lean_ctor_get(v_a_2248_, 0);
v_inheritedTraceOptions_2285_ = lean_ctor_get(v_toCold_2284_, 4);
v_cls_2286_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_2287_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_2288_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2285_, v_options_2282_, v___x_2287_);
if (v___x_2288_ == 0)
{
v___y_2264_ = v_a_2244_;
v___y_2265_ = v_a_2245_;
v___y_2266_ = v_a_2246_;
v___y_2267_ = v_a_2247_;
v___y_2268_ = v_a_2248_;
v___y_2269_ = v_a_2249_;
goto v___jp_2263_;
}
else
{
lean_object* v_expr_2289_; lean_object* v_type_x3f_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___y_2303_; 
v_expr_2289_ = lean_ctor_get(v_body_2243_, 0);
v_type_x3f_2290_ = lean_ctor_get(v_body_2243_, 1);
v___x_2291_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__8);
lean_inc_ref(v_fvars_2242_);
v___x_2292_ = lean_array_to_list(v_fvars_2242_);
v___x_2293_ = lean_box(0);
v___x_2294_ = l_List_mapTR_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__1(v___x_2292_, v___x_2293_);
v___x_2295_ = l_Lean_MessageData_ofList(v___x_2294_);
v___x_2296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2291_);
lean_ctor_set(v___x_2296_, 1, v___x_2295_);
v___x_2297_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__10);
v___x_2298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2296_);
lean_ctor_set(v___x_2298_, 1, v___x_2297_);
lean_inc_ref(v_expr_2289_);
v___x_2299_ = l_Lean_MessageData_ofExpr(v_expr_2289_);
v___x_2300_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__12);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2299_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
if (lean_obj_tag(v_type_x3f_2290_) == 0)
{
lean_object* v___x_2316_; 
v___x_2316_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__15);
v___y_2303_ = v___x_2316_;
goto v___jp_2302_;
}
else
{
lean_object* v_val_2317_; lean_object* v___x_2318_; 
v_val_2317_ = lean_ctor_get(v_type_x3f_2290_, 0);
lean_inc(v_val_2317_);
v___x_2318_ = l_Lean_MessageData_ofExpr(v_val_2317_);
v___y_2303_ = v___x_2318_;
goto v___jp_2302_;
}
v___jp_2302_:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; 
v___x_2304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2301_);
lean_ctor_set(v___x_2304_, 1, v___y_2303_);
v___x_2305_ = l_Lean_indentD(v___x_2304_);
v___x_2306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2306_, 0, v___x_2298_);
lean_ctor_set(v___x_2306_, 1, v___x_2305_);
v___x_2307_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2286_, v___x_2306_, v_a_2246_, v_a_2247_, v_a_2248_, v_a_2249_);
if (lean_obj_tag(v___x_2307_) == 0)
{
lean_dec_ref_known(v___x_2307_, 1);
v___y_2264_ = v_a_2244_;
v___y_2265_ = v_a_2245_;
v___y_2266_ = v_a_2246_;
v___y_2267_ = v_a_2247_;
v___y_2268_ = v_a_2248_;
v___y_2269_ = v_a_2249_;
goto v___jp_2263_;
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_dec_ref(v_body_2243_);
lean_dec_ref(v_fvars_2242_);
v_a_2308_ = lean_ctor_get(v___x_2307_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2307_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2307_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2307_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
v___jp_2251_:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___y_2256_);
lean_ctor_set(v___x_2260_, 1, v___y_2259_);
v___x_2261_ = lean_array_get_size(v_fvars_2242_);
v___x_2262_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2242_, v___x_2261_, v___x_2260_, v___y_2254_, v___y_2253_, v___y_2258_, v___y_2252_, v___y_2255_, v___y_2257_);
lean_dec_ref(v_fvars_2242_);
return v___x_2262_;
}
v___jp_2263_:
{
lean_object* v_expr_2270_; lean_object* v_type_x3f_2271_; lean_object* v___x_2272_; 
v_expr_2270_ = lean_ctor_get(v_body_2243_, 0);
lean_inc_ref(v_expr_2270_);
v_type_x3f_2271_ = lean_ctor_get(v_body_2243_, 1);
lean_inc(v_type_x3f_2271_);
lean_dec_ref(v_body_2243_);
v___x_2272_ = lean_expr_abstract(v_expr_2270_, v_fvars_2242_);
lean_dec_ref(v_expr_2270_);
if (lean_obj_tag(v_type_x3f_2271_) == 0)
{
v___y_2252_ = v___y_2267_;
v___y_2253_ = v___y_2265_;
v___y_2254_ = v___y_2264_;
v___y_2255_ = v___y_2268_;
v___y_2256_ = v___x_2272_;
v___y_2257_ = v___y_2269_;
v___y_2258_ = v___y_2266_;
v___y_2259_ = v_type_x3f_2271_;
goto v___jp_2251_;
}
else
{
lean_object* v_val_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2281_; 
v_val_2273_ = lean_ctor_get(v_type_x3f_2271_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v_type_x3f_2271_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2275_ = v_type_x3f_2271_;
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_val_2273_);
lean_dec(v_type_x3f_2271_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2281_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2277_; lean_object* v___x_2279_; 
v___x_2277_ = lean_expr_abstract(v_val_2273_, v_fvars_2242_);
lean_dec(v_val_2273_);
if (v_isShared_2276_ == 0)
{
lean_ctor_set(v___x_2275_, 0, v___x_2277_);
v___x_2279_ = v___x_2275_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v___x_2277_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
v___y_2252_ = v___y_2267_;
v___y_2253_ = v___y_2265_;
v___y_2254_ = v___y_2264_;
v___y_2255_ = v___y_2268_;
v___y_2256_ = v___x_2272_;
v___y_2257_ = v___y_2269_;
v___y_2258_ = v___y_2266_;
v___y_2259_ = v___x_2279_;
goto v___jp_2251_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___boxed(lean_object* v_fvars_2319_, lean_object* v_body_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_, lean_object* v_a_2326_, lean_object* v_a_2327_){
_start:
{
lean_object* v_res_2328_; 
v_res_2328_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_2319_, v_body_2320_, v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_, v_a_2325_, v_a_2326_);
lean_dec(v_a_2326_);
lean_dec_ref(v_a_2325_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec(v_a_2321_);
return v_res_2328_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(lean_object* v_fvars_2329_, lean_object* v_n_2330_, lean_object* v_i_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v___y_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; 
v___x_2341_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___redArg(v_fvars_2329_, v_i_2331_, v_a_2333_, v___y_2334_, v___y_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
return v___x_2341_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0___boxed(lean_object* v_fvars_2342_, lean_object* v_n_2343_, lean_object* v_i_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l___private_Init_Data_Nat_Control_0__Nat_foldRevM_loop___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__0(v_fvars_2342_, v_n_2343_, v_i_2344_, v_a_2345_, v_a_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
lean_dec(v___y_2352_);
lean_dec_ref(v___y_2351_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec(v___y_2347_);
lean_dec(v_n_2343_);
lean_dec_ref(v_fvars_2342_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(lean_object* v_cls_2355_, lean_object* v_msg_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_){
_start:
{
lean_object* v___x_2364_; 
v___x_2364_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg(v_cls_2355_, v_msg_2356_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
return v___x_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___boxed(lean_object* v_cls_2365_, lean_object* v_msg_2366_, lean_object* v___y_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_, lean_object* v___y_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2(v_cls_2365_, v_msg_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
lean_dec(v___y_2370_);
lean_dec_ref(v___y_2369_);
lean_dec(v___y_2368_);
lean_dec(v___y_2367_);
return v_res_2374_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; 
v___x_2376_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__0));
v___x_2377_ = l_Lean_stringToMessageData(v___x_2376_);
return v___x_2377_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__2));
v___x_2380_ = l_Lean_stringToMessageData(v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(lean_object* v_struct_2381_, lean_object* v_structName_2382_, lean_object* v_idx_2383_, lean_object* v_a_2384_, lean_object* v_00_u03b1_2385_, lean_object* v_x_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v_expr_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2409_; 
v_expr_2394_ = lean_ctor_get(v_struct_2381_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v_struct_2381_);
if (v_isSharedCheck_2409_ == 0)
{
lean_object* v_unused_2410_; 
v_unused_2410_ = lean_ctor_get(v_struct_2381_, 1);
lean_dec(v_unused_2410_);
v___x_2396_ = v_struct_2381_;
v_isShared_2397_ = v_isSharedCheck_2409_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_expr_2394_);
lean_dec(v_struct_2381_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2409_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2402_; 
v___x_2398_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2399_ = l_Lean_mkProj(v_structName_2382_, v_idx_2383_, v_expr_2394_);
v___x_2400_ = l_Lean_indentExpr(v___x_2399_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set_tag(v___x_2396_, 7);
lean_ctor_set(v___x_2396_, 1, v___x_2400_);
lean_ctor_set(v___x_2396_, 0, v___x_2398_);
v___x_2402_ = v___x_2396_;
goto v_reusejp_2401_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v___x_2398_);
lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2400_);
v___x_2402_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2401_;
}
v_reusejp_2401_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2403_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2402_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = l_Lean_indentExpr(v_a_2384_);
v___x_2406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
v___x_2407_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2406_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
return v___x_2407_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___boxed(lean_object* v_struct_2411_, lean_object* v_structName_2412_, lean_object* v_idx_2413_, lean_object* v_a_2414_, lean_object* v_00_u03b1_2415_, lean_object* v_x_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
lean_object* v_res_2424_; 
v_res_2424_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2411_, v_structName_2412_, v_idx_2413_, v_a_2414_, v_00_u03b1_2415_, v_x_2416_, v___y_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
lean_dec(v___y_2420_);
lean_dec_ref(v___y_2419_);
lean_dec(v___y_2418_);
lean_dec(v___y_2417_);
return v_res_2424_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(lean_object* v_constName_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v___x_2433_; lean_object* v_env_2434_; uint8_t v___x_2435_; lean_object* v___x_2436_; 
v___x_2433_ = lean_st_ref_get(v___y_2431_);
v_env_2434_ = lean_ctor_get(v___x_2433_, 0);
lean_inc_ref(v_env_2434_);
lean_dec(v___x_2433_);
v___x_2435_ = 0;
lean_inc(v_constName_2425_);
v___x_2436_ = l_Lean_Environment_find_x3f(v_env_2434_, v_constName_2425_, v___x_2435_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
v___x_2437_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0___redArg(v_constName_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
return v___x_2437_;
}
else
{
lean_object* v_val_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v_constName_2425_);
v_val_2438_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2436_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_val_2438_);
lean_dec(v___x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set_tag(v___x_2440_, 0);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_val_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0___boxed(lean_object* v_constName_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
lean_object* v_res_2454_; 
v_res_2454_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_constName_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_, v___y_2451_, v___y_2452_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec(v___y_2447_);
return v_res_2454_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(lean_object* v_struct_2455_, lean_object* v_structName_2456_, lean_object* v_idx_2457_, lean_object* v_a_2458_, lean_object* v_00_u03b1_2459_, lean_object* v_x_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
lean_object* v_expr_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2483_; 
v_expr_2468_ = lean_ctor_get(v_struct_2455_, 0);
v_isSharedCheck_2483_ = !lean_is_exclusive(v_struct_2455_);
if (v_isSharedCheck_2483_ == 0)
{
lean_object* v_unused_2484_; 
v_unused_2484_ = lean_ctor_get(v_struct_2455_, 1);
lean_dec(v_unused_2484_);
v___x_2470_ = v_struct_2455_;
v_isShared_2471_ = v_isSharedCheck_2483_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_expr_2468_);
lean_dec(v_struct_2455_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2483_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2472_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__1);
v___x_2473_ = l_Lean_mkProj(v_structName_2456_, v_idx_2457_, v_expr_2468_);
v___x_2474_ = l_Lean_indentExpr(v___x_2473_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set_tag(v___x_2470_, 7);
lean_ctor_set(v___x_2470_, 1, v___x_2474_);
lean_ctor_set(v___x_2470_, 0, v___x_2472_);
v___x_2476_ = v___x_2470_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2482_; 
v_reuseFailAlloc_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2472_);
lean_ctor_set(v_reuseFailAlloc_2482_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2482_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; 
v___x_2477_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0___closed__3);
v___x_2478_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2478_, 0, v___x_2476_);
lean_ctor_set(v___x_2478_, 1, v___x_2477_);
v___x_2479_ = l_Lean_indentExpr(v_a_2458_);
v___x_2480_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2478_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
v___x_2481_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_2480_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
return v___x_2481_;
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed(lean_object* v_struct_2485_, lean_object* v_structName_2486_, lean_object* v_idx_2487_, lean_object* v_a_2488_, lean_object* v_00_u03b1_2489_, lean_object* v_x_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0(v_struct_2485_, v_structName_2486_, v_idx_2487_, v_a_2488_, v_00_u03b1_2489_, v_x_2490_, v___y_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_, v___y_2496_);
lean_dec(v___y_2496_);
lean_dec_ref(v___y_2495_);
lean_dec(v___y_2494_);
lean_dec_ref(v___y_2493_);
lean_dec(v___y_2492_);
lean_dec(v___y_2491_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(lean_object* v_a_2499_, lean_object* v_fst_2500_, lean_object* v_struct_2501_, lean_object* v_structName_2502_, uint8_t v_a_2503_, lean_object* v___f_2504_, lean_object* v_snd_2505_, lean_object* v_____r_2506_, lean_object* v_ctorType_2507_, lean_object* v_j_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
if (lean_obj_tag(v_ctorType_2507_) == 7)
{
lean_object* v_binderType_2516_; lean_object* v_body_2517_; lean_object* v___x_2518_; 
lean_dec(v_snd_2505_);
v_binderType_2516_ = lean_ctor_get(v_ctorType_2507_, 1);
lean_inc_ref(v_binderType_2516_);
v_body_2517_ = lean_ctor_get(v_ctorType_2507_, 2);
lean_inc_ref(v_body_2517_);
lean_dec_ref_known(v_ctorType_2507_, 3);
v___x_2518_ = lean_expr_instantiate_rev_range(v_binderType_2516_, v_j_2508_, v_a_2499_, v_fst_2500_);
lean_dec_ref(v_binderType_2516_);
if (v_a_2503_ == 0)
{
lean_dec_ref(v___f_2504_);
goto v___jp_2519_;
}
else
{
lean_object* v___x_2535_; 
lean_inc_ref(v___x_2518_);
v___x_2535_ = l_Lean_Meta_isProp(v___x_2518_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; uint8_t v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = lean_unbox(v_a_2536_);
lean_dec(v_a_2536_);
if (v___x_2537_ == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_box(0);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc(v___y_2509_);
v___x_2539_ = lean_apply_9(v___f_2504_, lean_box(0), v___x_2538_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, lean_box(0));
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_dec_ref_known(v___x_2539_, 1);
goto v___jp_2519_;
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_dec_ref(v___x_2518_);
lean_dec_ref(v_body_2517_);
lean_dec(v_structName_2502_);
lean_dec_ref(v_struct_2501_);
lean_dec(v_fst_2500_);
lean_dec(v_a_2499_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2539_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2539_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
else
{
lean_dec_ref(v___f_2504_);
goto v___jp_2519_;
}
}
else
{
lean_object* v_a_2548_; lean_object* v___x_2550_; uint8_t v_isShared_2551_; uint8_t v_isSharedCheck_2555_; 
lean_dec_ref(v___x_2518_);
lean_dec_ref(v_body_2517_);
lean_dec_ref(v___f_2504_);
lean_dec(v_structName_2502_);
lean_dec_ref(v_struct_2501_);
lean_dec(v_fst_2500_);
lean_dec(v_a_2499_);
v_a_2548_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2555_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2555_ == 0)
{
v___x_2550_ = v___x_2535_;
v_isShared_2551_ = v_isSharedCheck_2555_;
goto v_resetjp_2549_;
}
else
{
lean_inc(v_a_2548_);
lean_dec(v___x_2535_);
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
v___jp_2519_:
{
lean_object* v_expr_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2533_; 
v_expr_2520_ = lean_ctor_get(v_struct_2501_, 0);
v_isSharedCheck_2533_ = !lean_is_exclusive(v_struct_2501_);
if (v_isSharedCheck_2533_ == 0)
{
lean_object* v_unused_2534_; 
v_unused_2534_ = lean_ctor_get(v_struct_2501_, 1);
lean_dec(v_unused_2534_);
v___x_2522_ = v_struct_2501_;
v_isShared_2523_ = v_isSharedCheck_2533_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_expr_2520_);
lean_dec(v_struct_2501_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2533_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2527_; 
v___x_2524_ = l_Lean_Expr_proj___override(v_structName_2502_, v_a_2499_, v_expr_2520_);
v___x_2525_ = lean_array_push(v_fst_2500_, v___x_2524_);
lean_inc(v_j_2508_);
if (v_isShared_2523_ == 0)
{
lean_ctor_set(v___x_2522_, 1, v___x_2518_);
lean_ctor_set(v___x_2522_, 0, v_j_2508_);
v___x_2527_ = v___x_2522_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2532_; 
v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2532_, 0, v_j_2508_);
lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___x_2518_);
v___x_2527_ = v_reuseFailAlloc_2532_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2528_, 0, v___x_2525_);
lean_ctor_set(v___x_2528_, 1, v___x_2527_);
v___x_2529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2529_, 0, v_body_2517_);
lean_ctor_set(v___x_2529_, 1, v___x_2528_);
v___x_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
v___x_2531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2531_, 0, v___x_2530_);
return v___x_2531_;
}
}
}
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; 
lean_dec(v_structName_2502_);
lean_dec_ref(v_struct_2501_);
lean_dec(v_a_2499_);
v___x_2556_ = lean_box(0);
lean_inc(v___y_2514_);
lean_inc_ref(v___y_2513_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc(v___y_2509_);
v___x_2557_ = lean_apply_9(v___f_2504_, lean_box(0), v___x_2556_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, v___y_2514_, lean_box(0));
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2559_; uint8_t v_isShared_2560_; uint8_t v_isSharedCheck_2568_; 
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2568_ == 0)
{
lean_object* v_unused_2569_; 
v_unused_2569_ = lean_ctor_get(v___x_2557_, 0);
lean_dec(v_unused_2569_);
v___x_2559_ = v___x_2557_;
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
else
{
lean_dec(v___x_2557_);
v___x_2559_ = lean_box(0);
v_isShared_2560_ = v_isSharedCheck_2568_;
goto v_resetjp_2558_;
}
v_resetjp_2558_:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2566_; 
lean_inc(v_j_2508_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v_j_2508_);
lean_ctor_set(v___x_2561_, 1, v_snd_2505_);
v___x_2562_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2562_, 0, v_fst_2500_);
lean_ctor_set(v___x_2562_, 1, v___x_2561_);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v_ctorType_2507_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2564_, 0, v___x_2563_);
if (v_isShared_2560_ == 0)
{
lean_ctor_set(v___x_2559_, 0, v___x_2564_);
v___x_2566_ = v___x_2559_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v___x_2564_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
else
{
lean_object* v_a_2570_; lean_object* v___x_2572_; uint8_t v_isShared_2573_; uint8_t v_isSharedCheck_2577_; 
lean_dec_ref(v_ctorType_2507_);
lean_dec(v_snd_2505_);
lean_dec(v_fst_2500_);
v_a_2570_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2572_ = v___x_2557_;
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
else
{
lean_inc(v_a_2570_);
lean_dec(v___x_2557_);
v___x_2572_ = lean_box(0);
v_isShared_2573_ = v_isSharedCheck_2577_;
goto v_resetjp_2571_;
}
v_resetjp_2571_:
{
lean_object* v___x_2575_; 
if (v_isShared_2573_ == 0)
{
v___x_2575_ = v___x_2572_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_a_2570_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1___boxed(lean_object** _args){
lean_object* v_a_2578_ = _args[0];
lean_object* v_fst_2579_ = _args[1];
lean_object* v_struct_2580_ = _args[2];
lean_object* v_structName_2581_ = _args[3];
lean_object* v_a_2582_ = _args[4];
lean_object* v___f_2583_ = _args[5];
lean_object* v_snd_2584_ = _args[6];
lean_object* v_____r_2585_ = _args[7];
lean_object* v_ctorType_2586_ = _args[8];
lean_object* v_j_2587_ = _args[9];
lean_object* v___y_2588_ = _args[10];
lean_object* v___y_2589_ = _args[11];
lean_object* v___y_2590_ = _args[12];
lean_object* v___y_2591_ = _args[13];
lean_object* v___y_2592_ = _args[14];
lean_object* v___y_2593_ = _args[15];
lean_object* v___y_2594_ = _args[16];
_start:
{
uint8_t v_a_19024__boxed_2595_; lean_object* v_res_2596_; 
v_a_19024__boxed_2595_ = lean_unbox(v_a_2582_);
v_res_2596_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2578_, v_fst_2579_, v_struct_2580_, v_structName_2581_, v_a_19024__boxed_2595_, v___f_2583_, v_snd_2584_, v_____r_2585_, v_ctorType_2586_, v_j_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_, v___y_2592_, v___y_2593_);
lean_dec(v___y_2593_);
lean_dec_ref(v___y_2592_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec(v___y_2588_);
lean_dec(v_j_2587_);
return v_res_2596_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(lean_object* v_upperBound_2597_, lean_object* v_struct_2598_, lean_object* v_structName_2599_, uint8_t v_a_2600_, lean_object* v_idx_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_b_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_, lean_object* v___y_2609_, lean_object* v___y_2610_){
_start:
{
lean_object* v___y_2613_; uint8_t v___x_2635_; 
v___x_2635_ = lean_nat_dec_le(v_a_2603_, v_upperBound_2597_);
if (v___x_2635_ == 0)
{
lean_object* v___x_2636_; 
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_idx_2601_);
lean_dec(v_structName_2599_);
lean_dec_ref(v_struct_2598_);
v___x_2636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2636_, 0, v_b_2604_);
return v___x_2636_;
}
else
{
lean_object* v_snd_2637_; lean_object* v_snd_2638_; lean_object* v_fst_2639_; lean_object* v_fst_2640_; lean_object* v_fst_2641_; lean_object* v_snd_2642_; lean_object* v___f_2643_; uint8_t v___x_2644_; 
v_snd_2637_ = lean_ctor_get(v_b_2604_, 1);
lean_inc(v_snd_2637_);
v_snd_2638_ = lean_ctor_get(v_snd_2637_, 1);
lean_inc(v_snd_2638_);
v_fst_2639_ = lean_ctor_get(v_b_2604_, 0);
lean_inc(v_fst_2639_);
lean_dec_ref(v_b_2604_);
v_fst_2640_ = lean_ctor_get(v_snd_2637_, 0);
lean_inc(v_fst_2640_);
lean_dec(v_snd_2637_);
v_fst_2641_ = lean_ctor_get(v_snd_2638_, 0);
lean_inc(v_fst_2641_);
v_snd_2642_ = lean_ctor_get(v_snd_2638_, 1);
lean_inc(v_snd_2642_);
lean_dec(v_snd_2638_);
lean_inc_ref(v_a_2602_);
lean_inc(v_idx_2601_);
lean_inc(v_structName_2599_);
lean_inc_ref(v_struct_2598_);
v___f_2643_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__0___boxed), 13, 4);
lean_closure_set(v___f_2643_, 0, v_struct_2598_);
lean_closure_set(v___f_2643_, 1, v_structName_2599_);
lean_closure_set(v___f_2643_, 2, v_idx_2601_);
lean_closure_set(v___f_2643_, 3, v_a_2602_);
v___x_2644_ = l_Lean_Expr_isForall(v_fst_2639_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = lean_expr_instantiate_rev_range(v_fst_2639_, v_fst_2641_, v_a_2603_, v_fst_2640_);
lean_dec(v_fst_2641_);
lean_dec(v_fst_2639_);
lean_inc(v___y_2610_);
lean_inc_ref(v___y_2609_);
lean_inc(v___y_2608_);
lean_inc_ref(v___y_2607_);
v___x_2646_ = lean_whnf(v___x_2645_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = lean_box(0);
lean_inc(v_structName_2599_);
lean_inc_ref(v_struct_2598_);
lean_inc(v_a_2603_);
v___x_2649_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2603_, v_fst_2640_, v_struct_2598_, v_structName_2599_, v_a_2600_, v___f_2643_, v_snd_2642_, v___x_2648_, v_a_2647_, v_a_2603_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
v___y_2613_ = v___x_2649_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2657_; 
lean_dec_ref(v___f_2643_);
lean_dec(v_snd_2642_);
lean_dec(v_fst_2640_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_idx_2601_);
lean_dec(v_structName_2599_);
lean_dec_ref(v_struct_2598_);
v_a_2650_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2657_ == 0)
{
v___x_2652_ = v___x_2646_;
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
else
{
lean_inc(v_a_2650_);
lean_dec(v___x_2646_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2657_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2655_; 
if (v_isShared_2653_ == 0)
{
v___x_2655_ = v___x_2652_;
goto v_reusejp_2654_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_a_2650_);
v___x_2655_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2654_;
}
v_reusejp_2654_:
{
return v___x_2655_;
}
}
}
}
else
{
lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2658_ = lean_box(0);
lean_inc(v_structName_2599_);
lean_inc_ref(v_struct_2598_);
lean_inc(v_a_2603_);
v___x_2659_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___lam__1(v_a_2603_, v_fst_2640_, v_struct_2598_, v_structName_2599_, v_a_2600_, v___f_2643_, v_snd_2642_, v___x_2658_, v_fst_2639_, v_fst_2641_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_, v___y_2609_, v___y_2610_);
lean_dec(v_fst_2641_);
v___y_2613_ = v___x_2659_;
goto v___jp_2612_;
}
}
v___jp_2612_:
{
if (lean_obj_tag(v___y_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2626_; 
v_a_2614_ = lean_ctor_get(v___y_2613_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___y_2613_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2616_ = v___y_2613_;
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___y_2613_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2626_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
if (lean_obj_tag(v_a_2614_) == 0)
{
lean_object* v_a_2618_; lean_object* v___x_2620_; 
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_idx_2601_);
lean_dec(v_structName_2599_);
lean_dec_ref(v_struct_2598_);
v_a_2618_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_a_2618_);
lean_dec_ref_known(v_a_2614_, 1);
if (v_isShared_2617_ == 0)
{
lean_ctor_set(v___x_2616_, 0, v_a_2618_);
v___x_2620_ = v___x_2616_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2618_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
else
{
lean_object* v_a_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
lean_del_object(v___x_2616_);
v_a_2622_ = lean_ctor_get(v_a_2614_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v_a_2614_, 1);
v___x_2623_ = lean_unsigned_to_nat(1u);
v___x_2624_ = lean_nat_add(v_a_2603_, v___x_2623_);
lean_dec(v_a_2603_);
v_a_2603_ = v___x_2624_;
v_b_2604_ = v_a_2622_;
goto _start;
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_idx_2601_);
lean_dec(v_structName_2599_);
lean_dec_ref(v_struct_2598_);
v_a_2627_ = lean_ctor_get(v___y_2613_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___y_2613_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___y_2613_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___y_2613_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg___boxed(lean_object* v_upperBound_2660_, lean_object* v_struct_2661_, lean_object* v_structName_2662_, lean_object* v_a_2663_, lean_object* v_idx_2664_, lean_object* v_a_2665_, lean_object* v_a_2666_, lean_object* v_b_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_, lean_object* v___y_2671_, lean_object* v___y_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_){
_start:
{
uint8_t v_a_19181__boxed_2675_; lean_object* v_res_2676_; 
v_a_19181__boxed_2675_ = lean_unbox(v_a_2663_);
v_res_2676_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2660_, v_struct_2661_, v_structName_2662_, v_a_19181__boxed_2675_, v_idx_2664_, v_a_2665_, v_a_2666_, v_b_2667_, v___y_2668_, v___y_2669_, v___y_2670_, v___y_2671_, v___y_2672_, v___y_2673_);
lean_dec(v___y_2673_);
lean_dec_ref(v___y_2672_);
lean_dec(v___y_2671_);
lean_dec_ref(v___y_2670_);
lean_dec(v___y_2669_);
lean_dec(v___y_2668_);
lean_dec(v_upperBound_2660_);
return v_res_2676_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2(void){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2679_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__1));
v___x_2680_ = lean_unsigned_to_nat(18u);
v___x_2681_ = lean_unsigned_to_nat(1896u);
v___x_2682_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__0));
v___x_2683_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp___closed__0));
v___x_2684_ = l_mkPanicMessageWithDecl(v___x_2683_, v___x_2682_, v___x_2681_, v___x_2680_, v___x_2679_);
return v___x_2684_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3(void){
_start:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2685_ = lean_obj_once(&l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2, &l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2_once, _init_l_Lean_Meta_LetToHave_instInhabitedResult_default___closed__2);
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2687_, 0, v___x_2686_);
lean_ctor_set(v___x_2687_, 1, v___x_2685_);
return v___x_2687_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v___x_2688_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__3);
v___x_2689_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_2690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
lean_ctor_set(v___x_2690_, 1, v___x_2688_);
return v___x_2690_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5(void){
_start:
{
lean_object* v___x_2691_; lean_object* v_dummy_2692_; 
v___x_2691_ = lean_box(0);
v_dummy_2692_ = l_Lean_Expr_sort___override(v___x_2691_);
return v_dummy_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(lean_object* v_e_2693_, lean_object* v_structName_2694_, lean_object* v_idx_2695_, lean_object* v_struct_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v___y_2705_; lean_object* v___y_2706_; lean_object* v___y_2711_; uint8_t v___x_2715_; 
v___x_2715_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2697_);
if (v___x_2715_ == 0)
{
lean_dec(v_idx_2695_);
lean_dec(v_structName_2694_);
if (lean_obj_tag(v_e_2693_) == 11)
{
lean_object* v_expr_2716_; lean_object* v_typeName_2717_; lean_object* v_idx_2718_; lean_object* v_struct_2719_; size_t v___x_2720_; size_t v___x_2721_; uint8_t v___x_2722_; 
v_expr_2716_ = lean_ctor_get(v_struct_2696_, 0);
lean_inc_ref(v_expr_2716_);
lean_dec_ref(v_struct_2696_);
v_typeName_2717_ = lean_ctor_get(v_e_2693_, 0);
v_idx_2718_ = lean_ctor_get(v_e_2693_, 1);
v_struct_2719_ = lean_ctor_get(v_e_2693_, 2);
v___x_2720_ = lean_ptr_addr(v_struct_2719_);
v___x_2721_ = lean_ptr_addr(v_expr_2716_);
v___x_2722_ = lean_usize_dec_eq(v___x_2720_, v___x_2721_);
if (v___x_2722_ == 0)
{
lean_object* v___x_2723_; 
lean_inc(v_idx_2718_);
lean_inc(v_typeName_2717_);
lean_dec_ref_known(v_e_2693_, 3);
v___x_2723_ = l_Lean_Expr_proj___override(v_typeName_2717_, v_idx_2718_, v_expr_2716_);
v___y_2711_ = v___x_2723_;
goto v___jp_2710_;
}
else
{
lean_dec_ref(v_expr_2716_);
v___y_2711_ = v_e_2693_;
goto v___jp_2710_;
}
}
else
{
lean_object* v___x_2724_; lean_object* v___x_2725_; 
lean_dec_ref(v_struct_2696_);
lean_dec_ref(v_e_2693_);
v___x_2724_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2725_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2724_);
v___y_2711_ = v___x_2725_;
goto v___jp_2710_;
}
}
else
{
lean_object* v___x_2726_; 
lean_inc_ref(v_struct_2696_);
v___x_2726_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_struct_2696_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
if (lean_obj_tag(v___x_2726_) == 0)
{
lean_object* v_a_2727_; lean_object* v___x_2728_; 
v_a_2727_ = lean_ctor_get(v___x_2726_, 0);
lean_inc(v_a_2727_);
lean_dec_ref_known(v___x_2726_, 1);
lean_inc(v_a_2702_);
lean_inc_ref(v_a_2701_);
lean_inc(v_a_2700_);
lean_inc_ref(v_a_2699_);
v___x_2728_ = lean_whnf(v_a_2727_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
if (lean_obj_tag(v___x_2728_) == 0)
{
lean_object* v_a_2729_; lean_object* v___x_2730_; 
v_a_2729_ = lean_ctor_get(v___x_2728_, 0);
lean_inc_n(v_a_2729_, 2);
lean_dec_ref_known(v___x_2728_, 1);
v___x_2730_ = l_Lean_Meta_isProp(v_a_2729_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
if (lean_obj_tag(v___x_2730_) == 0)
{
lean_object* v_a_2731_; lean_object* v___x_2732_; 
v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc(v_a_2731_);
lean_dec_ref_known(v___x_2730_, 1);
v___x_2732_ = l_Lean_Expr_getAppFn(v_a_2729_);
if (lean_obj_tag(v___x_2732_) == 4)
{
lean_object* v_declName_2733_; lean_object* v_us_2734_; lean_object* v___x_2735_; lean_object* v_env_2739_; uint8_t v___x_2740_; lean_object* v___x_2741_; 
v_declName_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_declName_2733_);
v_us_2734_ = lean_ctor_get(v___x_2732_, 1);
lean_inc(v_us_2734_);
lean_dec_ref_known(v___x_2732_, 2);
v___x_2735_ = lean_st_ref_get(v_a_2702_);
v_env_2739_ = lean_ctor_get(v___x_2735_, 0);
lean_inc_ref(v_env_2739_);
lean_dec(v___x_2735_);
v___x_2740_ = 0;
v___x_2741_ = l_Lean_Environment_find_x3f(v_env_2739_, v_declName_2733_, v___x_2740_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
v___x_2742_ = lean_box(0);
v___x_2743_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2696_, v_structName_2694_, v_idx_2695_, v_a_2729_, lean_box(0), v___x_2742_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2743_;
}
else
{
lean_object* v_val_2744_; 
v_val_2744_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_val_2744_);
lean_dec_ref_known(v___x_2741_, 1);
if (lean_obj_tag(v_val_2744_) == 5)
{
lean_object* v_val_2745_; lean_object* v_ctors_2746_; 
v_val_2745_ = lean_ctor_get(v_val_2744_, 0);
lean_inc_ref(v_val_2745_);
lean_dec_ref_known(v_val_2744_, 1);
v_ctors_2746_ = lean_ctor_get(v_val_2745_, 4);
lean_inc(v_ctors_2746_);
if (lean_obj_tag(v_ctors_2746_) == 1)
{
lean_object* v_tail_2747_; 
v_tail_2747_ = lean_ctor_get(v_ctors_2746_, 1);
if (lean_obj_tag(v_tail_2747_) == 0)
{
lean_object* v_toConstantVal_2748_; lean_object* v_numParams_2749_; lean_object* v_numIndices_2750_; lean_object* v_head_2751_; lean_object* v___x_2753_; uint8_t v_isShared_2754_; uint8_t v_isSharedCheck_2860_; 
v_toConstantVal_2748_ = lean_ctor_get(v_val_2745_, 0);
lean_inc_ref(v_toConstantVal_2748_);
v_numParams_2749_ = lean_ctor_get(v_val_2745_, 1);
lean_inc(v_numParams_2749_);
v_numIndices_2750_ = lean_ctor_get(v_val_2745_, 2);
lean_inc(v_numIndices_2750_);
lean_dec_ref(v_val_2745_);
v_head_2751_ = lean_ctor_get(v_ctors_2746_, 0);
v_isSharedCheck_2860_ = !lean_is_exclusive(v_ctors_2746_);
if (v_isSharedCheck_2860_ == 0)
{
lean_object* v_unused_2861_; 
v_unused_2861_ = lean_ctor_get(v_ctors_2746_, 1);
lean_dec(v_unused_2861_);
v___x_2753_ = v_ctors_2746_;
v_isShared_2754_ = v_isSharedCheck_2860_;
goto v_resetjp_2752_;
}
else
{
lean_inc(v_head_2751_);
lean_dec(v_ctors_2746_);
v___x_2753_ = lean_box(0);
v_isShared_2754_ = v_isSharedCheck_2860_;
goto v_resetjp_2752_;
}
v_resetjp_2752_:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_getConstInfo___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__0(v_head_2751_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; 
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2755_, 1);
if (lean_obj_tag(v_a_2756_) == 6)
{
lean_object* v_val_2757_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v_name_2838_; uint8_t v___x_2839_; 
v_val_2757_ = lean_ctor_get(v_a_2756_, 0);
lean_inc_ref(v_val_2757_);
lean_dec_ref_known(v_a_2756_, 1);
v_name_2838_ = lean_ctor_get(v_toConstantVal_2748_, 0);
lean_inc(v_name_2838_);
lean_dec_ref(v_toConstantVal_2748_);
v___x_2839_ = lean_name_eq(v_name_2838_, v_structName_2694_);
lean_dec(v_name_2838_);
if (v___x_2839_ == 0)
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec_ref(v_val_2757_);
lean_del_object(v___x_2753_);
lean_dec(v_numIndices_2750_);
lean_dec(v_numParams_2749_);
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
v___x_2840_ = lean_box(0);
v___x_2841_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2696_, v_structName_2694_, v_idx_2695_, v_a_2729_, lean_box(0), v___x_2840_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
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
v___y_2813_ = v_a_2697_;
v___y_2814_ = v_a_2698_;
v___y_2815_ = v_a_2699_;
v___y_2816_ = v_a_2700_;
v___y_2817_ = v_a_2701_;
v___y_2818_ = v_a_2702_;
goto v___jp_2812_;
}
v___jp_2758_:
{
lean_object* v_toConstantVal_2766_; lean_object* v_name_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; 
v_toConstantVal_2766_ = lean_ctor_get(v_val_2757_, 0);
lean_inc_ref(v_toConstantVal_2766_);
lean_dec_ref(v_val_2757_);
v_name_2767_ = lean_ctor_get(v_toConstantVal_2766_, 0);
lean_inc(v_name_2767_);
lean_dec_ref(v_toConstantVal_2766_);
v___x_2768_ = l_Lean_mkConst(v_name_2767_, v_us_2734_);
v___x_2769_ = lean_unsigned_to_nat(0u);
v___x_2770_ = l_Array_toSubarray___redArg(v___y_2759_, v___x_2769_, v_numParams_2749_);
v___x_2771_ = l_Subarray_copy___redArg(v___x_2770_);
v___x_2772_ = l_Lean_mkAppN(v___x_2768_, v___x_2771_);
lean_dec_ref(v___x_2771_);
lean_inc(v___y_2765_);
lean_inc_ref(v___y_2764_);
lean_inc(v___y_2763_);
lean_inc_ref(v___y_2762_);
v___x_2773_ = lean_infer_type(v___x_2772_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v___x_2777_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__4);
if (v_isShared_2754_ == 0)
{
lean_ctor_set_tag(v___x_2753_, 0);
lean_ctor_set(v___x_2753_, 1, v___x_2775_);
lean_ctor_set(v___x_2753_, 0, v_a_2774_);
v___x_2777_ = v___x_2753_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2803_; 
v_reuseFailAlloc_2803_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2803_, 0, v_a_2774_);
lean_ctor_set(v_reuseFailAlloc_2803_, 1, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2803_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
uint8_t v___x_2778_; lean_object* v___x_2779_; 
v___x_2778_ = lean_unbox(v_a_2731_);
lean_dec(v_a_2731_);
lean_inc_ref(v_struct_2696_);
lean_inc(v_idx_2695_);
v___x_2779_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_idx_2695_, v_struct_2696_, v_structName_2694_, v___x_2778_, v_idx_2695_, v_a_2729_, v___x_2769_, v___x_2777_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
lean_dec(v_idx_2695_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v_snd_2781_; lean_object* v_snd_2782_; lean_object* v_snd_2783_; lean_object* v_expr_2784_; lean_object* v___x_2785_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v_snd_2781_ = lean_ctor_get(v_a_2780_, 1);
lean_inc(v_snd_2781_);
lean_dec(v_a_2780_);
v_snd_2782_ = lean_ctor_get(v_snd_2781_, 1);
lean_inc(v_snd_2782_);
lean_dec(v_snd_2781_);
v_snd_2783_ = lean_ctor_get(v_snd_2782_, 1);
lean_inc(v_snd_2783_);
lean_dec(v_snd_2782_);
v_expr_2784_ = lean_ctor_get(v_struct_2696_, 0);
lean_inc_ref(v_expr_2784_);
lean_dec_ref(v_struct_2696_);
v___x_2785_ = l_Lean_Expr_cleanupAnnotations(v_snd_2783_);
if (lean_obj_tag(v_e_2693_) == 11)
{
lean_object* v_typeName_2786_; lean_object* v_idx_2787_; lean_object* v_struct_2788_; size_t v___x_2789_; size_t v___x_2790_; uint8_t v___x_2791_; 
v_typeName_2786_ = lean_ctor_get(v_e_2693_, 0);
v_idx_2787_ = lean_ctor_get(v_e_2693_, 1);
v_struct_2788_ = lean_ctor_get(v_e_2693_, 2);
v___x_2789_ = lean_ptr_addr(v_struct_2788_);
v___x_2790_ = lean_ptr_addr(v_expr_2784_);
v___x_2791_ = lean_usize_dec_eq(v___x_2789_, v___x_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
lean_inc(v_idx_2787_);
lean_inc(v_typeName_2786_);
lean_dec_ref_known(v_e_2693_, 3);
v___x_2792_ = l_Lean_Expr_proj___override(v_typeName_2786_, v_idx_2787_, v_expr_2784_);
v___y_2705_ = v___x_2785_;
v___y_2706_ = v___x_2792_;
goto v___jp_2704_;
}
else
{
lean_dec_ref(v_expr_2784_);
v___y_2705_ = v___x_2785_;
v___y_2706_ = v_e_2693_;
goto v___jp_2704_;
}
}
else
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec_ref(v_expr_2784_);
lean_dec_ref(v_e_2693_);
v___x_2793_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__2);
v___x_2794_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_2793_);
v___y_2705_ = v___x_2785_;
v___y_2706_ = v___x_2794_;
goto v___jp_2704_;
}
}
else
{
lean_object* v_a_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2802_; 
lean_dec_ref(v_struct_2696_);
lean_dec_ref(v_e_2693_);
v_a_2795_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2797_ = v___x_2779_;
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
else
{
lean_inc(v_a_2795_);
lean_dec(v___x_2779_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2802_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2800_; 
if (v_isShared_2798_ == 0)
{
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
v___x_2800_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2799_;
}
v_reusejp_2799_:
{
return v___x_2800_;
}
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_del_object(v___x_2753_);
lean_dec(v_a_2731_);
lean_dec(v_a_2729_);
lean_dec_ref(v_struct_2696_);
lean_dec(v_idx_2695_);
lean_dec(v_structName_2694_);
lean_dec_ref(v_e_2693_);
v_a_2804_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2773_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2773_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
v___jp_2812_:
{
lean_object* v_dummy_2819_; lean_object* v_nargs_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; uint8_t v___x_2827_; 
v_dummy_2819_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_2820_ = l_Lean_Expr_getAppNumArgs(v_a_2729_);
lean_inc(v_nargs_2820_);
v___x_2821_ = lean_mk_array(v_nargs_2820_, v_dummy_2819_);
v___x_2822_ = lean_unsigned_to_nat(1u);
v___x_2823_ = lean_nat_sub(v_nargs_2820_, v___x_2822_);
lean_dec(v_nargs_2820_);
lean_inc(v_a_2729_);
v___x_2824_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2729_, v___x_2821_, v___x_2823_);
v___x_2825_ = lean_nat_add(v_numParams_2749_, v_numIndices_2750_);
lean_dec(v_numIndices_2750_);
v___x_2826_ = lean_array_get_size(v___x_2824_);
v___x_2827_ = lean_nat_dec_eq(v___x_2825_, v___x_2826_);
lean_dec(v___x_2825_);
if (v___x_2827_ == 0)
{
if (v___x_2715_ == 0)
{
v___y_2759_ = v___x_2824_;
v___y_2760_ = v___y_2813_;
v___y_2761_ = v___y_2814_;
v___y_2762_ = v___y_2815_;
v___y_2763_ = v___y_2816_;
v___y_2764_ = v___y_2817_;
v___y_2765_ = v___y_2818_;
goto v___jp_2758_;
}
else
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v_a_2830_; lean_object* v___x_2832_; uint8_t v_isShared_2833_; uint8_t v_isSharedCheck_2837_; 
lean_dec_ref(v___x_2824_);
lean_dec_ref(v_val_2757_);
lean_del_object(v___x_2753_);
lean_dec(v_numParams_2749_);
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
v___x_2828_ = lean_box(0);
v___x_2829_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2696_, v_structName_2694_, v_idx_2695_, v_a_2729_, lean_box(0), v___x_2828_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_);
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2837_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2837_ == 0)
{
v___x_2832_ = v___x_2829_;
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
else
{
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2832_ = lean_box(0);
v_isShared_2833_ = v_isSharedCheck_2837_;
goto v_resetjp_2831_;
}
v_resetjp_2831_:
{
lean_object* v___x_2835_; 
if (v_isShared_2833_ == 0)
{
v___x_2835_ = v___x_2832_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_a_2830_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
else
{
v___y_2759_ = v___x_2824_;
v___y_2760_ = v___y_2813_;
v___y_2761_ = v___y_2814_;
v___y_2762_ = v___y_2815_;
v___y_2763_ = v___y_2816_;
v___y_2764_ = v___y_2817_;
v___y_2765_ = v___y_2818_;
goto v___jp_2758_;
}
}
}
else
{
lean_object* v___x_2850_; lean_object* v___x_2851_; 
lean_dec(v_a_2756_);
lean_del_object(v___x_2753_);
lean_dec(v_numIndices_2750_);
lean_dec(v_numParams_2749_);
lean_dec_ref(v_toConstantVal_2748_);
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
v___x_2850_ = lean_box(0);
v___x_2851_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2696_, v_structName_2694_, v_idx_2695_, v_a_2729_, lean_box(0), v___x_2850_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2851_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_del_object(v___x_2753_);
lean_dec(v_numIndices_2750_);
lean_dec(v_numParams_2749_);
lean_dec_ref(v_toConstantVal_2748_);
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec(v_a_2729_);
lean_dec_ref(v_struct_2696_);
lean_dec(v_idx_2695_);
lean_dec(v_structName_2694_);
lean_dec_ref(v_e_2693_);
v_a_2852_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2755_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2755_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
}
else
{
lean_dec_ref_known(v_ctors_2746_, 2);
lean_dec_ref(v_val_2745_);
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
goto v___jp_2736_;
}
}
else
{
lean_dec(v_ctors_2746_);
lean_dec_ref(v_val_2745_);
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
goto v___jp_2736_;
}
}
else
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
lean_dec(v_val_2744_);
lean_dec(v_us_2734_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
v___x_2862_ = lean_box(0);
v___x_2863_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2696_, v_structName_2694_, v_idx_2695_, v_a_2729_, lean_box(0), v___x_2862_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2863_;
}
}
v___jp_2736_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = lean_box(0);
v___x_2738_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2696_, v_structName_2694_, v_idx_2695_, v_a_2729_, lean_box(0), v___x_2737_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2738_;
}
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref(v___x_2732_);
lean_dec(v_a_2731_);
lean_dec_ref(v_e_2693_);
v___x_2864_ = lean_box(0);
v___x_2865_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___lam__0(v_struct_2696_, v_structName_2694_, v_idx_2695_, v_a_2729_, lean_box(0), v___x_2864_, v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_, v_a_2701_, v_a_2702_);
return v___x_2865_;
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec(v_a_2729_);
lean_dec_ref(v_struct_2696_);
lean_dec(v_idx_2695_);
lean_dec(v_structName_2694_);
lean_dec_ref(v_e_2693_);
v_a_2866_ = lean_ctor_get(v___x_2730_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2730_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2730_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2730_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec_ref(v_struct_2696_);
lean_dec(v_idx_2695_);
lean_dec(v_structName_2694_);
lean_dec_ref(v_e_2693_);
v_a_2874_ = lean_ctor_get(v___x_2728_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2728_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2728_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2728_);
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
lean_dec_ref(v_struct_2696_);
lean_dec(v_idx_2695_);
lean_dec(v_structName_2694_);
lean_dec_ref(v_e_2693_);
v_a_2882_ = lean_ctor_get(v___x_2726_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2726_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2726_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2726_);
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
v___jp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; 
v___x_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2707_, 0, v___y_2705_);
v___x_2708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___y_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2708_);
return v___x_2709_;
}
v___jp_2710_:
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2712_ = lean_box(0);
v___x_2713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2713_, 0, v___y_2711_);
lean_ctor_set(v___x_2713_, 1, v___x_2712_);
v___x_2714_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2714_, 0, v___x_2713_);
return v___x_2714_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___boxed(lean_object* v_e_2890_, lean_object* v_structName_2891_, lean_object* v_idx_2892_, lean_object* v_struct_2893_, lean_object* v_a_2894_, lean_object* v_a_2895_, lean_object* v_a_2896_, lean_object* v_a_2897_, lean_object* v_a_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_2890_, v_structName_2891_, v_idx_2892_, v_struct_2893_, v_a_2894_, v_a_2895_, v_a_2896_, v_a_2897_, v_a_2898_, v_a_2899_);
lean_dec(v_a_2899_);
lean_dec_ref(v_a_2898_);
lean_dec(v_a_2897_);
lean_dec_ref(v_a_2896_);
lean_dec(v_a_2895_);
lean_dec(v_a_2894_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(lean_object* v_upperBound_2902_, lean_object* v_struct_2903_, lean_object* v_structName_2904_, uint8_t v_a_2905_, lean_object* v_idx_2906_, lean_object* v_a_2907_, lean_object* v_inst_2908_, lean_object* v_R_2909_, lean_object* v_a_2910_, lean_object* v_b_2911_, lean_object* v_c_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___redArg(v_upperBound_2902_, v_struct_2903_, v_structName_2904_, v_a_2905_, v_idx_2906_, v_a_2907_, v_a_2910_, v_b_2911_, v___y_2913_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_);
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1___boxed(lean_object** _args){
lean_object* v_upperBound_2921_ = _args[0];
lean_object* v_struct_2922_ = _args[1];
lean_object* v_structName_2923_ = _args[2];
lean_object* v_a_2924_ = _args[3];
lean_object* v_idx_2925_ = _args[4];
lean_object* v_a_2926_ = _args[5];
lean_object* v_inst_2927_ = _args[6];
lean_object* v_R_2928_ = _args[7];
lean_object* v_a_2929_ = _args[8];
lean_object* v_b_2930_ = _args[9];
lean_object* v_c_2931_ = _args[10];
lean_object* v___y_2932_ = _args[11];
lean_object* v___y_2933_ = _args[12];
lean_object* v___y_2934_ = _args[13];
lean_object* v___y_2935_ = _args[14];
lean_object* v___y_2936_ = _args[15];
lean_object* v___y_2937_ = _args[16];
lean_object* v___y_2938_ = _args[17];
_start:
{
uint8_t v_a_19705__boxed_2939_; lean_object* v_res_2940_; 
v_a_19705__boxed_2939_ = lean_unbox(v_a_2924_);
v_res_2940_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj_spec__1(v_upperBound_2921_, v_struct_2922_, v_structName_2923_, v_a_19705__boxed_2939_, v_idx_2925_, v_a_2926_, v_inst_2927_, v_R_2928_, v_a_2929_, v_b_2930_, v_c_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec(v___y_2932_);
lean_dec(v_upperBound_2921_);
return v_res_2940_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(lean_object* v_as_2941_, size_t v_i_2942_, size_t v_stop_2943_, lean_object* v_b_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
uint8_t v___x_2951_; 
v___x_2951_ = lean_usize_dec_eq(v_i_2942_, v_stop_2943_);
if (v___x_2951_ == 0)
{
size_t v___x_2952_; size_t v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2952_ = ((size_t)1ULL);
v___x_2953_ = lean_usize_sub(v_i_2942_, v___x_2952_);
v___x_2954_ = lean_array_uget_borrowed(v_as_2941_, v___x_2953_);
lean_inc(v___x_2954_);
v___x_2955_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v___x_2954_, v___y_2945_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref_known(v___x_2955_, 1);
v___x_2957_ = l_Lean_Expr_sortLevel_x21(v_a_2956_);
lean_dec(v_a_2956_);
v___x_2958_ = l_Lean_mkLevelIMax_x27(v___x_2957_, v_b_2944_);
v_i_2942_ = v___x_2953_;
v_b_2944_ = v___x_2958_;
goto _start;
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec(v_b_2944_);
v_a_2960_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2955_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2955_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v___x_2968_; 
v___x_2968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2968_, 0, v_b_2944_);
return v___x_2968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg___boxed(lean_object* v_as_2969_, lean_object* v_i_2970_, lean_object* v_stop_2971_, lean_object* v_b_2972_, lean_object* v___y_2973_, lean_object* v___y_2974_, lean_object* v___y_2975_, lean_object* v___y_2976_, lean_object* v___y_2977_, lean_object* v___y_2978_){
_start:
{
size_t v_i_boxed_2979_; size_t v_stop_boxed_2980_; lean_object* v_res_2981_; 
v_i_boxed_2979_ = lean_unbox_usize(v_i_2970_);
lean_dec(v_i_2970_);
v_stop_boxed_2980_ = lean_unbox_usize(v_stop_2971_);
lean_dec(v_stop_2971_);
v_res_2981_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_2969_, v_i_boxed_2979_, v_stop_boxed_2980_, v_b_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_);
lean_dec(v___y_2977_);
lean_dec_ref(v___y_2976_);
lean_dec(v___y_2975_);
lean_dec_ref(v___y_2974_);
lean_dec(v___y_2973_);
lean_dec_ref(v_as_2969_);
return v_res_2981_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3(void){
_start:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; 
v___x_2985_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__2));
v___x_2986_ = lean_unsigned_to_nat(14u);
v___x_2987_ = lean_unsigned_to_nat(22u);
v___x_2988_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__1));
v___x_2989_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__0));
v___x_2990_ = l_mkPanicMessageWithDecl(v___x_2989_, v___x_2988_, v___x_2987_, v___x_2986_, v___x_2985_);
return v___x_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(lean_object* v_fvars_2991_, lean_object* v_doms_2992_, lean_object* v_body_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_, lean_object* v_a_2999_){
_start:
{
lean_object* v_lctx_3001_; lean_object* v_expr_3002_; uint8_t v___x_3003_; uint8_t v___x_3004_; lean_object* v___x_3005_; lean_object* v_a_3007_; uint8_t v___x_3012_; 
v_lctx_3001_ = lean_ctor_get(v_a_2996_, 2);
v_expr_3002_ = lean_ctor_get(v_body_2993_, 0);
v___x_3003_ = 1;
v___x_3004_ = 0;
lean_inc_ref(v_lctx_3001_);
v___x_3005_ = l_Lean_LocalContext_mkForall(v_lctx_3001_, v_fvars_2991_, v_expr_3002_, v___x_3003_, v___x_3004_);
v___x_3012_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_2994_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3021_; 
v_isSharedCheck_3021_ = !lean_is_exclusive(v_body_2993_);
if (v_isSharedCheck_3021_ == 0)
{
lean_object* v_unused_3022_; lean_object* v_unused_3023_; 
v_unused_3022_ = lean_ctor_get(v_body_2993_, 1);
lean_dec(v_unused_3022_);
v_unused_3023_ = lean_ctor_get(v_body_2993_, 0);
lean_dec(v_unused_3023_);
v___x_3014_ = v_body_2993_;
v_isShared_3015_ = v_isSharedCheck_3021_;
goto v_resetjp_3013_;
}
else
{
lean_dec(v_body_2993_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3021_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3016_ = lean_box(0);
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 1, v___x_3016_);
lean_ctor_set(v___x_3014_, 0, v___x_3005_);
v___x_3018_ = v___x_3014_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v___x_3016_);
v___x_3018_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
lean_object* v___x_3019_; 
v___x_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
return v___x_3019_;
}
}
}
else
{
lean_object* v___x_3024_; 
v___x_3024_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_body_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___y_3027_; lean_object* v_type_x3f_3044_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v_type_x3f_3044_ = lean_ctor_get(v_a_3025_, 1);
lean_inc(v_type_x3f_3044_);
lean_dec(v_a_3025_);
if (lean_obj_tag(v_type_x3f_3044_) == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___closed__3);
v___x_3046_ = l_panic___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp_spec__0(v___x_3045_);
v___y_3027_ = v___x_3046_;
goto v___jp_3026_;
}
else
{
lean_object* v_val_3047_; 
v_val_3047_ = lean_ctor_get(v_type_x3f_3044_, 0);
lean_inc(v_val_3047_);
lean_dec_ref_known(v_type_x3f_3044_, 1);
v___y_3027_ = v_val_3047_;
goto v___jp_3026_;
}
v___jp_3026_:
{
lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v___x_3028_ = l_Lean_Expr_sortLevel_x21(v___y_3027_);
lean_dec_ref(v___y_3027_);
v___x_3029_ = lean_array_get_size(v_doms_2992_);
v___x_3030_ = lean_unsigned_to_nat(0u);
v___x_3031_ = lean_nat_dec_lt(v___x_3030_, v___x_3029_);
if (v___x_3031_ == 0)
{
v_a_3007_ = v___x_3028_;
goto v___jp_3006_;
}
else
{
size_t v___x_3032_; size_t v___x_3033_; lean_object* v___x_3034_; 
v___x_3032_ = lean_usize_of_nat(v___x_3029_);
v___x_3033_ = ((size_t)0ULL);
v___x_3034_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_doms_2992_, v___x_3032_, v___x_3033_, v___x_3028_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v_a_3007_ = v_a_3035_;
goto v___jp_3006_;
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec_ref(v___x_3005_);
v_a_3036_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3034_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3034_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
}
}
}
}
}
}
else
{
lean_dec_ref(v___x_3005_);
return v___x_3024_;
}
}
v___jp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
v___x_3008_ = l_Lean_Expr_sort___override(v_a_3007_);
v___x_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3009_, 0, v___x_3008_);
v___x_3010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3010_, 0, v___x_3005_);
lean_ctor_set(v___x_3010_, 1, v___x_3009_);
v___x_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
return v___x_3011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed(lean_object* v_fvars_3048_, lean_object* v_doms_3049_, lean_object* v_body_3050_, lean_object* v_a_3051_, lean_object* v_a_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3048_, v_doms_3049_, v_body_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
lean_dec(v_a_3052_);
lean_dec(v_a_3051_);
lean_dec_ref(v_doms_3049_);
lean_dec_ref(v_fvars_3048_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(lean_object* v_as_3059_, size_t v_i_3060_, size_t v_stop_3061_, lean_object* v_b_3062_, lean_object* v___y_3063_, lean_object* v___y_3064_, lean_object* v___y_3065_, lean_object* v___y_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___redArg(v_as_3059_, v_i_3060_, v_stop_3061_, v_b_3062_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_);
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0___boxed(lean_object* v_as_3071_, lean_object* v_i_3072_, lean_object* v_stop_3073_, lean_object* v_b_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
size_t v_i_boxed_3082_; size_t v_stop_boxed_3083_; lean_object* v_res_3084_; 
v_i_boxed_3082_ = lean_unbox_usize(v_i_3072_);
lean_dec(v_i_3072_);
v_stop_boxed_3083_ = lean_unbox_usize(v_stop_3073_);
lean_dec(v_stop_3073_);
v_res_3084_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize_spec__0(v_as_3071_, v_i_boxed_3082_, v_stop_boxed_3083_, v_b_3074_, v___y_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_, v___y_3080_);
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3079_);
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3077_);
lean_dec(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v_as_3071_);
return v_res_3084_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(lean_object* v_opts_3085_, lean_object* v_opt_3086_){
_start:
{
lean_object* v_name_3087_; lean_object* v_defValue_3088_; lean_object* v_map_3089_; lean_object* v___x_3090_; 
v_name_3087_ = lean_ctor_get(v_opt_3086_, 0);
v_defValue_3088_ = lean_ctor_get(v_opt_3086_, 1);
v_map_3089_ = lean_ctor_get(v_opts_3085_, 0);
v___x_3090_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3089_, v_name_3087_);
if (lean_obj_tag(v___x_3090_) == 0)
{
uint8_t v___x_3091_; 
v___x_3091_ = lean_unbox(v_defValue_3088_);
return v___x_3091_;
}
else
{
lean_object* v_val_3092_; 
v_val_3092_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v___x_3090_, 1);
if (lean_obj_tag(v_val_3092_) == 1)
{
uint8_t v_v_3093_; 
v_v_3093_ = lean_ctor_get_uint8(v_val_3092_, 0);
lean_dec_ref_known(v_val_3092_, 0);
return v_v_3093_;
}
else
{
uint8_t v___x_3094_; 
lean_dec(v_val_3092_);
v___x_3094_ = lean_unbox(v_defValue_3088_);
return v___x_3094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5___boxed(lean_object* v_opts_3095_, lean_object* v_opt_3096_){
_start:
{
uint8_t v_res_3097_; lean_object* v_r_3098_; 
v_res_3097_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3095_, v_opt_3096_);
lean_dec_ref(v_opt_3096_);
lean_dec_ref(v_opts_3095_);
v_r_3098_ = lean_box(v_res_3097_);
return v_r_3098_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(lean_object* v_x_3099_){
_start:
{
if (lean_obj_tag(v_x_3099_) == 0)
{
lean_object* v_a_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3108_; 
v_a_3101_ = lean_ctor_get(v_x_3099_, 0);
v_isSharedCheck_3108_ = !lean_is_exclusive(v_x_3099_);
if (v_isSharedCheck_3108_ == 0)
{
v___x_3103_ = v_x_3099_;
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_a_3101_);
lean_dec(v_x_3099_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3108_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___x_3106_; 
if (v_isShared_3104_ == 0)
{
lean_ctor_set_tag(v___x_3103_, 1);
v___x_3106_ = v___x_3103_;
goto v_reusejp_3105_;
}
else
{
lean_object* v_reuseFailAlloc_3107_; 
v_reuseFailAlloc_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3107_, 0, v_a_3101_);
v___x_3106_ = v_reuseFailAlloc_3107_;
goto v_reusejp_3105_;
}
v_reusejp_3105_:
{
return v___x_3106_;
}
}
}
else
{
lean_object* v_a_3109_; lean_object* v___x_3111_; uint8_t v_isShared_3112_; uint8_t v_isSharedCheck_3116_; 
v_a_3109_ = lean_ctor_get(v_x_3099_, 0);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_x_3099_);
if (v_isSharedCheck_3116_ == 0)
{
v___x_3111_ = v_x_3099_;
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
else
{
lean_inc(v_a_3109_);
lean_dec(v_x_3099_);
v___x_3111_ = lean_box(0);
v_isShared_3112_ = v_isSharedCheck_3116_;
goto v_resetjp_3110_;
}
v_resetjp_3110_:
{
lean_object* v___x_3114_; 
if (v_isShared_3112_ == 0)
{
lean_ctor_set_tag(v___x_3111_, 0);
v___x_3114_ = v___x_3111_;
goto v_reusejp_3113_;
}
else
{
lean_object* v_reuseFailAlloc_3115_; 
v_reuseFailAlloc_3115_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg___boxed(lean_object* v_x_3117_, lean_object* v___y_3118_){
_start:
{
lean_object* v_res_3119_; 
v_res_3119_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_3117_);
return v_res_3119_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(lean_object* v_e_3120_){
_start:
{
if (lean_obj_tag(v_e_3120_) == 0)
{
uint8_t v___x_3121_; 
v___x_3121_ = 2;
return v___x_3121_;
}
else
{
uint8_t v___x_3122_; 
v___x_3122_ = 0;
return v___x_3122_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15___boxed(lean_object* v_e_3123_){
_start:
{
uint8_t v_res_3124_; lean_object* v_r_3125_; 
v_res_3124_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_e_3123_);
lean_dec_ref(v_e_3123_);
v_r_3125_ = lean_box(v_res_3124_);
return v_r_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(lean_object* v_opts_3126_, lean_object* v_opt_3127_){
_start:
{
lean_object* v_name_3128_; lean_object* v_defValue_3129_; lean_object* v_map_3130_; lean_object* v___x_3131_; 
v_name_3128_ = lean_ctor_get(v_opt_3127_, 0);
v_defValue_3129_ = lean_ctor_get(v_opt_3127_, 1);
v_map_3130_ = lean_ctor_get(v_opts_3126_, 0);
v___x_3131_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_3130_, v_name_3128_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_inc(v_defValue_3129_);
return v_defValue_3129_;
}
else
{
lean_object* v_val_3132_; 
v_val_3132_ = lean_ctor_get(v___x_3131_, 0);
lean_inc(v_val_3132_);
lean_dec_ref_known(v___x_3131_, 1);
if (lean_obj_tag(v_val_3132_) == 3)
{
lean_object* v_v_3133_; 
v_v_3133_ = lean_ctor_get(v_val_3132_, 0);
lean_inc(v_v_3133_);
lean_dec_ref_known(v_val_3132_, 1);
return v_v_3133_;
}
else
{
lean_dec(v_val_3132_);
lean_inc(v_defValue_3129_);
return v_defValue_3129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16___boxed(lean_object* v_opts_3134_, lean_object* v_opt_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3134_, v_opt_3135_);
lean_dec_ref(v_opt_3135_);
lean_dec_ref(v_opts_3134_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(size_t v_sz_3137_, size_t v_i_3138_, lean_object* v_bs_3139_){
_start:
{
uint8_t v___x_3140_; 
v___x_3140_ = lean_usize_dec_lt(v_i_3138_, v_sz_3137_);
if (v___x_3140_ == 0)
{
return v_bs_3139_;
}
else
{
lean_object* v_v_3141_; lean_object* v_msg_3142_; lean_object* v___x_3143_; lean_object* v_bs_x27_3144_; size_t v___x_3145_; size_t v___x_3146_; lean_object* v___x_3147_; 
v_v_3141_ = lean_array_uget_borrowed(v_bs_3139_, v_i_3138_);
v_msg_3142_ = lean_ctor_get(v_v_3141_, 1);
lean_inc_ref(v_msg_3142_);
v___x_3143_ = lean_unsigned_to_nat(0u);
v_bs_x27_3144_ = lean_array_uset(v_bs_3139_, v_i_3138_, v___x_3143_);
v___x_3145_ = ((size_t)1ULL);
v___x_3146_ = lean_usize_add(v_i_3138_, v___x_3145_);
v___x_3147_ = lean_array_uset(v_bs_x27_3144_, v_i_3138_, v_msg_3142_);
v_i_3138_ = v___x_3146_;
v_bs_3139_ = v___x_3147_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15___boxed(lean_object* v_sz_3149_, lean_object* v_i_3150_, lean_object* v_bs_3151_){
_start:
{
size_t v_sz_boxed_3152_; size_t v_i_boxed_3153_; lean_object* v_res_3154_; 
v_sz_boxed_3152_ = lean_unbox_usize(v_sz_3149_);
lean_dec(v_sz_3149_);
v_i_boxed_3153_ = lean_unbox_usize(v_i_3150_);
lean_dec(v_i_3150_);
v_res_3154_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_boxed_3152_, v_i_boxed_3153_, v_bs_3151_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(lean_object* v_oldTraces_3155_, lean_object* v_data_3156_, lean_object* v_ref_3157_, lean_object* v_msg_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_toCold_3164_; lean_object* v_options_3165_; lean_object* v_currRecDepth_3166_; lean_object* v_maxRecDepth_3167_; lean_object* v_ref_3168_; lean_object* v_currNamespace_3169_; lean_object* v_openDecls_3170_; lean_object* v_initHeartbeats_3171_; lean_object* v_maxHeartbeats_3172_; lean_object* v_currMacroScope_3173_; uint8_t v_diag_3174_; uint8_t v_suppressElabErrors_3175_; lean_object* v___x_3176_; lean_object* v_traceState_3177_; lean_object* v_traces_3178_; lean_object* v_ref_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; size_t v_sz_3182_; size_t v___x_3183_; lean_object* v___x_3184_; lean_object* v_msg_3185_; lean_object* v___x_3186_; lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3224_; 
v_toCold_3164_ = lean_ctor_get(v___y_3161_, 0);
v_options_3165_ = lean_ctor_get(v___y_3161_, 1);
v_currRecDepth_3166_ = lean_ctor_get(v___y_3161_, 2);
v_maxRecDepth_3167_ = lean_ctor_get(v___y_3161_, 3);
v_ref_3168_ = lean_ctor_get(v___y_3161_, 4);
v_currNamespace_3169_ = lean_ctor_get(v___y_3161_, 5);
v_openDecls_3170_ = lean_ctor_get(v___y_3161_, 6);
v_initHeartbeats_3171_ = lean_ctor_get(v___y_3161_, 7);
v_maxHeartbeats_3172_ = lean_ctor_get(v___y_3161_, 8);
v_currMacroScope_3173_ = lean_ctor_get(v___y_3161_, 9);
v_diag_3174_ = lean_ctor_get_uint8(v___y_3161_, sizeof(void*)*10);
v_suppressElabErrors_3175_ = lean_ctor_get_uint8(v___y_3161_, sizeof(void*)*10 + 1);
v___x_3176_ = lean_st_ref_get(v___y_3162_);
v_traceState_3177_ = lean_ctor_get(v___x_3176_, 4);
lean_inc_ref(v_traceState_3177_);
lean_dec(v___x_3176_);
v_traces_3178_ = lean_ctor_get(v_traceState_3177_, 0);
lean_inc_ref(v_traces_3178_);
lean_dec_ref(v_traceState_3177_);
v_ref_3179_ = l_Lean_replaceRef(v_ref_3157_, v_ref_3168_);
lean_inc(v_currMacroScope_3173_);
lean_inc(v_maxHeartbeats_3172_);
lean_inc(v_initHeartbeats_3171_);
lean_inc(v_openDecls_3170_);
lean_inc(v_currNamespace_3169_);
lean_inc(v_maxRecDepth_3167_);
lean_inc(v_currRecDepth_3166_);
lean_inc_ref(v_options_3165_);
lean_inc_ref(v_toCold_3164_);
v___x_3180_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_3180_, 0, v_toCold_3164_);
lean_ctor_set(v___x_3180_, 1, v_options_3165_);
lean_ctor_set(v___x_3180_, 2, v_currRecDepth_3166_);
lean_ctor_set(v___x_3180_, 3, v_maxRecDepth_3167_);
lean_ctor_set(v___x_3180_, 4, v_ref_3179_);
lean_ctor_set(v___x_3180_, 5, v_currNamespace_3169_);
lean_ctor_set(v___x_3180_, 6, v_openDecls_3170_);
lean_ctor_set(v___x_3180_, 7, v_initHeartbeats_3171_);
lean_ctor_set(v___x_3180_, 8, v_maxHeartbeats_3172_);
lean_ctor_set(v___x_3180_, 9, v_currMacroScope_3173_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*10, v_diag_3174_);
lean_ctor_set_uint8(v___x_3180_, sizeof(void*)*10 + 1, v_suppressElabErrors_3175_);
v___x_3181_ = l_Lean_PersistentArray_toArray___redArg(v_traces_3178_);
lean_dec_ref(v_traces_3178_);
v_sz_3182_ = lean_array_size(v___x_3181_);
v___x_3183_ = ((size_t)0ULL);
v___x_3184_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_3182_, v___x_3183_, v___x_3181_);
v_msg_3185_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_3185_, 0, v_data_3156_);
lean_ctor_set(v_msg_3185_, 1, v_msg_3158_);
lean_ctor_set(v_msg_3185_, 2, v___x_3184_);
v___x_3186_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_3185_, v___y_3159_, v___y_3160_, v___x_3180_, v___y_3162_);
lean_dec_ref_known(v___x_3180_, 10);
v_a_3187_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3189_ = v___x_3186_;
v_isShared_3190_ = v_isSharedCheck_3224_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3186_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3224_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v_traceState_3192_; lean_object* v_env_3193_; lean_object* v_nextMacroScope_3194_; lean_object* v_ngen_3195_; lean_object* v_auxDeclNGen_3196_; lean_object* v_cache_3197_; lean_object* v_messages_3198_; lean_object* v_infoState_3199_; lean_object* v_snapshotTasks_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3223_; 
v___x_3191_ = lean_st_ref_take(v___y_3162_);
v_traceState_3192_ = lean_ctor_get(v___x_3191_, 4);
v_env_3193_ = lean_ctor_get(v___x_3191_, 0);
v_nextMacroScope_3194_ = lean_ctor_get(v___x_3191_, 1);
v_ngen_3195_ = lean_ctor_get(v___x_3191_, 2);
v_auxDeclNGen_3196_ = lean_ctor_get(v___x_3191_, 3);
v_cache_3197_ = lean_ctor_get(v___x_3191_, 5);
v_messages_3198_ = lean_ctor_get(v___x_3191_, 6);
v_infoState_3199_ = lean_ctor_get(v___x_3191_, 7);
v_snapshotTasks_3200_ = lean_ctor_get(v___x_3191_, 8);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3202_ = v___x_3191_;
v_isShared_3203_ = v_isSharedCheck_3223_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snapshotTasks_3200_);
lean_inc(v_infoState_3199_);
lean_inc(v_messages_3198_);
lean_inc(v_cache_3197_);
lean_inc(v_traceState_3192_);
lean_inc(v_auxDeclNGen_3196_);
lean_inc(v_ngen_3195_);
lean_inc(v_nextMacroScope_3194_);
lean_inc(v_env_3193_);
lean_dec(v___x_3191_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3223_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
uint64_t v_tid_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3221_; 
v_tid_3204_ = lean_ctor_get_uint64(v_traceState_3192_, sizeof(void*)*1);
v_isSharedCheck_3221_ = !lean_is_exclusive(v_traceState_3192_);
if (v_isSharedCheck_3221_ == 0)
{
lean_object* v_unused_3222_; 
v_unused_3222_ = lean_ctor_get(v_traceState_3192_, 0);
lean_dec(v_unused_3222_);
v___x_3206_ = v_traceState_3192_;
v_isShared_3207_ = v_isSharedCheck_3221_;
goto v_resetjp_3205_;
}
else
{
lean_dec(v_traceState_3192_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3221_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3211_; 
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v_ref_3157_);
lean_ctor_set(v___x_3208_, 1, v_a_3187_);
v___x_3209_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_3155_, v___x_3208_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3209_);
v___x_3211_ = v___x_3206_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v___x_3209_);
lean_ctor_set_uint64(v_reuseFailAlloc_3220_, sizeof(void*)*1, v_tid_3204_);
v___x_3211_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
lean_object* v___x_3213_; 
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 4, v___x_3211_);
v___x_3213_ = v___x_3202_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3219_; 
v_reuseFailAlloc_3219_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3219_, 0, v_env_3193_);
lean_ctor_set(v_reuseFailAlloc_3219_, 1, v_nextMacroScope_3194_);
lean_ctor_set(v_reuseFailAlloc_3219_, 2, v_ngen_3195_);
lean_ctor_set(v_reuseFailAlloc_3219_, 3, v_auxDeclNGen_3196_);
lean_ctor_set(v_reuseFailAlloc_3219_, 4, v___x_3211_);
lean_ctor_set(v_reuseFailAlloc_3219_, 5, v_cache_3197_);
lean_ctor_set(v_reuseFailAlloc_3219_, 6, v_messages_3198_);
lean_ctor_set(v_reuseFailAlloc_3219_, 7, v_infoState_3199_);
lean_ctor_set(v_reuseFailAlloc_3219_, 8, v_snapshotTasks_3200_);
v___x_3213_ = v_reuseFailAlloc_3219_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3217_; 
v___x_3214_ = lean_st_ref_put(v___y_3162_, v___x_3213_);
v___x_3215_ = lean_box(0);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3215_);
v___x_3217_ = v___x_3189_;
goto v_reusejp_3216_;
}
else
{
lean_object* v_reuseFailAlloc_3218_; 
v_reuseFailAlloc_3218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3218_, 0, v___x_3215_);
v___x_3217_ = v_reuseFailAlloc_3218_;
goto v_reusejp_3216_;
}
v_reusejp_3216_:
{
return v___x_3217_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg___boxed(lean_object* v_oldTraces_3225_, lean_object* v_data_3226_, lean_object* v_ref_3227_, lean_object* v_msg_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_){
_start:
{
lean_object* v_res_3234_; 
v_res_3234_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3225_, v_data_3226_, v_ref_3227_, v_msg_3228_, v___y_3229_, v___y_3230_, v___y_3231_, v___y_3232_);
lean_dec(v___y_3232_);
lean_dec_ref(v___y_3231_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
return v_res_3234_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1(void){
_start:
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__0));
v___x_3237_ = l_Lean_stringToMessageData(v___x_3236_);
return v___x_3237_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2(void){
_start:
{
lean_object* v___x_3238_; double v___x_3239_; 
v___x_3238_ = lean_unsigned_to_nat(1000u);
v___x_3239_ = lean_float_of_nat(v___x_3238_);
return v___x_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(lean_object* v_cls_3240_, uint8_t v_collapsed_3241_, lean_object* v_tag_3242_, lean_object* v_opts_3243_, uint8_t v_clsEnabled_3244_, lean_object* v_oldTraces_3245_, lean_object* v_msg_3246_, lean_object* v_resStartStop_3247_, lean_object* v___y_3248_, lean_object* v___y_3249_, lean_object* v___y_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_fst_3255_; lean_object* v_snd_3256_; lean_object* v___y_3258_; lean_object* v___y_3259_; lean_object* v_data_3260_; lean_object* v_fst_3271_; lean_object* v_snd_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; lean_object* v___y_3276_; lean_object* v_a_3277_; uint8_t v___y_3292_; double v___y_3323_; 
v_fst_3255_ = lean_ctor_get(v_resStartStop_3247_, 0);
lean_inc(v_fst_3255_);
v_snd_3256_ = lean_ctor_get(v_resStartStop_3247_, 1);
lean_inc(v_snd_3256_);
lean_dec_ref(v_resStartStop_3247_);
v_fst_3271_ = lean_ctor_get(v_snd_3256_, 0);
lean_inc(v_fst_3271_);
v_snd_3272_ = lean_ctor_get(v_snd_3256_, 1);
lean_inc(v_snd_3272_);
lean_dec(v_snd_3256_);
v___x_3273_ = l_Lean_trace_profiler;
v___x_3274_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3243_, v___x_3273_);
if (v___x_3274_ == 0)
{
v___y_3292_ = v___x_3274_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3328_; uint8_t v___x_3329_; 
v___x_3328_ = l_Lean_trace_profiler_useHeartbeats;
v___x_3329_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_3243_, v___x_3328_);
if (v___x_3329_ == 0)
{
lean_object* v___x_3330_; lean_object* v___x_3331_; double v___x_3332_; double v___x_3333_; double v___x_3334_; 
v___x_3330_ = l_Lean_trace_profiler_threshold;
v___x_3331_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3243_, v___x_3330_);
v___x_3332_ = lean_float_of_nat(v___x_3331_);
v___x_3333_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_3334_ = lean_float_div(v___x_3332_, v___x_3333_);
v___y_3323_ = v___x_3334_;
goto v___jp_3322_;
}
else
{
lean_object* v___x_3335_; lean_object* v___x_3336_; double v___x_3337_; 
v___x_3335_ = l_Lean_trace_profiler_threshold;
v___x_3336_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_3243_, v___x_3335_);
v___x_3337_ = lean_float_of_nat(v___x_3336_);
v___y_3323_ = v___x_3337_;
goto v___jp_3322_;
}
}
v___jp_3257_:
{
lean_object* v___x_3261_; 
lean_inc(v___y_3259_);
v___x_3261_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_3245_, v_data_3260_, v___y_3259_, v___y_3258_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_object* v___x_3262_; 
lean_dec_ref_known(v___x_3261_, 1);
v___x_3262_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3255_);
return v___x_3262_;
}
else
{
lean_object* v_a_3263_; lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3270_; 
lean_dec(v_fst_3255_);
v_a_3263_ = lean_ctor_get(v___x_3261_, 0);
v_isSharedCheck_3270_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3270_ == 0)
{
v___x_3265_ = v___x_3261_;
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
else
{
lean_inc(v_a_3263_);
lean_dec(v___x_3261_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3270_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v___x_3268_; 
if (v_isShared_3266_ == 0)
{
v___x_3268_ = v___x_3265_;
goto v_reusejp_3267_;
}
else
{
lean_object* v_reuseFailAlloc_3269_; 
v_reuseFailAlloc_3269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3269_, 0, v_a_3263_);
v___x_3268_ = v_reuseFailAlloc_3269_;
goto v_reusejp_3267_;
}
v_reusejp_3267_:
{
return v___x_3268_;
}
}
}
}
v___jp_3275_:
{
uint8_t v_result_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; double v___x_3281_; lean_object* v_data_3282_; 
v_result_3278_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__15(v_fst_3255_);
v___x_3279_ = lean_box(v_result_3278_);
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
v___x_3281_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_3242_);
lean_inc_ref(v___x_3280_);
lean_inc(v_cls_3240_);
v_data_3282_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3282_, 0, v_cls_3240_);
lean_ctor_set(v_data_3282_, 1, v___x_3280_);
lean_ctor_set(v_data_3282_, 2, v_tag_3242_);
lean_ctor_set_float(v_data_3282_, sizeof(void*)*3, v___x_3281_);
lean_ctor_set_float(v_data_3282_, sizeof(void*)*3 + 8, v___x_3281_);
lean_ctor_set_uint8(v_data_3282_, sizeof(void*)*3 + 16, v_collapsed_3241_);
if (v___x_3274_ == 0)
{
lean_dec_ref_known(v___x_3280_, 1);
lean_dec(v_snd_3272_);
lean_dec(v_fst_3271_);
lean_dec_ref(v_tag_3242_);
lean_dec(v_cls_3240_);
v___y_3258_ = v_a_3277_;
v___y_3259_ = v___y_3276_;
v_data_3260_ = v_data_3282_;
goto v___jp_3257_;
}
else
{
lean_object* v_data_3283_; double v___x_3284_; double v___x_3285_; 
lean_dec_ref_known(v_data_3282_, 3);
v_data_3283_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_3283_, 0, v_cls_3240_);
lean_ctor_set(v_data_3283_, 1, v___x_3280_);
lean_ctor_set(v_data_3283_, 2, v_tag_3242_);
v___x_3284_ = lean_unbox_float(v_fst_3271_);
lean_dec(v_fst_3271_);
lean_ctor_set_float(v_data_3283_, sizeof(void*)*3, v___x_3284_);
v___x_3285_ = lean_unbox_float(v_snd_3272_);
lean_dec(v_snd_3272_);
lean_ctor_set_float(v_data_3283_, sizeof(void*)*3 + 8, v___x_3285_);
lean_ctor_set_uint8(v_data_3283_, sizeof(void*)*3 + 16, v_collapsed_3241_);
v___y_3258_ = v_a_3277_;
v___y_3259_ = v___y_3276_;
v_data_3260_ = v_data_3283_;
goto v___jp_3257_;
}
}
v___jp_3286_:
{
lean_object* v_ref_3287_; lean_object* v___x_3288_; 
v_ref_3287_ = lean_ctor_get(v___y_3252_, 4);
lean_inc(v___y_3253_);
lean_inc_ref(v___y_3252_);
lean_inc(v___y_3251_);
lean_inc_ref(v___y_3250_);
lean_inc(v___y_3249_);
lean_inc(v___y_3248_);
lean_inc(v_fst_3255_);
v___x_3288_ = lean_apply_8(v_msg_3246_, v_fst_3255_, v___y_3248_, v___y_3249_, v___y_3250_, v___y_3251_, v___y_3252_, v___y_3253_, lean_box(0));
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v_a_3289_; 
v_a_3289_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_a_3289_);
lean_dec_ref_known(v___x_3288_, 1);
v___y_3276_ = v_ref_3287_;
v_a_3277_ = v_a_3289_;
goto v___jp_3275_;
}
else
{
lean_object* v___x_3290_; 
lean_dec_ref_known(v___x_3288_, 1);
v___x_3290_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_3276_ = v_ref_3287_;
v_a_3277_ = v___x_3290_;
goto v___jp_3275_;
}
}
v___jp_3291_:
{
if (v_clsEnabled_3244_ == 0)
{
if (v___y_3292_ == 0)
{
lean_object* v___x_3293_; lean_object* v_traceState_3294_; lean_object* v_env_3295_; lean_object* v_nextMacroScope_3296_; lean_object* v_ngen_3297_; lean_object* v_auxDeclNGen_3298_; lean_object* v_cache_3299_; lean_object* v_messages_3300_; lean_object* v_infoState_3301_; lean_object* v_snapshotTasks_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3321_; 
lean_dec(v_snd_3272_);
lean_dec(v_fst_3271_);
lean_dec_ref(v_msg_3246_);
lean_dec_ref(v_tag_3242_);
lean_dec(v_cls_3240_);
v___x_3293_ = lean_st_ref_take(v___y_3253_);
v_traceState_3294_ = lean_ctor_get(v___x_3293_, 4);
v_env_3295_ = lean_ctor_get(v___x_3293_, 0);
v_nextMacroScope_3296_ = lean_ctor_get(v___x_3293_, 1);
v_ngen_3297_ = lean_ctor_get(v___x_3293_, 2);
v_auxDeclNGen_3298_ = lean_ctor_get(v___x_3293_, 3);
v_cache_3299_ = lean_ctor_get(v___x_3293_, 5);
v_messages_3300_ = lean_ctor_get(v___x_3293_, 6);
v_infoState_3301_ = lean_ctor_get(v___x_3293_, 7);
v_snapshotTasks_3302_ = lean_ctor_get(v___x_3293_, 8);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3304_ = v___x_3293_;
v_isShared_3305_ = v_isSharedCheck_3321_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_snapshotTasks_3302_);
lean_inc(v_infoState_3301_);
lean_inc(v_messages_3300_);
lean_inc(v_cache_3299_);
lean_inc(v_traceState_3294_);
lean_inc(v_auxDeclNGen_3298_);
lean_inc(v_ngen_3297_);
lean_inc(v_nextMacroScope_3296_);
lean_inc(v_env_3295_);
lean_dec(v___x_3293_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3321_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
uint64_t v_tid_3306_; lean_object* v_traces_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3320_; 
v_tid_3306_ = lean_ctor_get_uint64(v_traceState_3294_, sizeof(void*)*1);
v_traces_3307_ = lean_ctor_get(v_traceState_3294_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_traceState_3294_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3309_ = v_traceState_3294_;
v_isShared_3310_ = v_isSharedCheck_3320_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_traces_3307_);
lean_dec(v_traceState_3294_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3320_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3313_; 
v___x_3311_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_3245_, v_traces_3307_);
lean_dec_ref(v_traces_3307_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 0, v___x_3311_);
v___x_3313_ = v___x_3309_;
goto v_reusejp_3312_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3311_);
lean_ctor_set_uint64(v_reuseFailAlloc_3319_, sizeof(void*)*1, v_tid_3306_);
v___x_3313_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3312_;
}
v_reusejp_3312_:
{
lean_object* v___x_3315_; 
if (v_isShared_3305_ == 0)
{
lean_ctor_set(v___x_3304_, 4, v___x_3313_);
v___x_3315_ = v___x_3304_;
goto v_reusejp_3314_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_env_3295_);
lean_ctor_set(v_reuseFailAlloc_3318_, 1, v_nextMacroScope_3296_);
lean_ctor_set(v_reuseFailAlloc_3318_, 2, v_ngen_3297_);
lean_ctor_set(v_reuseFailAlloc_3318_, 3, v_auxDeclNGen_3298_);
lean_ctor_set(v_reuseFailAlloc_3318_, 4, v___x_3313_);
lean_ctor_set(v_reuseFailAlloc_3318_, 5, v_cache_3299_);
lean_ctor_set(v_reuseFailAlloc_3318_, 6, v_messages_3300_);
lean_ctor_set(v_reuseFailAlloc_3318_, 7, v_infoState_3301_);
lean_ctor_set(v_reuseFailAlloc_3318_, 8, v_snapshotTasks_3302_);
v___x_3315_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3314_;
}
v_reusejp_3314_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = lean_st_ref_put(v___y_3253_, v___x_3315_);
v___x_3317_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_fst_3255_);
return v___x_3317_;
}
}
}
}
}
else
{
goto v___jp_3286_;
}
}
else
{
goto v___jp_3286_;
}
}
v___jp_3322_:
{
double v___x_3324_; double v___x_3325_; double v___x_3326_; uint8_t v___x_3327_; 
v___x_3324_ = lean_unbox_float(v_snd_3272_);
v___x_3325_ = lean_unbox_float(v_fst_3271_);
v___x_3326_ = lean_float_sub(v___x_3324_, v___x_3325_);
v___x_3327_ = lean_float_decLt(v___y_3323_, v___x_3326_);
v___y_3292_ = v___x_3327_;
goto v___jp_3291_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___boxed(lean_object* v_cls_3338_, lean_object* v_collapsed_3339_, lean_object* v_tag_3340_, lean_object* v_opts_3341_, lean_object* v_clsEnabled_3342_, lean_object* v_oldTraces_3343_, lean_object* v_msg_3344_, lean_object* v_resStartStop_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_){
_start:
{
uint8_t v_collapsed_boxed_3353_; uint8_t v_clsEnabled_boxed_3354_; lean_object* v_res_3355_; 
v_collapsed_boxed_3353_ = lean_unbox(v_collapsed_3339_);
v_clsEnabled_boxed_3354_ = lean_unbox(v_clsEnabled_3342_);
v_res_3355_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v_cls_3338_, v_collapsed_boxed_3353_, v_tag_3340_, v_opts_3341_, v_clsEnabled_boxed_3354_, v_oldTraces_3343_, v_msg_3344_, v_resStartStop_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
lean_dec(v___y_3351_);
lean_dec_ref(v___y_3350_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v_opts_3341_);
return v_res_3355_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v___x_3356_ = lean_unsigned_to_nat(32u);
v___x_3357_ = lean_mk_empty_array_with_capacity(v___x_3356_);
v___x_3358_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3358_, 0, v___x_3357_);
return v___x_3358_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1(void){
_start:
{
size_t v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3359_ = ((size_t)5ULL);
v___x_3360_ = lean_unsigned_to_nat(0u);
v___x_3361_ = lean_unsigned_to_nat(32u);
v___x_3362_ = lean_mk_empty_array_with_capacity(v___x_3361_);
v___x_3363_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__0);
v___x_3364_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v___x_3362_);
lean_ctor_set(v___x_3364_, 2, v___x_3360_);
lean_ctor_set(v___x_3364_, 3, v___x_3360_);
lean_ctor_set_usize(v___x_3364_, 4, v___x_3359_);
return v___x_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(lean_object* v___y_3365_){
_start:
{
lean_object* v___x_3367_; lean_object* v_traceState_3368_; lean_object* v_traces_3369_; lean_object* v___x_3370_; lean_object* v_traceState_3371_; lean_object* v_env_3372_; lean_object* v_nextMacroScope_3373_; lean_object* v_ngen_3374_; lean_object* v_auxDeclNGen_3375_; lean_object* v_cache_3376_; lean_object* v_messages_3377_; lean_object* v_infoState_3378_; lean_object* v_snapshotTasks_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3398_; 
v___x_3367_ = lean_st_ref_get(v___y_3365_);
v_traceState_3368_ = lean_ctor_get(v___x_3367_, 4);
lean_inc_ref(v_traceState_3368_);
lean_dec(v___x_3367_);
v_traces_3369_ = lean_ctor_get(v_traceState_3368_, 0);
lean_inc_ref(v_traces_3369_);
lean_dec_ref(v_traceState_3368_);
v___x_3370_ = lean_st_ref_take(v___y_3365_);
v_traceState_3371_ = lean_ctor_get(v___x_3370_, 4);
v_env_3372_ = lean_ctor_get(v___x_3370_, 0);
v_nextMacroScope_3373_ = lean_ctor_get(v___x_3370_, 1);
v_ngen_3374_ = lean_ctor_get(v___x_3370_, 2);
v_auxDeclNGen_3375_ = lean_ctor_get(v___x_3370_, 3);
v_cache_3376_ = lean_ctor_get(v___x_3370_, 5);
v_messages_3377_ = lean_ctor_get(v___x_3370_, 6);
v_infoState_3378_ = lean_ctor_get(v___x_3370_, 7);
v_snapshotTasks_3379_ = lean_ctor_get(v___x_3370_, 8);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3370_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3381_ = v___x_3370_;
v_isShared_3382_ = v_isSharedCheck_3398_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_snapshotTasks_3379_);
lean_inc(v_infoState_3378_);
lean_inc(v_messages_3377_);
lean_inc(v_cache_3376_);
lean_inc(v_traceState_3371_);
lean_inc(v_auxDeclNGen_3375_);
lean_inc(v_ngen_3374_);
lean_inc(v_nextMacroScope_3373_);
lean_inc(v_env_3372_);
lean_dec(v___x_3370_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3398_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
uint64_t v_tid_3383_; lean_object* v___x_3385_; uint8_t v_isShared_3386_; uint8_t v_isSharedCheck_3396_; 
v_tid_3383_ = lean_ctor_get_uint64(v_traceState_3371_, sizeof(void*)*1);
v_isSharedCheck_3396_ = !lean_is_exclusive(v_traceState_3371_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v_traceState_3371_, 0);
lean_dec(v_unused_3397_);
v___x_3385_ = v_traceState_3371_;
v_isShared_3386_ = v_isSharedCheck_3396_;
goto v_resetjp_3384_;
}
else
{
lean_dec(v_traceState_3371_);
v___x_3385_ = lean_box(0);
v_isShared_3386_ = v_isSharedCheck_3396_;
goto v_resetjp_3384_;
}
v_resetjp_3384_:
{
lean_object* v___x_3387_; lean_object* v___x_3389_; 
v___x_3387_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_3386_ == 0)
{
lean_ctor_set(v___x_3385_, 0, v___x_3387_);
v___x_3389_ = v___x_3385_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3387_);
lean_ctor_set_uint64(v_reuseFailAlloc_3395_, sizeof(void*)*1, v_tid_3383_);
v___x_3389_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3391_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set(v___x_3381_, 4, v___x_3389_);
v___x_3391_ = v___x_3381_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v_env_3372_);
lean_ctor_set(v_reuseFailAlloc_3394_, 1, v_nextMacroScope_3373_);
lean_ctor_set(v_reuseFailAlloc_3394_, 2, v_ngen_3374_);
lean_ctor_set(v_reuseFailAlloc_3394_, 3, v_auxDeclNGen_3375_);
lean_ctor_set(v_reuseFailAlloc_3394_, 4, v___x_3389_);
lean_ctor_set(v_reuseFailAlloc_3394_, 5, v_cache_3376_);
lean_ctor_set(v_reuseFailAlloc_3394_, 6, v_messages_3377_);
lean_ctor_set(v_reuseFailAlloc_3394_, 7, v_infoState_3378_);
lean_ctor_set(v_reuseFailAlloc_3394_, 8, v_snapshotTasks_3379_);
v___x_3391_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = lean_st_ref_put(v___y_3365_, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3393_, 0, v_traces_3369_);
return v___x_3393_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___boxed(lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_3399_);
lean_dec(v___y_3399_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(lean_object* v_x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
lean_inc(v___y_3404_);
lean_inc(v___y_3403_);
v___x_3410_ = lean_apply_7(v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_, lean_box(0));
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed(lean_object* v_x_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0(v_x_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3413_);
lean_dec(v___y_3412_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(lean_object* v_lctx_3420_, lean_object* v_localInsts_3421_, lean_object* v_x_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___f_3430_; lean_object* v___x_3431_; 
lean_inc(v___y_3424_);
lean_inc(v___y_3423_);
v___f_3430_ = lean_alloc_closure((void*)(l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___lam__0___boxed), 8, 3);
lean_closure_set(v___f_3430_, 0, v_x_3422_);
lean_closure_set(v___f_3430_, 1, v___y_3423_);
lean_closure_set(v___f_3430_, 2, v___y_3424_);
v___x_3431_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalContextImp(lean_box(0), v_lctx_3420_, v_localInsts_3421_, v___f_3430_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
if (lean_obj_tag(v___x_3431_) == 0)
{
return v___x_3431_;
}
else
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3432_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg___boxed(lean_object* v_lctx_3440_, lean_object* v_localInsts_3441_, lean_object* v_x_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_, lean_object* v___y_3445_, lean_object* v___y_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_){
_start:
{
lean_object* v_res_3450_; 
v_res_3450_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3440_, v_localInsts_3441_, v_x_3442_, v___y_3443_, v___y_3444_, v___y_3445_, v___y_3446_, v___y_3447_, v___y_3448_);
lean_dec(v___y_3448_);
lean_dec_ref(v___y_3447_);
lean_dec(v___y_3446_);
lean_dec_ref(v___y_3445_);
lean_dec(v___y_3444_);
lean_dec(v___y_3443_);
return v_res_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(lean_object* v___y_3451_){
_start:
{
lean_object* v___x_3453_; lean_object* v_ngen_3454_; lean_object* v_namePrefix_3455_; lean_object* v_idx_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3485_; 
v___x_3453_ = lean_st_ref_get(v___y_3451_);
v_ngen_3454_ = lean_ctor_get(v___x_3453_, 2);
lean_inc_ref(v_ngen_3454_);
lean_dec(v___x_3453_);
v_namePrefix_3455_ = lean_ctor_get(v_ngen_3454_, 0);
v_idx_3456_ = lean_ctor_get(v_ngen_3454_, 1);
v_isSharedCheck_3485_ = !lean_is_exclusive(v_ngen_3454_);
if (v_isSharedCheck_3485_ == 0)
{
v___x_3458_ = v_ngen_3454_;
v_isShared_3459_ = v_isSharedCheck_3485_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_idx_3456_);
lean_inc(v_namePrefix_3455_);
lean_dec(v_ngen_3454_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3485_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v_env_3461_; lean_object* v_nextMacroScope_3462_; lean_object* v_auxDeclNGen_3463_; lean_object* v_traceState_3464_; lean_object* v_cache_3465_; lean_object* v_messages_3466_; lean_object* v_infoState_3467_; lean_object* v_snapshotTasks_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3483_; 
v___x_3460_ = lean_st_ref_take(v___y_3451_);
v_env_3461_ = lean_ctor_get(v___x_3460_, 0);
v_nextMacroScope_3462_ = lean_ctor_get(v___x_3460_, 1);
v_auxDeclNGen_3463_ = lean_ctor_get(v___x_3460_, 3);
v_traceState_3464_ = lean_ctor_get(v___x_3460_, 4);
v_cache_3465_ = lean_ctor_get(v___x_3460_, 5);
v_messages_3466_ = lean_ctor_get(v___x_3460_, 6);
v_infoState_3467_ = lean_ctor_get(v___x_3460_, 7);
v_snapshotTasks_3468_ = lean_ctor_get(v___x_3460_, 8);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3483_ == 0)
{
lean_object* v_unused_3484_; 
v_unused_3484_ = lean_ctor_get(v___x_3460_, 2);
lean_dec(v_unused_3484_);
v___x_3470_ = v___x_3460_;
v_isShared_3471_ = v_isSharedCheck_3483_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_snapshotTasks_3468_);
lean_inc(v_infoState_3467_);
lean_inc(v_messages_3466_);
lean_inc(v_cache_3465_);
lean_inc(v_traceState_3464_);
lean_inc(v_auxDeclNGen_3463_);
lean_inc(v_nextMacroScope_3462_);
lean_inc(v_env_3461_);
lean_dec(v___x_3460_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3483_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v_r_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3476_; 
lean_inc(v_idx_3456_);
lean_inc(v_namePrefix_3455_);
v_r_3472_ = l_Lean_Name_num___override(v_namePrefix_3455_, v_idx_3456_);
v___x_3473_ = lean_unsigned_to_nat(1u);
v___x_3474_ = lean_nat_add(v_idx_3456_, v___x_3473_);
lean_dec(v_idx_3456_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 1, v___x_3474_);
v___x_3476_ = v___x_3458_;
goto v_reusejp_3475_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_namePrefix_3455_);
lean_ctor_set(v_reuseFailAlloc_3482_, 1, v___x_3474_);
v___x_3476_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3475_;
}
v_reusejp_3475_:
{
lean_object* v___x_3478_; 
if (v_isShared_3471_ == 0)
{
lean_ctor_set(v___x_3470_, 2, v___x_3476_);
v___x_3478_ = v___x_3470_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_env_3461_);
lean_ctor_set(v_reuseFailAlloc_3481_, 1, v_nextMacroScope_3462_);
lean_ctor_set(v_reuseFailAlloc_3481_, 2, v___x_3476_);
lean_ctor_set(v_reuseFailAlloc_3481_, 3, v_auxDeclNGen_3463_);
lean_ctor_set(v_reuseFailAlloc_3481_, 4, v_traceState_3464_);
lean_ctor_set(v_reuseFailAlloc_3481_, 5, v_cache_3465_);
lean_ctor_set(v_reuseFailAlloc_3481_, 6, v_messages_3466_);
lean_ctor_set(v_reuseFailAlloc_3481_, 7, v_infoState_3467_);
lean_ctor_set(v_reuseFailAlloc_3481_, 8, v_snapshotTasks_3468_);
v___x_3478_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
lean_object* v___x_3479_; lean_object* v___x_3480_; 
v___x_3479_ = lean_st_ref_put(v___y_3451_, v___x_3478_);
v___x_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3480_, 0, v_r_3472_);
return v___x_3480_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg___boxed(lean_object* v___y_3486_, lean_object* v___y_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3486_);
lean_dec(v___y_3486_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(lean_object* v___y_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
lean_object* v___x_3496_; lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
v___x_3496_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_3494_);
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1___boxed(lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_res_3512_; 
v_res_3512_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_3505_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
lean_dec(v___y_3510_);
lean_dec_ref(v___y_3509_);
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3507_);
lean_dec(v___y_3506_);
lean_dec(v___y_3505_);
return v_res_3512_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3514_; lean_object* v___x_3515_; 
v___x_3514_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__0));
v___x_3515_ = l_Lean_stringToMessageData(v___x_3514_);
return v___x_3515_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3517_; lean_object* v___x_3518_; 
v___x_3517_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__2));
v___x_3518_ = l_Lean_stringToMessageData(v___x_3517_);
return v___x_3518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(lean_object* v_e_3521_, lean_object* v_x_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_, lean_object* v___y_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v___x_3530_; lean_object* v___y_3532_; uint8_t v___x_3541_; 
v___x_3530_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__1);
v___x_3541_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v___y_3523_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
v___x_3542_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__4));
v___y_3532_ = v___x_3542_;
goto v___jp_3531_;
}
else
{
lean_object* v___x_3543_; 
v___x_3543_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__5));
v___y_3532_ = v___x_3543_;
goto v___jp_3531_;
}
v___jp_3531_:
{
lean_object* v___x_3533_; lean_object* v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; lean_object* v___x_3540_; 
lean_inc_ref(v___y_3532_);
v___x_3533_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3533_, 0, v___y_3532_);
v___x_3534_ = l_Lean_MessageData_ofFormat(v___x_3533_);
v___x_3535_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3535_, 0, v___x_3530_);
lean_ctor_set(v___x_3535_, 1, v___x_3534_);
v___x_3536_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___closed__3);
v___x_3537_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3537_, 0, v___x_3535_);
lean_ctor_set(v___x_3537_, 1, v___x_3536_);
v___x_3538_ = l_Lean_indentExpr(v_e_3521_);
v___x_3539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3539_, 0, v___x_3537_);
lean_ctor_set(v___x_3539_, 1, v___x_3538_);
v___x_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3540_, 0, v___x_3539_);
return v___x_3540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed(lean_object* v_e_3544_, lean_object* v_x_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
lean_object* v_res_3553_; 
v_res_3553_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2(v_e_3544_, v_x_3545_, v___y_3546_, v___y_3547_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
lean_dec(v___y_3551_);
lean_dec_ref(v___y_3550_);
lean_dec(v___y_3549_);
lean_dec_ref(v___y_3548_);
lean_dec(v___y_3547_);
lean_dec(v___y_3546_);
lean_dec_ref(v_x_3545_);
return v_res_3553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(lean_object* v_lctx_3554_, lean_object* v_x_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_keyedConfig_3563_; uint8_t v_trackZetaDelta_3564_; lean_object* v_zetaDeltaSet_3565_; lean_object* v_localInstances_3566_; lean_object* v_defEqCtx_x3f_3567_; lean_object* v_synthPendingDepth_3568_; lean_object* v_customCanUnfoldPredicate_x3f_3569_; uint8_t v_univApprox_3570_; uint8_t v_inTypeClassResolution_3571_; uint8_t v_cacheInferType_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v_keyedConfig_3563_ = lean_ctor_get(v___y_3558_, 0);
v_trackZetaDelta_3564_ = lean_ctor_get_uint8(v___y_3558_, sizeof(void*)*7);
v_zetaDeltaSet_3565_ = lean_ctor_get(v___y_3558_, 1);
v_localInstances_3566_ = lean_ctor_get(v___y_3558_, 3);
v_defEqCtx_x3f_3567_ = lean_ctor_get(v___y_3558_, 4);
v_synthPendingDepth_3568_ = lean_ctor_get(v___y_3558_, 5);
v_customCanUnfoldPredicate_x3f_3569_ = lean_ctor_get(v___y_3558_, 6);
v_univApprox_3570_ = lean_ctor_get_uint8(v___y_3558_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3571_ = lean_ctor_get_uint8(v___y_3558_, sizeof(void*)*7 + 2);
v_cacheInferType_3572_ = lean_ctor_get_uint8(v___y_3558_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_3569_);
lean_inc(v_synthPendingDepth_3568_);
lean_inc(v_defEqCtx_x3f_3567_);
lean_inc_ref(v_localInstances_3566_);
lean_inc(v_zetaDeltaSet_3565_);
lean_inc_ref(v_keyedConfig_3563_);
v___x_3573_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3573_, 0, v_keyedConfig_3563_);
lean_ctor_set(v___x_3573_, 1, v_zetaDeltaSet_3565_);
lean_ctor_set(v___x_3573_, 2, v_lctx_3554_);
lean_ctor_set(v___x_3573_, 3, v_localInstances_3566_);
lean_ctor_set(v___x_3573_, 4, v_defEqCtx_x3f_3567_);
lean_ctor_set(v___x_3573_, 5, v_synthPendingDepth_3568_);
lean_ctor_set(v___x_3573_, 6, v_customCanUnfoldPredicate_x3f_3569_);
lean_ctor_set_uint8(v___x_3573_, sizeof(void*)*7, v_trackZetaDelta_3564_);
lean_ctor_set_uint8(v___x_3573_, sizeof(void*)*7 + 1, v_univApprox_3570_);
lean_ctor_set_uint8(v___x_3573_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3571_);
lean_ctor_set_uint8(v___x_3573_, sizeof(void*)*7 + 3, v_cacheInferType_3572_);
lean_inc(v___y_3561_);
lean_inc_ref(v___y_3560_);
lean_inc(v___y_3559_);
lean_inc(v___y_3557_);
lean_inc(v___y_3556_);
v___x_3574_ = lean_apply_7(v_x_3555_, v___y_3556_, v___y_3557_, v___x_3573_, v___y_3559_, v___y_3560_, v___y_3561_, lean_box(0));
if (lean_obj_tag(v___x_3574_) == 0)
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
v_a_3575_ = lean_ctor_get(v___x_3574_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3574_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3574_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3574_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
else
{
return v___x_3574_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg___boxed(lean_object* v_lctx_3583_, lean_object* v_x_3584_, lean_object* v___y_3585_, lean_object* v___y_3586_, lean_object* v___y_3587_, lean_object* v___y_3588_, lean_object* v___y_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_){
_start:
{
lean_object* v_res_3592_; 
v_res_3592_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_3583_, v_x_3584_, v___y_3585_, v___y_3586_, v___y_3587_, v___y_3588_, v___y_3589_, v___y_3590_);
lean_dec(v___y_3590_);
lean_dec_ref(v___y_3589_);
lean_dec(v___y_3588_);
lean_dec_ref(v___y_3587_);
lean_dec(v___y_3586_);
lean_dec(v___y_3585_);
return v_res_3592_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(lean_object* v_fvars_3595_, lean_object* v_letFVars_3596_, lean_object* v_lctx_3597_, lean_object* v_v_3598_, lean_object* v_e_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; 
v___x_3607_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3608_ = lean_expr_instantiate_rev(v_e_3599_, v_fvars_3595_);
v___x_3609_ = lean_apply_1(v_v_3598_, v___x_3608_);
v___x_3610_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_withLetFVars___boxed), 10, 3);
lean_closure_set(v___x_3610_, 0, lean_box(0));
lean_closure_set(v___x_3610_, 1, v_letFVars_3596_);
lean_closure_set(v___x_3610_, 2, v___x_3609_);
v___x_3611_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3597_, v___x_3607_, v___x_3610_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
return v___x_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___boxed(lean_object* v_fvars_3612_, lean_object* v_letFVars_3613_, lean_object* v_lctx_3614_, lean_object* v_v_3615_, lean_object* v_e_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_3612_, v_letFVars_3613_, v_lctx_3614_, v_v_3615_, v_e_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec(v___y_3618_);
lean_dec(v___y_3617_);
lean_dec_ref(v_e_3616_);
lean_dec_ref(v_fvars_3612_);
return v_res_3624_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__0));
v___x_3627_ = l_Lean_stringToMessageData(v___x_3626_);
return v___x_3627_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(lean_object* v_a_3628_, lean_object* v_a_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
lean_object* v___x_3637_; 
lean_inc_ref(v_a_3628_);
v___x_3637_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Result_type___redArg(v_a_3628_, v___y_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
if (lean_obj_tag(v___x_3637_) == 0)
{
lean_object* v_a_3638_; lean_object* v_expr_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3689_; 
v_a_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc(v_a_3638_);
lean_dec_ref_known(v___x_3637_, 1);
v_expr_3639_ = lean_ctor_get(v_a_3629_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3629_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_a_3629_, 1);
lean_dec(v_unused_3690_);
v___x_3641_ = v_a_3629_;
v_isShared_3642_ = v_isSharedCheck_3689_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_expr_3639_);
lean_dec(v_a_3629_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3689_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; 
lean_inc(v_a_3638_);
lean_inc_ref(v_expr_3639_);
v___x_3643_ = l_Lean_Meta_isExprDefEq(v_expr_3639_, v_a_3638_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
if (lean_obj_tag(v___x_3643_) == 0)
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3680_; 
v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3646_ = v___x_3643_;
v_isShared_3647_ = v_isSharedCheck_3680_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3643_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3680_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_unbox(v_a_3644_);
lean_dec(v_a_3644_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
lean_del_object(v___x_3646_);
v___x_3649_ = lean_box(0);
v___x_3650_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
v___x_3651_ = l_Lean_Meta_mkHasTypeButIsExpectedMsg___redArg(v_a_3638_, v_expr_3639_, v___x_3649_, v___x_3650_);
if (lean_obj_tag(v___x_3651_) == 0)
{
lean_object* v_a_3652_; lean_object* v_expr_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3666_; 
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc(v_a_3652_);
lean_dec_ref_known(v___x_3651_, 1);
v_expr_3653_ = lean_ctor_get(v_a_3628_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_a_3628_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; 
v_unused_3667_ = lean_ctor_get(v_a_3628_, 1);
lean_dec(v_unused_3667_);
v___x_3655_ = v_a_3628_;
v_isShared_3656_ = v_isSharedCheck_3666_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_expr_3653_);
lean_dec(v_a_3628_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3666_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3657_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___closed__1);
v___x_3658_ = l_Lean_indentExpr(v_expr_3653_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set_tag(v___x_3655_, 7);
lean_ctor_set(v___x_3655_, 1, v___x_3658_);
lean_ctor_set(v___x_3655_, 0, v___x_3657_);
v___x_3660_ = v___x_3655_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3657_);
lean_ctor_set(v_reuseFailAlloc_3665_, 1, v___x_3658_);
v___x_3660_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
lean_object* v___x_3662_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 7);
lean_ctor_set(v___x_3641_, 1, v_a_3652_);
lean_ctor_set(v___x_3641_, 0, v___x_3660_);
v___x_3662_ = v___x_3641_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_a_3652_);
v___x_3662_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3663_; 
v___x_3663_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_3662_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
return v___x_3663_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_del_object(v___x_3641_);
lean_dec_ref(v_a_3628_);
v_a_3668_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3651_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3651_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
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
lean_object* v___x_3676_; lean_object* v___x_3678_; 
lean_del_object(v___x_3641_);
lean_dec_ref(v_expr_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3628_);
v___x_3676_ = lean_box(0);
if (v_isShared_3647_ == 0)
{
lean_ctor_set(v___x_3646_, 0, v___x_3676_);
v___x_3678_ = v___x_3646_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
return v___x_3678_;
}
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3641_);
lean_dec_ref(v_expr_3639_);
lean_dec(v_a_3638_);
lean_dec_ref(v_a_3628_);
v_a_3681_ = lean_ctor_get(v___x_3643_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3643_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3643_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3643_);
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
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3698_; 
lean_dec_ref(v_a_3629_);
lean_dec_ref(v_a_3628_);
v_a_3691_ = lean_ctor_get(v___x_3637_, 0);
v_isSharedCheck_3698_ = !lean_is_exclusive(v___x_3637_);
if (v_isSharedCheck_3698_ == 0)
{
v___x_3693_ = v___x_3637_;
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3637_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3698_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___x_3696_; 
if (v_isShared_3694_ == 0)
{
v___x_3696_ = v___x_3693_;
goto v_reusejp_3695_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
v___x_3696_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3695_;
}
v_reusejp_3695_:
{
return v___x_3696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed(lean_object* v_a_3699_, lean_object* v_a_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
lean_object* v_res_3708_; 
v_res_3708_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1(v_a_3699_, v_a_3700_, v___y_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
lean_dec(v___y_3704_);
lean_dec_ref(v___y_3703_);
lean_dec(v___y_3702_);
lean_dec(v___y_3701_);
return v_res_3708_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3710_; lean_object* v___x_3711_; 
v___x_3710_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__0));
v___x_3711_ = l_Lean_stringToMessageData(v___x_3710_);
return v___x_3711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(lean_object* v_e_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_, lean_object* v_a_3717_, lean_object* v_a_3718_){
_start:
{
if (lean_obj_tag(v_e_3712_) == 5)
{
lean_object* v_fn_3720_; lean_object* v_arg_3721_; lean_object* v___x_3722_; 
v_fn_3720_ = lean_ctor_get(v_e_3712_, 0);
v_arg_3721_ = lean_ctor_get(v_e_3712_, 1);
lean_inc_ref(v_fn_3720_);
v___x_3722_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_fn_3720_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; lean_object* v___x_3724_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref_known(v___x_3722_, 1);
lean_inc_ref(v_arg_3721_);
v___x_3724_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3721_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3724_) == 0)
{
lean_object* v_a_3725_; lean_object* v___x_3727_; uint8_t v_isShared_3728_; uint8_t v_isSharedCheck_3747_; 
v_a_3725_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3727_ = v___x_3724_;
v_isShared_3728_ = v_isSharedCheck_3747_;
goto v_resetjp_3726_;
}
else
{
lean_inc(v_a_3725_);
lean_dec(v___x_3724_);
v___x_3727_ = lean_box(0);
v_isShared_3728_ = v_isSharedCheck_3747_;
goto v_resetjp_3726_;
}
v_resetjp_3726_:
{
lean_object* v_expr_3729_; size_t v___x_3730_; size_t v___x_3731_; uint8_t v___x_3732_; 
v_expr_3729_ = lean_ctor_get(v_a_3725_, 0);
lean_inc_ref(v_expr_3729_);
lean_dec(v_a_3725_);
v___x_3730_ = lean_ptr_addr(v_fn_3720_);
v___x_3731_ = lean_ptr_addr(v_a_3723_);
v___x_3732_ = lean_usize_dec_eq(v___x_3730_, v___x_3731_);
if (v___x_3732_ == 0)
{
lean_object* v___x_3733_; lean_object* v___x_3735_; 
lean_dec_ref_known(v_e_3712_, 2);
v___x_3733_ = l_Lean_Expr_app___override(v_a_3723_, v_expr_3729_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3733_);
v___x_3735_ = v___x_3727_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v___x_3733_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
else
{
size_t v___x_3737_; size_t v___x_3738_; uint8_t v___x_3739_; 
v___x_3737_ = lean_ptr_addr(v_arg_3721_);
v___x_3738_ = lean_ptr_addr(v_expr_3729_);
v___x_3739_ = lean_usize_dec_eq(v___x_3737_, v___x_3738_);
if (v___x_3739_ == 0)
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
lean_dec_ref_known(v_e_3712_, 2);
v___x_3740_ = l_Lean_Expr_app___override(v_a_3723_, v_expr_3729_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v___x_3740_);
v___x_3742_ = v___x_3727_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
else
{
lean_object* v___x_3745_; 
lean_dec_ref(v_expr_3729_);
lean_dec(v_a_3723_);
if (v_isShared_3728_ == 0)
{
lean_ctor_set(v___x_3727_, 0, v_e_3712_);
v___x_3745_ = v___x_3727_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_e_3712_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
lean_dec(v_a_3723_);
lean_dec_ref_known(v_e_3712_, 2);
v_a_3748_ = lean_ctor_get(v___x_3724_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3724_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3724_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3724_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_dec_ref_known(v_e_3712_, 2);
return v___x_3722_;
}
}
else
{
lean_object* v___x_3756_; 
v___x_3756_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3712_, v_a_3713_, v_a_3714_, v_a_3715_, v_a_3716_, v_a_3717_, v_a_3718_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3765_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3765_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_expr_3761_; lean_object* v___x_3763_; 
v_expr_3761_ = lean_ctor_get(v_a_3757_, 0);
lean_inc_ref(v_expr_3761_);
lean_dec(v_a_3757_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_expr_3761_);
v___x_3763_ = v___x_3759_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_expr_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
v_a_3766_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3756_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3756_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed(lean_object* v_e_3774_, lean_object* v_a_3775_, lean_object* v_a_3776_, lean_object* v_a_3777_, lean_object* v_a_3778_, lean_object* v_a_3779_, lean_object* v_a_3780_, lean_object* v_a_3781_){
_start:
{
lean_object* v_res_3782_; 
v_res_3782_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_);
lean_dec(v_a_3780_);
lean_dec_ref(v_a_3779_);
lean_dec(v_a_3778_);
lean_dec_ref(v_a_3777_);
lean_dec(v_a_3776_);
lean_dec(v_a_3775_);
return v_res_3782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(lean_object* v_e_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_, lean_object* v_a_3789_){
_start:
{
if (lean_obj_tag(v_e_3783_) == 5)
{
lean_object* v_fn_3791_; lean_object* v_arg_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; 
v_fn_3791_ = lean_ctor_get(v_e_3783_, 0);
v_arg_3792_ = lean_ctor_get(v_e_3783_, 1);
lean_inc_ref_n(v_fn_3791_, 2);
v___x_3793_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go___boxed), 8, 1);
lean_closure_set(v___x_3793_, 0, v_fn_3791_);
v___x_3794_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_fn_3791_, v___x_3793_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
if (lean_obj_tag(v___x_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3796_; 
v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
lean_inc(v_a_3795_);
lean_dec_ref_known(v___x_3794_, 1);
lean_inc_ref(v_arg_3792_);
v___x_3796_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_arg_3792_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitApp(v_e_3783_, v_a_3795_, v_a_3797_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
return v___x_3798_;
}
else
{
lean_dec(v_a_3795_);
lean_dec_ref_known(v_e_3783_, 2);
return v___x_3796_;
}
}
else
{
lean_dec_ref_known(v_e_3783_, 2);
return v___x_3794_;
}
}
else
{
lean_object* v___x_3799_; 
v___x_3799_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_, v_a_3788_, v_a_3789_);
return v___x_3799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(lean_object* v_e_3800_, lean_object* v_a_3801_, lean_object* v_a_3802_, lean_object* v_a_3803_, lean_object* v_a_3804_, lean_object* v_a_3805_, lean_object* v_a_3806_){
_start:
{
uint8_t v___x_3808_; 
v___x_3808_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_Context_check(v_a_3801_);
if (v___x_3808_ == 0)
{
lean_object* v___x_3809_; 
v___x_3809_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v___x_3812_; uint8_t v_isShared_3813_; uint8_t v_isSharedCheck_3819_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3812_ = v___x_3809_;
v_isShared_3813_ = v_isSharedCheck_3819_;
goto v_resetjp_3811_;
}
else
{
lean_inc(v_a_3810_);
lean_dec(v___x_3809_);
v___x_3812_ = lean_box(0);
v_isShared_3813_ = v_isSharedCheck_3819_;
goto v_resetjp_3811_;
}
v_resetjp_3811_:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3817_; 
v___x_3814_ = lean_box(0);
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v_a_3810_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
if (v_isShared_3813_ == 0)
{
lean_ctor_set(v___x_3812_, 0, v___x_3815_);
v___x_3817_ = v___x_3812_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3815_);
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
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
v_a_3820_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3809_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3809_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
else
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_Expr_getAppFn(v_e_3800_);
if (lean_obj_tag(v___x_3828_) == 2)
{
lean_object* v_mvarId_3829_; lean_object* v_dummy_3830_; lean_object* v_nargs_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v_mvarId_3829_ = lean_ctor_get(v___x_3828_, 0);
lean_inc(v_mvarId_3829_);
lean_dec_ref_known(v___x_3828_, 1);
v_dummy_3830_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj___closed__5);
v_nargs_3831_ = l_Lean_Expr_getAppNumArgs(v_e_3800_);
lean_inc(v_nargs_3831_);
v___x_3832_ = lean_mk_array(v_nargs_3831_, v_dummy_3830_);
v___x_3833_ = lean_unsigned_to_nat(1u);
v___x_3834_ = lean_nat_sub(v_nargs_3831_, v___x_3833_);
lean_dec(v_nargs_3831_);
lean_inc_ref(v_e_3800_);
v___x_3835_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_3800_, v___x_3832_, v___x_3834_);
v___x_3836_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkMVar(v_mvarId_3829_, v___x_3835_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
lean_dec(v_mvarId_3829_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v___x_3837_; 
lean_dec_ref_known(v___x_3836_, 1);
v___x_3837_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
return v___x_3837_;
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_dec_ref(v_e_3800_);
v_a_3838_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3836_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3836_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
else
{
lean_object* v___x_3846_; 
lean_dec_ref(v___x_3828_);
v___x_3846_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go(v_e_3800_, v_a_3801_, v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_, v_a_3806_);
return v___x_3846_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed(lean_object* v_e_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_, lean_object* v_a_3850_, lean_object* v_a_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs(v_e_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec(v_a_3851_);
lean_dec_ref(v_a_3850_);
lean_dec(v_a_3849_);
lean_dec(v_a_3848_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(lean_object* v_e_3856_, lean_object* v_a_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v___x_3864_; 
v___x_3864_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3856_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3866_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
lean_inc(v_a_3865_);
lean_dec_ref_known(v___x_3864_, 1);
v___x_3866_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_ensureType(v_a_3865_, v_a_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
return v___x_3866_;
}
else
{
return v___x_3864_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed(lean_object* v_e_3867_, lean_object* v_a_3868_, lean_object* v_a_3869_, lean_object* v_a_3870_, lean_object* v_a_3871_, lean_object* v_a_3872_, lean_object* v_a_3873_, lean_object* v_a_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType(v_e_3867_, v_a_3868_, v_a_3869_, v_a_3870_, v_a_3871_, v_a_3872_, v_a_3873_);
lean_dec(v_a_3873_);
lean_dec_ref(v_a_3872_);
lean_dec(v_a_3871_);
lean_dec_ref(v_a_3870_);
lean_dec(v_a_3869_);
lean_dec(v_a_3868_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(lean_object* v___x_3876_, lean_object* v_fvars_3877_, lean_object* v_doms_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v___x_3886_; 
v___x_3886_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___x_3876_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
if (lean_obj_tag(v___x_3886_) == 0)
{
lean_object* v_a_3887_; lean_object* v___x_3888_; 
v_a_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc(v_a_3887_);
lean_dec_ref_known(v___x_3886_, 1);
v___x_3888_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize(v_fvars_3877_, v_doms_3878_, v_a_3887_, v___y_3879_, v___y_3880_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_);
return v___x_3888_;
}
else
{
return v___x_3886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed(lean_object* v___x_3889_, lean_object* v_fvars_3890_, lean_object* v_doms_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0(v___x_3889_, v_fvars_3890_, v_doms_3891_, v___y_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
lean_dec(v___y_3893_);
lean_dec(v___y_3892_);
lean_dec_ref(v_doms_3891_);
lean_dec_ref(v_fvars_3890_);
return v_res_3899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(lean_object* v_lctx_3900_, lean_object* v_fvars_3901_, lean_object* v_doms_3902_, lean_object* v_e_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_, lean_object* v_a_3906_, lean_object* v_a_3907_, lean_object* v_a_3908_, lean_object* v_a_3909_){
_start:
{
lean_object* v___x_3911_; 
v___x_3911_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_findCacheNoBVars_x3f___redArg(v_e_3903_, v_a_3905_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
if (lean_obj_tag(v_a_3912_) == 1)
{
lean_object* v_val_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_dec_ref(v_e_3903_);
v_val_3913_ = lean_ctor_get(v_a_3912_, 0);
lean_inc(v_val_3913_);
lean_dec_ref_known(v_a_3912_, 1);
v___x_3914_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3915_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_finalize___boxed), 10, 3);
lean_closure_set(v___x_3915_, 0, v_fvars_3901_);
lean_closure_set(v___x_3915_, 1, v_doms_3902_);
lean_closure_set(v___x_3915_, 2, v_val_3913_);
v___x_3916_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3900_, v___x_3914_, v___x_3915_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
return v___x_3916_;
}
else
{
lean_dec(v_a_3912_);
if (lean_obj_tag(v_e_3903_) == 7)
{
lean_object* v_binderName_3917_; lean_object* v_binderType_3918_; lean_object* v_body_3919_; uint8_t v_binderInfo_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; 
v_binderName_3917_ = lean_ctor_get(v_e_3903_, 0);
lean_inc(v_binderName_3917_);
v_binderType_3918_ = lean_ctor_get(v_e_3903_, 1);
lean_inc_ref(v_binderType_3918_);
v_body_3919_ = lean_ctor_get(v_e_3903_, 2);
lean_inc_ref(v_body_3919_);
v_binderInfo_3920_ = lean_ctor_get_uint8(v_e_3903_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_3903_, 3);
v___x_3921_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3922_ = lean_expr_instantiate_rev(v_binderType_3918_, v_fvars_3901_);
lean_dec_ref(v_binderType_3918_);
v___x_3923_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 1);
lean_closure_set(v___x_3923_, 0, v___x_3922_);
lean_inc_ref(v_lctx_3900_);
v___x_3924_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3900_, v___x_3921_, v___x_3923_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_3924_) == 0)
{
lean_object* v_a_3925_; lean_object* v___x_3926_; 
v_a_3925_ = lean_ctor_get(v___x_3924_, 0);
lean_inc(v_a_3925_);
lean_dec_ref_known(v___x_3924_, 1);
v___x_3926_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
if (lean_obj_tag(v___x_3926_) == 0)
{
lean_object* v_a_3927_; lean_object* v_expr_3928_; uint8_t v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v_a_3927_ = lean_ctor_get(v___x_3926_, 0);
lean_inc_n(v_a_3927_, 2);
lean_dec_ref_known(v___x_3926_, 1);
v_expr_3928_ = lean_ctor_get(v_a_3925_, 0);
v___x_3929_ = 0;
lean_inc_ref(v_expr_3928_);
v___x_3930_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_3900_, v_a_3927_, v_binderName_3917_, v_expr_3928_, v_binderInfo_3920_, v___x_3929_);
v___x_3931_ = l_Lean_Expr_fvar___override(v_a_3927_);
v___x_3932_ = lean_array_push(v_fvars_3901_, v___x_3931_);
v___x_3933_ = lean_array_push(v_doms_3902_, v_a_3925_);
v_lctx_3900_ = v___x_3930_;
v_fvars_3901_ = v___x_3932_;
v_doms_3902_ = v___x_3933_;
v_e_3903_ = v_body_3919_;
goto _start;
}
else
{
lean_object* v_a_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3942_; 
lean_dec(v_a_3925_);
lean_dec_ref(v_body_3919_);
lean_dec(v_binderName_3917_);
lean_dec_ref(v_doms_3902_);
lean_dec_ref(v_fvars_3901_);
lean_dec_ref(v_lctx_3900_);
v_a_3935_ = lean_ctor_get(v___x_3926_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v___x_3926_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3937_ = v___x_3926_;
v_isShared_3938_ = v_isSharedCheck_3942_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_a_3935_);
lean_dec(v___x_3926_);
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
else
{
lean_dec_ref(v_body_3919_);
lean_dec(v_binderName_3917_);
lean_dec_ref(v_doms_3902_);
lean_dec_ref(v_fvars_3901_);
lean_dec_ref(v_lctx_3900_);
return v___x_3924_;
}
}
else
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___f_3945_; lean_object* v___x_3946_; 
v___x_3943_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0___closed__0));
v___x_3944_ = lean_expr_instantiate_rev(v_e_3903_, v_fvars_3901_);
lean_dec_ref(v_e_3903_);
v___f_3945_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___lam__0___boxed), 10, 3);
lean_closure_set(v___f_3945_, 0, v___x_3944_);
lean_closure_set(v___f_3945_, 1, v_fvars_3901_);
lean_closure_set(v___f_3945_, 2, v_doms_3902_);
v___x_3946_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_3900_, v___x_3943_, v___f_3945_, v_a_3904_, v_a_3905_, v_a_3906_, v_a_3907_, v_a_3908_, v_a_3909_);
return v___x_3946_;
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_dec_ref(v_e_3903_);
lean_dec_ref(v_doms_3902_);
lean_dec_ref(v_fvars_3901_);
lean_dec_ref(v_lctx_3900_);
v_a_3947_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3911_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3911_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(lean_object* v_e_3955_, lean_object* v_a_3956_, lean_object* v_a_3957_, lean_object* v_a_3958_, lean_object* v_a_3959_, lean_object* v_a_3960_, lean_object* v_a_3961_){
_start:
{
uint32_t v___x_3963_; uint8_t v___x_3964_; 
v___x_3963_ = 5;
v___x_3964_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_3955_, v___x_3963_);
if (v___x_3964_ == 0)
{
lean_object* v_lctx_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v_lctx_3965_ = lean_ctor_get(v_a_3958_, 2);
v___x_3966_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc_ref(v_lctx_3965_);
v___x_3967_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_3965_, v___x_3966_, v___x_3966_, v_e_3955_, v_a_3956_, v_a_3957_, v_a_3958_, v_a_3959_, v_a_3960_, v_a_3961_);
return v___x_3967_;
}
else
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = lean_box(0);
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v_e_3955_);
lean_ctor_set(v___x_3969_, 1, v___x_3968_);
v___x_3970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3969_);
return v___x_3970_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed(lean_object* v_e_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_, lean_object* v_a_3974_, lean_object* v_a_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall(v_e_3971_, v_a_3972_, v_a_3973_, v_a_3974_, v_a_3975_, v_a_3976_, v_a_3977_);
lean_dec(v_a_3977_);
lean_dec_ref(v_a_3976_);
lean_dec(v_a_3975_);
lean_dec_ref(v_a_3974_);
lean_dec(v_a_3973_);
lean_dec(v_a_3972_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed(lean_object* v_struct_3980_, lean_object* v_e_3981_, lean_object* v_typeName_3982_, lean_object* v_idx_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v_res_3991_; 
v_res_3991_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(v_struct_3980_, v_e_3981_, v_typeName_3982_, v_idx_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_, v___y_3989_);
lean_dec(v___y_3989_);
lean_dec_ref(v___y_3988_);
lean_dec(v___y_3987_);
lean_dec_ref(v___y_3986_);
lean_dec(v___y_3985_);
lean_dec(v___y_3984_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed(lean_object* v_e_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_3992_, v_a_3993_, v_a_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
lean_dec(v_a_3994_);
lean_dec(v_a_3993_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(lean_object* v_fvars_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_){
_start:
{
lean_object* v___x_4010_; 
v___x_4010_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; lean_object* v___x_4012_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
v___x_4012_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize(v_fvars_4001_, v_a_4011_, v___y_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
return v___x_4012_;
}
else
{
lean_dec_ref(v_fvars_4001_);
return v___x_4010_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed(lean_object* v_fvars_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2(v_fvars_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec(v___y_4015_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(lean_object* v_lctx_4023_, lean_object* v_fvars_4024_, lean_object* v_e_4025_, lean_object* v_letFVars_4026_, lean_object* v_a_4027_, lean_object* v_a_4028_, lean_object* v_a_4029_, lean_object* v_a_4030_, lean_object* v_a_4031_, lean_object* v_a_4032_){
_start:
{
switch(lean_obj_tag(v_e_4025_))
{
case 6:
{
lean_object* v_binderName_4034_; lean_object* v_binderType_4035_; lean_object* v_body_4036_; uint8_t v_binderInfo_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v_binderName_4034_ = lean_ctor_get(v_e_4025_, 0);
lean_inc(v_binderName_4034_);
v_binderType_4035_ = lean_ctor_get(v_e_4025_, 1);
lean_inc_ref(v_binderType_4035_);
v_body_4036_ = lean_ctor_get(v_e_4025_, 2);
lean_inc_ref(v_body_4036_);
v_binderInfo_4037_ = lean_ctor_get_uint8(v_e_4025_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_e_4025_, 3);
v___x_4038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4023_);
lean_inc(v_letFVars_4026_);
v___x_4039_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4024_, v_letFVars_4026_, v_lctx_4023_, v___x_4038_, v_binderType_4035_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec_ref(v_binderType_4035_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4041_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v___x_4039_, 1);
v___x_4041_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v_expr_4043_; uint8_t v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_n(v_a_4042_, 2);
lean_dec_ref_known(v___x_4041_, 1);
v_expr_4043_ = lean_ctor_get(v_a_4040_, 0);
lean_inc_ref(v_expr_4043_);
lean_dec(v_a_4040_);
v___x_4044_ = 0;
v___x_4045_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_4023_, v_a_4042_, v_binderName_4034_, v_expr_4043_, v_binderInfo_4037_, v___x_4044_);
v___x_4046_ = l_Lean_Expr_fvar___override(v_a_4042_);
v___x_4047_ = lean_array_push(v_fvars_4024_, v___x_4046_);
v_lctx_4023_ = v___x_4045_;
v_fvars_4024_ = v___x_4047_;
v_e_4025_ = v_body_4036_;
goto _start;
}
else
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4056_; 
lean_dec(v_a_4040_);
lean_dec_ref(v_body_4036_);
lean_dec(v_binderName_4034_);
lean_dec(v_letFVars_4026_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
v_a_4049_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4056_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4056_ == 0)
{
v___x_4051_ = v___x_4041_;
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4041_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4056_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4054_; 
if (v_isShared_4052_ == 0)
{
v___x_4054_ = v___x_4051_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
}
}
else
{
lean_dec_ref(v_body_4036_);
lean_dec(v_binderName_4034_);
lean_dec(v_letFVars_4026_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
return v___x_4039_;
}
}
case 8:
{
lean_object* v_declName_4057_; lean_object* v_type_4058_; lean_object* v_value_4059_; lean_object* v_body_4060_; uint8_t v_nondep_4061_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; lean_object* v___y_4067_; lean_object* v___y_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_declName_4057_ = lean_ctor_get(v_e_4025_, 0);
lean_inc(v_declName_4057_);
v_type_4058_ = lean_ctor_get(v_e_4025_, 1);
lean_inc_ref(v_type_4058_);
v_value_4059_ = lean_ctor_get(v_e_4025_, 2);
lean_inc_ref(v_value_4059_);
v_body_4060_ = lean_ctor_get(v_e_4025_, 3);
lean_inc_ref(v_body_4060_);
v_nondep_4061_ = lean_ctor_get_uint8(v_e_4025_, sizeof(void*)*4 + 8);
lean_dec_ref_known(v_e_4025_, 4);
v___x_4075_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitType___boxed), 8, 0);
lean_inc_ref(v_lctx_4023_);
lean_inc(v_letFVars_4026_);
v___x_4076_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4024_, v_letFVars_4026_, v_lctx_4023_, v___x_4075_, v_type_4058_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec_ref(v_type_4058_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
v___x_4078_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___boxed), 8, 0);
lean_inc_ref(v_lctx_4023_);
lean_inc(v_letFVars_4026_);
v___x_4079_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4024_, v_letFVars_4026_, v_lctx_4023_, v___x_4078_, v_value_4059_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec_ref(v_value_4059_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___y_4082_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; uint8_t v___x_4110_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4080_);
lean_dec_ref_known(v___x_4079_, 1);
v___x_4110_ = l_List_isEmpty___redArg(v_letFVars_4026_);
if (v___x_4110_ == 0)
{
lean_object* v___f_4111_; lean_object* v___x_4112_; 
lean_inc(v_a_4077_);
lean_inc(v_a_4080_);
v___f_4111_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__1___boxed), 9, 2);
lean_closure_set(v___f_4111_, 0, v_a_4080_);
lean_closure_set(v___f_4111_, 1, v_a_4077_);
lean_inc_ref(v_lctx_4023_);
v___x_4112_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4023_, v___f_4111_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_dec_ref_known(v___x_4112_, 1);
v___y_4082_ = v_a_4027_;
v___y_4083_ = v_a_4028_;
v___y_4084_ = v_a_4029_;
v___y_4085_ = v_a_4030_;
v___y_4086_ = v_a_4031_;
v___y_4087_ = v_a_4032_;
goto v___jp_4081_;
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
lean_dec(v_a_4080_);
lean_dec(v_a_4077_);
lean_dec_ref(v_body_4060_);
lean_dec(v_declName_4057_);
lean_dec(v_letFVars_4026_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4112_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4112_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4112_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
else
{
v___y_4082_ = v_a_4027_;
v___y_4083_ = v_a_4028_;
v___y_4084_ = v_a_4029_;
v___y_4085_ = v_a_4030_;
v___y_4086_ = v_a_4031_;
v___y_4087_ = v_a_4032_;
goto v___jp_4081_;
}
v___jp_4081_:
{
lean_object* v___x_4088_; 
v___x_4088_ = l_Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1(v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
if (lean_obj_tag(v___x_4088_) == 0)
{
lean_object* v_a_4089_; lean_object* v_expr_4090_; lean_object* v_expr_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4100_; 
v_a_4089_ = lean_ctor_get(v___x_4088_, 0);
lean_inc(v_a_4089_);
lean_dec_ref_known(v___x_4088_, 1);
v_expr_4090_ = lean_ctor_get(v_a_4077_, 0);
lean_inc_ref(v_expr_4090_);
lean_dec(v_a_4077_);
v_expr_4091_ = lean_ctor_get(v_a_4080_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v_a_4080_);
if (v_isSharedCheck_4100_ == 0)
{
lean_object* v_unused_4101_; 
v_unused_4101_ = lean_ctor_get(v_a_4080_, 1);
lean_dec(v_unused_4101_);
v___x_4093_ = v_a_4080_;
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_expr_4091_);
lean_dec(v_a_4080_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4100_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
uint8_t v___x_4095_; lean_object* v___x_4096_; 
v___x_4095_ = 0;
lean_inc(v_a_4089_);
v___x_4096_ = l_Lean_LocalContext_mkLetDecl(v_lctx_4023_, v_a_4089_, v_declName_4057_, v_expr_4090_, v_expr_4091_, v_nondep_4061_, v___x_4095_);
if (v_nondep_4061_ == 0)
{
lean_object* v___x_4098_; 
lean_inc(v_a_4089_);
if (v_isShared_4094_ == 0)
{
lean_ctor_set_tag(v___x_4093_, 1);
lean_ctor_set(v___x_4093_, 1, v_letFVars_4026_);
lean_ctor_set(v___x_4093_, 0, v_a_4089_);
v___x_4098_ = v___x_4093_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_a_4089_);
lean_ctor_set(v_reuseFailAlloc_4099_, 1, v_letFVars_4026_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
v___y_4063_ = v___y_4085_;
v___y_4064_ = v___x_4096_;
v___y_4065_ = v___y_4086_;
v___y_4066_ = v___y_4082_;
v___y_4067_ = v___y_4087_;
v___y_4068_ = v___y_4083_;
v___y_4069_ = v___y_4084_;
v___y_4070_ = v_a_4089_;
v___y_4071_ = v___x_4098_;
goto v___jp_4062_;
}
}
else
{
lean_del_object(v___x_4093_);
v___y_4063_ = v___y_4085_;
v___y_4064_ = v___x_4096_;
v___y_4065_ = v___y_4086_;
v___y_4066_ = v___y_4082_;
v___y_4067_ = v___y_4087_;
v___y_4068_ = v___y_4083_;
v___y_4069_ = v___y_4084_;
v___y_4070_ = v_a_4089_;
v___y_4071_ = v_letFVars_4026_;
goto v___jp_4062_;
}
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
lean_dec(v_a_4080_);
lean_dec(v_a_4077_);
lean_dec_ref(v_body_4060_);
lean_dec(v_declName_4057_);
lean_dec(v_letFVars_4026_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
v_a_4102_ = lean_ctor_get(v___x_4088_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4088_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_4088_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4088_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
}
else
{
lean_dec(v_a_4077_);
lean_dec_ref(v_body_4060_);
lean_dec(v_declName_4057_);
lean_dec(v_letFVars_4026_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
return v___x_4079_;
}
}
else
{
lean_dec_ref(v_body_4060_);
lean_dec_ref(v_value_4059_);
lean_dec(v_declName_4057_);
lean_dec(v_letFVars_4026_);
lean_dec_ref(v_fvars_4024_);
lean_dec_ref(v_lctx_4023_);
return v___x_4076_;
}
v___jp_4062_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = l_Lean_Expr_fvar___override(v___y_4070_);
v___x_4073_ = lean_array_push(v_fvars_4024_, v___x_4072_);
v_lctx_4023_ = v___y_4064_;
v_fvars_4024_ = v___x_4073_;
v_e_4025_ = v_body_4060_;
v_letFVars_4026_ = v___y_4071_;
v_a_4027_ = v___y_4066_;
v_a_4028_ = v___y_4068_;
v_a_4029_ = v___y_4069_;
v_a_4030_ = v___y_4063_;
v_a_4031_ = v___y_4065_;
v_a_4032_ = v___y_4067_;
goto _start;
}
}
default: 
{
lean_object* v___f_4121_; lean_object* v___x_4122_; 
lean_inc_ref(v_fvars_4024_);
v___f_4121_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4121_, 0, v_fvars_4024_);
v___x_4122_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___lam__0(v_fvars_4024_, v_letFVars_4026_, v_lctx_4023_, v___f_4121_, v_e_4025_, v_a_4027_, v_a_4028_, v_a_4029_, v_a_4030_, v_a_4031_, v_a_4032_);
lean_dec_ref(v_e_4025_);
lean_dec_ref(v_fvars_4024_);
return v___x_4122_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(lean_object* v_e_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_){
_start:
{
uint32_t v___x_4131_; uint8_t v___x_4132_; 
v___x_4131_ = 5;
v___x_4132_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_canSkip(v_e_4123_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v_lctx_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_lctx_4133_ = lean_ctor_get(v_a_4126_, 2);
v___x_4134_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar___closed__0));
lean_inc(v_a_4124_);
lean_inc_ref(v_lctx_4133_);
v___x_4135_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4133_, v___x_4134_, v_e_4123_, v_a_4124_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_, v_a_4129_);
return v___x_4135_;
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4136_ = lean_box(0);
v___x_4137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4137_, 0, v_e_4123_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
return v___x_4138_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed(lean_object* v_e_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet(v_e_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec(v_a_4140_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(lean_object* v_e_4148_, lean_object* v___y_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
switch(lean_obj_tag(v_e_4148_))
{
case 0:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4156_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___closed__1);
v___x_4157_ = l_Lean_MessageData_ofExpr(v_e_4148_);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7___redArg(v___x_4158_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4159_;
}
case 1:
{
lean_object* v___x_4160_; 
v___x_4160_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitFVar___redArg(v_e_4148_, v___y_4151_, v___y_4153_, v___y_4154_);
return v___x_4160_;
}
case 2:
{
lean_object* v___x_4161_; 
v___x_4161_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitMVar(v_e_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4161_;
}
case 3:
{
lean_object* v_u_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; 
v_u_4162_ = lean_ctor_get(v_e_4148_, 0);
lean_inc(v_u_4162_);
v___x_4163_ = l_Lean_Level_succ___override(v_u_4162_);
v___x_4164_ = l_Lean_Expr_sort___override(v___x_4163_);
v___x_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
v___x_4166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4166_, 0, v_e_4148_);
lean_ctor_set(v___x_4166_, 1, v___x_4165_);
v___x_4167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
return v___x_4167_;
}
case 4:
{
lean_object* v___x_4168_; 
v___x_4168_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst(v_e_4148_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4168_;
}
case 5:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; 
lean_inc_ref(v_e_4148_);
v___x_4169_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs___boxed), 8, 1);
lean_closure_set(v___x_4169_, 0, v_e_4148_);
v___x_4170_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4148_, v___x_4169_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4170_;
}
case 7:
{
lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_inc_ref(v_e_4148_);
v___x_4171_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall___boxed), 8, 1);
lean_closure_set(v___x_4171_, 0, v_e_4148_);
v___x_4172_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4148_, v___x_4171_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4172_;
}
case 9:
{
lean_object* v_a_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v_a_4173_ = lean_ctor_get(v_e_4148_, 0);
v___x_4174_ = l_Lean_Literal_type(v_a_4173_);
v___x_4175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v_e_4148_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
return v___x_4177_;
}
case 10:
{
lean_object* v_data_4178_; lean_object* v_expr_4179_; lean_object* v___x_4180_; 
v_data_4178_ = lean_ctor_get(v_e_4148_, 0);
v_expr_4179_ = lean_ctor_get(v_e_4148_, 1);
lean_inc_ref(v_expr_4179_);
v___x_4180_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_expr_4179_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
if (lean_obj_tag(v___x_4180_) == 0)
{
lean_object* v_a_4181_; lean_object* v___x_4183_; uint8_t v_isShared_4184_; uint8_t v_isSharedCheck_4203_; 
v_a_4181_ = lean_ctor_get(v___x_4180_, 0);
v_isSharedCheck_4203_ = !lean_is_exclusive(v___x_4180_);
if (v_isSharedCheck_4203_ == 0)
{
v___x_4183_ = v___x_4180_;
v_isShared_4184_ = v_isSharedCheck_4203_;
goto v_resetjp_4182_;
}
else
{
lean_inc(v_a_4181_);
lean_dec(v___x_4180_);
v___x_4183_ = lean_box(0);
v_isShared_4184_ = v_isSharedCheck_4203_;
goto v_resetjp_4182_;
}
v_resetjp_4182_:
{
lean_object* v_expr_4185_; lean_object* v_type_x3f_4186_; lean_object* v___x_4188_; uint8_t v_isShared_4189_; uint8_t v_isSharedCheck_4202_; 
v_expr_4185_ = lean_ctor_get(v_a_4181_, 0);
v_type_x3f_4186_ = lean_ctor_get(v_a_4181_, 1);
v_isSharedCheck_4202_ = !lean_is_exclusive(v_a_4181_);
if (v_isSharedCheck_4202_ == 0)
{
v___x_4188_ = v_a_4181_;
v_isShared_4189_ = v_isSharedCheck_4202_;
goto v_resetjp_4187_;
}
else
{
lean_inc(v_type_x3f_4186_);
lean_inc(v_expr_4185_);
lean_dec(v_a_4181_);
v___x_4188_ = lean_box(0);
v_isShared_4189_ = v_isSharedCheck_4202_;
goto v_resetjp_4187_;
}
v_resetjp_4187_:
{
lean_object* v___y_4191_; size_t v___x_4198_; size_t v___x_4199_; uint8_t v___x_4200_; 
v___x_4198_ = lean_ptr_addr(v_expr_4179_);
v___x_4199_ = lean_ptr_addr(v_expr_4185_);
v___x_4200_ = lean_usize_dec_eq(v___x_4198_, v___x_4199_);
if (v___x_4200_ == 0)
{
lean_object* v___x_4201_; 
lean_inc(v_data_4178_);
lean_dec_ref_known(v_e_4148_, 2);
v___x_4201_ = l_Lean_Expr_mdata___override(v_data_4178_, v_expr_4185_);
v___y_4191_ = v___x_4201_;
goto v___jp_4190_;
}
else
{
lean_dec_ref(v_expr_4185_);
v___y_4191_ = v_e_4148_;
goto v___jp_4190_;
}
v___jp_4190_:
{
lean_object* v___x_4193_; 
if (v_isShared_4189_ == 0)
{
lean_ctor_set(v___x_4188_, 0, v___y_4191_);
v___x_4193_ = v___x_4188_;
goto v_reusejp_4192_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___y_4191_);
lean_ctor_set(v_reuseFailAlloc_4197_, 1, v_type_x3f_4186_);
v___x_4193_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4192_;
}
v_reusejp_4192_:
{
lean_object* v___x_4195_; 
if (v_isShared_4184_ == 0)
{
lean_ctor_set(v___x_4183_, 0, v___x_4193_);
v___x_4195_ = v___x_4183_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4193_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
}
else
{
lean_dec_ref_known(v_e_4148_, 2);
return v___x_4180_;
}
}
case 11:
{
lean_object* v_typeName_4204_; lean_object* v_idx_4205_; lean_object* v_struct_4206_; lean_object* v___f_4207_; lean_object* v___x_4208_; 
v_typeName_4204_ = lean_ctor_get(v_e_4148_, 0);
v_idx_4205_ = lean_ctor_get(v_e_4148_, 1);
v_struct_4206_ = lean_ctor_get(v_e_4148_, 2);
lean_inc(v_idx_4205_);
lean_inc(v_typeName_4204_);
lean_inc_ref(v_e_4148_);
lean_inc_ref(v_struct_4206_);
v___f_4207_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0___boxed), 11, 4);
lean_closure_set(v___f_4207_, 0, v_struct_4206_);
lean_closure_set(v___f_4207_, 1, v_e_4148_);
lean_closure_set(v___f_4207_, 2, v_typeName_4204_);
lean_closure_set(v___f_4207_, 3, v_idx_4205_);
v___x_4208_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4148_, v___f_4207_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4208_;
}
default: 
{
lean_object* v___x_4209_; lean_object* v___x_4210_; 
lean_inc_ref(v_e_4148_);
v___x_4209_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet___boxed), 8, 1);
lean_closure_set(v___x_4209_, 0, v_e_4148_);
v___x_4210_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_checkCache(v_e_4148_, v___x_4209_, v___y_4149_, v___y_4150_, v___y_4151_, v___y_4152_, v___y_4153_, v___y_4154_);
return v___x_4210_;
}
}
}
}
static double _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0(void){
_start:
{
lean_object* v___x_4211_; double v___x_4212_; 
v___x_4211_ = lean_unsigned_to_nat(1000000000u);
v___x_4212_ = lean_float_of_nat(v___x_4211_);
return v___x_4212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(lean_object* v_e_4213_, lean_object* v_a_4214_, lean_object* v_a_4215_, lean_object* v_a_4216_, lean_object* v_a_4217_, lean_object* v_a_4218_, lean_object* v_a_4219_){
_start:
{
lean_object* v_options_4221_; uint8_t v_hasTrace_4222_; 
v_options_4221_ = lean_ctor_get(v_a_4218_, 1);
v_hasTrace_4222_ = lean_ctor_get_uint8(v_options_4221_, sizeof(void*)*1);
if (v_hasTrace_4222_ == 0)
{
lean_object* v___x_4223_; 
v___x_4223_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4223_;
}
else
{
lean_object* v_toCold_4224_; lean_object* v_inheritedTraceOptions_4225_; lean_object* v___f_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v_a_4234_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v_a_4249_; 
v_toCold_4224_ = lean_ctor_get(v_a_4218_, 0);
v_inheritedTraceOptions_4225_ = lean_ctor_get(v_toCold_4224_, 4);
lean_inc_ref(v_e_4213_);
v___f_4226_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__2___boxed), 9, 1);
lean_closure_set(v___f_4226_, 0, v_e_4213_);
v___x_4227_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_4228_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4229_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__6);
v___x_4230_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4225_, v_options_4221_, v___x_4229_);
if (v___x_4230_ == 0)
{
lean_object* v___x_4307_; uint8_t v___x_4308_; 
v___x_4307_ = l_Lean_trace_profiler;
v___x_4308_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4221_, v___x_4307_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; 
lean_dec_ref(v___f_4226_);
v___x_4309_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4309_;
}
else
{
goto v___jp_4258_;
}
}
else
{
goto v___jp_4258_;
}
v___jp_4231_:
{
lean_object* v___x_4235_; double v___x_4236_; double v___x_4237_; double v___x_4238_; double v___x_4239_; double v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4235_ = lean_io_mono_nanos_now();
v___x_4236_ = lean_float_of_nat(v___y_4233_);
v___x_4237_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_4238_ = lean_float_div(v___x_4236_, v___x_4237_);
v___x_4239_ = lean_float_of_nat(v___x_4235_);
v___x_4240_ = lean_float_div(v___x_4239_, v___x_4237_);
v___x_4241_ = lean_box_float(v___x_4238_);
v___x_4242_ = lean_box_float(v___x_4240_);
v___x_4243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4244_, 0, v_a_4234_);
lean_ctor_set(v___x_4244_, 1, v___x_4243_);
v___x_4245_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4227_, v_hasTrace_4222_, v___x_4228_, v_options_4221_, v___x_4230_, v___y_4232_, v___f_4226_, v___x_4244_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4245_;
}
v___jp_4246_:
{
lean_object* v___x_4250_; double v___x_4251_; double v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4250_ = lean_io_get_num_heartbeats();
v___x_4251_ = lean_float_of_nat(v___y_4247_);
v___x_4252_ = lean_float_of_nat(v___x_4250_);
v___x_4253_ = lean_box_float(v___x_4251_);
v___x_4254_ = lean_box_float(v___x_4252_);
v___x_4255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4253_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4256_, 0, v_a_4249_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
v___x_4257_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6(v___x_4227_, v_hasTrace_4222_, v___x_4228_, v_options_4221_, v___x_4230_, v___y_4248_, v___f_4226_, v___x_4256_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
return v___x_4257_;
}
v___jp_4258_:
{
lean_object* v___x_4259_; 
v___x_4259_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v_a_4219_);
if (lean_obj_tag(v___x_4259_) == 0)
{
lean_object* v_a_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v_a_4260_ = lean_ctor_get(v___x_4259_, 0);
lean_inc(v_a_4260_);
lean_dec_ref_known(v___x_4259_, 1);
v___x_4261_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4262_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_4221_, v___x_4261_);
if (v___x_4262_ == 0)
{
lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4263_ = lean_io_mono_nanos_now();
v___x_4264_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4267_; uint8_t v_isShared_4268_; uint8_t v_isSharedCheck_4272_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4267_ = v___x_4264_;
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
else
{
lean_inc(v_a_4265_);
lean_dec(v___x_4264_);
v___x_4267_ = lean_box(0);
v_isShared_4268_ = v_isSharedCheck_4272_;
goto v_resetjp_4266_;
}
v_resetjp_4266_:
{
lean_object* v___x_4270_; 
if (v_isShared_4268_ == 0)
{
lean_ctor_set_tag(v___x_4267_, 1);
v___x_4270_ = v___x_4267_;
goto v_reusejp_4269_;
}
else
{
lean_object* v_reuseFailAlloc_4271_; 
v_reuseFailAlloc_4271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
v___x_4270_ = v_reuseFailAlloc_4271_;
goto v_reusejp_4269_;
}
v_reusejp_4269_:
{
v___y_4232_ = v_a_4260_;
v___y_4233_ = v___x_4263_;
v_a_4234_ = v___x_4270_;
goto v___jp_4231_;
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
v_a_4273_ = lean_ctor_get(v___x_4264_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4264_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4264_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4264_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
lean_ctor_set_tag(v___x_4275_, 0);
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
v___y_4232_ = v_a_4260_;
v___y_4233_ = v___x_4263_;
v_a_4234_ = v___x_4278_;
goto v___jp_4231_;
}
}
}
}
else
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_io_get_num_heartbeats();
v___x_4282_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4213_, v_a_4214_, v_a_4215_, v_a_4216_, v_a_4217_, v_a_4218_, v_a_4219_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___x_4282_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
lean_ctor_set_tag(v___x_4285_, 1);
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
v___y_4247_ = v___x_4281_;
v___y_4248_ = v_a_4260_;
v_a_4249_ = v___x_4288_;
goto v___jp_4246_;
}
}
}
else
{
lean_object* v_a_4291_; lean_object* v___x_4293_; uint8_t v_isShared_4294_; uint8_t v_isSharedCheck_4298_; 
v_a_4291_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4298_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4298_ == 0)
{
v___x_4293_ = v___x_4282_;
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
else
{
lean_inc(v_a_4291_);
lean_dec(v___x_4282_);
v___x_4293_ = lean_box(0);
v_isShared_4294_ = v_isSharedCheck_4298_;
goto v_resetjp_4292_;
}
v_resetjp_4292_:
{
lean_object* v___x_4296_; 
if (v_isShared_4294_ == 0)
{
lean_ctor_set_tag(v___x_4293_, 0);
v___x_4296_ = v___x_4293_;
goto v_reusejp_4295_;
}
else
{
lean_object* v_reuseFailAlloc_4297_; 
v_reuseFailAlloc_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
v___x_4296_ = v_reuseFailAlloc_4297_;
goto v_reusejp_4295_;
}
v_reusejp_4295_:
{
v___y_4247_ = v___x_4281_;
v___y_4248_ = v_a_4260_;
v_a_4249_ = v___x_4296_;
goto v___jp_4246_;
}
}
}
}
}
else
{
lean_object* v_a_4299_; lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4306_; 
lean_dec_ref(v___f_4226_);
lean_dec_ref(v_e_4213_);
v_a_4299_ = lean_ctor_get(v___x_4259_, 0);
v_isSharedCheck_4306_ = !lean_is_exclusive(v___x_4259_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4301_ = v___x_4259_;
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
else
{
lean_inc(v_a_4299_);
lean_dec(v___x_4259_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4306_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v___x_4304_; 
if (v_isShared_4302_ == 0)
{
v___x_4304_ = v___x_4301_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v_a_4299_);
v___x_4304_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
return v___x_4304_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__0(lean_object* v_struct_4310_, lean_object* v_e_4311_, lean_object* v_typeName_4312_, lean_object* v_idx_4313_, lean_object* v___y_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_struct_4310_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4323_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref_known(v___x_4321_, 1);
v___x_4323_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitProj(v_e_4311_, v_typeName_4312_, v_idx_4313_, v_a_4322_, v___y_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
return v___x_4323_;
}
else
{
lean_dec(v_idx_4313_);
lean_dec(v_typeName_4312_);
lean_dec_ref(v_e_4311_);
return v___x_4321_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27___boxed(lean_object* v_e_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_){
_start:
{
lean_object* v_res_4332_; 
v_res_4332_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitAppArgs_go_x27(v_e_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_, v_a_4330_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
lean_dec_ref(v_a_4327_);
lean_dec(v_a_4326_);
lean_dec(v_a_4325_);
return v_res_4332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go___boxed(lean_object* v_lctx_4333_, lean_object* v_fvars_4334_, lean_object* v_doms_4335_, lean_object* v_e_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_, lean_object* v_a_4339_, lean_object* v_a_4340_, lean_object* v_a_4341_, lean_object* v_a_4342_, lean_object* v_a_4343_){
_start:
{
lean_object* v_res_4344_; 
v_res_4344_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitForall_go(v_lctx_4333_, v_fvars_4334_, v_doms_4335_, v_e_4336_, v_a_4337_, v_a_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_);
lean_dec(v_a_4342_);
lean_dec_ref(v_a_4341_);
lean_dec(v_a_4340_);
lean_dec_ref(v_a_4339_);
lean_dec(v_a_4338_);
lean_dec(v_a_4337_);
return v_res_4344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1___boxed(lean_object* v_e_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___lam__1(v_e_4345_, v___y_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
lean_dec(v___y_4347_);
lean_dec(v___y_4346_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go___boxed(lean_object* v_lctx_4354_, lean_object* v_fvars_4355_, lean_object* v_e_4356_, lean_object* v_letFVars_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go(v_lctx_4354_, v_fvars_4355_, v_e_4356_, v_letFVars_4357_, v_a_4358_, v_a_4359_, v_a_4360_, v_a_4361_, v_a_4362_, v_a_4363_);
lean_dec(v_a_4363_);
lean_dec_ref(v_a_4362_);
lean_dec(v_a_4361_);
lean_dec_ref(v_a_4360_);
lean_dec(v_a_4359_);
lean_dec(v_a_4358_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(lean_object* v_00_u03b1_4366_, lean_object* v_lctx_4367_, lean_object* v_localInsts_4368_, lean_object* v_x_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_, lean_object* v___y_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_){
_start:
{
lean_object* v___x_4377_; 
v___x_4377_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___redArg(v_lctx_4367_, v_localInsts_4368_, v_x_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_, v___y_4375_);
return v___x_4377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0___boxed(lean_object* v_00_u03b1_4378_, lean_object* v_lctx_4379_, lean_object* v_localInsts_4380_, lean_object* v_x_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_Meta_withLCtx___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__0(v_00_u03b1_4378_, v_lctx_4379_, v_localInsts_4380_, v_x_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
lean_dec(v___y_4383_);
lean_dec(v___y_4382_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(lean_object* v_00_u03b1_4390_, lean_object* v_lctx_4391_, lean_object* v_x_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; 
v___x_4400_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___redArg(v_lctx_4391_, v_x_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_, v___y_4398_);
return v___x_4400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2___boxed(lean_object* v_00_u03b1_4401_, lean_object* v_lctx_4402_, lean_object* v_x_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_){
_start:
{
lean_object* v_res_4411_; 
v_res_4411_ = l_Lean_Meta_withLCtx_x27___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__2(v_00_u03b1_4401_, v_lctx_4402_, v_x_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_, v___y_4409_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
lean_dec(v___y_4407_);
lean_dec_ref(v___y_4406_);
lean_dec(v___y_4405_);
lean_dec(v___y_4404_);
return v_res_4411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_){
_start:
{
lean_object* v___x_4419_; 
v___x_4419_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg(v___y_4417_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___boxed(lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_){
_start:
{
lean_object* v_res_4427_; 
v_res_4427_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4(v___y_4420_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_);
lean_dec(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec(v___y_4423_);
lean_dec_ref(v___y_4422_);
lean_dec(v___y_4421_);
lean_dec(v___y_4420_);
return v_res_4427_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_){
_start:
{
lean_object* v___x_4435_; 
v___x_4435_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___redArg(v___y_4433_);
return v___x_4435_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7___boxed(lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_){
_start:
{
lean_object* v_res_4443_; 
v_res_4443_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_go_spec__1_spec__7(v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_, v___y_4441_);
lean_dec(v___y_4441_);
lean_dec_ref(v___y_4440_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec(v___y_4436_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(lean_object* v_00_u03b1_4444_, lean_object* v_x_4445_, lean_object* v___y_4446_, lean_object* v___y_4447_, lean_object* v___y_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_){
_start:
{
lean_object* v___x_4453_; 
v___x_4453_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___redArg(v_x_4445_);
return v___x_4453_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14___boxed(lean_object* v_00_u03b1_4454_, lean_object* v_x_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__14(v_00_u03b1_4454_, v_x_4455_, v___y_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
lean_dec(v___y_4456_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(lean_object* v_oldTraces_4464_, lean_object* v_data_4465_, lean_object* v_ref_4466_, lean_object* v_msg_4467_, lean_object* v___y_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
lean_object* v___x_4475_; 
v___x_4475_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___redArg(v_oldTraces_4464_, v_data_4465_, v_ref_4466_, v_msg_4467_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
return v___x_4475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13___boxed(lean_object* v_oldTraces_4476_, lean_object* v_data_4477_, lean_object* v_ref_4478_, lean_object* v_msg_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13(v_oldTraces_4476_, v_data_4477_, v_ref_4478_, v_msg_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec(v___y_4480_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(lean_object* v___y_4488_){
_start:
{
lean_object* v___x_4490_; lean_object* v_traceState_4491_; lean_object* v_traces_4492_; lean_object* v___x_4493_; lean_object* v_traceState_4494_; lean_object* v_env_4495_; lean_object* v_nextMacroScope_4496_; lean_object* v_ngen_4497_; lean_object* v_auxDeclNGen_4498_; lean_object* v_cache_4499_; lean_object* v_messages_4500_; lean_object* v_infoState_4501_; lean_object* v_snapshotTasks_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4523_; 
v___x_4490_ = lean_st_ref_get(v___y_4488_);
v_traceState_4491_ = lean_ctor_get(v___x_4490_, 4);
lean_inc_ref(v_traceState_4491_);
lean_dec(v___x_4490_);
v_traces_4492_ = lean_ctor_get(v_traceState_4491_, 0);
lean_inc_ref(v_traces_4492_);
lean_dec_ref(v_traceState_4491_);
v___x_4493_ = lean_st_ref_take(v___y_4488_);
v_traceState_4494_ = lean_ctor_get(v___x_4493_, 4);
v_env_4495_ = lean_ctor_get(v___x_4493_, 0);
v_nextMacroScope_4496_ = lean_ctor_get(v___x_4493_, 1);
v_ngen_4497_ = lean_ctor_get(v___x_4493_, 2);
v_auxDeclNGen_4498_ = lean_ctor_get(v___x_4493_, 3);
v_cache_4499_ = lean_ctor_get(v___x_4493_, 5);
v_messages_4500_ = lean_ctor_get(v___x_4493_, 6);
v_infoState_4501_ = lean_ctor_get(v___x_4493_, 7);
v_snapshotTasks_4502_ = lean_ctor_get(v___x_4493_, 8);
v_isSharedCheck_4523_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4523_ == 0)
{
v___x_4504_ = v___x_4493_;
v_isShared_4505_ = v_isSharedCheck_4523_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_snapshotTasks_4502_);
lean_inc(v_infoState_4501_);
lean_inc(v_messages_4500_);
lean_inc(v_cache_4499_);
lean_inc(v_traceState_4494_);
lean_inc(v_auxDeclNGen_4498_);
lean_inc(v_ngen_4497_);
lean_inc(v_nextMacroScope_4496_);
lean_inc(v_env_4495_);
lean_dec(v___x_4493_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4523_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
uint64_t v_tid_4506_; lean_object* v___x_4508_; uint8_t v_isShared_4509_; uint8_t v_isSharedCheck_4521_; 
v_tid_4506_ = lean_ctor_get_uint64(v_traceState_4494_, sizeof(void*)*1);
v_isSharedCheck_4521_ = !lean_is_exclusive(v_traceState_4494_);
if (v_isSharedCheck_4521_ == 0)
{
lean_object* v_unused_4522_; 
v_unused_4522_ = lean_ctor_get(v_traceState_4494_, 0);
lean_dec(v_unused_4522_);
v___x_4508_ = v_traceState_4494_;
v_isShared_4509_ = v_isSharedCheck_4521_;
goto v_resetjp_4507_;
}
else
{
lean_dec(v_traceState_4494_);
v___x_4508_ = lean_box(0);
v_isShared_4509_ = v_isSharedCheck_4521_;
goto v_resetjp_4507_;
}
v_resetjp_4507_:
{
lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v___x_4510_ = lean_unsigned_to_nat(32u);
v___x_4511_ = lean_mk_empty_array_with_capacity(v___x_4510_);
lean_dec_ref(v___x_4511_);
v___x_4512_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__4___redArg___closed__1);
if (v_isShared_4509_ == 0)
{
lean_ctor_set(v___x_4508_, 0, v___x_4512_);
v___x_4514_ = v___x_4508_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4520_; 
v_reuseFailAlloc_4520_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4520_, 0, v___x_4512_);
lean_ctor_set_uint64(v_reuseFailAlloc_4520_, sizeof(void*)*1, v_tid_4506_);
v___x_4514_ = v_reuseFailAlloc_4520_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
lean_object* v___x_4516_; 
if (v_isShared_4505_ == 0)
{
lean_ctor_set(v___x_4504_, 4, v___x_4514_);
v___x_4516_ = v___x_4504_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4519_; 
v_reuseFailAlloc_4519_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4519_, 0, v_env_4495_);
lean_ctor_set(v_reuseFailAlloc_4519_, 1, v_nextMacroScope_4496_);
lean_ctor_set(v_reuseFailAlloc_4519_, 2, v_ngen_4497_);
lean_ctor_set(v_reuseFailAlloc_4519_, 3, v_auxDeclNGen_4498_);
lean_ctor_set(v_reuseFailAlloc_4519_, 4, v___x_4514_);
lean_ctor_set(v_reuseFailAlloc_4519_, 5, v_cache_4499_);
lean_ctor_set(v_reuseFailAlloc_4519_, 6, v_messages_4500_);
lean_ctor_set(v_reuseFailAlloc_4519_, 7, v_infoState_4501_);
lean_ctor_set(v_reuseFailAlloc_4519_, 8, v_snapshotTasks_4502_);
v___x_4516_ = v_reuseFailAlloc_4519_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4517_ = lean_st_ref_put(v___y_4488_, v___x_4516_);
v___x_4518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4518_, 0, v_traces_4492_);
return v___x_4518_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg___boxed(lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4524_);
lean_dec(v___y_4524_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v___y_4530_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___boxed(lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_){
_start:
{
lean_object* v_res_4538_; 
v_res_4538_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1(v___y_4533_, v___y_4534_, v___y_4535_, v___y_4536_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
lean_dec(v___y_4534_);
lean_dec_ref(v___y_4533_);
return v_res_4538_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(lean_object* v___y_4539_, lean_object* v_zetaDeltaFVarIds_4540_, lean_object* v_a_x3f_4541_){
_start:
{
lean_object* v___x_4543_; lean_object* v_mctx_4544_; lean_object* v_cache_4545_; lean_object* v_postponed_4546_; lean_object* v_diag_4547_; lean_object* v___x_4549_; uint8_t v_isShared_4550_; uint8_t v_isSharedCheck_4557_; 
v___x_4543_ = lean_st_ref_take(v___y_4539_);
v_mctx_4544_ = lean_ctor_get(v___x_4543_, 0);
v_cache_4545_ = lean_ctor_get(v___x_4543_, 1);
v_postponed_4546_ = lean_ctor_get(v___x_4543_, 3);
v_diag_4547_ = lean_ctor_get(v___x_4543_, 4);
v_isSharedCheck_4557_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4557_ == 0)
{
lean_object* v_unused_4558_; 
v_unused_4558_ = lean_ctor_get(v___x_4543_, 2);
lean_dec(v_unused_4558_);
v___x_4549_ = v___x_4543_;
v_isShared_4550_ = v_isSharedCheck_4557_;
goto v_resetjp_4548_;
}
else
{
lean_inc(v_diag_4547_);
lean_inc(v_postponed_4546_);
lean_inc(v_cache_4545_);
lean_inc(v_mctx_4544_);
lean_dec(v___x_4543_);
v___x_4549_ = lean_box(0);
v_isShared_4550_ = v_isSharedCheck_4557_;
goto v_resetjp_4548_;
}
v_resetjp_4548_:
{
lean_object* v___x_4552_; 
if (v_isShared_4550_ == 0)
{
lean_ctor_set(v___x_4549_, 2, v_zetaDeltaFVarIds_4540_);
v___x_4552_ = v___x_4549_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4556_; 
v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4556_, 0, v_mctx_4544_);
lean_ctor_set(v_reuseFailAlloc_4556_, 1, v_cache_4545_);
lean_ctor_set(v_reuseFailAlloc_4556_, 2, v_zetaDeltaFVarIds_4540_);
lean_ctor_set(v_reuseFailAlloc_4556_, 3, v_postponed_4546_);
lean_ctor_set(v_reuseFailAlloc_4556_, 4, v_diag_4547_);
v___x_4552_ = v_reuseFailAlloc_4556_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; 
v___x_4553_ = lean_st_ref_put(v___y_4539_, v___x_4552_);
v___x_4554_ = lean_box(0);
v___x_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4554_);
return v___x_4555_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0___boxed(lean_object* v___y_4559_, lean_object* v_zetaDeltaFVarIds_4560_, lean_object* v_a_x3f_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v_res_4563_; 
v_res_4563_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4559_, v_zetaDeltaFVarIds_4560_, v_a_x3f_4561_);
lean_dec(v_a_x3f_4561_);
lean_dec(v___y_4559_);
return v_res_4563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(lean_object* v_cls_4564_, lean_object* v_msg_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_ref_4571_; lean_object* v___x_4572_; lean_object* v_a_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4617_; 
v_ref_4571_ = lean_ctor_get(v___y_4568_, 4);
v___x_4572_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
v_a_4573_ = lean_ctor_get(v___x_4572_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4572_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4575_ = v___x_4572_;
v_isShared_4576_ = v_isSharedCheck_4617_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_a_4573_);
lean_dec(v___x_4572_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4617_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
lean_object* v___x_4577_; lean_object* v_traceState_4578_; lean_object* v_env_4579_; lean_object* v_nextMacroScope_4580_; lean_object* v_ngen_4581_; lean_object* v_auxDeclNGen_4582_; lean_object* v_cache_4583_; lean_object* v_messages_4584_; lean_object* v_infoState_4585_; lean_object* v_snapshotTasks_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4616_; 
v___x_4577_ = lean_st_ref_take(v___y_4569_);
v_traceState_4578_ = lean_ctor_get(v___x_4577_, 4);
v_env_4579_ = lean_ctor_get(v___x_4577_, 0);
v_nextMacroScope_4580_ = lean_ctor_get(v___x_4577_, 1);
v_ngen_4581_ = lean_ctor_get(v___x_4577_, 2);
v_auxDeclNGen_4582_ = lean_ctor_get(v___x_4577_, 3);
v_cache_4583_ = lean_ctor_get(v___x_4577_, 5);
v_messages_4584_ = lean_ctor_get(v___x_4577_, 6);
v_infoState_4585_ = lean_ctor_get(v___x_4577_, 7);
v_snapshotTasks_4586_ = lean_ctor_get(v___x_4577_, 8);
v_isSharedCheck_4616_ = !lean_is_exclusive(v___x_4577_);
if (v_isSharedCheck_4616_ == 0)
{
v___x_4588_ = v___x_4577_;
v_isShared_4589_ = v_isSharedCheck_4616_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_snapshotTasks_4586_);
lean_inc(v_infoState_4585_);
lean_inc(v_messages_4584_);
lean_inc(v_cache_4583_);
lean_inc(v_traceState_4578_);
lean_inc(v_auxDeclNGen_4582_);
lean_inc(v_ngen_4581_);
lean_inc(v_nextMacroScope_4580_);
lean_inc(v_env_4579_);
lean_dec(v___x_4577_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4616_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
uint64_t v_tid_4590_; lean_object* v_traces_4591_; lean_object* v___x_4593_; uint8_t v_isShared_4594_; uint8_t v_isSharedCheck_4615_; 
v_tid_4590_ = lean_ctor_get_uint64(v_traceState_4578_, sizeof(void*)*1);
v_traces_4591_ = lean_ctor_get(v_traceState_4578_, 0);
v_isSharedCheck_4615_ = !lean_is_exclusive(v_traceState_4578_);
if (v_isSharedCheck_4615_ == 0)
{
v___x_4593_ = v_traceState_4578_;
v_isShared_4594_ = v_isSharedCheck_4615_;
goto v_resetjp_4592_;
}
else
{
lean_inc(v_traces_4591_);
lean_dec(v_traceState_4578_);
v___x_4593_ = lean_box(0);
v_isShared_4594_ = v_isSharedCheck_4615_;
goto v_resetjp_4592_;
}
v_resetjp_4592_:
{
lean_object* v___x_4595_; double v___x_4596_; uint8_t v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4595_ = lean_box(0);
v___x_4596_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
v___x_4597_ = 0;
v___x_4598_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_4599_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_4599_, 0, v_cls_4564_);
lean_ctor_set(v___x_4599_, 1, v___x_4595_);
lean_ctor_set(v___x_4599_, 2, v___x_4598_);
lean_ctor_set_float(v___x_4599_, sizeof(void*)*3, v___x_4596_);
lean_ctor_set_float(v___x_4599_, sizeof(void*)*3 + 8, v___x_4596_);
lean_ctor_set_uint8(v___x_4599_, sizeof(void*)*3 + 16, v___x_4597_);
v___x_4600_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__2));
v___x_4601_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_4601_, 0, v___x_4599_);
lean_ctor_set(v___x_4601_, 1, v_a_4573_);
lean_ctor_set(v___x_4601_, 2, v___x_4600_);
lean_inc(v_ref_4571_);
v___x_4602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4602_, 0, v_ref_4571_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = l_Lean_PersistentArray_push___redArg(v_traces_4591_, v___x_4602_);
if (v_isShared_4594_ == 0)
{
lean_ctor_set(v___x_4593_, 0, v___x_4603_);
v___x_4605_ = v___x_4593_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4614_; 
v_reuseFailAlloc_4614_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_4614_, 0, v___x_4603_);
lean_ctor_set_uint64(v_reuseFailAlloc_4614_, sizeof(void*)*1, v_tid_4590_);
v___x_4605_ = v_reuseFailAlloc_4614_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4607_; 
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 4, v___x_4605_);
v___x_4607_ = v___x_4588_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4613_; 
v_reuseFailAlloc_4613_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4613_, 0, v_env_4579_);
lean_ctor_set(v_reuseFailAlloc_4613_, 1, v_nextMacroScope_4580_);
lean_ctor_set(v_reuseFailAlloc_4613_, 2, v_ngen_4581_);
lean_ctor_set(v_reuseFailAlloc_4613_, 3, v_auxDeclNGen_4582_);
lean_ctor_set(v_reuseFailAlloc_4613_, 4, v___x_4605_);
lean_ctor_set(v_reuseFailAlloc_4613_, 5, v_cache_4583_);
lean_ctor_set(v_reuseFailAlloc_4613_, 6, v_messages_4584_);
lean_ctor_set(v_reuseFailAlloc_4613_, 7, v_infoState_4585_);
lean_ctor_set(v_reuseFailAlloc_4613_, 8, v_snapshotTasks_4586_);
v___x_4607_ = v_reuseFailAlloc_4613_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4608_ = lean_st_ref_put(v___y_4569_, v___x_4607_);
v___x_4609_ = lean_box(0);
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 0, v___x_4609_);
v___x_4611_ = v___x_4575_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4612_; 
v_reuseFailAlloc_4612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4612_, 0, v___x_4609_);
v___x_4611_ = v_reuseFailAlloc_4612_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
return v___x_4611_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0___boxed(lean_object* v_cls_4618_, lean_object* v_msg_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4618_, v_msg_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
return v_res_4625_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1(void){
_start:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; 
v___x_4627_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__0));
v___x_4628_ = l_Lean_stringToMessageData(v___x_4627_);
return v___x_4628_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3(void){
_start:
{
lean_object* v___x_4630_; lean_object* v___x_4631_; 
v___x_4630_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__2));
v___x_4631_ = l_Lean_stringToMessageData(v___x_4630_);
return v___x_4631_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5(void){
_start:
{
lean_object* v___x_4633_; lean_object* v___x_4634_; 
v___x_4633_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__4));
v___x_4634_ = l_Lean_stringToMessageData(v___x_4633_);
return v___x_4634_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7(void){
_start:
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4636_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__6));
v___x_4637_ = l_Lean_stringToMessageData(v___x_4636_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(lean_object* v___x_4638_, lean_object* v_e_4639_, lean_object* v___x_4640_, lean_object* v___x_4641_, lean_object* v_cls_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_){
_start:
{
lean_object* v___x_4648_; lean_object* v___x_4649_; 
v___x_4648_ = lean_st_mk_ref(v___x_4638_);
v___x_4649_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit(v_e_4639_, v___x_4640_, v___x_4648_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4649_) == 0)
{
lean_object* v_a_4650_; lean_object* v___x_4652_; uint8_t v_isShared_4653_; uint8_t v_isSharedCheck_4721_; 
v_a_4650_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4652_ = v___x_4649_;
v_isShared_4653_ = v_isSharedCheck_4721_;
goto v_resetjp_4651_;
}
else
{
lean_inc(v_a_4650_);
lean_dec(v___x_4649_);
v___x_4652_ = lean_box(0);
v_isShared_4653_ = v_isSharedCheck_4721_;
goto v_resetjp_4651_;
}
v_resetjp_4651_:
{
lean_object* v___x_4654_; lean_object* v_count_4655_; lean_object* v___x_4657_; uint8_t v_isShared_4658_; uint8_t v_isSharedCheck_4719_; 
v___x_4654_ = lean_st_ref_get(v___x_4648_);
lean_dec(v___x_4648_);
v_count_4655_ = lean_ctor_get(v___x_4654_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4654_);
if (v_isSharedCheck_4719_ == 0)
{
lean_object* v_unused_4720_; 
v_unused_4720_ = lean_ctor_get(v___x_4654_, 1);
lean_dec(v_unused_4720_);
v___x_4657_ = v___x_4654_;
v_isShared_4658_ = v_isSharedCheck_4719_;
goto v_resetjp_4656_;
}
else
{
lean_inc(v_count_4655_);
lean_dec(v___x_4654_);
v___x_4657_ = lean_box(0);
v_isShared_4658_ = v_isSharedCheck_4719_;
goto v_resetjp_4656_;
}
v_resetjp_4656_:
{
uint8_t v___x_4681_; 
v___x_4681_ = lean_nat_dec_eq(v_count_4655_, v___x_4641_);
if (v___x_4681_ == 0)
{
lean_object* v_options_4682_; uint8_t v_hasTrace_4683_; 
v_options_4682_ = lean_ctor_get(v___y_4645_, 1);
v_hasTrace_4683_ = lean_ctor_get_uint8(v_options_4682_, sizeof(void*)*1);
if (v_hasTrace_4683_ == 0)
{
lean_dec(v_cls_4642_);
goto v___jp_4659_;
}
else
{
lean_object* v_toCold_4684_; lean_object* v_inheritedTraceOptions_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; uint8_t v___x_4688_; 
v_toCold_4684_ = lean_ctor_get(v___y_4645_, 0);
v_inheritedTraceOptions_4685_ = lean_ctor_get(v_toCold_4684_, 4);
v___x_4686_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4642_);
v___x_4687_ = l_Lean_Name_append(v___x_4686_, v_cls_4642_);
v___x_4688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4685_, v_options_4682_, v___x_4687_);
lean_dec(v___x_4687_);
if (v___x_4688_ == 0)
{
lean_dec(v_cls_4642_);
goto v___jp_4659_;
}
else
{
lean_object* v_expr_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; 
v_expr_4689_ = lean_ctor_get(v_a_4650_, 0);
v___x_4690_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__5);
lean_inc_ref(v_expr_4689_);
v___x_4691_ = l_Lean_indentExpr(v_expr_4689_);
v___x_4692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4692_, 0, v___x_4690_);
lean_ctor_set(v___x_4692_, 1, v___x_4691_);
v___x_4693_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4642_, v___x_4692_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4693_) == 0)
{
lean_dec_ref_known(v___x_4693_, 1);
goto v___jp_4659_;
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
lean_del_object(v___x_4657_);
lean_dec(v_count_4655_);
lean_del_object(v___x_4652_);
lean_dec(v_a_4650_);
v_a_4694_ = lean_ctor_get(v___x_4693_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4693_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4693_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4693_);
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
}
else
{
lean_object* v_options_4702_; uint8_t v_hasTrace_4703_; 
v_options_4702_ = lean_ctor_get(v___y_4645_, 1);
v_hasTrace_4703_ = lean_ctor_get_uint8(v_options_4702_, sizeof(void*)*1);
if (v_hasTrace_4703_ == 0)
{
lean_dec(v_cls_4642_);
goto v___jp_4659_;
}
else
{
lean_object* v_toCold_4704_; lean_object* v_inheritedTraceOptions_4705_; lean_object* v___x_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v_toCold_4704_ = lean_ctor_get(v___y_4645_, 0);
v_inheritedTraceOptions_4705_ = lean_ctor_get(v_toCold_4704_, 4);
v___x_4706_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
lean_inc(v_cls_4642_);
v___x_4707_ = l_Lean_Name_append(v___x_4706_, v_cls_4642_);
v___x_4708_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4705_, v_options_4702_, v___x_4707_);
lean_dec(v___x_4707_);
if (v___x_4708_ == 0)
{
lean_dec(v_cls_4642_);
goto v___jp_4659_;
}
else
{
lean_object* v___x_4709_; lean_object* v___x_4710_; 
v___x_4709_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__7);
v___x_4710_ = l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__0(v_cls_4642_, v___x_4709_, v___y_4643_, v___y_4644_, v___y_4645_, v___y_4646_);
if (lean_obj_tag(v___x_4710_) == 0)
{
lean_dec_ref_known(v___x_4710_, 1);
goto v___jp_4659_;
}
else
{
lean_object* v_a_4711_; lean_object* v___x_4713_; uint8_t v_isShared_4714_; uint8_t v_isSharedCheck_4718_; 
lean_del_object(v___x_4657_);
lean_dec(v_count_4655_);
lean_del_object(v___x_4652_);
lean_dec(v_a_4650_);
v_a_4711_ = lean_ctor_get(v___x_4710_, 0);
v_isSharedCheck_4718_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4718_ == 0)
{
v___x_4713_ = v___x_4710_;
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
else
{
lean_inc(v_a_4711_);
lean_dec(v___x_4710_);
v___x_4713_ = lean_box(0);
v_isShared_4714_ = v_isSharedCheck_4718_;
goto v_resetjp_4712_;
}
v_resetjp_4712_:
{
lean_object* v___x_4716_; 
if (v_isShared_4714_ == 0)
{
v___x_4716_ = v___x_4713_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4717_; 
v_reuseFailAlloc_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4717_, 0, v_a_4711_);
v___x_4716_ = v_reuseFailAlloc_4717_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
return v___x_4716_;
}
}
}
}
}
}
v___jp_4659_:
{
lean_object* v_expr_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4679_; 
v_expr_4660_ = lean_ctor_get(v_a_4650_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v_a_4650_);
if (v_isSharedCheck_4679_ == 0)
{
lean_object* v_unused_4680_; 
v_unused_4680_ = lean_ctor_get(v_a_4650_, 1);
lean_dec(v_unused_4680_);
v___x_4662_ = v_a_4650_;
v_isShared_4663_ = v_isSharedCheck_4679_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_expr_4660_);
lean_dec(v_a_4650_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4679_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4669_; 
v___x_4664_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__1);
v___x_4665_ = l_Nat_reprFast(v_count_4655_);
v___x_4666_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
v___x_4667_ = l_Lean_MessageData_ofFormat(v___x_4666_);
if (v_isShared_4663_ == 0)
{
lean_ctor_set_tag(v___x_4662_, 7);
lean_ctor_set(v___x_4662_, 1, v___x_4667_);
lean_ctor_set(v___x_4662_, 0, v___x_4664_);
v___x_4669_ = v___x_4662_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4678_, 1, v___x_4667_);
v___x_4669_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
lean_object* v___x_4670_; lean_object* v___x_4672_; 
v___x_4670_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___closed__3);
if (v_isShared_4658_ == 0)
{
lean_ctor_set_tag(v___x_4657_, 7);
lean_ctor_set(v___x_4657_, 1, v___x_4670_);
lean_ctor_set(v___x_4657_, 0, v___x_4669_);
v___x_4672_ = v___x_4657_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4669_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v___x_4670_);
v___x_4672_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; lean_object* v___x_4675_; 
v___x_4673_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4673_, 0, v_expr_4660_);
lean_ctor_set(v___x_4673_, 1, v___x_4672_);
if (v_isShared_4653_ == 0)
{
lean_ctor_set(v___x_4652_, 0, v___x_4673_);
v___x_4675_ = v___x_4652_;
goto v_reusejp_4674_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4673_);
v___x_4675_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4674_;
}
v_reusejp_4674_:
{
return v___x_4675_;
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
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_dec(v___x_4648_);
lean_dec(v_cls_4642_);
v_a_4722_ = lean_ctor_get(v___x_4649_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4649_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4649_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed(lean_object* v___x_4730_, lean_object* v_e_4731_, lean_object* v___x_4732_, lean_object* v___x_4733_, lean_object* v_cls_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
lean_object* v_res_4740_; 
v_res_4740_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1(v___x_4730_, v_e_4731_, v___x_4732_, v___x_4733_, v_cls_4734_, v___y_4735_, v___y_4736_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec_ref(v___y_4737_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
lean_dec(v___x_4733_);
lean_dec(v___x_4732_);
return v_res_4740_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(lean_object* v___y_4741_, lean_object* v_cache_4742_, lean_object* v_a_x3f_4743_){
_start:
{
lean_object* v___x_4745_; lean_object* v_mctx_4746_; lean_object* v_zetaDeltaFVarIds_4747_; lean_object* v_postponed_4748_; lean_object* v_diag_4749_; lean_object* v___x_4751_; uint8_t v_isShared_4752_; uint8_t v_isSharedCheck_4759_; 
v___x_4745_ = lean_st_ref_take(v___y_4741_);
v_mctx_4746_ = lean_ctor_get(v___x_4745_, 0);
v_zetaDeltaFVarIds_4747_ = lean_ctor_get(v___x_4745_, 2);
v_postponed_4748_ = lean_ctor_get(v___x_4745_, 3);
v_diag_4749_ = lean_ctor_get(v___x_4745_, 4);
v_isSharedCheck_4759_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4759_ == 0)
{
lean_object* v_unused_4760_; 
v_unused_4760_ = lean_ctor_get(v___x_4745_, 1);
lean_dec(v_unused_4760_);
v___x_4751_ = v___x_4745_;
v_isShared_4752_ = v_isSharedCheck_4759_;
goto v_resetjp_4750_;
}
else
{
lean_inc(v_diag_4749_);
lean_inc(v_postponed_4748_);
lean_inc(v_zetaDeltaFVarIds_4747_);
lean_inc(v_mctx_4746_);
lean_dec(v___x_4745_);
v___x_4751_ = lean_box(0);
v_isShared_4752_ = v_isSharedCheck_4759_;
goto v_resetjp_4750_;
}
v_resetjp_4750_:
{
lean_object* v___x_4754_; 
if (v_isShared_4752_ == 0)
{
lean_ctor_set(v___x_4751_, 1, v_cache_4742_);
v___x_4754_ = v___x_4751_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4758_; 
v_reuseFailAlloc_4758_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4758_, 0, v_mctx_4746_);
lean_ctor_set(v_reuseFailAlloc_4758_, 1, v_cache_4742_);
lean_ctor_set(v_reuseFailAlloc_4758_, 2, v_zetaDeltaFVarIds_4747_);
lean_ctor_set(v_reuseFailAlloc_4758_, 3, v_postponed_4748_);
lean_ctor_set(v_reuseFailAlloc_4758_, 4, v_diag_4749_);
v___x_4754_ = v_reuseFailAlloc_4758_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; 
v___x_4755_ = lean_st_ref_put(v___y_4741_, v___x_4754_);
v___x_4756_ = lean_box(0);
v___x_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4756_);
return v___x_4757_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2___boxed(lean_object* v___y_4761_, lean_object* v_cache_4762_, lean_object* v_a_x3f_4763_, lean_object* v___y_4764_){
_start:
{
lean_object* v_res_4765_; 
v_res_4765_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4761_, v_cache_4762_, v_a_x3f_4763_);
lean_dec(v_a_x3f_4763_);
lean_dec(v___y_4761_);
return v_res_4765_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0(void){
_start:
{
uint8_t v___x_4766_; lean_object* v___x_4767_; 
v___x_4766_ = 2;
v___x_4767_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v___x_4766_);
return v___x_4767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(uint8_t v___x_4768_, lean_object* v___f_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v___x_4820_; uint8_t v_beta_4821_; 
v___x_4820_ = l_Lean_Meta_Context_config(v___y_4770_);
v_beta_4821_ = lean_ctor_get_uint8(v___x_4820_, 13);
if (v_beta_4821_ == 0)
{
lean_dec_ref(v___x_4820_);
goto v___jp_4775_;
}
else
{
uint8_t v_iota_4822_; 
v_iota_4822_ = lean_ctor_get_uint8(v___x_4820_, 12);
if (v_iota_4822_ == 0)
{
lean_dec_ref(v___x_4820_);
goto v___jp_4775_;
}
else
{
uint8_t v_zeta_4823_; 
v_zeta_4823_ = lean_ctor_get_uint8(v___x_4820_, 15);
if (v_zeta_4823_ == 0)
{
lean_dec_ref(v___x_4820_);
goto v___jp_4775_;
}
else
{
uint8_t v_zetaHave_4824_; 
v_zetaHave_4824_ = lean_ctor_get_uint8(v___x_4820_, 18);
if (v_zetaHave_4824_ == 0)
{
lean_dec_ref(v___x_4820_);
goto v___jp_4775_;
}
else
{
uint8_t v_zetaDelta_4825_; 
v_zetaDelta_4825_ = lean_ctor_get_uint8(v___x_4820_, 16);
if (v_zetaDelta_4825_ == 0)
{
lean_dec_ref(v___x_4820_);
goto v___jp_4775_;
}
else
{
uint8_t v_etaStruct_4826_; uint8_t v_proj_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; uint8_t v___x_4830_; 
v_etaStruct_4826_ = lean_ctor_get_uint8(v___x_4820_, 10);
v_proj_4827_ = lean_ctor_get_uint8(v___x_4820_, 14);
lean_dec_ref(v___x_4820_);
v___x_4828_ = l_Lean_Meta_ProjReductionKind_ctorIdx(v_proj_4827_);
v___x_4829_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___closed__0);
v___x_4830_ = lean_nat_dec_eq(v___x_4828_, v___x_4829_);
lean_dec(v___x_4828_);
if (v___x_4830_ == 0)
{
goto v___jp_4775_;
}
else
{
uint8_t v___x_4831_; uint8_t v___x_4832_; 
v___x_4831_ = 0;
v___x_4832_ = l_Lean_Meta_instBEqEtaStructMode_beq(v_etaStruct_4826_, v___x_4831_);
if (v___x_4832_ == 0)
{
goto v___jp_4775_;
}
else
{
lean_object* v___x_4833_; 
v___x_4833_ = lean_apply_5(v___f_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, lean_box(0));
return v___x_4833_;
}
}
}
}
}
}
}
v___jp_4775_:
{
lean_object* v___x_4776_; uint8_t v_foApprox_4777_; uint8_t v_ctxApprox_4778_; uint8_t v_quasiPatternApprox_4779_; uint8_t v_constApprox_4780_; uint8_t v_isDefEqStuckEx_4781_; uint8_t v_unificationHints_4782_; uint8_t v_proofIrrelevance_4783_; uint8_t v_assignSyntheticOpaque_4784_; uint8_t v_offsetCnstrs_4785_; uint8_t v_transparency_4786_; uint8_t v_univApprox_4787_; uint8_t v_zetaUnused_4788_; uint8_t v_canUnfoldPredicateConfig_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4819_; 
v___x_4776_ = l_Lean_Meta_Context_config(v___y_4770_);
v_foApprox_4777_ = lean_ctor_get_uint8(v___x_4776_, 0);
v_ctxApprox_4778_ = lean_ctor_get_uint8(v___x_4776_, 1);
v_quasiPatternApprox_4779_ = lean_ctor_get_uint8(v___x_4776_, 2);
v_constApprox_4780_ = lean_ctor_get_uint8(v___x_4776_, 3);
v_isDefEqStuckEx_4781_ = lean_ctor_get_uint8(v___x_4776_, 4);
v_unificationHints_4782_ = lean_ctor_get_uint8(v___x_4776_, 5);
v_proofIrrelevance_4783_ = lean_ctor_get_uint8(v___x_4776_, 6);
v_assignSyntheticOpaque_4784_ = lean_ctor_get_uint8(v___x_4776_, 7);
v_offsetCnstrs_4785_ = lean_ctor_get_uint8(v___x_4776_, 8);
v_transparency_4786_ = lean_ctor_get_uint8(v___x_4776_, 9);
v_univApprox_4787_ = lean_ctor_get_uint8(v___x_4776_, 11);
v_zetaUnused_4788_ = lean_ctor_get_uint8(v___x_4776_, 17);
v_canUnfoldPredicateConfig_4789_ = lean_ctor_get_uint8(v___x_4776_, 19);
v_isSharedCheck_4819_ = !lean_is_exclusive(v___x_4776_);
if (v_isSharedCheck_4819_ == 0)
{
v___x_4791_ = v___x_4776_;
v_isShared_4792_ = v_isSharedCheck_4819_;
goto v_resetjp_4790_;
}
else
{
lean_dec(v___x_4776_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4819_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
uint8_t v___x_4793_; uint8_t v___x_4794_; lean_object* v___x_4796_; 
v___x_4793_ = 0;
v___x_4794_ = 2;
if (v_isShared_4792_ == 0)
{
v___x_4796_ = v___x_4791_;
goto v_reusejp_4795_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 0, v_foApprox_4777_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 1, v_ctxApprox_4778_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 2, v_quasiPatternApprox_4779_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 3, v_constApprox_4780_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 4, v_isDefEqStuckEx_4781_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 5, v_unificationHints_4782_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 6, v_proofIrrelevance_4783_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 7, v_assignSyntheticOpaque_4784_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 8, v_offsetCnstrs_4785_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 9, v_transparency_4786_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 11, v_univApprox_4787_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 17, v_zetaUnused_4788_);
lean_ctor_set_uint8(v_reuseFailAlloc_4818_, 19, v_canUnfoldPredicateConfig_4789_);
v___x_4796_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4795_;
}
v_reusejp_4795_:
{
uint8_t v_trackZetaDelta_4797_; lean_object* v_zetaDeltaSet_4798_; lean_object* v_lctx_4799_; lean_object* v_localInstances_4800_; lean_object* v_defEqCtx_x3f_4801_; lean_object* v_synthPendingDepth_4802_; lean_object* v_customCanUnfoldPredicate_x3f_4803_; uint8_t v_univApprox_4804_; uint8_t v_inTypeClassResolution_4805_; uint8_t v_cacheInferType_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4816_; 
lean_ctor_set_uint8(v___x_4796_, 10, v___x_4793_);
lean_ctor_set_uint8(v___x_4796_, 12, v___x_4768_);
lean_ctor_set_uint8(v___x_4796_, 13, v___x_4768_);
lean_ctor_set_uint8(v___x_4796_, 14, v___x_4794_);
lean_ctor_set_uint8(v___x_4796_, 15, v___x_4768_);
lean_ctor_set_uint8(v___x_4796_, 16, v___x_4768_);
lean_ctor_set_uint8(v___x_4796_, 18, v___x_4768_);
v_trackZetaDelta_4797_ = lean_ctor_get_uint8(v___y_4770_, sizeof(void*)*7);
v_zetaDeltaSet_4798_ = lean_ctor_get(v___y_4770_, 1);
v_lctx_4799_ = lean_ctor_get(v___y_4770_, 2);
v_localInstances_4800_ = lean_ctor_get(v___y_4770_, 3);
v_defEqCtx_x3f_4801_ = lean_ctor_get(v___y_4770_, 4);
v_synthPendingDepth_4802_ = lean_ctor_get(v___y_4770_, 5);
v_customCanUnfoldPredicate_x3f_4803_ = lean_ctor_get(v___y_4770_, 6);
v_univApprox_4804_ = lean_ctor_get_uint8(v___y_4770_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4805_ = lean_ctor_get_uint8(v___y_4770_, sizeof(void*)*7 + 2);
v_cacheInferType_4806_ = lean_ctor_get_uint8(v___y_4770_, sizeof(void*)*7 + 3);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___y_4770_);
if (v_isSharedCheck_4816_ == 0)
{
lean_object* v_unused_4817_; 
v_unused_4817_ = lean_ctor_get(v___y_4770_, 0);
lean_dec(v_unused_4817_);
v___x_4808_ = v___y_4770_;
v_isShared_4809_ = v_isSharedCheck_4816_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_customCanUnfoldPredicate_x3f_4803_);
lean_inc(v_synthPendingDepth_4802_);
lean_inc(v_defEqCtx_x3f_4801_);
lean_inc(v_localInstances_4800_);
lean_inc(v_lctx_4799_);
lean_inc(v_zetaDeltaSet_4798_);
lean_dec(v___y_4770_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4816_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
uint64_t v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4813_; 
v___x_4810_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4796_);
v___x_4811_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4811_, 0, v___x_4796_);
lean_ctor_set_uint64(v___x_4811_, sizeof(void*)*1, v___x_4810_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set(v___x_4808_, 0, v___x_4811_);
v___x_4813_ = v___x_4808_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4811_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_zetaDeltaSet_4798_);
lean_ctor_set(v_reuseFailAlloc_4815_, 2, v_lctx_4799_);
lean_ctor_set(v_reuseFailAlloc_4815_, 3, v_localInstances_4800_);
lean_ctor_set(v_reuseFailAlloc_4815_, 4, v_defEqCtx_x3f_4801_);
lean_ctor_set(v_reuseFailAlloc_4815_, 5, v_synthPendingDepth_4802_);
lean_ctor_set(v_reuseFailAlloc_4815_, 6, v_customCanUnfoldPredicate_x3f_4803_);
lean_ctor_set_uint8(v_reuseFailAlloc_4815_, sizeof(void*)*7, v_trackZetaDelta_4797_);
lean_ctor_set_uint8(v_reuseFailAlloc_4815_, sizeof(void*)*7 + 1, v_univApprox_4804_);
lean_ctor_set_uint8(v_reuseFailAlloc_4815_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4805_);
lean_ctor_set_uint8(v_reuseFailAlloc_4815_, sizeof(void*)*7 + 3, v_cacheInferType_4806_);
v___x_4813_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4814_; 
v___x_4814_ = lean_apply_5(v___f_4769_, v___x_4813_, v___y_4771_, v___y_4772_, v___y_4773_, lean_box(0));
return v___x_4814_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3___boxed(lean_object* v___x_4834_, lean_object* v___f_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
uint8_t v___x_14076__boxed_4841_; lean_object* v_res_4842_; 
v___x_14076__boxed_4841_ = lean_unbox(v___x_4834_);
v_res_4842_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_14076__boxed_4841_, v___f_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
return v_res_4842_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__1));
v___x_4847_ = l_Lean_MessageData_ofFormat(v___x_4846_);
return v___x_4847_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3(void){
_start:
{
lean_object* v___x_4848_; 
v___x_4848_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4848_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4(void){
_start:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4849_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__3);
v___x_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4849_);
return v___x_4850_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5(void){
_start:
{
lean_object* v___x_4851_; lean_object* v___x_4852_; 
v___x_4851_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__4);
v___x_4852_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4852_, 0, v___x_4851_);
lean_ctor_set(v___x_4852_, 1, v___x_4851_);
lean_ctor_set(v___x_4852_, 2, v___x_4851_);
lean_ctor_set(v___x_4852_, 3, v___x_4851_);
lean_ctor_set(v___x_4852_, 4, v___x_4851_);
lean_ctor_set(v___x_4852_, 5, v___x_4851_);
return v___x_4852_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6(void){
_start:
{
lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4853_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitDepExpr_spec__3___redArg___closed__1);
v___x_4854_ = lean_unsigned_to_nat(0u);
v___x_4855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
lean_ctor_set(v___x_4855_, 1, v___x_4853_);
return v___x_4855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(uint8_t v___x_4856_, lean_object* v_e_4857_, lean_object* v_cls_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
if (v___x_4856_ == 0)
{
lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; 
lean_dec(v_cls_4858_);
v___x_4864_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__2);
v___x_4865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4865_, 0, v_e_4857_);
lean_ctor_set(v___x_4865_, 1, v___x_4864_);
v___x_4866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4865_);
return v___x_4866_;
}
else
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v_mctx_4869_; lean_object* v_zetaDeltaFVarIds_4870_; lean_object* v_postponed_4871_; lean_object* v_diag_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4969_; 
v___x_4867_ = lean_st_ref_get(v___y_4860_);
v___x_4868_ = lean_st_ref_take(v___y_4860_);
v_mctx_4869_ = lean_ctor_get(v___x_4868_, 0);
v_zetaDeltaFVarIds_4870_ = lean_ctor_get(v___x_4868_, 2);
v_postponed_4871_ = lean_ctor_get(v___x_4868_, 3);
v_diag_4872_ = lean_ctor_get(v___x_4868_, 4);
v_isSharedCheck_4969_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4969_ == 0)
{
lean_object* v_unused_4970_; 
v_unused_4970_ = lean_ctor_get(v___x_4868_, 1);
lean_dec(v_unused_4970_);
v___x_4874_ = v___x_4868_;
v_isShared_4875_ = v_isSharedCheck_4969_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_diag_4872_);
lean_inc(v_postponed_4871_);
lean_inc(v_zetaDeltaFVarIds_4870_);
lean_inc(v_mctx_4869_);
lean_dec(v___x_4868_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4969_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; lean_object* v___x_4878_; 
v___x_4876_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__5);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 1, v___x_4876_);
v___x_4878_ = v___x_4874_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4968_; 
v_reuseFailAlloc_4968_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_mctx_4869_);
lean_ctor_set(v_reuseFailAlloc_4968_, 1, v___x_4876_);
lean_ctor_set(v_reuseFailAlloc_4968_, 2, v_zetaDeltaFVarIds_4870_);
lean_ctor_set(v_reuseFailAlloc_4968_, 3, v_postponed_4871_);
lean_ctor_set(v_reuseFailAlloc_4968_, 4, v_diag_4872_);
v___x_4878_ = v_reuseFailAlloc_4968_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v_mctx_4881_; lean_object* v_cache_4882_; lean_object* v_zetaDeltaFVarIds_4883_; lean_object* v_postponed_4884_; lean_object* v_diag_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4967_; 
v___x_4879_ = lean_st_ref_put(v___y_4860_, v___x_4878_);
v___x_4880_ = lean_st_ref_take(v___y_4860_);
v_mctx_4881_ = lean_ctor_get(v___x_4880_, 0);
v_cache_4882_ = lean_ctor_get(v___x_4880_, 1);
v_zetaDeltaFVarIds_4883_ = lean_ctor_get(v___x_4880_, 2);
v_postponed_4884_ = lean_ctor_get(v___x_4880_, 3);
v_diag_4885_ = lean_ctor_get(v___x_4880_, 4);
v_isSharedCheck_4967_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4967_ == 0)
{
v___x_4887_ = v___x_4880_;
v_isShared_4888_ = v_isSharedCheck_4967_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_diag_4885_);
lean_inc(v_postponed_4884_);
lean_inc(v_zetaDeltaFVarIds_4883_);
lean_inc(v_cache_4882_);
lean_inc(v_mctx_4881_);
lean_dec(v___x_4880_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4967_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4889_; lean_object* v___x_4891_; 
v___x_4889_ = lean_box(1);
if (v_isShared_4888_ == 0)
{
lean_ctor_set(v___x_4887_, 2, v___x_4889_);
v___x_4891_ = v___x_4887_;
goto v_reusejp_4890_;
}
else
{
lean_object* v_reuseFailAlloc_4966_; 
v_reuseFailAlloc_4966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4966_, 0, v_mctx_4881_);
lean_ctor_set(v_reuseFailAlloc_4966_, 1, v_cache_4882_);
lean_ctor_set(v_reuseFailAlloc_4966_, 2, v___x_4889_);
lean_ctor_set(v_reuseFailAlloc_4966_, 3, v_postponed_4884_);
lean_ctor_set(v_reuseFailAlloc_4966_, 4, v_diag_4885_);
v___x_4891_ = v_reuseFailAlloc_4966_;
goto v_reusejp_4890_;
}
v_reusejp_4890_:
{
lean_object* v___x_4892_; lean_object* v_cache_4893_; lean_object* v_keyedConfig_4894_; lean_object* v_zetaDeltaSet_4895_; lean_object* v_lctx_4896_; lean_object* v_localInstances_4897_; lean_object* v_defEqCtx_x3f_4898_; lean_object* v_synthPendingDepth_4899_; lean_object* v_customCanUnfoldPredicate_x3f_4900_; uint8_t v_univApprox_4901_; uint8_t v_inTypeClassResolution_4902_; uint8_t v_cacheInferType_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; uint8_t v_transparency_4906_; lean_object* v___x_4907_; uint8_t v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___f_4911_; lean_object* v_a_4913_; lean_object* v_a_4925_; lean_object* v_a_4938_; lean_object* v___y_4942_; lean_object* v___y_4946_; uint8_t v___x_4949_; 
v___x_4892_ = lean_st_ref_put(v___y_4860_, v___x_4891_);
v_cache_4893_ = lean_ctor_get(v___x_4867_, 1);
lean_inc_ref(v_cache_4893_);
lean_dec(v___x_4867_);
v_keyedConfig_4894_ = lean_ctor_get(v___y_4859_, 0);
v_zetaDeltaSet_4895_ = lean_ctor_get(v___y_4859_, 1);
v_lctx_4896_ = lean_ctor_get(v___y_4859_, 2);
v_localInstances_4897_ = lean_ctor_get(v___y_4859_, 3);
v_defEqCtx_x3f_4898_ = lean_ctor_get(v___y_4859_, 4);
v_synthPendingDepth_4899_ = lean_ctor_get(v___y_4859_, 5);
v_customCanUnfoldPredicate_x3f_4900_ = lean_ctor_get(v___y_4859_, 6);
v_univApprox_4901_ = lean_ctor_get_uint8(v___y_4859_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4902_ = lean_ctor_get_uint8(v___y_4859_, sizeof(void*)*7 + 2);
v_cacheInferType_4903_ = lean_ctor_get_uint8(v___y_4859_, sizeof(void*)*7 + 3);
lean_inc(v_customCanUnfoldPredicate_x3f_4900_);
lean_inc(v_synthPendingDepth_4899_);
lean_inc(v_defEqCtx_x3f_4898_);
lean_inc_ref(v_localInstances_4897_);
lean_inc_ref(v_lctx_4896_);
lean_inc(v_zetaDeltaSet_4895_);
lean_inc_ref(v_keyedConfig_4894_);
v___x_4904_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4904_, 0, v_keyedConfig_4894_);
lean_ctor_set(v___x_4904_, 1, v_zetaDeltaSet_4895_);
lean_ctor_set(v___x_4904_, 2, v_lctx_4896_);
lean_ctor_set(v___x_4904_, 3, v_localInstances_4897_);
lean_ctor_set(v___x_4904_, 4, v_defEqCtx_x3f_4898_);
lean_ctor_set(v___x_4904_, 5, v_synthPendingDepth_4899_);
lean_ctor_set(v___x_4904_, 6, v_customCanUnfoldPredicate_x3f_4900_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7, v___x_4856_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7 + 1, v_univApprox_4901_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4902_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7 + 3, v_cacheInferType_4903_);
v___x_4905_ = l_Lean_Meta_Context_config(v___x_4904_);
v_transparency_4906_ = lean_ctor_get_uint8(v___x_4905_, 9);
lean_dec_ref(v___x_4905_);
v___x_4907_ = lean_unsigned_to_nat(0u);
v___x_4908_ = 0;
v___x_4909_ = lean_box(0);
v___x_4910_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___closed__6);
v___f_4911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__1___boxed), 10, 5);
lean_closure_set(v___f_4911_, 0, v___x_4910_);
lean_closure_set(v___f_4911_, 1, v_e_4857_);
lean_closure_set(v___f_4911_, 2, v___x_4909_);
lean_closure_set(v___f_4911_, 3, v___x_4907_);
lean_closure_set(v___f_4911_, 4, v_cls_4858_);
v___x_4949_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4906_, v___x_4908_);
if (v___x_4949_ == 0)
{
lean_object* v___x_4950_; lean_object* v___x_4951_; lean_object* v___x_4952_; uint8_t v_transparency_4953_; uint8_t v___x_4954_; uint8_t v___x_4955_; 
lean_dec_ref_known(v___x_4904_, 7);
lean_inc_ref(v_keyedConfig_4894_);
v___x_4950_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4908_, v_keyedConfig_4894_);
lean_inc(v_customCanUnfoldPredicate_x3f_4900_);
lean_inc(v_synthPendingDepth_4899_);
lean_inc(v_defEqCtx_x3f_4898_);
lean_inc_ref(v_localInstances_4897_);
lean_inc_ref(v_lctx_4896_);
lean_inc(v_zetaDeltaSet_4895_);
lean_inc_ref(v___x_4950_);
v___x_4951_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4951_, 0, v___x_4950_);
lean_ctor_set(v___x_4951_, 1, v_zetaDeltaSet_4895_);
lean_ctor_set(v___x_4951_, 2, v_lctx_4896_);
lean_ctor_set(v___x_4951_, 3, v_localInstances_4897_);
lean_ctor_set(v___x_4951_, 4, v_defEqCtx_x3f_4898_);
lean_ctor_set(v___x_4951_, 5, v_synthPendingDepth_4899_);
lean_ctor_set(v___x_4951_, 6, v_customCanUnfoldPredicate_x3f_4900_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7, v___x_4856_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7 + 1, v_univApprox_4901_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4902_);
lean_ctor_set_uint8(v___x_4951_, sizeof(void*)*7 + 3, v_cacheInferType_4903_);
v___x_4952_ = l_Lean_Meta_Context_config(v___x_4951_);
v_transparency_4953_ = lean_ctor_get_uint8(v___x_4952_, 9);
lean_dec_ref(v___x_4952_);
v___x_4954_ = 1;
v___x_4955_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4953_, v___x_4954_);
if (v___x_4955_ == 0)
{
lean_object* v___x_4956_; 
lean_dec_ref(v___x_4950_);
lean_inc(v___y_4862_);
lean_inc_ref(v___y_4861_);
lean_inc(v___y_4860_);
v___x_4956_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4856_, v___f_4911_, v___x_4951_, v___y_4860_, v___y_4861_, v___y_4862_);
v___y_4946_ = v___x_4956_;
goto v___jp_4945_;
}
else
{
lean_object* v___x_4957_; lean_object* v___x_4958_; lean_object* v___x_4959_; 
lean_dec_ref_known(v___x_4951_, 7);
v___x_4957_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4954_, v___x_4950_);
lean_inc(v_customCanUnfoldPredicate_x3f_4900_);
lean_inc(v_synthPendingDepth_4899_);
lean_inc(v_defEqCtx_x3f_4898_);
lean_inc_ref(v_localInstances_4897_);
lean_inc_ref(v_lctx_4896_);
lean_inc(v_zetaDeltaSet_4895_);
v___x_4958_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4958_, 0, v___x_4957_);
lean_ctor_set(v___x_4958_, 1, v_zetaDeltaSet_4895_);
lean_ctor_set(v___x_4958_, 2, v_lctx_4896_);
lean_ctor_set(v___x_4958_, 3, v_localInstances_4897_);
lean_ctor_set(v___x_4958_, 4, v_defEqCtx_x3f_4898_);
lean_ctor_set(v___x_4958_, 5, v_synthPendingDepth_4899_);
lean_ctor_set(v___x_4958_, 6, v_customCanUnfoldPredicate_x3f_4900_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7, v___x_4856_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7 + 1, v_univApprox_4901_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4902_);
lean_ctor_set_uint8(v___x_4958_, sizeof(void*)*7 + 3, v_cacheInferType_4903_);
lean_inc(v___y_4862_);
lean_inc_ref(v___y_4861_);
lean_inc(v___y_4860_);
v___x_4959_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4856_, v___f_4911_, v___x_4958_, v___y_4860_, v___y_4861_, v___y_4862_);
v___y_4946_ = v___x_4959_;
goto v___jp_4945_;
}
}
else
{
uint8_t v___x_4960_; uint8_t v___x_4961_; 
v___x_4960_ = 1;
v___x_4961_ = l_Lean_Meta_TransparencyMode_lt(v_transparency_4906_, v___x_4960_);
if (v___x_4961_ == 0)
{
lean_object* v___x_4962_; 
lean_inc(v___y_4862_);
lean_inc_ref(v___y_4861_);
lean_inc(v___y_4860_);
v___x_4962_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4949_, v___f_4911_, v___x_4904_, v___y_4860_, v___y_4861_, v___y_4862_);
v___y_4942_ = v___x_4962_;
goto v___jp_4941_;
}
else
{
lean_object* v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
lean_dec_ref_known(v___x_4904_, 7);
lean_inc_ref(v_keyedConfig_4894_);
v___x_4963_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4960_, v_keyedConfig_4894_);
lean_inc(v_customCanUnfoldPredicate_x3f_4900_);
lean_inc(v_synthPendingDepth_4899_);
lean_inc(v_defEqCtx_x3f_4898_);
lean_inc_ref(v_localInstances_4897_);
lean_inc_ref(v_lctx_4896_);
lean_inc(v_zetaDeltaSet_4895_);
v___x_4964_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4964_, 0, v___x_4963_);
lean_ctor_set(v___x_4964_, 1, v_zetaDeltaSet_4895_);
lean_ctor_set(v___x_4964_, 2, v_lctx_4896_);
lean_ctor_set(v___x_4964_, 3, v_localInstances_4897_);
lean_ctor_set(v___x_4964_, 4, v_defEqCtx_x3f_4898_);
lean_ctor_set(v___x_4964_, 5, v_synthPendingDepth_4899_);
lean_ctor_set(v___x_4964_, 6, v_customCanUnfoldPredicate_x3f_4900_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*7, v___x_4856_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*7 + 1, v_univApprox_4901_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4902_);
lean_ctor_set_uint8(v___x_4964_, sizeof(void*)*7 + 3, v_cacheInferType_4903_);
lean_inc(v___y_4862_);
lean_inc_ref(v___y_4861_);
lean_inc(v___y_4860_);
v___x_4965_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__3(v___x_4949_, v___f_4911_, v___x_4964_, v___y_4860_, v___y_4861_, v___y_4862_);
v___y_4942_ = v___x_4965_;
goto v___jp_4941_;
}
}
v___jp_4912_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
v___x_4914_ = lean_box(0);
v___x_4915_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4860_, v_cache_4893_, v___x_4914_);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4915_);
if (v_isSharedCheck_4922_ == 0)
{
lean_object* v_unused_4923_; 
v_unused_4923_ = lean_ctor_get(v___x_4915_, 0);
lean_dec(v_unused_4923_);
v___x_4917_ = v___x_4915_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_dec(v___x_4915_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
lean_ctor_set_tag(v___x_4917_, 1);
lean_ctor_set(v___x_4917_, 0, v_a_4913_);
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4913_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
v___jp_4924_:
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4930_; uint8_t v_isShared_4931_; uint8_t v_isSharedCheck_4935_; 
lean_inc(v_a_4925_);
v___x_4926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4926_, 0, v_a_4925_);
v___x_4927_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4860_, v_zetaDeltaFVarIds_4883_, v___x_4926_);
lean_dec_ref(v___x_4927_);
v___x_4928_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__2(v___y_4860_, v_cache_4893_, v___x_4926_);
lean_dec_ref_known(v___x_4926_, 1);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4935_ == 0)
{
lean_object* v_unused_4936_; 
v_unused_4936_ = lean_ctor_get(v___x_4928_, 0);
lean_dec(v_unused_4936_);
v___x_4930_ = v___x_4928_;
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
else
{
lean_dec(v___x_4928_);
v___x_4930_ = lean_box(0);
v_isShared_4931_ = v_isSharedCheck_4935_;
goto v_resetjp_4929_;
}
v_resetjp_4929_:
{
lean_object* v___x_4933_; 
if (v_isShared_4931_ == 0)
{
lean_ctor_set(v___x_4930_, 0, v_a_4925_);
v___x_4933_ = v___x_4930_;
goto v_reusejp_4932_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_a_4925_);
v___x_4933_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4932_;
}
v_reusejp_4932_:
{
return v___x_4933_;
}
}
}
v___jp_4937_:
{
lean_object* v___x_4939_; lean_object* v___x_4940_; 
v___x_4939_ = lean_box(0);
v___x_4940_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__0(v___y_4860_, v_zetaDeltaFVarIds_4883_, v___x_4939_);
lean_dec_ref(v___x_4940_);
v_a_4913_ = v_a_4938_;
goto v___jp_4912_;
}
v___jp_4941_:
{
if (lean_obj_tag(v___y_4942_) == 0)
{
lean_object* v_a_4943_; 
v_a_4943_ = lean_ctor_get(v___y_4942_, 0);
lean_inc(v_a_4943_);
lean_dec_ref_known(v___y_4942_, 1);
v_a_4925_ = v_a_4943_;
goto v___jp_4924_;
}
else
{
lean_object* v_a_4944_; 
v_a_4944_ = lean_ctor_get(v___y_4942_, 0);
lean_inc(v_a_4944_);
lean_dec_ref_known(v___y_4942_, 1);
v_a_4938_ = v_a_4944_;
goto v___jp_4937_;
}
}
v___jp_4945_:
{
if (lean_obj_tag(v___y_4946_) == 0)
{
lean_object* v_a_4947_; 
v_a_4947_ = lean_ctor_get(v___y_4946_, 0);
lean_inc(v_a_4947_);
lean_dec_ref_known(v___y_4946_, 1);
v_a_4925_ = v_a_4947_;
goto v___jp_4924_;
}
else
{
lean_object* v_a_4948_; 
v_a_4948_ = lean_ctor_get(v___y_4946_, 0);
lean_inc(v_a_4948_);
lean_dec_ref_known(v___y_4946_, 1);
v_a_4938_ = v_a_4948_;
goto v___jp_4937_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5___boxed(lean_object* v___x_4971_, lean_object* v_e_4972_, lean_object* v_cls_4973_, lean_object* v___y_4974_, lean_object* v___y_4975_, lean_object* v___y_4976_, lean_object* v___y_4977_, lean_object* v___y_4978_){
_start:
{
uint8_t v___x_14199__boxed_4979_; lean_object* v_res_4980_; 
v___x_14199__boxed_4979_ = lean_unbox(v___x_4971_);
v_res_4980_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_14199__boxed_4979_, v_e_4972_, v_cls_4973_, v___y_4974_, v___y_4975_, v___y_4976_, v___y_4977_);
lean_dec(v___y_4977_);
lean_dec_ref(v___y_4976_);
lean_dec(v___y_4975_);
lean_dec_ref(v___y_4974_);
return v_res_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(lean_object* v_x_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_, lean_object* v___y_4984_, lean_object* v___y_4985_){
_start:
{
if (lean_obj_tag(v_x_4981_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4995_; 
v_a_4987_ = lean_ctor_get(v_x_4981_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v_x_4981_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4989_ = v_x_4981_;
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v_x_4981_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4993_; 
v___x_4991_ = l_Lean_Exception_toMessageData(v_a_4987_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v___x_4991_);
v___x_4993_ = v___x_4989_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v___x_4991_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
else
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5004_; 
v_a_4996_ = lean_ctor_get(v_x_4981_, 0);
v_isSharedCheck_5004_ = !lean_is_exclusive(v_x_4981_);
if (v_isSharedCheck_5004_ == 0)
{
v___x_4998_ = v_x_4981_;
v_isShared_4999_ = v_isSharedCheck_5004_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v_x_4981_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5004_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v_snd_5000_; lean_object* v___x_5002_; 
v_snd_5000_ = lean_ctor_get(v_a_4996_, 1);
lean_inc(v_snd_5000_);
lean_dec(v_a_4996_);
if (v_isShared_4999_ == 0)
{
lean_ctor_set_tag(v___x_4998_, 0);
lean_ctor_set(v___x_4998_, 0, v_snd_5000_);
v___x_5002_ = v___x_4998_;
goto v_reusejp_5001_;
}
else
{
lean_object* v_reuseFailAlloc_5003_; 
v_reuseFailAlloc_5003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5003_, 0, v_snd_5000_);
v___x_5002_ = v_reuseFailAlloc_5003_;
goto v_reusejp_5001_;
}
v_reusejp_5001_:
{
return v___x_5002_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4___boxed(lean_object* v_x_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__4(v_x_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
lean_dec(v___y_5007_);
lean_dec_ref(v___y_5006_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(lean_object* v_x_5012_){
_start:
{
if (lean_obj_tag(v_x_5012_) == 0)
{
lean_object* v_a_5014_; lean_object* v___x_5016_; uint8_t v_isShared_5017_; uint8_t v_isSharedCheck_5021_; 
v_a_5014_ = lean_ctor_get(v_x_5012_, 0);
v_isSharedCheck_5021_ = !lean_is_exclusive(v_x_5012_);
if (v_isSharedCheck_5021_ == 0)
{
v___x_5016_ = v_x_5012_;
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
else
{
lean_inc(v_a_5014_);
lean_dec(v_x_5012_);
v___x_5016_ = lean_box(0);
v_isShared_5017_ = v_isSharedCheck_5021_;
goto v_resetjp_5015_;
}
v_resetjp_5015_:
{
lean_object* v___x_5019_; 
if (v_isShared_5017_ == 0)
{
lean_ctor_set_tag(v___x_5016_, 1);
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
else
{
lean_object* v_a_5022_; lean_object* v___x_5024_; uint8_t v_isShared_5025_; uint8_t v_isSharedCheck_5029_; 
v_a_5022_ = lean_ctor_get(v_x_5012_, 0);
v_isSharedCheck_5029_ = !lean_is_exclusive(v_x_5012_);
if (v_isSharedCheck_5029_ == 0)
{
v___x_5024_ = v_x_5012_;
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
else
{
lean_inc(v_a_5022_);
lean_dec(v_x_5012_);
v___x_5024_ = lean_box(0);
v_isShared_5025_ = v_isSharedCheck_5029_;
goto v_resetjp_5023_;
}
v_resetjp_5023_:
{
lean_object* v___x_5027_; 
if (v_isShared_5025_ == 0)
{
lean_ctor_set_tag(v___x_5024_, 0);
v___x_5027_ = v___x_5024_;
goto v_reusejp_5026_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v_a_5022_);
v___x_5027_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5026_;
}
v_reusejp_5026_:
{
return v___x_5027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg___boxed(lean_object* v_x_5030_, lean_object* v___y_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5030_);
return v_res_5032_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(lean_object* v_e_5033_){
_start:
{
if (lean_obj_tag(v_e_5033_) == 0)
{
uint8_t v___x_5034_; 
v___x_5034_ = 2;
return v___x_5034_;
}
else
{
uint8_t v___x_5035_; 
v___x_5035_ = 0;
return v___x_5035_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4___boxed(lean_object* v_e_5036_){
_start:
{
uint8_t v_res_5037_; lean_object* v_r_5038_; 
v_res_5037_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_e_5036_);
lean_dec_ref(v_e_5036_);
v_r_5038_ = lean_box(v_res_5037_);
return v_r_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(lean_object* v_oldTraces_5039_, lean_object* v_data_5040_, lean_object* v_ref_5041_, lean_object* v_msg_5042_, lean_object* v___y_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_, lean_object* v___y_5046_){
_start:
{
lean_object* v_toCold_5048_; lean_object* v_options_5049_; lean_object* v_currRecDepth_5050_; lean_object* v_maxRecDepth_5051_; lean_object* v_ref_5052_; lean_object* v_currNamespace_5053_; lean_object* v_openDecls_5054_; lean_object* v_initHeartbeats_5055_; lean_object* v_maxHeartbeats_5056_; lean_object* v_currMacroScope_5057_; uint8_t v_diag_5058_; uint8_t v_suppressElabErrors_5059_; lean_object* v___x_5060_; lean_object* v_traceState_5061_; lean_object* v_traces_5062_; lean_object* v_ref_5063_; lean_object* v___x_5064_; lean_object* v___x_5065_; size_t v_sz_5066_; size_t v___x_5067_; lean_object* v___x_5068_; lean_object* v_msg_5069_; lean_object* v___x_5070_; lean_object* v_a_5071_; lean_object* v___x_5073_; uint8_t v_isShared_5074_; uint8_t v_isSharedCheck_5108_; 
v_toCold_5048_ = lean_ctor_get(v___y_5045_, 0);
v_options_5049_ = lean_ctor_get(v___y_5045_, 1);
v_currRecDepth_5050_ = lean_ctor_get(v___y_5045_, 2);
v_maxRecDepth_5051_ = lean_ctor_get(v___y_5045_, 3);
v_ref_5052_ = lean_ctor_get(v___y_5045_, 4);
v_currNamespace_5053_ = lean_ctor_get(v___y_5045_, 5);
v_openDecls_5054_ = lean_ctor_get(v___y_5045_, 6);
v_initHeartbeats_5055_ = lean_ctor_get(v___y_5045_, 7);
v_maxHeartbeats_5056_ = lean_ctor_get(v___y_5045_, 8);
v_currMacroScope_5057_ = lean_ctor_get(v___y_5045_, 9);
v_diag_5058_ = lean_ctor_get_uint8(v___y_5045_, sizeof(void*)*10);
v_suppressElabErrors_5059_ = lean_ctor_get_uint8(v___y_5045_, sizeof(void*)*10 + 1);
v___x_5060_ = lean_st_ref_get(v___y_5046_);
v_traceState_5061_ = lean_ctor_get(v___x_5060_, 4);
lean_inc_ref(v_traceState_5061_);
lean_dec(v___x_5060_);
v_traces_5062_ = lean_ctor_get(v_traceState_5061_, 0);
lean_inc_ref(v_traces_5062_);
lean_dec_ref(v_traceState_5061_);
v_ref_5063_ = l_Lean_replaceRef(v_ref_5041_, v_ref_5052_);
lean_inc(v_currMacroScope_5057_);
lean_inc(v_maxHeartbeats_5056_);
lean_inc(v_initHeartbeats_5055_);
lean_inc(v_openDecls_5054_);
lean_inc(v_currNamespace_5053_);
lean_inc(v_maxRecDepth_5051_);
lean_inc(v_currRecDepth_5050_);
lean_inc_ref(v_options_5049_);
lean_inc_ref(v_toCold_5048_);
v___x_5064_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_5064_, 0, v_toCold_5048_);
lean_ctor_set(v___x_5064_, 1, v_options_5049_);
lean_ctor_set(v___x_5064_, 2, v_currRecDepth_5050_);
lean_ctor_set(v___x_5064_, 3, v_maxRecDepth_5051_);
lean_ctor_set(v___x_5064_, 4, v_ref_5063_);
lean_ctor_set(v___x_5064_, 5, v_currNamespace_5053_);
lean_ctor_set(v___x_5064_, 6, v_openDecls_5054_);
lean_ctor_set(v___x_5064_, 7, v_initHeartbeats_5055_);
lean_ctor_set(v___x_5064_, 8, v_maxHeartbeats_5056_);
lean_ctor_set(v___x_5064_, 9, v_currMacroScope_5057_);
lean_ctor_set_uint8(v___x_5064_, sizeof(void*)*10, v_diag_5058_);
lean_ctor_set_uint8(v___x_5064_, sizeof(void*)*10 + 1, v_suppressElabErrors_5059_);
v___x_5065_ = l_Lean_PersistentArray_toArray___redArg(v_traces_5062_);
lean_dec_ref(v_traces_5062_);
v_sz_5066_ = lean_array_size(v___x_5065_);
v___x_5067_ = ((size_t)0ULL);
v___x_5068_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__13_spec__15(v_sz_5066_, v___x_5067_, v___x_5065_);
v_msg_5069_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_5069_, 0, v_data_5040_);
lean_ctor_set(v_msg_5069_, 1, v_msg_5042_);
lean_ctor_set(v_msg_5069_, 2, v___x_5068_);
v___x_5070_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitConst_spec__0_spec__0_spec__2_spec__3_spec__5_spec__7_spec__8(v_msg_5069_, v___y_5043_, v___y_5044_, v___x_5064_, v___y_5046_);
lean_dec_ref_known(v___x_5064_, 10);
v_a_5071_ = lean_ctor_get(v___x_5070_, 0);
v_isSharedCheck_5108_ = !lean_is_exclusive(v___x_5070_);
if (v_isSharedCheck_5108_ == 0)
{
v___x_5073_ = v___x_5070_;
v_isShared_5074_ = v_isSharedCheck_5108_;
goto v_resetjp_5072_;
}
else
{
lean_inc(v_a_5071_);
lean_dec(v___x_5070_);
v___x_5073_ = lean_box(0);
v_isShared_5074_ = v_isSharedCheck_5108_;
goto v_resetjp_5072_;
}
v_resetjp_5072_:
{
lean_object* v___x_5075_; lean_object* v_traceState_5076_; lean_object* v_env_5077_; lean_object* v_nextMacroScope_5078_; lean_object* v_ngen_5079_; lean_object* v_auxDeclNGen_5080_; lean_object* v_cache_5081_; lean_object* v_messages_5082_; lean_object* v_infoState_5083_; lean_object* v_snapshotTasks_5084_; lean_object* v___x_5086_; uint8_t v_isShared_5087_; uint8_t v_isSharedCheck_5107_; 
v___x_5075_ = lean_st_ref_take(v___y_5046_);
v_traceState_5076_ = lean_ctor_get(v___x_5075_, 4);
v_env_5077_ = lean_ctor_get(v___x_5075_, 0);
v_nextMacroScope_5078_ = lean_ctor_get(v___x_5075_, 1);
v_ngen_5079_ = lean_ctor_get(v___x_5075_, 2);
v_auxDeclNGen_5080_ = lean_ctor_get(v___x_5075_, 3);
v_cache_5081_ = lean_ctor_get(v___x_5075_, 5);
v_messages_5082_ = lean_ctor_get(v___x_5075_, 6);
v_infoState_5083_ = lean_ctor_get(v___x_5075_, 7);
v_snapshotTasks_5084_ = lean_ctor_get(v___x_5075_, 8);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5075_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5086_ = v___x_5075_;
v_isShared_5087_ = v_isSharedCheck_5107_;
goto v_resetjp_5085_;
}
else
{
lean_inc(v_snapshotTasks_5084_);
lean_inc(v_infoState_5083_);
lean_inc(v_messages_5082_);
lean_inc(v_cache_5081_);
lean_inc(v_traceState_5076_);
lean_inc(v_auxDeclNGen_5080_);
lean_inc(v_ngen_5079_);
lean_inc(v_nextMacroScope_5078_);
lean_inc(v_env_5077_);
lean_dec(v___x_5075_);
v___x_5086_ = lean_box(0);
v_isShared_5087_ = v_isSharedCheck_5107_;
goto v_resetjp_5085_;
}
v_resetjp_5085_:
{
uint64_t v_tid_5088_; lean_object* v___x_5090_; uint8_t v_isShared_5091_; uint8_t v_isSharedCheck_5105_; 
v_tid_5088_ = lean_ctor_get_uint64(v_traceState_5076_, sizeof(void*)*1);
v_isSharedCheck_5105_ = !lean_is_exclusive(v_traceState_5076_);
if (v_isSharedCheck_5105_ == 0)
{
lean_object* v_unused_5106_; 
v_unused_5106_ = lean_ctor_get(v_traceState_5076_, 0);
lean_dec(v_unused_5106_);
v___x_5090_ = v_traceState_5076_;
v_isShared_5091_ = v_isSharedCheck_5105_;
goto v_resetjp_5089_;
}
else
{
lean_dec(v_traceState_5076_);
v___x_5090_ = lean_box(0);
v_isShared_5091_ = v_isSharedCheck_5105_;
goto v_resetjp_5089_;
}
v_resetjp_5089_:
{
lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v___x_5095_; 
v___x_5092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5092_, 0, v_ref_5041_);
lean_ctor_set(v___x_5092_, 1, v_a_5071_);
v___x_5093_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_5039_, v___x_5092_);
if (v_isShared_5091_ == 0)
{
lean_ctor_set(v___x_5090_, 0, v___x_5093_);
v___x_5095_ = v___x_5090_;
goto v_reusejp_5094_;
}
else
{
lean_object* v_reuseFailAlloc_5104_; 
v_reuseFailAlloc_5104_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5104_, 0, v___x_5093_);
lean_ctor_set_uint64(v_reuseFailAlloc_5104_, sizeof(void*)*1, v_tid_5088_);
v___x_5095_ = v_reuseFailAlloc_5104_;
goto v_reusejp_5094_;
}
v_reusejp_5094_:
{
lean_object* v___x_5097_; 
if (v_isShared_5087_ == 0)
{
lean_ctor_set(v___x_5086_, 4, v___x_5095_);
v___x_5097_ = v___x_5086_;
goto v_reusejp_5096_;
}
else
{
lean_object* v_reuseFailAlloc_5103_; 
v_reuseFailAlloc_5103_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5103_, 0, v_env_5077_);
lean_ctor_set(v_reuseFailAlloc_5103_, 1, v_nextMacroScope_5078_);
lean_ctor_set(v_reuseFailAlloc_5103_, 2, v_ngen_5079_);
lean_ctor_set(v_reuseFailAlloc_5103_, 3, v_auxDeclNGen_5080_);
lean_ctor_set(v_reuseFailAlloc_5103_, 4, v___x_5095_);
lean_ctor_set(v_reuseFailAlloc_5103_, 5, v_cache_5081_);
lean_ctor_set(v_reuseFailAlloc_5103_, 6, v_messages_5082_);
lean_ctor_set(v_reuseFailAlloc_5103_, 7, v_infoState_5083_);
lean_ctor_set(v_reuseFailAlloc_5103_, 8, v_snapshotTasks_5084_);
v___x_5097_ = v_reuseFailAlloc_5103_;
goto v_reusejp_5096_;
}
v_reusejp_5096_:
{
lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v___x_5101_; 
v___x_5098_ = lean_st_ref_put(v___y_5046_, v___x_5097_);
v___x_5099_ = lean_box(0);
if (v_isShared_5074_ == 0)
{
lean_ctor_set(v___x_5073_, 0, v___x_5099_);
v___x_5101_ = v___x_5073_;
goto v_reusejp_5100_;
}
else
{
lean_object* v_reuseFailAlloc_5102_; 
v_reuseFailAlloc_5102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5102_, 0, v___x_5099_);
v___x_5101_ = v_reuseFailAlloc_5102_;
goto v_reusejp_5100_;
}
v_reusejp_5100_:
{
return v___x_5101_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2___boxed(lean_object* v_oldTraces_5109_, lean_object* v_data_5110_, lean_object* v_ref_5111_, lean_object* v_msg_5112_, lean_object* v___y_5113_, lean_object* v___y_5114_, lean_object* v___y_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v_res_5118_; 
v_res_5118_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5109_, v_data_5110_, v_ref_5111_, v_msg_5112_, v___y_5113_, v___y_5114_, v___y_5115_, v___y_5116_);
lean_dec(v___y_5116_);
lean_dec_ref(v___y_5115_);
lean_dec(v___y_5114_);
lean_dec_ref(v___y_5113_);
return v_res_5118_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(lean_object* v_cls_5119_, uint8_t v_collapsed_5120_, lean_object* v_tag_5121_, lean_object* v_opts_5122_, uint8_t v_clsEnabled_5123_, lean_object* v_oldTraces_5124_, lean_object* v_msg_5125_, lean_object* v_resStartStop_5126_, lean_object* v___y_5127_, lean_object* v___y_5128_, lean_object* v___y_5129_, lean_object* v___y_5130_){
_start:
{
lean_object* v_fst_5132_; lean_object* v_snd_5133_; lean_object* v___y_5135_; lean_object* v___y_5136_; lean_object* v_data_5137_; lean_object* v_fst_5148_; lean_object* v_snd_5149_; lean_object* v___x_5150_; uint8_t v___x_5151_; lean_object* v___y_5153_; lean_object* v_a_5154_; uint8_t v___y_5169_; double v___y_5200_; 
v_fst_5132_ = lean_ctor_get(v_resStartStop_5126_, 0);
lean_inc(v_fst_5132_);
v_snd_5133_ = lean_ctor_get(v_resStartStop_5126_, 1);
lean_inc(v_snd_5133_);
lean_dec_ref(v_resStartStop_5126_);
v_fst_5148_ = lean_ctor_get(v_snd_5133_, 0);
lean_inc(v_fst_5148_);
v_snd_5149_ = lean_ctor_get(v_snd_5133_, 1);
lean_inc(v_snd_5149_);
lean_dec(v_snd_5133_);
v___x_5150_ = l_Lean_trace_profiler;
v___x_5151_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5122_, v___x_5150_);
if (v___x_5151_ == 0)
{
v___y_5169_ = v___x_5151_;
goto v___jp_5168_;
}
else
{
lean_object* v___x_5205_; uint8_t v___x_5206_; 
v___x_5205_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5206_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_opts_5122_, v___x_5205_);
if (v___x_5206_ == 0)
{
lean_object* v___x_5207_; lean_object* v___x_5208_; double v___x_5209_; double v___x_5210_; double v___x_5211_; 
v___x_5207_ = l_Lean_trace_profiler_threshold;
v___x_5208_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5122_, v___x_5207_);
v___x_5209_ = lean_float_of_nat(v___x_5208_);
v___x_5210_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__2);
v___x_5211_ = lean_float_div(v___x_5209_, v___x_5210_);
v___y_5200_ = v___x_5211_;
goto v___jp_5199_;
}
else
{
lean_object* v___x_5212_; lean_object* v___x_5213_; double v___x_5214_; 
v___x_5212_ = l_Lean_trace_profiler_threshold;
v___x_5213_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6_spec__16(v_opts_5122_, v___x_5212_);
v___x_5214_ = lean_float_of_nat(v___x_5213_);
v___y_5200_ = v___x_5214_;
goto v___jp_5199_;
}
}
v___jp_5134_:
{
lean_object* v___x_5138_; 
lean_inc(v___y_5136_);
v___x_5138_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__2(v_oldTraces_5124_, v_data_5137_, v___y_5136_, v___y_5135_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_);
if (lean_obj_tag(v___x_5138_) == 0)
{
lean_object* v___x_5139_; 
lean_dec_ref_known(v___x_5138_, 1);
v___x_5139_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5132_);
return v___x_5139_;
}
else
{
lean_object* v_a_5140_; lean_object* v___x_5142_; uint8_t v_isShared_5143_; uint8_t v_isSharedCheck_5147_; 
lean_dec(v_fst_5132_);
v_a_5140_ = lean_ctor_get(v___x_5138_, 0);
v_isSharedCheck_5147_ = !lean_is_exclusive(v___x_5138_);
if (v_isSharedCheck_5147_ == 0)
{
v___x_5142_ = v___x_5138_;
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
else
{
lean_inc(v_a_5140_);
lean_dec(v___x_5138_);
v___x_5142_ = lean_box(0);
v_isShared_5143_ = v_isSharedCheck_5147_;
goto v_resetjp_5141_;
}
v_resetjp_5141_:
{
lean_object* v___x_5145_; 
if (v_isShared_5143_ == 0)
{
v___x_5145_ = v___x_5142_;
goto v_reusejp_5144_;
}
else
{
lean_object* v_reuseFailAlloc_5146_; 
v_reuseFailAlloc_5146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5146_, 0, v_a_5140_);
v___x_5145_ = v_reuseFailAlloc_5146_;
goto v_reusejp_5144_;
}
v_reusejp_5144_:
{
return v___x_5145_;
}
}
}
}
v___jp_5152_:
{
uint8_t v_result_5155_; lean_object* v___x_5156_; lean_object* v___x_5157_; double v___x_5158_; lean_object* v_data_5159_; 
v_result_5155_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__4(v_fst_5132_);
v___x_5156_ = lean_box(v_result_5155_);
v___x_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5157_, 0, v___x_5156_);
v___x_5158_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__0);
lean_inc_ref(v_tag_5121_);
lean_inc_ref(v___x_5157_);
lean_inc(v_cls_5119_);
v_data_5159_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5159_, 0, v_cls_5119_);
lean_ctor_set(v_data_5159_, 1, v___x_5157_);
lean_ctor_set(v_data_5159_, 2, v_tag_5121_);
lean_ctor_set_float(v_data_5159_, sizeof(void*)*3, v___x_5158_);
lean_ctor_set_float(v_data_5159_, sizeof(void*)*3 + 8, v___x_5158_);
lean_ctor_set_uint8(v_data_5159_, sizeof(void*)*3 + 16, v_collapsed_5120_);
if (v___x_5151_ == 0)
{
lean_dec_ref_known(v___x_5157_, 1);
lean_dec(v_snd_5149_);
lean_dec(v_fst_5148_);
lean_dec_ref(v_tag_5121_);
lean_dec(v_cls_5119_);
v___y_5135_ = v_a_5154_;
v___y_5136_ = v___y_5153_;
v_data_5137_ = v_data_5159_;
goto v___jp_5134_;
}
else
{
lean_object* v_data_5160_; double v___x_5161_; double v___x_5162_; 
lean_dec_ref_known(v_data_5159_, 3);
v_data_5160_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_5160_, 0, v_cls_5119_);
lean_ctor_set(v_data_5160_, 1, v___x_5157_);
lean_ctor_set(v_data_5160_, 2, v_tag_5121_);
v___x_5161_ = lean_unbox_float(v_fst_5148_);
lean_dec(v_fst_5148_);
lean_ctor_set_float(v_data_5160_, sizeof(void*)*3, v___x_5161_);
v___x_5162_ = lean_unbox_float(v_snd_5149_);
lean_dec(v_snd_5149_);
lean_ctor_set_float(v_data_5160_, sizeof(void*)*3 + 8, v___x_5162_);
lean_ctor_set_uint8(v_data_5160_, sizeof(void*)*3 + 16, v_collapsed_5120_);
v___y_5135_ = v_a_5154_;
v___y_5136_ = v___y_5153_;
v_data_5137_ = v_data_5160_;
goto v___jp_5134_;
}
}
v___jp_5163_:
{
lean_object* v_ref_5164_; lean_object* v___x_5165_; 
v_ref_5164_ = lean_ctor_get(v___y_5129_, 4);
lean_inc(v___y_5130_);
lean_inc_ref(v___y_5129_);
lean_inc(v___y_5128_);
lean_inc_ref(v___y_5127_);
lean_inc(v_fst_5132_);
v___x_5165_ = lean_apply_6(v_msg_5125_, v_fst_5132_, v___y_5127_, v___y_5128_, v___y_5129_, v___y_5130_, lean_box(0));
if (lean_obj_tag(v___x_5165_) == 0)
{
lean_object* v_a_5166_; 
v_a_5166_ = lean_ctor_get(v___x_5165_, 0);
lean_inc(v_a_5166_);
lean_dec_ref_known(v___x_5165_, 1);
v___y_5153_ = v_ref_5164_;
v_a_5154_ = v_a_5166_;
goto v___jp_5152_;
}
else
{
lean_object* v___x_5167_; 
lean_dec_ref_known(v___x_5165_, 1);
v___x_5167_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__6___closed__1);
v___y_5153_ = v_ref_5164_;
v_a_5154_ = v___x_5167_;
goto v___jp_5152_;
}
}
v___jp_5168_:
{
if (v_clsEnabled_5123_ == 0)
{
if (v___y_5169_ == 0)
{
lean_object* v___x_5170_; lean_object* v_traceState_5171_; lean_object* v_env_5172_; lean_object* v_nextMacroScope_5173_; lean_object* v_ngen_5174_; lean_object* v_auxDeclNGen_5175_; lean_object* v_cache_5176_; lean_object* v_messages_5177_; lean_object* v_infoState_5178_; lean_object* v_snapshotTasks_5179_; lean_object* v___x_5181_; uint8_t v_isShared_5182_; uint8_t v_isSharedCheck_5198_; 
lean_dec(v_snd_5149_);
lean_dec(v_fst_5148_);
lean_dec_ref(v_msg_5125_);
lean_dec_ref(v_tag_5121_);
lean_dec(v_cls_5119_);
v___x_5170_ = lean_st_ref_take(v___y_5130_);
v_traceState_5171_ = lean_ctor_get(v___x_5170_, 4);
v_env_5172_ = lean_ctor_get(v___x_5170_, 0);
v_nextMacroScope_5173_ = lean_ctor_get(v___x_5170_, 1);
v_ngen_5174_ = lean_ctor_get(v___x_5170_, 2);
v_auxDeclNGen_5175_ = lean_ctor_get(v___x_5170_, 3);
v_cache_5176_ = lean_ctor_get(v___x_5170_, 5);
v_messages_5177_ = lean_ctor_get(v___x_5170_, 6);
v_infoState_5178_ = lean_ctor_get(v___x_5170_, 7);
v_snapshotTasks_5179_ = lean_ctor_get(v___x_5170_, 8);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5170_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5181_ = v___x_5170_;
v_isShared_5182_ = v_isSharedCheck_5198_;
goto v_resetjp_5180_;
}
else
{
lean_inc(v_snapshotTasks_5179_);
lean_inc(v_infoState_5178_);
lean_inc(v_messages_5177_);
lean_inc(v_cache_5176_);
lean_inc(v_traceState_5171_);
lean_inc(v_auxDeclNGen_5175_);
lean_inc(v_ngen_5174_);
lean_inc(v_nextMacroScope_5173_);
lean_inc(v_env_5172_);
lean_dec(v___x_5170_);
v___x_5181_ = lean_box(0);
v_isShared_5182_ = v_isSharedCheck_5198_;
goto v_resetjp_5180_;
}
v_resetjp_5180_:
{
uint64_t v_tid_5183_; lean_object* v_traces_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5197_; 
v_tid_5183_ = lean_ctor_get_uint64(v_traceState_5171_, sizeof(void*)*1);
v_traces_5184_ = lean_ctor_get(v_traceState_5171_, 0);
v_isSharedCheck_5197_ = !lean_is_exclusive(v_traceState_5171_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5186_ = v_traceState_5171_;
v_isShared_5187_ = v_isSharedCheck_5197_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_traces_5184_);
lean_dec(v_traceState_5171_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5197_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
lean_object* v___x_5188_; lean_object* v___x_5190_; 
v___x_5188_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_5124_, v_traces_5184_);
lean_dec_ref(v_traces_5184_);
if (v_isShared_5187_ == 0)
{
lean_ctor_set(v___x_5186_, 0, v___x_5188_);
v___x_5190_ = v___x_5186_;
goto v_reusejp_5189_;
}
else
{
lean_object* v_reuseFailAlloc_5196_; 
v_reuseFailAlloc_5196_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_5196_, 0, v___x_5188_);
lean_ctor_set_uint64(v_reuseFailAlloc_5196_, sizeof(void*)*1, v_tid_5183_);
v___x_5190_ = v_reuseFailAlloc_5196_;
goto v_reusejp_5189_;
}
v_reusejp_5189_:
{
lean_object* v___x_5192_; 
if (v_isShared_5182_ == 0)
{
lean_ctor_set(v___x_5181_, 4, v___x_5190_);
v___x_5192_ = v___x_5181_;
goto v_reusejp_5191_;
}
else
{
lean_object* v_reuseFailAlloc_5195_; 
v_reuseFailAlloc_5195_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5195_, 0, v_env_5172_);
lean_ctor_set(v_reuseFailAlloc_5195_, 1, v_nextMacroScope_5173_);
lean_ctor_set(v_reuseFailAlloc_5195_, 2, v_ngen_5174_);
lean_ctor_set(v_reuseFailAlloc_5195_, 3, v_auxDeclNGen_5175_);
lean_ctor_set(v_reuseFailAlloc_5195_, 4, v___x_5190_);
lean_ctor_set(v_reuseFailAlloc_5195_, 5, v_cache_5176_);
lean_ctor_set(v_reuseFailAlloc_5195_, 6, v_messages_5177_);
lean_ctor_set(v_reuseFailAlloc_5195_, 7, v_infoState_5178_);
lean_ctor_set(v_reuseFailAlloc_5195_, 8, v_snapshotTasks_5179_);
v___x_5192_ = v_reuseFailAlloc_5195_;
goto v_reusejp_5191_;
}
v_reusejp_5191_:
{
lean_object* v___x_5193_; lean_object* v___x_5194_; 
v___x_5193_ = lean_st_ref_put(v___y_5130_, v___x_5192_);
v___x_5194_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_fst_5132_);
return v___x_5194_;
}
}
}
}
}
else
{
goto v___jp_5163_;
}
}
else
{
goto v___jp_5163_;
}
}
v___jp_5199_:
{
double v___x_5201_; double v___x_5202_; double v___x_5203_; uint8_t v___x_5204_; 
v___x_5201_ = lean_unbox_float(v_snd_5149_);
v___x_5202_ = lean_unbox_float(v_fst_5148_);
v___x_5203_ = lean_float_sub(v___x_5201_, v___x_5202_);
v___x_5204_ = lean_float_decLt(v___y_5200_, v___x_5203_);
v___y_5169_ = v___x_5204_;
goto v___jp_5168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2___boxed(lean_object* v_cls_5215_, lean_object* v_collapsed_5216_, lean_object* v_tag_5217_, lean_object* v_opts_5218_, lean_object* v_clsEnabled_5219_, lean_object* v_oldTraces_5220_, lean_object* v_msg_5221_, lean_object* v_resStartStop_5222_, lean_object* v___y_5223_, lean_object* v___y_5224_, lean_object* v___y_5225_, lean_object* v___y_5226_, lean_object* v___y_5227_){
_start:
{
uint8_t v_collapsed_boxed_5228_; uint8_t v_clsEnabled_boxed_5229_; lean_object* v_res_5230_; 
v_collapsed_boxed_5228_ = lean_unbox(v_collapsed_5216_);
v_clsEnabled_boxed_5229_ = lean_unbox(v_clsEnabled_5219_);
v_res_5230_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5215_, v_collapsed_boxed_5228_, v_tag_5217_, v_opts_5218_, v_clsEnabled_boxed_5229_, v_oldTraces_5220_, v_msg_5221_, v_resStartStop_5222_, v___y_5223_, v___y_5224_, v___y_5225_, v___y_5226_);
lean_dec(v___y_5226_);
lean_dec_ref(v___y_5225_);
lean_dec(v___y_5224_);
lean_dec_ref(v___y_5223_);
lean_dec_ref(v_opts_5218_);
return v_res_5230_;
}
}
static lean_object* _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2(void){
_start:
{
lean_object* v_cls_5235_; lean_object* v___x_5236_; lean_object* v___x_5237_; 
v_cls_5235_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5236_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__5));
v___x_5237_ = l_Lean_Name_append(v___x_5236_, v_cls_5235_);
return v___x_5237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(lean_object* v_e_5238_, lean_object* v_a_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_){
_start:
{
lean_object* v___y_5245_; lean_object* v_options_5263_; lean_object* v_toCold_5264_; uint8_t v_hasTrace_5265_; lean_object* v_cls_5266_; uint8_t v___x_5267_; 
v_options_5263_ = lean_ctor_get(v_a_5241_, 1);
v_toCold_5264_ = lean_ctor_get(v_a_5241_, 0);
v_hasTrace_5265_ = lean_ctor_get_uint8(v_options_5263_, sizeof(void*)*1);
v_cls_5266_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5267_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_hasDepLet(v_e_5238_);
if (v_hasTrace_5265_ == 0)
{
lean_object* v___x_5268_; 
v___x_5268_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5267_, v_e_5238_, v_cls_5266_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
v___y_5245_ = v___x_5268_;
goto v___jp_5244_;
}
else
{
lean_object* v_inheritedTraceOptions_5269_; lean_object* v___f_5270_; lean_object* v___x_5271_; lean_object* v___x_5272_; uint8_t v___x_5273_; lean_object* v___y_5275_; lean_object* v___y_5276_; lean_object* v_a_5277_; lean_object* v___y_5290_; lean_object* v___y_5291_; lean_object* v_a_5292_; 
v_inheritedTraceOptions_5269_ = lean_ctor_get(v_toCold_5264_, 4);
v___f_5270_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__1));
v___x_5271_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize_spec__2___redArg___closed__1));
v___x_5272_ = lean_obj_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__2);
v___x_5273_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5269_, v_options_5263_, v___x_5272_);
if (v___x_5273_ == 0)
{
lean_object* v___x_5342_; uint8_t v___x_5343_; 
v___x_5342_ = l_Lean_trace_profiler;
v___x_5343_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5263_, v___x_5342_);
if (v___x_5343_ == 0)
{
lean_object* v___x_5344_; 
v___x_5344_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5267_, v_e_5238_, v_cls_5266_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
v___y_5245_ = v___x_5344_;
goto v___jp_5244_;
}
else
{
goto v___jp_5301_;
}
}
else
{
goto v___jp_5301_;
}
v___jp_5274_:
{
lean_object* v___x_5278_; double v___x_5279_; double v___x_5280_; double v___x_5281_; double v___x_5282_; double v___x_5283_; lean_object* v___x_5284_; lean_object* v___x_5285_; lean_object* v___x_5286_; lean_object* v___x_5287_; lean_object* v___x_5288_; 
v___x_5278_ = lean_io_mono_nanos_now();
v___x_5279_ = lean_float_of_nat(v___y_5275_);
v___x_5280_ = lean_float_once(&l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0, &l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0_once, _init_l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit___closed__0);
v___x_5281_ = lean_float_div(v___x_5279_, v___x_5280_);
v___x_5282_ = lean_float_of_nat(v___x_5278_);
v___x_5283_ = lean_float_div(v___x_5282_, v___x_5280_);
v___x_5284_ = lean_box_float(v___x_5281_);
v___x_5285_ = lean_box_float(v___x_5283_);
v___x_5286_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5286_, 0, v___x_5284_);
lean_ctor_set(v___x_5286_, 1, v___x_5285_);
v___x_5287_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5287_, 0, v_a_5277_);
lean_ctor_set(v___x_5287_, 1, v___x_5286_);
v___x_5288_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5266_, v_hasTrace_5265_, v___x_5271_, v_options_5263_, v___x_5273_, v___y_5276_, v___f_5270_, v___x_5287_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
v___y_5245_ = v___x_5288_;
goto v___jp_5244_;
}
v___jp_5289_:
{
lean_object* v___x_5293_; double v___x_5294_; double v___x_5295_; lean_object* v___x_5296_; lean_object* v___x_5297_; lean_object* v___x_5298_; lean_object* v___x_5299_; lean_object* v___x_5300_; 
v___x_5293_ = lean_io_get_num_heartbeats();
v___x_5294_ = lean_float_of_nat(v___y_5291_);
v___x_5295_ = lean_float_of_nat(v___x_5293_);
v___x_5296_ = lean_box_float(v___x_5294_);
v___x_5297_ = lean_box_float(v___x_5295_);
v___x_5298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5298_, 0, v___x_5296_);
lean_ctor_set(v___x_5298_, 1, v___x_5297_);
v___x_5299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5299_, 0, v_a_5292_);
lean_ctor_set(v___x_5299_, 1, v___x_5298_);
v___x_5300_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2(v_cls_5266_, v_hasTrace_5265_, v___x_5271_, v_options_5263_, v___x_5273_, v___y_5290_, v___f_5270_, v___x_5299_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
v___y_5245_ = v___x_5300_;
goto v___jp_5244_;
}
v___jp_5301_:
{
lean_object* v___x_5302_; lean_object* v_a_5303_; lean_object* v___x_5304_; uint8_t v___x_5305_; 
v___x_5302_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__1___redArg(v_a_5242_);
v_a_5303_ = lean_ctor_get(v___x_5302_, 0);
lean_inc(v_a_5303_);
lean_dec_ref(v___x_5302_);
v___x_5304_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5305_ = l_Lean_Option_get___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visit_spec__5(v_options_5263_, v___x_5304_);
if (v___x_5305_ == 0)
{
lean_object* v___x_5306_; lean_object* v___x_5307_; 
v___x_5306_ = lean_io_mono_nanos_now();
v___x_5307_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5267_, v_e_5238_, v_cls_5266_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5310_; uint8_t v_isShared_5311_; uint8_t v_isSharedCheck_5315_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5315_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5315_ == 0)
{
v___x_5310_ = v___x_5307_;
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
else
{
lean_inc(v_a_5308_);
lean_dec(v___x_5307_);
v___x_5310_ = lean_box(0);
v_isShared_5311_ = v_isSharedCheck_5315_;
goto v_resetjp_5309_;
}
v_resetjp_5309_:
{
lean_object* v___x_5313_; 
if (v_isShared_5311_ == 0)
{
lean_ctor_set_tag(v___x_5310_, 1);
v___x_5313_ = v___x_5310_;
goto v_reusejp_5312_;
}
else
{
lean_object* v_reuseFailAlloc_5314_; 
v_reuseFailAlloc_5314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5314_, 0, v_a_5308_);
v___x_5313_ = v_reuseFailAlloc_5314_;
goto v_reusejp_5312_;
}
v_reusejp_5312_:
{
v___y_5275_ = v___x_5306_;
v___y_5276_ = v_a_5303_;
v_a_5277_ = v___x_5313_;
goto v___jp_5274_;
}
}
}
else
{
lean_object* v_a_5316_; lean_object* v___x_5318_; uint8_t v_isShared_5319_; uint8_t v_isSharedCheck_5323_; 
v_a_5316_ = lean_ctor_get(v___x_5307_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5307_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5318_ = v___x_5307_;
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
else
{
lean_inc(v_a_5316_);
lean_dec(v___x_5307_);
v___x_5318_ = lean_box(0);
v_isShared_5319_ = v_isSharedCheck_5323_;
goto v_resetjp_5317_;
}
v_resetjp_5317_:
{
lean_object* v___x_5321_; 
if (v_isShared_5319_ == 0)
{
lean_ctor_set_tag(v___x_5318_, 0);
v___x_5321_ = v___x_5318_;
goto v_reusejp_5320_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v_a_5316_);
v___x_5321_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5320_;
}
v_reusejp_5320_:
{
v___y_5275_ = v___x_5306_;
v___y_5276_ = v_a_5303_;
v_a_5277_ = v___x_5321_;
goto v___jp_5274_;
}
}
}
}
else
{
lean_object* v___x_5324_; lean_object* v___x_5325_; 
v___x_5324_ = lean_io_get_num_heartbeats();
v___x_5325_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___lam__5(v___x_5267_, v_e_5238_, v_cls_5266_, v_a_5239_, v_a_5240_, v_a_5241_, v_a_5242_);
if (lean_obj_tag(v___x_5325_) == 0)
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5333_; 
v_a_5326_ = lean_ctor_get(v___x_5325_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5328_ = v___x_5325_;
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5325_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___x_5331_; 
if (v_isShared_5329_ == 0)
{
lean_ctor_set_tag(v___x_5328_, 1);
v___x_5331_ = v___x_5328_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
v___y_5290_ = v_a_5303_;
v___y_5291_ = v___x_5324_;
v_a_5292_ = v___x_5331_;
goto v___jp_5289_;
}
}
}
else
{
lean_object* v_a_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5341_; 
v_a_5334_ = lean_ctor_get(v___x_5325_, 0);
v_isSharedCheck_5341_ = !lean_is_exclusive(v___x_5325_);
if (v_isSharedCheck_5341_ == 0)
{
v___x_5336_ = v___x_5325_;
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_a_5334_);
lean_dec(v___x_5325_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5341_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
lean_object* v___x_5339_; 
if (v_isShared_5337_ == 0)
{
lean_ctor_set_tag(v___x_5336_, 0);
v___x_5339_ = v___x_5336_;
goto v_reusejp_5338_;
}
else
{
lean_object* v_reuseFailAlloc_5340_; 
v_reuseFailAlloc_5340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5340_, 0, v_a_5334_);
v___x_5339_ = v_reuseFailAlloc_5340_;
goto v_reusejp_5338_;
}
v_reusejp_5338_:
{
v___y_5290_ = v_a_5303_;
v___y_5291_ = v___x_5324_;
v_a_5292_ = v___x_5339_;
goto v___jp_5289_;
}
}
}
}
}
}
v___jp_5244_:
{
if (lean_obj_tag(v___y_5245_) == 0)
{
lean_object* v_a_5246_; lean_object* v___x_5248_; uint8_t v_isShared_5249_; uint8_t v_isSharedCheck_5254_; 
v_a_5246_ = lean_ctor_get(v___y_5245_, 0);
v_isSharedCheck_5254_ = !lean_is_exclusive(v___y_5245_);
if (v_isSharedCheck_5254_ == 0)
{
v___x_5248_ = v___y_5245_;
v_isShared_5249_ = v_isSharedCheck_5254_;
goto v_resetjp_5247_;
}
else
{
lean_inc(v_a_5246_);
lean_dec(v___y_5245_);
v___x_5248_ = lean_box(0);
v_isShared_5249_ = v_isSharedCheck_5254_;
goto v_resetjp_5247_;
}
v_resetjp_5247_:
{
lean_object* v_fst_5250_; lean_object* v___x_5252_; 
v_fst_5250_ = lean_ctor_get(v_a_5246_, 0);
lean_inc(v_fst_5250_);
lean_dec(v_a_5246_);
if (v_isShared_5249_ == 0)
{
lean_ctor_set(v___x_5248_, 0, v_fst_5250_);
v___x_5252_ = v___x_5248_;
goto v_reusejp_5251_;
}
else
{
lean_object* v_reuseFailAlloc_5253_; 
v_reuseFailAlloc_5253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5253_, 0, v_fst_5250_);
v___x_5252_ = v_reuseFailAlloc_5253_;
goto v_reusejp_5251_;
}
v_reusejp_5251_:
{
return v___x_5252_;
}
}
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5262_; 
v_a_5255_ = lean_ctor_get(v___y_5245_, 0);
v_isSharedCheck_5262_ = !lean_is_exclusive(v___y_5245_);
if (v_isSharedCheck_5262_ == 0)
{
v___x_5257_ = v___y_5245_;
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___y_5245_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5262_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v___x_5260_; 
if (v_isShared_5258_ == 0)
{
v___x_5260_ = v___x_5257_;
goto v_reusejp_5259_;
}
else
{
lean_object* v_reuseFailAlloc_5261_; 
v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
v___x_5260_ = v_reuseFailAlloc_5261_;
goto v_reusejp_5259_;
}
v_reusejp_5259_:
{
return v___x_5260_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed(lean_object* v_e_5345_, lean_object* v_a_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_, lean_object* v_a_5350_){
_start:
{
lean_object* v_res_5351_; 
v_res_5351_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main(v_e_5345_, v_a_5346_, v_a_5347_, v_a_5348_, v_a_5349_);
lean_dec(v_a_5349_);
lean_dec_ref(v_a_5348_);
lean_dec(v_a_5347_);
lean_dec_ref(v_a_5346_);
return v_res_5351_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(lean_object* v_00_u03b1_5352_, lean_object* v_x_5353_, lean_object* v___y_5354_, lean_object* v___y_5355_, lean_object* v___y_5356_, lean_object* v___y_5357_){
_start:
{
lean_object* v___x_5359_; 
v___x_5359_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___redArg(v_x_5353_);
return v___x_5359_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3___boxed(lean_object* v_00_u03b1_5360_, lean_object* v_x_5361_, lean_object* v___y_5362_, lean_object* v___y_5363_, lean_object* v___y_5364_, lean_object* v___y_5365_, lean_object* v___y_5366_){
_start:
{
lean_object* v_res_5367_; 
v_res_5367_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main_spec__2_spec__3(v_00_u03b1_5360_, v_x_5361_, v___y_5362_, v___y_5363_, v___y_5364_, v___y_5365_);
lean_dec(v___y_5365_);
lean_dec_ref(v___y_5364_);
lean_dec(v___y_5363_);
lean_dec_ref(v___y_5362_);
return v_res_5367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(lean_object* v_e_5368_, lean_object* v___y_5369_){
_start:
{
uint8_t v___x_5371_; 
v___x_5371_ = l_Lean_Expr_hasMVar(v_e_5368_);
if (v___x_5371_ == 0)
{
lean_object* v___x_5372_; 
v___x_5372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5372_, 0, v_e_5368_);
return v___x_5372_;
}
else
{
lean_object* v___x_5373_; lean_object* v_mctx_5374_; lean_object* v___x_5375_; lean_object* v_fst_5376_; lean_object* v_snd_5377_; lean_object* v___x_5378_; lean_object* v_cache_5379_; lean_object* v_zetaDeltaFVarIds_5380_; lean_object* v_postponed_5381_; lean_object* v_diag_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5391_; 
v___x_5373_ = lean_st_ref_get(v___y_5369_);
v_mctx_5374_ = lean_ctor_get(v___x_5373_, 0);
lean_inc_ref(v_mctx_5374_);
lean_dec(v___x_5373_);
v___x_5375_ = l_Lean_instantiateMVarsCore(v_mctx_5374_, v_e_5368_);
v_fst_5376_ = lean_ctor_get(v___x_5375_, 0);
lean_inc(v_fst_5376_);
v_snd_5377_ = lean_ctor_get(v___x_5375_, 1);
lean_inc(v_snd_5377_);
lean_dec_ref(v___x_5375_);
v___x_5378_ = lean_st_ref_take(v___y_5369_);
v_cache_5379_ = lean_ctor_get(v___x_5378_, 1);
v_zetaDeltaFVarIds_5380_ = lean_ctor_get(v___x_5378_, 2);
v_postponed_5381_ = lean_ctor_get(v___x_5378_, 3);
v_diag_5382_ = lean_ctor_get(v___x_5378_, 4);
v_isSharedCheck_5391_ = !lean_is_exclusive(v___x_5378_);
if (v_isSharedCheck_5391_ == 0)
{
lean_object* v_unused_5392_; 
v_unused_5392_ = lean_ctor_get(v___x_5378_, 0);
lean_dec(v_unused_5392_);
v___x_5384_ = v___x_5378_;
v_isShared_5385_ = v_isSharedCheck_5391_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_diag_5382_);
lean_inc(v_postponed_5381_);
lean_inc(v_zetaDeltaFVarIds_5380_);
lean_inc(v_cache_5379_);
lean_dec(v___x_5378_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5391_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
lean_ctor_set(v___x_5384_, 0, v_snd_5377_);
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v_snd_5377_);
lean_ctor_set(v_reuseFailAlloc_5390_, 1, v_cache_5379_);
lean_ctor_set(v_reuseFailAlloc_5390_, 2, v_zetaDeltaFVarIds_5380_);
lean_ctor_set(v_reuseFailAlloc_5390_, 3, v_postponed_5381_);
lean_ctor_set(v_reuseFailAlloc_5390_, 4, v_diag_5382_);
v___x_5387_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; 
v___x_5388_ = lean_st_ref_put(v___y_5369_, v___x_5387_);
v___x_5389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5389_, 0, v_fst_5376_);
return v___x_5389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg___boxed(lean_object* v_e_5393_, lean_object* v___y_5394_, lean_object* v___y_5395_){
_start:
{
lean_object* v_res_5396_; 
v_res_5396_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5393_, v___y_5394_);
lean_dec(v___y_5394_);
return v_res_5396_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(lean_object* v_e_5397_, lean_object* v___y_5398_, lean_object* v___y_5399_, lean_object* v___y_5400_, lean_object* v___y_5401_){
_start:
{
lean_object* v___x_5403_; 
v___x_5403_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5397_, v___y_5399_);
return v___x_5403_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___boxed(lean_object* v_e_5404_, lean_object* v___y_5405_, lean_object* v___y_5406_, lean_object* v___y_5407_, lean_object* v___y_5408_, lean_object* v___y_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0(v_e_5404_, v___y_5405_, v___y_5406_, v___y_5407_, v___y_5408_);
lean_dec(v___y_5408_);
lean_dec_ref(v___y_5407_);
lean_dec(v___y_5406_);
lean_dec_ref(v___y_5405_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(lean_object* v_category_5411_, lean_object* v_opts_5412_, lean_object* v_act_5413_, lean_object* v_decl_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_, lean_object* v___y_5417_, lean_object* v___y_5418_){
_start:
{
lean_object* v___x_5420_; lean_object* v___x_5421_; 
lean_inc(v___y_5418_);
lean_inc_ref(v___y_5417_);
lean_inc(v___y_5416_);
lean_inc_ref(v___y_5415_);
v___x_5420_ = lean_apply_4(v_act_5413_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
v___x_5421_ = l_Lean_profileitIOUnsafe___redArg(v_category_5411_, v_opts_5412_, v___x_5420_, v_decl_5414_);
return v___x_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg___boxed(lean_object* v_category_5422_, lean_object* v_opts_5423_, lean_object* v_act_5424_, lean_object* v_decl_5425_, lean_object* v___y_5426_, lean_object* v___y_5427_, lean_object* v___y_5428_, lean_object* v___y_5429_, lean_object* v___y_5430_){
_start:
{
lean_object* v_res_5431_; 
v_res_5431_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5422_, v_opts_5423_, v_act_5424_, v_decl_5425_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_);
lean_dec(v___y_5429_);
lean_dec_ref(v___y_5428_);
lean_dec(v___y_5427_);
lean_dec_ref(v___y_5426_);
lean_dec_ref(v_opts_5423_);
lean_dec_ref(v_category_5422_);
return v_res_5431_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(lean_object* v_00_u03b1_5432_, lean_object* v_category_5433_, lean_object* v_opts_5434_, lean_object* v_act_5435_, lean_object* v_decl_5436_, lean_object* v___y_5437_, lean_object* v___y_5438_, lean_object* v___y_5439_, lean_object* v___y_5440_){
_start:
{
lean_object* v___x_5442_; 
v___x_5442_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v_category_5433_, v_opts_5434_, v_act_5435_, v_decl_5436_, v___y_5437_, v___y_5438_, v___y_5439_, v___y_5440_);
return v___x_5442_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___boxed(lean_object* v_00_u03b1_5443_, lean_object* v_category_5444_, lean_object* v_opts_5445_, lean_object* v_act_5446_, lean_object* v_decl_5447_, lean_object* v___y_5448_, lean_object* v___y_5449_, lean_object* v___y_5450_, lean_object* v___y_5451_, lean_object* v___y_5452_){
_start:
{
lean_object* v_res_5453_; 
v_res_5453_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2(v_00_u03b1_5443_, v_category_5444_, v_opts_5445_, v_act_5446_, v_decl_5447_, v___y_5448_, v___y_5449_, v___y_5450_, v___y_5451_);
lean_dec(v___y_5451_);
lean_dec_ref(v___y_5450_);
lean_dec(v___y_5449_);
lean_dec_ref(v___y_5448_);
lean_dec_ref(v_opts_5445_);
lean_dec_ref(v_category_5444_);
return v_res_5453_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(lean_object* v___y_5454_, uint8_t v_isExporting_5455_, lean_object* v___x_5456_, lean_object* v___y_5457_, lean_object* v___x_5458_, lean_object* v_a_x3f_5459_){
_start:
{
lean_object* v___x_5461_; lean_object* v_env_5462_; lean_object* v_nextMacroScope_5463_; lean_object* v_ngen_5464_; lean_object* v_auxDeclNGen_5465_; lean_object* v_traceState_5466_; lean_object* v_messages_5467_; lean_object* v_infoState_5468_; lean_object* v_snapshotTasks_5469_; lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5494_; 
v___x_5461_ = lean_st_ref_take(v___y_5454_);
v_env_5462_ = lean_ctor_get(v___x_5461_, 0);
v_nextMacroScope_5463_ = lean_ctor_get(v___x_5461_, 1);
v_ngen_5464_ = lean_ctor_get(v___x_5461_, 2);
v_auxDeclNGen_5465_ = lean_ctor_get(v___x_5461_, 3);
v_traceState_5466_ = lean_ctor_get(v___x_5461_, 4);
v_messages_5467_ = lean_ctor_get(v___x_5461_, 6);
v_infoState_5468_ = lean_ctor_get(v___x_5461_, 7);
v_snapshotTasks_5469_ = lean_ctor_get(v___x_5461_, 8);
v_isSharedCheck_5494_ = !lean_is_exclusive(v___x_5461_);
if (v_isSharedCheck_5494_ == 0)
{
lean_object* v_unused_5495_; 
v_unused_5495_ = lean_ctor_get(v___x_5461_, 5);
lean_dec(v_unused_5495_);
v___x_5471_ = v___x_5461_;
v_isShared_5472_ = v_isSharedCheck_5494_;
goto v_resetjp_5470_;
}
else
{
lean_inc(v_snapshotTasks_5469_);
lean_inc(v_infoState_5468_);
lean_inc(v_messages_5467_);
lean_inc(v_traceState_5466_);
lean_inc(v_auxDeclNGen_5465_);
lean_inc(v_ngen_5464_);
lean_inc(v_nextMacroScope_5463_);
lean_inc(v_env_5462_);
lean_dec(v___x_5461_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5494_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5473_; lean_object* v___x_5475_; 
v___x_5473_ = l_Lean_Environment_setExporting(v_env_5462_, v_isExporting_5455_);
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 5, v___x_5456_);
lean_ctor_set(v___x_5471_, 0, v___x_5473_);
v___x_5475_ = v___x_5471_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5473_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_nextMacroScope_5463_);
lean_ctor_set(v_reuseFailAlloc_5493_, 2, v_ngen_5464_);
lean_ctor_set(v_reuseFailAlloc_5493_, 3, v_auxDeclNGen_5465_);
lean_ctor_set(v_reuseFailAlloc_5493_, 4, v_traceState_5466_);
lean_ctor_set(v_reuseFailAlloc_5493_, 5, v___x_5456_);
lean_ctor_set(v_reuseFailAlloc_5493_, 6, v_messages_5467_);
lean_ctor_set(v_reuseFailAlloc_5493_, 7, v_infoState_5468_);
lean_ctor_set(v_reuseFailAlloc_5493_, 8, v_snapshotTasks_5469_);
v___x_5475_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
lean_object* v___x_5476_; lean_object* v___x_5477_; lean_object* v_mctx_5478_; lean_object* v_zetaDeltaFVarIds_5479_; lean_object* v_postponed_5480_; lean_object* v_diag_5481_; lean_object* v___x_5483_; uint8_t v_isShared_5484_; uint8_t v_isSharedCheck_5491_; 
v___x_5476_ = lean_st_ref_put(v___y_5454_, v___x_5475_);
v___x_5477_ = lean_st_ref_take(v___y_5457_);
v_mctx_5478_ = lean_ctor_get(v___x_5477_, 0);
v_zetaDeltaFVarIds_5479_ = lean_ctor_get(v___x_5477_, 2);
v_postponed_5480_ = lean_ctor_get(v___x_5477_, 3);
v_diag_5481_ = lean_ctor_get(v___x_5477_, 4);
v_isSharedCheck_5491_ = !lean_is_exclusive(v___x_5477_);
if (v_isSharedCheck_5491_ == 0)
{
lean_object* v_unused_5492_; 
v_unused_5492_ = lean_ctor_get(v___x_5477_, 1);
lean_dec(v_unused_5492_);
v___x_5483_ = v___x_5477_;
v_isShared_5484_ = v_isSharedCheck_5491_;
goto v_resetjp_5482_;
}
else
{
lean_inc(v_diag_5481_);
lean_inc(v_postponed_5480_);
lean_inc(v_zetaDeltaFVarIds_5479_);
lean_inc(v_mctx_5478_);
lean_dec(v___x_5477_);
v___x_5483_ = lean_box(0);
v_isShared_5484_ = v_isSharedCheck_5491_;
goto v_resetjp_5482_;
}
v_resetjp_5482_:
{
lean_object* v___x_5486_; 
if (v_isShared_5484_ == 0)
{
lean_ctor_set(v___x_5483_, 1, v___x_5458_);
v___x_5486_ = v___x_5483_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v_mctx_5478_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v___x_5458_);
lean_ctor_set(v_reuseFailAlloc_5490_, 2, v_zetaDeltaFVarIds_5479_);
lean_ctor_set(v_reuseFailAlloc_5490_, 3, v_postponed_5480_);
lean_ctor_set(v_reuseFailAlloc_5490_, 4, v_diag_5481_);
v___x_5486_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5487_; lean_object* v___x_5488_; lean_object* v___x_5489_; 
v___x_5487_ = lean_st_ref_put(v___y_5457_, v___x_5486_);
v___x_5488_ = lean_box(0);
v___x_5489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5489_, 0, v___x_5488_);
return v___x_5489_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0___boxed(lean_object* v___y_5496_, lean_object* v_isExporting_5497_, lean_object* v___x_5498_, lean_object* v___y_5499_, lean_object* v___x_5500_, lean_object* v_a_x3f_5501_, lean_object* v___y_5502_){
_start:
{
uint8_t v_isExporting_boxed_5503_; lean_object* v_res_5504_; 
v_isExporting_boxed_5503_ = lean_unbox(v_isExporting_5497_);
v_res_5504_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5496_, v_isExporting_boxed_5503_, v___x_5498_, v___y_5499_, v___x_5500_, v_a_x3f_5501_);
lean_dec(v_a_x3f_5501_);
lean_dec(v___y_5499_);
lean_dec(v___y_5496_);
return v_res_5504_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_5505_; 
v___x_5505_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_5505_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_5506_; lean_object* v___x_5507_; 
v___x_5506_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__0);
v___x_5507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5507_, 0, v___x_5506_);
return v___x_5507_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_5508_; lean_object* v___x_5509_; 
v___x_5508_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5509_, 0, v___x_5508_);
lean_ctor_set(v___x_5509_, 1, v___x_5508_);
return v___x_5509_;
}
}
static lean_object* _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_5510_; lean_object* v___x_5511_; 
v___x_5510_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__1);
v___x_5511_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_5511_, 0, v___x_5510_);
lean_ctor_set(v___x_5511_, 1, v___x_5510_);
lean_ctor_set(v___x_5511_, 2, v___x_5510_);
lean_ctor_set(v___x_5511_, 3, v___x_5510_);
lean_ctor_set(v___x_5511_, 4, v___x_5510_);
lean_ctor_set(v___x_5511_, 5, v___x_5510_);
return v___x_5511_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(lean_object* v_x_5512_, uint8_t v_isExporting_5513_, lean_object* v___y_5514_, lean_object* v___y_5515_, lean_object* v___y_5516_, lean_object* v___y_5517_){
_start:
{
lean_object* v___x_5519_; lean_object* v_env_5520_; lean_object* v___x_5521_; uint8_t v_isModule_5522_; 
v___x_5519_ = lean_st_ref_get(v___y_5517_);
v_env_5520_ = lean_ctor_get(v___x_5519_, 0);
lean_inc_ref(v_env_5520_);
lean_dec(v___x_5519_);
v___x_5521_ = l_Lean_Environment_header(v_env_5520_);
v_isModule_5522_ = lean_ctor_get_uint8(v___x_5521_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_5521_);
if (v_isModule_5522_ == 0)
{
lean_object* v___x_5523_; 
lean_dec_ref(v_env_5520_);
lean_inc(v___y_5517_);
lean_inc_ref(v___y_5516_);
lean_inc(v___y_5515_);
lean_inc_ref(v___y_5514_);
v___x_5523_ = lean_apply_5(v_x_5512_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, lean_box(0));
return v___x_5523_;
}
else
{
uint8_t v_isExporting_5524_; 
v_isExporting_5524_ = lean_ctor_get_uint8(v_env_5520_, sizeof(void*)*8);
lean_dec_ref(v_env_5520_);
if (v_isExporting_5513_ == 0)
{
if (v_isExporting_5524_ == 0)
{
lean_object* v___x_5590_; 
lean_inc(v___y_5517_);
lean_inc_ref(v___y_5516_);
lean_inc(v___y_5515_);
lean_inc_ref(v___y_5514_);
v___x_5590_ = lean_apply_5(v_x_5512_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, lean_box(0));
return v___x_5590_;
}
else
{
goto v___jp_5525_;
}
}
else
{
if (v_isExporting_5524_ == 0)
{
goto v___jp_5525_;
}
else
{
lean_object* v___x_5591_; 
lean_inc(v___y_5517_);
lean_inc_ref(v___y_5516_);
lean_inc(v___y_5515_);
lean_inc_ref(v___y_5514_);
v___x_5591_ = lean_apply_5(v_x_5512_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, lean_box(0));
return v___x_5591_;
}
}
v___jp_5525_:
{
lean_object* v___x_5526_; lean_object* v_env_5527_; lean_object* v_nextMacroScope_5528_; lean_object* v_ngen_5529_; lean_object* v_auxDeclNGen_5530_; lean_object* v_traceState_5531_; lean_object* v_messages_5532_; lean_object* v_infoState_5533_; lean_object* v_snapshotTasks_5534_; lean_object* v___x_5536_; uint8_t v_isShared_5537_; uint8_t v_isSharedCheck_5588_; 
v___x_5526_ = lean_st_ref_take(v___y_5517_);
v_env_5527_ = lean_ctor_get(v___x_5526_, 0);
v_nextMacroScope_5528_ = lean_ctor_get(v___x_5526_, 1);
v_ngen_5529_ = lean_ctor_get(v___x_5526_, 2);
v_auxDeclNGen_5530_ = lean_ctor_get(v___x_5526_, 3);
v_traceState_5531_ = lean_ctor_get(v___x_5526_, 4);
v_messages_5532_ = lean_ctor_get(v___x_5526_, 6);
v_infoState_5533_ = lean_ctor_get(v___x_5526_, 7);
v_snapshotTasks_5534_ = lean_ctor_get(v___x_5526_, 8);
v_isSharedCheck_5588_ = !lean_is_exclusive(v___x_5526_);
if (v_isSharedCheck_5588_ == 0)
{
lean_object* v_unused_5589_; 
v_unused_5589_ = lean_ctor_get(v___x_5526_, 5);
lean_dec(v_unused_5589_);
v___x_5536_ = v___x_5526_;
v_isShared_5537_ = v_isSharedCheck_5588_;
goto v_resetjp_5535_;
}
else
{
lean_inc(v_snapshotTasks_5534_);
lean_inc(v_infoState_5533_);
lean_inc(v_messages_5532_);
lean_inc(v_traceState_5531_);
lean_inc(v_auxDeclNGen_5530_);
lean_inc(v_ngen_5529_);
lean_inc(v_nextMacroScope_5528_);
lean_inc(v_env_5527_);
lean_dec(v___x_5526_);
v___x_5536_ = lean_box(0);
v_isShared_5537_ = v_isSharedCheck_5588_;
goto v_resetjp_5535_;
}
v_resetjp_5535_:
{
lean_object* v___x_5538_; lean_object* v___x_5539_; lean_object* v___x_5541_; 
v___x_5538_ = l_Lean_Environment_setExporting(v_env_5527_, v_isExporting_5513_);
v___x_5539_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__2);
if (v_isShared_5537_ == 0)
{
lean_ctor_set(v___x_5536_, 5, v___x_5539_);
lean_ctor_set(v___x_5536_, 0, v___x_5538_);
v___x_5541_ = v___x_5536_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5587_; 
v_reuseFailAlloc_5587_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5587_, 0, v___x_5538_);
lean_ctor_set(v_reuseFailAlloc_5587_, 1, v_nextMacroScope_5528_);
lean_ctor_set(v_reuseFailAlloc_5587_, 2, v_ngen_5529_);
lean_ctor_set(v_reuseFailAlloc_5587_, 3, v_auxDeclNGen_5530_);
lean_ctor_set(v_reuseFailAlloc_5587_, 4, v_traceState_5531_);
lean_ctor_set(v_reuseFailAlloc_5587_, 5, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5587_, 6, v_messages_5532_);
lean_ctor_set(v_reuseFailAlloc_5587_, 7, v_infoState_5533_);
lean_ctor_set(v_reuseFailAlloc_5587_, 8, v_snapshotTasks_5534_);
v___x_5541_ = v_reuseFailAlloc_5587_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v_mctx_5544_; lean_object* v_zetaDeltaFVarIds_5545_; lean_object* v_postponed_5546_; lean_object* v_diag_5547_; lean_object* v___x_5549_; uint8_t v_isShared_5550_; uint8_t v_isSharedCheck_5585_; 
v___x_5542_ = lean_st_ref_put(v___y_5517_, v___x_5541_);
v___x_5543_ = lean_st_ref_take(v___y_5515_);
v_mctx_5544_ = lean_ctor_get(v___x_5543_, 0);
v_zetaDeltaFVarIds_5545_ = lean_ctor_get(v___x_5543_, 2);
v_postponed_5546_ = lean_ctor_get(v___x_5543_, 3);
v_diag_5547_ = lean_ctor_get(v___x_5543_, 4);
v_isSharedCheck_5585_ = !lean_is_exclusive(v___x_5543_);
if (v_isSharedCheck_5585_ == 0)
{
lean_object* v_unused_5586_; 
v_unused_5586_ = lean_ctor_get(v___x_5543_, 1);
lean_dec(v_unused_5586_);
v___x_5549_ = v___x_5543_;
v_isShared_5550_ = v_isSharedCheck_5585_;
goto v_resetjp_5548_;
}
else
{
lean_inc(v_diag_5547_);
lean_inc(v_postponed_5546_);
lean_inc(v_zetaDeltaFVarIds_5545_);
lean_inc(v_mctx_5544_);
lean_dec(v___x_5543_);
v___x_5549_ = lean_box(0);
v_isShared_5550_ = v_isSharedCheck_5585_;
goto v_resetjp_5548_;
}
v_resetjp_5548_:
{
lean_object* v___x_5551_; lean_object* v___x_5553_; 
v___x_5551_ = lean_obj_once(&l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3, &l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3_once, _init_l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___closed__3);
if (v_isShared_5550_ == 0)
{
lean_ctor_set(v___x_5549_, 1, v___x_5551_);
v___x_5553_ = v___x_5549_;
goto v_reusejp_5552_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v_mctx_5544_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v___x_5551_);
lean_ctor_set(v_reuseFailAlloc_5584_, 2, v_zetaDeltaFVarIds_5545_);
lean_ctor_set(v_reuseFailAlloc_5584_, 3, v_postponed_5546_);
lean_ctor_set(v_reuseFailAlloc_5584_, 4, v_diag_5547_);
v___x_5553_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5552_;
}
v_reusejp_5552_:
{
lean_object* v___x_5554_; lean_object* v_r_5555_; 
v___x_5554_ = lean_st_ref_put(v___y_5515_, v___x_5553_);
lean_inc(v___y_5517_);
lean_inc_ref(v___y_5516_);
lean_inc(v___y_5515_);
lean_inc_ref(v___y_5514_);
v_r_5555_ = lean_apply_5(v_x_5512_, v___y_5514_, v___y_5515_, v___y_5516_, v___y_5517_, lean_box(0));
if (lean_obj_tag(v_r_5555_) == 0)
{
lean_object* v_a_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5572_; 
v_a_5556_ = lean_ctor_get(v_r_5555_, 0);
v_isSharedCheck_5572_ = !lean_is_exclusive(v_r_5555_);
if (v_isSharedCheck_5572_ == 0)
{
v___x_5558_ = v_r_5555_;
v_isShared_5559_ = v_isSharedCheck_5572_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_a_5556_);
lean_dec(v_r_5555_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5572_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v___x_5561_; 
lean_inc(v_a_5556_);
if (v_isShared_5559_ == 0)
{
lean_ctor_set_tag(v___x_5558_, 1);
v___x_5561_ = v___x_5558_;
goto v_reusejp_5560_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v_a_5556_);
v___x_5561_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5560_;
}
v_reusejp_5560_:
{
lean_object* v___x_5562_; lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
v___x_5562_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5517_, v_isExporting_5524_, v___x_5539_, v___y_5515_, v___x_5551_, v___x_5561_);
lean_dec_ref(v___x_5561_);
v_isSharedCheck_5569_ = !lean_is_exclusive(v___x_5562_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; 
v_unused_5570_ = lean_ctor_get(v___x_5562_, 0);
lean_dec(v_unused_5570_);
v___x_5564_ = v___x_5562_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_dec(v___x_5562_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 0, v_a_5556_);
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v_a_5556_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
}
else
{
lean_object* v_a_5573_; lean_object* v___x_5574_; lean_object* v___x_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5582_; 
v_a_5573_ = lean_ctor_get(v_r_5555_, 0);
lean_inc(v_a_5573_);
lean_dec_ref_known(v_r_5555_, 1);
v___x_5574_ = lean_box(0);
v___x_5575_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___lam__0(v___y_5517_, v_isExporting_5524_, v___x_5539_, v___y_5515_, v___x_5551_, v___x_5574_);
v_isSharedCheck_5582_ = !lean_is_exclusive(v___x_5575_);
if (v_isSharedCheck_5582_ == 0)
{
lean_object* v_unused_5583_; 
v_unused_5583_ = lean_ctor_get(v___x_5575_, 0);
lean_dec(v_unused_5583_);
v___x_5577_ = v___x_5575_;
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
else
{
lean_dec(v___x_5575_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5582_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
lean_object* v___x_5580_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set_tag(v___x_5577_, 1);
lean_ctor_set(v___x_5577_, 0, v_a_5573_);
v___x_5580_ = v___x_5577_;
goto v_reusejp_5579_;
}
else
{
lean_object* v_reuseFailAlloc_5581_; 
v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5573_);
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg___boxed(lean_object* v_x_5592_, lean_object* v_isExporting_5593_, lean_object* v___y_5594_, lean_object* v___y_5595_, lean_object* v___y_5596_, lean_object* v___y_5597_, lean_object* v___y_5598_){
_start:
{
uint8_t v_isExporting_boxed_5599_; lean_object* v_res_5600_; 
v_isExporting_boxed_5599_ = lean_unbox(v_isExporting_5593_);
v_res_5600_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5592_, v_isExporting_boxed_5599_, v___y_5594_, v___y_5595_, v___y_5596_, v___y_5597_);
lean_dec(v___y_5597_);
lean_dec_ref(v___y_5596_);
lean_dec(v___y_5595_);
lean_dec_ref(v___y_5594_);
return v_res_5600_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(lean_object* v_x_5601_, uint8_t v_when_5602_, lean_object* v___y_5603_, lean_object* v___y_5604_, lean_object* v___y_5605_, lean_object* v___y_5606_){
_start:
{
if (v_when_5602_ == 0)
{
lean_object* v___x_5608_; 
lean_inc(v___y_5606_);
lean_inc_ref(v___y_5605_);
lean_inc(v___y_5604_);
lean_inc_ref(v___y_5603_);
v___x_5608_ = lean_apply_5(v_x_5601_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_, lean_box(0));
return v___x_5608_;
}
else
{
uint8_t v___x_5609_; lean_object* v___x_5610_; 
v___x_5609_ = 0;
v___x_5610_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5601_, v___x_5609_, v___y_5603_, v___y_5604_, v___y_5605_, v___y_5606_);
return v___x_5610_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg___boxed(lean_object* v_x_5611_, lean_object* v_when_5612_, lean_object* v___y_5613_, lean_object* v___y_5614_, lean_object* v___y_5615_, lean_object* v___y_5616_, lean_object* v___y_5617_){
_start:
{
uint8_t v_when_boxed_5618_; lean_object* v_res_5619_; 
v_when_boxed_5618_ = lean_unbox(v_when_5612_);
v_res_5619_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5611_, v_when_boxed_5618_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_);
lean_dec(v___y_5616_);
lean_dec_ref(v___y_5615_);
lean_dec(v___y_5614_);
lean_dec_ref(v___y_5613_);
return v_res_5619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0(lean_object* v_e_5620_, lean_object* v___y_5621_, lean_object* v___y_5622_, lean_object* v___y_5623_, lean_object* v___y_5624_){
_start:
{
lean_object* v___x_5626_; lean_object* v_a_5627_; lean_object* v___x_5628_; uint8_t v___x_5629_; lean_object* v___x_5630_; 
v___x_5626_ = l_Lean_instantiateMVars___at___00Lean_Meta_letToHave_spec__0___redArg(v_e_5620_, v___y_5622_);
v_a_5627_ = lean_ctor_get(v___x_5626_, 0);
lean_inc(v_a_5627_);
lean_dec_ref(v___x_5626_);
v___x_5628_ = lean_alloc_closure((void*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___boxed), 6, 1);
lean_closure_set(v___x_5628_, 0, v_a_5627_);
v___x_5629_ = 1;
v___x_5630_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v___x_5628_, v___x_5629_, v___y_5621_, v___y_5622_, v___y_5623_, v___y_5624_);
return v___x_5630_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___lam__0___boxed(lean_object* v_e_5631_, lean_object* v___y_5632_, lean_object* v___y_5633_, lean_object* v___y_5634_, lean_object* v___y_5635_, lean_object* v___y_5636_){
_start:
{
lean_object* v_res_5637_; 
v_res_5637_ = l_Lean_Meta_letToHave___lam__0(v_e_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_);
lean_dec(v___y_5635_);
lean_dec_ref(v___y_5634_);
lean_dec(v___y_5633_);
lean_dec_ref(v___y_5632_);
return v_res_5637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave(lean_object* v_e_5639_, lean_object* v_a_5640_, lean_object* v_a_5641_, lean_object* v_a_5642_, lean_object* v_a_5643_){
_start:
{
lean_object* v_options_5645_; lean_object* v___f_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; 
v_options_5645_ = lean_ctor_get(v_a_5642_, 1);
v___f_5646_ = lean_alloc_closure((void*)(l_Lean_Meta_letToHave___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5646_, 0, v_e_5639_);
v___x_5647_ = ((lean_object*)(l_Lean_Meta_letToHave___closed__0));
v___x_5648_ = lean_box(0);
v___x_5649_ = l_Lean_profileitM___at___00Lean_Meta_letToHave_spec__2___redArg(v___x_5647_, v_options_5645_, v___f_5646_, v___x_5648_, v_a_5640_, v_a_5641_, v_a_5642_, v_a_5643_);
return v___x_5649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_letToHave___boxed(lean_object* v_e_5650_, lean_object* v_a_5651_, lean_object* v_a_5652_, lean_object* v_a_5653_, lean_object* v_a_5654_, lean_object* v_a_5655_){
_start:
{
lean_object* v_res_5656_; 
v_res_5656_ = l_Lean_Meta_letToHave(v_e_5650_, v_a_5651_, v_a_5652_, v_a_5653_, v_a_5654_);
lean_dec(v_a_5654_);
lean_dec_ref(v_a_5653_);
lean_dec(v_a_5652_);
lean_dec_ref(v_a_5651_);
return v_res_5656_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(lean_object* v_00_u03b1_5657_, lean_object* v_x_5658_, uint8_t v_isExporting_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
lean_object* v___x_5665_; 
v___x_5665_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___redArg(v_x_5658_, v_isExporting_5659_, v___y_5660_, v___y_5661_, v___y_5662_, v___y_5663_);
return v___x_5665_;
}
}
LEAN_EXPORT lean_object* l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1___boxed(lean_object* v_00_u03b1_5666_, lean_object* v_x_5667_, lean_object* v_isExporting_5668_, lean_object* v___y_5669_, lean_object* v___y_5670_, lean_object* v___y_5671_, lean_object* v___y_5672_, lean_object* v___y_5673_){
_start:
{
uint8_t v_isExporting_boxed_5674_; lean_object* v_res_5675_; 
v_isExporting_boxed_5674_ = lean_unbox(v_isExporting_5668_);
v_res_5675_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1_spec__1(v_00_u03b1_5666_, v_x_5667_, v_isExporting_boxed_5674_, v___y_5669_, v___y_5670_, v___y_5671_, v___y_5672_);
lean_dec(v___y_5672_);
lean_dec_ref(v___y_5671_);
lean_dec(v___y_5670_);
lean_dec_ref(v___y_5669_);
return v_res_5675_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(lean_object* v_00_u03b1_5676_, lean_object* v_x_5677_, uint8_t v_when_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_){
_start:
{
lean_object* v___x_5684_; 
v___x_5684_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___redArg(v_x_5677_, v_when_5678_, v___y_5679_, v___y_5680_, v___y_5681_, v___y_5682_);
return v___x_5684_;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1___boxed(lean_object* v_00_u03b1_5685_, lean_object* v_x_5686_, lean_object* v_when_5687_, lean_object* v___y_5688_, lean_object* v___y_5689_, lean_object* v___y_5690_, lean_object* v___y_5691_, lean_object* v___y_5692_){
_start:
{
uint8_t v_when_boxed_5693_; lean_object* v_res_5694_; 
v_when_boxed_5693_ = lean_unbox(v_when_5687_);
v_res_5694_ = l_Lean_withoutExporting___at___00Lean_Meta_letToHave_spec__1(v_00_u03b1_5685_, v_x_5686_, v_when_boxed_5693_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_);
lean_dec(v___y_5691_);
lean_dec_ref(v___y_5690_);
lean_dec(v___y_5689_);
lean_dec_ref(v___y_5688_);
return v_res_5694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5751_; uint8_t v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5754_; 
v___x_5751_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_main___closed__0));
v___x_5752_ = 0;
v___x_5753_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_));
v___x_5754_ = l_Lean_registerTraceClass(v___x_5751_, v___x_5752_, v___x_5753_);
if (lean_obj_tag(v___x_5754_) == 0)
{
lean_object* v___x_5755_; lean_object* v___x_5756_; 
lean_dec_ref_known(v___x_5754_, 1);
v___x_5755_ = ((lean_object*)(l___private_Lean_Meta_LetToHave_0__Lean_Meta_LetToHave_visitLambdaLet_finalize___closed__3));
v___x_5756_ = l_Lean_registerTraceClass(v___x_5755_, v___x_5752_, v___x_5753_);
return v___x_5756_;
}
else
{
return v___x_5754_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2____boxed(lean_object* v_a_5757_){
_start:
{
lean_object* v_res_5758_; 
v_res_5758_ = l___private_Lean_Meta_LetToHave_0__Lean_Meta_initFn_00___x40_Lean_Meta_LetToHave_1606831773____hygCtx___hyg_2_();
return v_res_5758_;
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
